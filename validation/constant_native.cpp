// Listing 6 with M08: compile-time trailing-zero gaps, same USEWORD32 macros.
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <vector>
static_assert(sizeof(void*)==4,"Finite x86 absolute operand words");
extern "C" void __cdecl ConstantInvoke(void*,std::uint32_t,std::uint32_t);
extern "C" std::uint32_t ConstantObservation[10];
static unsigned ctz(std::uint32_t n) {unsigned r=0;while((n&1u)==0u){++r;n>>=1;}return r;}
static std::uint32_t consume(std::uint32_t n,unsigned count){return count==32?0u:n>>count;}
static std::uint32_t random(std::uint64_t& n){n^=n<<13;n^=n>>7;n^=n<<17;return static_cast<std::uint32_t>(n);}
struct Op {unsigned kind,count;}; // 0=store zero,1=SHL,2=XCHG data,3=MOV scratch,EAX,4=ADD scratch,EAX,5=ADD data,current scratch immediate
static std::vector<Op> compile(std::uint32_t n) {
    std::vector<Op> ops;
    if(!n){ops.push_back({0,0});return ops;}
    unsigned first=ctz(n);if(first)ops.push_back({1,first});
    n=consume(n,first+1);if(!n)return ops;
    ops.insert(ops.end(),{{2,0},{3,0},{2,0}});
    for(;;) {
        unsigned gap=ctz(n)+1;ops.push_back({1,gap});n=consume(n,gap);
        if(!n){ops.push_back({5,0});break;}
        ops.insert(ops.end(),{{2,0},{4,0},{2,0}});
    }
    return ops;
}
static unsigned length(Op op){switch(op.kind){case 0:case 5:return 10;case 1:return op.count==1?6:7;case 3:return 5;default:return 6;}}
static void put(std::vector<unsigned char>& b,std::uint32_t x){for(unsigned i=0;i<4;++i)b.push_back(static_cast<unsigned char>(x>>(i*8)));}
struct Image {
    unsigned char* base;unsigned data,scratch,pure,span;std::vector<Op> ops;
    explicit Image(std::uint32_t n):base(nullptr),data(0),scratch(0),pure(0),span(0),ops(compile(n)) {
        for(auto op:ops)pure+=length(op);
        data=pure+1+6;scratch=data+10;
        unsigned cursor=0;for(auto op:ops){if(op.kind==5)scratch=cursor+6;cursor+=length(op);}
        span=pure+1+10+(scratch==data+10?10:0);
        base=static_cast<unsigned char*>(VirtualAlloc(nullptr,span,MEM_COMMIT|MEM_RESERVE,PAGE_EXECUTE_READWRITE));
        if(!base){std::puts("allocation failed");std::exit(1);}
        auto addr=[&](unsigned offset){return static_cast<std::uint32_t>(reinterpret_cast<std::uintptr_t>(base+offset));};
        std::vector<unsigned char> bytes;
        for(auto op:ops){
            switch(op.kind){
            case 0:bytes.insert(bytes.end(),{0xc7,0x05});put(bytes,addr(data));put(bytes,0);break;
            case 1:bytes.insert(bytes.end(),{static_cast<unsigned char>(op.count==1?0xd1:0xc1),0x25});put(bytes,addr(data));if(op.count!=1)bytes.push_back(static_cast<unsigned char>(op.count));break;
            case 2:bytes.insert(bytes.end(),{0x87,0x05});put(bytes,addr(data));break;
            case 3:bytes.push_back(0xa3);put(bytes,addr(scratch));break;
            case 4:bytes.insert(bytes.end(),{0x01,0x05});put(bytes,addr(scratch));break;
            case 5:bytes.insert(bytes.end(),{0x81,0x05});put(bytes,addr(data));put(bytes,0x12345678u);break;
            }
        }
        bytes.push_back(0xc3); // host return is outside pure extent
        bytes.insert(bytes.end(),{0xc7,0x05});put(bytes,addr(data));put(bytes,0);
        if(scratch==data+10){bytes.insert(bytes.end(),{0x81,0x05});put(bytes,addr(data));put(bytes,0x12345678u);}
        if(bytes.size()!=span || data+4>span || scratch+4>span){std::puts("image shape failed");std::exit(1);}
        std::memcpy(base,bytes.data(),span);FlushInstructionCache(GetCurrentProcess(),base,span);
    }
    ~Image(){VirtualFree(base,0,MEM_RELEASE);}
    void write(unsigned at,std::uint32_t n){std::memcpy(base+at,&n,4);}
    std::uint32_t read(unsigned at)const{std::uint32_t n;std::memcpy(&n,base+at,4);return n;}
    void record(FILE* f,std::uint32_t n,bool comma)const {
        std::fprintf(f,"%s{\"constant\":%u,\"base\":%u,\"data\":%u,\"scratch\":%u,\"pure\":%u,\"bytes\":[",comma?",\n":"",n,static_cast<unsigned>(reinterpret_cast<std::uintptr_t>(base)),data,scratch,pure);
        for(unsigned i=0;i<span;++i)std::fprintf(f,"%s%u",i?",":"",base[i]);std::fputs("]}",f);
    }
    bool check(std::uint32_t n,std::uint32_t x,std::uint32_t seed,bool cf,std::uint64_t& rng) {
        write(data,x);write(scratch,random(rng));auto before=std::vector<unsigned char>(base,base+span);
        std::uint32_t factor=x,total=read(scratch);bool carry=cf;
        for(auto op:ops) {
            switch(op.kind) {
            case 0:factor=0;break;
            case 1:if(op.count<1||op.count>31)return false;carry=((factor>>(32-op.count))&1u)!=0;factor<<=op.count;break;
            case 3:total=factor;break;
            case 4:carry=(std::uint64_t(total)+factor)>0xffffffffULL;total+=factor;break;
            case 5:carry=(std::uint64_t(factor)+total)>0xffffffffULL;factor+=total;break;
            default:break;
            }
        }
        // This host flush synchronizes initializer writes only. Within the pure
        // trace, actual native patched immediate consumption is being tested.
        FlushInstructionCache(GetCurrentProcess(),base,span);
        ConstantInvoke(base,seed,cf?1u:0u);
        auto product=static_cast<std::uint32_t>(std::uint64_t(x)*n);
        if(factor!=product||read(data)!=product||read(scratch)!=total||ConstantObservation[0]!=seed||
            ConstantObservation[1]!=ConstantObservation[9]||ConstantObservation[2]!=0x13579bdfu||
            ConstantObservation[3]!=0x2468ace0u||ConstantObservation[4]!=0x0badc0deu||
            ConstantObservation[5]!=0x11223344u||ConstantObservation[6]!=0x55667788u||
            ConstantObservation[7]!=0x76543210u||((ConstantObservation[8]&1u)!=0)!=carry) {
            std::printf("FAIL n=%x x=%x product=%x actual=%x scratch=%x/%x CF=%u/%u\n",n,x,product,read(data),read(scratch),total,ConstantObservation[8]&1u,carry?1u:0u);return false;
        }
        for(unsigned i=0;i<span;++i)if(!(data<=i&&i<data+4)&&!(scratch<=i&&i<scratch+4)&&before[i]!=base[i]){std::puts("exterior byte frame failed");return false;}
        return true;
    }
};
int main(){
    std::vector<std::uint32_t> constants={0,1,2,3,5,7,15,0x7fffffffu,0x80000000u,0xffffffffu,0x55555555u,0xaaaaaaaau};
    for(unsigned i=0;i<32;++i)constants.push_back(1u<<i);
    for(unsigned i=0;i<32;++i)for(unsigned j=i+1;j<32;++j)constants.push_back((1u<<i)|(1u<<j));
    std::uint64_t rng=0x4d6f7273652018ULL;for(unsigned i=0;i<128;++i)constants.push_back(random(rng));
    std::sort(constants.begin(),constants.end());constants.erase(std::unique(constants.begin(),constants.end()),constants.end());
    const std::uint32_t edges[]={0,1,2,3,0x7fffffffu,0x80000000u,0xffffffffu,0x55555555u,0xaaaaaaaau};
    FILE* f=nullptr;if(fopen_s(&f,"constant-packets.json","w")!=0||!f)return 1;std::fputs("[\n",f);
    unsigned cases=0,packets=0;bool comma=false;
    for(auto n:constants){Image image(n);image.record(f,n,comma);comma=true;packets+=static_cast<unsigned>(image.ops.size());
        for(auto x:edges)for(unsigned cf=0;cf<2;++cf){if(!image.check(n,x,random(rng),cf!=0,rng))return 1;++cases;}
        for(unsigned i=0;i<32;++i){auto x=random(rng);for(unsigned cf=0;cf<2;++cf){if(!image.check(n,x,random(rng),cf!=0,rng))return 1;++cases;}}
    }
    std::fputs("\n]\n",f);std::fclose(f);
    std::printf("Listing 6 x86: PASS %u cases; %u constants; %u pure packets (product, scratch, all GPRs/ESP/CF, exterior bytes, repeated calls)\n",cases,static_cast<unsigned>(constants.size()),packets);
    return 0;
}
