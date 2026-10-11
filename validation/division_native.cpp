// Positive execution of the minimally corrected printed Listing 12.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>
static_assert(sizeof(void*)==4,"Listing 12 has DWORD fields and x86 near CALL");
using Word=std::uint32_t;
using Entry=void (__cdecl*)(Word,Word);
struct Descriptor {Entry entry;unsigned char** fields;Word count,mod,sign;};
extern "C" Descriptor** __cdecl GetDivTable();
extern "C" unsigned char* __cdecl GetDivBegin();
extern "C" unsigned char* __cdecl GetDivEnd();
extern "C" Word DivObservation[10];
static Word read(unsigned char* p) {Word value;std::memcpy(&value,p,4);return value;}
static void write(unsigned char* p,Word value) {std::memcpy(p,&value,4);}
static Word random(std::uint64_t& state) {state^=state<<13;state^=state>>7;state^=state<<17;return Word(state);}
static std::int64_t signedValue(Word value) {return value<0x80000000u?std::int64_t(value):std::int64_t(value)-0x100000000LL;}
static bool check(const Descriptor& d,Word x,Word y,Word seed,bool carry,std::uint64_t& rng) {
    auto fields=d.fields;
    if(y==0 || (d.sign && !d.mod && x==0x80000000u && y==0xffffffffu)) return true;
    if(read(fields[3])!=0) {std::puts("FAIL reusable CALL displacement");return false;}
    write(fields[0],x);write(fields[1],y);write(fields[2],random(rng));
    for(Word i=6;i<d.count;++i) write(fields[i],random(rng));
    auto begin=GetDivBegin(),end=GetDivEnd();
    std::vector<unsigned char> code(begin,end);
    const Word stackPointer=read(fields[4]),stackAddress=read(fields[5]);
    std::int64_t answer;
    if(d.sign) {
        const auto a=signedValue(x),b=signedValue(y);
        answer=d.mod?a%b:a/b; // Independent standard truncation-toward-zero oracle.
    } else answer=d.mod?std::int64_t(x%y):std::int64_t(x/y);
    const Word expected=Word(answer);
    const std::uint64_t magnitude=answer<0?std::uint64_t(-answer):std::uint64_t(answer);
    const bool expectedCarry=d.sign && answer<0 && magnitude>0 && magnitude<0x80000000ULL;
    d.entry(seed,carry?1u:0u);
    if(read(fields[2])!=expected || read(fields[0])!=x || read(fields[1])!=y ||
       read(fields[3])!=0 || read(fields[4])!=stackPointer || read(fields[5])!=stackAddress) {
        std::printf("FAIL result/input/stack/reuse mod=%u sign=%u x=%x y=%x expected=%x actual=%x\n",d.mod,d.sign,x,y,expected,read(fields[2]));return false;
    }
    if(DivObservation[0]!=seed || DivObservation[1]!=DivObservation[9] ||
       DivObservation[2]!=0x13579bdfu || DivObservation[3]!=0x2468ace0u ||
       DivObservation[4]!=0x0badc0deu || DivObservation[5]!=0x11223344u ||
       DivObservation[6]!=0x55667788u || DivObservation[7]!=0x76543210u ||
       bool(DivObservation[8]&1u)!=expectedCarry) {
        std::printf("FAIL register/CF mod=%u sign=%u x=%x y=%x\n",d.mod,d.sign,x,y);return false;
    }
    for(std::size_t i=0;i<code.size();++i) {
        const auto position=reinterpret_cast<std::uintptr_t>(begin+i);
        bool owned=false;
        for(Word f=0;f<d.count;++f) {
            const auto field=reinterpret_cast<std::uintptr_t>(fields[f]);
            owned|=field<=position && position<field+4;
        }
        if(!owned && code[i]!=begin[i]) {std::puts("FAIL complete exterior code-byte frame");return false;}
    }
    return true;
}
int main() {
    const Word edges[]={0,1,2,3,0x7ffffffeu,0x7fffffffu,0x80000000u,0x80000001u,0xfffffffeu,0xffffffffu,0xaaaaaaaau,0x55555555u};
    std::uint64_t rng=0x4469766973696f6eULL;
    unsigned total=0;
    for(unsigned mode=0;mode<4;++mode) {
        const auto& d=*GetDivTable()[mode];
        if(d.count!=(d.sign?(d.mod?26u:27u):19u) || d.mod!=(mode%2) || d.sign!=(mode/2)) return 1;
        std::vector<std::uintptr_t> positions;
        for(Word f=0;f<d.count;++f) {
            const auto field=reinterpret_cast<std::uintptr_t>(d.fields[f]);
            if(field<reinterpret_cast<std::uintptr_t>(GetDivBegin()) || field+4>reinterpret_cast<std::uintptr_t>(GetDivEnd())) return 1;
            positions.push_back(field);
            if(f==3) {if(d.fields[f][-1]!=0xe8) return 1;}
            else if(f==5) {if(d.fields[f][-2]!=0xc7) return 1;}
            else if(d.fields[f][-6]!=0xc7 && d.fields[f][-6]!=0x81) return 1;
        }
        std::sort(positions.begin(),positions.end());
        for(std::size_t i=1;i<positions.size();++i) if(positions[i-1]+4>positions[i]) return 1;
        if(d.fields[4]-4!=d.fields[5] || read(d.fields[4])!=reinterpret_cast<std::uintptr_t>(d.fields[4]) || read(d.fields[5])!=read(d.fields[4])) return 1;
        unsigned cases=0;
        auto exercise=[&](Word x,Word y,Word seed) {
            if(y==0 || (d.sign && !d.mod && x==0x80000000u && y==0xffffffffu)) return true;
            for(unsigned cf=0;cf<2;++cf) {if(!check(d,x,y,seed,cf!=0,rng)) return false;++cases;}
            return true;
        };
        for(auto x:edges) for(auto y:edges) for(auto seed:edges) if(!exercise(x,y,seed)) return 1;
        for(unsigned i=0;i<5000;++i) {const auto x=random(rng),y=random(rng),seed=random(rng);if(!exercise(x,y,seed)) return 1;}
        total+=cases;
        std::printf("Listing 12 mode %u: PASS %u executions; mod=%u sign=%u; %u complete fields (quotient/remainder, inputs, all GPRs/ESP/CF, exact exterior code frame, repeated calls)\n",mode,cases,d.mod,d.sign,d.count);
    }
    std::printf("Listing 12 x86: PASS %u executions in four modes\n",total);
    return 0;
}
