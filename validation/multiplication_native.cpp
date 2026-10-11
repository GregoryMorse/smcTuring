// Corrected Listing 11. Host setup and observation surround the pure loop.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>
static_assert(sizeof(void*)==4,"Listing 11 uses 32-bit fields and calls");
extern "C" void __cdecl MulNative(std::uint32_t,std::uint32_t);
extern "C" unsigned char** __cdecl GetMulFields();
extern "C" unsigned char* __cdecl GetMulBegin();
extern "C" unsigned char* __cdecl GetMulEnd();
extern "C" unsigned char* __cdecl GetMulNext();
extern "C" unsigned char* __cdecl GetMulExit();
extern "C" std::uint32_t MulObservation[10];
static unsigned char** fields;
static unsigned char *begin,*end;
static std::uint32_t read(unsigned i) {std::uint32_t v;std::memcpy(&v,fields[i],4);return v;}
static void write(unsigned i,std::uint32_t v) {std::memcpy(fields[i],&v,4);}
static std::uint32_t random(std::uint64_t& s) {s^=s<<13;s^=s>>7;s^=s<<17;return static_cast<std::uint32_t>(s);}
static bool check(std::uint32_t x,std::uint32_t y,std::uint32_t seed,bool carry,std::uint64_t& rng) {
    if(read(8)!=0) {std::puts("FAIL reused CALL displacement");return false;}
    write(0,x);write(1,y);write(2,random(rng));
    for(unsigned i: {3u,4u,5u,6u,7u,9u,10u,11u}) write(i,random(rng));
    std::array<std::uint32_t,14> before{};
    for(unsigned i=0;i<14;++i) before[i]=read(i);
    std::vector<unsigned char> code(begin,end);
    MulNative(seed,carry?1u:0u);
    std::uint32_t a=x,b=y,r=0,addend=before[11];
    while(b) {addend=(b&1u)?a:0; r+=addend;a<<=1;b>>=1;}
    const auto delta=static_cast<std::uint32_t>(reinterpret_cast<std::uintptr_t>(GetMulExit())-reinterpret_cast<std::uintptr_t>(GetMulNext()));
    std::array<std::uint32_t,14> expected=before;
    expected[2]=r;expected[3]=a;expected[4]=0;expected[5]=r;expected[6]=delta;expected[7]=delta;expected[8]=0;
    if(y!=0) {expected[9]=0xffffffffu;expected[10]=0xffffffffu;expected[11]=addend;}
    for(unsigned i=0;i<14;++i) if(read(i)!=expected[i]) {
        std::printf("FAIL field %u: x=%x y=%x expected=%x actual=%x\n",i,x,y,expected[i],read(i));return false;
    }
    const std::uint32_t product=static_cast<std::uint32_t>(std::uint64_t(x)*y);
    if(r!=product || MulObservation[0]!=seed || MulObservation[1]!=MulObservation[9] ||
       MulObservation[2]!=0x13579bdfu || MulObservation[3]!=0x2468ace0u || MulObservation[4]!=0x0badc0deu ||
       MulObservation[5]!=0x11223344u || MulObservation[6]!=0x55667788u || MulObservation[7]!=0x76543210u || (MulObservation[8]&1u)) {
        std::printf("FAIL result/register/CF: x=%x y=%x seed=%x actualAX=%x\n",x,y,seed,MulObservation[0]);return false;
    }
    for(std::size_t i=0;i<code.size();++i) {
        const auto p=reinterpret_cast<std::uintptr_t>(begin+i);
        bool owned=false;
        for(unsigned f=0;f<14;++f) {const auto q=reinterpret_cast<std::uintptr_t>(fields[f]);owned|=q<=p && p<q+4;}
        if(!owned && code[i]!=begin[i]) {std::puts("FAIL exterior code-byte frame");return false;}
    }
    return true;
}
int main() {
    fields=GetMulFields();begin=GetMulBegin();end=GetMulEnd();
    std::array<std::uintptr_t,14> positions{};
    for(unsigned i=0;i<14;++i) {
        positions[i]=reinterpret_cast<std::uintptr_t>(fields[i]);
        if(positions[i]<reinterpret_cast<std::uintptr_t>(begin)||positions[i]+4>reinterpret_cast<std::uintptr_t>(end)) return 1;
    }
    std::sort(positions.begin(),positions.end());
    for(unsigned i=1;i<14;++i) if(positions[i-1]+4>positions[i]) return 1;
    if(fields[12]-4!=fields[13] || read(12)!=reinterpret_cast<std::uintptr_t>(fields[12]) || read(13)!=read(12)) return 1;
    for(unsigned i: {0u,1u,2u,3u,4u,5u,6u,7u,9u,10u,11u}) if(fields[i][-6]!=0xc7 && fields[i][-6]!=0x81) return 1;
    if(fields[8][-1]!=0xe8) return 1;
    const std::uint32_t edges[]={0,1,2,3,0x7fffffffu,0x80000000u,0xffffffffu,0xaaaaaaaau,0x55555555u};
    std::uint64_t rng=0x4d6f7273652018ULL;unsigned cases=0;
    for(auto x:edges) for(auto y:edges) for(auto seed:edges) for(unsigned cf=0;cf<2;++cf) {
        if(!check(x,y,seed,cf!=0,rng)) return 1;++cases;
    }
    for(unsigned i=0;i<5000;++i) {auto x=random(rng),y=random(rng),seed=random(rng);for(unsigned cf=0;cf<2;++cf) {
        if(!check(x,y,seed,cf!=0,rng)) return 1;++cases;
    }}
    std::printf("Listing 11 x86: PASS %u cases (product, all 14 words, all GPRs/ESP/CF, exterior code bytes, repeated calls)\n",cases);
    return 0;
}
