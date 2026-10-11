#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>
#include <algorithm>
extern "C" unsigned char ZeroPrinted[],ZeroForced[];
extern "C" std::uintptr_t ZeroObservation[18];
extern "C" void ZeroInvoke(void*,std::uintptr_t,std::uintptr_t);
static std::uint32_t read(const unsigned char* p){std::uint32_t v;std::memcpy(&v,p,4);return v;}
static std::uint32_t random(std::uint64_t& v){v^=v<<13;v^=v>>7;v^=v<<17;return static_cast<std::uint32_t>(v);}
static constexpr std::uintptr_t expected[]={0x13579bdf,0x2468ace0,0x0badc0de,0x11223344,0x55667788,0x76543210,0x10203040,0x50607080,0x90a0b0c0,0xd0e0f001,0x23456789,0xabcdef01,0x31415926,0x27182818};
static void packet(FILE* f,const char* name,unsigned char* p,unsigned len,bool comma){
    std::fprintf(f,"%s{\"name\":\"%s\",\"pc\":%llu,\"bytes\":[",comma?",":"",name,static_cast<unsigned long long>(reinterpret_cast<std::uintptr_t>(p)));
    for(unsigned i=0;i<len;++i)std::fprintf(f,"%s%u",i?",":"",p[i]);std::fputs("]}",f);
}
int main(){
    if(ZeroPrinted[0]!=0x83||ZeroPrinted[1]!=0x35||ZeroForced[0]!=0x81||ZeroForced[1]!=0x35||read(ZeroForced+6)!=0x80000000u)return 2;
    FILE* f=nullptr;if(fopen_s(&f,"zero-packets.json","w")||!f)return 3;
    std::fputs("[",f);packet(f,"typed_printed",ZeroPrinted,10,false);packet(f,"corrected",ZeroForced,20,true);std::fputs("]\n",f);std::fclose(f);
    auto before=read(ZeroPrinted+6);ZeroInvoke(ZeroPrinted,0x12345678u,1);
    if(before==0||read(ZeroPrinted+6)!=before)return 4;
    std::printf("Typed printed DEFZERO baseline: imm8; before=%08x after=%08x\n",before,read(ZeroPrinted+6));
    std::vector<std::uint32_t> words={0,1,2,0x7f,0x80,0xff,0x100,0x7fffffff,0x80000000,0xffffffff,0xaaaaaaaa,0x55555555};
    for(unsigned bit=0;bit<32;++bit){words.push_back(1u<<bit);words.push_back(~(1u<<bit));}
    std::uint64_t rng=0x146a80f247c159e3ULL;for(unsigned i=0;i<512;++i)words.push_back(random(rng));
    std::sort(words.begin(),words.end());words.erase(std::unique(words.begin(),words.end()),words.end());
    unsigned cases=0;
    for(auto value:words)for(unsigned cf=0;cf<2;++cf)for(unsigned rep=0;rep<4;++rep){
        auto seed=static_cast<std::uintptr_t>(random(rng));
#ifdef _WIN64
        seed|=static_cast<std::uintptr_t>(random(rng))<<32;
#endif
        std::memcpy(ZeroForced+6,&value,4);unsigned char snapshot[20];std::memcpy(snapshot,ZeroForced,20);
        FlushInstructionCache(GetCurrentProcess(),ZeroForced,20); // Host initialization only.
        for(unsigned call=0;call<2;++call){
            ZeroInvoke(ZeroForced,seed,cf);
            if(read(ZeroForced+6)!=0||ZeroObservation[0]!=seed||ZeroObservation[1]!=ZeroObservation[17]||(ZeroObservation[16]&1)!=0)return 5;
            const unsigned registers=sizeof(void*)==8?14:6;
            for(unsigned i=0;i<registers;++i)if(ZeroObservation[i+2]!=expected[i])return 6;
            for(unsigned i=0;i<20;++i)if((i<6||i>=10)&&ZeroForced[i]!=snapshot[i])return 7;
            ++cases;
        }
    }
    std::printf("DEFZERO %u-bit: PASS %u executions; %zu live words (zero, all GPRs/SP/CF, exact exterior bytes, repeated live fetch)\n",unsigned(sizeof(void*)*8),cases,words.size());
    return 0;
}
