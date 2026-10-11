// Literal corresponding-half operations. Setup/flags observation are host code.
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>
#include <algorithm>
using Word = std::uintptr_t;
extern "C" Word __cdecl HalfMove(Word, Word);
extern "C" Word __cdecl HalfXor(Word, Word);
extern "C" Word __cdecl HalfAnd(Word, Word);
extern "C" Word __cdecl HalfOr(Word, Word);
extern "C" Word __cdecl HalfNot(Word, Word);
extern "C" Word __cdecl GetHalfFlags();
extern "C" void* __cdecl GetHalfFields();
extern "C" void* __cdecl GetHalfBegin();
extern "C" void* __cdecl GetHalfEnd();
using Entry = Word (__cdecl *)(Word, Word);
static Entry entries[] = {HalfMove,HalfXor,HalfAnd,HalfOr,HalfNot};
static unsigned char *fields, *begin, *end;
static std::uint32_t read(unsigned i) {
    std::uint32_t value;
    std::memcpy(&value, fields+10*i+6, 4);
    return value;
}
static void write(unsigned i, std::uint32_t value) { std::memcpy(fields+10*i+6,&value,4); }
static std::uint64_t expected(unsigned op, std::uint64_t target, std::uint64_t source) {
    switch(op) {
    case 0: return source;
    case 1: return target^source;
    case 2: return target&source;
    case 3: return target|source;
    default: return ~target;
    }
}
static bool check(unsigned op, std::uint64_t target, std::uint64_t source, Word seed, bool carry) {
    write(0,static_cast<std::uint32_t>(target)); write(1,static_cast<std::uint32_t>(target>>32));
    write(2,static_cast<std::uint32_t>(source)); write(3,static_cast<std::uint32_t>(source>>32));
    std::vector<unsigned char> before(begin,end);
    const Word actual = entries[op](seed,carry ? 1u : 0u);
    const bool actualCF = (GetHalfFlags()&1u)!=0;
    const Word expectedAX = op==4 ? seed : static_cast<Word>(static_cast<std::uint32_t>(seed));
    const bool expectedCF = op==0 || op==4 ? carry : false;
    const std::uint64_t actualTarget = read(0)|(std::uint64_t(read(1))<<32);
    const std::uint64_t actualSource = read(2)|(std::uint64_t(read(3))<<32);
    if(actual!=expectedAX || actualCF!=expectedCF || actualTarget!=expected(op,target,source) || actualSource!=source) {
        std::printf("FAIL op=%u CF=%u target=%llx source=%llx seed=%llx AX=%llx\n",op,unsigned(carry),
                    static_cast<unsigned long long>(target),static_cast<unsigned long long>(source),
                    static_cast<unsigned long long>(seed),static_cast<unsigned long long>(actual));
        return false;
    }
    for(std::size_t i=0;i<before.size();++i) {
        const auto p=begin+i;
        const bool targetWord=(p>=fields+6 && p<fields+10)||(p>=fields+16 && p<fields+20);
        if(!targetWord && *p!=before[i]) { std::puts("FAIL code byte frame"); return false; }
    }
    return true;
}
static std::uint64_t random(std::uint64_t& state) { state^=state<<13;state^=state>>7;state^=state<<17;return state; }
int main() {
    fields=static_cast<unsigned char*>(GetHalfFields());
    begin=static_cast<unsigned char*>(GetHalfBegin()); end=static_cast<unsigned char*>(GetHalfEnd());
    if(fields<begin || fields+40!=end) return 1;
    for(unsigned i=0;i<4;++i) if(fields[10*i]!=0xc7 || fields[10*i+1]!=0x05) return 1;
    const std::uint64_t edges[]={0,1,0xffffffffULL,0x100000000ULL,0x8000000000000000ULL,
        0xffffffffffffffffULL,0xffff0000ffff0000ULL,0x8000000080000000ULL,0x7fffffff7fffffffULL};
    unsigned cases=0;
    for(auto target:edges) for(auto source:edges) for(auto seed:edges)
        for(unsigned op=0;op<5;++op) for(unsigned cf=0;cf<2;++cf) {
            if(!check(op,target,source,static_cast<Word>(seed),cf!=0)) return 1;
            ++cases;
        }
    std::uint64_t rng=0x4d6f7273652018ULL;
    for(unsigned i=0;i<1000;++i) {
        const auto target=random(rng),source=random(rng),seed=random(rng);
        for(unsigned op=0;op<5;++op) for(unsigned cf=0;cf<2;++cf) {
            if(!check(op,target,source,static_cast<Word>(seed),cf!=0)) return 1;
            ++cases;
        }
    }
    std::printf("Half-frame %u-bit: PASS %u cases (five operations, both CF, source/AX/byte frame)\n",
                unsigned(sizeof(Word)*8),cases);
    return 0;
}
