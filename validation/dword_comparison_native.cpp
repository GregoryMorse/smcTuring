// Literal SUB/NEG/SBB/NOT match mask; host capture lies outside the pure block.
#define NOMINMAX
#include <windows.h>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <stdexcept>
#include <vector>
#include "comparison.hpp"
static void require(bool v,const char* s){if(!v)throw std::runtime_error(s);}
static std::uint32_t get(const void* p){std::uint32_t v;std::memcpy(&v,p,4);return v;}
static void put(void* p,std::uint32_t v){std::memcpy(p,&v,4);}
static std::uint64_t randomWord(std::uint64_t& s){s^=s<<13;s^=s>>7;s^=s<<17;return s;}
static void bytes(FILE* out,const unsigned char* first,unsigned size){std::fprintf(out,"[");
 for(unsigned i=0;i<size;++i)std::fprintf(out,i?",%u":"%u",unsigned(first[i]));std::fprintf(out,"]");}
int main(){try{
 require(CompareMarkerEnd-CompareMarker==39,"five packet length");
 require(CompareScalarEnd-CompareScalar==10 && CompareMaskEnd-CompareMask==10,"owner lengths");
 std::vector<Word> seeds={0,1,2,3,Word(-1),Word(1)<<(sizeof(Word)*8-1),(Word(1)<<(sizeof(Word)*8-1))-1,Word(0x0123456789abcdefULL & std::uint64_t(Word(-1)))};
 std::vector<std::uint32_t> values={0,1,2,3,0xffffffffU,0x80000000U,0x7fffffffU,0xabcdef01U};
 std::uint64_t random=0x12345678abcdef01ULL;for(unsigned i=0;i<32;++i)values.push_back(std::uint32_t(randomWord(random)));
 FILE* out=nullptr;require(fopen_s(&out,"comparison-packets.json","w")==0,"packet file");
 auto addr=[](const void* p){return static_cast<unsigned long long>(reinterpret_cast<std::uintptr_t>(p));};
 std::fprintf(out,"{\"pc\":%llu,\"scalar\":%llu,\"mask\":%llu,\"endpoint\":%llu,\"initial\":",
  addr(CompareMarker),addr(CompareScalar+6),addr(CompareMask+6),addr(CompareMarkerEnd));
 bytes(out,CompareMarker,39);std::fprintf(out,",\"owners\":[");bytes(out,CompareScalar,10);
 std::fprintf(out,",");bytes(out,CompareMask,10);std::fprintf(out,"],\"live\":[");
 for(unsigned i=0;i<values.size();++i){put(CompareMarker+16,values[i]);if(i)std::fprintf(out,",");
  std::fprintf(out,"{\"symbol\":%u,\"bytes\":",values[i]);bytes(out,CompareMarker,39);std::fprintf(out,"}");}
 std::fprintf(out,"]}\n");std::fclose(out);
 unsigned cases=0,matches=0;
 const auto size=static_cast<std::size_t>(CompareMaskEnd-CompareMarker);
 for(Word seed:seeds)for(auto candidate:values)for(auto symbol:values)for(unsigned cf=0;cf<2;++cf){
  for(unsigned reuse=0;reuse<2;++reuse){
   put(CompareMarker+16,symbol);put(CompareScalar+6,candidate);put(CompareMask+6,0xabcde123U);
   std::vector<unsigned char> before(CompareMarker,CompareMarker+size);
   require(FlushInstructionCache(GetCurrentProcess(),CompareMarker,size)!=0,"flush");CompareEntry(seed,cf);
   const bool same=candidate==symbol;const auto* o=CompareObservation;
   require(o[0]==seed,"full AX changed");require(o[1]==o[RegisterCount],"SP changed");
   for(unsigned i=2;i<RegisterCount;++i)require(o[i]==ExpectedRegisters[i],"GPR changed");
   require((o[RegisterCount+1]&1)==cf,"entry CF");
   require((o[RegisterCount+2]&0x8d5)==(same?0x44U:0x95U),"comparison status flags");
   require(o[RegisterCount+3]==reinterpret_cast<std::uintptr_t>(CompareMarkerEnd),"endpoint");
   require(get(CompareScalar+6)==std::uint32_t(symbol-candidate),"scalar negated difference");
   require(get(CompareMask+6)==(same?0xffffffffU:0),"match mask");
   for(std::size_t i=0;i<size;++i){const auto* p=CompareMarker+i;
    if((p>=CompareScalar+6&&p<CompareScalar+10)||(p>=CompareMask+6&&p<CompareMask+10))continue;
    require(*p==before[i],"exterior code byte changed");}
   ++cases;matches+=same?1:0;
  }}
 require(cases==51200 && matches==1280,"case counts");
 std::printf("DWORD COMPARISON %u-bit: PASS 51200 cases/1280 matches; live DWORD/full AX/GPR/SP/flags/endpoint/code frame/reuse\n",unsigned(sizeof(Word)*8));return 0;
}catch(const std::exception& e){std::fprintf(stderr,"%s\n",e.what());return 1;}}
