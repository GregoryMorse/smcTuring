// Positive current imm32 copy, with the exact typed published baseline.
#define NOMINMAX
#include <windows.h>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <stdexcept>
#include <vector>
using Word=std::uintptr_t;
struct Fixture {unsigned index;bool corrected;void(*entry)(Word,unsigned);unsigned char *start,*second,*third,*stop,*source,*target,*compare,*end;};
#include "input.hpp"
static void require(bool v,const char* s){if(!v)throw std::runtime_error(s);}
static std::uint32_t get(const void* p){std::uint32_t v;std::memcpy(&v,p,4);return v;}
static void put(void* p,std::uint32_t v){std::memcpy(p,&v,4);}
static std::uint64_t randomWord(std::uint64_t& s){s^=s<<13;s^=s>>7;s^=s<<17;return s;}
static void dumpPackets(){FILE* out=nullptr;require(fopen_s(&out,"input-packets.json","w")==0,"packet file");std::fprintf(out,"[");
 for(const auto& f:Fixtures){if(f.index)std::fprintf(out,",");
  const auto addr=[](const void* p){return static_cast<unsigned long long>(reinterpret_cast<Word>(p));};
  std::fprintf(out,"{\"index\":%u,\"corrected\":%s,\"sites\":{\"start\":%llu,\"source\":%llu,\"target\":%llu,\"compare\":%llu},\"packets\":[",f.index,f.corrected?"true":"false",addr(f.start),addr(f.source),addr(f.target),addr(f.compare));
  const std::array<const char*,6> names={"first","second","third","source","target","compare"};
  const std::array<unsigned char*,6> begin={f.start,f.second,f.third,f.source,f.target,f.compare};
  const std::array<unsigned char*,6> end={f.second,f.third,f.stop,f.source+10,f.target+7,f.compare+10};
  for(unsigned i=0;i<begin.size();++i){if(i)std::fprintf(out,",");std::fprintf(out,"{\"name\":\"%s\",\"pc\":%llu,\"bytes\":[",names[i],addr(begin[i]));
   for(auto* p=begin[i];p<end[i];++p)std::fprintf(out,p==begin[i]?"%u":",%u",unsigned(*p));std::fprintf(out,"]}");}
  std::fprintf(out,"]}");}
 std::fprintf(out,"]\n");std::fclose(out);}
int main(){try{dumpPackets();
 std::vector<Word> seeds={0,1,2,3,Word(-1),Word(1)<<(sizeof(Word)*8-1),(Word(1)<<(sizeof(Word)*8-1))-1,Word(0x0123456789abcdefULL & std::uint64_t(Word(-1)))};
 std::vector<std::uint32_t> symbols={0,1,2,3,0xffffffffU,0x80000000U,0x7fffffffU,0xabcdef01U};
 std::uint64_t random=0xabcdef1234567890ULL;for(unsigned i=0;i<32;++i){seeds.push_back(Word(randomWord(random)));symbols.push_back(std::uint32_t(randomWord(random)));}
 std::array<unsigned,2> cases={0,0};
 for(const auto& f:Fixtures)for(Word seed:seeds)for(auto symbol:symbols)for(unsigned cf=0;cf<2;++cf){
  put(f.source+6,symbol);put(f.target+3,std::uint32_t(randomWord(random)));const auto expected=f.corrected?symbol:get(f.source);
  for(unsigned reuse=0;reuse<2;++reuse){std::vector<unsigned char> before(f.start,f.end);
   require(FlushInstructionCache(GetCurrentProcess(),f.start,before.size())!=0,"flush");f.entry(seed,cf);
   const auto* o=InputObservation;require(o[0]==Word(std::uint32_t(seed)),"low AX restoration/zero extension");require(o[1]==o[RegisterCount],"SP changed");
   for(unsigned i=2;i<RegisterCount;++i)require(o[i]==ExpectedRegisters[i],"GPR changed");
   require((o[RegisterCount+1]&1)==cf,"entry CF");require((o[RegisterCount+1]&0xcd5)==(o[RegisterCount+2]&0xcd5),"status flags changed");
   require(o[RegisterCount+3]==reinterpret_cast<Word>(f.stop),"endpoint");require(get(f.target+3)==expected,"copied operand value");require(get(f.source+6)==symbol,"source symbol changed");
   for(std::size_t i=0;i<before.size();++i){auto* p=f.start+i;const auto word=reinterpret_cast<Word>(p);const auto field=reinterpret_cast<Word>(f.target+3);
    if(word<field||word>=field+4)require(*p==before[i],"exterior code byte changed");}
   ++cases[f.index];}}
 require(cases[0]==6400&&cases[1]==6400,"case count");std::printf("INPUT OPERAND %u-bit: PASS 6400 typed-original and 6400 corrected cases; current symbol/low AX/GPR/SP/flags/endpoint/exterior bytes/reuse\n",unsigned(sizeof(Word)*8));return 0;
}catch(const std::exception& e){std::fprintf(stderr,"%s\n",e.what());return 1;}}
