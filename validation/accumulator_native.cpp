// Printed Listing 9, complete current code frame and pure-output preservation.
#define NOMINMAX
#include <windows.h>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <stdexcept>
#include <vector>
using Word=std::uintptr_t;
struct Fixture { unsigned index;void(*entry)(Word,unsigned);unsigned char *prologue,*bodyFirst,*bodySecond,*bodyStore,*epilogue,*second,*third,*marker,*markerEnd,*saveOwner,*pointerOwner,*bodyOwner,*outputOwner,*save,*pointer,*body,*output,*end; };
#include "accumulator.hpp"
static void require(bool value,const char* message){if(!value)throw std::runtime_error(message);}
static Word get(const void* p){Word v;std::memcpy(&v,p,sizeof v);return v;}
static void put(void* p,Word v){std::memcpy(p,&v,sizeof v);}
static std::uint64_t randomWord(std::uint64_t& state){state^=state<<13;state^=state>>7;state^=state<<17;return state;}
static void dumpPackets() {
 FILE* out=nullptr;require(fopen_s(&out,"accumulator-packets.json","w")==0,"packet file");std::fprintf(out,"[");
 for(const auto& f:Fixtures){
  if(f.index)std::fprintf(out,",");
  const auto address=[](const void* p){return static_cast<unsigned long long>(reinterpret_cast<Word>(p));};
  std::fprintf(out,"{\"index\":%u,\"sites\":{\"prologue\":%llu,\"epilogue\":%llu,\"save\":%llu,\"pointer\":%llu,\"body_first\":%llu,\"body_second\":%llu,\"body_store\":%llu,\"body\":%llu,\"output\":%llu},\"packets\":[",f.index,address(f.prologue),address(f.epilogue),address(f.save),address(f.pointer),address(f.bodyFirst),address(f.bodySecond),address(f.bodyStore),address(f.body),address(f.output));
  const std::array<const char*,12> names={"save","bodyFirst","bodySecond","bodyStore","first","second","third","terminal","saveOwner","pointerOwner","bodyOwner","outputOwner"};
  const std::array<unsigned char*,12> begin={f.prologue,f.bodyFirst,f.bodySecond,f.bodyStore,f.epilogue,f.second,f.third,f.marker,f.saveOwner,f.pointerOwner,f.bodyOwner,f.outputOwner};
  const std::array<unsigned char*,12> end={f.bodyFirst,f.bodySecond,f.bodyStore,f.epilogue,f.second,f.third,f.marker,f.markerEnd,f.save+sizeof(Word),f.pointer+sizeof(Word),f.body+sizeof(Word),f.output+sizeof(Word)};
  for(unsigned i=0;i<begin.size();++i){
   if(i)std::fprintf(out,",");std::fprintf(out,"{\"name\":\"%s\",\"pc\":%llu,\"bytes\":[",names[i],address(begin[i]));
   for(auto* p=begin[i];p<end[i];++p)std::fprintf(out,p==begin[i]?"%u":",%u",unsigned(*p));std::fprintf(out,"]}");
  }
  std::fprintf(out,"]}");
 }
 std::fprintf(out,"]\n");std::fclose(out);
}
int main(){try{
 dumpPackets();
 std::vector<Word> values={0,1,2,3,Word(-1),Word(1)<<(sizeof(Word)*8-1),(Word(1)<<(sizeof(Word)*8-1))-1,Word(0x0123456789abcdefULL & std::uint64_t(Word(-1)))};
 std::uint64_t random=0x12345678abc98765ULL;for(unsigned i=0;i<32;++i)values.push_back(Word(randomWord(random)));
 unsigned cases=0;
 for(const auto& f:Fixtures)for(Word seed:values)for(Word value:values)for(unsigned cf=0;cf<2;++cf){
  put(f.save,Word(randomWord(random)));put(f.pointer,reinterpret_cast<Word>(f.save));put(f.body,value);put(f.output,Word(randomWord(random)));
  for(unsigned reuse=0;reuse<2;++reuse){
   std::vector<unsigned char> before(f.prologue,f.end);
   require(FlushInstructionCache(GetCurrentProcess(),f.prologue,before.size())!=0,"flush");f.entry(seed,cf);
   const auto* o=AccumulatorObservation;
   require(o[0]==seed,"full accumulator not restored");require(o[1]==o[RegisterCount],"SP changed");
   for(unsigned i=2;i<RegisterCount;++i)require(o[i]==ExpectedRegisters[i],"GPR changed");
   require((o[RegisterCount+1]&1)==cf,"entry CF");require((o[RegisterCount+1]&0xcd5)==(o[RegisterCount+2]&0xcd5),"status flags changed");
   require(o[RegisterCount+3]==reinterpret_cast<Word>(f.markerEnd),"endpoint");
   require(get(f.save)==reinterpret_cast<Word>(f.save)&&get(f.pointer)==reinterpret_cast<Word>(f.save),"reserved field reset");
   require(get(f.body)==value&&get(f.output)==value,"body result or output preservation");
   for(std::size_t i=0;i<before.size();++i){auto* p=f.prologue+i;
    const auto inside=[p](const unsigned char* field){return p>=field&&p<field+sizeof(Word);};
    if(!inside(f.save)&&!inside(f.output))require(*p==before[i],"exterior code byte changed");
   }
   ++cases;
  }
 }
 require(cases==38400,"case count");std::printf("ACCUMULATOR %u-bit: PASS 38400 executions; 6 owner orders; full AX/GPR/SP/flags/outputs/endpoint/code-frame/reuse\n",unsigned(sizeof(Word)*8));return 0;
}catch(const std::exception& e){std::fprintf(stderr,"%s\n",e.what());return 1;}}
