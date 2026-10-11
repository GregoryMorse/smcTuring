// Host capture is outside the exact three-instruction pure cursor fragment.
#define NOMINMAX
#include <windows.h>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <stdexcept>
#include <vector>
#include "cursor.hpp"
static void require(bool v,const char* s){if(!v)throw std::runtime_error(s);}
template<class T> static T get(const void* p){T v;std::memcpy(&v,p,sizeof(v));return v;}
template<class T> static void put(void* p,T v){std::memcpy(p,&v,sizeof(v));}
static std::uint64_t randomWord(std::uint64_t& s){s^=s<<13;s^=s>>7;s^=s<<17;return s;}
static unsigned status(std::uint32_t v){
 unsigned low=v&255U,count=0;for(unsigned i=0;i<8;++i)count+=(low>>i)&1U;
 return (count%2==0?4U:0U)|(v==0?64U:0U)|(v>>31?128U:0U);
}
static void bytes(FILE* out,const unsigned char* p,unsigned size){
 std::fprintf(out,"[");for(unsigned i=0;i<size;++i)std::fprintf(out,i?",%u":"%u",unsigned(p[i]));std::fprintf(out,"]");
}
int main(){try{
 const unsigned span=sizeof(Word)==8?21U:19U;
 require(CursorMarkerEnd-CursorMarker==span,"three-instruction length");
 require(CursorXor-CursorMarker==(sizeof(Word)==8?7:6),"middle instruction position");
 require(CursorOwnerEnd-CursorOwner==sizeof(Word)+(sizeof(Word)==8?2:1),"MOFFS owner length");
 require(CursorPointer-CursorOwner==(sizeof(Word)==8?2:1),"full-width owned operand");
 require(CursorTapeEnd-CursorTape==10,"DWORD owner length");
 auto address=[](const void* p){return static_cast<unsigned long long>(reinterpret_cast<std::uintptr_t>(p));};
 const Word head=Word(reinterpret_cast<std::uintptr_t>(CursorTape));
 std::vector<Word> seeds={0,1,2,3,Word(-1),Word(1)<<(sizeof(Word)*8-1),(Word(1)<<(sizeof(Word)*8-1))-1,Word(0x0123456789abcdefULL & std::uint64_t(Word(-1)))};
 std::vector<std::uint32_t> symbols={0,1,2,3,0xffffffffU,0x80000000U,0x7fffffffU,0xabcdef01U};
 std::uint64_t random=0x12345678abcdef01ULL;
 for(unsigned i=0;i<32;++i){symbols.push_back(std::uint32_t(randomWord(random)));if(i<8)seeds.push_back(Word(randomWord(random)));}
 FILE* out=nullptr;require(fopen_s(&out,"cursor-packets.json","w")==0,"packet file");
 std::fprintf(out,"{\"pc\":%llu,\"cursor\":%llu,\"head\":%llu,\"endpoint\":%llu,\"initial\":",
  address(CursorMarker),address(CursorPointer),address(CursorTape),address(CursorMarkerEnd));
 bytes(out,CursorMarker,span);std::fprintf(out,",\"owners\":[");bytes(out,CursorOwner,unsigned(CursorOwnerEnd-CursorOwner));
 std::fprintf(out,",");bytes(out,CursorTape,10);std::fprintf(out,"],\"live\":[");
 for(unsigned i=0;i<symbols.size();++i){
  put<std::uint32_t>(CursorXor+3,symbols[i]);if(i)std::fprintf(out,",");
  std::fprintf(out,"{\"value\":%u,\"bytes\":",symbols[i]);bytes(out,CursorMarker,span);std::fprintf(out,"}");
 }
 std::fprintf(out,"]}\n");std::fclose(out);
 unsigned cases=0;
 const auto size=static_cast<std::size_t>(CursorTapeEnd-CursorMarker);
 for(Word seed:seeds)for(auto old:symbols)for(auto fresh:symbols)for(unsigned chosen=0;chosen<2;++chosen)for(unsigned cf=0;cf<2;++cf){
  const std::uint32_t change=chosen?(old^fresh):0U;
  put<Word>(CursorPointer,head);put<std::uint32_t>(CursorTape+6,old);put<std::uint32_t>(CursorXor+3,change);
  for(unsigned reuse=0;reuse<2;++reuse){
   const std::uint32_t expected=chosen&&reuse==0?fresh:old;
   std::vector<unsigned char> before(CursorMarker,CursorMarker+size);
   require(FlushInstructionCache(GetCurrentProcess(),CursorMarker,size)!=0,"flush");
   CursorEntry(seed,cf);
   const auto* o=CursorObservation;
   require(o[0]==seed,"full accumulator not restored");require(o[1]==o[RegisterCount],"SP changed");
   for(unsigned i=2;i<RegisterCount;++i)require(o[i]==ExpectedRegisters[i],"GPR changed");
   require((o[RegisterCount+1]&1)==cf,"entry CF");
   require((o[RegisterCount+2]&0x8c5)==status(expected),"defined XOR status flags");
   require((o[RegisterCount+2]&0x400)==(o[RegisterCount+1]&0x400),"direction flag changed");
   require(o[RegisterCount+3]==reinterpret_cast<std::uintptr_t>(CursorMarkerEnd),"endpoint");
   require(get<Word>(CursorPointer)==head,"full cursor not restored");
   require(get<std::uint32_t>(CursorTape+6)==expected,"conditional tape symbol");
   for(std::size_t i=0;i<size;++i){
    const auto* p=CursorMarker+i;if(p>=CursorTape+6&&p<CursorTape+10)continue;
    require(*p==before[i],"exterior code byte changed");
   }
   ++cases;
  }
 }
 require(cases==204800,"case count");
 std::printf("CURSOR %u-bit: PASS 204800 cases; full AX/cursor/GPR/SP/defined flags/endpoint/tape/code frame/unchanged-image reuse\n",unsigned(sizeof(Word)*8));
 return 0;
}catch(const std::exception& e){std::fprintf(stderr,"%s\n",e.what());return 1;}}
