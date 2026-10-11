#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>
extern "C" unsigned char TransferBegin[],TransferEnd[],TransferSource[],TransferDestination[],TransferWrongSource[],TransferWrongDestination[],TransferPrinted[];
extern "C" std::uintptr_t TransferObservation[18],TransferIndexSeeds[2],TransferFixtures[][8];
extern "C" unsigned TransferFixtureCount;
extern "C" void TransferInvoke(void*,std::uintptr_t,std::uintptr_t);
static std::uintptr_t address(const unsigned char* p){return reinterpret_cast<std::uintptr_t>(p);}
static unsigned char* pointer(std::uintptr_t p){return reinterpret_cast<unsigned char*>(p);}
static std::uintptr_t read(const unsigned char* p){std::uintptr_t v;std::memcpy(&v,p,sizeof(v));return v;}
static void write(unsigned char* p,std::uintptr_t v){std::memcpy(p,&v,sizeof(v));}
static std::uint64_t random(std::uint64_t& v){v^=v<<13;v^=v>>7;v^=v<<17;return v;}
static constexpr std::uintptr_t expected[]={0x13579bdf,0x2468ace0,0x0badc0de,0x11223344,0x55667788,0x76543210,0x10203040,0x50607080,0x90a0b0c0,0xd0e0f001,0x23456789,0xabcdef01,0x31415926,0x27182818};
int main(){
 FILE* f=nullptr;if(fopen_s(&f,"transfer-packets.json","w")||!f)return 2;
 std::fputs("[",f);
 for(unsigned fi=0;fi<TransferFixtureCount;++fi){auto& row=TransferFixtures[fi];auto start=pointer(row[2]);auto stop=pointer(row[3]);auto size=address(stop)-address(start);
  std::fprintf(f,"%s{\"size\":%llu,\"offset\":%llu,\"start\":%llu,\"end\":%llu,\"sourceField\":%llu,\"destinationField\":%llu,\"body\":%llu,\"bodyEnd\":%llu,\"source\":%llu,\"destination\":%llu,\"bytes\":[",fi?",":"",
   static_cast<unsigned long long>(row[0]),static_cast<unsigned long long>(row[1]),static_cast<unsigned long long>(row[2]),static_cast<unsigned long long>(row[3]),
   static_cast<unsigned long long>(row[4]),static_cast<unsigned long long>(row[5]),static_cast<unsigned long long>(row[6]),static_cast<unsigned long long>(row[7]),
   static_cast<unsigned long long>(address(TransferSource)+row[1]),static_cast<unsigned long long>(address(TransferDestination)+row[1]));
  for(std::uintptr_t i=0;i<size;++i)std::fprintf(f,"%s%u",i?",":"",start[i]);std::fputs("]}",f);
 }
 std::fputs("]\n",f);std::fclose(f);
 for(unsigned i=0;i<640;++i){TransferSource[i]=static_cast<unsigned char>(i*17+3);TransferDestination[i]=static_cast<unsigned char>(i*29+5);TransferWrongSource[i]=static_cast<unsigned char>(i*41+7);TransferWrongDestination[i]=static_cast<unsigned char>(i*43+11);}
 write(TransferSource,address(TransferWrongSource));write(TransferDestination,address(TransferWrongDestination));
 unsigned char sourceBefore[640],destBefore[640],wrongBefore[640];std::memcpy(sourceBefore,TransferSource,640);std::memcpy(destBefore,TransferDestination,640);std::memcpy(wrongBefore,TransferWrongSource,640);
 TransferIndexSeeds[0]=0x13579bdf;TransferIndexSeeds[1]=0x2468ace0;
 TransferInvoke(TransferPrinted,0x11223344,1);
 if(std::memcmp(TransferSource,sourceBefore,640)||std::memcmp(TransferDestination,destBefore,640)||std::memcmp(TransferWrongDestination,wrongBefore,16))return 3;
 std::puts("Typed printed TRANSFERDATA baseline: declared cursor fields unused; intended buffers restored/unchanged; pointer-valued payload selects other buffers");
 const auto codeSize=address(TransferEnd)-address(TransferBegin);std::vector<unsigned char> snapshot(codeSize);
 std::uint64_t rng=0x71905dce43a9b682ULL;unsigned cases=0;
 for(unsigned fi=0;fi<TransferFixtureCount;++fi){auto& row=TransferFixtures[fi];auto size=row[0],offset=row[1];
  if(size+offset>640||read(pointer(row[4]))!=address(TransferSource)+offset||read(pointer(row[5]))!=address(TransferDestination)+offset)return 4;
  for(unsigned cf=0;cf<2;++cf)for(unsigned trial=0;trial<32;++trial){
   for(unsigned i=0;i<640;++i){TransferSource[i]=static_cast<unsigned char>(random(rng));TransferDestination[i]=static_cast<unsigned char>(random(rng));}
   std::memcpy(sourceBefore,TransferSource,640);std::memcpy(destBefore,TransferDestination,640);std::memcpy(snapshot.data(),TransferBegin,codeSize);
   TransferIndexSeeds[0]=static_cast<std::uintptr_t>(random(rng));TransferIndexSeeds[1]=static_cast<std::uintptr_t>(random(rng));auto seed=static_cast<std::uintptr_t>(random(rng));
   FlushInstructionCache(GetCurrentProcess(),TransferBegin,codeSize); // Host initialization only.
   for(unsigned call=0;call<2;++call){
    auto accumulator=sizeof(void*)==8?read(TransferDestination+offset):seed;
    TransferInvoke(pointer(row[2]),seed,cf);
    if(TransferObservation[0]!=accumulator||TransferObservation[1]!=TransferObservation[17]||(TransferObservation[16]&1)!=0)return 5;
    const unsigned registers=sizeof(void*)==8?14:6;for(unsigned i=0;i<registers;++i){auto value=i==3?TransferIndexSeeds[0]:i==4?TransferIndexSeeds[1]:expected[i];if(TransferObservation[i+2]!=value)return 6;}
    if(std::memcmp(TransferSource,sourceBefore,640))return 7;
    for(unsigned i=0;i<640;++i){auto value=i>=offset&&i<offset+size?sourceBefore[i]:destBefore[i];if(TransferDestination[i]!=value)return 8;}
    if(std::memcmp(TransferBegin,snapshot.data(),codeSize))return 9;
    if(read(pointer(row[4]))!=address(TransferSource)+offset||read(pointer(row[5]))!=address(TransferDestination)+offset)return 10;
    ++cases;
   }
  }
 }
 std::printf("TRANSFERDATA %u-bit: PASS %u executions; %u sizes (0..35/all tails/127/128/513, arbitrary full SI/DI, source/destination/cursor/all GPRs/SP/CF/entire code frame, repeat)\n",unsigned(sizeof(void*)*8),cases,TransferFixtureCount);
 return 0;
}
