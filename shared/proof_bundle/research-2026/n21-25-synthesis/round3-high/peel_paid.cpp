// Source-derived exact peeling, with already-replayed strict graph obstacles.
// The immutable degree kernel is preserved. No optimizer or local theorem
// enters this program. The launcher must content-bind the paid pattern table.
#include <functional>
#include <sstream>
#include <unordered_map>
#define main paid_enum_main
#include "peel_paid_kernel.inc"
#undef main

// A separate read-only matching mode tests actual emitted maps without a
// topology search. Its output does not assert catalogue completeness.
int main(int argc,char** argv) {
 if(argc<2||string(argv[1])!="match")return paid_enum_main(argc,argv);
 try{
  if(argc!=7)throw runtime_error("usage: paid-peel match N B paid-table requests output");
  n=stoi(argv[2]);b=stoi(argv[3]);
  if(b<3||n<b||n>MAXN)throw runtime_error("match parameter bounds");
  load_obstacles(argv[4]);
  ifstream requests(argv[5]);if(!requests)throw runtime_error("match requests open");
  vector<pair<int,PaidMatch>> answers;
  string line;
  while(getline(requests,line)){
   istringstream row(line);int id,F;
   if(!(row>>id>>F)||id!=(int)answers.size()||F<1||F>MAXF)
    throw runtime_error("match request header");
   vector<uint32_t> raw;
   for(int j=0;j<F;j++){
    uint64_t mask;
    if(!(row>>mask)||mask>=(uint64_t(1)<<n)||pop(uint32_t(mask))!=3||
       pop(uint32_t(mask)&((uint32_t(1)<<b)-1))<2)
     throw runtime_error("match request face");
    raw.push_back(uint32_t(mask));
   }
   string extra;if(row>>extra)throw runtime_error("match extra columns");
   if(!is_sorted(raw.begin(),raw.end())||adjacent_find(raw.begin(),raw.end())!=raw.end())
    throw runtime_error("match repeated or unordered face");
   answers.emplace_back(id,canonical_paid(raw));
  }
  if(!requests.eof())throw runtime_error("match request read failure");
  ofstream out(argv[6]);if(!out)throw runtime_error("match output open");
  out<<"{\"scope\":\"pattern maps only, not enumeration\",\"matches\":[";
  bool comma=false;
  for(auto const& [id,match]:answers){
   if(comma)out<<",";comma=true;
   out<<"{\"request\":"<<id<<",\"obstacle\":"<<match.id<<",\"centers\":[";
   for(size_t j=0;j<match.centers.size();j++){if(j)out<<",";out<<match.centers[j];}
   out<<"],\"anchors\":[";
   for(size_t j=0;j<match.anchors.size();j++){if(j)out<<",";out<<match.anchors[j];}
   out<<"],\"orientation\":"<<match.sign<<",\"shift\":"<<match.shift<<"}";
  }
  out<<"]}\n";out.close();if(!out)throw runtime_error("match output write");
  return 0;
 }catch(exception const& e){cerr<<"REJECTED "<<e.what()<<"\n";return 1;}
}
