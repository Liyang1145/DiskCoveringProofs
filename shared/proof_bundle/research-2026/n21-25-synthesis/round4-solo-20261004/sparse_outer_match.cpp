// Read-only prototype; does not perform or certify a full necessary search.
#include <functional>
#include <sstream>
#include <unordered_map>
#define main frozen_degree_main
#define visit frozen_degree_visit
#include "../round3-high/peel_degree.cpp"
#undef visit
#undef main
#include "../round3-high/paid_outer_matcher.inc"
#include "sparse_outer_matcher.inc"

int main(int argc,char**argv){try{
 if(argc!=7||string(argv[1])!="match")
  throw runtime_error("usage: sparse match N B table requests output");
 n=stoi(argv[2]);b=stoi(argv[3]);
 if(b<3||n<b||n>MAXN)throw runtime_error("sparse match bounds");
 load_sparse_obstacles(argv[4]);
 ifstream input(argv[5]);if(!input)throw runtime_error("sparse requests open");
 vector<PaidMatch> answers;string line;
 while(getline(input,line)){
  istringstream row(line);int index,F;
  if(!(row>>index>>F)||index!=(int)answers.size()||F<1||F>MAXF)
   throw runtime_error("sparse request header");
  vector<uint32_t> faces;
  for(int j=0;j<F;j++){
   uint64_t mask;
   if(!(row>>mask)||mask>=(uint64_t(1)<<n)||pop(uint32_t(mask))!=3||
      pop(uint32_t(mask)&((uint32_t(1)<<b)-1))<1)throw runtime_error("sparse request face");
   faces.push_back(mask);
  }
  string extra;
  if(row>>extra||!is_sorted(faces.begin(),faces.end())||
     adjacent_find(faces.begin(),faces.end())!=faces.end())
   throw runtime_error("sparse request order/extra");
  answers.push_back(contained_sparse(faces));
 }
 if(!input.eof())throw runtime_error("sparse requests read");
 ofstream out(argv[6]);if(!out)throw runtime_error("sparse answers open");
 out<<"{\"scope\":\"sparse subgraph maps only\",\"matches\":[";
 for(size_t i=0;i<answers.size();i++){
  if(i)out<<",";auto const& m=answers[i];
  out<<"{\"request\":"<<i<<",\"obstacle\":"<<m.id<<",\"centers\":[";
  for(size_t j=0;j<m.centers.size();j++){if(j)out<<",";out<<m.centers[j];}
  out<<"],\"anchors\":[";
  for(size_t j=0;j<m.anchors.size();j++){if(j)out<<",";out<<m.anchors[j];}
  out<<"],\"orientation\":"<<m.sign<<",\"shift\":"<<m.shift<<"}";
 }
 out<<"]}\n";out.close();if(!out)throw runtime_error("sparse answers write");
 return 0;
}catch(exception const&e){cerr<<"REJECTED "<<e.what()<<"\n";return 1;}}
