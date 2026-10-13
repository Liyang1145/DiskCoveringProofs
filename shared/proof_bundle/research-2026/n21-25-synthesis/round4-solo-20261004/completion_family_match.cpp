// Witness proposals for fixed-order topology-conditioned lower payments only.
#include <functional>
#include <sstream>
#include <unordered_map>
#define main frozen_degree_main
#define visit frozen_degree_visit
#include "../round3-high/peel_degree.cpp"
#undef visit
#undef main
#include "../round3-high/paid_outer_matcher.inc"
#include "completion_family_matcher.inc"

int main(int argc,char**argv){try{
 if(argc!=6)throw runtime_error("usage: completion-match N B library requests output");
 n=stoi(argv[1]);b=stoi(argv[2]);
 if(n!=25||b<3||b>n)throw runtime_error("completion matching requires N25 and valid B");
 load_completion_obstacles(argv[3]);
 ifstream input(argv[4]);if(!input)throw runtime_error("completion requests open");
 string line;vector<PaidMatch> answers;
 while(getline(input,line)){
  istringstream row(line);int index,F;
  if(!(row>>index>>F)||index!=(int)answers.size()||F<1||F>MAXF)
   throw runtime_error("completion request bounds");
  vector<uint32_t> faces;
  for(int j=0;j<F;j++){
   uint64_t value;
   if(!(row>>value)||value>=(uint64_t(1)<<n)||pop(uint32_t(value))!=3||
      !(value&((uint32_t(1)<<b)-1)))throw runtime_error("completion request face");
   faces.push_back(value);
  }
  string extra;
  if(row>>extra||!is_sorted(faces.begin(),faces.end())||
     adjacent_find(faces.begin(),faces.end())!=faces.end())
   throw runtime_error("completion request order/extra");
  answers.push_back(contained_completion(faces));
 }
 if(!input.eof())throw runtime_error("completion requests read");
 ofstream out(argv[5]);if(!out)throw runtime_error("completion output open");
 out<<"{\"scope\":\"N25 equal-outer-face topology-conditioned payment maps only\",\"matches\":[";
 for(size_t i=0;i<answers.size();i++){
  if(i)out<<",";auto const&m=answers[i];
  out<<"{\"request\":"<<i<<",\"pattern\":"<<m.id<<",\"centers\":[";
  for(size_t j=0;j<m.centers.size();j++){if(j)out<<",";out<<m.centers[j];}
  out<<"],\"anchors\":[";
  for(size_t j=0;j<m.anchors.size();j++){if(j)out<<",";out<<m.anchors[j];}
  out<<"],\"orientation\":"<<m.sign<<",\"shift\":"<<m.shift<<"}";
 }
 out<<"]}\n";out.close();if(!out)throw runtime_error("completion output write");
 return 0;
}catch(exception const&e){cerr<<"REJECTED "<<e.what()<<"\n";return 1;}}
