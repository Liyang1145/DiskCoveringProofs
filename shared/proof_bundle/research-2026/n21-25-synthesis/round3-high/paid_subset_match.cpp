// Read-only prototype: a strict pair-face obstacle may be contained in,
// rather than equal to, the current weak graph. No active kernel is edited.
#include <functional>
#include <sstream>
#include <unordered_map>
#include <filesystem>
#include <memory>
#define main original_paid_enum_main
#include "peel_paid_stream_kernel.inc"
#undef main

struct SubsetVariant {
 int id,centers,shift,sign;
 vector<int> boundary,degree;
 vector<uint32_t> all_boundary;
 vector<vector<uint32_t>> required;
};
vector<SubsetVariant> subset_variants;

void prepare_subset_variants() {
 for(auto const& [code,pattern]:paid_patterns)
  for(int sign:{1,-1})for(int shift=0;shift<b;shift++){
   SubsetVariant v{pattern.id,pattern.centers,shift,sign};
   v.degree.assign(b,0);v.required.resize(pattern.centers-b);
   for(int j=0;j<b;j++)v.boundary.push_back((shift+sign*j+b)%b);
   for(uint32_t mask:pattern.faces){
    uint32_t pair=0;int inside=-1;
    for(int j=0;j<pattern.centers;j++)if(mask>>j&1){
     if(j<b){pair|=uint32_t(1)<<v.boundary[j];v.degree[v.boundary[j]]++;}
     else{if(inside>=0)throw runtime_error("not a pair-face obstacle");inside=j-b;}
    }
    if(inside<0)v.all_boundary.push_back(pair);
    else v.required[inside].push_back(pair);
   }
   sort(v.all_boundary.begin(),v.all_boundary.end());
   for(auto& sig:v.required){sort(sig.begin(),sig.end());if(sig.empty())throw runtime_error("unused inside label");}
   subset_variants.push_back(move(v));
  }
}

PaidMatch contained_paid(vector<uint32_t> const& raw) {
 vector<uint32_t> all_boundary;
 vector<vector<uint32_t>> signature(n-b);
 vector<int> degree(b,0),used;
 auto boundary_mask=(uint32_t(1)<<b)-1;
 for(uint32_t mask:raw){
  auto pair=mask&boundary_mask,inside=mask^pair;
  for(int j=0;j<b;j++)if(pair>>j&1)degree[j]++;
  if(!inside)all_boundary.push_back(pair);
  else{
   if(pop(inside)!=1||pop(pair)!=2)throw runtime_error("subset request not pair faces");
   signature[first(inside)-b].push_back(pair);
  }
 }
 sort(all_boundary.begin(),all_boundary.end());
 for(int i=0;i<n-b;i++){
  sort(signature[i].begin(),signature[i].end());
  if(!signature[i].empty())used.push_back(i);
 }
 for(auto const& v:subset_variants){
  int K=v.centers-b;
  if(K>(int)used.size())continue;
  bool valid=true;
  for(int j=0;j<b;j++)if(v.degree[j]>degree[j]){valid=false;break;}
  if(!valid||!includes(all_boundary.begin(),all_boundary.end(),
                       v.all_boundary.begin(),v.all_boundary.end()))continue;
  vector<vector<int>> domains(K);
  for(int i=0;i<K;i++){
   for(int k:used)if(includes(signature[k].begin(),signature[k].end(),
                             v.required[i].begin(),v.required[i].end()))domains[i].push_back(k);
   if(domains[i].empty()){valid=false;break;}
  }
  if(!valid)continue;
  vector<int> owner(n-b,-1),order(K),assigned(K,-1);
  iota(order.begin(),order.end(),0);
  sort(order.begin(),order.end(),[&](int a,int c){return domains[a].size()<domains[c].size();});
  function<bool(int,vector<bool>&)> augment=[&](int i,vector<bool>& seen){
   for(int k:domains[i])if(!seen[k]){
    seen[k]=true;
    if(owner[k]<0||augment(owner[k],seen)){owner[k]=i;return true;}
   }
   return false;
  };
  for(int i:order){vector<bool> seen(n-b);if(!augment(i,seen)){valid=false;break;}}
  if(!valid)continue;
  for(int k:used)if(owner[k]>=0)assigned[owner[k]]=b+k;
  PaidMatch result;result.id=v.id;result.shift=v.shift;result.sign=v.sign;
  result.centers=v.boundary;
  result.centers.insert(result.centers.end(),assigned.begin(),assigned.end());
  for(int j=0;j<b;j++)result.anchors.push_back((v.shift+v.sign*j-(v.sign<0)+2*b)%b);
  set<int> distinct(result.centers.begin(),result.centers.end());
  if((int)distinct.size()!=v.centers||distinct.count(-1))throw runtime_error("subset noninjection");
  // Every successful hit is explicitly checked, independent of matching.
  auto pattern=find_if(paid_patterns.begin(),paid_patterns.end(),
                      [&](auto const& entry){return entry.second.id==result.id;});
  if(pattern==paid_patterns.end())throw runtime_error("subset unknown obstacle");
  for(uint32_t face:pattern->second.faces){
   uint32_t image=0;
   for(int j=0;j<v.centers;j++)if(face>>j&1)image|=uint32_t(1)<<result.centers[j];
   if(!binary_search(raw.begin(),raw.end(),image))throw runtime_error("subset missing image face");
  }
  for(int j=0;j<b;j++)if(set<int>{result.centers[j],result.centers[(j+1)%b]}!=
                        set<int>{result.anchors[j],(result.anchors[j]+1)%b})
   throw runtime_error("subset boundary rod transport");
  return result;
 }
 return {};
}

int main(int argc,char** argv){try{
 if(argc!=6)throw runtime_error("usage: subset-match N B strict-table requests output");
 n=stoi(argv[1]);b=stoi(argv[2]);
 if(b<3||n<b||n>MAXN)throw runtime_error("subset dimensions");
 load_obstacles(argv[3]);prepare_subset_variants();
 ifstream requests(argv[4]);if(!requests)throw runtime_error("subset requests open");
 if(filesystem::exists(argv[5]))throw runtime_error("refuse output overwrite");
 ofstream out(argv[5]);if(!out)throw runtime_error("subset output open");
 out<<"{\"scope\":\"read-only strict subset maps; not search or global proof\",\"matches\":[";
 string line;int count=0;
 while(getline(requests,line)){
  istringstream row(line);int id,F;
  if(!(row>>id>>F)||id!=count||F<1||F>MAXF)throw runtime_error("subset request header");
  vector<uint32_t> raw;
  for(int j=0;j<F;j++){
   uint64_t mask;
   if(!(row>>mask)||mask>=(uint64_t(1)<<n)||pop(uint32_t(mask))!=3||
      pop(uint32_t(mask)&((uint32_t(1)<<b)-1))<2)throw runtime_error("subset request face");
   raw.push_back(uint32_t(mask));
  }
  string extra;if(row>>extra)throw runtime_error("subset extra columns");
  if(!is_sorted(raw.begin(),raw.end())||adjacent_find(raw.begin(),raw.end())!=raw.end())
   throw runtime_error("subset request repeated/unsorted");
  auto legacy=canonical_paid(raw),match=contained_paid(raw);
  if(count)out<<",";count++;
  out<<"{\"request\":"<<id<<",\"legacy_exact_obstacle\":"<<legacy.id
     <<",\"obstacle\":"<<match.id<<",\"centers\":[";
  for(size_t j=0;j<match.centers.size();j++){if(j)out<<",";out<<match.centers[j];}
  out<<"],\"anchors\":[";
  for(size_t j=0;j<match.anchors.size();j++){if(j)out<<",";out<<match.anchors[j];}
  out<<"],\"orientation\":"<<match.sign<<",\"shift\":"<<match.shift<<"}";
 }
 if(!requests.eof())throw runtime_error("subset requests read");
 out<<"]}\n";out.close();if(!out)throw runtime_error("subset output write");
 cerr<<"SUBSET MAPS COMPLETE requests="<<count<<" variants="<<subset_variants.size()<<"\n";
 return 0;
}catch(exception const& e){cerr<<"REJECTED "<<e.what()<<"\n";return 1;}}
