// New over-approximating necessary outer-collar enumeration.
// Frozen peeling/angle/degree routines are included, never edited.
// Regions with no original boundary vertex may be left untriangulated.
// This lists weaker graphs, not complete disk triangulations or covers.
#include <functional>
#include <sstream>
#include <unordered_map>
#include <unistd.h>
#define main frozen_degree_main
#define visit frozen_degree_visit
#include "../round3-high/peel_degree.cpp"
#undef visit
#undef main
#include "../round3-high/paid_outer_matcher.inc"
#include "sparse_outer_matcher.inc"

map<vector<uint32_t>,int> collars;
uint64_t omitted_regions=0;
constexpr size_t COLLAR_MEMORY_LIMIT=2000000;

pair<vector<uint32_t>,int> collar_code(vector<uint32_t> const& raw) {
 array<uint32_t,MAXN> adj{};
 uint32_t used=0;
 for(auto mask:raw){
  used|=mask;
  for(int v=0;v<n;v++)if(mask>>v&1)adj[v]|=mask^(uint32_t(1)<<v);
 }
 if((used&((uint32_t(1)<<b)-1))!=(uint32_t(1)<<b)-1)
  throw runtime_error("collar lost original boundary vertex");
 vector<int> minimum;
 vector<pair<int,int>> roots;
 for(int sign:{1,-1})for(int shift=0;shift<b;shift++){
  vector<int> profile;
  for(int j=0;j<b;j++)profile.push_back(pop(adj[(shift+sign*j+b)%b]));
  if(minimum.empty()||profile<minimum){minimum=profile;roots.clear();}
  if(profile==minimum)roots.emplace_back(shift,sign);
 }
 vector<uint32_t> best;
 int centers_needed=pop(used);
 for(auto [shift,sign]:roots){
  array<int,MAXN> label;label.fill(-1);
  vector<int> centers;
  for(int j=0;j<b;j++){
   int v=(shift+sign*j+b)%b;
   label[v]=j;centers.push_back(v);
  }
  map<pair<int,uint32_t>,vector<int>> colors;
  for(int v=b;v<n;v++)if(used>>v&1){
   uint32_t neighbors=0;
   for(int w=0;w<b;w++)if(adj[v]>>w&1)neighbors|=uint32_t(1)<<label[w];
   colors[{pop(adj[v]),neighbors}].push_back(v);
  }
  vector<vector<int>> blocks;
  for(auto const& entry:colors)blocks.push_back(entry.second);
  function<void(size_t)> permute=[&](size_t k){
   if(k==blocks.size()){
    vector<uint32_t> code;
    for(auto face:raw){
     uint32_t image=0;
     for(int v=0;v<n;v++)if(face>>v&1){
      if(label[v]<0)throw runtime_error("collar partial unassigned label");
      image|=uint32_t(1)<<label[v];
     }
     code.push_back(image);
    }
    sort(code.begin(),code.end());
    if(best.empty()||code<best)best=code;
    return;
   }
   auto order=blocks[k];
   sort(order.begin(),order.end());
   do {
    auto oldsize=centers.size();
    for(int v:order){label[v]=centers.size();centers.push_back(v);}
    permute(k+1);
    centers.resize(oldsize);
    for(int v:order)label[v]=-1;
   }while(next_permutation(order.begin(),order.end()));
  };
  permute(0);
 }
 if(best.empty()||centers_needed<b||centers_needed>n)
  throw runtime_error("bad collar canonical code");
 uint32_t labeled=0;
 for(auto face:best)labeled|=face;
 if(labeled!=(uint32_t(1)<<centers_needed)-1)
  throw runtime_error("unused compressed collar label");
 return {best,centers_needed};
}

void visit_collar(State s,vector<Region> pending,int omitted_faces){
 calls++;
 if(limit&&calls>=limit)throw runtime_error("NODE LIMIT: incomplete collar search, no completion");
 // A dropped region has no original boundary vertex. No triangle in any
 // completion of it can be an outer face. Its unexposed budget is reserved,
 // and its Euler face budget is retained only as an accounting invariant.
 for(size_t j=0;j<pending.size();){
  auto const& task=pending[j];
  bool original_boundary=false;
  for(int v:task.boundary)if(v<b)original_boundary=true;
  if(original_boundary){j++;continue;}
  int size=task.boundary.size(),inside=task.interior;
  if(size==2){if(inside)return;}
  else if(size<3||inside<0||size+inside>n)
   throw runtime_error("invalid dropped collar region");
  s.next+=inside;
  omitted_faces+=2*inside+size-2;
  if(s.next>n)throw runtime_error("collar reserved vertex budget overflow");
  omitted_regions++;
  pending.erase(pending.begin()+j);
 }
 if(calls%1000000==0)cerr<<"COLLAR PROGRESS B="<<b<<" calls="<<calls
  <<" weak_graphs="<<collars.size()<<" omitted_regions="<<omitted_regions
  <<" proof_prunes="<<proof_prunes<<" sparse_prunes="<<sparse_prunes<<" seconds="
  <<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<"\n";
 bool exposed_to_future[MAXN]{};
 for(auto const& region:pending)for(int v:region.boundary)exposed_to_future[v]=true;
 int root_degree=pop(s.adjacency[0]);
 for(int v=1;v<b;v++)if(!exposed_to_future[v]&&pop(s.adjacency[v])<root_degree){
  prunes++;return;
 }
 if(already_sparse_paid(s))return;
 if(already_paid(s))return;
 if(pending.empty()){
  if(s.next!=n||s.count+omitted_faces!=faces_needed)
   throw runtime_error("collar complete Euler/budget accounting mismatch");
  vector<uint32_t> raw;
  for(int f=0;f<s.count;f++)
   if(pop(s.faces[f]&((uint32_t(1)<<b)-1))>=1)raw.push_back(s.faces[f]);
  sort(raw.begin(),raw.end());
  auto [code,centers_needed]=collar_code(raw);rooted++;
  auto [iterator,fresh]=collars.emplace(code,centers_needed);
  if(!fresh&&iterator->second!=centers_needed)throw runtime_error("collar center count conflict");
  if(collars.size()>COLLAR_MEMORY_LIMIT)
   throw runtime_error("MEMORY LIMIT: collar catalogue incomplete");
  return;
 }
 int pick=pending.size()-1;
 if(audit_order)for(int j=0;j<(int)pending.size();j++){
  if(pending[j].interior<pending[pick].interior||
     (pending[j].interior==pending[pick].interior&&pending[j].boundary.size()>pending[pick].boundary.size()))pick=j;
 }
 Region task=pending[pick];pending.erase(pending.begin()+pick);
 auto boundary=task.boundary;int size=boundary.size(),inside=task.interior;
 if(size==2){if(!inside)visit_collar(s,pending,omitted_faces);return;}
 if(size<3||inside<0||size+inside>n)throw runtime_error("invalid pending region");
 int a=boundary[0],c=boundary[1];
 for(int jj=2;jj<size;jj++){
  int k=audit_order?size+1-jj:jj,w=boundary[k];
  if(k>2&&(s.adjacency[c]>>w&1))continue;
  if(k<size-1&&(s.adjacency[a]>>w&1))continue;
  State next=s;
  bool changed=false;
  for(auto edge:vector<pair<int,int>>{{a,w},{c,w}}){
   if(!(next.adjacency[edge.first]>>edge.second&1))changed=true;
   next.adjacency[edge.first]|=uint32_t(1)<<edge.second;
   next.adjacency[edge.second]|=uint32_t(1)<<edge.first;
  }
  if(next.count>=faces_needed)throw runtime_error("too many faces");
  next.faces[next.count++]=(uint32_t(1)<<a)|(uint32_t(1)<<c)|(uint32_t(1)<<w);
  if(changed&&!possible(next)){prunes++;continue;}
  vector<int> left{w},right{a};
  for(int j=1;j<k;j++)left.push_back(boundary[j]);
  for(int j=k;j<size;j++)right.push_back(boundary[j]);
  for(int j=0;j<=inside;j++){
   int left_inside=audit_order?inside-j:j;
   if((left.size()==2&&left_inside)||(right.size()==2&&inside-left_inside))continue;
   auto work=pending;
   if(!audit_order){work.push_back({right,inside-left_inside});work.push_back({left,left_inside});}
   else{work.push_back({left,left_inside});work.push_back({right,inside-left_inside});}
   visit_collar(next,work,omitted_faces);
  }
 }
 if(inside){
  State next=s;int v=next.next++;
  if(v>=n||next.count>=faces_needed)throw runtime_error("interior/face overflow");
  for(int node:{a,c}){next.adjacency[v]|=uint32_t(1)<<node;next.adjacency[node]|=uint32_t(1)<<v;}
  next.faces[next.count++]=(uint32_t(1)<<a)|(uint32_t(1)<<c)|(uint32_t(1)<<v);
  if(!possible(next)){prunes++;return;}
  vector<int> polygon{a,v};
  for(int j=1;j<size;j++)polygon.push_back(boundary[j]);
  pending.push_back({polygon,inside-1});
  visit_collar(next,pending,omitted_faces);
 }
}

int bounded_production_entry(int argc,char**argv){try{
 if(argc!=12)throw runtime_error("usage: sparse-collar N B output scale cap2 cap4 cap6 node-limit mode exact-table-or-minus sparse-table-or-minus");
 n=stoi(argv[1]);b=stoi(argv[2]);string output=argv[3];
 scale=stoll(argv[4]);for(int j=0;j<3;j++)caps[j]=stoll(argv[5+j]);limit=stoull(argv[8]);
 string mode=argv[9];audit_order=mode.find("audit")!=string::npos;screen=mode.find("noscreen")==string::npos;
 if(n>MAXN||b<3||n<b||scale<=0||scale>100000000||caps[0]<=0||caps[2]>=scale/2)
  throw runtime_error("parameter bounds");
 faces_needed=2*n-b-2;if(faces_needed>MAXF)throw runtime_error("face bitset bound");
 load_obstacles(argv[10]);
 load_sparse_obstacles(argv[11]);
 State initial;initial.next=b;
 for(int i=0;i<b;i++){int j=(i+1)%b;initial.adjacency[i]|=uint32_t(1)<<j;initial.adjacency[j]|=uint32_t(1)<<i;}
 vector<int> boundary(b);iota(boundary.begin(),boundary.end(),0);
 if(audit_order)rotate(boundary.begin(),boundary.begin()+b/2,boundary.end());
 started=chrono::steady_clock::now();
 cerr<<"COLLAR NATIVE PID="<<getpid()<<" N="<<n<<" B="<<b<<"\n";
 if(possible(initial))visit_collar(initial,{{boundary,n-b}},0);else prunes++;
 ofstream out(output);if(!out)throw runtime_error("collar output open");
 out<<"{\"schema\":\"outer-collar-overapproximation-v1\",\"complete_necessary_outer_search\":true"
    <<",\"complete_full_triangulations\":false,\"N\":"<<n<<",\"B\":"<<b
    <<",\"screen\":"<<(screen?"true":"false")<<",\"mode\":\""<<mode<<"\",\"scale\":"<<scale
    <<",\"caps\":["<<caps[0]<<","<<caps[1]<<","<<caps[2]<<"],\"calls\":"<<calls
    <<",\"omitted_internal_regions_not_type_count\":"<<omitted_regions
    <<",\"weak_graph_count\":"<<collars.size();
 write_paid_summary(out);
 write_sparse_summary(out);
 out<<",\"weak_graphs\":[";
 bool comma=false;
 for(auto const& [code,centers_needed]:collars){
  if(comma)out<<",";comma=true;
  out<<"{\"centers\":"<<centers_needed<<",\"faces\":[";
  for(size_t j=0;j<code.size();j++){if(j)out<<",";out<<code[j];}
  out<<"]}";
 }
 out<<"]}\n";out.close();if(!out)throw runtime_error("collar output write");
 cerr<<"COLLAR SEARCH COMPLETE B="<<b<<" calls="<<calls<<" weak_graphs="<<collars.size()
     <<" proof_prunes="<<proof_prunes<<" sparse_prunes="<<sparse_prunes<<"\n";
 return 0;
}catch(exception const&e){cerr<<"REJECTED "<<e.what()<<"\n";return 1;}}
