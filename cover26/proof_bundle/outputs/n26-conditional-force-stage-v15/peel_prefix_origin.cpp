// N21..25 synthesis kernel, derived from the bound N21 source without editing it.
// Derived method: pinned DiskCoveringSolve cover20 DFS/BFS manuscripts.
// New configurable code: no inherited n20 numeric caps; no optimizer trusted.
// A node limit exits nonzero BEFORE writing any complete output.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <filesystem>
#include <functional>
#include <iostream>
#include <map>
#include <numeric>
#include <queue>
#include <set>
#include <stdexcept>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
// Exploratory N26 prefix partitioner. The geometric screen is inherited;
// exhaustion of a named subtree is not a proof of arbitrary-cover reduction.
constexpr int MAXN=26,MAXF=47;
int n,b,faces_needed;
long long scale,caps[4];
bool screen=true,audit_order=false;
bool origin_screen=false;
uint64_t origin_prunes=0;
uint64_t calls=0,prunes=0,rooted=0,limit=0;
auto started=chrono::steady_clock::now();
struct Region{vector<int> boundary;int interior;};
struct State{
 array<uint32_t,MAXN> adjacency{};
 array<uint32_t,MAXF> faces{};
 int next=0,count=0;
};
map<vector<uint32_t>,int> survivors;
int pop(uint32_t x){return __builtin_popcount(x);}
int first(uint32_t x){if(!x)throw runtime_error("empty bitset");return __builtin_ctz(x);}

bool possible(State const&s){
 // Necessary for an actual cover with rho < U < 1/4, not for
 // arbitrary weak graph realizability. Already-added edges persist.
 if(origin_screen){
  uint32_t exposed=(uint32_t(1)<<b)-1;
  for(int i=0;i<b;i++)exposed|=s.adjacency[i];
  if(exposed==(uint32_t(1)<<n)-1){origin_prunes++;return false;}
 }
 if(!screen)return true;
 uint32_t one[MAXN]{},two[MAXN]{},three[MAXN]{};
 for(int i=0;i<n;i++)one[i]=s.adjacency[i]|(uint32_t(1)<<i);
 for(int i=0;i<n;i++){
  auto mask=one[i],value=mask;
  while(mask){int j=first(mask);mask&=mask-1;value|=one[j];}
  two[i]=value;
 }
 for(int i=0;i<n;i++){
  auto mask=two[i],value=uint32_t(0);
  while(mask){int j=first(mask);mask&=mask-1;value|=one[j];}
  three[i]=value;
 }
 vector<array<long long,3>> inequalities;
 for(int i=0;i<b;i++){
  int j=(i+1)%b;
  inequalities.push_back({i,j,caps[0]-(j==0?scale:0)});
  inequalities.push_back({j,i,j==0?scale:0});
 }
 for(int i=0;i<b;i++){
  auto reach1=one[i]|one[(i+1)%b],reach2=two[i]|two[(i+1)%b],
       reach3=three[i]|three[(i+1)%b];
  for(int j=i+1;j<b;j++){
   auto ends=(uint32_t(1)<<j)|(uint32_t(1)<<((j+1)%b));
   long long cap;
   if(reach1&ends)cap=caps[1];
   else if(reach2&ends)cap=caps[2];
   else if(reach3&ends)cap=caps[3];
   else continue;
   int k=j-i;
   if(min(k,b-k)*caps[0]<=cap)continue;
   bool short_forward=k*caps[0]<scale-cap;
   bool short_backward=(b-k)*caps[0]<scale-cap;
   if(short_forward&&short_backward)return false;
   if(short_forward)inequalities.push_back({i,j,cap});
   else if(short_backward)inequalities.push_back({j,i,cap-scale});
  }
 }
 if(!audit_order){
  long long dist[MAXN]{};
  for(int pass=0;pass<b;pass++){
   bool changed=false;
   for(auto edge:inequalities){
    int u=edge[0],v=edge[1];
    if(dist[v]>dist[u]+edge[2]){dist[v]=dist[u]+edge[2];changed=true;}
   }
   if(!changed)return true;
  }
  return false;
 }
 // Alternative closure uses Floyd-Warshall, not Bellman-Ford relaxation.
 constexpr long long INF=1000000000000LL;
 long long dist[MAXN][MAXN];
 for(int i=0;i<b;i++)for(int j=0;j<b;j++)dist[i][j]=i==j?0:INF;
 for(auto edge:inequalities)dist[edge[0]][edge[1]]=min(dist[edge[0]][edge[1]],edge[2]);
 for(int k=0;k<b;k++)for(int i=0;i<b;i++)for(int j=0;j<b;j++)
  dist[i][j]=min(dist[i][j],dist[i][k]+dist[k][j]);
 for(int i=0;i<b;i++)if(dist[i][i]<0)return false;
 return true;
}

pair<vector<uint32_t>,int> canonical(State const&s){
 uint64_t incidence[MAXN][MAXN]{};
 array<int,3> triangles[MAXF];
 set<uint32_t> unique;
 uint32_t used=0;
 for(int f=0;f<s.count;f++){
  uint32_t mask=s.faces[f];
  if(pop(mask)!=3||mask>=(uint32_t(1)<<n)||!unique.insert(mask).second)
   throw runtime_error("invalid or repeated triangle");
  used|=mask;
  for(int k=0;k<3;k++){triangles[f][k]=first(mask);mask&=mask-1;}
  for(int i=0;i<3;i++)for(int j=i+1;j<3;j++){
   int u=triangles[f][i],v=triangles[f][j];
   incidence[u][v]|=uint64_t(1)<<f;incidence[v][u]|=uint64_t(1)<<f;
  }
 }
 if(used!=(uint32_t(1)<<n)-1)throw runtime_error("unused vertex");
 int edge_count=0;
 for(int u=0;u<n;u++)for(int v=u+1;v<n;v++){
  int count=__builtin_popcountll(incidence[u][v]);
  bool boundary=u<b&&v<b&&(v==u+1||(u==0&&v==b-1));
  if(boundary&&count!=1)throw runtime_error("bad boundary edge");
  if(count){edge_count++;if(count!=(boundary?1:2))throw runtime_error("bad interior incidence");}
 }
 if(n-edge_count+s.count!=1)throw runtime_error("bad Euler characteristic");
 for(int v=0;v<n;v++){
  uint32_t link[MAXN]{},vertices=0;
  for(auto face:unique)if(face>>v&1){
   auto rest=face^(uint32_t(1)<<v);int u=first(rest);rest&=rest-1;int w=first(rest);
   link[u]|=uint32_t(1)<<w;link[w]|=uint32_t(1)<<u;vertices|=(uint32_t(1)<<u)|(uint32_t(1)<<w);
  }
  uint32_t endpoints=0;
  for(int u=0;u<n;u++)if(vertices>>u&1){
   int degree=pop(link[u]);if(degree==1)endpoints|=uint32_t(1)<<u;
   else if(degree!=2)throw runtime_error("bad vertex link");
  }
  uint32_t required=v<b?((uint32_t(1)<<((v+b-1)%b))|(uint32_t(1)<<((v+1)%b))):0;
  if(endpoints!=required)throw runtime_error("wrong link endpoints");
  uint32_t reached=uint32_t(1)<<first(vertices),previous=0;
  while(reached!=previous){previous=reached;for(int u=0;u<n;u++)if(reached>>u&1)reached|=link[u];}
  if(reached!=vertices)throw runtime_error("disconnected vertex link");
 }
 vector<uint32_t> best;int stabilizer=0;
 vector<int> minimum_profile;
 vector<pair<int,int>> candidate_roots;
 // Profile is a full-isomorphism invariant. Retain all roots attaining its
 // minimum, not a heuristic subset; stabilizer multiplicities are preserved.
 for(int direction:{1,-1})for(int start=0;start<b;start++){
  vector<int> profile;
  for(int j=0;j<b;j++)profile.push_back(pop(s.adjacency[(start+direction*j+b)%b]));
  if(minimum_profile.empty()||profile<minimum_profile){
   minimum_profile=profile;candidate_roots.clear();
  }
  if(profile==minimum_profile)candidate_roots.emplace_back(start,direction);
 }
 // Same BFS code in both searches: exact surviving-set comparison does not
 // rely on differently ordered internal labels being the same.
 for(auto [start,direction]:candidate_roots){
  int label[MAXN];fill(label,label+n,-1);
  for(int j=0;j<b;j++)label[(start+direction*j+b)%b]=j;
  int end=(start+direction+b)%b;
  auto root=incidence[start][end];
  if(__builtin_popcountll(root)!=1)throw runtime_error("bad root");
  array<int,3> tasks[MAXF];int front=0,back=1;
  tasks[0]={__builtin_ctzll(root),start,end};uint64_t scheduled=root;
  int next=b;vector<uint32_t> code;
  while(front<back){
   auto task=tasks[front++];int f=task[0],u=task[1],v=task[2];
   int w=triangles[f][0]^triangles[f][1]^triangles[f][2]^u^v;
   if(label[w]<0)label[w]=next++;
   if(label[u]<0||label[v]<0)throw runtime_error("unassigned BFS label");
   code.push_back((uint32_t(1)<<label[u])|(uint32_t(1)<<label[v])|(uint32_t(1)<<label[w]));
   for(auto edge:vector<pair<int,int>>{{v,w},{w,u}}){
    auto unseen=incidence[edge.first][edge.second]&~scheduled;
    if(unseen){
     if(__builtin_popcountll(unseen)!=1||back>=MAXF)throw runtime_error("bad BFS adjacency");
     scheduled|=unseen;tasks[back++]={__builtin_ctzll(unseen),edge.first,edge.second};
    }
   }
  }
  if(next!=n||(int)code.size()!=faces_needed)throw runtime_error("disconnected dual or missing vertex");
  sort(code.begin(),code.end());
  if(best.empty()||code<best){best=code;stabilizer=1;}else if(code==best)stabilizer++;
 }
 return {best,stabilizer};
}

int pick_region(vector<Region> const&pending){
 int pick=(int)pending.size()-1;
 if(audit_order)for(int j=0;j<(int)pending.size();j++){
  if(pending[j].interior<pending[pick].interior||
     (pending[j].interior==pending[pick].interior&&pending[j].boundary.size()>pending[pick].boundary.size()))pick=j;
 }
 return pick;
}

void normalize(vector<Region>&pending){
 // Two-edge regions have no triangle choice and consume no prefix index.
 while(!pending.empty()){
  int pick=pick_region(pending);
  auto const&task=pending[pick];
  if(task.boundary.size()!=2)return;
  if(task.interior)throw runtime_error("nonempty digon");
  pending.erase(pending.begin()+pick);
 }
}

template<class Consumer>
int children(State const&s,vector<Region> pending,Consumer consume){
 normalize(pending);
 if(pending.empty())return 0;
 int pick=pick_region(pending);
 Region task=pending[pick];pending.erase(pending.begin()+pick);
 auto boundary=task.boundary;int size=boundary.size(),inside=task.interior;
 if(size<3||inside<0||size+inside>n)throw runtime_error("invalid pending region");
 int a=boundary[0],c=boundary[1],branch=0;
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
   consume(branch++,next,work);
  }
 }
 if(inside){
  State next=s;int v=next.next++;
  if(v>=n||next.count>=faces_needed)throw runtime_error("interior/face overflow");
  for(int node:{a,c}){next.adjacency[v]|=uint32_t(1)<<node;next.adjacency[node]|=uint32_t(1)<<v;}
  next.faces[next.count++]=(uint32_t(1)<<a)|(uint32_t(1)<<c)|(uint32_t(1)<<v);
  if(!possible(next)){prunes++;return branch;}
  vector<int> polygon{a,v};
  for(int j=1;j<size;j++)polygon.push_back(boundary[j]);
  pending.push_back({polygon,inside-1});
  consume(branch++,next,pending);
 }
 return branch;
}

void count_call(){
 calls++;
 if(limit&&calls>=limit)throw runtime_error("NODE LIMIT: incomplete subtree, no complete output");
 if(calls%1000000==0)cerr<<"PROGRESS B="<<b<<" calls="<<calls<<" survivors="<<survivors.size()
                         <<" seconds="<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<"\n";
}

void visit(State const&s,vector<Region> pending){
 count_call();normalize(pending);
 if(pending.empty()){
  if(s.next!=n||s.count!=faces_needed)throw runtime_error("wrong complete size");
  auto [code,stabilizer]=canonical(s);rooted++;
  auto [iterator,fresh]=survivors.emplace(code,stabilizer);
  if(!fresh&&iterator->second!=stabilizer)throw runtime_error("inconsistent stabilizer");
  return;
 }
 children(s,pending,[&](int,State const&next,vector<Region> const&work){visit(next,work);});
}

struct Frontier{
 vector<int> prefix;
 State state;
 vector<Region> pending;
 int child_count;
 bool terminal;
};
vector<Frontier> frontier;

void cut(State const&s,vector<Region> pending,vector<int>&path,int depth){
 count_call();normalize(pending);
 if(pending.empty()||!depth){
  int k=children(s,pending,[](int,State const&,vector<Region> const&){});
  frontier.push_back({path,s,pending,k,pending.empty()});
  return;
 }
 int k=children(s,pending,[&](int index,State const&next,vector<Region> const&work){
  path.push_back(index);cut(next,work,path,depth-1);path.pop_back();
 });
 // A node with no legal children is a covered, empty subtree, not a missing task.
 if(!k)frontier.push_back({path,s,pending,0,false});
}

long long integer(string text){
 size_t used=0;long long value=stoll(text,&used);
 if(used!=text.size())throw runtime_error("invalid integer");
 return value;
}

vector<int> parse_prefix(string text){
 vector<int> result;
 if(text=="-")return result;
 if(text.empty()||text.back()==',')throw runtime_error("invalid prefix");
 string item;istringstream input(text);
 while(getline(input,item,',')){
  long long index=integer(item);
  if(index<0||index>1000000)throw runtime_error("invalid prefix component");
  result.push_back((int)index);
 }
 return result;
}

void numbers(ostream&out,vector<int> const&values){
 out<<"[";
 for(size_t i=0;i<values.size();i++){if(i)out<<",";out<<values[i];}
 out<<"]";
}

int main(int argc,char**argv){try{
 if(argc!=15)throw runtime_error("usage: peel N B output scale cap2 cap4 cap6 cap8 node-limit mode operation(solve|frontier) prefix(-|i,j,...) frontier-depth origin-screen(0|1)");
 n=(int)integer(argv[1]);b=(int)integer(argv[2]);string output=argv[3];
 scale=integer(argv[4]);for(int j=0;j<4;j++)caps[j]=integer(argv[5+j]);
 long long requested_limit=integer(argv[9]);
 if(requested_limit<0)throw runtime_error("negative limit");
 limit=(uint64_t)requested_limit;
 string mode=argv[10],operation=argv[11];
 if(mode!="dfs"&&mode!="audit"&&mode!="noscreen"&&mode!="audit-noscreen")throw runtime_error("invalid mode");
 audit_order=mode.find("audit")!=string::npos;screen=mode.find("noscreen")==string::npos;
 if(operation!="solve"&&operation!="frontier")throw runtime_error("invalid operation");
 auto prefix=parse_prefix(argv[12]);int depth=(int)integer(argv[13]);
 long long origin_flag=integer(argv[14]);
 if(origin_flag!=0&&origin_flag!=1)throw runtime_error("invalid origin flag");
 origin_screen=origin_flag;
 if(depth<0||depth>MAXF||(operation=="solve"&&depth))throw runtime_error("invalid depth");
 if(n<3||n>MAXN||b<3||n<b||scale<=0||scale>100000000||caps[0]<=0||
    !(caps[0]<caps[1]&&caps[1]<caps[2]&&caps[2]<caps[3])||caps[3]>=scale/2)
  throw runtime_error("parameter bounds");
 if(filesystem::exists(output)||filesystem::exists(output+".partial"))throw runtime_error("output already exists");
 faces_needed=2*n-b-2;if(faces_needed>MAXF)throw runtime_error("face bitset bound");
 State current;current.next=b;
 for(int i=0;i<b;i++){int j=(i+1)%b;current.adjacency[i]|=uint32_t(1)<<j;current.adjacency[j]|=uint32_t(1)<<i;}
 vector<int> boundary(b);iota(boundary.begin(),boundary.end(),0);
 if(audit_order)rotate(boundary.begin(),boundary.begin()+b/2,boundary.end());
 vector<Region> pending{{boundary,n-b}};
 bool feasible=possible(current);
 if(!feasible&&!prefix.empty())throw runtime_error("prefix under rejected root");
 for(int index:prefix){
  normalize(pending);
  if(pending.empty())throw runtime_error("prefix past terminal");
  State selected;vector<Region> work;bool found=false;
  children(current,pending,[&](int child,State const&next,vector<Region> const&tasks){
   if(index==child){selected=next;work=tasks;found=true;}
  });
  if(!found)throw runtime_error("PREFIX INDEX OUT OF RANGE");
  current=selected;pending=work;
 }
 calls=0;prunes=0;origin_prunes=0;started=chrono::steady_clock::now();
 if(feasible){
  if(operation=="solve")visit(current,pending);
  else{auto path=prefix;cut(current,pending,path,depth);}
 }else prunes++;
 ofstream f(output+".partial");if(!f)throw runtime_error("output open failed");
 f<<"{\"schema\":\"N26-recursive-prefix-v1\",\"complete\":true,\"family_complete\":"
  <<(prefix.empty()&&operation=="solve"?"true":"false")
  <<",\"global_optimality_proved\":false,\"geometric_reduction_proved\":false,\"N\":"<<n
  <<",\"B\":"<<b<<",\"screen\":"<<(screen?"true":"false")
  <<",\"mode\":\""<<mode<<"\",\"operation\":\""<<operation<<"\",\"prefix\":";
 numbers(f,prefix);
 f<<",\"origin_screen\":"<<(origin_screen?"true":"false")<<",\"origin_prunes\":"<<origin_prunes<<",\"frontier_depth\":"<<depth<<",\"scale\":"<<scale<<",\"caps\":[";
 for(int j=0;j<4;j++){if(j)f<<",";f<<caps[j];}
 f<<"],\"root_feasible\":"<<(feasible?"true":"false")
  <<",\"calls\":"<<calls<<",\"prunes\":"<<prunes<<",\"rooted\":"<<rooted<<",\"orbits\":"<<survivors.size()<<",\"survivors\":[";
 bool comma=false;
 for(auto const&[code,stab]:survivors){
  if(comma)f<<",";
  comma=true;f<<"{\"stabilizer\":"<<stab<<",\"faces\":[";
  for(size_t j=0;j<code.size();j++){if(j)f<<",";f<<code[j];}f<<"]}";
 }
 f<<"],\"frontier\":[";
 comma=false;
 for(auto const&entry:frontier){
  if(comma)f<<",";
  comma=true;f<<"{\"prefix\":";numbers(f,entry.prefix);
  f<<",\"terminal\":"<<(entry.terminal?"true":"false")
   <<",\"child_count\":"<<entry.child_count<<",\"next\":"<<entry.state.next<<",\"faces\":[";
  for(int j=0;j<entry.state.count;j++){if(j)f<<",";f<<entry.state.faces[j];}
  f<<"],\"adjacency\":[";
  for(int j=0;j<n;j++){if(j)f<<",";f<<entry.state.adjacency[j];}
  f<<"],\"pending\":[";
  for(size_t j=0;j<entry.pending.size();j++){
   if(j)f<<",";
   f<<"{\"boundary\":";numbers(f,entry.pending[j].boundary);
   f<<",\"interior\":"<<entry.pending[j].interior<<"}";
  }
  f<<"]}";
 }
 f<<"]}\n";f.close();if(!f)throw runtime_error("output write failure");
 filesystem::rename(output+".partial",output);
 cerr<<"COMPLETE "<<operation<<" B="<<b<<" calls="<<calls<<" orbits="<<survivors.size()
     <<" frontier="<<frontier.size()<<"\n";
 return 0;
}catch(exception const&e){cerr<<"REJECTED "<<e.what()<<" calls="<<calls<<" origin_prunes="<<origin_prunes<<" survivors="<<survivors.size()<<"\n";return 1;}}
