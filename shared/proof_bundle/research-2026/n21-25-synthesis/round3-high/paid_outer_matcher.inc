// Included after the frozen topology/angle routines, before recursion.
struct PaidPattern {
 int id,centers;
 vector<uint32_t> faces;
};
struct PaidMatch {
 int id=-1,shift=0,sign=1;
 vector<int> centers,anchors;
};
struct FacesHash {
 size_t operator()(vector<uint32_t> const& value) const {
  size_t h=1469598103934665603ULL;
  for(auto x:value){h^=x;h*=1099511628211ULL;}
  return h;
 }
};
map<vector<uint32_t>,PaidPattern> paid_patterns;
unordered_map<vector<uint32_t>,PaidMatch,FacesHash> paid_cache;
map<int,uint64_t> paid_counts;
map<int,pair<vector<uint32_t>,PaidMatch>> paid_samples;
uint64_t proof_prunes=0,paid_match_queries=0;
int min_paid_faces=MAXF+1,min_paid_centers=MAXN+1;

void load_obstacles(string const& path) {
 if(path=="-")return; // Regression-only: no proof pruning.
 ifstream stream(path);
 if(!stream)throw runtime_error("paid library open failed");
 string line;
 if(!getline(stream,line)||line!="strict-outer-obstacle-library-v1")
  throw runtime_error("paid library schema");
 int previous=-1;
 while(getline(stream,line)){
  if(line.empty())throw runtime_error("empty paid pattern row");
  istringstream row(line);
  int id,B,N,F;
  if(!(row>>id>>B>>N>>F)||id!=previous+1||B<3||N<B||N>MAXN||F<1||F>MAXF)
   throw runtime_error("paid pattern header");
  previous=id;
  vector<uint32_t> masks;
  uint32_t used=0;
  for(int j=0;j<F;j++){
   uint64_t mask;
   if(!(row>>mask)||mask>=(uint64_t(1)<<N)||pop(uint32_t(mask))!=3||
      pop(uint32_t(mask)&((uint32_t(1)<<B)-1))<1)
    throw runtime_error("paid pattern face");
   masks.push_back(uint32_t(mask));used|=uint32_t(mask);
  }
  string extra;
  if(row>>extra)throw runtime_error("extra paid row columns");
  if(!is_sorted(masks.begin(),masks.end())||
     adjacent_find(masks.begin(),masks.end())!=masks.end()||
     used!=(uint32_t(1)<<N)-1)
   throw runtime_error("noncanonical or unused paid graph labels");
  if(B!=b||N>n)continue;
  if(!paid_patterns.emplace(masks,PaidPattern{id,N,masks}).second)
   throw runtime_error("duplicate paid pattern");
  min_paid_faces=min(min_paid_faces,F);min_paid_centers=min(min_paid_centers,N);
 }
 if(!stream.eof())throw runtime_error("paid table read failure");
}

PaidMatch canonical_paid(vector<uint32_t> const& raw) {
 array<uint32_t,MAXN> adj{};
 uint32_t used=0;
 for(auto mask:raw){
  used|=mask;
  for(int v=0;v<n;v++)if(mask>>v&1)adj[v]|=mask^(uint32_t(1)<<v);
 }
 if(pop(used)<min_paid_centers)return {};
 vector<int> minimum;
 vector<pair<int,int>> roots;
 for(int sign:{1,-1})for(int shift=0;shift<b;shift++){
  vector<int> profile;
  for(int j=0;j<b;j++)profile.push_back(pop(adj[(shift+sign*j+b)%b]));
  if(minimum.empty()||profile<minimum){minimum=profile;roots.clear();}
  if(profile==minimum)roots.emplace_back(shift,sign);
 }
 vector<uint32_t> best;
 PaidMatch bestmap;
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
      if(label[v]<0)throw runtime_error("paid partial unassigned label");
      image|=uint32_t(1)<<label[v];
     }
     code.push_back(image);
    }
    sort(code.begin(),code.end());
    if(best.empty()||code<best){
     best=code;bestmap.centers=centers;bestmap.shift=shift;bestmap.sign=sign;
     bestmap.anchors.clear();
     for(int j=0;j<b;j++)bestmap.anchors.push_back((shift+sign*j-(sign<0)+2*b)%b);
    }
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
 auto found=paid_patterns.find(best);
 if(found==paid_patterns.end())return {};
 auto const& pattern=found->second;
 if((int)bestmap.centers.size()!=pattern.centers)
  throw runtime_error("paid center count mismatch");
 // Verify every actual injection and the reflected anchor offset on a hit.
 set<int> injection(bestmap.centers.begin(),bestmap.centers.end());
 if(injection.size()!=bestmap.centers.size())throw runtime_error("paid noninjective map");
 for(int j=0;j<b;j++){
  int anchor=bestmap.anchors[j],left=bestmap.centers[j],right=bestmap.centers[(j+1)%b];
  if(set<int>{left,right}!=set<int>{anchor,(anchor+1)%b})
   throw runtime_error("paid wrong boundary rod map");
 }
 vector<uint32_t> images;
 for(auto face:pattern.faces){
  uint32_t image=0;
  for(int v=0;v<pattern.centers;v++)if(face>>v&1)image|=uint32_t(1)<<bestmap.centers[v];
  images.push_back(image);
 }
 sort(images.begin(),images.end());
 if(images!=raw)throw runtime_error("paid face injection mismatch");
 bestmap.id=pattern.id;
 return bestmap;
}

bool already_paid(State const& s) {
 if(paid_patterns.empty()||s.count<min_paid_faces)return false;
 vector<uint32_t> raw;uint32_t boundary_used=0;
 for(int f=0;f<s.count;f++){
  auto face=s.faces[f];
  if(pop(face&((uint32_t(1)<<b)-1))>=1){raw.push_back(face);boundary_used|=face;}
 }
 if((int)raw.size()<min_paid_faces||
    (boundary_used&((uint32_t(1)<<b)-1))!=(uint32_t(1)<<b)-1)return false;
 sort(raw.begin(),raw.end());
 paid_match_queries++;
 auto cached=paid_cache.find(raw);
 PaidMatch match;
 if(cached!=paid_cache.end())match=cached->second;
 else{
  match=canonical_paid(raw);
  if(paid_cache.size()>=65536)paid_cache.clear(); // Eviction cannot discard proof obligations.
  paid_cache.emplace(raw,match);
 }
 if(match.id<0)return false;
 proof_prunes++;paid_counts[match.id]++;
 paid_samples.emplace(match.id,make_pair(raw,match));
 return true;
}

void write_paid_summary(ostream& stream) {
 stream<<",\"proof_prunes\":"<<proof_prunes<<",\"paid_match_queries\":"<<paid_match_queries
       <<",\"paid_patterns_loaded\":"<<paid_patterns.size()<<",\"proof_payments\":[";
 bool comma=false;
 for(auto const& [id,count]:paid_counts){
  if(comma)stream<<",";comma=true;
  auto const& [raw,match]=paid_samples.at(id);
  stream<<"{\"obstacle\":"<<id<<",\"pruned_recursive_states\":"<<count<<",\"sample_faces\":[";
  for(size_t j=0;j<raw.size();j++){if(j)stream<<",";stream<<raw[j];}
  stream<<"],\"centers\":[";
  for(size_t j=0;j<match.centers.size();j++){if(j)stream<<",";stream<<match.centers[j];}
  stream<<"],\"anchors\":[";
  for(size_t j=0;j<match.anchors.size();j++){if(j)stream<<",";stream<<match.anchors[j];}
  stream<<"],\"orientation\":"<<match.sign<<",\"shift\":"<<match.shift<<"}";
 }
 stream<<"]";
}
