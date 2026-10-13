// Proper hypergraph containment. All B boundary sites and anchor rods remain,
// including boundary sites which occur in no retained face.
struct CompletionPattern {
 int id,centers;
 vector<uint32_t> faces;
};
struct CompletionVariant {
 int id,K,shift,sign,F;
 array<int,MAXN> boundary_face_degree{},boundary_degree{};
 vector<int> internal_face_degree,internal_degree;
 vector<uint32_t> boundary_neighbors,all_boundary_faces;
 vector<vector<uint32_t>> boundary_pairs;
 vector<vector<uint32_t>> required_pair_boundaries;
};
vector<CompletionPattern> completion_patterns;
vector<CompletionVariant> completion_variants;
int completion_min_faces=MAXF+1;
unordered_map<vector<uint32_t>,PaidMatch,FacesHash> completion_cache;
map<int,uint64_t> completion_counts;
map<int,pair<vector<uint32_t>,PaidMatch>> completion_samples;
uint64_t completion_prunes=0,completion_queries=0;

void load_completion_obstacles(string const& path) {
 if(path=="-")return;
 if(n!=25)throw runtime_error("completion theorem requires exactly N25");
 ifstream input(path);
 string line;
 if(!input||!getline(input,line)||line!="paid-simple-collar-completion-library-v1")
  throw runtime_error("completion library schema/open");
 int previous=-1;
 while(getline(input,line)){
  istringstream row(line);
  int id,B,N,F;
  if(!(row>>id>>B>>N>>F)||id!=previous+1||B<3||N<B||N>MAXN||F<1||F>MAXF)
   throw runtime_error("completion pattern header");
  previous=id;
  vector<uint32_t> faces;uint32_t used=0;
  for(int j=0;j<F;j++){
   uint64_t value;
   if(!(row>>value)||value>=(uint64_t(1)<<N)||pop(uint32_t(value))!=3||
      pop(uint32_t(value)&((uint32_t(1)<<B)-1))<1)
    throw runtime_error("completion pattern face");
   faces.push_back(value);used|=value;
  }
  string extra;
  if(row>>extra||!is_sorted(faces.begin(),faces.end())||
     adjacent_find(faces.begin(),faces.end())!=faces.end()||
     used!=(uint32_t(1)<<N)-1)
   throw runtime_error("completion pattern extra/order/unused internal label");
  if(B!=b||N>n)continue;
  completion_patterns.push_back({id,N,faces});
  completion_min_faces=min(completion_min_faces,F);
 }
 if(!input.eof())throw runtime_error("completion library read failure");
 for(auto const& pattern:completion_patterns){
  array<uint32_t,MAXN> adj{};
  array<int,MAXN> facedeg{};
  for(auto face:pattern.faces)for(int j=0;j<pattern.centers;j++)if(face>>j&1){
   adj[j]|=face^(uint32_t(1)<<j);facedeg[j]++;
  }
  for(int sign:{1,-1})for(int shift=0;shift<b;shift++){
   int K=pattern.centers-b;
   CompletionVariant v;v.id=pattern.id;v.K=K;v.shift=shift;v.sign=sign;v.F=pattern.faces.size();
   v.internal_face_degree.resize(K);v.internal_degree.resize(K);
   v.boundary_neighbors.resize(K);v.boundary_pairs.resize(K);
   v.required_pair_boundaries.assign(K,vector<uint32_t>(K));
   auto boundary_image=[&](int j){return (shift+sign*j+b)%b;};
   for(int j=0;j<b;j++){
    v.boundary_face_degree[boundary_image(j)]=facedeg[j];
    v.boundary_degree[boundary_image(j)]=pop(adj[j]);
   }
   for(int i=0;i<K;i++){
    v.internal_face_degree[i]=facedeg[b+i];v.internal_degree[i]=pop(adj[b+i]);
    for(int j=0;j<b;j++)if(adj[b+i]>>j&1)
     v.boundary_neighbors[i]|=uint32_t(1)<<boundary_image(j);
   }
   for(auto face:pattern.faces){
    uint32_t boundary=0;vector<int> interior;
    for(int j=0;j<pattern.centers;j++)if(face>>j&1){
     if(j<b)boundary|=uint32_t(1)<<boundary_image(j);else interior.push_back(j-b);
    }
    if(interior.empty())v.all_boundary_faces.push_back(boundary);
    else if(interior.size()==1)v.boundary_pairs[interior[0]].push_back(boundary);
    else if(interior.size()==2){
     int i=interior[0],j=interior[1];
     v.required_pair_boundaries[i][j]|=boundary;
     v.required_pair_boundaries[j][i]|=boundary;
    }else throw runtime_error("completion outer face has no boundary center");
   }
   sort(v.all_boundary_faces.begin(),v.all_boundary_faces.end());
   for(auto& pairs:v.boundary_pairs)sort(pairs.begin(),pairs.end());
   completion_variants.push_back(move(v));
  }
 }
}

CompletionPattern const& completion_pattern(int id) {
 auto found=find_if(completion_patterns.begin(),completion_patterns.end(),
                    [&](auto const& value){return value.id==id;});
 if(found==completion_patterns.end())throw runtime_error("unknown completion id");
 return *found;
}

void verify_completion_injection(vector<uint32_t> const& raw,PaidMatch const& match) {
 auto const& pattern=completion_pattern(match.id);
 if(raw.size()!=pattern.faces.size()||(int)match.centers.size()!=pattern.centers||(int)match.anchors.size()!=b)
  throw runtime_error("completion injection dimensions");
 set<int> distinct(match.centers.begin(),match.centers.end());
 if((int)distinct.size()!=pattern.centers)throw runtime_error("completion center collision");
 for(int j=0;j<b;j++){
  int anchor=(match.shift+match.sign*j-(match.sign<0)+2*b)%b;
  if(match.centers[j]!=(match.shift+match.sign*j+b)%b||match.anchors[j]!=anchor||
     set<int>{match.centers[j],match.centers[(j+1)%b]}!=set<int>{anchor,(anchor+1)%b})
   throw runtime_error("completion boundary/anchor rod map");
 }
 for(int j=b;j<pattern.centers;j++)
  if(match.centers[j]<b||match.centers[j]>=n)throw runtime_error("completion internal color/range");
 for(auto face:pattern.faces){
  uint32_t image=0;
  for(int j=0;j<pattern.centers;j++)if(face>>j&1)image|=uint32_t(1)<<match.centers[j];
  if(!binary_search(raw.begin(),raw.end(),image))throw runtime_error("completion missing image face");
 }
}

PaidMatch contained_completion(vector<uint32_t> const& raw) {
 if(completion_patterns.empty()||(int)raw.size()<completion_min_faces)return {};
 array<uint32_t,MAXN> adj{};
 array<int,MAXN> facedeg{};
 vector<vector<uint32_t>> pairs(n-b);
 vector<vector<uint32_t>> relation(n-b,vector<uint32_t>(n-b));
 uint32_t used_inside=0,bmask=(uint32_t(1)<<b)-1;
 for(auto face:raw){
  for(int j=0;j<n;j++)if(face>>j&1){adj[j]|=face^(uint32_t(1)<<j);facedeg[j]++;}
  uint32_t boundary=face&bmask,inside=face^boundary;
  if(inside)used_inside|=inside>>b;
  if(pop(inside)==1)pairs[first(inside)-b].push_back(boundary);
  else if(pop(inside)==2){
   int i=first(inside)-b;inside&=inside-1;int j=first(inside)-b;
   relation[i][j]|=boundary;relation[j][i]|=boundary;
  }
 }
 for(auto& values:pairs)sort(values.begin(),values.end());
 for(auto const& variant:completion_variants){
  int K=variant.K;
  if(K!=pop(used_inside)||(int)raw.size()!=variant.F)continue;
  bool valid=true;
  for(int j=0;j<b;j++)if(variant.boundary_face_degree[j]>facedeg[j]||
                         variant.boundary_degree[j]>pop(adj[j])){valid=false;break;}
  if(!valid)continue;
  for(auto face:variant.all_boundary_faces)
   if(!binary_search(raw.begin(),raw.end(),face)){valid=false;break;}
  if(!valid)continue;
  vector<uint32_t> domains(K);
  for(int i=0;i<K;i++){
   for(int k=0;k<n-b;k++)if(used_inside>>k&1){
    if(variant.internal_face_degree[i]>facedeg[b+k]||
       variant.internal_degree[i]>pop(adj[b+k])||
       (variant.boundary_neighbors[i]&(adj[b+k]&bmask))!=variant.boundary_neighbors[i])continue;
    if(!includes(pairs[k].begin(),pairs[k].end(),
                 variant.boundary_pairs[i].begin(),variant.boundary_pairs[i].end()))continue;
    domains[i]|=uint32_t(1)<<k;
   }
   if(!domains[i]){valid=false;break;}
  }
  if(!valid)continue;
  vector<int> assignment(K,-1);
  function<bool(uint32_t,int)> search=[&](uint32_t used,int assigned){
   if(assigned==K)return true;
   int pick=-1;uint32_t choices=0;
   for(int i=0;i<K;i++)if(assignment[i]<0){
    uint32_t filtered=0,candidates=domains[i]&~used;
    while(candidates){
     int k=first(candidates);candidates&=candidates-1;
     bool fits=true;
     for(int j=0;j<K;j++)if(assignment[j]>=0){
      uint32_t need=variant.required_pair_boundaries[i][j];
      if((relation[k][assignment[j]]&need)!=need){fits=false;break;}
     }
     if(fits)filtered|=uint32_t(1)<<k;
    }
    if(!filtered)return false;
    if(pick<0||pop(filtered)<pop(choices)){pick=i;choices=filtered;}
   }
   while(choices){
    int k=first(choices);choices&=choices-1;assignment[pick]=k;
    uint32_t next_used=used|(uint32_t(1)<<k);
    bool forward=true;
    for(int j=0;j<K;j++)if(assignment[j]<0){
     uint32_t need=variant.required_pair_boundaries[pick][j];
     if(!need)continue;
     bool support=false;uint32_t available=domains[j]&~next_used;
     while(available){int other=first(available);available&=available-1;
      if((relation[k][other]&need)==need){support=true;break;}
     }
     if(!support){forward=false;break;}
    }
    if(forward&&search(next_used,assigned+1))return true;
    assignment[pick]=-1;
   }
   return false;
  };
  if(!search(0,0))continue;
  PaidMatch result;result.id=variant.id;result.shift=variant.shift;result.sign=variant.sign;
  for(int j=0;j<b;j++){
   result.centers.push_back((variant.shift+variant.sign*j+b)%b);
   result.anchors.push_back((variant.shift+variant.sign*j-(variant.sign<0)+2*b)%b);
  }
  for(int i=0;i<K;i++)result.centers.push_back(b+assignment[i]);
  verify_completion_injection(raw,result);
  return result;
 }
 return {};
}

bool already_completion_paid(State const& state) {
 if(completion_patterns.empty()||state.count<completion_min_faces)return false;
 vector<uint32_t> raw;
 for(int f=0;f<state.count;f++)
  if(pop(state.faces[f]&((uint32_t(1)<<b)-1))>=1)raw.push_back(state.faces[f]);
 if((int)raw.size()<completion_min_faces)return false;
 sort(raw.begin(),raw.end());completion_queries++;
 auto old=completion_cache.find(raw);PaidMatch match;
 if(old!=completion_cache.end())match=old->second;
 else{
  match=contained_completion(raw);
  if(completion_cache.size()>=65536)completion_cache.clear();
  completion_cache.emplace(raw,match);
 }
 if(match.id<0)return false;
 verify_completion_injection(raw,match);
 completion_prunes++;completion_counts[match.id]++;
 completion_samples.emplace(match.id,make_pair(raw,match));
 return true;
}

void write_completion_summary(ostream& out) {
 out<<",\"completion_proof_prunes\":"<<completion_prunes<<",\"completion_queries\":"<<completion_queries
    <<",\"completion_patterns_loaded\":"<<completion_patterns.size()<<",\"completion_payments\":[";
 bool comma=false;
 for(auto const& [id,count]:completion_counts){
  if(comma)out<<",";comma=true;
  auto const& [raw,match]=completion_samples.at(id);
  out<<"{\"obstacle\":"<<id<<",\"pruned_recursive_states\":"<<count<<",\"sample_faces\":[";
  for(size_t j=0;j<raw.size();j++){if(j)out<<",";out<<raw[j];}
  out<<"],\"centers\":[";
  for(size_t j=0;j<match.centers.size();j++){if(j)out<<",";out<<match.centers[j];}
  out<<"],\"anchors\":[";
  for(size_t j=0;j<match.anchors.size();j++){if(j)out<<",";out<<match.anchors[j];}
  out<<"],\"orientation\":"<<match.sign<<",\"shift\":"<<match.shift<<"}";
 }
 out<<"]";
}
