// Actual N25 disk covers, not arbitrary geometric weak realizations.
// An origin-covering center cannot be adjacent to any boundary center:
// 1 <= |q-b|+|b-w|+|w-c|+|c-0| <= 4*r <= 4*U25 < 1.
bool origin_cover_screen=false;
uint64_t origin_cover_prunes=0;
constexpr uint64_t ORIGIN_U_NUM=239146311738101ULL;
constexpr uint64_t ORIGIN_U_DEN=1000000000000000ULL;
static_assert(4*ORIGIN_U_NUM<ORIGIN_U_DEN);
vector<vector<uint32_t>> origin_cover_samples;

void initialize_cover_origin(string const& flag){
 if(flag!="0"&&flag!="1")throw runtime_error("origin cover screen must be 0 or 1");
 origin_cover_screen=flag=="1";
}

bool already_cover_origin_paid(State const& s){
 if(!origin_cover_screen||n!=25)return false;
 uint32_t mask=(uint32_t(1)<<b)-1;
 for(int v=0;v<b;v++)mask|=s.adjacency[v];
 if(mask!=(uint32_t(1)<<n)-1)return false;
 if(origin_cover_samples.size()<8){
  vector<uint32_t> outer;
  uint32_t checked=(uint32_t(1)<<b)-1;
  for(int f=0;f<s.count;f++)if(s.faces[f]&((uint32_t(1)<<b)-1)){
   outer.push_back(s.faces[f]);checked|=s.faces[f];
  }
  if(checked!=mask)throw runtime_error("origin face/adjacency exposure mismatch");
  sort(outer.begin(),outer.end());
  origin_cover_samples.push_back(outer);
 }
 origin_cover_prunes++;
 return true;
}

void write_cover_origin_summary(ostream& out){
 out<<",\"origin_cover_screen\":"<<(origin_cover_screen?"true":"false")
    <<",\"origin_cover_only_N25\":true"
    <<",\"origin_cover_scope\":\"actual arbitrary disk covers only; not weak graph geometry\""
    <<",\"origin_radius_upper_numerator\":"<<ORIGIN_U_NUM
    <<",\"origin_radius_upper_denominator\":"<<ORIGIN_U_DEN
    <<",\"origin_cover_prunes_not_type_count\":"<<origin_cover_prunes
    <<",\"origin_cover_samples\":[";
 for(size_t j=0;j<origin_cover_samples.size();j++){
  if(j)out<<",";
  out<<"{\"outer_faces\":[";
  auto const& faces=origin_cover_samples[j];
  for(size_t k=0;k<faces.size();k++){if(k)out<<",";out<<faces[k];}
  out<<"]}";
 }
 out<<"]";
}
