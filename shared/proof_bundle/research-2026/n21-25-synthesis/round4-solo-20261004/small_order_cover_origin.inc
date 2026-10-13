// Actual N23/N24 cover necessity, never a weak-graph geometry exclusion.
// An origin-covering center cannot appear with a boundary center in a face:
// 1 <= |q-b|+|b-w|+|w-c|+|c-0| <= 4*r <= 4*U_N < 1.
bool origin_cover_screen=false;
uint64_t origin_cover_prunes=0,origin_upper_num=0,origin_upper_den=1;
static_assert(4*249953776586051ULL<1000000000000000ULL);
static_assert(4*61325412542131ULL<250000000000000ULL);
vector<vector<uint32_t>> origin_cover_samples;

void initialize_cover_origin(string const& flag){
 if(flag!="0"&&flag!="1")throw runtime_error("origin cover screen must be 0 or 1");
 if(n==23){origin_upper_num=249953776586051ULL;origin_upper_den=1000000000000000ULL;}
 else if(n==24){origin_upper_num=61325412542131ULL;origin_upper_den=250000000000000ULL;}
 origin_cover_screen=flag=="1";
 if(origin_cover_screen&&n!=23&&n!=24)
  throw runtime_error("small-order origin screen requires N23 or N24");
 if(origin_cover_screen&&4*origin_upper_num>=origin_upper_den)
  throw runtime_error("small-order origin strict quarter-radius gap missing");
}

bool already_cover_origin_paid(State const& s){
 if(!origin_cover_screen)return false;
 if(n!=23&&n!=24)throw runtime_error("wrong order for origin necessity");
 uint32_t mask=(uint32_t(1)<<b)-1;
 for(int v=0;v<b;v++)mask|=s.adjacency[v];
 if(mask!=(uint32_t(1)<<n)-1)return false;
 if(origin_cover_samples.size()<8){
  vector<uint32_t> outer;
  uint32_t checked=(uint32_t(1)<<b)-1;
  for(int f=0;f<s.count;f++)if(s.faces[f]&((uint32_t(1)<<b)-1)){
   outer.push_back(s.faces[f]);checked|=s.faces[f];
  }
  if(checked!=mask)throw runtime_error("small-order origin face/adjacency exposure mismatch");
  sort(outer.begin(),outer.end());
  origin_cover_samples.push_back(outer);
 }
 origin_cover_prunes++;
 return true;
}

void write_cover_origin_summary(ostream& out){
 out<<",\"origin_cover_screen\":"<<(origin_cover_screen?"true":"false")
    <<",\"origin_cover_orders\":[23,24]"
    <<",\"origin_cover_scope\":\"actual arbitrary disk covers only; not weak graph geometry\""
    <<",\"origin_radius_upper_numerator\":"<<origin_upper_num
    <<",\"origin_radius_upper_denominator\":"<<origin_upper_den
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
