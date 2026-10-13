// Exact binary little-endian runs. Runs are retained, never silently deleted.
#ifndef PAID_BLOCK_LIMIT
#define PAID_BLOCK_LIMIT 100000
#endif
constexpr size_t SURVIVOR_BLOCK=PAID_BLOCK_LIMIT;
string residual_target;
vector<string> residual_runs;
uint64_t rows_to_runs=0;
string replay_prefix_directory="-";
uint64_t replay_prefix_count=0,replay_prefix_runs_compared=0;

void write_u32(ostream& out,uint32_t value){
 for(int j=0;j<4;j++)out.put(char((value>>(8*j))&255));
 if(!out)throw runtime_error("binary residual write failure");
}
void write_u64(ostream& out,uint64_t value){
 for(int j=0;j<8;j++)out.put(char((value>>(8*j))&255));
 if(!out)throw runtime_error("binary count write failure");
}
uint32_t read_u32(istream& in){
 uint32_t value=0;
 for(int j=0;j<4;j++){
  int byte=in.get();if(byte==char_traits<char>::eof())throw runtime_error("truncated residual run");
  value|=uint32_t(static_cast<unsigned char>(byte))<<(8*j);
 }
 return value;
}
void initialize_paid_storage(string const& output){
 residual_target=output;
 if(filesystem::exists(output)||filesystem::exists(output+".building")||filesystem::exists(output+".runs"))
  throw runtime_error("refuse to overwrite residual output/runs");
 filesystem::create_directory(output+".runs");
}
void flush_paid_run(){
 if(survivors.empty())return;
 if(residual_runs.size()<replay_prefix_count){
  string oldpath=replay_prefix_directory+"/run-"+to_string(residual_runs.size())+".bin";
  ifstream old(oldpath,ios::binary);char magic[8];old.read(magic,8);
  if(!old||string(magic,8)!="PAIDRUN1")throw runtime_error("invalid resume-prefix run");
  if(read_u32(old)!=uint32_t(n)||read_u32(old)!=uint32_t(b)||read_u32(old)!=uint32_t(faces_needed))
   throw runtime_error("resume-prefix dimension mismatch");
  uint64_t count=0;
  for(int j=0;j<8;j++){
   int byte=old.get();if(byte==char_traits<char>::eof())throw runtime_error("resume-prefix count truncated");
   count|=uint64_t(static_cast<unsigned char>(byte))<<(8*j);
  }
  if(count!=survivors.size())throw runtime_error("resume-prefix generated block size mismatch");
  for(auto const& [code,stab]:survivors){
   if(read_u32(old)!=uint32_t(stab))throw runtime_error("resume-prefix stabilizer mismatch");
   for(auto face:code)if(read_u32(old)!=face)throw runtime_error("resume-prefix full code mismatch");
  }
  if(old.peek()!=char_traits<char>::eof())throw runtime_error("resume-prefix extra bytes");
  replay_prefix_runs_compared++;
 }
 string path=residual_target+".runs/run-"+to_string(residual_runs.size())+".bin";
 if(filesystem::exists(path))throw runtime_error("run overwrite refused");
 ofstream out(path,ios::binary);
 if(!out)throw runtime_error("run open failed");
 out.write("PAIDRUN1",8);
 write_u32(out,uint32_t(n));write_u32(out,uint32_t(b));write_u32(out,uint32_t(faces_needed));
 write_u64(out,uint64_t(survivors.size()));
 for(auto const& [code,stab]:survivors){
  if((int)code.size()!=faces_needed||stab<=0)throw runtime_error("run row size/stabilizer");
  write_u32(out,uint32_t(stab));
  for(auto face:code)write_u32(out,face);
 }
 out.close();if(!out)throw runtime_error("run close failed");
 rows_to_runs+=survivors.size();residual_runs.push_back(path);survivors.clear();
}
struct RunCursor{
 ifstream stream;
 uint64_t remaining=0;
 vector<uint32_t> previous,code;
 uint32_t stab=0;
 bool ended=false;
 explicit RunCursor(string const& path):stream(path,ios::binary){
  char magic[8];stream.read(magic,8);
  if(!stream||string(magic,8)!="PAIDRUN1")throw runtime_error("run header");
  if(read_u32(stream)!=uint32_t(n)||read_u32(stream)!=uint32_t(b)||
     read_u32(stream)!=uint32_t(faces_needed))throw runtime_error("run graph dimensions");
  for(int j=0;j<8;j++){
   int byte=stream.get();if(byte==char_traits<char>::eof())throw runtime_error("run count");
   remaining|=uint64_t(static_cast<unsigned char>(byte))<<(8*j);
  }
  advance();
 }
 bool advance(){
  if(!remaining){
   if(stream.peek()!=char_traits<char>::eof())throw runtime_error("extra run bytes");
   ended=true;stream.close();return false;
  }
  stab=read_u32(stream);code.clear();
  for(int j=0;j<faces_needed;j++)code.push_back(read_u32(stream));
  if(!stab||!is_sorted(code.begin(),code.end())||
     adjacent_find(code.begin(),code.end())!=code.end()||
     (!previous.empty()&&!(previous<code)))throw runtime_error("run sort/stabilizer failure");
  previous=code;remaining--;return true;
 }
};

uint64_t write_search_phase(string const& mode){
 flush_paid_run();
 if(replay_prefix_runs_compared!=replay_prefix_count)
  throw runtime_error("requested resume prefix was not fully regenerated");
 ostringstream metadata;
 metadata<<"{\"complete\":false,\"residual_complete\":true,\"schema\":\"paid-peeling-residual-binary-v1\""
         <<",\"N\":"<<n<<",\"B\":"<<b<<",\"screen\":"<<(screen?"true":"false")
         <<",\"root_degree_prune\":true,\"mode\":\""<<mode<<"\",\"scale\":"<<scale
         <<",\"caps\":["<<caps[0]<<","<<caps[1]<<","<<caps[2]<<"],\"calls\":"<<calls
         <<",\"prunes\":"<<prunes<<",\"rooted\":"<<rooted
         <<",\"rows_to_runs\":"<<rows_to_runs<<",\"run_count\":"<<residual_runs.size()
         <<",\"survivor_block_size\":"<<SURVIVOR_BLOCK;
 metadata<<",\"native_search_only_stage\":true,\"prefix_runs_replayed_and_compared\":"<<replay_prefix_runs_compared;
 write_paid_summary(metadata);metadata<<"}";
 auto text=metadata.str();
 if(text.size()>64*1024*1024)throw runtime_error("residual metadata limit");
 ofstream out(residual_target+".building",ios::binary);
 if(!out)throw runtime_error("binary residual output open");
 out.write("PAIDRSV1",8);
 write_u32(out,uint32_t(n));write_u32(out,uint32_t(b));write_u32(out,uint32_t(faces_needed));
 write_u32(out,uint32_t(text.size()));
 write_u64(out,0); // Patched only after the complete exact merge.
 out.write(text.data(),text.size());
 out.close();if(!out)throw runtime_error("search phase close failed");
 return rows_to_runs;
}
