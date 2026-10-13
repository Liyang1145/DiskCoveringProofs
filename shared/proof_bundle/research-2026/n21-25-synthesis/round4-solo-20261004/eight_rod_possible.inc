// Necessary 2/4/6/8-rod anchor constraints. No floating-point arithmetic.
long long cap8=0;
bool possible(State const&s){
 if(!screen)return true;
 uint32_t one[MAXN]{},two[MAXN]{},three[MAXN]{};
 for(int i=0;i<n;i++)one[i]=s.adjacency[i]|(uint32_t(1)<<i);
 for(int i=0;i<n;i++){
  auto mask=one[i],value=mask;
  while(mask){int j=first(mask);mask&=mask-1;value|=one[j];}
  two[i]=value;
 }
 for(int i=0;i<n;i++){
  auto mask=one[i],value=two[i];
  while(mask){int j=first(mask);mask&=mask-1;value|=two[j];}
  three[i]=value;
 }
 vector<array<long long,3>> inequalities;
 for(int i=0;i<b;i++){
  int j=(i+1)%b;
  inequalities.push_back({i,j,caps[0]-(j==0?scale:0)});
  inequalities.push_back({j,i,j==0?scale:0});
 }
 for(int i=0;i<b;i++){
  auto reach1=one[i]|one[(i+1)%b],reach2=two[i]|two[(i+1)%b];
  auto reach3=three[i]|three[(i+1)%b];
  for(int j=i+1;j<b;j++){
   auto ends=(uint32_t(1)<<j)|(uint32_t(1)<<((j+1)%b));
   long long cap;
   if(reach1&ends)cap=caps[1];
   else if(reach2&ends)cap=caps[2];
   else if(reach3&ends)cap=cap8;
   else continue;
   int k=j-i;
   if(min(k,b-k)*caps[0]<=cap)continue;
   bool forward=k*caps[0]<scale-cap;
   bool backward=(b-k)*caps[0]<scale-cap;
   if(forward&&backward)return false;
   if(forward)inequalities.push_back({i,j,cap});
   else if(backward)inequalities.push_back({j,i,cap-scale});
  }
 }
 if(!audit_order){
  long long distance[MAXN]{};
  for(int pass=0;pass<b;pass++){
   bool changed=false;
   for(auto edge:inequalities){
    int u=edge[0],v=edge[1];
    if(distance[v]>distance[u]+edge[2]){
     distance[v]=distance[u]+edge[2];changed=true;
    }
   }
   if(!changed)return true;
  }
  return false;
 }
 constexpr long long INF=1000000000000LL;
 long long distance[MAXN][MAXN];
 for(int i=0;i<b;i++)for(int j=0;j<b;j++)distance[i][j]=i==j?0:INF;
 for(auto edge:inequalities)
  distance[edge[0]][edge[1]]=min(distance[edge[0]][edge[1]],edge[2]);
 for(int k=0;k<b;k++)for(int i=0;i<b;i++)for(int j=0;j<b;j++)
  distance[i][j]=min(distance[i][j],distance[i][k]+distance[k][j]);
 for(int i=0;i<b;i++)if(distance[i][i]<0)return false;
 return true;
}
