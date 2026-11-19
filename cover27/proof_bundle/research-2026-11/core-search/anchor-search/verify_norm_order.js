// Exact B=14 lower bounds on sorted outer-center norms at U=0.230796.
"use strict";
const {S,Q,add,sub,mul,div,sq,sqrt,check,gt,sin,cos,pi}=require("../exact-interval.js");

const radius=Q(230796,1000000),half=div(sq(radius),Q(2)),tau=mul(Q(2),pi);
const ticks=10_000_000;
const t=x=>Q(x,ticks);
const low=1490000,high=2328957;
check(gt(sin(t(high)),radius)&&gt(sin(t(low)),div(radius,Q(2))),"owner angle range");
const polygon=k=>mul(half,mul(Q(k),sin(div(tau,Q(k)))));
const cache=new Map();
function chord(l){
  if(!cache.has(l)){
    const s=sin(t(l));
    const z=div(s,radius);
    const guess=Math.floor(ticks*Math.asin(Math.min(1,Number(z[0])/Number(S))))-2;
    let theta=Q(0);
    if(guess>0&&guess<15707963&&gt(z,sin(t(guess))))theta=t(2*guess);
    cache.set(l,{theta,s,cap:div(sin(t(2*l)),Q(2))});
  }
  return cache.get(l);
}

const data=[
  [2,1840000,842400000,"-3.63272812","0.00760208","0.67250969","0.57974967","0.09277869"],
  [3,1975000,859000000,"-4.15398631","0.00736861","0.79390787","0.71544011","0.09417954"],
  [4,2045000,869490000,"-5.80159221","0.00736861","1.17635143","1.07178532","0.09417954"],
  [5,2095000,878000000,"-8.00000000","0.00736861","1.68754525","1.55402238","0.09417954"],
  [6,2130000,884700000,"-8.00000000","0.00736861","1.68754525","1.57662267","0.09417954"],
  [7,2155000,890000000,"-8.00000000","0.00736861","1.68754525","1.59245898","0.09417954"]
];
const fixed=x=>Q(BigInt(x.replace(".","")),100000000n);
for(const [m,end,cap,a,b,c,d,e] of data){
  const lambda=fixed(a),mu=fixed(b);
  const big=add(fixed(c),Q(1,20000)),small=add(fixed(d),Q(1,5000)),inside=add(fixed(e),Q(1,50000));
  check(gt(Q(0),lambda)&&gt(big,small),"support coefficient signs");
  for(let k=3;k<=26;k++)check(gt(add(inside,mul(mu,Q(k))),polygon(k)),"inner polygon");
  let boxes=0;
  for(const [right,constant] of [[high,big],[end,small]]){
    for(let degree=3;degree<=15;degree++){
      const peak=div(tau,Q(degree+1));
      const stack=[[low,right]];
      while(stack.length){
        const [l,h]=stack.pop(); boxes++;
        const {theta,s,cap}=chord(l);
        if(gt(s,radius))continue;
        const P=gt(theta,peak)?
          mul(half,add(sin(theta),mul(Q(degree),sin(div(sub(tau,theta),Q(degree)))))):
          polygon(degree+1);
        const bound=add(add(constant,mul(mu,Q(degree))),mul(lambda,t(h)));
        if(gt(bound,sub(P,cap)))continue;
        check(h-l>1,"unresolved B14 order box "+[m,degree,l,h]);
        const mid=Math.floor((l+h)/2);
        stack.push([l,mid],[mid,h]);
      }
    }
  }
  const total=add(add(mul(lambda,pi),mul(mu,Q(128))),
    add(add(mul(Q(14-m),big),mul(Q(m),small)),mul(Q(13),inside)));
  check(gt(Q(0),total),"short-owner multiplicity "+m);
  const norm=sub(cos(t(end)),sqrt(sub(sq(radius),sq(sin(t(end))))));
  check(gt(norm,Q(cap,1_000_000_000)),"inverse radius enclosure "+m);
  console.log(`PASS B=14: sorted norm D[${m}] > ${cap}/1e9 in ${boxes} boxes.`);
}
