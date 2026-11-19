// Geometric bounds on the paths through one interior center in the B=14 dual.
"use strict";
const {S,Q,add,sub,mul,div,sq,sqrt,check,gt,sin,cos,pi}=require("../exact-interval.js");
const U=Q(230796,1000000),T=Q(2328957,10000000);
const a=Q(812,1000),b=Q(8424,10000),c=Q(859,1000);
check(gt(sin(T),U),"outer arc half-angle");

function separated(step,x,y,bound){
  // The lift from the first arc's far endpoint to the second's includes
  // step+1 arcs. The two center offsets cost one further half-angle T.
  const h=sub(pi,mul(Q(14-step),T));
  check(gt(h,Q(0))&&gt(div(pi,Q(2)),h),"angular separation domain");
  // Use a lower bound on the shorter angular separation in [0,pi].
  const s=sin(h);
  const dist=add(sq(sub(x,y)),mul(Q(4),mul(mul(x,y),sq(s))));
  check(gt(dist,sq(bound)),"center separation");
  const cosine=sub(Q(1),mul(Q(2),sq(s)));
  check(gt(x,mul(y,cosine))&&gt(y,mul(x,cosine)),"radial corner gives minimum");
}
separated(3,b,c,mul(Q(4),U));
separated(4,a,a,mul(Q(4),U));
separated(3,Q(826,1000),c,mul(Q(4),U));
separated(2,a,b,mul(Q(2),U));
check(gt(pi,mul(Q(13),T)),"consecutive owner directions stay ordered");

// A cyclic distance-three pair forces both norms into short-arc classes.
const h=sub(pi,mul(Q(11),T)),C=cos(mul(Q(2),h)),D=sin(mul(Q(2),h));
check(gt(C,Q(0))&&gt(D,Q(0)),"distance-three separation angle");
const upper=x=>[x[1],x[1]];
function halfAngle(d) {
  const v=div(sub(add(Q(1),sq(d)),sq(U)),mul(Q(2),d));
  const guess=Math.ceil(1e8*Math.acos(Math.max(-1,Math.min(1,Number(v[0])/Number(S)))))+3;
  const t=Q(guess,100000000);
  check(gt(pi,t)&&gt(v,cos(t)),"half-angle arithmetic");
  return guess;
}
const data=[
  ["-4.69171578","0.00736861","0.91861021","0.66141870","0.84759221","0.09417954"],
  ["-4.40030360","0.00736861","0.85101091","0.62648965","0.78462736","0.09417954"],
  ["-4.21900548","0.00736861","0.80897736","0.60691707","0.74452956","0.09417954"],
  ["-4.15380434","0.00736861","0.79386562","0.60461536","0.72816260","0.09417954"],
  ["-4.07728656","0.00739815","0.77604586","0.59970981","0.70942179","0.09400232"],
  ["-3.96777712","0.00744324","0.75054140","0.58864826","0.68407868","0.09373174"],
  ["-3.87563195","0.00748334","0.72908200","0.57974031","0.66233503","0.09349117"]
];
const fixed=x=>Q(BigInt(x.replace(".","")),100000000n);
const t=x=>Q(x,100000000);
const lower=14900000,high=23289570;
const half=div(sq(U),Q(2)),tau=mul(Q(2),pi);
const polygon=k=>mul(half,mul(Q(k),sin(div(tau,Q(k)))));
check(gt(sin(t(lower)),div(U,Q(2))),"long boundary chords");
const cache=new Map();
function at(i) {
  if(!cache.has(i)){
    const s=sin(t(i)),z=div(s,U);
    let k=Math.floor(1e8*Math.asin(Math.max(0,Math.min(1,Number(z[0])/Number(S)))))-2;
    if(k<=0||!gt(div(pi,Q(2)),t(k))||!gt(z,sin(t(k))))k=0;
    cache.set(i,{s,a:t(2*k),cap:div(sin(t(2*i)),Q(2))});
  }
  return cache.get(i);
}

let boxes=0;
function areaLine(lambda,mu,constant,end){
  for(let d=3;d<=15;d++){
    const peak=div(tau,Q(d+1)),stack=[[lower,end]];
    while(stack.length){
      const [l,h]=stack.pop(); boxes++;
      const {s,a,cap}=at(l);
      if(gt(s,U))continue;
      const P=gt(a,peak)?
        mul(half,add(sin(a),mul(Q(d),sin(div(sub(tau,a),Q(d)))))):
        polygon(d+1);
      const bound=add(add(constant,mul(mu,Q(d))),mul(lambda,t(h)));
      if(gt(bound,sub(P,cap)))continue;
      check(h-l>1,"unresolved chord polygon box "+[d,l,h]);
      const m=Math.floor((l+h)/2);
      stack.push([l,m],[m,h]);
    }
  }
}
function checkShortPair(i,step,values) {
  const x=Q(i,1000),y=Q(i+step,1000);
  const span=sub(sq(mul(Q(4),U)),sq(mul(x,D)));
  // The derivative of x*C + sqrt((4U)^2-x^2 D^2) is negative
  // throughout the slab, since x*D^2/sqrt(span) is increasing.
  check(gt(mul(x,sq(D)),mul(C,sqrt(span))),"far norm upper bound monotonicity");
  const g=upper(add(mul(x,C),sqrt(span)));
  check(gt(sub(Q(1),sq(U)),sq(g))&&gt(sub(Q(1),sq(U)),sq(y)),
        "boundary half-angle monotonicity");
  const [lambda,mu,G,M,F,I]=values.map(fixed);
  check(gt(Q(0),lambda),"affine angular coefficient");
  const general=add(G,Q(1,10000)),minimum=add(M,Q(1,1000)),far=add(F,Q(1,1000));
  const interior=add(I,Q(1,20000));
  for(let k=3;k<=26;k++)check(gt(add(interior,mul(mu,Q(k))),polygon(k)),"interior polygon");
  for(const [constant,end] of [[general,high],[minimum,halfAngle(y)],[far,halfAngle(g)]])
    areaLine(lambda,mu,constant,end);
  const excess=add(add(mul(lambda,pi),mul(Q(128),mu)),
                   add(add(mul(Q(12),general),add(minimum,far)),mul(Q(13),interior)));
  check(gt(Q(0),excess),"distance-three pair still allowed at "+i);
}
for(let i=812;i<826;i+=2)checkShortPair(i,2,data[(i-812)/2]);
console.log("PASS B=14: no two-edge path between boundary owners at cyclic distance at least four.");
console.log(`PASS B=14: no two-edge path at cyclic distance three (${boxes} area boxes).`);
