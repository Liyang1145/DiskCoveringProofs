// Exact exclusion using the common Voronoi-edge angle at both endpoints.
"use strict";
const {S,Q,add,sub,mul,div,sq,check,gt,sin,cos,pi}=require("./exact-interval.js");

const r=Q(229360,1000000);
const halfR2=div(sq(r),Q(2));
const tau=Q(0);
const lambda=Q(-2376376,1000000);
const innerWeight=Q(353826,1000000);
const mean=div(pi,Q(14));
const twoPi=mul(Q(2),pi);
const clampLo=Q(-995,1000)[0],clampHi=Q(995,1000)[1];
const coefficients=[
  [Q(-234877,1000000),Q(-10622996,1000000)],
  [Q(697799,1000000),Q(-10623008,1000000)],
  [Q(501534,1000000),Q(-12527453,1000000)]
];
const ticks=10_000_000;
const low=1_331_285,high=2_314_203;
const t=x=>Q(x,ticks);
const point=x=>[x,x];
const upper=x=>point(x[1]);
const lower=x=>point(x[0]);
const max=(x,y)=>x>y?x:y;
const min=(x,y)=>x<y?x:y;

check(gt(sin(t(high)),r)&&gt(sub(pi,mul(Q(13),t(high))),t(low)),"outer angle domain");
check(gt(sin(t(low)),div(r,Q(2))),"outer chord is longer than r");
const R=Q(230796,1000000), T=Q(233,1000);
const gap=sub(pi,mul(Q(12),T));
check(gt(R,r)&&gt(sin(T),R)&&gt(pi,mul(Q(13),T)),"owner ordering");
check(gt(sin(div(pi,Q(13))),R),"at least fourteen owners");
check(gt(gap,Q(0))&&gt(div(pi,Q(2)),gap)
      &&gt(mul(sub(Q(1),R),sin(gap)),R),"no outer chords");
check(gt(sin(div(pi,Q(7))),div(R,sub(Q(1),mul(Q(2),R)))),"eight exposed inner owners");

function floating(a) { return Number(a)/Number(S); }

function asinLower(x) {
  const n=Math.floor(1e8*Math.asin(Math.min(1,floating(x))))-2;
  if(n<=0)return Q(0);
  const q=Q(n,100000000);
  if(gt(div(pi,Q(2)),q)&&gt(point(x),sin(q)))return lower(q);
  return Q(0);
}

function acosUpper(x) {
  if(x<=0n)return upper(div(pi,Q(2)));
  if(x>=S)return Q(0);
  const n=Math.ceil(1e8*Math.acos(floating(x)))+2;
  const q=Q(n,100000000);
  if(gt(pi,q)&&gt(point(x),cos(q)))return upper(q);
  return upper(div(pi,Q(2)));
}

// Upper bound for sin(theta) - weight*theta on the indicated interval.
// Floating point only chooses a rational tangent point. Concavity supplies
// the bound for every such point, including when that proposal is poor.
function support(weight,lo,hi) {
  const theta=Math.acos(Math.max(-1,Math.min(1,floating(weight[0]))));
  const guess=Math.min(floating(hi[1]),Math.max(floating(lo[0]),theta));
  let q=Q(Math.floor(1e8*guess),100000000);
  if(q[0]<0n||!gt(pi,q))q=Q(1);
  const c=cos(q);
  const a=sub(sin(q),mul(c,q));
  const m=sub(c,weight);
  return point(max(add(a,mul(m,lo))[1],add(a,mul(m,hi))[1]));
}

function ownerWeight(d,lo,hi) {
  const [a,m]=coefficients[Math.min(d-3,2)];
  let [u,v]=add(a,mul(m,sub([t(lo)[0],t(hi)[1]],mean)));
  if(d>=6){
    const z=Q(43+5*(d-5),100)[0];
    u=max(u,z); v=max(v,z);
  }
  return [min(max(u,clampLo),clampHi),min(max(v,clampLo),clampHi)];
}

const K=upper(mul(Q(2),support(innerWeight,Q(0),upper(pi))));
const C=add(sub(mul(halfR2,add(mul(Q(13),mul(twoPi,innerWeight)),mul(Q(78),K))),
                mul(Q(50),tau)),mul(lambda,pi));
const target=lower(div(sub(Q(0),C),Q(14)));
const angleCache=new Map(),ownerCache=new Map();

function leftEndpoint(l) {
  if(!angleCache.has(l)){
    const arc=t(l);
    const s=sin(arc);
    const z=div(s,r)[0];
    const alpha=lower(mul(Q(2),asinLower(z)));
    angleCache.set(l,{impossible:gt(s,r),alpha,short:sin(t(2*l))});
  }
  return angleCache.get(l);
}

function owner(d,l,h) {
  const key=[d,l,h].join(",");
  if(!ownerCache.has(key)){
    const left=leftEndpoint(l);
    const w=ownerWeight(d,l,h);
    const up=upper(w);
    const cap=add(support(up,left.alpha,upper(pi)),mul(up,twoPi));
    const inner=mul(Q(2*(d-2)),support(div(add(w,innerWeight),Q(2)),Q(0),upper(pi)));
    const area=sub(mul(halfR2,sub(add(cap,inner),mul(Q(d),K))),div(left.short,Q(2)));
    const part=add(sub(area,mul(lambda,t(h))),mul(tau,Q(d)));
    ownerCache.set(key,{w,part,left});
  }
  return ownerCache.get(key);
}

let checked=0,leaves=0,worst=null;
for(let d=3;d<=15;d++){
  for(let e=d;e<=15;e++){
    const stack=[[low,high,low,high]];
    while(stack.length){
      const [l,h,m,n]=stack.pop();
      checked++;
      if(leftEndpoint(l).impossible||leftEndpoint(m).impossible)continue;
      const a=owner(d,l,h),b=owner(e,m,n);
      const x=div(sub(add(a.left.short,b.left.short),mul(Q(2),r)),mul(Q(2),r))[0];
      const beta=upper(mul(Q(2),acosUpper(x)));
      const shared=support(div(add(a.w,b.w),Q(2)),Q(0),beta);
      const total=add(div(add(a.part,b.part),Q(2)),mul(sq(r),shared));
      if(gt(target,total)){
        leaves++;
        worst=worst===null?total[1]:max(worst,total[1]);
        continue;
      }
      check(Math.max(h-l,n-m)>1,"unresolved pair "+[d,e,l,h,m,n]);
      if(h-l>=n-m){
        const mid=Math.floor((l+h)/2);
        stack.push([l,mid,m,n],[mid,h,m,n]);
      }else{
        const mid=Math.floor((m+n)/2);
        stack.push([l,h,m,mid],[l,h,mid,n]);
      }
    }
  }
}
check(worst!==null&&gt(Q(0),add(C,mul(Q(14),point(worst)))),"strict area contradiction");
console.log(`PASS: b=14 at U=0.229360, ${checked} angle boxes, ${leaves} paid leaves.`);


