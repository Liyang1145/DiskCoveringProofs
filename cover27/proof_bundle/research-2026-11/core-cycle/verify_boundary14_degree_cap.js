// Separate degree multipliers for the outer and inner Voronoi cells.
"use strict";
const {S,Q,add,sub,mul,div,sq,check,gt,sin,pi}=require("./exact-interval.js");
const r=Q(230796,1000000);
const ticks=10_000_000;
const t=x=>Q(x,ticks);
const low=1_139_400,high=2_328_957;
check(gt(sin(t(high)),r)&&gt(sub(pi,mul(Q(13),t(high))),t(low)),"half-angle range");
const lambda=Q(-22094,10000);
const outerDegree=Q(46256,10000000),innerDegree=Q(201157,10000000);
const outerConstant=Q(35880,100000),innerConstant=Q(2608,100000);
const twoPi=mul(Q(2),pi),halfR2=div(sq(r),Q(2));
const polygon=k=>mul(halfR2,mul(Q(k),sin(div(twoPi,Q(k)))));
for(let k=3;k<=26;k++){
  check(gt(add(innerConstant,mul(innerDegree,Q(k))),polygon(k)),"inner degree "+k);
}
const cache=new Map();
function lowerChordAngle(l){
  if(!cache.has(l)){
    const z=div(sin(t(l)),r);
    if(!gt(z,Q(1,2))){
      cache.set(l,Q(0));
      return Q(0);
    }
    const guessed=Math.floor(ticks*Math.asin(Math.min(1,Number(z[0])/Number(S))))-2;
    if(guessed>0&&guessed<=15_707_963&&gt(z,sin(t(guessed)))){
      cache.set(l,t(2*guessed));
      return cache.get(l);
    }
    let a=0,b=15_707_963;
    while(b-a>1){
      const m=Math.floor((a+b)/2);
      if(gt(z,sin(t(m))))a=m;
      else b=m;
    }
    cache.set(l,t(2*a));
  }
  return cache.get(l);
}
function boundaryCap(d,theta){
  const even=div(twoPi,Q(d+1));
  return gt(theta,even)?
    mul(halfR2,add(sin(theta),mul(Q(d),sin(div(sub(twoPi,theta),Q(d)))))):
    polygon(d+1);
}
let boxes=0;
for(let d=3;d<=15;d++){
  const stack=[[low,high]];
  while(stack.length){
    const [l,h]=stack.pop();
    boxes++;
    if(gt(sin(t(l)),r))continue;
    const cap=boundaryCap(d,lowerChordAngle(l));
    const area=sub(cap,div(sin(t(2*l)),Q(2)));
    const line=add(add(outerConstant,mul(outerDegree,Q(d))),mul(lambda,t(h)));
    if(gt(line,area))continue;
    check(h-l>1,"unresolved degree and angle "+[d,l,h]);
    const m=Math.floor((l+h)/2);
    stack.push([l,m],[m,h]);
  }
}
const slope=sub(outerDegree,innerDegree);
check(gt(Q(0),slope),"monotonic degree bound");
const excess=add(add(mul(lambda,pi),mul(Q(128),innerDegree)),
  add(mul(Q(65),slope),add(mul(Q(14),outerConstant),mul(Q(13),innerConstant))));
check(gt(Q(0),excess),"outer degree sum 65 still allowed");
console.log(`PASS: b=14 at U=0.230796 requires outer degree sum at most 64 (${boxes} boxes).`);

// For each degree and each rational multiplier, enclose the maximum
// of the boundary-cell area minus its angle and minus lambda*angle.
const lambdas=Array.from({length:53},(_,i)=>Q(-2900+25*i,1000));
const caps=lambdas.map(()=>Array(16).fill(null));
for(let l=low;l<high;l+=250){
  const h=Math.min(high,l+250);
  if(gt(sin(t(l)),r))continue;
  const alpha=lowerChordAngle(l),chord=div(sin(t(2*l)),Q(2));
  const shifts=lambdas.map(lambda=>mul(lambda,t(h))[0]);
  for(let d=3;d<=15;d++){
    const upper=sub(boundaryCap(d,alpha),chord)[1];
    for(let j=0;j<lambdas.length;j++){
      const x=upper-shifts[j];
      const old=caps[j][d];
      if(old===null||x>old)caps[j][d]=x;
    }
  }
}

const interiors=new Map();
for(let d=50;d<=64;d++){
  const count=128-d,k=Math.floor(count/13),c=count%13;
  interiors.set(d,add(mul(Q(13-c),polygon(k)),mul(Q(c),polygon(k+1))));
}
const offsets=lambdas.map(lambda=>mul(lambda,pi)[1]);
const tally=Array.from({length:15},(_,i)=>({degreeSum:50+i,checked:0,excluded:0}));
const residual=[];
function visit(profile,minDegree,sum){
  const remaining=14-profile.length;
  if(remaining===0){
    if(sum<50)return;
    const stats=tally[sum-50];
    stats.checked++;
    const inner=interiors.get(sum)[1];
    const excluded=caps.some((bound,j)=>
      profile.reduce((s,d)=>s+bound[d],inner+offsets[j])<0n);
    if(excluded)stats.excluded++;
    else residual.push(profile.slice());
    return;
  }
  for(let d=minDegree;d<=15&&sum+remaining*d<=64;d++){
    profile.push(d);
    visit(profile,d,sum+d);
    profile.pop();
  }
}
visit([],3,0);
const checked=tally.reduce((n,t)=>n+t.checked,0);
check(checked===4059,"unexpected number of degree profiles");
console.log(`PASS: b=14 degree profiles, ${checked-residual.length} excluded of ${checked}, ${residual.length} retained.`);
if(process.argv[2]){
  const fs=require("node:fs");
  const report={
    scope:"Normalized n=27 covers at test radius 230796/1000000, with 14 boundary owners",
    degreeSum:[50,64],
    tested:checked,
    excluded:checked-residual.length,
    retained:residual.length,
    tally,
    residual
  };
  fs.writeFileSync(process.argv[2],JSON.stringify(report)+"\n");
}
