// Exact degree-and-area exclusion for the normalized n=27, b=14 case.
"use strict";
const {S,Q,add,sub,mul,div,sq,check,gt,sin,pi}=require("./exact-interval.js");

const r=Q(2288,10000);
const largerRadius=Q(230796,1000000);
check(gt(sin(div(pi,Q(13))),largerRadius),"at least fourteen boundary owners");
check(gt(sin(div(pi,Q(7))),div(largerRadius,sub(Q(1),mul(Q(2),largerRadius)))),
      "at least nine core disks");
const turns=Q(233,1000);
check(gt(sin(turns),largerRadius),"outer arc half-angle upper bound");
check(gt(pi,mul(Q(13),turns)),"boundary owner directions preserve cyclic order");
const separatedAngle=sub(pi,mul(Q(12),turns));
check(gt(separatedAngle,Q(0))&&gt(div(pi,Q(2)),separatedAngle),"chord angle domain");
check(gt(mul(sub(Q(1),largerRadius),sin(separatedAngle)),largerRadius),
      "nonconsecutive boundary disks must be disjoint");

const ticks=10_000_000;
const low=1_406_000, high=2_308_450;
const t=x=>Q(x,ticks);
check(gt(sin(t(high)),r)&&gt(sub(pi,mul(Q(13),t(high))),t(low)),"half-angle domain");
check(gt(sin(t(low)),div(r,Q(2))),"long chord domain");

const lambda=Q(-224874,100000);
const mu=Q(8857,1000000);
const boundaryConstant=Q(34636,100000);
const interiorConstant=Q(8287,100000);
const halfR2=div(sq(r),Q(2));
const tau=mul(Q(2),pi);
const innerArea=d=>mul(halfR2,mul(Q(d),sin(div(tau,Q(d)))));
for(let d=3;d<=26;d++){
  check(gt(add(interiorConstant,mul(mu,Q(d))),innerArea(d)), "interior degree "+d);
}

const cache=new Map();
function angleLower(left){
  if(!cache.has(left)){
    const z=div(sin(t(left)),r);
    let a=0,b=15_707_963;
    while(b-a>1){
      const m=Math.floor((a+b)/2);
      if(gt(z,sin(t(m))))a=m;
      else b=m;
    }
    cache.set(left,t(2*a));
  }
  return cache.get(left);
}

let checked=0;
for(let d=3;d<=15;d++){
  const even=div(tau,Q(d+1));
  const stack=[[low,high]];
  while(stack.length){
    const [l,h]=stack.pop();
    checked++;
    if(gt(sin(t(l)),r))continue;
    const theta=angleLower(l);
    const poly=gt(theta,even)
      ?mul(halfR2,add(sin(theta),mul(Q(d),sin(div(sub(tau,theta),Q(d))))))
      :innerArea(d+1);
    const cap=sub(poly,div(sin(t(2*l)),Q(2)));
    const comparison=add(add(boundaryConstant,mul(mu,Q(d))),mul(lambda,t(h)));
    if(gt(comparison,cap))continue;
    check(h-l>1,"unresolved boundary degree/angle box "+[d,l,h]);
    const m=Math.floor((l+h)/2);
    stack.push([l,m],[m,h]);
  }
}

const excess=add(add(mul(lambda,pi),mul(mu,Q(128))),
                 add(mul(Q(14),boundaryConstant),mul(Q(13),interiorConstant)));
check(gt(Q(0),excess),"degree-weighted area contradiction");
console.log(`PASS: n=27 and b=14 excluded at U=0.2288, ${checked} angle boxes.`);
console.log(`Upper bound on area minus pi: ${Number(excess[1])/Number(S)}`);
