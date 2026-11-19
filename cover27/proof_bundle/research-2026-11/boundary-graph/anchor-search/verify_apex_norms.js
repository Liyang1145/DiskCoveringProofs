// B=14 bounds for a center adjacent to two prescribed boundary owners.
"use strict";
const {S,Q,add,sub,mul,div,sq,check,gt,sin,cos,pi}=require("../exact-interval.js");
const U=Q(230796,1000000),T=Q(2328957,10000000),E=mul(Q(2),U);
const ranks=[812000,842400,859000,869490,878000,884700,890000];
const grid=1000000;
const point=x=>[x,x];
const R=x=>Q(x,grid);
check(gt(sin(T),U),"boundary arc half-angle cap");

function acosUpper(x) {
  if(x[0]>=S)return Q(0);
  const q=Q(Math.ceil(1e8*Math.acos(Math.max(-1,Number(x[0])/Number(S))))+2,100000000);
  check(gt(pi,q)&&gt(x,cos(q)),"arccos upper comparison");
  return q;
}

function angleCap(norm,hi) {
  const t=R(hi),d=R(norm);
  if(gt(d,add(t,E)))return null;
  const v=sub(add(sq(d),sq(t)),sq(E));
  const beta=acosUpper(div(v,mul(Q(2),mul(d,t))));
  const f=R(Math.min(hi+461592,974000));
  const unitThreshold=div(sub(add(Q(1),sq(f)),sq(U)),mul(Q(2),f));
  // On these intervals the unit-boundary arc size grows with norm.
  check(gt(sub(Q(1),sq(U)),sq(f)),"arc monotonicity");
  return add(beta,acosUpper(unitThreshold));
}

function verify(left,right,step,norm) {
  const cap=R(norm),d=R(Math.min(left,right));
  check(gt(sq(d),add(sq(cap),sq(E))),"intersection half-angle monotonicity");
  const target=mul(Q(2),sub(pi,mul(Q(14-step),T)));
  const p=angleCap(left,norm),q=angleCap(right,norm);
  let boxes=0;
  function possible(owner) {
    const end=Math.min(974000,norm+461592),r=R(norm);
    let best=0n;
    for(let a=owner;a<=end;a+=20){
      const b=Math.min(a+20,end);
      const x=R(a),y=R(b);
      if(gt(x,add(r,E)))continue;
      const v=div(sub(add(sq(x),sq(r)),sq(E)),mul(Q(2),mul(x,r)));
      const z=div(sub(add(Q(1),sq(y)),sq(U)),mul(Q(2),y));
      const bound=add(acosUpper(v),acosUpper(z))[1];
      if(bound>best)best=bound;
      boxes++;
    }
    return point(best);
  }
  if(p!==null&&q!==null&&!gt(target,add(p,q)))
    check(gt(target,add(possible(left),possible(right))),"unresolved apex norm "+[left,right,step,norm]);
  console.log(`PASS B=14: common neighbor norm > ${norm}/1e6 for rank floors ${left},${right} and separation ${step} (${boxes} boxes).`);
}

for(const [i,cap] of [382000,400000,411000,420000,427000,433000].entries())
  verify(ranks[i],ranks[i+1],2,cap);
