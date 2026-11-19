// Exact radial-shell angular bounds in the 14-owner branch.
"use strict";
const {S,Q,add,sub,mul,div,sq,sqrt,check,gt,sin,cos,pi}=require("../exact-interval.js");

const U=Q(230796,1000000);
const E=mul(Q(2),U);
const T=Q(2328957,10000000);
const delta=mul(Q(2),sub(pi,mul(Q(12),T)));
const A=div(delta,Q(2));
check(gt(sin(T),U)&&gt(A,Q(0))&&gt(div(pi,Q(2)),A),"outer angle domain");

function minimumCommonNorm(norm) {
  const d=Q(norm,1000000);
  const disc=sub(sq(E),sq(mul(d,sin(A))));
  check(gt(d,E)&&gt(disc,Q(0)),"inner shell radial bounds");
  return sub(mul(d,cos(A)),sqrt(disc));
}

for(const [outward,minInner] of [
  [812000,393670],[833896,419930],[868210,461592],
  [897775,498000],[901500,502620],[905600,507720],
  [908500,511330],[912000,515700]
]) {
  const low=minimumCommonNorm(outward);
  check(gt(low,Q(minInner,1000000)),"repeated apex can have a small norm");
  console.log(`PASS B=14: if D1 >= ${outward}/1e6, every repeated apex has norm > ${minInner}/1e6.`);
}

function angleBound(d,t) {
  check(gt(sq(d),add(sq(t),sq(E))),"angular monotonicity for unequal owner norms");
  const c=div(sub(add(sq(d),sq(t)),sq(E)),mul(Q(2),mul(d,t)));
  if(c[0]>=S)return Q(0);
  const p=Q(Math.ceil(1e8*Math.acos(Number(c[0])/Number(S)))+2,100000000);
  check(gt(pi,p)&&gt(c,cos(p)),"outward bound for an unequal owner angle");
  return p;
}

const radialRanks=[812000,842400,859000,869490,878000,884700,890000];
const targets=[413310,440650,456890,468460,477770,485140];
for(const [i,target] of targets.entries()) {
  const left=radialRanks[i],right=radialRanks[i+1];
  const t=Q(target,1000000);
  check(gt(delta,add(angleBound(Q(left,1000000),t),angleBound(Q(right,1000000),t))),
        "common neighbor can join two owners two steps apart");
  console.log(`PASS B=14: outer norm floors ${left}/1e6 and ${right}/1e6 require shared inner norm > ${target}/1e6.`);
}

for(const [d,sector] of [[812000,1281960],[901500,1452020],[905600,1460110]]) {
  const sep=mul(Q(d,1000000),sin(A));
  const a=Q(sector,2000000);
  check(gt(div(pi,Q(2)),a)&&gt(sep,div(E,Q(2)))&&gt(sep,mul(E,sin(a))),
        "turning angle lower bound at an interior common neighbor");
  console.log(`PASS B=14: at D1 >= ${d}/1e6, the sector angle between rays to owners two steps apart is > ${sector}/1e6.`);
}
