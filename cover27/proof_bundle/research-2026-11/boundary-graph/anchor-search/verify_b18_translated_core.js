// Area exclusion for 18 owners with three jointly short boundary arcs.
"use strict";
const {S,Q,add,sub,mul,div,sq,sqrt,check,gt,sin,cos,pi}=require("../exact-interval.js");

const r=Q(22672,100000);
const L=mul(r,add(Q(2),sqrt(Q(2))));
const t=x=>Q(x,100000000);
const lo=t(77328000),hi=t(77407051);
const r2=sq(r);
const A=mul(Q(3,4),sqrt(Q(3)));
const cut=Q(387,10000);
const point=x=>[x,x];
const upper=x=>point(x[1]);
const sqrtNonnegative=([a,b])=>sqrt([a>0n?a:0n,b]);
check(gt(hi,L)&&gt(L,lo)&&sub(Q(1),r)[0]===lo[0],"first norm interval");
check(gt(sin(div(pi,Q(13))),r)&&gt(Q(1),mul(Q(5),r2)),"coverage and concavity domain");
check(gt(sub(add(A,Q(1,2)),Q(147325,83694)),cut),"single boundary edge loss");
check(gt(Q(1101,500),sqrt(add(Q(9,4),mul(Q(3,2),sqrt(Q(3)))))),"two-edge area bound");
check(gt(sub(add(A,Q(1)),Q(1101,500)),mul(Q(2),cut)),"two-edge loss");

const T=Q(22871,100000);
check(gt(sin(T),r),"universal half-angle bound");
check(gt(sub(add(Q(1),r),L),sqrtNonnegative(sub(sq(L),sq(lo)))),"translation radius is available");
check(gt(sub(add(Q(1),r),L),sub(L,lo)),"second-smallest norm translation is available");

function cap(d) {
  // At the maximum reach the half-angle is asin(r). Use the
  // radial expression below that maximum and the universal cap above.
  if(!gt(sub(Q(1),r2),sq(d)))return T;
  const c=div(sub(add(Q(1),sq(d)),r2),mul(Q(2),d));
  const guess=Math.ceil(100000000*Math.acos(Math.min(1,Number(c[0])/Number(S))))+3;
  check(gt(pi,t(guess))&&gt(c,cos(t(guess))),"owner arc upper bound");
  return t(guess);
}

function G(angle) {
  const s=sin(angle);
  return add(sub(angle,mul(s,cos(angle))),mul(s,sqrt(sub(r2,sq(s)))));
}

const fixed=mul(r2,add(mul(Q(34),A),mul(Q(18),sub(Q(1,2),cut))));
const b=18, mean=div(pi,Q(b));
let boxes=0, skipped=0;
function checkBox(l,h) {
  if(gt(t(l),L)){skipped++;return;}
  const x=t(l),y=t(h);
  const v=upper(sub(mul(Q(2),L),x));
  const dx=sub(sq(L),sq(x));
  if(dx[1]<0n){skipped++;return;}
  const w=upper(add(L,sqrtNonnegative(dx)));
  const first=cap(y),second=cap(v),third=cap(w);
  check(gt(mean,first)&&gt(mean,second),"first and second arc caps below the mean");
  const remaining=sub(pi,add(first,second));
  const restMean=div(remaining,Q(16));
  let area=add(G(first),G(second));
  if(gt(restMean,third)) {
    area=add(area,add(G(third),mul(Q(15),G(div(sub(remaining,third),Q(15))))));
  } else {
    area=add(area,mul(Q(16),G(restMean)));
  }
  if(gt(pi,add(fixed,area))){boxes++;return;}
  check(h-l>1,"unresolved norm interval "+[l,h]);
  const mid=Math.floor((l+h)/2);
  checkBox(l,mid);
  checkBox(mid,h);
}
checkBox(77328000,77407051);
console.log("PASS B=18: no strictly covered normalized configuration at radius 0.22672 ("+boxes+" norm intervals, "+skipped+" outside the domain).");
