// Each high-norm boundary owner is nearest along its ray to the core.
"use strict";
const {Q,add,sub,mul,div,sq,check,gt,sin,cos,pi}=require("../exact-interval.js");

const U=Q(230796,1000000);
const T=Q(2328957,10000000);
const K=mul(Q(2),sub(pi,mul(Q(12),T)));
const ticks=x=>Q(x,1000000);
const low=908500;
const a=ticks(low),s=sub(a,U);
const top=ticks(974000);
const alphaPeak=sub(Q(1),sq(U));
check(gt(sin(T),U)&&gt(K,Q(0))&&gt(pi,K),"angular gap domain");
check(gt(a,s),"radial monotonicity domain");

function cap(d,trial) {
  const x=ticks(d),t=ticks(trial);
  const threshold=div(sub(add(Q(1),sq(x)),sq(U)),mul(Q(2),x));
  check(gt(pi,t)&&gt(threshold,cos(t)),"owner angular cap");
  return t;
}

function verifyBin(lo,hi,alpha) {
  const d=ticks(lo),h=ticks(hi);
  const gap=sub(K,add(T,alpha));
  check(gt(gap,Q(0)),"positive angular gap");
  const increase=add(sub(sq(d),sq(top)),mul(Q(2),mul(s,sub(top,mul(d,cos(gap))))));
  // For every d_j in this bin the squared distance to the point s*e_i
  // increases with d_j and angular gap. It increases as d_i decreases.
  check(gt(increase,Q(0)),"other outer owner could win at the radial probe");
  check(gt(h,d),"empty norm bin");
}

const width=25;
let count=0;
for(let lo=low;lo<974000;lo+=width) {
  const hi=Math.min(lo+width,974000);
  const x=hi/1000000,r=230796/1000000;
  const trial=Math.ceil(1000000*Math.acos((1+x*x-r*r)/(2*x)))+1;
  const alpha=gt(alphaPeak,sq(ticks(hi)))?cap(hi,trial):T;
  verifyBin(lo,hi,alpha);
  count++;
}
console.log("PASS B=14: at D1 >= 0.9085, each owner is closer than all other owners on its ray at radius 0.677704 ("+count+" norm bins).");

const v=ticks(534800);
const edge=mul(Q(2),U);
check(gt(sq(a),add(sq(v),sq(edge)))&&gt(add(sq(s),sq(U)),sq(v))
      &&gt(sq(s),add(sq(v),sq(U))),"angular monotonicity for small ray witnesses");
const alpha=ticks(391210),beta=ticks(302187);
function angularBound(r,w,angle) {
  const numerator=sub(add(sq(r),sq(v)),sq(w));
  check(gt(numerator,mul(Q(2),mul(mul(r,v),cos(angle)))),"small ray witness angle cap");
}
angularBound(a,edge,alpha);
angularBound(s,U,beta);
check(gt(K,add(alpha,beta)),"small inner witness can span two outer steps");
console.log("PASS B=14: a boundary-adjacent inner disk of norm <=0.5348 can reach an owner ray at radius >=0.677704 only within one outer step of every adjacent owner.");
