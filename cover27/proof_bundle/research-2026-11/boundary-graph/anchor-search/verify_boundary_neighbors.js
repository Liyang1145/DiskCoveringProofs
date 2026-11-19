// Norm and graph constraints for the outer ring with 14 owners.
"use strict";
const {Q,add,sub,mul,div,sq,sqrt,check,gt,sin,cos,pi}=require("../exact-interval.js");

const U=Q(230796,1000000);
const T=Q(2328957,10000000);
const tau=mul(Q(2),pi);
const ticks=x=>Q(x,1000000);
check(gt(sin(T),U)&&gt(div(pi,Q(2)),T),"boundary half-angle cap");

for(const [floor,number] of [[812000,8],[833896,9],[905600,10]]) {
  const s=sub(ticks(floor),U);
  const halfAngle=div(pi,Q(number-1));
  check(gt(s,U)&&gt(mul(s,sin(halfAngle)),U),"angular capacity at first radial exit");
  console.log(`PASS B=14: D1 >= ${floor}/1e6 forces at least ${number} interior neighbors of the boundary.`);
}

const capTwo=mul(Q(2),U);
const capThree=ticks(498000);
const exactCapThree=mul(U,add(Q(1),div(Q(2),sqrt(Q(3)))));
check(gt(capThree,exactCapThree),"three-disk core norm cap");

function angularCap(floor,apex,trial) {
  const a=ticks(floor);
  const witness=add(apex,U);
  const angle=ticks(trial);
  check(gt(sq(a),add(sq(witness),sq(U)))&&gt(pi,angle),"monotonicity for small apex witness");
  // Lower bound for cos of the angle between the witness and either owner.
  const numerator=sub(add(sq(a),sq(witness)),sq(U));
  const denominator=mul(Q(2),mul(a,witness));
  check(gt(numerator,mul(denominator,cos(angle))),"small apex witness angle");
  return mul(Q(2),angle);
}

for(const [floor,count,q2,q3] of [[876600,12,178712,222229],[892960,11,145344,201436]]) {
  const repeatsOfCapTwo=count-10;
  const smaller=angularCap(floor,capTwo,q2);
  const larger=angularCap(floor,capThree,q3);
  const total=add(add(mul(Q(repeatsOfCapTwo),smaller),larger),
                  mul(Q(13-repeatsOfCapTwo),mul(Q(2),T)));
  check(gt(tau,total),"small apices still allow all boundary gaps");
  console.log(`PASS B=14: ${count} distinct boundary-face apices require D1 < ${floor}/1e6.`);
}

// D1 bounds every outer norm. For cyclic separation k the center distance
// is at least 2*D1*sin(pi-(14-k)*T). Each graph step costs at most 2U.
for(const [floor,step] of [[812000,5],[953569,4]]) {
  const a=ticks(floor),halfGap=sub(pi,mul(Q(14-step),T));
  check(gt(halfGap,Q(0))&&gt(div(pi,Q(2)),halfGap),"angle domain for three-edge paths");
  check(gt(mul(a,sin(halfGap)),mul(Q(3),U)),"three-edge path between distant owners");
  const hypothesis=step===5?"":" if both endpoint norms are at least 953569/1e6";
  console.log(`PASS B=14: no path of length at most three spans ${step} or more outer steps${hypothesis}.`);
}
const overlapGap=mul(Q(2),sub(pi,mul(Q(11),T)));

const delta=mul(Q(2),sub(pi,mul(Q(12),T)));
function checkRepeatedApex(a,norm) {
  const d=ticks(a),v=ticks(norm);
  const e=mul(Q(2),U);
  check(gt(sq(d),add(sq(v),sq(e))),"norm monotonicity for repeated apex");
  const num=sub(add(sq(d),sq(v)),sq(e)),denom=mul(Q(2),mul(d,v));
  check(gt(num,mul(denom,cos(div(delta,Q(2))))),"repeated apex at a small norm");
}
for(const [floor,norm] of [[868210,461592],[897775,498000]]) {
  checkRepeatedApex(floor,norm);
  console.log(`PASS B=14: at D1 >= ${floor}/1e6 every repeated apex has norm > ${norm}/1e6.`);
}

const gamma=ticks(605000),eta=ticks(409000);
check(gt(div(pi,Q(2)),gamma)&&gt(div(pi,Q(2)),eta),"ray angle domain");
check(gt(mul(ticks(812000),sin(gamma)),mul(Q(2),U)),"angular radius of a disk about an owner");
check(gt(mul(sub(ticks(812000),U),sin(eta)),U),"first radial exit angular bound");
check(gt(overlapGap,add(gamma,eta)),"ray separated by at least three outer steps");
console.log("PASS B=14: an inner neighbor can cover an outer owner's ray at radius >= D1-U only within two outer steps of every owner adjacent to that inner center.");

check(gt(overlapGap,mul(Q(2),eta)),"one inner disk reaching two distant outer-owner rays");
console.log("PASS B=14: the owner rays reached by any inner disk above D1-U are contained in three consecutive outer-owner rays.");
