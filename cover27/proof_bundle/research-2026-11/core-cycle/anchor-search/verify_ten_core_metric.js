// The ten exposed inner centers have only short chords in core order.
"use strict";
const {Q,add,sub,mul,div,sq,check,gt,sin,cos,pi}=require("../exact-interval.js");

const U=Q(230796,1000000);
const s=Q(670703,1000000);
const d=sub(s,U);
const T=Q(351292,1000000);
check(gt(mul(s,sin(T)),U)&&gt(div(pi,Q(2)),T),"ten-core half-angle cap");
check(gt(pi,mul(Q(8),T)),"core arcs spanning at least three owners");
const theta=sub(pi,mul(Q(7),T));
const theta5=sub(pi,mul(Q(5),T));
check(gt(theta,Q(0))&&gt(div(pi,Q(2)),theta5),"three- to five-step distance domain");
check(gt(mul(d,sin(theta)),U),"a three-step center pair could share a Voronoi edge");
console.log("PASS B=14: in the ten-vertex core cycle, each chord skips just one core vertex.");

// A chord bounds a triangular ear on the three consecutive vertices.
// If two norm floors are large enough, its corresponding side is too long.
const theta2=sub(pi,mul(Q(8),T));
const distanceLimit=mul(Q(2),U);
for(const [x,y] of [[725000,725000],[614000,774000]]) {
  const a=Q(x,1000000),b=Q(y,1000000);
  const c=cos(mul(Q(2),theta2));
  check(gt(a,mul(b,c))&&gt(b,mul(a,c)),"core chord radius corner");
  const separation=sub(add(sq(a),sq(b)),mul(Q(2),mul(mul(a,b),c)));
  check(gt(separation,sq(distanceLimit)),"ear chord radial floor");
  console.log(`PASS B=14: core norm floors ${x}/1e6 and ${y}/1e6 forbid a chord spanning two core steps.`);
}
for(const [floor,cap,angle] of [
  [901500,751000,351292],[905600,719000,349066],
  [909000,695000,347268],[912600,672000,345332]
]) {
  const radius=sub(Q(floor*1000-1000,1000000000),U);
  const upperAngle=Q(angle,1000000);
  const gap=mul(Q(2),sub(pi,mul(Q(8),upperAngle)));
  check(gt(mul(radius,sin(upperAngle)),U)&&gt(gap,Q(0))
        &&gt(div(pi,Q(2)),gap),"short core chord angle");
  check(gt(mul(Q(cap,1000000),sin(gap)),distanceLimit),
        "an endpoint of a short core chord could have large norm");
  console.log(`PASS B=14: at D1 >= ${floor}/1e6, each core chord endpoint has norm < ${cap}/1e6.`);
}
