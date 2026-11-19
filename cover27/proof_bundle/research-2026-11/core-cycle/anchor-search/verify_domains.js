// Exact radius bounds for the innermost unit-boundary owner, B=14.
"use strict";
const {S,Q,add,sub,mul,div,sq,sqrt,check,gt,sin,cos,pi}=require("../exact-interval.js");
const U=Q(230796,1000000);
const t=x=>Q(x,10_000_000);
const low=1_139_400,high=2_328_957,short=1_490_000;
const twoPi=mul(Q(2),pi),h2=div(sq(U),Q(2));
const lambda=Q(-3107832,1000000),mu=Q(794517,100000000);
const usual=Q(550260,1000000),small=Q(413170,1000000),inner=Q(90730,1000000);
const polygon=k=>mul(h2,mul(Q(k),sin(div(twoPi,Q(k)))));
check(gt(sin(t(high)),U)&&gt(sub(pi,mul(Q(13),t(high))),t(low)),"half-angle range");
for(let k=3;k<=26;k++){
  check(gt(add(inner,mul(mu,Q(k))),polygon(k)),"interior area line");
}

function chordAngle(left){
  const z=div(sin(t(left)),U);
  if(!gt(z,Q(1,2)))return Q(0);
  const j=Math.floor(1e7*Math.asin(Math.min(1,Number(z[0])/Number(S))))-2;
  if(j>0&&j<15_707_963&&gt(z,sin(t(j))))return t(2*j);
  return Q(0);
}

let boxes=0;
for(const [end,cap] of [[high,usual],[short,small]]){
  for(let d=3;d<=15;d++){
    const even=div(twoPi,Q(d+1)),stack=[[low,end]];
    while(stack.length){
      const [a,b]=stack.pop(); boxes++;
      if(gt(sin(t(a)),U))continue;
      const theta=chordAngle(a);
      const P=gt(theta,even)
        ?mul(h2,add(sin(theta),mul(Q(d),sin(div(sub(twoPi,theta),Q(d))))))
        :polygon(d+1);
      const area=sub(P,div(sin(t(2*a)),Q(2)));
      const affine=add(add(cap,mul(mu,Q(d))),mul(lambda,t(b)));
      if(gt(affine,area))continue;
      check(b-a>1,"unresolved angle "+[d,a,b]);
      const m=Math.floor((a+b)/2);
      stack.push([a,m],[m,b]);
    }
  }
}
const excess=add(add(mul(lambda,pi),mul(Q(128),mu)),
                 add(add(mul(Q(13),usual),small),mul(Q(13),inner)));
check(gt(Q(0),excess),"short-owner contradiction");
const s=sin(t(short));
const d0=sub(cos(t(short)),sqrt(sub(sq(U),sq(s))));
check(gt(d0,Q(812,1000)),"minimum owner norm");
check(gt(sq(Q(974,1000)),sub(Q(1),sq(U))),"inward normalization cap");

const q=Q(3324,10000),q2=sq(q),A=mul(Q(3,4),sqrt(Q(3))),loss=Q(387,10000);
check(gt(sin(div(pi,Q(9))),q)&&gt(Q(1),mul(Q(5),q2)),"thirteen-disk counts and fan domain");
check(gt(sub(add(A,Q(1,2)),Q(147325,83694)),loss),"single-edge loss");
check(gt(Q(1101,500),sqrt(add(Q(9,4),mul(Q(3,2),sqrt(Q(3)))))),"two-edge area");
check(gt(sub(add(A,Q(1)),Q(1101,500)),mul(Q(2),loss)),"two-edge loss");
for(let b=10;b<=12;b++){
  const d=div(pi,Q(b)),s=sin(d),c=cos(d);
  const G=add(sub(d,mul(s,c)),mul(s,sqrt(sub(q2,sq(s)))));
  const area=add(mul(Q(b),G),
    mul(q2,add(mul(Q(24-b),A),mul(Q(b),sub(Q(1,2),loss)))));
  check(gt(pi,area),"thirteen-disk area "+b);
}
check(gt(Q(926,1000),mul(U,add(Q(1),div(Q(1),q)))),"maximum owner norm");
const smaller=[
  [sin(div(pi,Q(3))),498],[sin(div(pi,Q(4))),558],[sin(div(pi,Q(5))),624],
  [Q(1,2),693],[Q(1,2),693],
  [div(Q(1),add(Q(1),mul(Q(2),cos(div(twoPi,Q(7)))))),750],
  [sub(sqrt(Q(2)),Q(1)),789],[Q(385,1000),831],[Q(3646,10000),864],[Q(3611,10000),871]
];
check(mul(Q(2),U)[1]<=Q(461592000,1_000_000_000)[0],"at most two disks have lower bound one");
for(const [lower,cap] of smaller)
  check(gt(Q(cap,1000),mul(U,add(Q(1),div(Q(1),lower)))),"nested core radius bound "+cap);
for(const [b,q,cap] of [
  [14,Q(3385,10000),912615794],
  [15,Q(3611,10000),869943051],
  [16,Q(3646,10000),863807520],
  [17,Q(385,1000),830266130],
  [18,sub(sqrt(Q(2)),Q(1)),787986834]
]){
  check(gt(Q(cap,1_000_000_000),mul(U,add(Q(1),div(Q(1),q)))),"outer norm upper bound "+b);
}
check(gt(sin(div(pi,Q(13))),U)&&gt(sin(div(pi,Q(7))),div(U,sub(Q(1),mul(Q(2),U)))),
      "normalized boundary count range");
console.log(`PASS: all B=14 owner half-angles exceed 0.149 (${boxes} boxes).`);
console.log("PASS: B=14 minimum owner norm lies in [0.812, 0.926] at U=0.230796.");
console.log("PASS: nested core radius constants for 1 through 12 disks and the 14–18 owner radial bounds.");
