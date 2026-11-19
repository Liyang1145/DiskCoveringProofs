// Exact trigonometric checks for the eight/nine-disk wheel and the n=27 core.
"use strict";
const {Q,add,sub,mul,div,sq,sqrt,check,gt,sin,cos,pi}=require("./exact-interval.js");

const R8=div(Q(1),add(Q(1),mul(Q(2),cos(div(mul(Q(2),pi),Q(7))))));
const R9=sub(sqrt(Q(2)),Q(1));
for(const [b,r,t] of [[7,R8,Q(463,1000)],[8,R9,Q(428,1000)]]){
  const half=div(pi,Q(2));
  const gap=sub(pi,mul(Q(b-3),t));
  check(gt(sin(div(pi,Q(b-1))),r),"minimum wheel size");
  check(gt(sin(t),r)&&gt(half,gap)&&gt(gap,Q(0)),"wheel angle domain");
  check(gt(sin(gap),mul(Q(2),r))&&gt(cos(t),mul(Q(2),r)),"no outer chords");
  check(gt(Q(1),mul(Q(5),sq(r))),"convex perimeter contribution");
  const d=div(pi,Q(b)),radial=mul(Q(2),mul(r,cos(d)));
  check(gt(Q(1),radial)&&gt(radial,Q(0)),"wheel construction center norm");
}

const coreLower=div(Q(1),add(Q(3),sqrt(Q(2))));
check(gt(coreLower,Q(2265409,10000000))&&gt(Q(2265410,10000000),coreLower),
      "18-owner lower bound enclosure");
const U=Q(230796,1000000);
const ell=mul(U,add(Q(2),sqrt(Q(2))));
const second=sub(mul(Q(2),ell),sub(Q(1),U));
check(gt(Q(788,1000),ell)&&gt(Q(807,1000),second),"upper bounds on the two owner norms");

function shortArc(d,t){
  const c=cos(t);
  check(gt(c,d),"endpoint quadratic is decreasing on the norm range");
  const excess=sub(add(Q(1),sq(d)),add(mul(Q(2),mul(d,c)),sq(U)));
  check(gt(excess,Q(0)),"owner arc reaches past the proposed bound");
}

shortArc(ell,Q(103,1000));
shortArc(second,Q(141,1000));
const shifted=Q(57,1000),cut=Q(786,1000),third=Q(845,1000);
check(gt(third,add(ell,shifted)),"third owner norm");
check(gt(shifted,sub(ell,cut))&&gt(sub(add(Q(1),U),ell),shifted),"shift domain");
check(gt(sq(cut),sub(sq(ell),sq(shifted))),"two expanded disks miss a shift direction");
shortArc(cut,Q(98,1000));
shortArc(third,Q(187,1000));

const triangle=mul(Q(3,4),sqrt(Q(3))), loss=Q(387,10000);
check(gt(sub(add(triangle,Q(1,2)),Q(147325,83694)),loss),"single boundary edge loss");
check(gt(Q(1101,500),sqrt(add(Q(9,4),mul(Q(3,2),sqrt(Q(3)))))),"two boundary edges");
check(gt(sub(add(triangle,Q(1)),Q(1101,500)),mul(Q(2),loss)),"two-edge loss");
const q10=Q(385,1000),q11=Q(3646,10000);
for(const [n,q,bmin] of [[10,q10,8],[11,q11,9]]){
  const q2=sq(q);
  check(gt(Q(1,2),q)&&gt(Q(1),mul(Q(5),q2))
        &&gt(sin(div(pi,Q(bmin-1))),q),"small core owner count");
  for(let b=bmin;b<n;b++){
    const d=div(pi,Q(b)),s=sin(d),c=cos(d);
    const G=add(sub(d,mul(s,c)),mul(s,sqrt(sub(q2,sq(s)))));
    const area=add(mul(Q(b),G),
                   mul(q2,add(mul(Q(2*n-b-2),triangle),mul(Q(b),sub(Q(1,2),loss)))));
    check(gt(pi,area),"small core area "+[n,b]);
  }
}

const reach=q=>mul(U,add(Q(1),div(Q(1),q)));
shortArc(reach(Q(3611,10000)),Q(205,1000)); // Previously proved n=12 lower bound.
shortArc(reach(q11),Q(201,1000));
const L17=reach(q10);
shortArc(L17,Q(172,1000));
shortArc(sub(mul(Q(2),L17),sub(Q(1),U)),Q(217,1000));
console.log("PASS: exact wheel bounds for 8 and 9, and area bounds for 10 and 11 disks.");
console.log("PASS: inward owner constraints for b=15,16,17,18 at U=0.230796.");
