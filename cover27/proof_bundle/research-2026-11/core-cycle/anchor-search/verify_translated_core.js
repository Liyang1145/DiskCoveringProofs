// Conditional area exclusions using the three least boundary-owner norms.
"use strict";
const {S,Q,add,sub,mul,div,sq,sqrt,check,gt,sin,cos,pi}=require("../exact-interval.js");

const t=x=>Q(x,100000000);
const point=x=>[x,x];
const upper=x=>point(x[1]);
const sqrtNonnegative=([a,b])=>sqrt([a>0n?a:0n,b]);
const A=mul(Q(3,4),sqrt(Q(3)));
const cut=Q(387,10000);
check(gt(sub(add(A,Q(1,2)),Q(147325,83694)),cut),"single boundary edge loss");
check(gt(Q(1101,500),sqrt(add(Q(9,4),mul(Q(3,2),sqrt(Q(3)))))),"two-edge area bound");
check(gt(sub(add(A,Q(1)),Q(1101,500)),mul(Q(2),cut)),"two-edge loss");

function verify({b,r,scale,L,first,last,T}) {
  const lo=t(first),hi=t(last),r2=sq(r);
  check(gt(hi,L)&&gt(L,lo)&&sub(Q(1),r)[0]===lo[0],"first norm interval");
  check(gt(sin(div(pi,Q(13))),r)&&gt(Q(1),mul(Q(5),r2)),"coverage and concavity domain");
  const translatedCore=sub(add(Q(1),r),L);
  check(gt(translatedCore,sqrtNonnegative(sub(sq(L),sq(lo)))),"third norm translation is available");
  check(gt(translatedCore,sub(L,lo)),"second norm translation is available");
  check(gt(sin(T),r),"universal half-angle bound");

  function cap(d) {
    // The angular radius is increasing below sqrt(1-r^2).
    if(!gt(sub(Q(1),r2),sq(d)))return T;
    const c=div(sub(add(Q(1),sq(d)),r2),mul(Q(2),d));
    const guess=Math.ceil(1e8*Math.acos(Math.min(1,Number(c[0])/Number(S))))+3;
    check(gt(pi,t(guess))&&gt(c,cos(t(guess))),"owner arc upper bound");
    return t(guess);
  }

  function G(angle) {
    const s=sin(angle);
    return add(sub(angle,mul(s,cos(angle))),mul(s,sqrt(sub(r2,sq(s)))));
  }

  const fixed=mul(r2,add(mul(Q(52-b),A),mul(Q(b),sub(Q(1,2),cut))));
  let boxes=0, skipped=0;
  function checkBox(l,h) {
    const x=t(l),y=t(h);
    if(gt(x,L)){skipped++;return;}
    const d2=upper(sub(mul(Q(2),L),x));
    const d3=upper(add(L,sqrtNonnegative(sub(sq(L),sq(x)))));
    const caps=[cap(y),cap(d2),cap(d3)].sort((a,b)=>a[0]<b[0]?-1:a[0]>b[0]?1:0);
    let remaining=pi,total=Q(0),count=b;
    for(const bound of caps) {
      if(!gt(div(remaining,Q(count)),bound))break;
      remaining=sub(remaining,bound);
      total=add(total,G(bound));
      count--;
    }
    const area=add(total,mul(Q(count),G(div(remaining,Q(count)))));
    if(gt(pi,add(fixed,area))){boxes++;return;}
    check(h-l>1,"unresolved norm interval "+[b,l,h]);
    const mid=Math.floor((l+h)/2);
    checkBox(l,mid);
    checkBox(mid,h);
  }

  checkBox(first,last);
  console.log(`PASS B=${b}: at U=${scale}/1e6, ${boxes} radial intervals contradict area (${skipped} empty intervals).`);
}

const r15=Q(225300,1000000);
const r18=Q(226720,1000000);
verify({b:15,r:r15,scale:225300,L:mul(r15,add(Q(1),Q(10000,3611))),
        first:77470000,last:84922691,T:Q(227252,1000000)});
verify({b:18,r:r18,scale:226720,L:mul(r18,add(Q(2),sqrt(Q(2)))),
        first:77328000,last:77407051,T:Q(228710,1000000)});
