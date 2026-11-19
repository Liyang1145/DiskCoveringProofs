// Exact scalar certificate for n=27 and n=28 area lower bounds.
// Adapted from the n=26 local certificate.
"use strict";
const {S,floor,max,Q,add,sub,mul,div,sq,sqrt,check,gt,sin,cos,pi}=require("./exact-interval.js");
const n=Number(process.argv[2]??27);
const configurations={
  27:{u:224410,minBoundary:14,shifts:{16:-22000},widths:{16:[76000,48000]}},
  28:{u:220001,minBoundary:15,shifts:{16:-8644,17:-10000},widths:{16:[46000,32500],17:[44000,42000]}}
};
const cfg=configurations[n];
check(cfg!==undefined,"n must be 27 or 28");
const r=Q(cfg.u,1000000),r2=sq(r);
const A=mul(Q(3,4),sqrt(Q(3)));
const base=Q(387,10000),earBase=Q(97,1000);
const f=x=>add(div(x,Q(2)),mul(x,sqrt(sub(Q(1),div(sq(x),Q(4))))));
const Young=Q(147325,83694);
check(gt(sub(add(A,Q(1,2)),Young),base),"single-edge loss");
check(gt(Q(1101,500),sqrt(add(Q(9,4),mul(Q(3,2),sqrt(Q(3)))))),"ear upper");
check(gt(sub(add(A,Q(1)),Q(1101,500)),earBase),"ear loss");
check(gt(sin(div(pi,Q(cfg.minBoundary-1))),r)&&gt(Q(1),mul(Q(5),r2)),"geometric domain");
const G=d=>{let s=sin(d);return add(sub(d,mul(s,cos(d))),mul(s,sqrt(sub(r2,sq(s)))));};
check(gt(sin(div(pi,Q(7))),div(r,sub(Q(1),mul(Q(2),r)))),"core bound");
const rows=[];
for(let b=cfg.minBoundary;b<=n-9;b++){
  const mean=div(pi,Q(b));
  const shift=Q(cfg.shifts[b]??0,1000000);
  const d=add(mean,shift);
  const s=sin(d);
  const p=add(mul(Q(2),sq(s)),div(mul(cos(d),sub(r2,mul(Q(2),sq(s)))),sqrt(sub(r2,sq(s)))));
  const fan=sub(G(d),mul(p,shift));
  check(gt(r,sin(d)),"fan domain");
  const uncorrected=add(mul(r2,add(mul(Q(2*n-2-b),A),Q(b,2))),mul(Q(b),fan));
  const needed=div(sub(uncorrected,pi),mul(Q(b),r2));
  const lossTarget=max([base[0],needed[1]+S/1000000n]);
  const e=[lossTarget,lossTarget];
  if(gt(e,base)){

    const [left,right]=cfg.widths[b]??[34000,34000];
    const budget=mul(Q(2),mul(sub(e,base),r2));
    const cache=new Map();
    const at=i=>{
      if(!cache.has(i)){
        const offset=Q(i,1000000),t=add(d,offset),s=sin(t),c=cos(t);
        const h=sqrt(sub(r2,sq(s)));
        const J=sub(add(G(d),mul(p,offset)),add(sub(t,mul(s,c)),mul(s,h)));
        cache.set(i,{s,a:sub(c,h),h,J});
      }
      return cache.get(i);
    };
    check(gt(at(-left).J,budget)&&gt(at(right).J,budget),"Jensen window "+b);
    const tangents=[];
    for(let i=1250;i<=1610;i+=10){
      const t=Q(i,1000),z=sqrt(sub(Q(1),div(sq(t),Q(4))));
      const D=add(Q(1,2),div(sub(Q(1),div(sq(t),Q(2))),z));
      if(gt(D,Q(0)))tangents.push({t,D,F:f(t)});
    }
    const inv=div(Q(1),mul(Q(2),r2));
    const stack=[[-left,right,-left,right]];
    let boxes=0;
    const point=x=>[x,x];
    const lowJ=(l,h)=>l>0?at(l).J[0]:h<0?at(h).J[0]:0n;
    const edgeBound=(l,h,m,n,loWeight,hiWeight)=>{
      const al=at(l).a,ah=at(h).a,am=at(m).a,an=at(n).a;
      const diff=point(max([0n,ah[1]-am[0],an[1]-al[0]]));
      const sine=point(sin(add(d,Q(h+n,2000000)))[1]);
      const cosine=point(cos(add(d,Q(l+m,2000000)))[1]);
      const dx=mul(diff,cosine),dy=mul(add(ah,an),sine);
      const shiftX=[],shiftY=[];
      for(const [entry,weight] of [[at(l),loWeight],[at(m),hiWeight]]){
        const s=point(entry.s[0]),h=point(entry.h[1]);
        const weightedS=mul(s,weight);
        shiftX.push(div(add(cosine,mul(div(h,s),sine)),weightedS)[1]);
        shiftY.push(div(add(sine,mul(div(h,s),cosine)),weightedS)[1]);
      }
      return w=>{
        const x=add(dx,mul(point(max(shiftX)),w)),y=add(dy,mul(point(max(shiftY)),w));
        return div(sqrt(add(sq(x),sq(y))),r);
      };
    };
    while(stack.length){
      const [l,h,m,n]=stack.pop(); boxes++;
      const J=point(max([0n,lowJ(l,h)+lowJ(m,n)]));
      if(gt(J,budget))continue;
      const rem=point(max([0n,budget[1]-J[0]]));
      const ell=edgeBound(l,h,m,n,Q(1),Q(1));
      const first=ell(Q(0));
      const last=ell(rem);
      const fixed=add(add(A,Q(1,2)),mul(J,inv));
      let passed=false;
      for(const {t,D,F} of tangents){
        const loss0=sub(fixed,add(F,mul(D,sub(first,t))));
        const loss1=sub(add(fixed,mul(rem,inv)),add(F,mul(D,sub(last,t))));
        if(gt(loss0,e)&&gt(loss1,e)){passed=true;break;}
      }
      if(passed)continue;
      check(Math.max(h-l,n-m)>1,"unresolved angular box "+[b,l,h,m,n]);
      if(h-l>=n-m){const k=Math.floor((l+h)/2);stack.push([l,k,m,n],[k,h,m,n]);}
      else {const k=Math.floor((m+n)/2);stack.push([l,h,m,k],[l,h,k,n]);}
    }
    console.log({b,boxes});
    if(gt(mul(Q(2),e),earBase)){
      // The two-edge group has endpoints weighted 1/2 and middle owner weighted 1.
      const earBudget=mul(r2,sub(mul(Q(2),e),earBase));
      check(gt(at(-left).J,mul(Q(2),earBudget))&&gt(at(right).J,mul(Q(2),earBudget)),"ear window "+b);
      const ears=[[-left,right,-left,right,-left,right]];
      let earBoxes=0;
      const earPeak=add(Q(2),mul(Q(2),sqrt(Q(3))));
      while(ears.length){
        const bounds=ears.pop(); earBoxes++;
        const [l,h,m,n,o,p]=bounds;
        const j=point(max([0n,floor(lowJ(l,h)+lowJ(o,p),2n)+lowJ(m,n)]));
        if(gt(j,earBudget))continue;
        const rem=point(max([0n,earBudget[1]-j[0]]));
        const x=edgeBound(l,h,m,n,Q(1,2),Q(1))(rem);
        const y=edgeBound(m,n,o,p,Q(1),Q(1,2))(rem);
        const twiceArea=mul(x,y);
        const loss=add(sub(A,div(twiceArea,Q(2))),div(j,r2));
        if(gt(loss,mul(Q(2),e)))continue;
        const v=point(max([Q(4)[1],add(sq(x),sq(y))[1]]));
        if(gt(earPeak,v)){
          const curved=div(mul(add(v,Q(4)),sqrt(mul(v,sub(Q(8),v)))),Q(16));
          const area=point(max([Q(2)[1],curved[1]]));
          const betterLoss=add(sub(add(A,Q(1)),area),div(j,r2));
          if(gt(betterLoss,mul(Q(2),e)))continue;
        }
        const widths=[h-l,n-m,p-o];
        const k=2*widths.indexOf(Math.max(...widths));
        check(bounds[k+1]-bounds[k]>1,"unresolved ear box "+[b,...bounds]);
        const mid=Math.floor((bounds[k]+bounds[k+1])/2);
        const left=bounds.slice(),right=bounds.slice();
        left[k+1]=mid; right[k]=mid;
        ears.push(left,right);
      }
      console.log({b,earBoxes});
    }

  }
  const upper=add(mul(r2,add(mul(Q(2*n-2-b),A),mul(Q(b),sub(Q(1,2),e)))),mul(Q(b),fan));
  check(gt(pi,upper),"area contradiction "+b);
  rows.push([b,Number(pi[0]-upper[1])/Number(S)]);
}
console.log(rows);
console.log(`PASS: all five strict n=${n} area inequalities at U=${cfg.u}/1000000`);



