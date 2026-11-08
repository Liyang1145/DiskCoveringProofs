'use strict';
// Exact scalar certificate. The written proof supplies the geometric premises.
const fs=require('fs');
const I=require('./interval.js');
const {S,min,max,Q,point,add,sub,mul,div,sqrt,sq,check,gt,sin,cos,pi}=I;
const radius=process.argv.includes('--negative-control')?230001:229001;
const U=Q(radius,1000000),U2=sq(U),inv=div(Q(1),U2);
const A=mul(Q(3,4),sqrt(Q(3))),base=Q(387,10000),earBase=Q(97,1000);
const young=Q(147325,83694),earCap=Q(1101,500);
check(gt(sub(add(A,Q(1,2)),young),base),'one-edge constant');
check(gt(earCap,sqrt(add(Q(9,4),mul(Q(3,2),sqrt(Q(3)))))), 'ear constant');
check(gt(sub(add(A,Q(1)),earCap),earBase),'ear deficit');
check(gt(sin(div(pi,Q(13))),U)&&gt(Q(1),mul(Q(5),U2)),'geometric domain');
const G=t=>{const s=sin(t);return add(sub(t,mul(s,cos(t))),mul(s,sqrt(sub(U2,sq(s)))));};
const f=x=>add(div(x,Q(2)),mul(x,sqrt(sub(Q(1),div(sq(x),Q(4))))));
const singleTangents=[];
for(let k=1100;k<=1610;k+=10){
  const z=Q(k,1000),h=sqrt(sub(Q(1),div(sq(z),Q(4))));
  const D=add(Q(1,2),div(sub(Q(1),div(sq(z),Q(2))),h));
  if(gt(D,Q(0)))singleTangents.push({z,D,F:f(z),key:k});
}
// H is the common-disk ear upper bound as a concave function of x^2+y^2.
const earTangents=[];
for(let k=2500;k<=5400;k+=100){
  const z=Q(k,1000),h=sqrt(mul(z,sub(Q(8),z)));
  const F=k<=4000?div(add(z,h),Q(4)):div(mul(add(z,Q(4)),h),Q(16));
  const D=k<=4000?add(Q(1,4),div(sub(Q(4),z),mul(Q(4),h))):
    div(add(sub(mul(Q(4),z),sq(z)),Q(8)),mul(Q(8),h));
  check(gt(D,Q(0)),'ear tangent increasing');
  earTangents.push({z,D,F,key:k});
}
const configurations={
  16:{e:Q(8,100),shift:Q(2,100),single:[-52500,36300],ear:[-67300,42300]},
  17:{e:Q(6,100),shift:Q(0),single:[-32400,24600],ear:[-33900,25400]},
  18:{e:Q(44,1000),shift:Q(0),single:[-17400,15300]},
};
const results=[];
const transcript={radius:String(radius)+'/1000000',scale:String(S),cases:[],passed:false};
for(let b=14;b<=26;b++){
  const cfg=configurations[b],e=cfg?cfg.e:base,d=div(pi,Q(b));
  const anchor=cfg?sub(d,cfg.shift):d;
  check(gt(anchor,Q(0))&&gt(U,sin(anchor)),'anchor domain');
  const sa=sin(anchor),ha=sqrt(sub(U2,sq(sa)));
  const slope=add(mul(Q(2),sq(sa)),div(mul(cos(anchor),sub(U2,mul(Q(2),sq(sa)))),ha));
  const intercept=add(G(anchor),mul(slope,sub(d,anchor)));
  const cache=new Map();
  const at=i=>{
    if(!cache.has(i)){
      const offset=Q(i,1000000),t=add(anchor,offset),s=sin(t),c=cos(t);
      check(gt(t,Q(0))&&gt(U,s),'window domain');
      const h=sqrt(sub(U2,sq(s)));
      const J=sub(add(G(anchor),mul(slope,offset)),add(sub(t,mul(s,c)),mul(s,h)));
      cache.set(i,{s,a:sub(c,h),J});
    }
    return cache.get(i);
  };
  const lowJ=(l,h)=>max([0n,l>0?at(l).J[0]:h<0?at(h).J[0]:0n]);
  const edge=(l,h,m,n)=>{
    const al=at(l).a,ah=at(h).a,am=at(m).a,an=at(n).a;
    const diff=point(max([0n,ah[1]-am[0],an[1]-al[0]]));
    const angle=add(anchor,Q(h+n,2000000));
    return div(sqrt(add(sq(diff),mul(Q(4),mul(mul(ah,an),sq(sin(angle)))))),U);
  };
  const report={b,oneEdgeBoxes:0,twoEdgeBoxes:0,splits:0,leaves:[]};
  if(cfg){
    const budget=mul(Q(2),mul(sub(e,base),U2));
    const [lo,hi]=cfg.single;
    check(gt(at(lo).J,budget)&&gt(at(hi).J,budget),'single window '+b);
    const stack=[[lo,hi,lo,hi]];
    while(stack.length){
      const box=stack.pop(),[l,h,m,n]=box;report.oneEdgeBoxes++;
      check(report.oneEdgeBoxes<500000,'single box limit');
      const J=point(lowJ(l,h)+lowJ(m,n));
      if(gt(J,budget)){report.leaves.push({type:'single',box,kind:'J'});continue;}
      const ideal=edge(l,h,m,n),smin=point(min([at(l).s[0],at(m).s[0]]));
      const rem=point(max([0n,budget[1]-J[0]]));
      const fixed=add(add(A,Q(1,2)),div(J,mul(Q(2),U2)));
      let witness;
      for(const {z,D,F,key} of singleTangents){
        const coeff=sub(div(inv,Q(2)),div(D,sq(smin)));
        const loss=add(sub(fixed,add(F,mul(D,sub(ideal,z)))),mul(point(min([0n,coeff[0]])),rem));
        if(gt(loss,e)){witness=key;break;}
      }
      if(witness!==undefined){report.leaves.push({type:'single',box,kind:'tangent',z:witness});continue;}
      check(Math.max(h-l,n-m)>1,'unresolved single '+[b,...box]);
      if(h-l>=n-m){const k=Math.floor((l+h)/2);stack.push([l,k,m,n],[k,h,m,n]);}
      else{const k=Math.floor((m+n)/2);stack.push([l,h,m,k],[l,h,k,n]);}
      report.splits++;
    }
    if(cfg.ear){
      const target=mul(Q(2),e),budget=mul(sub(target,earBase),U2);
      const [lo,hi]=cfg.ear;
      check(gt(at(lo).J,mul(Q(2),budget))&&gt(at(hi).J,mul(Q(2),budget)),'ear window '+b);
      const stack=[[lo,hi,lo,hi,lo,hi,0n,budget[1]]];
      while(stack.length){
        const box=stack.pop(),[l,h,m,n,p,q,tlo,thi]=box;report.twoEdgeBoxes++;
        check(report.twoEdgeBoxes<1000000,'ear box limit');
        const J=div(point(lowJ(l,h)+2n*lowJ(m,n)+lowJ(p,q)),Q(2));
        if(gt(add(J,point(tlo)),budget)){
          report.leaves.push({type:'ear',box,kind:'J'});continue;
        }
        const capped=min([thi,max([0n,budget[1]-J[0]])]);
        if(gt(add(sub(add(A,Q(1)),earCap),mul(add(J,point(tlo)),inv)),target)){
          report.leaves.push({type:'ear',box,kind:'base'});continue;
        }
        const ell1=edge(l,h,m,n),ell2=edge(m,n,p,q);
        const ss=[at(l).s,at(m).s,at(p).s].map(x=>sq(point(x[0])));
        let witness;
        for(const {z,D,F,key} of earTangents){
          let passed=true;
          for(const t of [tlo,capped]){
            for(let vertex=0;vertex<3;vertex++){
              const v=div(mul(point(t),Q(vertex===1?1:2)),ss[vertex]);
              const x=vertex<2?add(ell1,v):ell1,y=vertex>0?add(ell2,v):ell2;
              const area=add(F,mul(D,sub(add(sq(x),sq(y)),z)));
              const loss=add(sub(add(A,Q(1)),area),mul(add(J,point(t)),inv));
              if(!gt(loss,target)){passed=false;break;}
            }
            if(!passed)break;
          }
          if(passed){witness=key;break;}
        }
        if(witness!==undefined){report.leaves.push({type:'ear',box,kind:'tangent',z:witness});continue;}
        const widths=[h-l,n-m,q-p];
        const maxAngle=Math.max(...widths);
        // Balance angular variation against residual variation; this affects speed only.
        const residualWidth=Number(capped-tlo)/Number(U2[0])*1000000;
        if(residualWidth>2*maxAngle&&capped-tlo>1n){
          const mid=(tlo+capped)/2n;
          stack.push([l,h,m,n,p,q,tlo,mid],[l,h,m,n,p,q,mid,capped]);
        }else{
          check(maxAngle>1,'unresolved ear '+[b,...box]);
          const dim=widths.indexOf(maxAngle),a=box.slice(0,6),c=box.slice(0,6);
          const mid=Math.floor((a[2*dim]+a[2*dim+1])/2);
          a[2*dim+1]=mid;c[2*dim]=mid;
          stack.push([...a,tlo,capped],[...c,tlo,capped]);
        }
        report.splits++;
      }
    }else check(gt(earBase,mul(Q(2),e)),'base ear pays two edges');
  }else check(gt(earBase,mul(Q(2),base)),'base grouping');
  const upper=add(mul(U2,add(mul(Q(50-b),A),mul(Q(b),sub(Q(1,2),e)))),mul(Q(b),intercept));
  check(gt(pi,upper),'area contradiction '+b);
  report.gapLower=String(pi[0]-upper[1])+'/'+String(S);
  results.push({b,oneEdgeBoxes:report.oneEdgeBoxes,twoEdgeBoxes:report.twoEdgeBoxes,
    gapLowerDecimal:Number(pi[0]-upper[1])/Number(S)});
  transcript.cases.push(report);
  console.log(results.at(-1));
}
transcript.passed=true;
if(process.argv.includes('--write'))fs.writeFileSync(__dirname+'/certificate.json',JSON.stringify(transcript,(_,v)=>typeof v==='bigint'?v.toString():v));
console.log('PASS: scalar inequalities at U='+radius+'/1000000; written geometry required.');
