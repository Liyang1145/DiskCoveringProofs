// Exact area certificate using disjoint angular sectors for boundary faces.
"use strict";
const {
  S,Q,add,sub,mul,div,sq,sqrt,check,gt,sin,cos,pi,max,min
}=require("./exact-interval.js");
const point=x=>[x,x];
const hi=x=>point(x[1]);
const lo=x=>point(x[0]);
const neg=x=>sub(Q(0),x);
const absolute=([a,b])=>max([-a,b]);
const square=([a,b])=>[a<=0n&&b>=0n?0n:min([sq(point(a))[0],sq(point(b))[0]]),
                       max([sq(point(a))[1],sq(point(b))[1]])];
const cross=(a,b)=>sub(mul(a[0],b[1]),mul(a[1],b[0]));
const difference=(a,b)=>a.map((x,i)=>sub(x,b[i]));
const n=27;
const A=mul(Q(3,4),sqrt(Q(3)));
const base=Q(387,10000),earBase=Q(97,1000);
const scopes={
  global:{
    radius:224640, rows:[
      {b:15,offset:0,right:0,good:base,bad:base},
      {b:16,offset:-22000,right:51000,good:Q(81,1000),bad:Q(10315,100000)},
      {b:17,offset:-25000,right:65500,good:Q(94,1000),bad:Q(94,1000)}
    ]
  },
  b15:{radius:225080,rows:[{b:15,offset:-3000,right:20000,good:base,bad:Q(76,1000)}]},
  b17:{radius:225400,rows:[{b:17,offset:-25000,right:66500,earLeft:-150000,
                           good:Q(1105,10000),bad:Q(127,1000)}]}
};
const scope=scopes[process.argv[2]??"global"];
check(scope!==undefined,"choose global, b15 or b17");
const r=Q(scope.radius,1000000),r2=sq(r);
check(gt(sin(div(pi,Q(13))),r)&&gt(Q(1),mul(Q(5),r2)),"geometric domain");
check(gt(sin(div(pi,Q(7))),div(r,sub(Q(1),mul(Q(2),r)))),"at least nine inner disks");
check(gt(Q(1),mul(r,add(Q(3),sqrt(Q(2))))),"eighteen-owner core obstruction");
check(gt(sub(add(A,Q(1,2)),Q(147325,83694)),base),"universal single-edge loss");
check(gt(Q(1101,500),sqrt(add(Q(9,4),mul(Q(3,2),sqrt(Q(3)))))),"ear upper");
check(gt(sub(add(A,Q(1)),Q(1101,500)),earBase),"universal ear loss");

function geometry(b,offset) {
  const mean=div(pi,Q(b)),d=add(mean,Q(offset,1_000_000));
  const s=sin(d),c=cos(d),h=sqrt(sub(r2,sq(s)));
  const G=(t,s,c,h)=>add(sub(t,mul(s,c)),mul(s,h));
  const value=G(d,s,c,h);
  const deriv=add(mul(Q(2),sq(s)),div(mul(c,sub(r2,mul(Q(2),sq(s)))),h));
  const cache=new Map();
  function at(i) {
    if(!cache.has(i)){
      const v=Q(i,1_000_000);
      const t=add(d,v),s=sin(t),c=cos(t),h=sqrt(sub(r2,sq(s)));
      const J=sub(add(value,mul(deriv,v)),G(t,s,c,h));
      cache.set(i,{t,s,c,h,a:sub(c,h),J});
    }
    return cache.get(i);
  }
  function arc(l,u) {
    const L=at(l),H=at(u);
    const J=l>0?L.J[0]:u<0?H.J[0]:0n;
    return {
      t:[L.t[0],H.t[1]],s:[L.s[0],H.s[1]],c:[H.c[0],L.c[1]],
      h:[H.h[0],L.h[1]],a:[L.a[0],H.a[1]],J:point(max([0n,J]))
    };
  }
  return {at,arc,fan:add(value,mul(deriv,sub(mean,d)))};
}

const tangents=[];
for(let i=40;i<=190;i++){
  const x=Q(i,100),h=sqrt(sub(Q(1),div(sq(x),Q(4))));
  const f=add(div(x,Q(2)),mul(x,h));
  const slope=add(Q(1,2),div(sub(Q(1),div(sq(x),Q(2))),h));
  tangents.push({x,f,slope});
}
const young=Q(147325,83694)[1];
function fUpper(z) {
  // Choose a tangent near the maximizer over z. Its enclosure is exact.
  const guessed=Math.min(Number(z[1])/Number(S),Math.max(1.61,Number(z[0])/Number(S)));
  const index=Math.max(40,Math.min(190,Math.round(guessed*100)))-40;
  const {x,f,slope}=tangents[index];
  return point(min([young,add(f,mul(slope,sub(z,x)))[1]]));
}

function edge(a,b,w) {
  const leftX=mul(a.a,a.c),rightX=mul(b.a,b.c);
  const leftY=mul(a.a,a.s),rightY=mul(b.a,b.s);
  const cx=point(max([div(add(a.c,a.h),a.s)[1],div(add(b.c,b.h),b.s)[1]]));
  const cy=point(max([div(mul(a.c,a.h),square(a.s))[1],div(mul(b.c,b.h),square(b.s))[1]]));
  const xError=hi(mul(w,cx));
  const yError=hi(mul(w,cy));
  const dx=add(sub(rightX,leftX),[-xError[1],xError[1]]);
  const dy=add(add(add(rightY,leftY),w),[-yError[1],yError[1]]);
  const y=[max([0n,dy[0]]),dy[1]];
  const q=add(square(dx),square(y));
  if(gt(q,mul(Q(4),r2)))return null;
  const L=sqrt([q[0],min([q[1],mul(Q(4),r2)[1]])]);
  const z=div(L,r);
  return {L,z,dx,y,xError,yError,leftX,rightX,leftY,rightY};
}

function tightLength(a,b,w,e) {
  const dx=sub(e.rightX,e.leftX),dy=add(e.rightY,e.leftY);
  const ideal=sqrt(add(square(dx),square(dy)));
  if(ideal[0]<=0n)return e;
  let maxSquared=0n, projection=null;
  // The feasible displacement of the edge is in the convex hull of
  // the four choices which assign the entire budget to one endpoint.
  for(const [arc,orientation] of [[a,-1],[b,1]]){
    const s=mul(Q(orientation),arc.s);
    const radial=mul(Q(orientation),div(w,arc.s));
    for(const sign of [-1,1]){
      const t=mul(Q(sign),div(arc.h,arc.s));
      const x=mul(radial,sub(arc.c,mul(t,s)));
      const y=mul(radial,add(s,mul(t,arc.c)));
      maxSquared=max([maxSquared,add(square(add(dx,x)),square(add(dy,y)))[1]]);
      const pr=div(add(mul(dx,x),mul(dy,y)),ideal)[0];
      projection=projection===null?pr:min([pr,projection]);
    }
  }
  const L=[max([e.L[0],ideal[0]+projection]),min([e.L[1],sqrt(point(maxSquared))[1]])];
  if(L[0]>L[1])return null;
  return {...e,L,z:div(L,r)};
}

function outsideSectorPenalty(a,b,w,info) {
  if(info.L[0]<=0n)return Q(0);
  const {L,z,dx,y,xError,yError,leftX,rightX,leftY,rightY}=info;
  const radicand=sub(r2,div(square(L),Q(4)));
  const height=add(r,sqrt([max([0n,radicand[0]]),max([0n,radicand[1]])]));
  const k=div(height,L);
  const mx=div(add(add(leftX,rightX),[0n,xError[1]]),Q(2));
  const dy=hi(add(w,yError));
  const my=div(add(sub(rightY,leftY),[-dy[1],dy[1]]),Q(2));
  const ny=div(dx,L);
  const nx=div(y,L);
  const px=sub(mx,mul(height,[max([0n,nx[0]]),min([S,nx[1]])]));
  const py=add(my,mul(height,ny));
  const eta=add(a.t,b.t),s=sin(eta),c=cos(eta);
  const sideMargin=(near,far)=>{
    const ideal=add(div(mul(far.a,s),Q(2)),mul(k,sub(mul(far.a,c),near.a)));
    const atNear=neg(div(add(k,div(div(near.h,near.s),Q(2))),near.s));
    const drift=absolute(sub(div(c,Q(2)),mul(k,s)));
    const atFar=div(sub(add(div(s,Q(2)),mul(k,c)),mul(div(far.h,far.s),point(drift))),far.s);
    const coeff=point(min([atNear[0],atFar[0]]));
    return add(ideal,mul(w,coeff));
  };
  const leftMargin=sideMargin(a,b),rightMargin=sideMargin(b,a);
  const norm=sqrt(add(square(px),square(py)));
  const outerMargin=sub(sub(Q(1),r),norm);
  const innerMargin=sub(norm,r);
  const m=point(max([0n,min([r[0],leftMargin[0],rightMargin[0],outerMargin[0],innerMargin[0]])]));
  return div(mul(lo(z),square(div(m,r))),Q(4));
}

function oneEdge(g,target,bad) {
  if(!gt(target,base))return 0;
  const budget=mul(Q(2),mul(sub(target,base),r2));
  const low=-102000, high=g.right;
  check(gt(g.at(low).J,budget)&&gt(g.at(high).J,budget),"one-edge window");
  const ticks=10_000_000;
  const top=Number((budget[1]*BigInt(ticks))/S)+1;
  const stack=[[low,high,low,high,0,top]];
  let boxes=0;
  while(stack.length){
    const [l,h,m,n,x,y]=stack.pop();
    boxes++;
    const a=g.arc(l,h),b=g.arc(m,n);
    const w=[Q(x,ticks)[0],Q(y,ticks)[1]];
    const paid=add(add(a.J,b.J),w);
    if(gt(paid,budget))continue;
    const coarse=edge(a,b,w);
    if(coarse===null)continue;
    function proves(e){
      let loss=add(sub(add(A,Q(1,2)),fUpper(e.z)),div(paid,mul(Q(2),r2)));
      if(bad&&!gt(loss,target))loss=add(loss,outsideSectorPenalty(a,b,w,e));
      return gt(loss,target);
    }
    if(proves(coarse))continue;
    const sharp=tightLength(a,b,w,coarse);
    if(sharp===null||proves(sharp))continue;
    split(stack,[l,h,m,n,x,y]);
  }
  return boxes;
}

function split(stack,box) {
  const widths=box.filter((_,i)=>i%2===0).map((x,i)=>box[2*i+1]-x);
  const width=Math.max(...widths),i=2*widths.indexOf(width);
  check(width>1,"unresolved angle box "+box);
  const mid=Math.floor((box[i]+box[i+1])/2);
  const left=box.slice(),right=box.slice();
  left[i+1]=mid;
  right[i]=mid;
  stack.push(left,right);
}

function earAreaByBudget(arcs,axes,W) {
  const weights=[Q(1,2),Q(1),Q(1,2)];
  const ideal=[],directions=[];
  for(let i=0;i<3;i++){
    const arc=arcs[i],axis=axes[i];
    const e=[cos(axis),i===0?neg(sin(axis)):sin(axis)];
    const J=[neg(e[1]),e[0]];
    ideal.push(e.map(x=>mul(arc.a,x)));
    const rad=div(Q(1),mul(weights[i],arc.s));
    const tang=div(arc.h,arc.s);
    directions.push([-1,1].map(sign=>e.map((x,j)=>mul(rad,add(x,mul(Q(sign),mul(tang,J[j])))))));
  }
  const I=add(add(cross(ideal[0],ideal[1]),cross(ideal[1],ideal[2])),cross(ideal[2],ideal[0]));
  let best=0n;
  for(const sign of [-1,1]){
    const D=mul(Q(sign),I);
    const p=directions.map((endpoints,i)=>{
      const v=difference(ideal[(i+1)%3],ideal[(i+2)%3]);
      return point(max(endpoints.map(u=>mul(Q(sign),cross(u,v))[1])));
    });
    let bound=max([D[1],...p.map(x=>add(D,mul(W,x))[1])]);
    for(let i=0;i<3;i++){
      const j=(i+1)%3;
      const q=point(max(directions[i].flatMap(x=>directions[j].map(y=>mul(Q(sign),cross(x,y))[1]))));
      const edgeCoefficient=add(D,div(add(mul(W,add(p[i],p[j])),mul(square(W),q)),Q(2)));
      bound=max([bound,edgeCoefficient[1]]);
    }
    best=max([best,bound]);
  }
  return div(point(best),Q(2));
}

function ear(g,target,earLeft) {
  const threshold=mul(Q(2),target);
  if(!gt(threshold,earBase))return 0;
  const budget=mul(r2,sub(threshold,earBase));
  const low=earLeft??-113000,high=g.right;
  check(gt(g.at(low).J,mul(Q(2),budget))&&gt(g.at(high).J,mul(Q(2),budget)),"ear window");
  const stack=[[low,high,low,high,low,high]];
  let boxes=0;
  while(stack.length){
    const box=stack.pop();
    boxes++;
    const [l,h,m,n,o,p]=box;
    const [a,b,c]=[g.arc(l,h),g.arc(m,n),g.arc(o,p)];
    const sigma=add(add(a.t,b.t),c.t);
    // The centers at the two ends are adjacent in the ear and therefore
    // no farther apart than 2r. Their far endpoints are no farther than 4r.
    if(gt(sin(lo(sigma)),mul(Q(2),r)))continue;
    const J=add(div(add(a.J,c.J),Q(2)),b.J);
    if(gt(J,budget))continue;
    const rem=point(max([0n,sub(budget,J)[1]]));
    const allowances=[div(mul(Q(2),rem),a.s),div(rem,b.s),div(mul(Q(2),rem),c.s)];
    function center(arc,axis,sign,x) {
      const s=sin(axis),c=cos(axis);
      const y=hi(div(mul(arc.h,x),arc.s));
      const a=add(arc.a,[0n,x[1]]);
      return [
        add(mul(a,c),mul([-y[1],y[1]],s)),
        add(mul(a,sign>0?s:neg(s)),mul([-y[1],y[1]],c))
      ];
    }
    const ab=add(mul(Q(2),b.t),c.t);
    const u=center(a,a.t,-1,allowances[0]),v=center(b,b.t,1,allowances[1]),
          w=center(c,ab,1,allowances[2]);
    const x=[sub(v[0],u[0]),sub(v[1],u[1])],y=[sub(w[0],v[0]),sub(w[1],v[1])];
    const area=div(point(absolute(sub(mul(x[0],y[1]),mul(x[1],y[0])))),Q(2));
    const chord=[add(x[0],y[0]),add(x[1],y[1])];
    if(gt(add(square(chord[0]),square(chord[1])),mul(Q(4),r2)))continue;
    if(gt(add(A,div(sub(J,area),r2)),threshold))continue;
    const tightArea=earAreaByBudget([a,b,c],[a.t,b.t,ab],rem);
    if(gt(add(A,div(sub(J,tightArea),r2)),threshold))continue;
    split(stack,box);
  }
  return boxes;
}

for(const {b,offset,right,earLeft,good,bad} of scope.rows){
  const g=geometry(b,offset);
  g.right=right;
  const paid=add(mul(Q(n-b-1),good),mul(Q(2*b-n+1),bad));
  const bound=add(mul(r2,sub(add(mul(Q(2*n-b-2),A),Q(b,2)),paid)),mul(Q(b),g.fan));
  check(gt(pi,bound),"area contradiction "+b);
  const goodBoxes=oneEdge(g,good,false);
  const badBoxes=gt(bad,good)?oneEdge(g,bad,true):0;
  const earBoxes=ear(g,bad,earLeft);
  console.log({b,goodBoxes,badBoxes,earBoxes});
}
console.log(`PASS: b=${scope.rows.map(row=>row.b).join(",")} at U=${scope.radius}/1000000, with apex sectors.`);
