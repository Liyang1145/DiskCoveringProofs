'use strict';
// Certifies a triangle-shape lemma, not a new 26-disk lower bound.
const fs=require('fs');
const I=require('../round-20261107/interval.js');
const {S,Q,point,add,sub,mul,div,sqrt,check,gt,sin,cos,pi,min,max}=I;
const sq=([a,b])=>{
  if(a>=0n)return mul([a,b],[a,b]);
  if(b<=0n)return mul([-b,-a],[-b,-a]);
  return [0n,div(point(max([a*a,b*b])),Q(S))[1]];
};
const sqrt3=sqrt(Q(3)),A=mul(Q(3,4),sqrt3),kappa=Q(4,5),h=Q(1,5);
if(process.argv.includes('--negative-control')){
  const delta=Q(1,100);
  const loss=mul(div(sqrt3,Q(2)),sub(Q(1),cos(mul(Q(2),delta))));
  const falsePenalty=mul(Q(9,10),mul(Q(2),sq(delta)));
  check(gt(falsePenalty,loss),'counterexample for false constant');
  console.log('PASS: kappa=0.9 is false at angles pi/3-0.01, pi/3, pi/3+0.01.');
  process.exit(0);
}
const eta=Q(3,50),mu=Q(31,50);
check(gt(div(pi,Q(6)),eta),'analytic core angle domain');
const coreSine=add(mul(div(sqrt3,Q(2)),cos(eta)),div(sin(eta),Q(2)));
check(gt(Q(1),mul(Q(31,25),sq(coreSine))),'core log-sine curvature');
const smax=mul(Q(3),sq(eta));
check(gt(mul(mul(A,mu),sub(Q(1),div(mul(mu,smax),Q(2)))),kappa),'analytic core coefficient');
function factorial(n){let x=1n;for(let i=2;i<=n;i++)x*=BigInt(i);return x;}
const remainderCos=Q(5n**42n,factorial(42));
const remainderSin=Q(5n**43n,factorial(43));
const symmetricError=upper=>[-upper[1],upper[1]];
function tails(delta){
  const x=mul(Q(2),delta),x2=sq(x);
  check(x[0]>=-5n*S&&x[1]<=5n*S,'Taylor tail domain');
  // Ctail=1-cos(x)-x^2/2 and Stail=sin(x)-x.
  let ct=div(mul(x2,x2),Q(24)),cs=point(0n);
  let st=div(mul(x,x2),Q(6)),ss=point(0n);
  for(let j=1;j<=20;j++){
    if(j>=2){
      if(j>2)ct=div(mul(ct,x2),Q((2*j)*(2*j-1)));
      cs=(j%2===0)?sub(cs,ct):add(cs,ct);
    }
    if(j>1)st=div(mul(st,x2),Q((2*j)*(2*j+1)));
    ss=(j%2===1)?sub(ss,st):add(ss,st);
  }
  return {C:add(cs,symmetricError(remainderCos)),T:add(ss,symmetricError(remainderSin))};
}
function branch(delta,kind){
  const {C,T}=tails(delta);
  const quadratic=mul(div(sqrt3,Q(2)),sq(delta));
  const higher=add(mul(div(sqrt3,Q(4)),C),div(T,Q(4)));
  if(kind==='core')return add(mul(sub(div(sqrt3,Q(2)),kappa),sq(delta)),higher);
  const abs=kind==='positive'?delta:[-delta[1],-delta[0]];
  const penalty=mul(kappa,sub(mul(mul(Q(2),h),abs),sq(h)));
  return sub(add(quadratic,higher),penalty);
}
function term(delta){
  const pieces=[];
  if(delta[0]<-h[0])pieces.push(branch([delta[0],min([delta[1],-h[0]])],'negative'));
  if(delta[1]>=-h[1]&&delta[0]<=h[1])pieces.push(branch([max([delta[0],-h[1]]),min([delta[1],h[1]])],'core'));
  if(delta[1]>h[0])pieces.push(branch([max([delta[0],h[0]]),delta[1]],'positive'));
  check(pieces.length>0,'piecewise domain');
  return [min(pieces.map(x=>x[0])),max(pieces.map(x=>x[1]))];
}
const GRID=1048576;
const range=(a,b)=>[Q(a,GRID)[0],Q(b,GRID)[1]];
const stack=[[0,GRID,0,GRID]],leaves=[];
let boxes=0,analytic=0,minGap;
while(stack.length){
  const box=stack.pop(),[vl,vh,ul,uh]=box;boxes++;
  check(boxes<2000000,'subdivision limit');
  const w=mul(div(pi,Q(3)),range(vl,vh));
  if(gt(eta,mul(Q(2),w))){analytic++;leaves.push({box,kind:'analytic'});continue;}
  const u=range(ul,uh);
  const ds=[[-w[1],-w[0]],mul(w,sub(mul(Q(3,2),u),Q(1))),mul(w,sub(Q(2),mul(Q(3,2),u)))];
  const gap=ds.map(term).reduce(add,point(0n));
  if(gt(gap,Q(0))){
    minGap=minGap===undefined?gap[0]:min([minGap,gap[0]]);
    leaves.push({box,kind:'interval'});continue;
  }
  check(Math.max(vh-vl,uh-ul)>1,'unresolved box '+box);
  if(vh-vl>=uh-ul){const mid=Math.floor((vl+vh)/2);stack.push([vl,mid,ul,uh],[mid,vh,ul,uh]);}
  else{const mid=Math.floor((ul+uh)/2);stack.push([vl,vh,ul,mid],[vl,vh,mid,uh]);}
}
const result={passed:true,boxes,analyticLeaves:analytic,intervalLeaves:leaves.length-analytic,
  minimumIntervalMargin:String(minGap)+'/'+String(S),
  claim:'For every triangle of circumradius <= R, area <= R^2 [3sqrt(3)/4 -(4/5) sum H_(1/5)(angle-pi/3)].',
  scope:'Triangle lemma only. Boundary-angle coupling for arbitrary 26-disk covers is not proved here.'};
if(process.argv.includes('--write'))fs.writeFileSync(__dirname+'/ANGLE-CERTIFICATE.json',JSON.stringify({result,leaves}));
console.log(JSON.stringify(result,null,2));
