// Voronoi-cell area support functions using both boundary and inner degrees.
"use strict";
const {S,Q,add,sub,mul,div,sq,check,gt,sin,pi}=require("../exact-interval.js");
const fs=require("node:fs");

const U=Q(230796,1000000);
const half=div(sq(U),Q(2)),tau=mul(Q(2),pi);
const step=250,scale=10000000,first=1490000,last=2328957;
const angle=x=>Q(x,scale);
const point=x=>[x,x];
const lambda=Array.from({length:85},(_,i)=>Q(-5000+50*i,1000));
const penalty=lambda.map(v=>mul(v,pi)[1]);
const poly=Array.from({length:27},(_,k)=>k<3?null:mul(half,mul(Q(k),sin(div(tau,Q(k))))));
const maxima=lambda.map(()=>Array(8).fill(null));

check(gt(sin(angle(last)),U)&&gt(sin(angle(first)),div(U,Q(2))),"owner angle range");
for(let l=first;l<last;l+=step) {
  const h=Math.min(last,l+step);
  const s=sin(angle(l));
  if(gt(s,U))continue;
  const z=div(s,U);
  const guess=Math.floor(scale*Math.asin(Math.min(1,Number(z[0])/Number(S))))-2;
  let chord=Q(0);
  if(guess>0&&guess<=15707963&&gt(z,sin(angle(guess))))chord=angle(2*guess);
  const segment=div(sin(angle(2*l)),Q(2));
  for(let d=3;d<=7;d++) {
    const a=gt(chord,div(tau,Q(d+1)))?
      mul(half,add(sin(chord),mul(Q(d),sin(div(sub(tau,chord),Q(d)))))):poly[d+1];
    const fixed=sub(a,segment)[1];
    for(let i=0;i<lambda.length;i++) {
      const v=fixed-mul(lambda[i],angle(h))[0];
      const previous=maxima[i][d];
      if(previous===null||v>previous)maxima[i][d]=v;
    }
  }
}

const source=JSON.parse(fs.readFileSync(process.argv[2],"utf8"));
check(source.degree_sum===52&&source.degree_profiles.length===7,"degree profiles for core annuli");
const supports=source.degree_profiles.map(ds=> {
  check(ds.length===14&&ds.every(d=>d>=3&&d<=7)&&ds.reduce((a,b)=>a+b,0)===52,
        "invalid outer degree multiset");
  const v=maxima.map((f,i)=>penalty[i]+ds.reduce((a,b)=>a+f[b],0n));
  return [ds.join(","),v.reduce((a,b)=>a<b?a:b).toString()];
});
const enclosed=poly.map(x=>x===null?null:x[1].toString());
fs.writeFileSync(process.argv[3],JSON.stringify({supports,enclosed})+"\n");
console.log("PASS B=14: outward-rounded area supports for seven outer profiles and internal cell areas.");
