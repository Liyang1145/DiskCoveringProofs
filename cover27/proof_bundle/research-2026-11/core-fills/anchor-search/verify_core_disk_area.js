// Necessary Voronoi areas on the disc bounded by the ten-owner core circle.
"use strict";
const {S,Q,add,sub,mul,div,sq,check,gt,sin,cos,pi}=require("../exact-interval.js");
const fs=require("node:fs");

const U=Q(230796,1000000);
const half=div(sq(U),Q(2)),tau=mul(Q(2),pi);
const scale=10000000;
const angle=x=>Q(x,scale);
const polygon=Array.from({length:13},(_,k)=>k<3?null:mul(half,mul(Q(k),sin(div(tau,Q(k))))));
const slopes=Array.from({length:171},(_,i)=>Q(-1600+10*i,1000));
const intercepts=slopes.map(x=>mul(x,pi)[1]);
const bands=[
  [901500,3512920,2656950],
  [905600,3490660,2566120],
  [908500,3475090,2499400],
  [911500,3459130,2428030],
];

function makeSupport(floor,right,shortEnd) {
  const s=Q(floor-230797,1000000),s2=sq(s);
  const d=Q(498,1000);
  const c=div(sub(add(s2,sq(d)),sq(U)),mul(Q(2),mul(s,d)));
  check(gt(mul(s,sin(angle(right))),U)&&gt(div(pi,Q(4)),angle(right)),"core half-angle cap");
  check(gt(sub(s2,sq(U)),sq(d))&&gt(c,cos(angle(shortEnd))),"a short core owner");
  const general=slopes.map(()=>Array(13).fill(null));
  const small=slopes.map(()=>Array(13).fill(null));
  const step=800;
  for(let lo=0;lo<right;lo+=step) {
    const hi=Math.min(right,lo+step);
    const chord=mul(s,sin(angle(lo)));
    if(gt(chord,U))continue;
    let a=Q(0);
    if(gt(chord,div(U,Q(2)))) {
      const z=div(chord,U);
      const k=Math.floor(scale*Math.asin(Math.min(1,Number(z[0])/Number(S))))-2;
      if(k>0&&k<=15707963&&gt(z,sin(angle(k))))a=angle(2*k);
    }
    const segment=div(mul(s2,sin(angle(2*lo))),Q(2));
    const overrides=slopes.map(x=>mul(x,angle(x[0]<0n?hi:lo))[0]);
    for(let k=2;k<=11;k++) {
      const bound=gt(a,div(tau,Q(k+1)))?
        mul(half,add(sin(a),mul(Q(k),sin(div(sub(tau,a),Q(k)))))):polygon[k+1];
      const fixed=sub(bound,segment)[1];
      for(let i=0;i<slopes.length;i++) {
        const f=fixed-overrides[i];
        if(general[i][k]===null||f>general[i][k])general[i][k]=f;
        if(lo<=shortEnd&&(small[i][k]===null||f>small[i][k]))small[i][k]=f;
      }
    }
  }
  return {floor,general,small};
}

function allowed(profile,support) {
  const [edges,inner]=profile;
  const interior=inner.reduce((v,d)=>v+polygon[d][1],0n);
  return !intercepts.some((c,i)=>{
    const g=support.general[i],s=support.small[i];
    let extra=s[edges[0]]-g[edges[0]];
    const total=edges.reduce((x,d)=>{
      const y=s[d]-g[d];
      if(y>extra)extra=y;
      return x+g[d];
    },interior+c);
    return total+extra<0n;
  });
}

const groups=JSON.parse(fs.readFileSync(process.argv[2],"utf8"));
const output=[];
for(const band of bands) {
  const support=makeSupport(...band);
  const excluding=groups.map(record=>!allowed(record.slice(0,2),support));
  const count=excluding.reduce((n,result,i)=>n+(result?groups[i][2]:0),0);
  output.push({owner_norm_floor:support.floor,excluded_core_fills:count,group_excluded:excluding});
  console.log("PASS B=14: at D1 >= "+support.floor+"/1e6, "+count+" core fills contradict the core-disk area.");
}
fs.writeFileSync(process.argv[3],JSON.stringify(output)+"\n");
