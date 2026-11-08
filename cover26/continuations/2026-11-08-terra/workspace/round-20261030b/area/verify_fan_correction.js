const S=10n**24n;
const floor=(a,b)=>a/b-((a%b<0n)?1n:0n);
const ceil=(a,b)=>-floor(-a,b);
const Q=(a,b=1)=>[floor(BigInt(a)*S,BigInt(b)),ceil(BigInt(a)*S,BigInt(b))];
const add=([a,b],[c,d])=>[a+c,b+d];
const neg=([a,b])=>[-b,-a];
const sub=(a,b)=>add(a,neg(b));
const min=a=>a.reduce((x,y)=>x<y?x:y);
const max=a=>a.reduce((x,y)=>x>y?x:y);
const mul=([a,b],[c,d])=>{let p=[a*c,a*d,b*c,b*d];return [floor(min(p),S),ceil(max(p),S)];};
const div=([a,b],[c,d])=>{if(c<=0n)throw Error("nonpositive divisor");return [min([floor(a*S,c),floor(a*S,d)]),max([ceil(b*S,c),ceil(b*S,d)])];};
function isqrt(n){if(n<0n)throw Error("negative radicand");if(n<2n)return n;let x=n,y=(x+1n)/2n;while(y<x){x=y;y=(x+n/x)/2n;}return x;}
const sqrt=([a,b])=>[isqrt(a*S),isqrt(b*S)+1n];
const sq=a=>mul(a,a);
const check=(p,m)=>{if(!p)throw Error(m);};
const gt=(a,b)=>a[0]>b[1];
function series(x,kind){
  check(x[0]>=0n && x[1]<=S,"Taylor domain");
  let term=kind==="cos"?Q(1):x, sum=term;
  for(let j=1;j<=12;j++){
    let k=kind==="cos"?2*j:2*j+1;
    term=kind==="atan"?div(mul(term,mul(sq(x),Q(k-2))),Q(k)):
         div(mul(term,sq(x)),Q(k*(k-1)));
    let prev=sum;
    sum=j%2?sub(sum,term):add(sum,term);
    if(j===12)return [prev[0],sum[1]];
  }
}
const sin=x=>series(x,"sin"),cos=x=>series(x,"cos");
const pi=sub(mul(Q(16),series(Q(1,5),"atan")),mul(Q(4),series(Q(1,239),"atan")));
const r=Q(228501,1000000),r2=sq(r);
const A=mul(Q(3,4),sqrt(Q(3)));
const base=Q(387,10000),enhanced=Q(81,2000);
const f=x=>add(div(x,Q(2)),mul(x,sqrt(sub(Q(1),div(sq(x),Q(4))))));
const Young=Q(147325,83694);
check(gt(sub(add(A,Q(1,2)),Young),base),"single-edge loss");
check(gt(Q(1101,500),sqrt(add(Q(9,4),mul(Q(3,2),sqrt(Q(3)))))),"ear upper");
check(gt(sub(add(A,Q(1)),Q(1101,500)),mul(Q(2),enhanced)),"ear loss");
check(gt(sin(div(pi,Q(13))),r)&&gt(Q(1),mul(Q(5),r2)),"geometric domain");
const G=d=>{let s=sin(d);return add(sub(d,mul(s,cos(d))),mul(s,sqrt(sub(r2,sq(s)))));};
const rows=[];
for(let b=14;b<=26;b++){
  const d=div(pi,Q(b));
  check(gt(r,sin(d)),"fan domain");
  const e=(b===16||b===17)?enhanced:base;
  if(b===16||b===17){
    const width=b===16?Q(8,1000):Q(9,1000);
    const lo=sub(d,width),hi=add(d,width),s=sin(d);
    const p=add(mul(Q(2),sq(s)),div(mul(cos(d),sub(r2,mul(Q(2),sq(s)))),sqrt(sub(r2,sq(s)))));
    const B=t=>sub(add(G(d),mul(p,sub(t,d))),G(t));
    const budget=mul(Q(2),mul(sub(e,base),r2));
    check(gt(B(lo),budget)&&gt(B(hi),budget),"Jensen window "+b);
    const a=t=>sub(cos(t),sqrt(sub(r2,sq(sin(t)))));
    check(gt(a(lo),Q(0))&&gt(Q(1),a(hi)),"ideal radii");
    const ideal=sqrt(add(sq(sub(a(hi),a(lo))),sq(mul(Q(2),mul(a(hi),sin(hi))))));
    const length=add(ideal,div(mul(r,budget),sq(sin(lo))));
    const x=Q(1563,1000);
    check(gt(x,div(length,r)),"short edge "+b);
    // f is concave on [0,2]. A positive derivative at x bounds f on [0,x].
    const z=sqrt(sub(Q(1),div(sq(x),Q(4))));
    check(gt(add(Q(1,2),div(sub(Q(1),div(sq(x),Q(2))),z)),Q(0)),"f monotonic");
    check(gt(sub(add(A,Q(1,2)),f(x)),e),"short edge loss "+b);
  }
  const upper=add(mul(r2,add(mul(Q(50-b),A),mul(Q(b),sub(Q(1,2),e)))),mul(Q(b),G(d)));
  check(gt(pi,upper),"area contradiction "+b);
  rows.push([b,Number(pi[0]-upper[1])/Number(S)]);
}
console.log(rows);
