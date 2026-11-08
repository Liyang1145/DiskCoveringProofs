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
const r=Q(228701,1000000),r2=sq(r);
const A=mul(Q(3,4),sqrt(Q(3)));
const base=Q(387,10000),enhanced=Q(19,400);
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

    const width=23000,s=sin(d);
    const p=add(mul(Q(2),sq(s)),div(mul(cos(d),sub(r2,mul(Q(2),sq(s)))),sqrt(sub(r2,sq(s)))));
    const budget=mul(Q(2),mul(sub(e,base),r2));
    const cache=new Map();
    const at=i=>{
      if(!cache.has(i)){
        const offset=Q(i,1000000),t=add(d,offset),s=sin(t),c=cos(t);
        const h=sqrt(sub(r2,sq(s)));
        const J=sub(add(G(d),mul(p,offset)),add(sub(t,mul(s,c)),mul(s,h)));
        cache.set(i,{s,a:sub(c,h),J});
      }
      return cache.get(i);
    };
    check(gt(at(-width).J,budget)&&gt(at(width).J,budget),"Jensen window "+b);
    const tangents=[];
    for(let i=1250;i<=1610;i+=10){
      const t=Q(i,1000),z=sqrt(sub(Q(1),div(sq(t),Q(4))));
      const D=add(Q(1,2),div(sub(Q(1),div(sq(t),Q(2))),z));
      if(gt(D,Q(0)))tangents.push({t,D,F:f(t)});
    }
    const inv=div(Q(1),mul(Q(2),r2));
    const stack=[[-width,width,-width,width]];
    let boxes=0;
    const point=x=>[x,x];
    const lowJ=(l,h)=>l>0?at(l).J[0]:h<0?at(h).J[0]:0n;
    while(stack.length){
      const [l,h,m,n]=stack.pop(); boxes++;
      const J=point(max([0n,lowJ(l,h)+lowJ(m,n)]));
      if(gt(J,budget))continue;
      const al=at(l).a,ah=at(h).a,am=at(m).a,an=at(n).a;
      const diff=point(max([0n,ah[1]-am[0],an[1]-al[0]]));
      const mid=sin(add(d,Q(h+n,2000000)));
      const ideal=div(sqrt(add(sq(diff),mul(Q(4),mul(mul(ah,an),sq(mid))))),r);
      const smin=point(min([at(l).s[0],at(m).s[0]]));
      const rem=point(max([0n,budget[1]-J[0]]));
      const fixed=add(add(A,Q(1,2)),mul(J,inv));
      let passed=false;
      for(const {t,D,F} of tangents){
        const coeff=sub(inv,div(D,sq(smin)));
        const loss=add(sub(fixed,add(F,mul(D,sub(ideal,t)))),mul(point(min([0n,coeff[0]])),rem));
        if(gt(loss,e)){passed=true;break;}
      }
      if(passed)continue;
      check(Math.max(h-l,n-m)>1,"unresolved angular box "+[b,l,h,m,n]);
      if(h-l>=n-m){const k=Math.floor((l+h)/2);stack.push([l,k,m,n],[k,h,m,n]);}
      else {const k=Math.floor((m+n)/2);stack.push([l,h,m,k],[l,h,k,n]);}
    }
    console.log({b,boxes});

  }
  const upper=add(mul(r2,add(mul(Q(50-b),A),mul(Q(b),sub(Q(1,2),e)))),mul(Q(b),G(d)));
  check(gt(pi,upper),"area contradiction "+b);
  rows.push([b,Number(pi[0]-upper[1])/Number(S)]);
}
console.log(rows);
