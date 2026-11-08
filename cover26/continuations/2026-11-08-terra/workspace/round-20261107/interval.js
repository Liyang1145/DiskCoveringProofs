'use strict';
// Closed, outward-rounded intervals with an integer denominator 10^24.
const S=10n**24n;
const floor=(a,b)=>a/b-((a%b<0n)?1n:0n);
const ceil=(a,b)=>-floor(-a,b);
const min=a=>a.reduce((x,y)=>x<y?x:y);
const max=a=>a.reduce((x,y)=>x>y?x:y);
const Q=(a,b=1)=>[floor(BigInt(a)*S,BigInt(b)),ceil(BigInt(a)*S,BigInt(b))];
const point=x=>[x,x];
const add=([a,b],[c,d])=>[a+c,b+d];
const neg=([a,b])=>[-b,-a];
const sub=(a,b)=>add(a,neg(b));
const mul=([a,b],[c,d])=>{const p=[a*c,a*d,b*c,b*d];return [floor(min(p),S),ceil(max(p),S)];};
const div=([a,b],[c,d])=>{if(c<=0n)throw Error('nonpositive divisor');return [min([floor(a*S,c),floor(a*S,d)]),max([ceil(b*S,c),ceil(b*S,d)])];};
function isqrt(n){
  if(n<0n)throw Error('negative radicand');
  if(n<2n)return n;
  let x=1n<<BigInt(Math.ceil(n.toString(2).length/2));
  while(true){const y=(x+n/x)/2n;if(y>=x)return x;x=y;}
}
const sqrt=([a,b])=>[isqrt(a*S),isqrt(b*S)+1n];
const sq=a=>mul(a,a);
const check=(p,m)=>{if(!p)throw Error(m);};
const gt=(a,b)=>a[0]>b[1];
function series(x,kind){
  check(x[0]>=0n&&x[1]<=S,'Taylor domain');
  let term=kind==='cos'?Q(1):x,sum=term;
  for(let j=1;j<=14;j++){
    const k=kind==='cos'?2*j:2*j+1;
    term=kind==='atan'?div(mul(term,mul(sq(x),Q(k-2))),Q(k)):
      div(mul(term,sq(x)),Q(k*(k-1)));
    const prev=sum;sum=j%2?sub(sum,term):add(sum,term);
    if(j===14)return [prev[0],sum[1]];
  }
}
const sin=x=>series(x,'sin'),cos=x=>series(x,'cos');
const pi=sub(mul(Q(16),series(Q(1,5),'atan')),mul(Q(4),series(Q(1,239),'atan')));
module.exports={S,floor,ceil,min,max,Q,point,add,sub,mul,div,sqrt,sq,check,gt,sin,cos,pi};
