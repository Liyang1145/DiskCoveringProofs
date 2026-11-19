import json
from pathlib import Path
from verify_lower import M, check_pi_lo, radial_units_upper

SCALE=10**6


def maximum(circles,lo,hi,step,radius):
    value=-1
    for left in range(lo,hi,step):
        right=min(left+step,hi)
        value=max(value,sum(w*radial_units_upper(t,left,right,radius) for t,w in circles))
    return value


def check():
    check_pi_lo()
    data=json.loads(Path(__file__).with_name('class-cert.json').read_text(encoding='utf-8'))
    assert [(q['r'],q['k']) for q in data]==[(354500,9),(354500,10),(361103,11)]
    for record in data:
        r,k,step=record['r'],record['k'],record['step']
        circles=record['circles']
        assert step>0 and all(0<t<=SCALE and w>0 for t,w in circles)
        inner_end=3*r-SCALE if k==11 else SCALE-r
        inner=maximum(circles,0,inner_end,step,r)
        outer=maximum(circles,SCALE-r,SCALE,step,r)
        total=M*sum(w for t,w in circles)
        covered=(12-k)*inner+k*outer
        assert covered<total
        print(f'r={r}/{SCALE} and k={k}: inner max {inner}, outer max {outer}')
        print(f'  total mass numerator {total} > covered {covered}, gap {total-covered}')
    print('global lower bound > 0.3545; eleven exterior disks impossible at 0.361103')


if __name__=='__main__':
    check()
