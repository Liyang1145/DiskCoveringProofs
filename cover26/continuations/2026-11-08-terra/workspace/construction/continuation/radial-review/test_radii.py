import subprocess,sys
from pathlib import Path
p=Path(__file__).resolve().parent; source=(p/'independent_atan.py').read_text(encoding='utf8')
for k in (442,444,446,448,450,452,454,456,458):
 code=source.replace('r=F(11,50)',f'r=F({k},2000)').replace('count=2440',f'count={2000+k}')
 result=subprocess.run([sys.executable,'-c',code],capture_output=True,text=True)
 print(k,'PASS' if not result.returncode else 'FAIL',result.stdout.strip().splitlines()[-2:] if result.stdout else '')
