from pathlib import Path
p=Path(__file__).parent/'verify_triangles.py';s=p.read_text(encoding='utf8');s=s.replace('if (a,b) not in boundary:assert directions[a,b]==directions[b,a]==1',"if (a,b) not in boundary and not directions[a,b]==directions[b,a]==1: print('BAD',a,b,directions[a,b],directions[b,a])")
exec(compile(s,str(p),'exec'))
