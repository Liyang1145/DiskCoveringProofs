from pathlib import Path
p=Path(__file__).resolve().parent
s=(p/'independent_atan.py').read_text(encoding='utf8')
s=s.replace('r=F(11,50)','r=F(2,9)')
a=s.index('data=['); b=s.index('\nassert all',a)
s=s[:a]+"data=[(F(t),w) for t,w in [('23/100',23488),('19/75',19949),('83/300',25455),('3/10',18639),('97/300',11565),('26/75',9087),('37/100',440),('59/100',104502),('37/60',59049),('193/300',43611),('67/100',33041),('209/300',22845),('217/300',19185),('3/4',640),('1',446238)]]"+s[b:]
s=s.replace('step=F(1,2000); count=2440','step=F(1,3600); count=4400').replace('all 2440 closed distance intervals','all 4400 closed distance intervals')
(p/'independent_atan_2_9.py').write_text(s,encoding='utf8')
