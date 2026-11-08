from pathlib import Path
p=Path('research-2026/n26-terra/round-20261030b');s=(p/'area/verify_area.py').read_text(encoding='utf8');s=s.replace('R = F(2271, 10000)','R = F(22781, 100000)').replace('TARGET = F(227, 1000)','TARGET = F(1139, 5000)');s=s.replace('SQRT3_HI = root_bounds(F(3))[1]',"# Young bound on x/2 + x sqrt(1-x^2/4).\nw = F(37,100); a = 1/(4*w)-w; C = 1/(2*w)+1/(8*a)\nassert a>0 and C == F(147325,83694)\nassert F(3,4)*F(433,250)+F(1,2)-C > F(19,500)\nassert F(433,250)**2 < 3\nSQRT3_HI = root_bounds(F(3))[1]")
s=s.replace('+ owners*R*R/2 + owners*curved_fan_hi)', '+ owners*R*R/2 + owners*curved_fan_hi - F(19,1000)*owners*R*R)')
s=s.replace('F(313721, 100000)','F(31415, 10000)').replace('"313721/100000"','"31415/10000"')
(p/'coupling/next/verify_joint_area.py').write_text(s,encoding='utf8')
