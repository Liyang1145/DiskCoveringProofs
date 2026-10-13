import subprocess
for st in [0,2]:
 for b in range(9,15):
  subprocess.run(['py','-3','-B','research-2026/team-current/lead/shared_ear_angle.py',str(st),'4','24',str(b)],check=True)
