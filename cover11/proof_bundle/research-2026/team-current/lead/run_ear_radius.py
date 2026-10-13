import subprocess
for st in [0,2]:
 for b in range(8):
  subprocess.run(['py','-3','-B','research-2026/team-current/lead/shared_ear_radius.py',str(st),'4','8',str(b)],check=True)
