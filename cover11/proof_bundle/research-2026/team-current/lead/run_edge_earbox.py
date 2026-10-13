import subprocess
for b1 in range(8):
 for b0 in range(8-b1):
  subprocess.run(['py','-3','-B','research-2026/team-current/lead/edge_earbox_dual.py','0','8',str(b1),str(b0)],check=True)
