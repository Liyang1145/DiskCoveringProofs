import subprocess
for b in range(8):
 subprocess.run(['py','-3','-B','research-2026/team-current/lead/q0_hubangle_dual.py','0','3','8',str(b)],check=True)
