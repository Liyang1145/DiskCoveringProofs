import subprocess
for st in [0,2]:
 subprocess.run(['py','-3','-B','research-2026/team-current/lead/certify_shared_moments_dense.py',str(st),'4'],check=True)
