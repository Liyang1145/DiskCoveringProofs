import subprocess
for s in [0,1,2,3]:
 subprocess.run(['py','-3','-B','research-2026/team-current/lead/certify_shared_factors.py',str(s),'3'],check=True)

