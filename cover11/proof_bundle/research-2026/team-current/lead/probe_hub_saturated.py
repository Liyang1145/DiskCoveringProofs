"""Threefixedouter boundarymax enclosure calibration; nobroadcertificate."""
from pathlib import Path
import json,time
import interval_hub_saturated as f
from interval_joint_patch import I
P=Path(__file__).parent;start=time.time();rows=[]
for literals in [['.38','1.107','1.0695'],['.38','1','1'],['.375','1.18','1.18']]:
 out=f.bound([I(x)for x in literals],maxeval=257);rows.append({'outer':literals,'bound':out})
obj={'scope':'fixedouteranalyticboundaryenclosure, calibrationnotglobal','rows':rows,'seconds':time.time()-start};(P/'hub_saturated_probe.json').write_text(json.dumps(obj,indent=2));print(json.dumps(obj,indent=2))
