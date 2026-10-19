import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P214
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(5/2 : Rat),(11/4 : Rat),(7/8 : Rat),(29/32 : Rat),(3/8 : Rat),(13/32 : Rat)⟩
def toks : List Tok := [.S 1 (57/64 : Rat),.S 2 (25/64 : Rat),.S 0 (21/8 : Rat),.L (306023/262144 : Rat) (1338215/1048576 : Rat) (234527/1048576 : Rat) (256821/1048576 : Rat),.L (310391/262144 : Rat) (1349967/1048576 : Rat) (237933/1048576 : Rat) (64781/262144 : Rat),.S 0 (21/8 : Rat),.L (1238431/1048576 : Rat) (1353999/1048576 : Rat) (118661/524288 : Rat) (129957/524288 : Rat),.L (628209/524288 : Rat) (341519/262144 : Rat) (240831/1048576 : Rat) (262281/1048576 : Rat),.S 2 (25/64 : Rat),.S 0 (21/8 : Rat),.L (1239945/1048576 : Rat) (1354657/1048576 : Rat) (118809/524288 : Rat) (260043/1048576 : Rat),.L (1257503/1048576 : Rat) (1366469/1048576 : Rat) (120521/524288 : Rat) (131179/524288 : Rat),.S 0 (21/8 : Rat),.L (1254257/1048576 : Rat) (685219/524288 : Rat) (240409/1048576 : Rat) (263137/1048576 : Rat),.S 0 (43/16 : Rat),.L (642973/524288 : Rat) (683291/524288 : Rat) (61649/262144 : Rat) (262381/1048576 : Rat),.L (161743/131072 : Rat) (1374807/1048576 : Rat) (248159/1048576 : Rat) (131997/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P214
