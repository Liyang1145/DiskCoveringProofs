import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P197
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(5/2 : Rat),(11/4 : Rat),(29/32 : Rat),(15/16 : Rat),(11/32 : Rat),(3/8 : Rat)⟩
def toks : List Tok := [.S 1 (59/64 : Rat),.S 2 (23/64 : Rat),.S 0 (21/8 : Rat),.L (1227399/1048576 : Rat) (334895/262144 : Rat) (58793/262144 : Rat) (257089/1048576 : Rat),.L (1243949/1048576 : Rat) (675381/524288 : Rat) (119199/524288 : Rat) (259279/1048576 : Rat),.S 0 (21/8 : Rat),.L (620789/524288 : Rat) (1355331/1048576 : Rat) (14871/65536 : Rat) (260175/1048576 : Rat),.L (157335/131072 : Rat) (683431/524288 : Rat) (30159/131072 : Rat) (262435/1048576 : Rat),.S 2 (23/64 : Rat),.S 0 (21/8 : Rat),.L (1243331/1048576 : Rat) (678011/524288 : Rat) (119139/524288 : Rat) (130155/524288 : Rat),.L (1259951/1048576 : Rat) (1367255/1048576 : Rat) (15095/65536 : Rat) (262513/1048576 : Rat),.S 0 (21/8 : Rat),.L (314371/262144 : Rat) (1371771/1048576 : Rat) (241039/1048576 : Rat) (131699/524288 : Rat),.L (637331/524288 : Rat) (1383357/1048576 : Rat) (30549/131072 : Rat) (33209/131072 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P197
