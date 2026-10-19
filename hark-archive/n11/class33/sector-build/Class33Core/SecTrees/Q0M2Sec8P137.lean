import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P137
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(5/2 : Rat),(314159265358979323847/100000000000000000000 : Rat),(5/8 : Rat),(11/16 : Rat),(7/8 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 2 (15/16 : Rat),.S 0 (11/4 : Rat),.S 1 (21/32 : Rat),.L (1421121/1048576 : Rat) (1677261/1048576 : Rat) (273089/1048576 : Rat) (161901/524288 : Rat),.S 2 (29/32 : Rat),.L (1450509/1048576 : Rat) (418995/262144 : Rat) (34859/131072 : Rat) (161773/524288 : Rat),.L (740219/524288 : Rat) (427321/262144 : Rat) (142385/524288 : Rat) (165097/524288 : Rat),.L (1405431/1048576 : Rat) (857621/524288 : Rat) (270005/1048576 : Rat) (331385/1048576 : Rat),.S 0 (11/4 : Rat),.S 1 (21/32 : Rat),.S 2 (31/32 : Rat),.L (1481365/1048576 : Rat) (427635/262144 : Rat) (284953/1048576 : Rat) (330445/1048576 : Rat),.L (377913/262144 : Rat) (217975/131072 : Rat) (72733/262144 : Rat) (337099/1048576 : Rat),.S 2 (31/32 : Rat),.L (377621/262144 : Rat) (217821/131072 : Rat) (290701/1048576 : Rat) (84213/262144 : Rat),.L (770321/524288 : Rat) (1775833/1048576 : Rat) (296663/1048576 : Rat) (343521/1048576 : Rat),.L (732057/524288 : Rat) (445693/262144 : Rat) (17597/65536 : Rat) (344913/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P137
