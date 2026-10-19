import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P838
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(11/4 : Rat),(314159265358979323847/100000000000000000000 : Rat),(15/16 : Rat),(31/32 : Rat),(7/8 : Rat),(15/16 : Rat)⟩
def toks : List Tok := [.S 0 (3 : Rat),.S 2 (29/32 : Rat),.L (1764155/1048576 : Rat) (1967445/1048576 : Rat) (341177/1048576 : Rat) (382223/1048576 : Rat),.L (1753/1024 : Rat) (999827/524288 : Rat) (347383/1048576 : Rat) (388781/1048576 : Rat),.L (457747/262144 : Rat) (500249/262144 : Rat) (22163/65536 : Rat) (389055/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P838
