import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P44
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(11/16 : Rat),(3/4 : Rat),(3/8 : Rat),(1/2 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (3/16 : Rat) (750111/1048576 : Rat) (37363/1048576 : Rat) (35741/262144 : Rat),.S 0 (3/2 : Rat),.L (16497/32768 : Rat) (496549/524288 : Rat) (100455/1048576 : Rat) (189723/1048576 : Rat),.S 0 (7/4 : Rat),.L (733371/1048576 : Rat) (1086299/1048576 : Rat) (139753/1048576 : Rat) (103877/524288 : Rat),.S 2 (7/16 : Rat),.L (834057/1048576 : Rat) (69691/65536 : Rat) (19885/131072 : Rat) (106665/524288 : Rat),.L (877539/1048576 : Rat) (1162599/1048576 : Rat) (167443/1048576 : Rat) (111281/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P44
