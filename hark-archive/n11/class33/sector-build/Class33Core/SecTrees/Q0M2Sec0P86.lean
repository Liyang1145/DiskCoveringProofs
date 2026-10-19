import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P86
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(13/16 : Rat),(27/32 : Rat),(3/16 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 0 (9/4 : Rat),.L (888063/1048576 : Rat) (1134203/1048576 : Rat) (42367/262144 : Rat) (108523/524288 : Rat),.S 2 (7/32 : Rat),.S 0 (19/8 : Rat),.L (477301/524288 : Rat) (136977/131072 : Rat) (182291/1048576 : Rat) (209599/1048576 : Rat),.L (969183/1048576 : Rat) (1112281/1048576 : Rat) (11569/65536 : Rat) (212791/1048576 : Rat),.S 0 (19/8 : Rat),.L (979189/1048576 : Rat) (1122803/1048576 : Rat) (46759/262144 : Rat) (214833/1048576 : Rat),.L (62235/65536 : Rat) (285289/262144 : Rat) (47559/262144 : Rat) (54599/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P86
