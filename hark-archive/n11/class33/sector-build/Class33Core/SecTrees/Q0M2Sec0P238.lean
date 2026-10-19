import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P238
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(15/16 : Rat),(1 : Rat),(7/16 : Rat),(1/2 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (7/16 : Rat) (472217/524288 : Rat) (87263/1048576 : Rat) (180331/1048576 : Rat),.S 0 (3/2 : Rat),.L (769621/1048576 : Rat) (1206949/1048576 : Rat) (73353/524288 : Rat) (231189/1048576 : Rat),.S 0 (7/4 : Rat),.L (501149/524288 : Rat) (1309629/1048576 : Rat) (191499/1048576 : Rat) (251227/1048576 : Rat),.L (274755/262144 : Rat) (708327/524288 : Rat) (210219/1048576 : Rat) (68053/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P238
