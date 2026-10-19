import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P203
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(31/32 : Rat),(1 : Rat),(1/4 : Rat),(5/16 : Rat)⟩
def toks : List Tok := [.S 0 (9/4 : Rat),.S 2 (9/32 : Rat),.L (552357/524288 : Rat) (1304737/1048576 : Rat) (211323/1048576 : Rat) (125135/524288 : Rat),.L (1123303/1048576 : Rat) (665639/524288 : Rat) (214929/1048576 : Rat) (255463/1048576 : Rat),.S 2 (9/32 : Rat),.S 0 (19/8 : Rat),.L (1162821/1048576 : Rat) (1314051/1048576 : Rat) (55651/262144 : Rat) (63023/262144 : Rat),.L (73865/65536 : Rat) (333741/262144 : Rat) (113151/524288 : Rat) (256185/1048576 : Rat),.S 0 (19/8 : Rat),.L (593725/524288 : Rat) (670709/524288 : Rat) (227393/1048576 : Rat) (257449/1048576 : Rat),.L (604195/524288 : Rat) (1364169/1048576 : Rat) (231469/1048576 : Rat) (261907/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P203
