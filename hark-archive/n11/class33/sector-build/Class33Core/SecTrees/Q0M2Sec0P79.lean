import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P79
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(13/16 : Rat),(27/32 : Rat),(1/8 : Rat),(3/16 : Rat)⟩
def toks : List Tok := [.S 2 (5/32 : Rat),.S 0 (9/4 : Rat),.L (109499/131072 : Rat) (518669/524288 : Rat) (167145/1048576 : Rat) (99137/524288 : Rat),.L (898713/1048576 : Rat) (66621/65536 : Rat) (171519/1048576 : Rat) (203809/1048576 : Rat),.S 0 (9/4 : Rat),.L (223159/262144 : Rat) (1062715/1048576 : Rat) (170349/1048576 : Rat) (203185/1048576 : Rat),.S 1 (53/64 : Rat),.L (230109/262144 : Rat) (269903/262144 : Rat) (175703/1048576 : Rat) (103229/524288 : Rat),.L (117059/131072 : Rat) (548075/524288 : Rat) (89397/524288 : Rat) (209663/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P79
