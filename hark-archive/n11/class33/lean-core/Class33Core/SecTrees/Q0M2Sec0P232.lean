import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P232
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(5/2 : Rat),(11/4 : Rat),(15/16 : Rat),(31/32 : Rat),(3/8 : Rat),(13/32 : Rat)⟩
def toks : List Tok := [.S 1 (61/64 : Rat),.S 2 (25/64 : Rat),.S 0 (21/8 : Rat),.L (1287583/1048576 : Rat) (1403973/1048576 : Rat) (61729/262144 : Rat) (33715/131072 : Rat),.L (163173/131072 : Rat) (1415961/1048576 : Rat) (250395/1048576 : Rat) (68019/262144 : Rat),.S 0 (21/8 : Rat),.L (162727/131072 : Rat) (709875/524288 : Rat) (124849/524288 : Rat) (272821/1048576 : Rat),.L (660077/524288 : Rat) (716039/524288 : Rat) (253285/1048576 : Rat) (275245/1048576 : Rat),.S 2 (25/64 : Rat),.S 0 (21/8 : Rat),.L (20367/16384 : Rat) (1420409/1048576 : Rat) (250025/1048576 : Rat) (136475/524288 : Rat),.L (1321365/1048576 : Rat) (1432453/1048576 : Rat) (126761/524288 : Rat) (275319/1048576 : Rat),.S 0 (21/8 : Rat),.L (1317695/1048576 : Rat) (1436185/1048576 : Rat) (63201/262144 : Rat) (276053/1048576 : Rat),.L (1336115/1048576 : Rat) (362143/262144 : Rat) (256409/1048576 : Rat) (69623/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P232
