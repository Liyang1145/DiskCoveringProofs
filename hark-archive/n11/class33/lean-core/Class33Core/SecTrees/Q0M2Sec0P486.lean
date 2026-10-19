import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P486
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(3/4 : Rat),(13/16 : Rat),(3/4 : Rat),(7/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (0 : Rat) (222313/262144 : Rat) (0 : Rat) (84849/524288 : Rat),.S 0 (3/2 : Rat),.L (361835/524288 : Rat) (631229/524288 : Rat) (68947/524288 : Rat) (121005/524288 : Rat),.S 0 (7/4 : Rat),.L (130451/131072 : Rat) (700217/524288 : Rat) (99743/524288 : Rat) (269025/1048576 : Rat),.S 2 (13/16 : Rat),.L (1169551/1048576 : Rat) (1481457/1048576 : Rat) (27989/131072 : Rat) (71243/262144 : Rat),.L (304327/262144 : Rat) (1541459/1048576 : Rat) (116603/524288 : Rat) (148413/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P486
