import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P89
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(27/32 : Rat),(7/8 : Rat),(3/16 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 0 (9/4 : Rat),.S 2 (7/32 : Rat),.L (29435/32768 : Rat) (1121303/1048576 : Rat) (179845/1048576 : Rat) (107271/524288 : Rat),.L (240003/262144 : Rat) (1147399/1048576 : Rat) (91667/524288 : Rat) (27451/131072 : Rat),.S 2 (7/32 : Rat),.S 0 (19/8 : Rat),.L (493275/524288 : Rat) (141085/131072 : Rat) (188457/1048576 : Rat) (215973/1048576 : Rat),.L (1001205/1048576 : Rat) (1145261/1048576 : Rat) (23911/131072 : Rat) (219193/1048576 : Rat),.S 0 (19/8 : Rat),.L (505479/524288 : Rat) (288909/262144 : Rat) (48293/262144 : Rat) (27651/131072 : Rat),.L (1027629/1048576 : Rat) (1174131/1048576 : Rat) (196395/1048576 : Rat) (56201/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P89
