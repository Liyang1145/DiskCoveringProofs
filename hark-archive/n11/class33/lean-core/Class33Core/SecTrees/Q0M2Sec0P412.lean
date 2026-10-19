import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P412
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(31/32 : Rat),(1 : Rat),(19/32 : Rat),(5/8 : Rat)⟩
def toks : List Tok := [.S 1 (63/64 : Rat),.S 2 (39/64 : Rat),.S 1 (125/128 : Rat),.L (789423/524288 : Rat) (833423/524288 : Rat) (304231/1048576 : Rat) (321725/1048576 : Rat),.L (793403/524288 : Rat) (1675099/1048576 : Rat) (305809/1048576 : Rat) (323371/1048576 : Rat),.S 1 (125/128 : Rat),.L (1594533/1048576 : Rat) (1683033/1048576 : Rat) (307343/1048576 : Rat) (324953/1048576 : Rat),.L (1602487/1048576 : Rat) (845643/524288 : Rat) (154461/524288 : Rat) (40825/131072 : Rat),.S 2 (39/64 : Rat),.S 1 (127/128 : Rat),.L (99673/65536 : Rat) (210419/131072 : Rat) (307389/1048576 : Rat) (325017/1048576 : Rat),.L (1602733/1048576 : Rat) (422901/262144 : Rat) (154485/524288 : Rat) (40833/131072 : Rat),.S 1 (127/128 : Rat),.L (402611/262144 : Rat) (1699539/1048576 : Rat) (155251/524288 : Rat) (41031/131072 : Rat),.L (1618403/1048576 : Rat) (106737/65536 : Rat) (312083/1048576 : Rat) (41237/131072 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P412
