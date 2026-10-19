import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P187
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(29/32 : Rat),(15/16 : Rat),(1/4 : Rat),(5/16 : Rat)⟩
def toks : List Tok := [.S 0 (9/4 : Rat),.S 2 (9/32 : Rat),.L (1041629/1048576 : Rat) (1239279/1048576 : Rat) (199103/1048576 : Rat) (237489/1048576 : Rat),.L (1060685/1048576 : Rat) (316479/262144 : Rat) (202791/1048576 : Rat) (242685/1048576 : Rat),.S 2 (9/32 : Rat),.S 0 (19/8 : Rat),.L (274801/262144 : Rat) (1248471/1048576 : Rat) (105127/524288 : Rat) (239281/1048576 : Rat),.L (1118019/1048576 : Rat) (1269101/1048576 : Rat) (13369/65536 : Rat) (243307/1048576 : Rat),.S 0 (19/8 : Rat),.L (140519/131072 : Rat) (159489/131072 : Rat) (107547/524288 : Rat) (244637/1048576 : Rat),.S 1 (59/64 : Rat),.L (286209/262144 : Rat) (1281865/1048576 : Rat) (219109/1048576 : Rat) (30725/131072 : Rat),.L (2267/2048 : Rat) (649165/524288 : Rat) (13887/65536 : Rat) (249017/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P187
