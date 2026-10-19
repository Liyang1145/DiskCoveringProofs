import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P170
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(5/2 : Rat),(11/4 : Rat),(13/16 : Rat),(27/32 : Rat),(13/32 : Rat),(7/16 : Rat)⟩
def toks : List Tok := [.S 1 (53/64 : Rat),.S 0 (21/8 : Rat),.S 0 (41/16 : Rat),.L (1196809/1048576 : Rat) (1301215/1048576 : Rat) (114607/524288 : Rat) (249581/1048576 : Rat),.L (1206967/1048576 : Rat) (327953/262144 : Rat) (28899/131072 : Rat) (125827/524288 : Rat),.S 2 (27/64 : Rat),.L (301965/262144 : Rat) (1316137/1048576 : Rat) (115683/524288 : Rat) (63125/262144 : Rat),.L (1222879/1048576 : Rat) (333063/262144 : Rat) (234291/1048576 : Rat) (127827/524288 : Rat),.S 0 (21/8 : Rat),.S 0 (41/16 : Rat),.L (1212467/1048576 : Rat) (1317641/1048576 : Rat) (232263/1048576 : Rat) (126397/524288 : Rat),.L (1222687/1048576 : Rat) (83019/65536 : Rat) (117127/524288 : Rat) (254881/1048576 : Rat),.S 2 (27/64 : Rat),.L (611851/524288 : Rat) (1332655/1048576 : Rat) (234451/1048576 : Rat) (255733/1048576 : Rat),.L (619349/524288 : Rat) (1348773/1048576 : Rat) (118687/524288 : Rat) (129445/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P170
