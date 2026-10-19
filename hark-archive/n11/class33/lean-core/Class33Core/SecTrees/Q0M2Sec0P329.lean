import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P329
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(27/32 : Rat),(7/8 : Rat),(19/32 : Rat),(5/8 : Rat)⟩
def toks : List Tok := [.S 1 (55/64 : Rat),.S 2 (39/64 : Rat),.S 1 (109/128 : Rat),.L (362959/262144 : Rat) (767353/524288 : Rat) (279133/1048576 : Rat) (147745/524288 : Rat),.L (1459753/1048576 : Rat) (771485/524288 : Rat) (280693/1048576 : Rat) (297125/1048576 : Rat),.S 1 (109/128 : Rat),.L (1467625/1048576 : Rat) (1550887/1048576 : Rat) (70561/262144 : Rat) (74673/262144 : Rat),.L (1475535/1048576 : Rat) (1559151/1048576 : Rat) (283803/1048576 : Rat) (300329/1048576 : Rat),.S 2 (39/64 : Rat),.S 1 (111/128 : Rat),.L (1467673/1048576 : Rat) (1551233/1048576 : Rat) (141127/524288 : Rat) (298761/1048576 : Rat),.L (368899/262144 : Rat) (194937/131072 : Rat) (35477/131072 : Rat) (300397/1048576 : Rat),.S 1 (111/128 : Rat),.L (1483449/1048576 : Rat) (1567415/1048576 : Rat) (71341/262144 : Rat) (150983/524288 : Rat),.L (1491365/1048576 : Rat) (787839/524288 : Rat) (143463/524288 : Rat) (75901/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P329
