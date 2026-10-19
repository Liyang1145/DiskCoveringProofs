import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P551
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(25/32 : Rat),(13/16 : Rat),(15/16 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 2 (31/32 : Rat),.S 1 (51/64 : Rat),.S 2 (61/64 : Rat),.L (1736393/1048576 : Rat) (3587/2048 : Rat) (335615/1048576 : Rat) (22233/65536 : Rat),.L (438039/262144 : Rat) (1853059/1048576 : Rat) (84693/262144 : Rat) (359057/1048576 : Rat),.S 2 (61/64 : Rat),.L (1752245/1048576 : Rat) (1852769/1048576 : Rat) (169395/524288 : Rat) (358999/1048576 : Rat),.L (1767997/1048576 : Rat) (1869285/1048576 : Rat) (85487/262144 : Rat) (90583/262144 : Rat),.S 1 (51/64 : Rat),.S 2 (63/64 : Rat),.L (883965/524288 : Rat) (467393/262144 : Rat) (170967/524288 : Rat) (181195/524288 : Rat),.L (1783715/1048576 : Rat) (1886083/1048576 : Rat) (172551/524288 : Rat) (182863/524288 : Rat),.S 2 (63/64 : Rat),.L (111485/65536 : Rat) (942899/524288 : Rat) (345111/1048576 : Rat) (365669/1048576 : Rat),.L (899767/524288 : Rat) (1902309/1048576 : Rat) (348279/1048576 : Rat) (369009/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P551
