import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P365
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(27/32 : Rat),(7/8 : Rat),(11/16 : Rat),(23/32 : Rat)⟩
def toks : List Tok := [.S 1 (55/64 : Rat),.S 2 (45/64 : Rat),.S 1 (109/128 : Rat),.L (1546755/1048576 : Rat) (815927/524288 : Rat) (297873/1048576 : Rat) (157379/524288 : Rat),.L (1554633/1048576 : Rat) (205015/131072 : Rat) (299433/1048576 : Rat) (316403/1048576 : Rat),.S 1 (109/128 : Rat),.L (1562615/1048576 : Rat) (1648059/1048576 : Rat) (150507/524288 : Rat) (317983/1048576 : Rat),.L (196311/131072 : Rat) (1656325/1048576 : Rat) (151287/524288 : Rat) (319629/1048576 : Rat),.S 2 (45/64 : Rat),.S 1 (111/128 : Rat),.L (1562515/1048576 : Rat) (1648385/1048576 : Rat) (150497/524288 : Rat) (9939/32768 : Rat),.L (49075/32768 : Rat) (1656649/1048576 : Rat) (75639/262144 : Rat) (159847/524288 : Rat),.S 1 (111/128 : Rat),.L (1578363/1048576 : Rat) (832295/524288 : Rat) (304135/1048576 : Rat) (80319/262144 : Rat),.L (793121/524288 : Rat) (836427/524288 : Rat) (152849/524288 : Rat) (322923/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P365
