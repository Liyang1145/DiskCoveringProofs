import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P256
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(5/2 : Rat),(11/4 : Rat),(23/32 : Rat),(3/4 : Rat),(1/2 : Rat),(9/16 : Rat)⟩
def toks : List Tok := [.S 2 (17/32 : Rat),.S 1 (47/64 : Rat),.S 0 (21/8 : Rat),.L (1182043/1048576 : Rat) (1319399/1048576 : Rat) (226341/1048576 : Rat) (126569/524288 : Rat),.L (300459/262144 : Rat) (333189/262144 : Rat) (230193/1048576 : Rat) (31969/131072 : Rat),.S 0 (21/8 : Rat),.L (1197277/1048576 : Rat) (667999/524288 : Rat) (229305/1048576 : Rat) (256387/1048576 : Rat),.L (1217243/1048576 : Rat) (1349469/1048576 : Rat) (233193/1048576 : Rat) (129513/524288 : Rat),.S 1 (47/64 : Rat),.S 0 (21/8 : Rat),.L (606285/524288 : Rat) (1350789/1048576 : Rat) (232283/1048576 : Rat) (259285/1048576 : Rat),.L (308267/262144 : Rat) (682301/524288 : Rat) (236277/1048576 : Rat) (32749/131072 : Rat),.S 0 (21/8 : Rat),.L (1227739/1048576 : Rat) (683691/524288 : Rat) (117619/524288 : Rat) (262537/1048576 : Rat),.S 0 (43/16 : Rat),.L (1263967/1048576 : Rat) (1362953/1048576 : Rat) (1893/8192 : Rat) (261669/1048576 : Rat),.L (1273087/1048576 : Rat) (686199/524288 : Rat) (61021/262144 : Rat) (263521/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P256
