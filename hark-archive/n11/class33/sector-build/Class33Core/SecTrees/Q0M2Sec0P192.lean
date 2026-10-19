import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P192
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(5/2 : Rat),(11/4 : Rat),(7/8 : Rat),(29/32 : Rat),(5/16 : Rat),(11/32 : Rat)⟩
def toks : List Tok := [.S 1 (57/64 : Rat),.S 2 (21/64 : Rat),.S 0 (21/8 : Rat),.L (583637/524288 : Rat) (1275235/1048576 : Rat) (223469/1048576 : Rat) (244505/1048576 : Rat),.L (147819/131072 : Rat) (1285597/1048576 : Rat) (28305/131072 : Rat) (246529/1048576 : Rat),.S 0 (21/8 : Rat),.L (590697/524288 : Rat) (322739/262144 : Rat) (226215/1048576 : Rat) (30947/131072 : Rat),.L (1197241/1048576 : Rat) (650839/524288 : Rat) (114649/524288 : Rat) (31209/131072 : Rat),.S 2 (21/64 : Rat),.S 0 (21/8 : Rat),.L (295809/262144 : Rat) (1291681/1048576 : Rat) (226573/1048576 : Rat) (123859/524288 : Rat),.L (1198577/1048576 : Rat) (651045/524288 : Rat) (114779/524288 : Rat) (31219/131072 : Rat),.S 0 (21/8 : Rat),.L (74833/65536 : Rat) (1307401/1048576 : Rat) (229315/1048576 : Rat) (250791/1048576 : Rat),.L (1213245/1048576 : Rat) (1318175/1048576 : Rat) (116207/524288 : Rat) (126449/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P192
