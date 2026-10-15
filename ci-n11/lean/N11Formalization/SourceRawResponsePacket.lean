import N11Formalization.SourceRawResponseIntervals

/-! Kernel finite readouts of the ACTUAL two-spoke scalar response and
actual off-diagonal H0. Host literals are only proposals. No coercivity yet. -/
set_option autoImplicit false
namespace N11Formalization.SourceRawResponsePacket
open N11Formalization RatInterval SourceRawResponseIntervals SourceActiveMatrixIntervals
noncomputable section
set_option maxRecDepth 10000

def RL : Fin 9 → Fin 9 → ℤ :=
 ![![32765834,-13334935,-3009638,-188674,-155483,-1476337,-1570456,-2326273,-10741123],![-13336243,38903822,-17621337,-748256,-416202,-2281739,-2209428,-1570644,-757915],![-3011385,-17623725,42998528,-14345855,-942588,-2658921,-2283100,-1477819,-702396],![-188428,-747987,-14343880,30399943,-13575349,-941055,-415921,-155232,-65441],![-155232,-415921,-941055,-13575349,30399943,-14343880,-747987,-188428,-65441],![-1477819,-2283100,-2658921,-942588,-14345855,42998528,-17623725,-3011385,-702396],![-1570644,-2209428,-2281739,-416202,-748256,-17621337,38903822,-13336243,-757915],![-2326273,-1570456,-1476337,-155483,-188674,-3009638,-13334935,32765834,-10741123],![-10740477,-756470,-699704,-64319,-64319,-699704,-756470,-10740477,24496904]]

def RH : Fin 9 → Fin 9 → ℤ :=
 ![![32775812,-13326283,-3001690,-180918,-147729,-1468492,-1562605,-2318371,-10732646],![-13327463,38914509,-17612238,-740415,-408385,-2273783,-2201477,-1562741,-750072],![-3001098,-17612959,43010127,-14335195,-932369,-2648646,-2272837,-1467583,-692185],![-181222,-740765,-14336235,30408091,-13567725,-933826,-408709,-148027,-58239],![-148027,-408709,-933826,-13567725,30408091,-14336235,-740765,-181222,-58239],![-1467583,-2272837,-2648646,-932369,-14335195,43010127,-17612959,-3001098,-692185],![-1562741,-2201477,-2273783,-408385,-740415,-17612238,38914509,-13327463,-750072],![-2318371,-1562605,-1468492,-147729,-180918,-3001690,-13326283,32775812,-10732646],![-10734335,-751421,-694660,-59345,-59345,-694660,-751421,-10734335,24504552]]

def HL : Fin 9 → Fin 9 → ℤ :=
 ![![65531665,-20709459,-1936071,153906,277513,2693303,1762003,-384615,-15804694],![-20709459,77807642,-29828723,-360142,415567,4381040,4218870,1762003,-218748],![-1936071,-29828723,85997055,-20674489,-53313,3562871,4381040,2693303,562131],![153906,-360142,-20674489,60799885,-19369600,-53313,415567,277513,109859],![277513,415567,-53313,-19369600,60799886,-20674489,-360142,153906,109859],![2693303,4381040,3562871,-53313,-20674489,85997055,-29828723,-1936071,562131],![1762003,4218870,4381040,415567,-360142,-29828723,77807642,-20709459,-218748],![-384615,1762003,2693303,277513,153906,-1936071,-20709459,65531665,-15804694],![-15804694,-218748,562131,109859,109859,562131,-218748,-15804694,48993808]]

def HH : Fin 9 → Fin 9 → ℤ :=
 ![![65551627,-20697852,-1930957,160026,291019,2707689,1770703,-383307,-15795655],![-20697852,77829019,-29814540,-356663,422901,4396368,4234106,1770703,-217287],![-1930957,-29814540,86020257,-20663468,-52902,3576693,4396368,2707689,566213],![160026,-356663,-20663468,60816183,-19358721,-52902,422901,291019,119065],![291019,422901,-52902,-19358721,60816183,-20663468,-356663,160026,119065],![2707689,4396368,3576693,-52902,-20663468,86020257,-29814540,-1930957,566213],![1770703,4234106,4396368,422901,-356663,-29814540,77829019,-20697852,-217287],![-383307,1770703,2707689,291019,160026,-1930957,-20697852,65551627,-15795655],![-15795655,-217287,566213,119065,119065,566213,-217287,-15795655,49009103]]

def RB (k l : Fin 9) : RatInterval := intv ((RL k l : ℚ)/1000000000) ((RH k l : ℚ)/1000000000)
def HB (k l : Fin 9) : RatInterval := intv ((HL k l : ℚ)/1000000000) ((HH k l : ℚ)/1000000000)
private theorem s0_0 : SourceFineCompactStressIntervals.compact (.inl (0,0))=intv (2795158/100000000 : ℚ) (2795349/100000000) := rfl
private theorem s0_1 : SourceFineCompactStressIntervals.compact (.inl (0,1))=intv (3274979/100000000 : ℚ) (3275202/100000000) := rfl
private theorem p0_0 : anchorBox 0 0=intv (-73575385/100000000 : ℚ) (-73575382/100000000) := rfl
private theorem p0_1 : anchorBox 0 1=intv (-67724908/100000000 : ℚ) (-67724905/100000000) := rfl
private theorem h0_0 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (0 : Fin 11)) (ResumeLocalIncidence.siteMap 0)=intv (1215189231/2450000000 : ℚ) (1215501731/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (0 : Fin 11))
      (ResumeLocalIncidence.siteMap 0)=49605938 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h0_1 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (0 : Fin 11)) (ResumeLocalIncidence.siteMap 1)=intv (47286677/2450000000 : ℚ) (47599177/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (0 : Fin 11))
      (ResumeLocalIncidence.siteMap 1)=1936446 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h0_2 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (0 : Fin 11)) (ResumeLocalIncidence.siteMap 2)=intv (43714773/2450000000 : ℚ) (44027273/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (0 : Fin 11))
      (ResumeLocalIncidence.siteMap 2)=1790654 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h0_3 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (0 : Fin 11)) (ResumeLocalIncidence.siteMap 3)=intv (7469239/4900000000 : ℚ) (8094239/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (0 : Fin 11))
      (ResumeLocalIncidence.siteMap 3)=158811 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h0_4 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (0 : Fin 11)) (ResumeLocalIncidence.siteMap 4)=intv (7469239/4900000000 : ℚ) (8094239/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (0 : Fin 11))
      (ResumeLocalIncidence.siteMap 4)=158811 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h0_5 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (0 : Fin 11)) (ResumeLocalIncidence.siteMap 5)=intv (43714773/2450000000 : ℚ) (44027273/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (0 : Fin 11))
      (ResumeLocalIncidence.siteMap 5)=1790654 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h0_6 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (0 : Fin 11)) (ResumeLocalIncidence.siteMap 6)=intv (47286677/2450000000 : ℚ) (47599177/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (0 : Fin 11))
      (ResumeLocalIncidence.siteMap 6)=1936446 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h0_7 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (0 : Fin 11)) (ResumeLocalIncidence.siteMap 7)=intv (271653621/4900000000 : ℚ) (272278621/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (0 : Fin 11))
      (ResumeLocalIncidence.siteMap 7)=5550329 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h0_8 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (0 : Fin 11)) (ResumeLocalIncidence.siteMap 8)=intv (908105741/2450000000 : ℚ) (908418241/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (0 : Fin 11))
      (ResumeLocalIncidence.siteMap 8)=37071918 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem s1_0 : SourceFineCompactStressIntervals.compact (.inl (1,0))=intv (2641026/100000000 : ℚ) (2641223/100000000) := rfl
private theorem s1_1 : SourceFineCompactStressIntervals.compact (.inl (1,1))=intv (3462423/100000000 : ℚ) (3462681/100000000) := rfl
private theorem p1_0 : anchorBox 1 0=intv (-14458443/100000000 : ℚ) (-14458439/100000000) := rfl
private theorem p1_1 : anchorBox 1 1=intv (-98949248/100000000 : ℚ) (-98949246/100000000) := rfl
private theorem h1_0 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (1 : Fin 11)) (ResumeLocalIncidence.siteMap 0)=intv (1052117721/2450000000 : ℚ) (1052430221/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (1 : Fin 11))
      (ResumeLocalIncidence.siteMap 0)=42949958 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h1_1 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (1 : Fin 11)) (ResumeLocalIncidence.siteMap 1)=intv (191315171/490000000 : ℚ) (191377671/490000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (1 : Fin 11))
      (ResumeLocalIncidence.siteMap 1)=39050290 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h1_2 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (1 : Fin 11)) (ResumeLocalIncidence.siteMap 2)=intv (187245279/2450000000 : ℚ) (187557779/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (1 : Fin 11))
      (ResumeLocalIncidence.siteMap 2)=7649042 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h1_3 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (1 : Fin 11)) (ResumeLocalIncidence.siteMap 3)=intv (20693947/4900000000 : ℚ) (21318947/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (1 : Fin 11))
      (ResumeLocalIncidence.siteMap 3)=428703 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h1_4 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (1 : Fin 11)) (ResumeLocalIncidence.siteMap 4)=intv (7864119/2450000000 : ℚ) (8176619/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (1 : Fin 11))
      (ResumeLocalIncidence.siteMap 4)=327362 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h1_5 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (1 : Fin 11)) (ResumeLocalIncidence.siteMap 5)=intv (72547353/2450000000 : ℚ) (72859853/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (1 : Fin 11))
      (ResumeLocalIncidence.siteMap 5)=2967494 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h1_6 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (1 : Fin 11)) (ResumeLocalIncidence.siteMap 6)=intv (38269667/1225000000 : ℚ) (38425917/1225000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (1 : Fin 11))
      (ResumeLocalIncidence.siteMap 6)=3130432 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h1_7 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (1 : Fin 11)) (ResumeLocalIncidence.siteMap 7)=intv (57509841/2450000000 : ℚ) (57822341/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (1 : Fin 11))
      (ResumeLocalIncidence.siteMap 7)=2353718 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h1_8 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (1 : Fin 11)) (ResumeLocalIncidence.siteMap 8)=intv (55694647/4900000000 : ℚ) (56319647/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (1 : Fin 11))
      (ResumeLocalIncidence.siteMap 8)=1143003 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem s2_0 : SourceFineCompactStressIntervals.compact (.inl (2,0))=intv (4975411/100000000 : ℚ) (4975574/100000000) := rfl
private theorem s2_1 : SourceFineCompactStressIntervals.compact (.inl (2,1))=intv (3011168/100000000 : ℚ) (3011267/100000000) := rfl
private theorem p2_0 : anchorBox 2 0=intv (40460867/100000000 : ℚ) (40460870/100000000) := rfl
private theorem p2_1 : anchorBox 2 1=intv (-91448993/100000000 : ℚ) (-91448991/100000000) := rfl
private theorem h2_0 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (2 : Fin 11)) (ResumeLocalIncidence.siteMap 0)=intv (140525347/2450000000 : ℚ) (140837847/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (2 : Fin 11))
      (ResumeLocalIncidence.siteMap 0)=5742106 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h2_1 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (2 : Fin 11)) (ResumeLocalIncidence.siteMap 1)=intv (1671525703/4900000000 : ℚ) (1672150703/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (2 : Fin 11))
      (ResumeLocalIncidence.siteMap 1)=34119147 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h2_2 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (2 : Fin 11)) (ResumeLocalIncidence.siteMap 2)=intv (1103411901/2450000000 : ℚ) (1103724401/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (2 : Fin 11))
      (ResumeLocalIncidence.siteMap 2)=45043598 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h2_3 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (2 : Fin 11)) (ResumeLocalIncidence.siteMap 3)=intv (22249607/1225000000 : ℚ) (22405857/1225000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (2 : Fin 11))
      (ResumeLocalIncidence.siteMap 3)=1822672 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h2_4 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (2 : Fin 11)) (ResumeLocalIncidence.siteMap 4)=intv (45797431/4900000000 : ℚ) (46422431/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (2 : Fin 11))
      (ResumeLocalIncidence.siteMap 4)=941019 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h2_5 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (2 : Fin 11)) (ResumeLocalIncidence.siteMap 5)=intv (211110887/4900000000 : ℚ) (211735887/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (2 : Fin 11))
      (ResumeLocalIncidence.siteMap 5)=4314763 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h2_6 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (2 : Fin 11)) (ResumeLocalIncidence.siteMap 6)=intv (48697063/1225000000 : ℚ) (48853313/1225000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (2 : Fin 11))
      (ResumeLocalIncidence.siteMap 6)=3981648 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h2_7 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (2 : Fin 11)) (ResumeLocalIncidence.siteMap 7)=intv (133424817/4900000000 : ℚ) (134049817/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (2 : Fin 11))
      (ResumeLocalIncidence.siteMap 7)=2729333 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h2_8 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (2 : Fin 11)) (ResumeLocalIncidence.siteMap 8)=intv (63667731/4900000000 : ℚ) (64292731/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (2 : Fin 11))
      (ResumeLocalIncidence.siteMap 8)=1305719 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem s3_0 : SourceFineCompactStressIntervals.compact (.inl (3,0))=intv (2894180/100000000 : ℚ) (2894270/100000000) := rfl
private theorem s3_1 : SourceFineCompactStressIntervals.compact (.inl (3,1))=intv (2749356/100000000 : ℚ) (2749442/100000000) := rfl
private theorem p3_0 : anchorBox 3 0=intv (92558379/100000000 : ℚ) (92558381/100000000) := rfl
private theorem p3_1 : anchorBox 3 1=intv (-37854278/100000000 : ℚ) (-37854275/100000000) := rfl
private theorem h3_0 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (3 : Fin 11)) (ResumeLocalIncidence.siteMap 0)=intv (11987959/2450000000 : ℚ) (12300459/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (3 : Fin 11))
      (ResumeLocalIncidence.siteMap 0)=495682 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h3_1 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (3 : Fin 11)) (ResumeLocalIncidence.siteMap 1)=intv (10421969/490000000 : ℚ) (10484469/490000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (3 : Fin 11))
      (ResumeLocalIncidence.siteMap 1)=2133310 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h3_2 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (3 : Fin 11)) (ResumeLocalIncidence.siteMap 2)=intv (73477623/153125000 : ℚ) (293988617/612500000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (3 : Fin 11))
      (ResumeLocalIncidence.siteMap 2)=47991764 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h3_3 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (3 : Fin 11)) (ResumeLocalIncidence.siteMap 3)=intv (2185677509/4900000000 : ℚ) (2186302509/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (3 : Fin 11))
      (ResumeLocalIncidence.siteMap 3)=44612041 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h3_4 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (3 : Fin 11)) (ResumeLocalIncidence.siteMap 4)=intv (76050227/4900000000 : ℚ) (76675227/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (3 : Fin 11))
      (ResumeLocalIncidence.siteMap 4)=1558423 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h3_5 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (3 : Fin 11)) (ResumeLocalIncidence.siteMap 5)=intv (657481/39200000 : ℚ) (662481/39200000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (3 : Fin 11))
      (ResumeLocalIncidence.siteMap 5)=1683625 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h3_6 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (3 : Fin 11)) (ResumeLocalIncidence.siteMap 6)=intv (3000057/306250000 : ℚ) (6078239/612500000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (3 : Fin 11))
      (ResumeLocalIncidence.siteMap 6)=985988 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h3_7 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (3 : Fin 11)) (ResumeLocalIncidence.siteMap 7)=intv (18355863/4900000000 : ℚ) (18980863/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (3 : Fin 11))
      (ResumeLocalIncidence.siteMap 7)=380987 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h3_8 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (3 : Fin 11)) (ResumeLocalIncidence.siteMap 8)=intv (7438271/4900000000 : ℚ) (8063271/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (3 : Fin 11))
      (ResumeLocalIncidence.siteMap 8)=158179 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem s4_0 : SourceFineCompactStressIntervals.compact (.inl (4,0))=intv (2749356/100000000 : ℚ) (2749442/100000000) := rfl
private theorem s4_1 : SourceFineCompactStressIntervals.compact (.inl (4,1))=intv (2894180/100000000 : ℚ) (2894270/100000000) := rfl
private theorem p4_0 : anchorBox 4 0=intv (92558379/100000000 : ℚ) (92558381/100000000) := rfl
private theorem p4_1 : anchorBox 4 1=intv (37854276/100000000 : ℚ) (37854278/100000000) := rfl
private theorem h4_0 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (4 : Fin 11)) (ResumeLocalIncidence.siteMap 0)=intv (1411861/980000000 : ℚ) (1536861/980000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (4 : Fin 11))
      (ResumeLocalIncidence.siteMap 0)=150445 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h4_1 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (4 : Fin 11)) (ResumeLocalIncidence.siteMap 1)=intv (2231227/490000000 : ℚ) (2293727/490000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (4 : Fin 11))
      (ResumeLocalIncidence.siteMap 1)=461730 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h4_2 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (4 : Fin 11)) (ResumeLocalIncidence.siteMap 2)=intv (9989449/612500000 : ℚ) (5033787/306250000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (4 : Fin 11))
      (ResumeLocalIncidence.siteMap 2)=1637308 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h4_3 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (4 : Fin 11)) (ResumeLocalIncidence.siteMap 3)=intv (1169016041/2450000000 : ℚ) (1169328541/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (4 : Fin 11))
      (ResumeLocalIncidence.siteMap 3)=47721318 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h4_4 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (4 : Fin 11)) (ResumeLocalIncidence.siteMap 4)=intv (1169016041/2450000000 : ℚ) (1169328541/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (4 : Fin 11))
      (ResumeLocalIncidence.siteMap 4)=47721318 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h4_5 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (4 : Fin 11)) (ResumeLocalIncidence.siteMap 5)=intv (9989449/612500000 : ℚ) (5033787/306250000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (4 : Fin 11))
      (ResumeLocalIncidence.siteMap 5)=1637308 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h4_6 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (4 : Fin 11)) (ResumeLocalIncidence.siteMap 6)=intv (2231227/490000000 : ℚ) (2293727/490000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (4 : Fin 11))
      (ResumeLocalIncidence.siteMap 6)=461730 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h4_7 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (4 : Fin 11)) (ResumeLocalIncidence.siteMap 7)=intv (1411861/980000000 : ℚ) (1536861/980000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (4 : Fin 11))
      (ResumeLocalIncidence.siteMap 7)=150445 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h4_8 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (4 : Fin 11)) (ResumeLocalIncidence.siteMap 8)=intv (254959/490000000 : ℚ) (317459/490000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (4 : Fin 11))
      (ResumeLocalIncidence.siteMap 8)=58410 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem s5_0 : SourceFineCompactStressIntervals.compact (.inl (5,0))=intv (3011168/100000000 : ℚ) (3011267/100000000) := rfl
private theorem s5_1 : SourceFineCompactStressIntervals.compact (.inl (5,1))=intv (4975411/100000000 : ℚ) (4975574/100000000) := rfl
private theorem p5_0 : anchorBox 5 0=intv (40460867/100000000 : ℚ) (40460870/100000000) := rfl
private theorem p5_1 : anchorBox 5 1=intv (91448991/100000000 : ℚ) (91448993/100000000) := rfl
private theorem h5_0 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (5 : Fin 11)) (ResumeLocalIncidence.siteMap 0)=intv (18355863/4900000000 : ℚ) (18980863/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (5 : Fin 11))
      (ResumeLocalIncidence.siteMap 0)=380987 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h5_1 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (5 : Fin 11)) (ResumeLocalIncidence.siteMap 1)=intv (3000057/306250000 : ℚ) (6078239/612500000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (5 : Fin 11))
      (ResumeLocalIncidence.siteMap 1)=985988 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h5_2 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (5 : Fin 11)) (ResumeLocalIncidence.siteMap 2)=intv (657481/39200000 : ℚ) (662481/39200000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (5 : Fin 11))
      (ResumeLocalIncidence.siteMap 2)=1683625 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h5_3 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (5 : Fin 11)) (ResumeLocalIncidence.siteMap 3)=intv (76050227/4900000000 : ℚ) (76675227/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (5 : Fin 11))
      (ResumeLocalIncidence.siteMap 3)=1558423 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h5_4 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (5 : Fin 11)) (ResumeLocalIncidence.siteMap 4)=intv (2185677509/4900000000 : ℚ) (2186302509/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (5 : Fin 11))
      (ResumeLocalIncidence.siteMap 4)=44612041 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h5_5 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (5 : Fin 11)) (ResumeLocalIncidence.siteMap 5)=intv (73477623/153125000 : ℚ) (293988617/612500000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (5 : Fin 11))
      (ResumeLocalIncidence.siteMap 5)=47991764 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h5_6 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (5 : Fin 11)) (ResumeLocalIncidence.siteMap 6)=intv (10421969/490000000 : ℚ) (10484469/490000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (5 : Fin 11))
      (ResumeLocalIncidence.siteMap 6)=2133310 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h5_7 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (5 : Fin 11)) (ResumeLocalIncidence.siteMap 7)=intv (11987959/2450000000 : ℚ) (12300459/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (5 : Fin 11))
      (ResumeLocalIncidence.siteMap 7)=495682 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h5_8 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (5 : Fin 11)) (ResumeLocalIncidence.siteMap 8)=intv (7438271/4900000000 : ℚ) (8063271/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (5 : Fin 11))
      (ResumeLocalIncidence.siteMap 8)=158179 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem s6_0 : SourceFineCompactStressIntervals.compact (.inl (6,0))=intv (3462423/100000000 : ℚ) (3462681/100000000) := rfl
private theorem s6_1 : SourceFineCompactStressIntervals.compact (.inl (6,1))=intv (2641026/100000000 : ℚ) (2641223/100000000) := rfl
private theorem p6_0 : anchorBox 6 0=intv (-14458443/100000000 : ℚ) (-14458439/100000000) := rfl
private theorem p6_1 : anchorBox 6 1=intv (98949246/100000000 : ℚ) (98949248/100000000) := rfl
private theorem h6_0 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (6 : Fin 11)) (ResumeLocalIncidence.siteMap 0)=intv (133424817/4900000000 : ℚ) (134049817/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (6 : Fin 11))
      (ResumeLocalIncidence.siteMap 0)=2729333 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h6_1 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (6 : Fin 11)) (ResumeLocalIncidence.siteMap 1)=intv (48697063/1225000000 : ℚ) (48853313/1225000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (6 : Fin 11))
      (ResumeLocalIncidence.siteMap 1)=3981648 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h6_2 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (6 : Fin 11)) (ResumeLocalIncidence.siteMap 2)=intv (211110887/4900000000 : ℚ) (211735887/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (6 : Fin 11))
      (ResumeLocalIncidence.siteMap 2)=4314763 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h6_3 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (6 : Fin 11)) (ResumeLocalIncidence.siteMap 3)=intv (45797431/4900000000 : ℚ) (46422431/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (6 : Fin 11))
      (ResumeLocalIncidence.siteMap 3)=941019 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h6_4 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (6 : Fin 11)) (ResumeLocalIncidence.siteMap 4)=intv (22249607/1225000000 : ℚ) (22405857/1225000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (6 : Fin 11))
      (ResumeLocalIncidence.siteMap 4)=1822672 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h6_5 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (6 : Fin 11)) (ResumeLocalIncidence.siteMap 5)=intv (1103411901/2450000000 : ℚ) (1103724401/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (6 : Fin 11))
      (ResumeLocalIncidence.siteMap 5)=45043598 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h6_6 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (6 : Fin 11)) (ResumeLocalIncidence.siteMap 6)=intv (1671525703/4900000000 : ℚ) (1672150703/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (6 : Fin 11))
      (ResumeLocalIncidence.siteMap 6)=34119147 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h6_7 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (6 : Fin 11)) (ResumeLocalIncidence.siteMap 7)=intv (140525347/2450000000 : ℚ) (140837847/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (6 : Fin 11))
      (ResumeLocalIncidence.siteMap 7)=5742106 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h6_8 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (6 : Fin 11)) (ResumeLocalIncidence.siteMap 8)=intv (63667731/4900000000 : ℚ) (64292731/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (6 : Fin 11))
      (ResumeLocalIncidence.siteMap 8)=1305719 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem s7_0 : SourceFineCompactStressIntervals.compact (.inl (7,0))=intv (3274979/100000000 : ℚ) (3275202/100000000) := rfl
private theorem s7_1 : SourceFineCompactStressIntervals.compact (.inl (7,1))=intv (2795158/100000000 : ℚ) (2795349/100000000) := rfl
private theorem p7_0 : anchorBox 7 0=intv (-73575385/100000000 : ℚ) (-73575382/100000000) := rfl
private theorem p7_1 : anchorBox 7 1=intv (67724905/100000000 : ℚ) (67724908/100000000) := rfl
private theorem h7_0 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (7 : Fin 11)) (ResumeLocalIncidence.siteMap 0)=intv (57509841/2450000000 : ℚ) (57822341/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (7 : Fin 11))
      (ResumeLocalIncidence.siteMap 0)=2353718 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h7_1 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (7 : Fin 11)) (ResumeLocalIncidence.siteMap 1)=intv (38269667/1225000000 : ℚ) (38425917/1225000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (7 : Fin 11))
      (ResumeLocalIncidence.siteMap 1)=3130432 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h7_2 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (7 : Fin 11)) (ResumeLocalIncidence.siteMap 2)=intv (72547353/2450000000 : ℚ) (72859853/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (7 : Fin 11))
      (ResumeLocalIncidence.siteMap 2)=2967494 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h7_3 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (7 : Fin 11)) (ResumeLocalIncidence.siteMap 3)=intv (7864119/2450000000 : ℚ) (8176619/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (7 : Fin 11))
      (ResumeLocalIncidence.siteMap 3)=327362 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h7_4 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (7 : Fin 11)) (ResumeLocalIncidence.siteMap 4)=intv (20693947/4900000000 : ℚ) (21318947/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (7 : Fin 11))
      (ResumeLocalIncidence.siteMap 4)=428703 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h7_5 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (7 : Fin 11)) (ResumeLocalIncidence.siteMap 5)=intv (187245279/2450000000 : ℚ) (187557779/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (7 : Fin 11))
      (ResumeLocalIncidence.siteMap 5)=7649042 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h7_6 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (7 : Fin 11)) (ResumeLocalIncidence.siteMap 6)=intv (191315171/490000000 : ℚ) (191377671/490000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (7 : Fin 11))
      (ResumeLocalIncidence.siteMap 6)=39050290 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h7_7 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (7 : Fin 11)) (ResumeLocalIncidence.siteMap 7)=intv (1052117721/2450000000 : ℚ) (1052430221/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (7 : Fin 11))
      (ResumeLocalIncidence.siteMap 7)=42949958 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h7_8 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (7 : Fin 11)) (ResumeLocalIncidence.siteMap 8)=intv (55694647/4900000000 : ℚ) (56319647/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (7 : Fin 11))
      (ResumeLocalIncidence.siteMap 8)=1143003 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem s8_0 : SourceFineCompactStressIntervals.compact (.inl (8,0))=intv (1946618/100000000 : ℚ) (1946831/100000000) := rfl
private theorem s8_1 : SourceFineCompactStressIntervals.compact (.inl (8,1))=intv (1946618/100000000 : ℚ) (1946831/100000000) := rfl
private theorem p8_0 : anchorBox 8 0=intv (-100000000/100000000 : ℚ) (-99999999/100000000) := rfl
private theorem p8_1 : anchorBox 8 1=intv (-2/100000000 : ℚ) (2/100000000) := rfl
private theorem h8_0 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (8 : Fin 11)) (ResumeLocalIncidence.siteMap 0)=intv (271653621/4900000000 : ℚ) (272278621/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (8 : Fin 11))
      (ResumeLocalIncidence.siteMap 0)=5550329 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h8_1 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (8 : Fin 11)) (ResumeLocalIncidence.siteMap 1)=intv (47286677/2450000000 : ℚ) (47599177/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (8 : Fin 11))
      (ResumeLocalIncidence.siteMap 1)=1936446 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h8_2 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (8 : Fin 11)) (ResumeLocalIncidence.siteMap 2)=intv (43714773/2450000000 : ℚ) (44027273/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (8 : Fin 11))
      (ResumeLocalIncidence.siteMap 2)=1790654 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h8_3 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (8 : Fin 11)) (ResumeLocalIncidence.siteMap 3)=intv (7469239/4900000000 : ℚ) (8094239/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (8 : Fin 11))
      (ResumeLocalIncidence.siteMap 3)=158811 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h8_4 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (8 : Fin 11)) (ResumeLocalIncidence.siteMap 4)=intv (7469239/4900000000 : ℚ) (8094239/4900000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (8 : Fin 11))
      (ResumeLocalIncidence.siteMap 4)=158811 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h8_5 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (8 : Fin 11)) (ResumeLocalIncidence.siteMap 5)=intv (43714773/2450000000 : ℚ) (44027273/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (8 : Fin 11))
      (ResumeLocalIncidence.siteMap 5)=1790654 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h8_6 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (8 : Fin 11)) (ResumeLocalIncidence.siteMap 6)=intv (47286677/2450000000 : ℚ) (47599177/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (8 : Fin 11))
      (ResumeLocalIncidence.siteMap 6)=1936446 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h8_7 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (8 : Fin 11)) (ResumeLocalIncidence.siteMap 7)=intv (1215189231/2450000000 : ℚ) (1215501731/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (8 : Fin 11))
      (ResumeLocalIncidence.siteMap 7)=49605938 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem h8_8 : SourceFineResponseIntervals.clippedHBox (Fin.castAdd 9 (8 : Fin 11)) (ResumeLocalIncidence.siteMap 8)=intv (908105741/2450000000 : ℚ) (908418241/2450000000 : ℚ) := by
  have hy : SourceH20ResidualProposal.YN (Fin.castAdd 9 (8 : Fin 11))
      (ResumeLocalIncidence.siteMap 8)=37071918 := rfl
  simp only [SourceFineResponseIntervals.clippedHBox,SourceHarmonicSignedIntervals.clipUnit,
    SourceFineH20CertifiedEnclosure.HBox,hy,intv]
  norm_num
private theorem r0_0 : responseBox 0 0=intv (8027629389841143/245000000000000000 : ℚ) (8030073884258739/245000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s0_0,s0_1]
  have hs0 : SourceActiveLaplacian.spokeSite 0 0=(0 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 0 1=(1 : Fin 11) := by decide
  rw [hs0,hs1,h0_0,h1_0]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb0_0 : Contains (RB 0 0) (responseBox 0 0) := by
  have hb : RB 0 0=intv (32765834/1000000000 : ℚ) (32775812/1000000000) := rfl
  rw [hb,r0_0]
  norm_num [Contains,intv]
private theorem r0_1 : responseBox 0 1=intv (-3267058965900483/245000000000000000 : ℚ) (-3264939570542011/245000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s0_0,s0_1]
  have hs0 : SourceActiveLaplacian.spokeSite 0 0=(0 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 0 1=(1 : Fin 11) := by decide
  rw [hs0,hs1,h0_1,h1_1]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb0_1 : Contains (RB 0 1) (responseBox 0 1) := by
  have hb : RB 0 1=intv (-13334935/1000000000 : ℚ) (-13326283/1000000000) := rfl
  rw [hb,r0_1]
  norm_num [Contains,intv]
private theorem r0_2 : responseBox 0 2=intv (-147472241289927/49000000000000000 : ℚ) (-29416562161731/9800000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s0_0,s0_1]
  have hs0 : SourceActiveLaplacian.spokeSite 0 0=(0 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 0 1=(1 : Fin 11) := by decide
  rw [hs0,hs1,h0_2,h1_2]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb0_2 : Contains (RB 0 2) (responseBox 0 2) := by
  have hb : RB 0 2=intv (-3009638/1000000000 : ℚ) (-3001690/1000000000) := rfl
  rw [hb,r0_2]
  norm_num [Contains,intv]
private theorem r0_3 : responseBox 0 3=intv (-18490016149341/98000000000000000 : ℚ) (-28367982399/156800000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s0_0,s0_1]
  have hs0 : SourceActiveLaplacian.spokeSite 0 0=(0 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 0 1=(1 : Fin 11) := by decide
  rw [hs0,hs1,h0_3,h1_3]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb0_3 : Contains (RB 0 3) (responseBox 0 3) := by
  have hb : RB 0 3=intv (-188674/1000000000 : ℚ) (-180918/1000000000) := rfl
  rw [hb,r0_3]
  norm_num [Contains,intv]
private theorem r0_4 : responseBox 0 4=intv (-76186380698487/490000000000000000 : ℚ) (-18096838075441/122500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s0_0,s0_1]
  have hs0 : SourceActiveLaplacian.spokeSite 0 0=(0 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 0 1=(1 : Fin 11) := by decide
  rw [hs0,hs1,h0_4,h1_4]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb0_4 : Contains (RB 0 4) (responseBox 0 4) := by
  have hb : RB 0 4=intv (-155483/1000000000 : ℚ) (-147729/1000000000) := rfl
  rw [hb,r0_4]
  norm_num [Contains,intv]
private theorem r0_5 : responseBox 0 5=intv (-361702329818583/245000000000000000 : ℚ) (-359780755049721/245000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s0_0,s0_1]
  have hs0 : SourceActiveLaplacian.spokeSite 0 0=(0 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 0 1=(1 : Fin 11) := by decide
  rw [hs0,hs1,h0_5,h1_5]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb0_5 : Contains (RB 0 5) (responseBox 0 5) := by
  have hb : RB 0 5=intv (-1476337/1000000000 : ℚ) (-1468492/1000000000) := rfl
  rw [hb,r0_5]
  norm_num [Contains,intv]
private theorem r0_6 : responseBox 0 6=intv (-384761592248241/245000000000000000 : ℚ) (-11963701407311/7656250000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s0_0,s0_1]
  have hs0 : SourceActiveLaplacian.spokeSite 0 0=(0 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 0 1=(1 : Fin 11) := by decide
  rw [hs0,hs1,h0_6,h1_6]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb0_6 : Contains (RB 0 6) (responseBox 0 6) := by
  have hb : RB 0 6=intv (-1570456/1000000000 : ℚ) (-1562605/1000000000) := rfl
  rw [hb,r0_6]
  norm_num [Contains,intv]
private theorem r0_7 : responseBox 0 7=intv (-1139873464709493/490000000000000000 : ℚ) (-284000458775949/122500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s0_0,s0_1]
  have hs0 : SourceActiveLaplacian.spokeSite 0 0=(0 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 0 1=(1 : Fin 11) := by decide
  rw [hs0,hs1,h0_7,h1_7]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb0_7 : Contains (RB 0 7) (responseBox 0 7) := by
  have hb : RB 0 7=intv (-2326273/1000000000 : ℚ) (-2318371/1000000000) := rfl
  rw [hb,r0_7]
  norm_num [Contains,intv]
private theorem r0_8 : responseBox 0 8=intv (-657893782951989/61250000000000000 : ℚ) (-5258996852941569/490000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s0_0,s0_1]
  have hs0 : SourceActiveLaplacian.spokeSite 0 0=(0 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 0 1=(1 : Fin 11) := by decide
  rw [hs0,hs1,h0_8,h1_8]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb0_8 : Contains (RB 0 8) (responseBox 0 8) := by
  have hb : RB 0 8=intv (-10741123/1000000000 : ℚ) (-10732646/1000000000) := rfl
  rw [hb,r0_8]
  norm_num [Contains,intv]
private theorem r1_0 : responseBox 1 0=intv (-326737944248809/24500000000000000 : ℚ) (-3265228449757527/245000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s1_0,s1_1]
  have hs0 : SourceActiveLaplacian.spokeSite 1 0=(1 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 1 1=(2 : Fin 11) := by decide
  rw [hs0,hs1,h1_0,h2_0]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb1_0 : Contains (RB 1 0) (responseBox 1 0) := by
  have hb : RB 1 0=intv (-13336243/1000000000 : ℚ) (-13327463/1000000000) := rfl
  rw [hb,r1_0]
  norm_num [Contains,intv]
private theorem r1_1 : responseBox 1 1=intv (19062872997162171/490000000000000000 : ℚ) (19068109008268927/490000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s1_0,s1_1]
  have hs0 : SourceActiveLaplacian.spokeSite 1 0=(1 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 1 1=(2 : Fin 11) := by decide
  rw [hs0,hs1,h1_1,h2_1]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb1_1 : Contains (RB 1 1) (responseBox 1 1) := by
  have hb : RB 1 1=intv (38903822/1000000000 : ℚ) (38914509/1000000000) := rfl
  rw [hb,r1_1]
  norm_num [Contains,intv]
private theorem r1_2 : responseBox 1 2=intv (-2158613716151399/122500000000000000 : ℚ) (-4314998394712377/245000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s1_0,s1_1]
  have hs0 : SourceActiveLaplacian.spokeSite 1 0=(1 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 1 1=(2 : Fin 11) := by decide
  rw [hs0,hs1,h1_2,h2_2]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb1_2 : Contains (RB 1 2) (responseBox 1 2) := by
  have hb : RB 1 2=intv (-17621337/1000000000 : ℚ) (-17612238/1000000000) := rfl
  rw [hb,r1_2]
  norm_num [Contains,intv]
private theorem r1_3 : responseBox 1 3=intv (-366645434442649/490000000000000000 : ℚ) (-181401728070333/245000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s1_0,s1_1]
  have hs0 : SourceActiveLaplacian.spokeSite 1 0=(1 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 1 1=(2 : Fin 11) := by decide
  rw [hs0,hs1,h1_3,h2_3]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb1_3 : Contains (RB 1 3) (responseBox 1 3) := by
  have hb : RB 1 3=intv (-748256/1000000000 : ℚ) (-740415/1000000000) := rfl
  rw [hb,r1_3]
  norm_num [Contains,intv]
private theorem r1_4 : responseBox 1 4=intv (-40787723625517/98000000000000000 : ℚ) (-200108763927501/490000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s1_0,s1_1]
  have hs0 : SourceActiveLaplacian.spokeSite 1 0=(1 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 1 1=(2 : Fin 11) := by decide
  rw [hs0,hs1,h1_4,h2_4]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb1_4 : Contains (RB 1 4) (responseBox 1 4) := by
  have hb : RB 1 4=intv (-416202/1000000000 : ℚ) (-408385/1000000000) := rfl
  rw [hb,r1_4]
  norm_num [Contains,intv]
private theorem r1_5 : responseBox 1 5=intv (-223610414394697/98000000000000000 : ℚ) (-1114154081707557/490000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s1_0,s1_1]
  have hs0 : SourceActiveLaplacian.spokeSite 1 0=(1 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 1 1=(2 : Fin 11) := by decide
  rw [hs0,hs1,h1_5,h2_5]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb1_5 : Contains (RB 1 5) (responseBox 1 5) := by
  have hb : RB 1 5=intv (-2281739/1000000000 : ℚ) (-2273783/1000000000) := rfl
  rw [hb,r1_5]
  norm_num [Contains,intv]
private theorem r1_6 : responseBox 1 6=intv (-67663713622161/30625000000000000 : ℚ) (-269681016521991/122500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s1_0,s1_1]
  have hs0 : SourceActiveLaplacian.spokeSite 1 0=(1 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 1 1=(2 : Fin 11) := by decide
  rw [hs0,hs1,h1_6,h2_6]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb1_6 : Contains (RB 1 6) (responseBox 1 6) := by
  have hb : RB 1 6=intv (-2209428/1000000000 : ℚ) (-2201477/1000000000) := rfl
  rw [hb,r1_6]
  norm_num [Contains,intv]
private theorem r1_7 : responseBox 1 7=intv (-769615148305463/490000000000000000 : ℚ) (-765743125825323/490000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s1_0,s1_1]
  have hs0 : SourceActiveLaplacian.spokeSite 1 0=(1 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 1 1=(2 : Fin 11) := by decide
  rw [hs0,hs1,h1_7,h2_7]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb1_7 : Contains (RB 1 7) (responseBox 1 7) := by
  have hb : RB 1 7=intv (-1570644/1000000000 : ℚ) (-1562741/1000000000) := rfl
  rw [hb,r1_7]
  norm_num [Contains,intv]
private theorem r1_8 : responseBox 1 8=intv (-92844491270023/122500000000000000 : ℚ) (-73507125392007/98000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s1_0,s1_1]
  have hs0 : SourceActiveLaplacian.spokeSite 1 0=(1 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 1 1=(2 : Fin 11) := by decide
  rw [hs0,hs1,h1_8,h2_8]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb1_8 : Contains (RB 1 8) (responseBox 1 8) := by
  have hb : RB 1 8=intv (-757915/1000000000 : ℚ) (-750072/1000000000) := rfl
  rw [hb,r1_8]
  norm_num [Contains,intv]
private theorem r2_0 : responseBox 2 0=intv (-737789096020731/245000000000000000 : ℚ) (-735269115768729/245000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s2_0,s2_1]
  have hs0 : SourceActiveLaplacian.spokeSite 2 0=(2 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 2 1=(3 : Fin 11) := by decide
  rw [hs0,hs1,h2_0,h3_0]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb2_0 : Contains (RB 2 0) (responseBox 2 0) := by
  have hb : RB 2 0=intv (-3011385/1000000000 : ℚ) (-3001098/1000000000) := rfl
  rw [hb,r2_0]
  norm_num [Contains,intv]
private theorem r2_1 : responseBox 2 1=intv (-67465819664459/3828125000000000 : ℚ) (-8630350364986853/490000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s2_0,s2_1]
  have hs0 : SourceActiveLaplacian.spokeSite 2 0=(2 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 2 1=(3 : Fin 11) := by decide
  rw [hs0,hs1,h2_1,h3_1]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb2_1 : Contains (RB 2 1) (responseBox 2 1) := by
  have hb : RB 2 1=intv (-17623725/1000000000 : ℚ) (-17612959/1000000000) := rfl
  rw [hb,r2_1]
  norm_num [Contains,intv]
private theorem r2_2 : responseBox 2 2=intv (2106927912159513/49000000000000000 : ℚ) (1053748102204037/24500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s2_0,s2_1]
  have hs0 : SourceActiveLaplacian.spokeSite 2 0=(2 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 2 1=(3 : Fin 11) := by decide
  rw [hs0,hs1,h2_2,h3_2]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb2_2 : Contains (RB 2 2) (responseBox 2 2) := by
  have hb : RB 2 2=intv (42998528/1000000000 : ℚ) (43010127/1000000000) := rfl
  rw [hb,r2_2]
  norm_num [Contains,intv]
private theorem r2_3 : responseBox 2 3=intv (-281178743820663/19600000000000000 : ℚ) (-351212296553721/24500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s2_0,s2_1]
  have hs0 : SourceActiveLaplacian.spokeSite 2 0=(2 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 2 1=(3 : Fin 11) := by decide
  rw [hs0,hs1,h2_3,h3_3]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb2_3 : Contains (RB 2 3) (responseBox 2 3) := by
  have hb : RB 2 3=intv (-14345855/1000000000 : ℚ) (-14335195/1000000000) := rfl
  rw [hb,r2_3]
  norm_num [Contains,intv]
private theorem r2_4 : responseBox 2 4=intv (-461867821483003/490000000000000000 : ℚ) (-456861051904277/490000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s2_0,s2_1]
  have hs0 : SourceActiveLaplacian.spokeSite 2 0=(2 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 2 1=(3 : Fin 11) := by decide
  rw [hs0,hs1,h2_4,h3_4]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb2_4 : Contains (RB 2 4) (responseBox 2 4) := by
  have hb : RB 2 4=intv (-942588/1000000000 : ℚ) (-932369/1000000000) := rfl
  rw [hb,r2_4]
  norm_num [Contains,intv]
private theorem r2_5 : responseBox 2 5=intv (-1302870970902513/490000000000000000 : ℚ) (-1297836647875557/490000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s2_0,s2_1]
  have hs0 : SourceActiveLaplacian.spokeSite 2 0=(2 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 2 1=(3 : Fin 11) := by decide
  rw [hs0,hs1,h2_5,h3_5]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb2_5 : Contains (RB 2 5) (responseBox 2 5) := by
  have hb : RB 2 5=intv (-2658921/1000000000 : ℚ) (-2648646/1000000000) := rfl
  rw [hb,r2_5]
  norm_num [Contains,intv]
private theorem r2_6 : responseBox 2 6=intv (-17479979688393/7656250000000000 : ℚ) (-278422605464197/122500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s2_0,s2_1]
  have hs0 : SourceActiveLaplacian.spokeSite 2 0=(2 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 2 1=(3 : Fin 11) := by decide
  rw [hs0,hs1,h2_6,h3_6]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb2_6 : Contains (RB 2 6) (responseBox 2 6) := by
  have hb : RB 2 6=intv (-2283100/1000000000 : ℚ) (-2272837/1000000000) := rfl
  rw [hb,r2_6]
  norm_num [Contains,intv]
private theorem r2_7 : responseBox 2 7=intv (-724131230553379/490000000000000000 : ℚ) (-719115889452771/490000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s2_0,s2_1]
  have hs0 : SourceActiveLaplacian.spokeSite 2 0=(2 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 2 1=(3 : Fin 11) := by decide
  rw [hs0,hs1,h2_7,h3_7]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb2_7 : Contains (RB 2 7) (responseBox 2 7) := by
  have hb : RB 2 7=intv (-1477819/1000000000 : ℚ) (-1467583/1000000000) := rfl
  rw [hb,r2_7]
  norm_num [Contains,intv]
private theorem r2_8 : responseBox 2 8=intv (-344173902626951/490000000000000000 : ℚ) (-339171012772969/490000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s2_0,s2_1]
  have hs0 : SourceActiveLaplacian.spokeSite 2 0=(2 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 2 1=(3 : Fin 11) := by decide
  rw [hs0,hs1,h2_8,h3_8]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb2_8 : Contains (RB 2 8) (responseBox 2 8) := by
  have hb : RB 2 8=intv (-702396/1000000000 : ℚ) (-692185/1000000000) := rfl
  rw [hb,r2_8]
  norm_num [Contains,intv]
private theorem r3_0 : responseBox 3 0=intv (-9232924984767/49000000000000000 : ℚ) (-4439958245741/24500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s3_0,s3_1]
  have hs0 : SourceActiveLaplacian.spokeSite 3 0=(3 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 3 1=(4 : Fin 11) := by decide
  rw [hs0,hs1,h3_0,h4_0]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb3_0 : Contains (RB 3 0) (responseBox 3 0) := by
  have hb : RB 3 0=intv (-188428/1000000000 : ℚ) (-181222/1000000000) := rfl
  rw [hb,r3_0]
  norm_num [Contains,intv]
private theorem r3_1 : responseBox 3 1=intv (-9162838360741/12250000000000000 : ℚ) (-4537186447529/6125000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s3_0,s3_1]
  have hs0 : SourceActiveLaplacian.spokeSite 3 0=(3 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 3 1=(4 : Fin 11) := by decide
  rw [hs0,hs1,h3_1,h4_1]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb3_1 : Contains (RB 3 1) (responseBox 3 1) := by
  have hb : RB 3 1=intv (-747987/1000000000 : ℚ) (-740765/1000000000) := rfl
  rw [hb,r3_1]
  norm_num [Contains,intv]
private theorem r3_2 : responseBox 3 2=intv (-439281322659149/30625000000000000 : ℚ) (-219523604820351/15312500000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s3_0,s3_1]
  have hs0 : SourceActiveLaplacian.spokeSite 3 0=(3 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 3 1=(4 : Fin 11) := by decide
  rw [hs0,hs1,h3_2,h4_2]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb3_2 : Contains (RB 3 2) (responseBox 3 2) := by
  have hb : RB 3 2=intv (-14343880/1000000000 : ℚ) (-14336235/1000000000) := rfl
  rw [hb,r3_2]
  norm_num [Contains,intv]
private theorem r3_3 : responseBox 3 3=intv (3723993131040797/122500000000000000 : ℚ) (7449982176214163/245000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s3_0,s3_1]
  have hs0 : SourceActiveLaplacian.spokeSite 3 0=(3 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 3 1=(4 : Fin 11) := by decide
  rw [hs0,hs1,h3_3,h4_3]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb3_3 : Contains (RB 3 3) (responseBox 3 3) := by
  have hb : RB 3 3=intv (30399943/1000000000 : ℚ) (30408091/1000000000) := rfl
  rw [hb,r3_3]
  norm_num [Contains,intv]
private theorem r3_4 : responseBox 3 4=intv (-3325960407048767/245000000000000000 : ℚ) (-1662046394704513/122500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s3_0,s3_1]
  have hs0 : SourceActiveLaplacian.spokeSite 3 0=(3 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 3 1=(4 : Fin 11) := by decide
  rw [hs0,hs1,h3_4,h4_4]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb3_4 : Contains (RB 3 4) (responseBox 3 4) := by
  have hb : RB 3 4=intv (-13575349/1000000000 : ℚ) (-13567725/1000000000) := rfl
  rw [hb,r3_4]
  norm_num [Contains,intv]
private theorem r3_5 : responseBox 3 5=intv (-230558273416707/245000000000000000 : ℚ) (-114393739357813/122500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s3_0,s3_1]
  have hs0 : SourceActiveLaplacian.spokeSite 3 0=(3 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 3 1=(4 : Fin 11) := by decide
  rw [hs0,hs1,h3_5,h4_5]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb3_5 : Contains (RB 3 5) (responseBox 3 5) := by
  have hb : RB 3 5=intv (-941055/1000000000 : ℚ) (-933826/1000000000) := rfl
  rw [hb,r3_5]
  norm_num [Contains,intv]
private theorem r3_6 : responseBox 3 6=intv (-10190060591379/24500000000000000 : ℚ) (-5006691322257/12250000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s3_0,s3_1]
  have hs0 : SourceActiveLaplacian.spokeSite 3 0=(3 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 3 1=(4 : Fin 11) := by decide
  rw [hs0,hs1,h3_6,h4_6]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb3_6 : Contains (RB 3 6) (responseBox 3 6) := by
  have hb : RB 3 6=intv (-415921/1000000000 : ℚ) (-408709/1000000000) := rfl
  rw [hb,r3_6]
  norm_num [Contains,intv]
private theorem r3_7 : responseBox 3 7=intv (-3803164663141/24500000000000000 : ℚ) (-1813342853373/12250000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s3_0,s3_1]
  have hs0 : SourceActiveLaplacian.spokeSite 3 0=(3 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 3 1=(4 : Fin 11) := by decide
  rw [hs0,hs1,h3_7,h4_7]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb3_7 : Contains (RB 3 7) (responseBox 3 7) := by
  have hb : RB 3 7=intv (-155232/1000000000 : ℚ) (-148027/1000000000) := rfl
  rw [hb,r3_7]
  norm_num [Contains,intv]
private theorem r3_8 : responseBox 3 8=intv (-641312688719/9800000000000000 : ℚ) (-1426871286341/24500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s3_0,s3_1]
  have hs0 : SourceActiveLaplacian.spokeSite 3 0=(3 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 3 1=(4 : Fin 11) := by decide
  rw [hs0,hs1,h3_8,h4_8]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb3_8 : Contains (RB 3 8) (responseBox 3 8) := by
  have hb : RB 3 8=intv (-65441/1000000000 : ℚ) (-58239/1000000000) := rfl
  rw [hb,r3_8]
  norm_num [Contains,intv]
private theorem r4_0 : responseBox 4 0=intv (-3803164663141/24500000000000000 : ℚ) (-1813342853373/12250000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s4_0,s4_1]
  have hs0 : SourceActiveLaplacian.spokeSite 4 0=(4 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 4 1=(5 : Fin 11) := by decide
  rw [hs0,hs1,h4_0,h5_0]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb4_0 : Contains (RB 4 0) (responseBox 4 0) := by
  have hb : RB 4 0=intv (-155232/1000000000 : ℚ) (-148027/1000000000) := rfl
  rw [hb,r4_0]
  norm_num [Contains,intv]
private theorem r4_1 : responseBox 4 1=intv (-10190060591379/24500000000000000 : ℚ) (-5006691322257/12250000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s4_0,s4_1]
  have hs0 : SourceActiveLaplacian.spokeSite 4 0=(4 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 4 1=(5 : Fin 11) := by decide
  rw [hs0,hs1,h4_1,h5_1]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb4_1 : Contains (RB 4 1) (responseBox 4 1) := by
  have hb : RB 4 1=intv (-415921/1000000000 : ℚ) (-408709/1000000000) := rfl
  rw [hb,r4_1]
  norm_num [Contains,intv]
private theorem r4_2 : responseBox 4 2=intv (-230558273416707/245000000000000000 : ℚ) (-114393739357813/122500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s4_0,s4_1]
  have hs0 : SourceActiveLaplacian.spokeSite 4 0=(4 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 4 1=(5 : Fin 11) := by decide
  rw [hs0,hs1,h4_2,h5_2]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb4_2 : Contains (RB 4 2) (responseBox 4 2) := by
  have hb : RB 4 2=intv (-941055/1000000000 : ℚ) (-933826/1000000000) := rfl
  rw [hb,r4_2]
  norm_num [Contains,intv]
private theorem r4_3 : responseBox 4 3=intv (-3325960407048767/245000000000000000 : ℚ) (-1662046394704513/122500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s4_0,s4_1]
  have hs0 : SourceActiveLaplacian.spokeSite 4 0=(4 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 4 1=(5 : Fin 11) := by decide
  rw [hs0,hs1,h4_3,h5_3]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb4_3 : Contains (RB 4 3) (responseBox 4 3) := by
  have hb : RB 4 3=intv (-13575349/1000000000 : ℚ) (-13567725/1000000000) := rfl
  rw [hb,r4_3]
  norm_num [Contains,intv]
private theorem r4_4 : responseBox 4 4=intv (3723993131040797/122500000000000000 : ℚ) (7449982176214163/245000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s4_0,s4_1]
  have hs0 : SourceActiveLaplacian.spokeSite 4 0=(4 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 4 1=(5 : Fin 11) := by decide
  rw [hs0,hs1,h4_4,h5_4]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb4_4 : Contains (RB 4 4) (responseBox 4 4) := by
  have hb : RB 4 4=intv (30399943/1000000000 : ℚ) (30408091/1000000000) := rfl
  rw [hb,r4_4]
  norm_num [Contains,intv]
private theorem r4_5 : responseBox 4 5=intv (-439281322659149/30625000000000000 : ℚ) (-219523604820351/15312500000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s4_0,s4_1]
  have hs0 : SourceActiveLaplacian.spokeSite 4 0=(4 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 4 1=(5 : Fin 11) := by decide
  rw [hs0,hs1,h4_5,h5_5]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb4_5 : Contains (RB 4 5) (responseBox 4 5) := by
  have hb : RB 4 5=intv (-14343880/1000000000 : ℚ) (-14336235/1000000000) := rfl
  rw [hb,r4_5]
  norm_num [Contains,intv]
private theorem r4_6 : responseBox 4 6=intv (-9162838360741/12250000000000000 : ℚ) (-4537186447529/6125000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s4_0,s4_1]
  have hs0 : SourceActiveLaplacian.spokeSite 4 0=(4 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 4 1=(5 : Fin 11) := by decide
  rw [hs0,hs1,h4_6,h5_6]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb4_6 : Contains (RB 4 6) (responseBox 4 6) := by
  have hb : RB 4 6=intv (-747987/1000000000 : ℚ) (-740765/1000000000) := rfl
  rw [hb,r4_6]
  norm_num [Contains,intv]
private theorem r4_7 : responseBox 4 7=intv (-9232924984767/49000000000000000 : ℚ) (-4439958245741/24500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s4_0,s4_1]
  have hs0 : SourceActiveLaplacian.spokeSite 4 0=(4 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 4 1=(5 : Fin 11) := by decide
  rw [hs0,hs1,h4_7,h5_7]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb4_7 : Contains (RB 4 7) (responseBox 4 7) := by
  have hb : RB 4 7=intv (-188428/1000000000 : ℚ) (-181222/1000000000) := rfl
  rw [hb,r4_7]
  norm_num [Contains,intv]
private theorem r4_8 : responseBox 4 8=intv (-641312688719/9800000000000000 : ℚ) (-1426871286341/24500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s4_0,s4_1]
  have hs0 : SourceActiveLaplacian.spokeSite 4 0=(4 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 4 1=(5 : Fin 11) := by decide
  rw [hs0,hs1,h4_8,h5_8]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb4_8 : Contains (RB 4 8) (responseBox 4 8) := by
  have hb : RB 4 8=intv (-65441/1000000000 : ℚ) (-58239/1000000000) := rfl
  rw [hb,r4_8]
  norm_num [Contains,intv]
private theorem r5_0 : responseBox 5 0=intv (-724131230553379/490000000000000000 : ℚ) (-719115889452771/490000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s5_0,s5_1]
  have hs0 : SourceActiveLaplacian.spokeSite 5 0=(5 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 5 1=(6 : Fin 11) := by decide
  rw [hs0,hs1,h5_0,h6_0]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb5_0 : Contains (RB 5 0) (responseBox 5 0) := by
  have hb : RB 5 0=intv (-1477819/1000000000 : ℚ) (-1467583/1000000000) := rfl
  rw [hb,r5_0]
  norm_num [Contains,intv]
private theorem r5_1 : responseBox 5 1=intv (-17479979688393/7656250000000000 : ℚ) (-278422605464197/122500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s5_0,s5_1]
  have hs0 : SourceActiveLaplacian.spokeSite 5 0=(5 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 5 1=(6 : Fin 11) := by decide
  rw [hs0,hs1,h5_1,h6_1]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb5_1 : Contains (RB 5 1) (responseBox 5 1) := by
  have hb : RB 5 1=intv (-2283100/1000000000 : ℚ) (-2272837/1000000000) := rfl
  rw [hb,r5_1]
  norm_num [Contains,intv]
private theorem r5_2 : responseBox 5 2=intv (-1302870970902513/490000000000000000 : ℚ) (-1297836647875557/490000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s5_0,s5_1]
  have hs0 : SourceActiveLaplacian.spokeSite 5 0=(5 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 5 1=(6 : Fin 11) := by decide
  rw [hs0,hs1,h5_2,h6_2]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb5_2 : Contains (RB 5 2) (responseBox 5 2) := by
  have hb : RB 5 2=intv (-2658921/1000000000 : ℚ) (-2648646/1000000000) := rfl
  rw [hb,r5_2]
  norm_num [Contains,intv]
private theorem r5_3 : responseBox 5 3=intv (-461867821483003/490000000000000000 : ℚ) (-456861051904277/490000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s5_0,s5_1]
  have hs0 : SourceActiveLaplacian.spokeSite 5 0=(5 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 5 1=(6 : Fin 11) := by decide
  rw [hs0,hs1,h5_3,h6_3]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb5_3 : Contains (RB 5 3) (responseBox 5 3) := by
  have hb : RB 5 3=intv (-942588/1000000000 : ℚ) (-932369/1000000000) := rfl
  rw [hb,r5_3]
  norm_num [Contains,intv]
private theorem r5_4 : responseBox 5 4=intv (-281178743820663/19600000000000000 : ℚ) (-351212296553721/24500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s5_0,s5_1]
  have hs0 : SourceActiveLaplacian.spokeSite 5 0=(5 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 5 1=(6 : Fin 11) := by decide
  rw [hs0,hs1,h5_4,h6_4]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb5_4 : Contains (RB 5 4) (responseBox 5 4) := by
  have hb : RB 5 4=intv (-14345855/1000000000 : ℚ) (-14335195/1000000000) := rfl
  rw [hb,r5_4]
  norm_num [Contains,intv]
private theorem r5_5 : responseBox 5 5=intv (2106927912159513/49000000000000000 : ℚ) (1053748102204037/24500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s5_0,s5_1]
  have hs0 : SourceActiveLaplacian.spokeSite 5 0=(5 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 5 1=(6 : Fin 11) := by decide
  rw [hs0,hs1,h5_5,h6_5]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb5_5 : Contains (RB 5 5) (responseBox 5 5) := by
  have hb : RB 5 5=intv (42998528/1000000000 : ℚ) (43010127/1000000000) := rfl
  rw [hb,r5_5]
  norm_num [Contains,intv]
private theorem r5_6 : responseBox 5 6=intv (-67465819664459/3828125000000000 : ℚ) (-8630350364986853/490000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s5_0,s5_1]
  have hs0 : SourceActiveLaplacian.spokeSite 5 0=(5 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 5 1=(6 : Fin 11) := by decide
  rw [hs0,hs1,h5_6,h6_6]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb5_6 : Contains (RB 5 6) (responseBox 5 6) := by
  have hb : RB 5 6=intv (-17623725/1000000000 : ℚ) (-17612959/1000000000) := rfl
  rw [hb,r5_6]
  norm_num [Contains,intv]
private theorem r5_7 : responseBox 5 7=intv (-737789096020731/245000000000000000 : ℚ) (-735269115768729/245000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s5_0,s5_1]
  have hs0 : SourceActiveLaplacian.spokeSite 5 0=(5 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 5 1=(6 : Fin 11) := by decide
  rw [hs0,hs1,h5_7,h6_7]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb5_7 : Contains (RB 5 7) (responseBox 5 7) := by
  have hb : RB 5 7=intv (-3011385/1000000000 : ℚ) (-3001098/1000000000) := rfl
  rw [hb,r5_7]
  norm_num [Contains,intv]
private theorem r5_8 : responseBox 5 8=intv (-344173902626951/490000000000000000 : ℚ) (-339171012772969/490000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s5_0,s5_1]
  have hs0 : SourceActiveLaplacian.spokeSite 5 0=(5 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 5 1=(6 : Fin 11) := by decide
  rw [hs0,hs1,h5_8,h6_8]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb5_8 : Contains (RB 5 8) (responseBox 5 8) := by
  have hb : RB 5 8=intv (-702396/1000000000 : ℚ) (-692185/1000000000) := rfl
  rw [hb,r5_8]
  norm_num [Contains,intv]
private theorem r6_0 : responseBox 6 0=intv (-769615148305463/490000000000000000 : ℚ) (-765743125825323/490000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s6_0,s6_1]
  have hs0 : SourceActiveLaplacian.spokeSite 6 0=(6 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 6 1=(7 : Fin 11) := by decide
  rw [hs0,hs1,h6_0,h7_0]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb6_0 : Contains (RB 6 0) (responseBox 6 0) := by
  have hb : RB 6 0=intv (-1570644/1000000000 : ℚ) (-1562741/1000000000) := rfl
  rw [hb,r6_0]
  norm_num [Contains,intv]
private theorem r6_1 : responseBox 6 1=intv (-67663713622161/30625000000000000 : ℚ) (-269681016521991/122500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s6_0,s6_1]
  have hs0 : SourceActiveLaplacian.spokeSite 6 0=(6 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 6 1=(7 : Fin 11) := by decide
  rw [hs0,hs1,h6_1,h7_1]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb6_1 : Contains (RB 6 1) (responseBox 6 1) := by
  have hb : RB 6 1=intv (-2209428/1000000000 : ℚ) (-2201477/1000000000) := rfl
  rw [hb,r6_1]
  norm_num [Contains,intv]
private theorem r6_2 : responseBox 6 2=intv (-223610414394697/98000000000000000 : ℚ) (-1114154081707557/490000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s6_0,s6_1]
  have hs0 : SourceActiveLaplacian.spokeSite 6 0=(6 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 6 1=(7 : Fin 11) := by decide
  rw [hs0,hs1,h6_2,h7_2]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb6_2 : Contains (RB 6 2) (responseBox 6 2) := by
  have hb : RB 6 2=intv (-2281739/1000000000 : ℚ) (-2273783/1000000000) := rfl
  rw [hb,r6_2]
  norm_num [Contains,intv]
private theorem r6_3 : responseBox 6 3=intv (-40787723625517/98000000000000000 : ℚ) (-200108763927501/490000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s6_0,s6_1]
  have hs0 : SourceActiveLaplacian.spokeSite 6 0=(6 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 6 1=(7 : Fin 11) := by decide
  rw [hs0,hs1,h6_3,h7_3]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb6_3 : Contains (RB 6 3) (responseBox 6 3) := by
  have hb : RB 6 3=intv (-416202/1000000000 : ℚ) (-408385/1000000000) := rfl
  rw [hb,r6_3]
  norm_num [Contains,intv]
private theorem r6_4 : responseBox 6 4=intv (-366645434442649/490000000000000000 : ℚ) (-181401728070333/245000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s6_0,s6_1]
  have hs0 : SourceActiveLaplacian.spokeSite 6 0=(6 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 6 1=(7 : Fin 11) := by decide
  rw [hs0,hs1,h6_4,h7_4]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb6_4 : Contains (RB 6 4) (responseBox 6 4) := by
  have hb : RB 6 4=intv (-748256/1000000000 : ℚ) (-740415/1000000000) := rfl
  rw [hb,r6_4]
  norm_num [Contains,intv]
private theorem r6_5 : responseBox 6 5=intv (-2158613716151399/122500000000000000 : ℚ) (-4314998394712377/245000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s6_0,s6_1]
  have hs0 : SourceActiveLaplacian.spokeSite 6 0=(6 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 6 1=(7 : Fin 11) := by decide
  rw [hs0,hs1,h6_5,h7_5]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb6_5 : Contains (RB 6 5) (responseBox 6 5) := by
  have hb : RB 6 5=intv (-17621337/1000000000 : ℚ) (-17612238/1000000000) := rfl
  rw [hb,r6_5]
  norm_num [Contains,intv]
private theorem r6_6 : responseBox 6 6=intv (19062872997162171/490000000000000000 : ℚ) (19068109008268927/490000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s6_0,s6_1]
  have hs0 : SourceActiveLaplacian.spokeSite 6 0=(6 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 6 1=(7 : Fin 11) := by decide
  rw [hs0,hs1,h6_6,h7_6]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb6_6 : Contains (RB 6 6) (responseBox 6 6) := by
  have hb : RB 6 6=intv (38903822/1000000000 : ℚ) (38914509/1000000000) := rfl
  rw [hb,r6_6]
  norm_num [Contains,intv]
private theorem r6_7 : responseBox 6 7=intv (-326737944248809/24500000000000000 : ℚ) (-3265228449757527/245000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s6_0,s6_1]
  have hs0 : SourceActiveLaplacian.spokeSite 6 0=(6 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 6 1=(7 : Fin 11) := by decide
  rw [hs0,hs1,h6_7,h7_7]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb6_7 : Contains (RB 6 7) (responseBox 6 7) := by
  have hb : RB 6 7=intv (-13336243/1000000000 : ℚ) (-13327463/1000000000) := rfl
  rw [hb,r6_7]
  norm_num [Contains,intv]
private theorem r6_8 : responseBox 6 8=intv (-92844491270023/122500000000000000 : ℚ) (-73507125392007/98000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s6_0,s6_1]
  have hs0 : SourceActiveLaplacian.spokeSite 6 0=(6 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 6 1=(7 : Fin 11) := by decide
  rw [hs0,hs1,h6_8,h7_8]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb6_8 : Contains (RB 6 8) (responseBox 6 8) := by
  have hb : RB 6 8=intv (-757915/1000000000 : ℚ) (-750072/1000000000) := rfl
  rw [hb,r6_8]
  norm_num [Contains,intv]
private theorem r7_0 : responseBox 7 0=intv (-1139873464709493/490000000000000000 : ℚ) (-284000458775949/122500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s7_0,s7_1]
  have hs0 : SourceActiveLaplacian.spokeSite 7 0=(7 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 7 1=(8 : Fin 11) := by decide
  rw [hs0,hs1,h7_0,h8_0]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb7_0 : Contains (RB 7 0) (responseBox 7 0) := by
  have hb : RB 7 0=intv (-2326273/1000000000 : ℚ) (-2318371/1000000000) := rfl
  rw [hb,r7_0]
  norm_num [Contains,intv]
private theorem r7_1 : responseBox 7 1=intv (-384761592248241/245000000000000000 : ℚ) (-11963701407311/7656250000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s7_0,s7_1]
  have hs0 : SourceActiveLaplacian.spokeSite 7 0=(7 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 7 1=(8 : Fin 11) := by decide
  rw [hs0,hs1,h7_1,h8_1]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb7_1 : Contains (RB 7 1) (responseBox 7 1) := by
  have hb : RB 7 1=intv (-1570456/1000000000 : ℚ) (-1562605/1000000000) := rfl
  rw [hb,r7_1]
  norm_num [Contains,intv]
private theorem r7_2 : responseBox 7 2=intv (-361702329818583/245000000000000000 : ℚ) (-359780755049721/245000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s7_0,s7_1]
  have hs0 : SourceActiveLaplacian.spokeSite 7 0=(7 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 7 1=(8 : Fin 11) := by decide
  rw [hs0,hs1,h7_2,h8_2]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb7_2 : Contains (RB 7 2) (responseBox 7 2) := by
  have hb : RB 7 2=intv (-1476337/1000000000 : ℚ) (-1468492/1000000000) := rfl
  rw [hb,r7_2]
  norm_num [Contains,intv]
private theorem r7_3 : responseBox 7 3=intv (-76186380698487/490000000000000000 : ℚ) (-18096838075441/122500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s7_0,s7_1]
  have hs0 : SourceActiveLaplacian.spokeSite 7 0=(7 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 7 1=(8 : Fin 11) := by decide
  rw [hs0,hs1,h7_3,h8_3]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb7_3 : Contains (RB 7 3) (responseBox 7 3) := by
  have hb : RB 7 3=intv (-155483/1000000000 : ℚ) (-147729/1000000000) := rfl
  rw [hb,r7_3]
  norm_num [Contains,intv]
private theorem r7_4 : responseBox 7 4=intv (-18490016149341/98000000000000000 : ℚ) (-28367982399/156800000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s7_0,s7_1]
  have hs0 : SourceActiveLaplacian.spokeSite 7 0=(7 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 7 1=(8 : Fin 11) := by decide
  rw [hs0,hs1,h7_4,h8_4]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb7_4 : Contains (RB 7 4) (responseBox 7 4) := by
  have hb : RB 7 4=intv (-188674/1000000000 : ℚ) (-180918/1000000000) := rfl
  rw [hb,r7_4]
  norm_num [Contains,intv]
private theorem r7_5 : responseBox 7 5=intv (-147472241289927/49000000000000000 : ℚ) (-29416562161731/9800000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s7_0,s7_1]
  have hs0 : SourceActiveLaplacian.spokeSite 7 0=(7 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 7 1=(8 : Fin 11) := by decide
  rw [hs0,hs1,h7_5,h8_5]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb7_5 : Contains (RB 7 5) (responseBox 7 5) := by
  have hb : RB 7 5=intv (-3009638/1000000000 : ℚ) (-3001690/1000000000) := rfl
  rw [hb,r7_5]
  norm_num [Contains,intv]
private theorem r7_6 : responseBox 7 6=intv (-3267058965900483/245000000000000000 : ℚ) (-3264939570542011/245000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s7_0,s7_1]
  have hs0 : SourceActiveLaplacian.spokeSite 7 0=(7 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 7 1=(8 : Fin 11) := by decide
  rw [hs0,hs1,h7_6,h8_6]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb7_6 : Contains (RB 7 6) (responseBox 7 6) := by
  have hb : RB 7 6=intv (-13334935/1000000000 : ℚ) (-13326283/1000000000) := rfl
  rw [hb,r7_6]
  norm_num [Contains,intv]
private theorem r7_7 : responseBox 7 7=intv (8027629389841143/245000000000000000 : ℚ) (8030073884258739/245000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s7_0,s7_1]
  have hs0 : SourceActiveLaplacian.spokeSite 7 0=(7 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 7 1=(8 : Fin 11) := by decide
  rw [hs0,hs1,h7_7,h8_7]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb7_7 : Contains (RB 7 7) (responseBox 7 7) := by
  have hb : RB 7 7=intv (32765834/1000000000 : ℚ) (32775812/1000000000) := rfl
  rw [hb,r7_7]
  norm_num [Contains,intv]
private theorem r7_8 : responseBox 7 8=intv (-657893782951989/61250000000000000 : ℚ) (-5258996852941569/490000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s7_0,s7_1]
  have hs0 : SourceActiveLaplacian.spokeSite 7 0=(7 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 7 1=(8 : Fin 11) := by decide
  rw [hs0,hs1,h7_8,h8_8]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb7_8 : Contains (RB 7 8) (responseBox 7 8) := by
  have hb : RB 7 8=intv (-10741123/1000000000 : ℚ) (-10732646/1000000000) := rfl
  rw [hb,r7_8]
  norm_num [Contains,intv]
private theorem r8_0 : responseBox 8 0=intv (-5262833360928973/490000000000000000 : ℚ) (-2629912144672647/245000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s8_0,s8_1]
  have hs0 : SourceActiveLaplacian.spokeSite 8 0=(8 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 8 1=(0 : Fin 11) := by decide
  rw [hs0,hs1,h8_0,h0_0]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb8_0 : Contains (RB 8 0) (responseBox 8 0) := by
  have hb : RB 8 0=intv (-10740477/1000000000 : ℚ) (-10734335/1000000000) := rfl
  rw [hb,r8_0]
  norm_num [Contains,intv]
private theorem r8_1 : responseBox 8 1=intv (-92667553358087/122500000000000000 : ℚ) (-46024548304193/61250000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s8_0,s8_1]
  have hs0 : SourceActiveLaplacian.spokeSite 8 0=(8 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 8 1=(0 : Fin 11) := by decide
  rw [hs0,hs1,h8_1,h0_1]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb8_1 : Contains (RB 8 1) (responseBox 8 1) := by
  have hb : RB 8 1=intv (-756470/1000000000 : ℚ) (-751421/1000000000) := rfl
  rw [hb,r8_1]
  norm_num [Contains,intv]
private theorem r8_2 : responseBox 8 2=intv (-85713659921863/122500000000000000 : ℚ) (-42547981993857/61250000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s8_0,s8_1]
  have hs0 : SourceActiveLaplacian.spokeSite 8 0=(8 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 8 1=(0 : Fin 11) := by decide
  rw [hs0,hs1,h8_2,h0_2]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb8_2 : Contains (RB 8 2) (responseBox 8 2) := by
  have hb : RB 8 2=intv (-699704/1000000000 : ℚ) (-694660/1000000000) := rfl
  rw [hb,r8_2]
  norm_num [Contains,intv]
private theorem r8_3 : responseBox 8 3=intv (-15758115406609/245000000000000000 : ℚ) (-7269877541851/122500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s8_0,s8_1]
  have hs0 : SourceActiveLaplacian.spokeSite 8 0=(8 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 8 1=(0 : Fin 11) := by decide
  rw [hs0,hs1,h8_3,h0_3]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb8_3 : Contains (RB 8 3) (responseBox 8 3) := by
  have hb : RB 8 3=intv (-64319/1000000000 : ℚ) (-59345/1000000000) := rfl
  rw [hb,r8_3]
  norm_num [Contains,intv]
private theorem r8_4 : responseBox 8 4=intv (-15758115406609/245000000000000000 : ℚ) (-7269877541851/122500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s8_0,s8_1]
  have hs0 : SourceActiveLaplacian.spokeSite 8 0=(8 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 8 1=(0 : Fin 11) := by decide
  rw [hs0,hs1,h8_4,h0_4]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb8_4 : Contains (RB 8 4) (responseBox 8 4) := by
  have hb : RB 8 4=intv (-64319/1000000000 : ℚ) (-59345/1000000000) := rfl
  rw [hb,r8_4]
  norm_num [Contains,intv]
private theorem r8_5 : responseBox 8 5=intv (-85713659921863/122500000000000000 : ℚ) (-42547981993857/61250000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s8_0,s8_1]
  have hs0 : SourceActiveLaplacian.spokeSite 8 0=(8 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 8 1=(0 : Fin 11) := by decide
  rw [hs0,hs1,h8_5,h0_5]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb8_5 : Contains (RB 8 5) (responseBox 8 5) := by
  have hb : RB 8 5=intv (-699704/1000000000 : ℚ) (-694660/1000000000) := rfl
  rw [hb,r8_5]
  norm_num [Contains,intv]
private theorem r8_6 : responseBox 8 6=intv (-92667553358087/122500000000000000 : ℚ) (-46024548304193/61250000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s8_0,s8_1]
  have hs0 : SourceActiveLaplacian.spokeSite 8 0=(8 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 8 1=(0 : Fin 11) := by decide
  rw [hs0,hs1,h8_6,h0_6]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb8_6 : Contains (RB 8 6) (responseBox 8 6) := by
  have hb : RB 8 6=intv (-756470/1000000000 : ℚ) (-751421/1000000000) := rfl
  rw [hb,r8_6]
  norm_num [Contains,intv]
private theorem r8_7 : responseBox 8 7=intv (-5262833360928973/490000000000000000 : ℚ) (-2629912144672647/245000000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s8_0,s8_1]
  have hs0 : SourceActiveLaplacian.spokeSite 8 0=(8 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 8 1=(0 : Fin 11) := by decide
  rw [hs0,hs1,h8_7,h0_7]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb8_7 : Contains (RB 8 7) (responseBox 8 7) := by
  have hb : RB 8 7=intv (-10740477/1000000000 : ℚ) (-10734335/1000000000) := rfl
  rw [hb,r8_7]
  norm_num [Contains,intv]
private theorem r8_8 : responseBox 8 8=intv (1500435400270531/61250000000000000 : ℚ) (3001807542143229/122500000000000000 : ℚ) := by
  simp only [responseBox,sumI,Fin.sum_univ_two,s8_0,s8_1]
  have hs0 : SourceActiveLaplacian.spokeSite 8 0=(8 : Fin 11) := rfl
  have hs1 : SourceActiveLaplacian.spokeSite 8 1=(0 : Fin 11) := by decide
  rw [hs0,hs1,h8_8,h0_8]
  norm_num [Fin.ext_iff,RatInterval.mul,RatInterval.sub,ofRat,intv]
private theorem rb8_8 : Contains (RB 8 8) (responseBox 8 8) := by
  have hb : RB 8 8=intv (24496904/1000000000 : ℚ) (24504552/1000000000) := rfl
  rw [hb,r8_8]
  norm_num [Contains,intv]
private theorem hb0_0 : Contains (HB 0 0) (offBox 0 0) := by
  have hb : HB 0 0=intv (65531665/1000000000 : ℚ) (65551627/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r0_0,r0_0,innerBox,p0_0,p0_1,p0_0,p0_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb0_1 : Contains (HB 0 1) (offBox 0 1) := by
  have hb : HB 0 1=intv (-20709459/1000000000 : ℚ) (-20697852/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r0_1,r1_0,innerBox,p0_0,p0_1,p1_0,p1_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb0_2 : Contains (HB 0 2) (offBox 0 2) := by
  have hb : HB 0 2=intv (-1936071/1000000000 : ℚ) (-1930957/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r0_2,r2_0,innerBox,p0_0,p0_1,p2_0,p2_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb0_3 : Contains (HB 0 3) (offBox 0 3) := by
  have hb : HB 0 3=intv (153906/1000000000 : ℚ) (160026/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r0_3,r3_0,innerBox,p0_0,p0_1,p3_0,p3_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb0_4 : Contains (HB 0 4) (offBox 0 4) := by
  have hb : HB 0 4=intv (277513/1000000000 : ℚ) (291019/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r0_4,r4_0,innerBox,p0_0,p0_1,p4_0,p4_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb0_5 : Contains (HB 0 5) (offBox 0 5) := by
  have hb : HB 0 5=intv (2693303/1000000000 : ℚ) (2707689/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r0_5,r5_0,innerBox,p0_0,p0_1,p5_0,p5_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb0_6 : Contains (HB 0 6) (offBox 0 6) := by
  have hb : HB 0 6=intv (1762003/1000000000 : ℚ) (1770703/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r0_6,r6_0,innerBox,p0_0,p0_1,p6_0,p6_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb0_7 : Contains (HB 0 7) (offBox 0 7) := by
  have hb : HB 0 7=intv (-384615/1000000000 : ℚ) (-383307/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r0_7,r7_0,innerBox,p0_0,p0_1,p7_0,p7_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb0_8 : Contains (HB 0 8) (offBox 0 8) := by
  have hb : HB 0 8=intv (-15804694/1000000000 : ℚ) (-15795655/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r0_8,r8_0,innerBox,p0_0,p0_1,p8_0,p8_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb1_0 : Contains (HB 1 0) (offBox 1 0) := by
  have hb : HB 1 0=intv (-20709459/1000000000 : ℚ) (-20697852/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r1_0,r0_1,innerBox,p1_0,p1_1,p0_0,p0_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb1_1 : Contains (HB 1 1) (offBox 1 1) := by
  have hb : HB 1 1=intv (77807642/1000000000 : ℚ) (77829019/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r1_1,r1_1,innerBox,p1_0,p1_1,p1_0,p1_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb1_2 : Contains (HB 1 2) (offBox 1 2) := by
  have hb : HB 1 2=intv (-29828723/1000000000 : ℚ) (-29814540/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r1_2,r2_1,innerBox,p1_0,p1_1,p2_0,p2_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb1_3 : Contains (HB 1 3) (offBox 1 3) := by
  have hb : HB 1 3=intv (-360142/1000000000 : ℚ) (-356663/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r1_3,r3_1,innerBox,p1_0,p1_1,p3_0,p3_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb1_4 : Contains (HB 1 4) (offBox 1 4) := by
  have hb : HB 1 4=intv (415567/1000000000 : ℚ) (422901/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r1_4,r4_1,innerBox,p1_0,p1_1,p4_0,p4_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb1_5 : Contains (HB 1 5) (offBox 1 5) := by
  have hb : HB 1 5=intv (4381040/1000000000 : ℚ) (4396368/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r1_5,r5_1,innerBox,p1_0,p1_1,p5_0,p5_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb1_6 : Contains (HB 1 6) (offBox 1 6) := by
  have hb : HB 1 6=intv (4218870/1000000000 : ℚ) (4234106/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r1_6,r6_1,innerBox,p1_0,p1_1,p6_0,p6_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb1_7 : Contains (HB 1 7) (offBox 1 7) := by
  have hb : HB 1 7=intv (1762003/1000000000 : ℚ) (1770703/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r1_7,r7_1,innerBox,p1_0,p1_1,p7_0,p7_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb1_8 : Contains (HB 1 8) (offBox 1 8) := by
  have hb : HB 1 8=intv (-218748/1000000000 : ℚ) (-217287/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r1_8,r8_1,innerBox,p1_0,p1_1,p8_0,p8_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb2_0 : Contains (HB 2 0) (offBox 2 0) := by
  have hb : HB 2 0=intv (-1936071/1000000000 : ℚ) (-1930957/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r2_0,r0_2,innerBox,p2_0,p2_1,p0_0,p0_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb2_1 : Contains (HB 2 1) (offBox 2 1) := by
  have hb : HB 2 1=intv (-29828723/1000000000 : ℚ) (-29814540/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r2_1,r1_2,innerBox,p2_0,p2_1,p1_0,p1_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb2_2 : Contains (HB 2 2) (offBox 2 2) := by
  have hb : HB 2 2=intv (85997055/1000000000 : ℚ) (86020257/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r2_2,r2_2,innerBox,p2_0,p2_1,p2_0,p2_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb2_3 : Contains (HB 2 3) (offBox 2 3) := by
  have hb : HB 2 3=intv (-20674489/1000000000 : ℚ) (-20663468/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r2_3,r3_2,innerBox,p2_0,p2_1,p3_0,p3_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb2_4 : Contains (HB 2 4) (offBox 2 4) := by
  have hb : HB 2 4=intv (-53313/1000000000 : ℚ) (-52902/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r2_4,r4_2,innerBox,p2_0,p2_1,p4_0,p4_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb2_5 : Contains (HB 2 5) (offBox 2 5) := by
  have hb : HB 2 5=intv (3562871/1000000000 : ℚ) (3576693/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r2_5,r5_2,innerBox,p2_0,p2_1,p5_0,p5_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb2_6 : Contains (HB 2 6) (offBox 2 6) := by
  have hb : HB 2 6=intv (4381040/1000000000 : ℚ) (4396368/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r2_6,r6_2,innerBox,p2_0,p2_1,p6_0,p6_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb2_7 : Contains (HB 2 7) (offBox 2 7) := by
  have hb : HB 2 7=intv (2693303/1000000000 : ℚ) (2707689/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r2_7,r7_2,innerBox,p2_0,p2_1,p7_0,p7_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb2_8 : Contains (HB 2 8) (offBox 2 8) := by
  have hb : HB 2 8=intv (562131/1000000000 : ℚ) (566213/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r2_8,r8_2,innerBox,p2_0,p2_1,p8_0,p8_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb3_0 : Contains (HB 3 0) (offBox 3 0) := by
  have hb : HB 3 0=intv (153906/1000000000 : ℚ) (160026/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r3_0,r0_3,innerBox,p3_0,p3_1,p0_0,p0_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb3_1 : Contains (HB 3 1) (offBox 3 1) := by
  have hb : HB 3 1=intv (-360142/1000000000 : ℚ) (-356663/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r3_1,r1_3,innerBox,p3_0,p3_1,p1_0,p1_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb3_2 : Contains (HB 3 2) (offBox 3 2) := by
  have hb : HB 3 2=intv (-20674489/1000000000 : ℚ) (-20663468/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r3_2,r2_3,innerBox,p3_0,p3_1,p2_0,p2_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb3_3 : Contains (HB 3 3) (offBox 3 3) := by
  have hb : HB 3 3=intv (60799885/1000000000 : ℚ) (60816183/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r3_3,r3_3,innerBox,p3_0,p3_1,p3_0,p3_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb3_4 : Contains (HB 3 4) (offBox 3 4) := by
  have hb : HB 3 4=intv (-19369600/1000000000 : ℚ) (-19358721/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r3_4,r4_3,innerBox,p3_0,p3_1,p4_0,p4_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb3_5 : Contains (HB 3 5) (offBox 3 5) := by
  have hb : HB 3 5=intv (-53313/1000000000 : ℚ) (-52902/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r3_5,r5_3,innerBox,p3_0,p3_1,p5_0,p5_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb3_6 : Contains (HB 3 6) (offBox 3 6) := by
  have hb : HB 3 6=intv (415567/1000000000 : ℚ) (422901/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r3_6,r6_3,innerBox,p3_0,p3_1,p6_0,p6_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb3_7 : Contains (HB 3 7) (offBox 3 7) := by
  have hb : HB 3 7=intv (277513/1000000000 : ℚ) (291019/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r3_7,r7_3,innerBox,p3_0,p3_1,p7_0,p7_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb3_8 : Contains (HB 3 8) (offBox 3 8) := by
  have hb : HB 3 8=intv (109859/1000000000 : ℚ) (119065/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r3_8,r8_3,innerBox,p3_0,p3_1,p8_0,p8_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb4_0 : Contains (HB 4 0) (offBox 4 0) := by
  have hb : HB 4 0=intv (277513/1000000000 : ℚ) (291019/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r4_0,r0_4,innerBox,p4_0,p4_1,p0_0,p0_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb4_1 : Contains (HB 4 1) (offBox 4 1) := by
  have hb : HB 4 1=intv (415567/1000000000 : ℚ) (422901/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r4_1,r1_4,innerBox,p4_0,p4_1,p1_0,p1_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb4_2 : Contains (HB 4 2) (offBox 4 2) := by
  have hb : HB 4 2=intv (-53313/1000000000 : ℚ) (-52902/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r4_2,r2_4,innerBox,p4_0,p4_1,p2_0,p2_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb4_3 : Contains (HB 4 3) (offBox 4 3) := by
  have hb : HB 4 3=intv (-19369600/1000000000 : ℚ) (-19358721/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r4_3,r3_4,innerBox,p4_0,p4_1,p3_0,p3_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb4_4 : Contains (HB 4 4) (offBox 4 4) := by
  have hb : HB 4 4=intv (60799886/1000000000 : ℚ) (60816183/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r4_4,r4_4,innerBox,p4_0,p4_1,p4_0,p4_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb4_5 : Contains (HB 4 5) (offBox 4 5) := by
  have hb : HB 4 5=intv (-20674489/1000000000 : ℚ) (-20663468/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r4_5,r5_4,innerBox,p4_0,p4_1,p5_0,p5_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb4_6 : Contains (HB 4 6) (offBox 4 6) := by
  have hb : HB 4 6=intv (-360142/1000000000 : ℚ) (-356663/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r4_6,r6_4,innerBox,p4_0,p4_1,p6_0,p6_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb4_7 : Contains (HB 4 7) (offBox 4 7) := by
  have hb : HB 4 7=intv (153906/1000000000 : ℚ) (160026/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r4_7,r7_4,innerBox,p4_0,p4_1,p7_0,p7_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb4_8 : Contains (HB 4 8) (offBox 4 8) := by
  have hb : HB 4 8=intv (109859/1000000000 : ℚ) (119065/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r4_8,r8_4,innerBox,p4_0,p4_1,p8_0,p8_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb5_0 : Contains (HB 5 0) (offBox 5 0) := by
  have hb : HB 5 0=intv (2693303/1000000000 : ℚ) (2707689/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r5_0,r0_5,innerBox,p5_0,p5_1,p0_0,p0_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb5_1 : Contains (HB 5 1) (offBox 5 1) := by
  have hb : HB 5 1=intv (4381040/1000000000 : ℚ) (4396368/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r5_1,r1_5,innerBox,p5_0,p5_1,p1_0,p1_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb5_2 : Contains (HB 5 2) (offBox 5 2) := by
  have hb : HB 5 2=intv (3562871/1000000000 : ℚ) (3576693/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r5_2,r2_5,innerBox,p5_0,p5_1,p2_0,p2_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb5_3 : Contains (HB 5 3) (offBox 5 3) := by
  have hb : HB 5 3=intv (-53313/1000000000 : ℚ) (-52902/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r5_3,r3_5,innerBox,p5_0,p5_1,p3_0,p3_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb5_4 : Contains (HB 5 4) (offBox 5 4) := by
  have hb : HB 5 4=intv (-20674489/1000000000 : ℚ) (-20663468/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r5_4,r4_5,innerBox,p5_0,p5_1,p4_0,p4_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb5_5 : Contains (HB 5 5) (offBox 5 5) := by
  have hb : HB 5 5=intv (85997055/1000000000 : ℚ) (86020257/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r5_5,r5_5,innerBox,p5_0,p5_1,p5_0,p5_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb5_6 : Contains (HB 5 6) (offBox 5 6) := by
  have hb : HB 5 6=intv (-29828723/1000000000 : ℚ) (-29814540/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r5_6,r6_5,innerBox,p5_0,p5_1,p6_0,p6_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb5_7 : Contains (HB 5 7) (offBox 5 7) := by
  have hb : HB 5 7=intv (-1936071/1000000000 : ℚ) (-1930957/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r5_7,r7_5,innerBox,p5_0,p5_1,p7_0,p7_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb5_8 : Contains (HB 5 8) (offBox 5 8) := by
  have hb : HB 5 8=intv (562131/1000000000 : ℚ) (566213/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r5_8,r8_5,innerBox,p5_0,p5_1,p8_0,p8_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb6_0 : Contains (HB 6 0) (offBox 6 0) := by
  have hb : HB 6 0=intv (1762003/1000000000 : ℚ) (1770703/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r6_0,r0_6,innerBox,p6_0,p6_1,p0_0,p0_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb6_1 : Contains (HB 6 1) (offBox 6 1) := by
  have hb : HB 6 1=intv (4218870/1000000000 : ℚ) (4234106/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r6_1,r1_6,innerBox,p6_0,p6_1,p1_0,p1_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb6_2 : Contains (HB 6 2) (offBox 6 2) := by
  have hb : HB 6 2=intv (4381040/1000000000 : ℚ) (4396368/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r6_2,r2_6,innerBox,p6_0,p6_1,p2_0,p2_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb6_3 : Contains (HB 6 3) (offBox 6 3) := by
  have hb : HB 6 3=intv (415567/1000000000 : ℚ) (422901/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r6_3,r3_6,innerBox,p6_0,p6_1,p3_0,p3_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb6_4 : Contains (HB 6 4) (offBox 6 4) := by
  have hb : HB 6 4=intv (-360142/1000000000 : ℚ) (-356663/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r6_4,r4_6,innerBox,p6_0,p6_1,p4_0,p4_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb6_5 : Contains (HB 6 5) (offBox 6 5) := by
  have hb : HB 6 5=intv (-29828723/1000000000 : ℚ) (-29814540/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r6_5,r5_6,innerBox,p6_0,p6_1,p5_0,p5_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb6_6 : Contains (HB 6 6) (offBox 6 6) := by
  have hb : HB 6 6=intv (77807642/1000000000 : ℚ) (77829019/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r6_6,r6_6,innerBox,p6_0,p6_1,p6_0,p6_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb6_7 : Contains (HB 6 7) (offBox 6 7) := by
  have hb : HB 6 7=intv (-20709459/1000000000 : ℚ) (-20697852/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r6_7,r7_6,innerBox,p6_0,p6_1,p7_0,p7_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb6_8 : Contains (HB 6 8) (offBox 6 8) := by
  have hb : HB 6 8=intv (-218748/1000000000 : ℚ) (-217287/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r6_8,r8_6,innerBox,p6_0,p6_1,p8_0,p8_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb7_0 : Contains (HB 7 0) (offBox 7 0) := by
  have hb : HB 7 0=intv (-384615/1000000000 : ℚ) (-383307/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r7_0,r0_7,innerBox,p7_0,p7_1,p0_0,p0_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb7_1 : Contains (HB 7 1) (offBox 7 1) := by
  have hb : HB 7 1=intv (1762003/1000000000 : ℚ) (1770703/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r7_1,r1_7,innerBox,p7_0,p7_1,p1_0,p1_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb7_2 : Contains (HB 7 2) (offBox 7 2) := by
  have hb : HB 7 2=intv (2693303/1000000000 : ℚ) (2707689/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r7_2,r2_7,innerBox,p7_0,p7_1,p2_0,p2_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb7_3 : Contains (HB 7 3) (offBox 7 3) := by
  have hb : HB 7 3=intv (277513/1000000000 : ℚ) (291019/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r7_3,r3_7,innerBox,p7_0,p7_1,p3_0,p3_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb7_4 : Contains (HB 7 4) (offBox 7 4) := by
  have hb : HB 7 4=intv (153906/1000000000 : ℚ) (160026/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r7_4,r4_7,innerBox,p7_0,p7_1,p4_0,p4_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb7_5 : Contains (HB 7 5) (offBox 7 5) := by
  have hb : HB 7 5=intv (-1936071/1000000000 : ℚ) (-1930957/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r7_5,r5_7,innerBox,p7_0,p7_1,p5_0,p5_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb7_6 : Contains (HB 7 6) (offBox 7 6) := by
  have hb : HB 7 6=intv (-20709459/1000000000 : ℚ) (-20697852/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r7_6,r6_7,innerBox,p7_0,p7_1,p6_0,p6_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb7_7 : Contains (HB 7 7) (offBox 7 7) := by
  have hb : HB 7 7=intv (65531665/1000000000 : ℚ) (65551627/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r7_7,r7_7,innerBox,p7_0,p7_1,p7_0,p7_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb7_8 : Contains (HB 7 8) (offBox 7 8) := by
  have hb : HB 7 8=intv (-15804694/1000000000 : ℚ) (-15795655/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r7_8,r8_7,innerBox,p7_0,p7_1,p8_0,p8_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb8_0 : Contains (HB 8 0) (offBox 8 0) := by
  have hb : HB 8 0=intv (-15804694/1000000000 : ℚ) (-15795655/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r8_0,r0_8,innerBox,p8_0,p8_1,p0_0,p0_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb8_1 : Contains (HB 8 1) (offBox 8 1) := by
  have hb : HB 8 1=intv (-218748/1000000000 : ℚ) (-217287/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r8_1,r1_8,innerBox,p8_0,p8_1,p1_0,p1_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb8_2 : Contains (HB 8 2) (offBox 8 2) := by
  have hb : HB 8 2=intv (562131/1000000000 : ℚ) (566213/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r8_2,r2_8,innerBox,p8_0,p8_1,p2_0,p2_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb8_3 : Contains (HB 8 3) (offBox 8 3) := by
  have hb : HB 8 3=intv (109859/1000000000 : ℚ) (119065/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r8_3,r3_8,innerBox,p8_0,p8_1,p3_0,p3_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb8_4 : Contains (HB 8 4) (offBox 8 4) := by
  have hb : HB 8 4=intv (109859/1000000000 : ℚ) (119065/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r8_4,r4_8,innerBox,p8_0,p8_1,p4_0,p4_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb8_5 : Contains (HB 8 5) (offBox 8 5) := by
  have hb : HB 8 5=intv (562131/1000000000 : ℚ) (566213/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r8_5,r5_8,innerBox,p8_0,p8_1,p5_0,p5_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb8_6 : Contains (HB 8 6) (offBox 8 6) := by
  have hb : HB 8 6=intv (-218748/1000000000 : ℚ) (-217287/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r8_6,r6_8,innerBox,p8_0,p8_1,p6_0,p6_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb8_7 : Contains (HB 8 7) (offBox 8 7) := by
  have hb : HB 8 7=intv (-15804694/1000000000 : ℚ) (-15795655/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r8_7,r7_8,innerBox,p8_0,p8_1,p7_0,p7_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]
private theorem hb8_8 : Contains (HB 8 8) (offBox 8 8) := by
  have hb : HB 8 8=intv (48993808/1000000000 : ℚ) (49009103/1000000000) := rfl
  simp only [offBox,symmetricResponseBox,SourceResponseLinearIntervals.intersectBox,
    hb,r8_8,r8_8,innerBox,p8_0,p8_1,p8_0,p8_1]
  norm_num [Contains,RatInterval.mul,RatInterval.add,ofRat,intv]

theorem RB_contains (k l : Fin 9) : Contains (RB k l) (responseBox k l) := by
  fin_cases k <;> fin_cases l
  · exact rb0_0
  · exact rb0_1
  · exact rb0_2
  · exact rb0_3
  · exact rb0_4
  · exact rb0_5
  · exact rb0_6
  · exact rb0_7
  · exact rb0_8
  · exact rb1_0
  · exact rb1_1
  · exact rb1_2
  · exact rb1_3
  · exact rb1_4
  · exact rb1_5
  · exact rb1_6
  · exact rb1_7
  · exact rb1_8
  · exact rb2_0
  · exact rb2_1
  · exact rb2_2
  · exact rb2_3
  · exact rb2_4
  · exact rb2_5
  · exact rb2_6
  · exact rb2_7
  · exact rb2_8
  · exact rb3_0
  · exact rb3_1
  · exact rb3_2
  · exact rb3_3
  · exact rb3_4
  · exact rb3_5
  · exact rb3_6
  · exact rb3_7
  · exact rb3_8
  · exact rb4_0
  · exact rb4_1
  · exact rb4_2
  · exact rb4_3
  · exact rb4_4
  · exact rb4_5
  · exact rb4_6
  · exact rb4_7
  · exact rb4_8
  · exact rb5_0
  · exact rb5_1
  · exact rb5_2
  · exact rb5_3
  · exact rb5_4
  · exact rb5_5
  · exact rb5_6
  · exact rb5_7
  · exact rb5_8
  · exact rb6_0
  · exact rb6_1
  · exact rb6_2
  · exact rb6_3
  · exact rb6_4
  · exact rb6_5
  · exact rb6_6
  · exact rb6_7
  · exact rb6_8
  · exact rb7_0
  · exact rb7_1
  · exact rb7_2
  · exact rb7_3
  · exact rb7_4
  · exact rb7_5
  · exact rb7_6
  · exact rb7_7
  · exact rb7_8
  · exact rb8_0
  · exact rb8_1
  · exact rb8_2
  · exact rb8_3
  · exact rb8_4
  · exact rb8_5
  · exact rb8_6
  · exact rb8_7
  · exact rb8_8

theorem RB_mem (k l : Fin 9) : (RB k l).Mem (rawResponse k l) :=
  mem_of_contains (RB_contains k l) (responseBox_mem k l)
theorem HB_contains (k l : Fin 9) : Contains (HB k l) (offBox k l) := by
  fin_cases k <;> fin_cases l
  · exact hb0_0
  · exact hb0_1
  · exact hb0_2
  · exact hb0_3
  · exact hb0_4
  · exact hb0_5
  · exact hb0_6
  · exact hb0_7
  · exact hb0_8
  · exact hb1_0
  · exact hb1_1
  · exact hb1_2
  · exact hb1_3
  · exact hb1_4
  · exact hb1_5
  · exact hb1_6
  · exact hb1_7
  · exact hb1_8
  · exact hb2_0
  · exact hb2_1
  · exact hb2_2
  · exact hb2_3
  · exact hb2_4
  · exact hb2_5
  · exact hb2_6
  · exact hb2_7
  · exact hb2_8
  · exact hb3_0
  · exact hb3_1
  · exact hb3_2
  · exact hb3_3
  · exact hb3_4
  · exact hb3_5
  · exact hb3_6
  · exact hb3_7
  · exact hb3_8
  · exact hb4_0
  · exact hb4_1
  · exact hb4_2
  · exact hb4_3
  · exact hb4_4
  · exact hb4_5
  · exact hb4_6
  · exact hb4_7
  · exact hb4_8
  · exact hb5_0
  · exact hb5_1
  · exact hb5_2
  · exact hb5_3
  · exact hb5_4
  · exact hb5_5
  · exact hb5_6
  · exact hb5_7
  · exact hb5_8
  · exact hb6_0
  · exact hb6_1
  · exact hb6_2
  · exact hb6_3
  · exact hb6_4
  · exact hb6_5
  · exact hb6_6
  · exact hb6_7
  · exact hb6_8
  · exact hb7_0
  · exact hb7_1
  · exact hb7_2
  · exact hb7_3
  · exact hb7_4
  · exact hb7_5
  · exact hb7_6
  · exact hb7_7
  · exact hb7_8
  · exact hb8_0
  · exact hb8_1
  · exact hb8_2
  · exact hb8_3
  · exact hb8_4
  · exact hb8_5
  · exact hb8_6
  · exact hb8_7
  · exact hb8_8

theorem HB_mem (k l : Fin 9) (hkl : k≠l) : (HB k l).Mem (rawH0 k l) :=
  mem_of_contains (HB_contains k l) (offBox_mem k l hkl)
end
end N11Formalization.SourceRawResponsePacket
#check @N11Formalization.SourceRawResponsePacket.RB_mem
#check @N11Formalization.SourceRawResponsePacket.HB_mem
#print axioms N11Formalization.SourceRawResponsePacket.HB_mem
