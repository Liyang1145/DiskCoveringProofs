import N11Formalization.SourceStructuredIntervals

/-! Exact rational8x8 proposal; all numeric provider interfaces kernel-paid.
C is arbitrary, NOT a certified Cholesky/inverse/whitening equality. -/
set_option autoImplicit false
namespace N11Formalization.SourceStructuredCoercivityPacket
open N11Formalization RatInterval SourceStructuredIntervals
noncomputable section
-- Local evaluator stack depth only, default heartbeats/kernel unchanged.
set_option maxRecDepth 10000

def CN : Fin 8 → Fin 8 → ℤ :=
 ![![4883482,4175724,3902684,7393294,3301881,8302868,16099023,-3010967],![0,5982171,3727110,6773254,2463092,10520168,22621877,4961927],![0,0,4027190,5562605,3313270,10971583,25173644,13163982],![0,0,0,5287425,5124169,11616978,24413433,15916349],![0,0,0,0,4661828,9280818,19790346,23213619],![0,0,0,0,0,8302531,17821927,24470838],![0,0,0,0,0,0,11269767,24929594],![0,0,0,0,0,0,0,21427791]]

def TL : Fin 8 → Fin 4 → ℤ :=
 ![![5620311,6156273,8219637,4725032],![-1902193,-6663884,3497212,-2373050],![3237461,-9980226,1723524,-22284238],![-5661740,-5940449,-21639013,-9355595],![-8299445,-19378737,481787,-1485284],![-4429196,-10393292,-5652704,-9842426],![-13485769,-16299204,-5012945,-8828208],![-657524,19722880,14973207,28863636]]

def TH : Fin 8 → Fin 4 → ℤ :=
 ![![5625039,6162061,8224483,4730395],![-1892616,-6652163,3507032,-2362183],![3247297,-9968191,1733604,-22273082],![-5641762,-5916013,-21618532,-9332924],![-8283448,-19359166,498212,-1467129],![-4381500,-10334911,-5603744,-9788283],![-13374003,-16162388,-4898200,-8701313],![-545606,19859963,15088211,28990765]]

def QL : Fin 8 → Fin 8 → ℤ :=
 ![![998980725,-890540,-854043,-1473226,-800815,-1626636,-3495342,-5748805],![-890540,998068724,-1439268,-2378219,-1144675,-2220607,-4155010,-7667284],![-854043,-1439268,998144818,-2819327,-1614301,-3533764,-7033081,-9152312],![-1473226,-2378219,-2819327,994915864,-2805737,-5960363,-11368800,-14461429],![-800815,-1144675,-1614301,-2805737,997825438,-4300995,-8313833,-8587124],![-1626636,-2220607,-3533764,-5960363,-4300995,989660617,-18143840,-15554017],![-3495342,-4155010,-7033081,-11368800,-8313833,-18143840,965040705,-28814415],![-5748805,-7667284,-9152312,-14461429,-8587124,-15554017,-28814415,951729773]]

def QH : Fin 8 → Fin 8 → ℤ :=
 ![![1001019007,890392,854296,1472732,800746,1625781,3493279,5749890],![890392,1001931845,1439466,2378642,1145279,2221618,4157473,7666668],![854296,1439466,1001855236,2819298,1615009,3533748,7033507,9149998],![1472732,2378642,2819298,1005085581,2806253,5963733,11376590,14456573],![800746,1145279,1615009,2806253,1002175378,4302617,8317538,8586320],![1625781,2221618,3533748,5963733,4302617,1010347527,18162602,15542916],![3493279,4157473,7033507,11376590,8317538,18162602,1035003856,28788381],![5749890,7666668,9149998,14456573,8586320,15542916,28788381,1048314706]]

def C : Matrix (Fin 8) (Fin 8) ℚ := fun i j => (CN i j : ℚ)/1000000
def TB (i : Fin 8) (a : Fin 4) : RatInterval :=
  intv ((TL i a : ℚ)/1000000000) ((TH i a : ℚ)/1000000000)
def QB (i j : Fin 8) : RatInterval :=
  intv ((QL i j : ℚ)/1000000000) ((QH i j : ℚ)/1000000000)

private theorem trow0 (a : Fin 4) : Contains (TB 0 a) (TInput C 0 a) := by
  fin_cases a <;> unfold Contains <;> decide +kernel
private theorem trow1 (a : Fin 4) : Contains (TB 1 a) (TInput C 1 a) := by
  fin_cases a <;> unfold Contains <;> decide +kernel
private theorem trow2 (a : Fin 4) : Contains (TB 2 a) (TInput C 2 a) := by
  fin_cases a <;> unfold Contains <;> decide +kernel
private theorem trow3 (a : Fin 4) : Contains (TB 3 a) (TInput C 3 a) := by
  fin_cases a <;> unfold Contains <;> decide +kernel
private theorem trow4 (a : Fin 4) : Contains (TB 4 a) (TInput C 4 a) := by
  fin_cases a <;> unfold Contains <;> decide +kernel
private theorem trow5 (a : Fin 4) : Contains (TB 5 a) (TInput C 5 a) := by
  fin_cases a <;> unfold Contains <;> decide +kernel
private theorem trow6 (a : Fin 4) : Contains (TB 6 a) (TInput C 6 a) := by
  fin_cases a <;> unfold Contains <;> decide +kernel
private theorem trow7 (a : Fin 4) : Contains (TB 7 a) (TInput C 7 a) := by
  fin_cases a <;> unfold Contains <;> decide +kernel

theorem T_contains (i : Fin 8) (a : Fin 4) : Contains (TB i a) (TInput C i a) := by
  fin_cases i
  · exact trow0 a
  · exact trow1 a
  · exact trow2 a
  · exact trow3 a
  · exact trow4 a
  · exact trow5 a
  · exact trow6 a
  · exact trow7 a
private theorem qrow0 (j : Fin 8) : Contains (QB 0 j) (structuredBox C TB 0 j) := by
  fin_cases j <;> unfold Contains <;> decide +kernel
private theorem qrow1 (j : Fin 8) : Contains (QB 1 j) (structuredBox C TB 1 j) := by
  fin_cases j <;> unfold Contains <;> decide +kernel
private theorem qrow2 (j : Fin 8) : Contains (QB 2 j) (structuredBox C TB 2 j) := by
  fin_cases j <;> unfold Contains <;> decide +kernel
private theorem qrow3 (j : Fin 8) : Contains (QB 3 j) (structuredBox C TB 3 j) := by
  fin_cases j <;> unfold Contains <;> decide +kernel
private theorem qrow4 (j : Fin 8) : Contains (QB 4 j) (structuredBox C TB 4 j) := by
  fin_cases j <;> unfold Contains <;> decide +kernel
private theorem qrow5 (j : Fin 8) : Contains (QB 5 j) (structuredBox C TB 5 j) := by
  fin_cases j <;> unfold Contains <;> decide +kernel
private theorem qrow6 (j : Fin 8) : Contains (QB 6 j) (structuredBox C TB 6 j) := by
  fin_cases j <;> unfold Contains <;> decide +kernel
private theorem qrow7 (j : Fin 8) : Contains (QB 7 j) (structuredBox C TB 7 j) := by
  fin_cases j <;> unfold Contains <;> decide +kernel

theorem Q_contains (i j : Fin 8) : Contains (QB i j) (structuredBox C TB i j) := by
  fin_cases i
  · exact qrow0 j
  · exact qrow1 j
  · exact qrow2 j
  · exact qrow3 j
  · exact qrow4 j
  · exact qrow5 j
  · exact qrow6 j
  · exact qrow7 j
private theorem strict0 : (1/2 : ℚ)+
    (∑ j : Fin 8,if j=(0 : Fin 8) then 0 else (QB 0 j).abs.hi)≤(QB 0 0).lo := by
  decide +kernel
private theorem strict1 : (1/2 : ℚ)+
    (∑ j : Fin 8,if j=(1 : Fin 8) then 0 else (QB 1 j).abs.hi)≤(QB 1 1).lo := by
  decide +kernel
private theorem strict2 : (1/2 : ℚ)+
    (∑ j : Fin 8,if j=(2 : Fin 8) then 0 else (QB 2 j).abs.hi)≤(QB 2 2).lo := by
  decide +kernel
private theorem strict3 : (1/2 : ℚ)+
    (∑ j : Fin 8,if j=(3 : Fin 8) then 0 else (QB 3 j).abs.hi)≤(QB 3 3).lo := by
  decide +kernel
private theorem strict4 : (1/2 : ℚ)+
    (∑ j : Fin 8,if j=(4 : Fin 8) then 0 else (QB 4 j).abs.hi)≤(QB 4 4).lo := by
  decide +kernel
private theorem strict5 : (1/2 : ℚ)+
    (∑ j : Fin 8,if j=(5 : Fin 8) then 0 else (QB 5 j).abs.hi)≤(QB 5 5).lo := by
  decide +kernel
private theorem strict6 : (1/2 : ℚ)+
    (∑ j : Fin 8,if j=(6 : Fin 8) then 0 else (QB 6 j).abs.hi)≤(QB 6 6).lo := by
  decide +kernel
private theorem strict7 : (1/2 : ℚ)+
    (∑ j : Fin 8,if j=(7 : Fin 8) then 0 else (QB 7 j).abs.hi)≤(QB 7 7).lo := by
  decide +kernel

theorem strict_rows (i : Fin 8) : (1/2 : ℚ)+
    (∑ j : Fin 8,if j=i then 0 else (QB i j).abs.hi)≤(QB i i).lo := by
  fin_cases i
  · exact strict0
  · exact strict1
  · exact strict2
  · exact strict3
  · exact strict4
  · exact strict5
  · exact strict6
  · exact strict7

/-- SAME actualmu9/5000 coercivity, all source and numeric providers discharged.
This is a pinned source quadratic theorem, NOT local/global covering optimality. -/
theorem actual_coercivity (x : Fin 8 → ℝ) :
    (9/5000 : ℝ)*(∑ i : Fin 8,x i^2)≤
      (∑ i : Fin 8,∑ j : Fin 8,SourceRawResponseIntervals.rawH0 i.castSucc j.castSucc*x i*x j)+
        1468*(∑ a : Fin 4,(∑ i : Fin 8,rawG i.castSucc a*x i)^2) :=
  coercivity_of_certificate C TB QB T_contains Q_contains strict_rows x

end
end N11Formalization.SourceStructuredCoercivityPacket
#check @N11Formalization.SourceStructuredCoercivityPacket.T_contains
#check @N11Formalization.SourceStructuredCoercivityPacket.Q_contains
#check @N11Formalization.SourceStructuredCoercivityPacket.strict_rows
#check @N11Formalization.SourceStructuredCoercivityPacket.actual_coercivity
#print axioms N11Formalization.SourceStructuredCoercivityPacket.actual_coercivity
