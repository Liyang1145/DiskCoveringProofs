import N11Formalization.C450ChainCompletion
import N11Formalization.ActualMetricClassReduction

/-! The C450 completion consumer: the chain's `h450` is checked against the
public interface type and fed to the existing seven-class main theorem. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450ChainCompletionMain

open N11Formalization

theorem h450_type_witness : C450Source11Segment.RemainingSourceObligation :=
  C450ChainCompletion.h450

theorem main_of_energy_and_seven_classes
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  ActualMetricClassReduction.main_of_seven_class_certificates
    C450ChainCompletion.h450 henergy hclasses

end N11Formalization.C450ChainCompletionMain
#check @N11Formalization.C450ChainCompletionMain.main_of_energy_and_seven_classes
#print axioms N11Formalization.C450ChainCompletionMain.main_of_energy_and_seven_classes
