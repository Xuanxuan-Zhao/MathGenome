import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.SubharmonicOperations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.SubharmonicDefinition

noncomputable section
open Set Metric
open scoped BigOperators

namespace D12Complex.SubharmonicOperations

theorem subharmonicOn_const :
    Specs.D12Complex.Ch14.SubharmonicOperations.subharmonicOn_const_type := by
  intro U c hU
  apply SubharmonicDefinition.harmonicComparisonOn_subharmonicOn
    (SubharmonicDefinition.circleSubmeanOn_harmonicComparisonOn _)
  exact ⟨hU, continuousOn_const, fun a R _ _ => by rw [Real.circleAverage_const]⟩

theorem harmonicOn_subharmonicOn :
    Specs.D12Complex.Ch14.SubharmonicOperations.harmonicOn_subharmonicOn_type := by
  intro U h hh
  apply SubharmonicDefinition.harmonicComparisonOn_subharmonicOn
    (SubharmonicDefinition.circleSubmeanOn_harmonicComparisonOn _)
  exact ⟨hh.1, hh.2.1.continuousOn, fun a R hR hs =>
    (MeanValueStrongPrinciple.circle_average_eq hh hR.le hs).ge⟩

theorem subharmonicOn_add :
    Specs.D12Complex.Ch14.SubharmonicOperations.subharmonicOn_add_type := by
  intro U u v hu hv
  have hmu := SubharmonicDefinition.subharmonicOn_circleSubmeanOn hu
  have hmv := SubharmonicDefinition.subharmonicOn_circleSubmeanOn hv
  apply SubharmonicDefinition.harmonicComparisonOn_subharmonicOn
    (SubharmonicDefinition.circleSubmeanOn_harmonicComparisonOn _)
  refine ⟨hu.1, hu.2.1.add hv.2.1, ?_⟩
  intro a R hR hs
  have hsc := sphere_subset_closedBall.trans hs
  rw [Real.circleAverage_fun_add
    ((hu.2.1.mono hsc).circleIntegrable hR.le)
    ((hv.2.1.mono hsc).circleIntegrable hR.le)]
  exact add_le_add (hmu.2.2 a R hR hs) (hmv.2.2 a R hR hs)

theorem subharmonicOn_nonneg_mul :
    Specs.D12Complex.Ch14.SubharmonicOperations.subharmonicOn_nonneg_mul_type := by
  intro U u c hc hu
  have hmu := SubharmonicDefinition.subharmonicOn_circleSubmeanOn hu
  apply SubharmonicDefinition.harmonicComparisonOn_subharmonicOn
    (SubharmonicDefinition.circleSubmeanOn_harmonicComparisonOn _)
  refine ⟨hu.1, continuousOn_const.mul hu.2.1, ?_⟩
  intro a R hR hs
  have he : Real.circleAverage (fun z => c * u z) a R =
      c * Real.circleAverage u a R := by
    simpa only [smul_eq_mul] using
      (Real.circleAverage_fun_smul (a := c) (f := u) (c := a) (R := R))
  rw [he]
  exact mul_le_mul_of_nonneg_left (hmu.2.2 a R hR hs) hc

theorem subharmonicOn_nonneg_linearCombination :
    Specs.D12Complex.Ch14.SubharmonicOperations.subharmonicOn_nonneg_linearCombination_type := by
  intro ι s U c u hU hc hu
  classical
  induction s using Finset.induction_on with
  | empty => simpa using subharmonicOn_const U 0 hU
  | @insert i s hi ih =>
    have hiu := subharmonicOn_nonneg_mul U (u i) (c i)
      (hc i (Finset.mem_insert_self _ _)) (hu i (Finset.mem_insert_self _ _))
    have hsu := ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))
      (fun j hj => hu j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using subharmonicOn_add U _ _ hiu hsu

theorem subharmonicOn_max :
    Specs.D12Complex.Ch14.SubharmonicOperations.subharmonicOn_max_type := by
  intro U u v hu hv
  have hcu := (SubharmonicDefinition.subharmonicOn_iff_harmonicComparisonOn U u).mp hu
  have hcv := (SubharmonicDefinition.subharmonicOn_iff_harmonicComparisonOn U v).mp hv
  apply SubharmonicDefinition.harmonicComparisonOn_subharmonicOn
  refine ⟨hu.1, hu.2.1.sup hv.2.1, ?_⟩
  intro a R hR hs h hh hharm hb z hz
  exact max_le
    (hcu.2.2 a R hR hs h hh hharm
      (fun w hw => (le_max_left _ _).trans (hb w hw)) z hz)
    (hcv.2.2 a R hR hs h hh hharm
      (fun w hw => (le_max_right _ _).trans (hb w hw)) z hz)

theorem subharmonicOn_finset_max :
    Specs.D12Complex.Ch14.SubharmonicOperations.subharmonicOn_finset_max_type := by
  intro ι s hs U u hU hu
  apply SubharmonicDefinition.harmonicComparisonOn_subharmonicOn
  refine ⟨hU, ContinuousOn.finset_sup'_apply hs (fun i hi => (hu i hi).2.1), ?_⟩
  intro a R hR hsub h hh hharm hb z hz
  apply Finset.sup'_le
  intro i hi
  have hci := (SubharmonicDefinition.subharmonicOn_iff_harmonicComparisonOn U (u i)).mp
    (hu i hi)
  exact hci.2.2 a R hR hsub h hh hharm
    (fun w hw => (Finset.le_sup' (fun j => u j w) hi).trans (hb w hw)) z hz

theorem subharmonicOn_add_const :
    Specs.D12Complex.Ch14.SubharmonicOperations.subharmonicOn_add_const_type := by
  intro U u c hu
  exact subharmonicOn_add U u (fun _ => c) hu (subharmonicOn_const U c hu.1)

theorem subharmonicOn_sub_harmonic :
    Specs.D12Complex.Ch14.SubharmonicOperations.subharmonicOn_sub_harmonic_type := by
  intro U u h hu hh
  have hmu := SubharmonicDefinition.subharmonicOn_circleSubmeanOn hu
  apply SubharmonicDefinition.harmonicComparisonOn_subharmonicOn
    (SubharmonicDefinition.circleSubmeanOn_harmonicComparisonOn _)
  refine ⟨hu.1, hu.2.1.sub hh.2.1.continuousOn, ?_⟩
  intro a R hR hs
  have hsc := sphere_subset_closedBall.trans hs
  rw [Real.circleAverage_fun_sub
    ((hu.2.1.mono hsc).circleIntegrable hR.le)
    ((hh.2.1.continuousOn.mono hsc).circleIntegrable hR.le),
    MeanValueStrongPrinciple.circle_average_eq hh hR.le hs]
  exact sub_le_sub_right (hmu.2.2 a R hR hs) (h a)

end D12Complex.SubharmonicOperations
