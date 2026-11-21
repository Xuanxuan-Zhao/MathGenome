import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.EnfloSpace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.AP.BalancedIncidenceSets
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Supplements.BanachSums
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01ExamplesComplete
import Mathlib.Topology.Metrizable.Basic

/-! The Banach space from paper.tex:12789–12825. All blocks retain the
supremum norm on continuous functions. The only infinite-sum construction is
the accepted general Banach sum with p = 2. The existence theorem supplies
actual balanced incidence data; every such choice has the asserted properties. -/

noncomputable section
open scoped ENNReal BigOperators

namespace ExpandedFA.AP.EnfloSpace

abbrev IncidenceData := Spec.IncidenceData
abbrev n := Spec.n
abbrev t := Spec.t
abbrev k := Spec.k
abbrev Row := Spec.Row
abbrev Symbol := Spec.Symbol
abbrev incident := Spec.incident
abbrev K := Spec.K
abbrev Summand := Spec.Summand
abbrev Y := Spec.Y
abbrev upperLabels := Spec.upperLabels
abbrev lowerLabels := Spec.lowerLabels
abbrev ownBlock := Spec.ownBlock
abbrev nextBlock := Spec.nextBlock
abbrev generator := Spec.generator
abbrev AllSymbols := Spec.AllSymbols
abbrev generators := Spec.generators
abbrev closedSpan := Spec.closedSpan
abbrev X := Spec.X
abbrev generatorX := Spec.generatorX

/-- No additional incidence or labelling certificate is assumed. -/
theorem data_exists : Spec.DataExists := by
  obtain ⟨offset, N, hn, hN, hs⟩ := BalancedIncidenceSets.incidence_sets_exist
  exact ⟨⟨offset, N, hn, hN, hs⟩⟩

theorem summand_finite_dimensional : Spec.SummandFiniteDimensional := by
  intro D m
  exact FiniteDimensional.of_injective (ContinuousMap.coeFnLinearMap ℝ)
    ContinuousMap.coe_injective

theorem summand_complete : Spec.SummandComplete := by
  intro D m
  infer_instance

theorem summand_sup_norm : Spec.SummandSupNorm := by
  intro D m f
  simpa only [Real.norm_eq_abs] using f.norm_eq_iSup_norm

theorem ambient_complete : Spec.AmbientComplete := by
  intro D
  exact ExpandedFA.Supplements.BanachSums.complete_power_sum (Summand D) 2 (by simp)

/-- This is the square sum of the original sup norms, including arbitrary
finite subsums. It does not arise from any Euclidean norm on a summand. -/
theorem ambient_square_norm : Spec.AmbientSquareNorm := by
  intro D y
  have h := ExpandedFA.Supplements.BanachSumDefinitions.norm_rpow_eq_sup
    (Summand D) 2 (by simp) y
  simpa [ExpandedFA.Supplements.BanachSumDefinitions.Spec.powerSum, Real.rpow_two] using h

theorem generator_own : Spec.GeneratorOwn := by
  intro D m e r a
  change (lp.single 2 m (ownBlock D m e) +
    lp.single 2 (m + 1) (nextBlock D m e)) m (r, a) = _
  rw [lp.coeFn_add, Pi.add_apply, lp.single_apply_self,
    lp.single_apply_ne 2 (m + 1) _ (by omega), add_zero]
  rfl

theorem generator_next : Spec.GeneratorNext := by
  intro D m e r a
  change (lp.single 2 m (ownBlock D m e) +
    lp.single 2 (m + 1) (nextBlock D m e)) (m + 1) (r, a) = _
  rw [lp.coeFn_add, Pi.add_apply,
    lp.single_apply_ne 2 m _ (by omega), lp.single_apply_self, zero_add]
  rfl

theorem generator_other : Spec.GeneratorOther := by
  intro D m e j hj hj'
  change (lp.single 2 m (ownBlock D m e) +
    lp.single 2 (m + 1) (nextBlock D m e)) j = _
  rw [lp.coeFn_add, Pi.add_apply, lp.single_apply_ne 2 m _ hj,
    lp.single_apply_ne 2 (m + 1) _ hj', add_zero]

theorem generators_countable : Spec.GeneratorsCountable := by
  intro D
  exact Set.countable_range _

theorem closed_span_closed : Spec.ClosedSpanClosed := by
  intro D
  exact (Submodule.span ℝ (generators D)).isClosed_topologicalClosure

theorem x_complete : Spec.XComplete := by
  intro D
  exact (closed_span_closed D).isComplete.completeSpace_coe

theorem x_banach : Spec.XBanach := by
  intro D
  exact (ExpandedFA.P1.C01Banach.isBanachSpace_iff_completeSpace (X D)).mpr (x_complete D)

/-- A countable generating set is separable, its real span is separable,
and closure preserves separability in this metric space. -/
theorem x_separable : Spec.XSeparable := by
  intro D
  have hs := ((generators_countable D).isSeparable.span (R := ℝ)).closure
  exact hs.separableSpace

/-- One actual choice of the source incidence data yields the Banach space. -/
theorem space_exists : Spec.SpaceExists := by
  obtain ⟨D⟩ := data_exists
  exact ⟨D, ambient_complete D, x_complete D, x_separable D⟩

instance (D : IncidenceData) (m : ℕ) : FiniteDimensional ℝ (Summand D m) :=
  summand_finite_dimensional D m

instance (D : IncidenceData) : TopologicalSpace.SeparableSpace (X D) :=
  x_separable D

end ExpandedFA.AP.EnfloSpace
