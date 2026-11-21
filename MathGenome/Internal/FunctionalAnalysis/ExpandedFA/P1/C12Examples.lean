import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12Examples
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12Convergence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05LinfinityCounterexample
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.SequenceDuals
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.RieszRepresentation
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Three notions of convergence, and their finite-dimensional coincidence
(`fa2:p1:c12:examples`). The native ℓ² inner product is conjugate-first and
compatible with the already fixed lp norm. The ℓ∞ predual pairing is bilinear. -/

noncomputable section
open Filter
open scoped Topology ENNReal InnerProductSpace
universe u v
namespace ExpandedFA.P1.C12Examples
open C01SequenceSpaces

abbrev tailSequence : Spec.TailSequenceType.{u} := Spec.TailSequenceValue
abbrev tailWeakStarTopology : Spec.TailTopologyType.{u} := Spec.TailTopologyValue

/-- Riesz turns evaluation on the n-th unit vector into a conjugate coordinate. -/
theorem l2_unit_vectors_weak : Spec.UnitVectors.{u} := by
  intro 𝕜 _
  have hn (n : ℕ) : ‖lp.single (E := fun _ : ℕ => 𝕜) 2 n (1 : 𝕜)‖ = 1 := by
    rw [lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞)), norm_one]
  refine ⟨?_, hn, ?_⟩
  · apply (C12Convergence.weak_tendsto_iff 𝕜 (SequenceLp 𝕜 2) ℕ atTop _ 0).mpr
    intro f
    obtain ⟨y, hy, _, _⟩ := Hilbert.RieszRepresentation.functional_representation
      𝕜 (SequenceLp 𝕜 2) f
    have hc := lp_coordinates_tendsto_zero 𝕜 2 (by simp) y
    have hc' := hc.star
    simpa only [hy, lp.inner_single_right, RCLike.inner_apply', mul_one,
      inner_zero_right, star_zero, starRingEnd_apply] using hc'
  · intro h
    have he : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
      simpa only [hn, norm_zero] using h.norm
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds he)

@[simp] theorem tailSequence_apply (𝕜 : Type u) [RCLike 𝕜] (n k : ℕ) :
    tailSequence 𝕜 n k = if n ≤ k then 1 else 0 := rfl

/-- Dominated convergence for the absolutely summable bilinear pairing. -/
theorem tail_pairing_tendsto_zero (𝕜 : Type u) [RCLike 𝕜] (a : SequenceLp 𝕜 1) :
    Tendsto (fun n => ∑' k, tailSequence 𝕜 n k * a k) atTop (𝓝 0) := by
  have ha : Summable (fun k => ‖a k‖) := by
    simpa using (lp.memℓp a).summable (by simp : 0 < (1 : ℝ≥0∞).toReal)
  have h := tendsto_tsum_of_dominated_convergence
    (𝓕 := atTop) (f := fun n k => tailSequence 𝕜 n k * a k) (g := fun _ => (0 : 𝕜)) ha ?_ ?_
  · simpa using h
  · intro k
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop k] with n hn
    simp [tailSequence_apply, not_le.mpr hn]
  · apply Eventually.of_forall
    intro n k
    by_cases hnk : n ≤ k <;> simp [tailSequence_apply, hnk]

theorem tail_sequences_weakStar : Spec.TailWeakStar.{u} := by
  intro 𝕜 _
  rw [Spec.TailTopologyValue, nhds_iInf]
  simp only [tendsto_iInf, nhds_induced, tendsto_comap_iff, Function.comp_def]
  intro a
  simpa using tail_pairing_tendsto_zero 𝕜 a

/-- The fixed bilinear ℓ¹ duality realizes precisely the specified weak-star tests. -/
theorem tail_sequences_specified_predual : Spec.SpecifiedPredual.{u} := by
  intro 𝕜 _
  refine ⟨FunctionSpaces.SequenceDuals.l1Duality, fun _ _ => rfl, ?_, ?_⟩
  · rw [C12WeakStar.weakStarTopology_evaluations, induced_iInf]
    simp_rw [induced_compose]
    rfl
  · apply (C12Convergence.weakStar_tendsto_iff 𝕜 (SequenceLp 𝕜 1) ℕ atTop _ 0).mpr
    intro a
    change Tendsto (fun n => ∑' k, tailSequence 𝕜 n k * a k) atTop (𝓝 0)
    exact tail_pairing_tendsto_zero 𝕜 a

theorem tail_coordinates_tendsto_one (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    Tendsto (fun k => tailSequence 𝕜 n k) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with k hk
  simp [hk]

/-- Reuse the limit and its norm-preserving extension on the whole subspace c. -/
theorem sequence_limit_extension : Spec.LimitExtension.{u} := by
  intro 𝕜 _
  obtain ⟨lim, hlim, hnorm⟩ := C05LinfinityCounterexample.limit_functional 𝕜
  obtain ⟨L, hLnorm, hL, _, _, _⟩ :=
    C05LinfinityCounterexample.linfinity_extension_counterexample 𝕜
  refine ⟨lim, L, hnorm, hLnorm, hlim, ?_, ?_⟩
  · intro x
    obtain ⟨a, ha⟩ := x.property
    exact (hL x.val a ha).trans (hlim x a ha).symm
  · intro n
    exact hL _ 1 (tail_coordinates_tendsto_one 𝕜 n)

/-- This norm-continuous extension is a weak test constantly one on the tails. -/
theorem tail_sequences_not_weak : Spec.TailNotWeak.{u} := by
  intro 𝕜 _ h
  obtain ⟨_, L, _, _, _, _, hL⟩ := sequence_limit_extension 𝕜
  have ht := (C12Convergence.weak_tendsto_iff 𝕜 (SequenceLInfinity 𝕜) ℕ atTop _ 0).mp h L
  have ht' : Tendsto (fun _ : ℕ => (1 : 𝕜)) atTop (𝓝 0) := by
    simpa only [hL, map_zero] using ht
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht')

/-- Finite-dimensional Hausdorff vector topologies are unique. -/
theorem finite_dimensional_weak_eq_norm : Spec.WeakNormEquality.{u, v} := by
  intro 𝕜 E _ _ _ _
  let : FiniteDimensional 𝕜 (WeakSpace 𝕜 E) := (toWeakSpace 𝕜 E).finiteDimensional
  let A : E ≃L[𝕜] WeakSpace 𝕜 E := (toWeakSpace 𝕜 E).toContinuousLinearEquiv
  exact A.toHomeomorph.isInducing.eq_induced.symm

/-- Every linear functional is continuous in finite dimension. -/
theorem finrank_continuousDual (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    Module.finrank 𝕜 (E →L[𝕜] 𝕜) = Module.finrank 𝕜 E := by
  calc
    Module.finrank 𝕜 (E →L[𝕜] 𝕜) = Module.finrank 𝕜 (E →ₗ[𝕜] 𝕜) :=
      (LinearMap.toContinuousLinearMap : (E →ₗ[𝕜] 𝕜) ≃ₗ[𝕜] (E →L[𝕜] 𝕜)).finrank_eq.symm
    _ = Module.finrank 𝕜 E := Subspace.dual_finrank_eq

/-- Surjectivity of the canonical map itself follows from its dimension and separation. -/
theorem finite_dimensional_canonicalEvaluation_surjective :
    Spec.CanonicalEvaluationSurjective.{u, v} := by
  intro 𝕜 E _ _ _ _
  have hdim : Module.finrank 𝕜 E =
      Module.finrank 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) := by
    rw [finrank_continuousDual 𝕜 (E →L[𝕜] 𝕜), finrank_continuousDual 𝕜 E]
  change Function.Surjective (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E).toLinearMap
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (K := 𝕜) (V := E) (V₂ := (E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
    hdim (f := (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E).toLinearMap)).mp
  intro x y h
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).mpr
  intro f
  exact congrArg (fun Φ : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜 => Φ f) h

/-- On E′ the weak-star, weak, and norm topologies all coincide. -/
theorem finite_dimensional_dual_topologies_eq : Spec.DualTopologiesEquality.{u, v} := by
  intro 𝕜 E _ _ _ _
  refine ⟨?_, finite_dimensional_weak_eq_norm 𝕜 (E →L[𝕜] 𝕜)⟩
  rw [C12WeakStar.weakStarTopology_evaluations, C12WeakStar.dualWeakTopology_initial]
  exact (finite_dimensional_canonicalEvaluation_surjective 𝕜 E).iInf_comp
    (fun Φ : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜 => TopologicalSpace.induced Φ inferInstance)

end ExpandedFA.P1.C12Examples
