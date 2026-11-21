import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BoundedWeakstarDual
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.BoundedWeakstarTopology
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05NormExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.SequenceDuals
import Mathlib.LinearAlgebra.Isomorphisms

/-! The beta dual of a Banach dual is its predual. We factor a continuous
functional through c₀, extend it by Hahn–Banach, and sum its ℓ¹ coefficients
against a norm-null sequence in the original Banach space. -/

open Set Filter
open scoped Topology NNReal ENNReal

noncomputable section
namespace ExpandedFA.P1.BoundedWeakstarDual
open BoundedWeakstarTopology
open BoundedWeakstarTopology.Spec (NullSequence)
open C01SequenceSpaces

section NullSequences
variable {E : Type*} [NormedAddCommGroup E]

/-- Interlace two null sequences without combining their individual tests. -/
def interlace (x y : NullSequence E) : NullSequence E :=
  ⟨fun n => if n % 2 = 0 then x.1 (n / 2) else y.1 (n / 2), by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp x.2 ε hε
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp y.2 ε hε
    refine ⟨2 * max N M, fun n hn => ?_⟩
    have hdiv : max N M ≤ n / 2 := by omega
    change dist (if n % 2 = 0 then x.1 (n / 2) else y.1 (n / 2)) 0 < ε
    split_ifs
    · exact hN _ ((le_max_left _ _).trans hdiv)
    · exact hM _ ((le_max_right _ _).trans hdiv)⟩

lemma range_subset_interlace_left (x y : NullSequence E) :
    range x.1 ⊆ range (interlace x y).1 := by
  rintro z ⟨n, rfl⟩
  exact ⟨2 * n, by simp [interlace]⟩

lemma range_subset_interlace_right (x y : NullSequence E) :
    range y.1 ⊆ range (interlace x y).1 := by
  rintro z ⟨n, rfl⟩
  exact ⟨2 * n + 1, by simp [interlace, Nat.add_div]⟩

lemma finite_null_sequences (s : Finset (NullSequence E)) :
    ∃ x : NullSequence E, ∀ y ∈ s, range y.1 ⊆ range x.1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⟨0, tendsto_const_nhds⟩, by simp⟩
  | @insert y s hy ih =>
    obtain ⟨x, hx⟩ := ih
    refine ⟨interlace y x, ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact range_subset_interlace_left z x
    · exact (hx z hz).trans (range_subset_interlace_right y x)

end NullSequences

section Domination
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma nullSequenceSeminorm_le_of_range_subset (x y : NullSequence E)
    (h : range x.1 ⊆ range y.1) :
    nullSequenceSeminorm 𝕜 E x ≤ nullSequenceSeminorm 𝕜 E y := by
  intro f
  rw [nullSequenceSeminorm_apply]
  apply ciSup_le
  intro n
  obtain ⟨m, hm⟩ := h (mem_range_self n)
  rw [← hm]
  exact evaluation_le_nullSequenceSeminorm y f m

/-- Beta continuity gives domination by one null-sequence seminorm.
The constant can be retained in the range functional's norm bound. -/
lemma continuous_functional_bound (L : (E →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜)
    (hL : @Continuous _ _ (boundedWeakstarTopology 𝕜 E) inferInstance L) :
    ∃ (x : NullSequence E) (C : ℝ≥0),
      ∀ f, ‖L f‖ ≤ C * nullSequenceSeminorm 𝕜 E x f := by
  classical
  let : TopologicalSpace (E →L[𝕜] 𝕜) := boundedWeakstarTopology 𝕜 E
  have hp : WithSeminorms (nullSequenceSeminorm 𝕜 E) := ⟨rfl⟩
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous hp
    ((normSeminorm 𝕜 𝕜).comp L) (continuous_norm.comp hL)
  obtain ⟨x, hx⟩ := finite_null_sequences s
  have hs : s.sup (nullSequenceSeminorm 𝕜 E) ≤ nullSequenceSeminorm 𝕜 E x := by
    exact Finset.sup_le fun y hy => nullSequenceSeminorm_le_of_range_subset y x (hx y hy)
  refine ⟨x, C, fun f => (hC f).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (hs f) C.2

end Domination

section Factorization
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Test a functional on a norm-null sequence, obtaining an actual element of
our shared c₀ space with its inherited supremum norm. -/
def nullSequenceTest (x : NullSequence E) : (E →L[𝕜] 𝕜) →ₗ[𝕜] SequenceC0 𝕜 where
  toFun f :=
    ⟨⟨fun n => f (x.1 n), memℓp_infty
      ((finite_supremum 𝕜 E x f).1)⟩,
      by
        change Tendsto (fun n => f (x.1 n)) atTop (𝓝 0)
        simpa only [Function.comp_def, map_zero] using (f.continuous.tendsto 0).comp x.2⟩
  map_add' f g := rfl
  map_smul' a f := rfl

@[simp] lemma nullSequenceTest_apply (x : NullSequence E) (f : E →L[𝕜] 𝕜) (n : ℕ) :
    (nullSequenceTest (𝕜 := 𝕜) x f).val n = f (x.1 n) := rfl

lemma norm_nullSequenceTest (x : NullSequence E) (f : E →L[𝕜] 𝕜) :
    ‖nullSequenceTest (𝕜 := 𝕜) x f‖ = nullSequenceSeminorm 𝕜 E x f := by
  rw [nullSequenceSeminorm_apply]
  rfl

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- A functional dominated by the sequence seminorm factors continuously
through the range of the sequence test map, and Hahn–Banach extends the
factor to all of c₀. No closedness of that range is needed. -/
lemma c0_extension_of_bound (L : (E →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜)
    (x : NullSequence E) (C : ℝ≥0)
    (hL : ∀ f, ‖L f‖ ≤ C * nullSequenceSeminorm 𝕜 E x f) :
    ∃ v : SequenceC0 𝕜 →L[𝕜] 𝕜, ∀ f, v (nullSequenceTest x f) = L f := by
  let T : (E →L[𝕜] 𝕜) →ₗ[𝕜] SequenceC0 𝕜 := nullSequenceTest x
  have hk : T.rangeRestrict.ker ≤ L.ker := by
    intro f hf
    apply LinearMap.mem_ker.mpr
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    have ht : T f = 0 := by
      exact congrArg Subtype.val (LinearMap.mem_ker.mp hf)
    have hb := hL f
    rw [← norm_nullSequenceTest] at hb
    change ‖L f‖ ≤ C * ‖T f‖ at hb
    simpa only [ht, norm_zero, mul_zero] using hb
  let v₀ : T.range →ₗ[𝕜] 𝕜 :=
    LinearMap.liftOfSurjective (R := 𝕜) (M := E →L[𝕜] 𝕜)
      (M₂ := T.range) (M₃ := 𝕜) (f := T.rangeRestrict)
      T.surjective_rangeRestrict ⟨L, hk⟩
  have hv₀ (f : E →L[𝕜] 𝕜) : v₀ (T.rangeRestrict f) = L f :=
    LinearMap.equivOfSurjective_apply _ _
  have hvbound : ∀ y : T.range, ‖v₀ y‖ ≤ C * ‖y‖ := by
    intro y
    obtain ⟨f, rfl⟩ := T.surjective_rangeRestrict y
    rw [hv₀]
    exact (hL f).trans_eq (by rw [← norm_nullSequenceTest]; rfl)
  let v := LinearMap.mkContinuous (𝕜 := 𝕜) (𝕜₂ := 𝕜)
    (E := T.range) (F := 𝕜) v₀ C hvbound
  obtain ⟨V, hV, _⟩ := C05NormExtension.norm_preserving_extension
    𝕜 (SequenceC0 𝕜) T.range v
  refine ⟨V, fun f => ?_⟩
  exact (hV (T.rangeRestrict f)).trans (hv₀ f)

end Factorization

section Reconstruction
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E]

/-- This is an actual convergent series in E, not a formal tsum or a vector
in its completion. Completeness of E is used in the comparison test. -/
lemma summable_coefficients_nullSequence (a : SequenceLp 𝕜 1) (x : NullSequence E) :
    Summable (fun n => a n • x.1 n) := by
  have ha : Summable (fun n => ‖a n‖) := by
    simpa using (lp.memℓp a).summable (by simp)
  obtain ⟨R, hR⟩ := x.2.norm.bddAbove_range
  apply (ha.mul_right R).of_norm_bounded
  intro n
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hR (mem_range_self n)) (norm_nonneg _)

lemma exists_evaluation_of_continuous (L : (E →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜)
    (hL : @Continuous _ _ (boundedWeakstarTopology 𝕜 E) inferInstance L) :
    ∃ x : E, ∀ f : E →L[𝕜] 𝕜, L f = f x := by
  obtain ⟨x, C, hC⟩ := continuous_functional_bound L hL
  obtain ⟨v, hv⟩ := c0_extension_of_bound L x C hC
  obtain ⟨U, hU, _, _, _⟩ := FunctionSpaces.SequenceDuals.c0_duality 𝕜
  let a := U.symm v
  have ha : U a = v := U.apply_symm_apply v
  refine ⟨∑' n, a n • x.1 n, fun f => ?_⟩
  calc
    L f = v (nullSequenceTest x f) := (hv f).symm
    _ = ∑' n, a n * f (x.1 n) := by
      rw [← ha]
      exact (hU a (nullSequenceTest x f)).2
    _ = f (∑' n, a n • x.1 n) := by
      rw [f.map_tsum (summable_coefficients_nullSequence a x)]
      simp only [map_smul, smul_eq_mul]

end Reconstruction

section Evaluations
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma evaluation_continuous (x : E) :
    @Continuous (E →L[𝕜] 𝕜) 𝕜 (boundedWeakstarTopology 𝕜 E) inferInstance
      (fun f => f x) := by
  let : TopologicalSpace (E →L[𝕜] 𝕜) := boundedWeakstarTopology 𝕜 E
  have hp : WithSeminorms (nullSequenceSeminorm 𝕜 E) := ⟨rfl⟩
  let ev : (E →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜 :=
    { toFun := fun f => f x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply WithSeminorms.continuous_normedSpace_rng 𝕜 hp ev
  refine ⟨{singleSequence x}, 1, ?_⟩
  simp only [one_smul, Finset.sup_singleton]
  intro f
  exact evaluation_le_nullSequenceSeminorm (singleSequence x) f 0

lemma evaluation_unique {x y : E}
    (h : ∀ f : E →L[𝕜] 𝕜, f x = f y) : x = y := by
  obtain ⟨f, _, hf⟩ := exists_dual_vector'' 𝕜 (x - y)
  have hz : f (x - y) = 0 := by rw [map_sub, h f, sub_self]
  have hn : ‖x - y‖ = 0 := RCLike.ofReal_eq_zero.mp (hf.symm.trans hz)
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end Evaluations

/-- Full scalar-linear dual identification, including both continuity directions
and uniqueness, for every real or complex Banach space. -/
theorem continuous_dual_identification : Spec.ContinuousDualIdentification := by
  intro 𝕜 E _ _ _ _ L
  constructor
  · intro hL
    obtain ⟨x, hx⟩ := exists_evaluation_of_continuous L hL
    refine ⟨x, hx, fun y hy => ?_⟩
    exact evaluation_unique (fun f => (hy f).symm.trans (hx f))
  · rintro ⟨x, hx, _⟩
    have heq : (L : (E →L[𝕜] 𝕜) → 𝕜) = fun f => f x := funext hx
    rw [heq]
    exact evaluation_continuous x

end ExpandedFA.P1.BoundedWeakstarDual
