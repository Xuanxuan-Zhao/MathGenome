import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.FaithfulGNS
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CStar.CyclicGNS
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CStar.ContinuousNormalCalculus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05NormExtension
import Mathlib.Analysis.Normed.Lp.lpHolder
import Batteries.Tactic.OpenPrivate

noncomputable section
namespace ExpandedFA.CStar.FaithfulGNS
universe u v w
open scoped ComplexOrder InnerProductSpace ENNReal

attribute [local instance] Classical.propDecidable

open private ContinuousLinearMap.im_apply_eq_zero_of_tendsto_nhds_opNorm
  from Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional

/-- A spectral-calculus estimate for a single positive contraction.
This does not use order monotonicity of the norm. -/
lemma norm_one_sub_le {A : Type u} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (b : A) (hb : 0 ≤ b) (hn : ‖b‖ ≤ 1) :
    ‖1 - b‖ ≤ 1 := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simp [Subsingleton.elim (1 - b) 0]
  have hsa : IsSelfAdjoint b := hb.isSelfAdjoint
  have heq : cfc (fun x : ℝ => 1 - x) b = 1 - b := by
    rw [cfc_sub _ _ b, cfc_const_one ℝ b]
    congr 1
    exact cfc_id ℝ b
  rw [← heq]
  apply norm_cfc_le (by norm_num : (0 : ℝ) ≤ 1)
  intro x hx
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hb hx
  have hx1 : x ≤ 1 := (le_abs_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans hn)
  simpa only [Real.norm_eq_abs] using (abs_le.mpr (by constructor <;> linarith :
    -1 ≤ 1 - x ∧ 1 - x ≤ 1))

theorem norm_one_positive : Spec.NormOnePositive.{u} := by
  intro A _ f hn hu
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
/- The private library lemma proves realness from the C*-identity and a
  scalar quadratic bound. Applied to the constant approximate unit 1, it
  uses no order norm comparison or ideal/quotient theorem. -/
  have him (b : A) (hb : IsSelfAdjoint b) : (f b).im = 0 := by
    apply ContinuousLinearMap.im_apply_eq_zero_of_tendsto_nhds_opNorm (f := f) (.pure_one A) _ hb
    simpa only [hu, hn, Complex.ofReal_one] using (tendsto_pure_nhds f (1 : A))
  intro b hb
  have hb0 := (PositiveConeSquareRoots.positive_iff_nonneg b).mp hb
  refine ⟨him b hb0.isSelfAdjoint, ?_⟩
  by_cases hz : b = 0
  · simp [hz]
  have hn0 : 0 < ‖b‖ := norm_pos_iff.mpr hz
  let c : A := (‖b‖⁻¹ : ℝ) • b
  have hc0 : 0 ≤ c := smul_nonneg (inv_nonneg.mpr (norm_nonneg b)) hb0
  have hcn : ‖c‖ ≤ 1 := by simp [c, norm_smul, hz]
  have hfc : ‖1 - f c‖ ≤ 1 := by
    simpa only [← hu, ← map_sub, hn, one_mul] using
      (f.le_opNorm (1 - c)).trans (by simpa [hn] using norm_one_sub_le c hc0 hcn)
  have hre : 0 ≤ (f c).re := by
    have h := (Complex.re_le_norm (1 - f c)).trans hfc
    simp only [Complex.sub_re, Complex.one_re] at h
    linarith
  have heq : (f c).re = ‖b‖⁻¹ * (f b).re := by simp [c]
  rw [heq] at hre
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hn0)).mp hre

/-- Evaluate on C*(1,a*a) at its largest spectral value, then extend without
changing the norm. The unital norm-one criterion supplies positivity. -/
theorem norming_state : Spec.NormingState.{u} := by
  intro A _ a ha
  let : Nontrivial A := nontrivial_of_ne a 0 ha
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  let b := star a * a
  have hb : 0 ≤ b := star_mul_self_nonneg a
  let : IsStarNormal b := hb.isSelfAdjoint.isStarNormal
  have hs : (‖b‖ : ℂ) ∈ spectrum ℂ b :=
    hb.isSelfAdjoint.coe_mem_spectrum_complex.mpr
      (CStarAlgebra.norm_mem_spectrum_of_nonneg b hb)
  let χ := (StarAlgebra.elemental.characterSpaceHomeo b).symm ⟨(‖b‖ : ℂ), hs⟩
  have hχ : χ ⟨b, StarAlgebra.elemental.self_mem ℂ b⟩ = (‖b‖ : ℂ) :=
    congrArg Subtype.val ((StarAlgebra.elemental.characterSpaceHomeo b).apply_symm_apply
      ⟨(‖b‖ : ℂ), hs⟩)
  let f := (WeakDual.CharacterSpace.toAlgHom χ).toContinuousLinearMap
  have hfn : ‖f‖ = 1 := AlgHom.toContinuousLinearMap_norm _
  let M := (StarAlgebra.elemental ℂ b).toSubalgebra.toSubmodule
  obtain ⟨F, hF, hFn⟩ := P1.C05NormExtension.norm_preserving_extension ℂ A M f
  have hFone : F 1 = 1 := (hF ⟨1, (StarAlgebra.elemental ℂ b).one_mem⟩).trans
    (map_one χ)
  have hFn' : ‖F‖ = 1 := hFn.trans hfn
  refine ⟨⟨F.toLinearMap, norm_one_positive A F hFn' hFone, hFone⟩, ?_⟩
  change F b = (‖a‖ ^ 2 : ℝ)
  rw [hF ⟨b, StarAlgebra.elemental.self_mem ℂ b⟩]
  change χ ⟨b, StarAlgebra.elemental.self_mem ℂ b⟩ = _
  rw [hχ]
  congr 1
  simpa only [pow_two] using (CStarRing.norm_star_mul_self (x := a))

/-- Choose the cyclic construction for every state; the index set is not
restricted to a separating subfamily. -/
def gnsFamily (A : Type u) [CStarAlgebra A] : Spec.Family A := by
  classical
  choose H n i c r using (CyclicGNS.existence A)
  exact {
    H := H
    normed := n
    inner := i
    complete := c
    realization := fun φ => Classical.choice (r φ)
  }

/-- The bounded coordinatewise action on the Hilbert sum. -/
def sumOperator {A : Type u} [CStarAlgebra A] (F : Spec.Family A) (a : A) :
    lp F.H 2 →L[ℂ] lp F.H 2 :=
  lp.mapCLM 2 (fun φ => (F.realization φ).π a) (norm_nonneg a)
    (fun φ => (F.realization φ).norm_bound a)

@[simp] lemma sumOperator_apply {A : Type u} [CStarAlgebra A]
    (F : Spec.Family A) (a : A) (x : lp F.H 2) (φ : Conventions.Spec.StateValue A) :
    (sumOperator F a x) φ = (F.realization φ).π a (x φ) := rfl

lemma sumOperator_norm_le {A : Type u} [CStarAlgebra A] (F : Spec.Family A) (a : A) :
    ‖sumOperator F a‖ ≤ ‖a‖ :=
  lp.norm_mapCLM_le 2 _ (norm_nonneg a) _

/-- Involution is checked by summing the adjoint identities in each summand. -/
def sumRepresentation {A : Type u} [CStarAlgebra A] (F : Spec.Family A) :
    A →⋆ₐ[ℂ] (lp F.H 2 →L[ℂ] lp F.H 2) where
  toFun := sumOperator F
  map_zero' := by ext x φ; simp
  map_add' a b := by ext x φ; simp
  map_mul' a b := by ext x φ; simp
  map_one' := by ext x φ; simp
  commutes' z := by ext x φ; simp [Algebra.algebraMap_eq_smul_one]
  map_star' a := by
    change sumOperator F (star a) = ContinuousLinearMap.adjoint (sumOperator F a)
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    simp only [lp.inner_eq_tsum, sumOperator_apply]
    apply tsum_congr
    intro φ
    rw [map_star]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _

lemma sumOperator_single {A : Type u} [CStarAlgebra A] (F : Spec.Family A) (a : A)
    (φ : Conventions.Spec.StateValue A) (x : F.H φ) :
    sumOperator F a (lp.single 2 φ x) = lp.single 2 φ ((F.realization φ).π a x) := by
  classical
  ext ψ
  by_cases h : ψ = φ
  · subst ψ; simp
  · simp [Pi.single_eq_of_ne h]

/-- The cyclic-vector norm is determined by the original state's coefficient. -/
lemma cyclic_vector_norm_sq {A : Type u} [CStarAlgebra A]
    (F : Spec.Family A) (φ : Conventions.Spec.StateValue A) (a : A) :
    ‖(F.realization φ).π a (F.realization φ).ξ‖ ^ 2 = (φ.val (star a * a)).re := by
  let r := F.realization φ
  change ‖r.π a r.ξ‖ ^ 2 = _
  rw [r.vector_class, r.left_action, mul_one, norm_sq_eq_re_inner (𝕜 := ℂ), r.inner_classes]
  rfl

lemma norming_sum_vector {A : Type u} [CStarAlgebra A]
    (F : Spec.Family A) (a : A) (ha : a ≠ 0) :
    ∃ φ : Conventions.Spec.StateValue A,
      ‖sumOperator F a (lp.single 2 φ (F.realization φ).ξ)‖ = ‖a‖ := by
  classical
  obtain ⟨φ, hφ⟩ := norming_state A a ha
  refine ⟨φ, ?_⟩
  rw [sumOperator_single, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [cyclic_vector_norm_sq, hφ, Complex.ofReal_re]

lemma sumOperator_norm {A : Type u} [CStarAlgebra A] (F : Spec.Family A) (a : A) :
    ‖sumOperator F a‖ = ‖a‖ := by
  classical
  apply le_antisymm (sumOperator_norm_le F a)
  by_cases ha : a = 0
  · simp [ha]
  obtain ⟨φ, hφ⟩ := norming_sum_vector F a ha
  have hξ : ‖lp.single 2 φ (F.realization φ).ξ‖ = 1 := by
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), (F.realization φ).unit_vector]
  have h := (sumOperator F a).le_opNorm (lp.single 2 φ (F.realization φ).ξ)
  simpa only [hφ, hξ, mul_one] using h

theorem faithful_sum : Spec.FaithfulSum.{u} := by
  intro A _
  let F := gnsFamily A
  let π := sumRepresentation F
  have hn : ∀ a, ‖π a‖ = ‖a‖ := sumOperator_norm F
  have hi : Isometry π := AddMonoidHomClass.isometry_of_norm π hn
  exact ⟨F, π, sumOperator_apply F, hn, hi.injective, hi, norming_sum_vector F⟩

theorem positive_assertions : Spec.PositiveAssertions.{u} := by
  intro A _ φ hφ
  obtain (_ | _) := subsingleton_or_nontrivial A
  · have hzero : φ = 0 := by
      ext a
      rw [Subsingleton.elim a 0]
      simp
    subst φ
    exact ⟨⟨fun a => by simp, fun a b => by simp⟩,
      continuous_zero, 0, rfl, by simp, by simp, fun a => by simp⟩
  · exact ⟨PositiveFunctionals.schwarz A φ hφ,
      PositiveFunctionals.continuity_and_norm A φ hφ⟩

theorem positive_and_cyclic : Spec.PositiveAndCyclic.{u,v,w} :=
  ⟨positive_assertions, CyclicGNS.existence, CyclicGNS.uniqueness⟩

end ExpandedFA.CStar.FaithfulGNS
