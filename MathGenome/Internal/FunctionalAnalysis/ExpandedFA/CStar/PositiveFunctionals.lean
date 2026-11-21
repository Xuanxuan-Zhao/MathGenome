import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.PositiveFunctionals
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CStar.PositiveConeSquareRoots
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

noncomputable section
namespace ExpandedFA.CStar.PositiveFunctionals
universe u
open scoped ComplexOrder InnerProductSpace

abbrev nullSpace : Spec.NullSpaceType.{u} := Spec.NullSpaceValue

section Ordered
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Convert spectral positivity to the library's positive algebraic maps.
This conversion assumes no continuity. -/
def positiveMap (φ : A →ₗ[ℂ] ℂ)
    (hφ : Conventions.Spec.PositiveFunctionalValue A φ) : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ φ fun a ha => by
    have h := hφ a ((PositiveConeSquareRoots.positive_iff_nonneg a).mpr ha)
    exact Complex.nonneg_iff.mpr ⟨h.2, h.1.symm⟩

@[simp] lemma positiveMap_apply (φ : A →ₗ[ℂ] ℂ)
    (hφ : Conventions.Spec.PositiveFunctionalValue A φ) (a : A) :
    positiveMap φ hφ a = φ a := rfl

/-- The algebraic map to the separated pre-GNS space. -/
def quotientProjection (f : A →ₚ[ℂ] ℂ) :
    A →ₗ[ℂ] SeparationQuotient f.PreGNS :=
  (SeparationQuotient.mkCLM ℂ f.PreGNS).toLinearMap.comp f.toPreGNS.toLinearMap

@[simp] lemma quotientProjection_inner (f : A →ₚ[ℂ] ℂ) (a b : A) :
    ⟪quotientProjection f a, quotientProjection f b⟫_ℂ = f (star a * b) := rfl

lemma quotientProjection_eq_zero_iff (f : A →ₚ[ℂ] ℂ) (a : A) :
    quotientProjection f a = 0 ↔ f (star a * a) = 0 := by
  rw [← quotientProjection_inner]
  exact inner_self_eq_zero.symm

/-- This estimate uses positivity in the algebra, before any representation. -/
lemma preGNS_left_mul_bound (f : A →ₚ[ℂ] ℂ) (c a : A) :
    ‖f.toPreGNS (c * a)‖ ≤ ‖c‖ * ‖f.toPreGNS a‖ := by
  have hb : ‖f.leftMulMapPreGNS c‖ ≤ ‖c‖ := by
    unfold PositiveLinearMap.leftMulMapPreGNS
    exact LinearMap.mkContinuous_norm_le _ (norm_nonneg c) _
  exact (f.leftMulMapPreGNS c).le_opNorm (f.toPreGNS a) |>.trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

lemma nullSpace_eq_ker (φ : A →ₗ[ℂ] ℂ)
    (hφ : Conventions.Spec.PositiveFunctionalValue A φ) :
    nullSpace A φ = LinearMap.ker (quotientProjection (positiveMap φ hφ)) := by
  let f := positiveMap φ hφ
  have hs : {a : A | φ (star a * a) = 0} =
      (LinearMap.ker (quotientProjection f) : Set A) := by
    ext a
    exact (quotientProjection_eq_zero_iff f a).symm
  change Submodule.span ℂ _ = _
  rw [hs, Submodule.span_eq]

end Ordered

theorem schwarz : Spec.Schwarz.{u} := by
  intro A _ _ φ hφ
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  let f := positiveMap φ hφ
  have hn (a : A) : 0 ≤ f (star a * a) := f.map_nonneg (star_mul_self_nonneg a)
  refine ⟨fun a => ?_, fun a b => ?_⟩
  · have h := Complex.nonneg_iff.mp (hn a)
    exact ⟨h.2.symm, h.1⟩
  · have h := PositiveLinearMap.norm_map_star_mul_sq_le f b a
    rw [← Complex.re_eq_norm.mpr (hn b), ← Complex.re_eq_norm.mpr (hn a)] at h
    simpa only [positiveMap_apply, mul_comm, f] using h

theorem continuity_and_norm : Spec.ContinuityAndNorm.{u} := by
  intro A _ _ φ hφ
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  let f := positiveMap φ hφ
  let F : A →P[ℂ] ℂ := PositiveContinuousLinearMap.ofClass f
  have hn : (‖F.toContinuousLinearMap‖ : ℂ) = φ 1 :=
    PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one F
  have hr : ‖F.toContinuousLinearMap‖ = (φ 1).re := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re hn
  refine ⟨?_, F.toContinuousLinearMap, rfl, hn, hr, ?_⟩
  · exact F.toContinuousLinearMap.continuous
  · intro a
    rw [← hr]
    exact F.toContinuousLinearMap.le_opNorm a

theorem null_left_ideal : Spec.NullLeftIdeal.{u} := by
  intro A _ _ φ hφ
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  let f := positiveMap φ hφ
  have hm (a : A) : a ∈ nullSpace A φ ↔ quotientProjection f a = 0 := by
    rw [nullSpace_eq_ker φ hφ]
    rfl
  refine ⟨fun a => (hm a).trans (quotientProjection_eq_zero_iff f a), ?_⟩
  intro c a ha
  apply (hm (c * a)).mpr
  apply norm_eq_zero.mp
  change ‖f.toPreGNS (c * a)‖ = 0
  have hz : ‖f.toPreGNS a‖ = 0 := by
    change ‖quotientProjection f a‖ = 0
    rw [(hm a).mp ha, norm_zero]
  exact le_antisymm (by simpa only [hz, mul_zero] using preGNS_left_mul_bound f c a)
    (norm_nonneg _)

theorem quotient_form : Spec.QuotientForm.{u} := by
  intro A _ _ φ hφ
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  let f := positiveMap φ hφ
  let N := nullSpace A φ
  let q := quotientProjection f
  have hN : N = LinearMap.ker q := nullSpace_eq_ker φ hφ
  let e : Spec.NullQuotient φ →ₗ[ℂ] SeparationQuotient f.PreGNS := N.liftQ q hN.le
  have he : Function.Injective e := LinearMap.ker_eq_bot.mp
    (N.ker_liftQ_eq_bot q hN.le hN.ge)
  have he0 (x : Spec.NullQuotient φ) : e x = 0 ↔ x = 0 := by
    exact ⟨fun h => he (h.trans (map_zero e).symm), fun h => by simp [h]⟩
  let n : Seminorm ℂ (Spec.NullQuotient φ) :=
    (normSeminorm ℂ (SeparationQuotient f.PreGNS)).comp e
  refine ⟨{
    form := fun x y => ⟪e x, e y⟫_ℂ
    norm := n
    on_classes := ?_
    add_left := ?_
    add_right := ?_
    smul_left := ?_
    smul_right := ?_
    hermitian := ?_
    diagonal_nonnegative := ?_
    positive_definite := ?_
    norm_sq := ?_
    norm_eq_zero := ?_
    left_multiplication := ?_
  }⟩
  · intro a b
    rfl
  · intro x y z
    rw [map_add, inner_add_left]
  · intro x y z
    rw [map_add, inner_add_right]
  · intro r x y
    rw [map_smul, inner_smul_left]
    rfl
  · intro r x y
    rw [map_smul, inner_smul_right]
  · intro x y
    exact inner_conj_symm _ _
  · intro x
    exact ⟨inner_self_im (𝕜 := ℂ) (e x), inner_self_nonneg (𝕜 := ℂ) (x := e x)⟩
  · intro x
    rw [inner_self_eq_zero]
    exact he0 x
  · intro x
    exact norm_sq_eq_re_inner (𝕜 := ℂ) (e x)
  · intro x
    change ‖e x‖ = 0 ↔ x = 0
    rw [norm_eq_zero]
    exact he0 x
  · intro c
    have hc : N ≤ N.comap (LinearMap.mul ℂ A c) := by
      intro a ha
      exact (null_left_ideal A φ hφ).2 c a ha
    let T := N.mapQ N (LinearMap.mul ℂ A c) hc
    refine ⟨T, fun a => rfl, ?_⟩
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ a =>
      change ‖f.toPreGNS (c * a)‖ ≤ ‖c‖ * ‖f.toPreGNS a‖
      exact preGNS_left_mul_bound f c a

end ExpandedFA.CStar.PositiveFunctionals
