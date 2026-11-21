import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.PositiveConeSquareRoots
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder

noncomputable section
namespace ExpandedFA.CStar.PositiveConeSquareRoots
universe u
open scoped InnerProductSpace ComplexOrder

/-- The manuscript's spectral definition agrees with any C*-star order.
This lemma does not install a new order on an already ordered algebra. -/
lemma positive_iff_nonneg {A : Type u} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (a : A) :
    Conventions.Spec.PositiveValue A a ↔ 0 ≤ a := by
  change (IsSelfAdjoint a ∧ spectrum ℂ (a : Unitization ℂ A) ⊆
    Conventions.Spec.NonnegativeScalarsValue) ↔ 0 ≤ a
  rw [← Unitization.inr_nonneg_iff]
  constructor
  · rintro ⟨ha, hs⟩
    have ha' : IsSelfAdjoint (a : Unitization ℂ A) :=
      (Unitization.isSelfAdjoint_inr (R := ℂ)).mpr ha
    apply (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ ha').mpr
    intro r hr
    have h := hs ((ha'.coe_mem_spectrum_complex).mpr hr)
    exact h.2
  · intro ha
    refine ⟨(Unitization.isSelfAdjoint_inr (R := ℂ)).mp (.of_nonneg ha), ?_⟩
    intro z hz
    have h := spectrum_nonneg_of_nonneg ha hz
    exact ⟨h.2.symm, h.1⟩

/-- Install the spectral order only locally; no order is assumed in the statement. -/
theorem selfAdjoint_square_characterization : Spec.SelfAdjointSquareCharacterization.{u} := by
  intro A _ a
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  rw [positive_iff_nonneg]
  constructor
  · intro ha
    exact ⟨CFC.sqrt a, (CFC.sqrt_nonneg a).isSelfAdjoint,
      (CFC.sqrt_mul_sqrt_self a ha).symm⟩
  · rintro ⟨b, hb, rfl⟩
    simpa only [hb.star_eq] using star_mul_self_nonneg b

theorem star_square_characterization : Spec.StarSquareCharacterization.{u} := by
  intro A _ a
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  rw [positive_iff_nonneg]
  constructor
  · intro ha
    refine ⟨CFC.sqrt a, ?_⟩
    rw [(CFC.sqrt_nonneg a).star_eq, CFC.sqrt_mul_sqrt_self a ha]
  · rintro ⟨x, rfl⟩
    exact star_mul_self_nonneg x

theorem closed_proper_convex_cone : Spec.ClosedProperConvexCone.{u} := by
  intro A _
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  simp only [positive_iff_nonneg]
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun a b ha hb => add_nonneg ha hb
  · exact fun r a hr ha => smul_nonneg hr ha
  · exact convex_Ici (0 : A)
  · exact CStarAlgebra.isClosed_nonneg
  · intro a ha hna
    exact le_antisymm (neg_nonneg.mp hna) ha

theorem unique_positive_square_root : Spec.UniquePositiveSquareRoot.{u} := by
  intro A _ a ha
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  rw [positive_iff_nonneg] at ha
  simp only [positive_iff_nonneg]
  refine ⟨CFC.sqrt a, ⟨CFC.sqrt_nonneg a, CFC.sqrt_mul_sqrt_self a ha⟩, ?_⟩
  intro b hb
  exact (CFC.sqrt_unique hb.2 hb.1).symm

theorem operator_quadratic_characterization : Spec.OperatorQuadraticCharacterization.{u} := by
  intro H _ _ _ T
  rw [positive_iff_nonneg, ContinuousLinearMap.nonneg_iff_isPositive]
  constructor
  · intro h x
    have hx := h.inner_nonneg_right x
    exact ⟨hx.2.symm, hx.1⟩
  · intro h
    apply (ContinuousLinearMap.isPositive_iff_complex T).mpr
    intro x
    have hx := h x
    have hre : ((⟪T x, x⟫_ℂ).re : ℂ) = ⟪T x, x⟫_ℂ := by
      apply Complex.ext
      · simp
      · simp only [Complex.ofReal_im]
        change 0 = RCLike.im ⟪T x, x⟫_ℂ
        rw [inner_im_symm]
        change 0 = -(⟪x, T x⟫_ℂ).im
        rw [hx.1, neg_zero]
    exact ⟨hre, by simpa only [RCLike.re_eq_complex_re, inner_re_symm] using hx.2⟩

end ExpandedFA.CStar.PositiveConeSquareRoots
