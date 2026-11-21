import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch23.LittlePicard
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch23.QuantitativeBloch
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch23.AuxiliaryExcludedDisks
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PrimitivePeriodCriterion
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Tactic.LinearCombination

/-!
Little Picard, paper.tex:4199–4211.

If an entire g has nonzero derivative at a, scaled Bloch on the disk of
radius 128 / ‖g'(a)‖ produces a disk of radius two in its image. Thus an
entire auxiliary transform with the excluded-disk property has derivative
zero everywhere, and the primitive theorem makes it constant. The transform
identity makes the original function constant. An affine range normalization
handles any two distinct omitted values.
-/

noncomputable section

namespace D12Complex.LittlePicard
open Set Metric

private theorem univ_isDomain : IsDomain (univ : Set ℂ) :=
  ⟨univ_nonempty, isOpen_univ, isPreconnected_univ⟩

/-- An entire function whose image contains no radius-two disk is constant. -/
theorem constant_of_no_disk (g : ℂ → ℂ) (hg : HolomorphicOn univ g)
    (hno : ∀ c : ℂ, ¬ ball c 2 ⊆ g '' univ) :
    ∃ c : ℂ, ∀ z : ℂ, g z = c := by
  have hd : ∀ a : ℂ, deriv g a = 0 := by
    intro a
    by_contra hne
    have hnorm : 0 < ‖deriv g a‖ := norm_pos_iff.mpr hne
    let R : ℝ := 128 / ‖deriv g a‖
    have hR : 0 < R := div_pos (by norm_num) hnorm
    have hgR : HolomorphicOn (ball a R) g :=
      ⟨isOpen_ball, fun z _ => hg.2 z (mem_univ z)⟩
    obtain ⟨b, s, c, k, _, _, _, himage, _⟩ :=
      QuantitativeBloch.scaled a R g hR hgR hne
    have hradius : R * ‖deriv g a‖ / 64 = 2 := by
      dsimp [R]
      rw [div_mul_cancel₀ _ (ne_of_gt hnorm)]
      norm_num
    rw [hradius] at himage
    exact hno c (himage.trans (image_mono (subset_univ _)))
  obtain ⟨c, hc⟩ := Primitives.zero_derivative_constant univ g univ_isDomain hg
    (fun z _ => hd z)
  exact ⟨c, fun z => hc z (mem_univ z)⟩

/-- The auxiliary transform and Bloch prove constancy for omitted 0 and 1. -/
theorem omits_zero_one_constant :
    Specs.D12Complex.Ch23.LittlePicard.omits_zero_one_constant_type := by
  intro f hf hzero hone
  have hsc : IsSimplyConnected (univ : Set ℂ) := by
    apply (Homeomorph.Set.univ ℂ).toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨g, hg, hidentity, hno⟩ :=
    AuxiliaryExcludedDisks.exists_transform_no_disk univ f univ_isDomain hsc hf
      (fun z _ => hzero z) (fun z _ => hone z)
  obtain ⟨c, hc⟩ := constant_of_no_disk g hg hno
  refine ⟨-Complex.exp ((Real.pi : ℂ) * Complex.I * Complex.cosh (2 * c)), ?_⟩
  intro z
  rw [hidentity z (mem_univ z), hc z]

/-- Any two distinct omitted finite values force an entire function to be constant. -/
theorem omits_two_constant :
    Specs.D12Complex.Ch23.LittlePicard.omits_two_constant_type := by
  intro f a b hf hab ha hb
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  let F : ℂ → ℂ := fun z => (f z - a) / (b - a)
  have hF : HolomorphicOn univ F :=
    ⟨isOpen_univ, fun z hz => ((hf.2 z hz).sub_const a).div_const (b - a)⟩
  have hzero : ∀ z : ℂ, F z ≠ 0 := by
    intro z h
    exact ha z (sub_eq_zero.mp (((div_eq_zero_iff).mp h).resolve_right hba))
  have hone : ∀ z : ℂ, F z ≠ 1 := by
    intro z h
    apply hb z
    have h' := (div_eq_one_iff_eq hba).mp h
    linear_combination h'
  obtain ⟨c, hc⟩ := omits_zero_one_constant F hF hzero hone
  refine ⟨a + c * (b - a), ?_⟩
  intro z
  have h := (div_eq_iff hba).mp (hc z)
  linear_combination h

/-- A nonconstant entire function omits at most one finite complex value. -/
theorem little_picard : Specs.D12Complex.Ch23.LittlePicard.little_picard_type := by
  intro f hf hnonconstant a ha b hb
  by_contra hab
  apply hnonconstant
  exact omits_two_constant f a b hf hab
    (fun z hz => ha ⟨z, hz⟩) (fun z hz => hb ⟨z, hz⟩)

end D12Complex.LittlePicard
