import MathGenome.Internal.Specs.D05.M09.RealComplexBridge.InnerExtension
import MathGenome.Internal.D05.M09.RealComplexBridge
import MathGenome.Internal.D05.M12.InnerProduct
import Mathlib.Tactic.Ring

/-! The real inner product extends uniquely to the prerequisite complexification.
All proofs are algebraic; no finite-dimensional or spectral result is used. -/
namespace D05.M09.RealComplexBridge.InnerExtension

open Specs.D05.M09.RealComplexBridge
open Specs.D05.M09.RealComplexBridge.Complexification
open Specs.D05.M09.RealComplexBridge.InnerExtension
open D05.M12.InnerProduct

universe u

abbrev extendedInner : Specs.D05.M09.RealComplexBridge.InnerExtension.extendedInner_type :=
  @Specs.D05.M09.RealComplexBridge.InnerExtension.extendedInner

abbrev conjugation : Specs.D05.M09.RealComplexBridge.InnerExtension.conjugation_type :=
  @Specs.D05.M09.RealComplexBridge.InnerExtension.conjugation

variable {W : Type u} [AddCommGroup W] [Module ℝ W]
variable {b : W → W → ℝ} (hb : D05.IsFirstInnerProduct b)

include hb in
private theorem b_symm (x y : W) : b x y = b y x := by
  simpa using hb.2.1 y x

include hb in
private theorem b_add (x y w : W) : b (x + y) w = b x w + b y w := by
  simpa using hb.1 1 1 x y w

include hb in
private theorem b_smul (a : ℝ) (x w : W) : b (a • x) w = a * b x w := by
  simpa using hb.1 a 0 x 0 w

include hb in
private theorem b_sub (x y w : W) : b (x - y) w = b x w - b y w := by
  simpa [sub_eq_add_neg] using hb.1 1 (-1) x y w

include hb in
private theorem b_neg (x w : W) : b (-x) w = -b x w := by
  simpa using b_smul hb (-1) x w

include hb in
private theorem b_zero (w : W) : b 0 w = 0 := (zero_of_axioms b hb w).1
include hb in
private theorem b_zero_right (w : W) : b w 0 = 0 := (zero_of_axioms b hb w).2

include hb in
private theorem b_nonneg (x : W) : 0 ≤ b x x := by
  by_cases hx : x = 0
  · subst x
    rw [b_zero hb]
  · exact (hb.2.2.2 x hx).le

include hb in
private theorem extension_linear (a c : ℂ) (z w t : Complexification W) :
    extendedInner b (a • z + c • w) t =
      a * extendedInner b z t + c * extendedInner b w t := by
  apply Complex.ext <;>
    simp [extendedInner, Specs.D05.M09.RealComplexBridge.InnerExtension.extendedInner,
      b_add hb, b_sub hb, b_smul hb] <;> ring

include hb in
private theorem extension_symmetry (z w : Complexification W) :
    extendedInner b w z = starRingEnd ℂ (extendedInner b z w) := by
  apply Complex.ext <;>
    simp [extendedInner, Specs.D05.M09.RealComplexBridge.InnerExtension.extendedInner]
  · rw [b_symm hb (re w) (re z), b_symm hb (im w) (im z)]
  · rw [b_symm hb (im w) (re z), b_symm hb (re w) (im z)]

include hb in
private theorem extension_diagonal (z : Complexification W) :
    extendedInner b z z = ((b (re z) (re z) + b (im z) (im z) : ℝ) : ℂ) := by
  simp [extendedInner, Specs.D05.M09.RealComplexBridge.InnerExtension.extendedInner,
    b_symm hb (im z) (re z)]

include hb in
private theorem diagonal_pos (z : Complexification W) (hz : z ≠ 0) :
    0 < b (re z) (re z) + b (im z) (im z) := by
  by_cases hx : re z = 0
  · have hy : im z ≠ 0 := by
      intro hy
      exact hz (D05.M09.RealComplexBridge.ext hx hy)
    exact add_pos_of_nonneg_of_pos (b_nonneg hb _) (hb.2.2.2 _ hy)
  · exact add_pos_of_pos_of_nonneg (hb.2.2.2 _ hx) (b_nonneg hb _)

theorem extension_axioms : Specs.D05.M09.RealComplexBridge.InnerExtension.extension_axioms := by
  intro W _ _ b hb
  refine ⟨extension_linear hb, extension_symmetry hb, ?_, ?_⟩
  · intro z
    change Complex.im (extendedInner b z z) = 0
    rw [extension_diagonal hb]
    rfl
  · intro z hz
    change 0 < Complex.re (extendedInner b z z)
    rw [extension_diagonal hb]
    exact diagonal_pos hb z hz

theorem extends_real : Specs.D05.M09.RealComplexBridge.InnerExtension.extends_real := by
  intro W _ _ b hb x u
  simp [Specs.D05.M09.RealComplexBridge.InnerExtension.extendedInner, re, im, pair,
    b_zero hb, b_zero_right hb]

theorem second_slot : Specs.D05.M09.RealComplexBridge.InnerExtension.second_slot := by
  intro W _ _ b hb
  exact second_slot_of_axioms _ (extension_axioms b hb)

theorem diagonal : Specs.D05.M09.RealComplexBridge.InnerExtension.diagonal := by
  intro W _ _ b hb x y
  refine ⟨extension_diagonal hb _, ?_, ?_⟩
  · constructor
    · intro hp hz
      have hx : x = 0 := congrArg re hz
      have hy : y = 0 := congrArg im hz
      subst x
      subst y
      simp [b_zero hb] at hp
    · exact diagonal_pos hb _
  · constructor
    · intro hz
      have he : b x x + b y y = 0 := by
        have := congrArg Complex.re hz
        simpa [extension_diagonal hb] using this
      have hzpair : pair x y = (0 : Complexification W) := by
        by_contra hn
        have hp := diagonal_pos hb (pair x y) hn
        exact (ne_of_gt hp) he
      exact ⟨congrArg re hzpair, congrArg im hzpair⟩
    · rintro ⟨rfl, rfl⟩
      simp [extension_diagonal hb, b_zero hb]

private theorem inner_add_left {h : Complexification W → Complexification W → ℂ}
    (hh : D05.IsFirstInnerProduct h) (z w t : Complexification W) :
    h (z + w) t = h z t + h w t := by
  simpa using hh.1 1 1 z w t

private theorem inner_smul_left {h : Complexification W → Complexification W → ℂ}
    (hh : D05.IsFirstInnerProduct h) (a : ℂ) (z w : Complexification W) :
    h (a • z) w = a * h z w := by
  simpa using hh.1 a 0 z 0 w

private theorem inner_add_right {h : Complexification W → Complexification W → ℂ}
    (hh : D05.IsFirstInnerProduct h) (z w t : Complexification W) :
    h z (w + t) = h z w + h z t := by
  simpa using second_slot_of_axioms h hh 1 1 z w t

private theorem inner_smul_right {h : Complexification W → Complexification W → ℂ}
    (hh : D05.IsFirstInnerProduct h) (a : ℂ) (z w : Complexification W) :
    h z (a • w) = starRingEnd ℂ a * h z w := by
  simpa using second_slot_of_axioms h hh a 0 z w 0

theorem forced_formula : Specs.D05.M09.RealComplexBridge.InnerExtension.forced_formula := by
  intro W _ _ b _ h hh he x y u v
  rw [real_imag_decomposition x y, real_imag_decomposition u v]
  simp only [inner_add_left hh, inner_smul_left hh,
    inner_add_right hh, inner_smul_right hh, he]
  apply Complex.ext <;> simp <;> ring

theorem unique_extension : Specs.D05.M09.RealComplexBridge.InnerExtension.unique_extension := by
  intro W _ _ b hb
  refine ⟨extendedInner b, ⟨extension_axioms b hb, extends_real b hb⟩, ?_⟩
  intro h hh
  funext z w
  exact forced_formula b hb h hh.1 hh.2 (re z) (im z) (re w) (im w)

theorem conjugation_laws : Specs.D05.M09.RealComplexBridge.InnerExtension.conjugation_laws := by
  intro W _ _ z w a
  refine ⟨?_, ?_, ?_⟩
  · apply D05.M09.RealComplexBridge.ext <;>
      simp [Specs.D05.M09.RealComplexBridge.InnerExtension.conjugation, add_comm]
  · apply D05.M09.RealComplexBridge.ext <;>
      simp [Specs.D05.M09.RealComplexBridge.InnerExtension.conjugation, add_comm]
  · apply D05.M09.RealComplexBridge.ext <;>
      simp [Specs.D05.M09.RealComplexBridge.InnerExtension.conjugation, add_comm]

theorem antiunitary : Specs.D05.M09.RealComplexBridge.InnerExtension.antiunitary := by
  intro W _ _ b hb z w
  have hn : extendedInner b (conjugation z) (conjugation w) =
      starRingEnd ℂ (extendedInner b z w) := by
    have bnr : ∀ x y, b x (-y) = - b x y := fun x y => by
      rw [b_symm hb x (-y), b_neg hb, b_symm hb y x]
    apply Complex.ext <;>
      simp [extendedInner, Specs.D05.M09.RealComplexBridge.InnerExtension.extendedInner,
        conjugation, Specs.D05.M09.RealComplexBridge.InnerExtension.conjugation,
        b_neg hb, bnr] <;> ring
  exact ⟨hn, hn.trans (extension_symmetry hb z w).symm⟩

theorem extension_core : Specs.D05.M09.RealComplexBridge.InnerExtension.extension_core := by
  intro W _ _ b hb
  obtain ⟨c, hc⟩ := (axioms_iff_core _).mp (extension_axioms b hb)
  exact ⟨c, fun z w => hc w z⟩

end D05.M09.RealComplexBridge.InnerExtension
