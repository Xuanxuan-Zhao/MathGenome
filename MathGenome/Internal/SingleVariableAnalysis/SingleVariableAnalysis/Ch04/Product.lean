import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Peano
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Product
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Linarith

/-!
# Products, reciprocals, and quotients with real increments

K03.04.product, paper.tex:680–695. We use the proved equivalence between the
source's real-increment derivative and `HasDerivAt` over ℝ. Mathlib's product,
reciprocal, and quotient rules apply to normed real field algebras, hence to
both ℝ and ℂ without changing the differentiation field. Their precise
nonzero-value hypothesis is retained. The local denominator bound follows
from differentiability's continuity consequence and the reverse triangle
inequality with error ‖g a‖ / 2, including the base point itself.
-/

namespace SingleVariableAnalysis

universe u
variable {K : Type u} [NontriviallyNormedField K] [NormedAlgebra ℝ K]

theorem incrementDerivative_mul (f g : ℝ → K) (L M : K) (a : ℝ)
    (hf : HasRealIncrementDerivative f L a) (hg : HasRealIncrementDerivative g M a) :
    HasRealIncrementDerivative (fun x => f x * g x) (L * g a + f a * M) a := by
  apply (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mpr
  exact ((hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp hf).mul
    ((hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp hg)

theorem incrementDerivative_inv (g : ℝ → K) (M : K) (a : ℝ)
    (hg : HasRealIncrementDerivative g M a) (ha : g a ≠ 0) :
    HasRealIncrementDerivative (fun x => 1 / g x) (-M / g a ^ 2) a := by
  apply (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mpr
  simpa only [one_div] using
    ((hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp hg).fun_inv ha

theorem incrementDerivative_div (f g : ℝ → K) (L M : K) (a : ℝ)
    (hf : HasRealIncrementDerivative f L a) (hg : HasRealIncrementDerivative g M a)
    (ha : g a ≠ 0) :
    HasRealIncrementDerivative (fun x => f x / g x)
      ((L * g a - f a * M) / g a ^ 2) a := by
  apply (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mpr
  exact ((hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp hf).div
    ((hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp hg) ha

theorem deriv_mul (f g : ℝ → K) (a : ℝ)
    (hf : DifferentiableAt ℝ f a) (hg : DifferentiableAt ℝ g a) :
    deriv (fun x => f x * g x) a = deriv f a * g a + f a * deriv g a :=
  (hf.hasDerivAt.mul hg.hasDerivAt).deriv

theorem deriv_inv (g : ℝ → K) (a : ℝ) (hg : DifferentiableAt ℝ g a) (ha : g a ≠ 0) :
    deriv (fun x => 1 / g x) a = -deriv g a / g a ^ 2 := by
  simpa only [one_div] using (hg.hasDerivAt.fun_inv ha).deriv

theorem deriv_div (f g : ℝ → K) (a : ℝ)
    (hf : DifferentiableAt ℝ f a) (hg : DifferentiableAt ℝ g a) (ha : g a ≠ 0) :
    deriv (fun x => f x / g x) a =
      (deriv f a * g a - f a * deriv g a) / g a ^ 2 :=
  (hf.hasDerivAt.div hg.hasDerivAt ha).deriv

theorem incrementDerivative_local_nonzero (g : ℝ → K) (M : K) (a : ℝ)
    (hg : HasRealIncrementDerivative g M a) (ha : g a ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x - a| < δ →
      ‖g a‖ / 2 ≤ ‖g x‖ ∧ g x ≠ 0 := by
  have hp : 0 < ‖g a‖ / 2 := half_pos (norm_pos_iff.mpr ha)
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.mp
    (incrementDerivative_continuousAt g M a hg) (‖g a‖ / 2) hp
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have hclose : dist (g x) (g a) < ‖g a‖ / 2 := hb (by simpa [Real.dist_eq] using hx)
  have hreverse : ‖g a‖ - ‖g x‖ ≤ dist (g x) (g a) := by
    simpa only [dist_eq_norm, norm_sub_rev] using norm_sub_norm_le (g a) (g x)
  have hlower : ‖g a‖ / 2 ≤ ‖g x‖ := by linarith
  exact ⟨hlower, norm_pos_iff.mp (hp.trans_le hlower)⟩

theorem withinDerivative_mul (f g : ℝ → K) (L M : K) (I : Set ℝ) (a : ℝ)
    (ha : a ∈ interior I) (hf : HasRealIncrementDerivativeWithin f L I a)
    (hg : HasRealIncrementDerivativeWithin g M I a) :
    HasRealIncrementDerivativeWithin (fun x => f x * g x) (L * g a + f a * M) I a := by
  apply (withinDerivative_interior_iff _ _ I a ha).mpr
  exact ((withinDerivative_interior_iff _ _ I a ha).mp hf).mul
    ((withinDerivative_interior_iff _ _ I a ha).mp hg)

theorem withinDerivative_inv (g : ℝ → K) (M : K) (I : Set ℝ) (a : ℝ)
    (ha : a ∈ interior I) (hg : HasRealIncrementDerivativeWithin g M I a)
    (hga : g a ≠ 0) :
    HasRealIncrementDerivativeWithin (fun x => 1 / g x) (-M / g a ^ 2) I a := by
  apply (withinDerivative_interior_iff _ _ I a ha).mpr
  simpa only [one_div] using ((withinDerivative_interior_iff _ _ I a ha).mp hg).fun_inv hga

theorem withinDerivative_div (f g : ℝ → K) (L M : K) (I : Set ℝ) (a : ℝ)
    (ha : a ∈ interior I) (hf : HasRealIncrementDerivativeWithin f L I a)
    (hg : HasRealIncrementDerivativeWithin g M I a) (hga : g a ≠ 0) :
    HasRealIncrementDerivativeWithin (fun x => f x / g x)
      ((L * g a - f a * M) / g a ^ 2) I a := by
  apply (withinDerivative_interior_iff _ _ I a ha).mpr
  exact ((withinDerivative_interior_iff _ _ I a ha).mp hf).div
    ((withinDerivative_interior_iff _ _ I a ha).mp hg) hga

theorem withinDerivative_local_nonzero (g : ℝ → K) (M : K) (I : Set ℝ) (a : ℝ)
    (ha : a ∈ interior I) (hg : HasRealIncrementDerivativeWithin g M I a) (hga : g a ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ I, |x - a| < δ →
      ‖g a‖ / 2 ≤ ‖g x‖ ∧ g x ≠ 0 := by
  have hd : HasRealIncrementDerivative g M a :=
    (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mpr
      ((withinDerivative_interior_iff _ _ I a ha).mp hg)
  obtain ⟨δ, hδ, hb⟩ := incrementDerivative_local_nonzero g M a hd hga
  exact ⟨δ, hδ, fun x _ hx => hb x hx⟩

end SingleVariableAnalysis
