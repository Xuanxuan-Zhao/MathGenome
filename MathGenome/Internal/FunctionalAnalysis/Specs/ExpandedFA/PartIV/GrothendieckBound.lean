import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.FspaceOpenGraph
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Independent scope for the norm bounds in `fa2:p4:grothendieck-lp`,
paper.tex:19534–19565.  The a.e. quotient is Mathlib's `Lp` for every
positive exponent, including exponents below one.  Its additive-group norm
below is the p-th power of the usual quasi-norm when p < 1.  This is an
additive-group norm, not an assertion that the scalar space is normable. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

universe u
namespace ExpandedFA.PartIV.GrothendieckBound

variable {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]

/-- Exponent used for the standard translation-invariant Lp metric. -/
def metricExponent (p : ℝ≥0∞) : ℝ := if p < 1 then p.toReal else 1

/-- The extended distance to zero before taking the finite real value. -/
def lpMass (p : ℝ≥0∞) (μ : Measure X) (f : Lp V p μ) : ℝ≥0∞ :=
  eLpNorm f p μ ^ metricExponent p

lemma metricExponent_pos {p : ℝ≥0∞} (hp : 0 < p) : 0 < metricExponent p := by
  unfold metricExponent
  split_ifs with h
  · exact ENNReal.toReal_pos hp.ne' (h.trans ENNReal.one_lt_top).ne
  · exact zero_lt_one

lemma lpMass_eq_inhmg {p : ℝ≥0∞} (hp : 0 < p) (μ : Measure X)
    (f : Lp V p μ) : lpMass p μ f = inhmgELpNorm f p μ := by
  unfold lpMass metricExponent
  split_ifs with h
  · exact (inhmgELpNorm_eq_eLpNorm_pow h.le hp.ne').symm
  · rw [ENNReal.rpow_one, inhmgELpNorm_eq_eLpNorm (le_of_not_gt h)]

lemma lpMass_ne_top {p : ℝ≥0∞} (hp : 0 < p) (μ : Measure X)
    (f : Lp V p μ) : lpMass p μ f ≠ ∞ :=
  ENNReal.rpow_ne_top_of_nonneg (metricExponent_pos hp).le (Lp.eLpNorm_ne_top f)

/-- A genuine additive-group norm on Lp for every positive p. -/
def lpGroupNorm (p : ℝ≥0∞) (hp : 0 < p) (μ : Measure X) : AddGroupNorm (Lp V p μ) where
  toFun f := (lpMass p μ f).toReal
  map_zero' := by
    change (eLpNorm (0 : Lp V p μ) p μ ^ metricExponent p).toReal = 0
    rw [eLpNorm_congr_ae (Lp.coeFn_zero V p μ), eLpNorm_zero,
      ENNReal.zero_rpow_of_pos (metricExponent_pos hp), ENNReal.toReal_zero]
  neg' f := by
    simp only [lpMass, eLpNorm_congr_ae (Lp.coeFn_neg f), eLpNorm_neg]
  add_le' f g := by
    have h : lpMass p μ (f + g) ≤ lpMass p μ f + lpMass p μ g := by
      rw [lpMass_eq_inhmg hp, lpMass_eq_inhmg hp, lpMass_eq_inhmg hp]
      rw [← lpMass_eq_inhmg hp]
      have heq : inhmgELpNorm (f + g : Lp V p μ) p μ =
          inhmgELpNorm (⇑f + ⇑g) p μ := by
        rcases lt_or_ge p 1 with h | h
        · rw [inhmgELpNorm_eq_eLpNorm_pow h.le hp.ne',
            inhmgELpNorm_eq_eLpNorm_pow h.le hp.ne',
            eLpNorm_congr_ae (Lp.coeFn_add f g)]
        · rw [inhmgELpNorm_eq_eLpNorm h, inhmgELpNorm_eq_eLpNorm h,
            eLpNorm_congr_ae (Lp.coeFn_add f g)]
      rw [lpMass_eq_inhmg hp, heq]
      exact inhmgELpNorm_add_le
    exact (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨lpMass_ne_top hp μ f, lpMass_ne_top hp μ g⟩) h).trans_eq
      (ENNReal.toReal_add (lpMass_ne_top hp μ f) (lpMass_ne_top hp μ g))
  eq_zero_of_map_eq_zero' f hf := by
    have hm : lpMass p μ f = 0 :=
      (ENNReal.toReal_eq_zero_iff _).mp hf |>.resolve_right (lpMass_ne_top hp μ f)
    have hn : eLpNorm f p μ = 0 := by
      rcases ENNReal.rpow_eq_zero_iff.mp hm with h | h
      · exact h.1
      · exact False.elim ((Lp.eLpNorm_ne_top f) h.1)
    exact Lp.eq_zero_iff_ae_eq_zero.mpr ((eLpNorm_eq_zero_iff hp.ne').mp hn)

/-- The standard Lp metric, without imposing p ≥ 1. -/
def lpNormedGroup (p : ℝ≥0∞) (hp : 0 < p) (μ : Measure X) :
    NormedAddCommGroup (Lp V p μ) :=
  (lpGroupNorm p hp μ).toNormedAddCommGroup

namespace Spec

/-- Completeness in the actual metric above; no finite-measure premise is needed. -/
def PositiveLpComplete : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (𝕜 : Type*) [RCLike 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (hp : 0 < p),
    letI := lpNormedGroup (V := 𝕜) p hp μ
    CompleteSpace (Lp 𝕜 p μ)

/-- The same Lp topology and translation uniformity form an F-space. -/
def PositiveLpFSpace : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (𝕜 : Type*) [RCLike 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (hp : 0 < p),
    letI := lpNormedGroup (V := 𝕜) p hp μ
    ExpandedFA.P1.FSpace 𝕜 (Lp 𝕜 p μ)

/-- For 0 < p < 1 this is exactly the source's integral metric. -/
def FractionalMetric : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (𝕜 : Type*) [RCLike 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (hp : 0 < p), p < 1 →
    letI := lpNormedGroup (V := 𝕜) p hp μ
    ∀ f g : Lp 𝕜 p μ,
      @dist (Lp 𝕜 p μ) (lpNormedGroup p hp μ).toDist f g = (∫⁻ x, ‖f x - g x‖ₑ ^ p.toReal ∂μ).toReal

/-- The complete assigned conclusion. Essential boundedness is a property of
these a.e. classes, not of arbitrary representatives everywhere. -/
def NormBounds : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (𝕜 : Type*) [RCLike 𝕜]
    (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ≥0∞) (hp : 0 < p), p < ∞ →
    letI := lpNormedGroup (V := 𝕜) p hp μ
    ∀ E : Submodule 𝕜 (Lp 𝕜 p μ), IsClosed (E : Set (Lp 𝕜 p μ)) →
      (∀ f : E, MemLp (f : Lp 𝕜 p μ) ∞ μ) →
      ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
        (∀ f : E, (eLpNorm (f : Lp 𝕜 p μ) ∞ μ).toReal ≤
          C * (eLpNorm (f : Lp 𝕜 p μ) p μ).toReal) ∧
        (∀ f : E, MemLp (f : Lp 𝕜 p μ) 2 μ ∧
          (eLpNorm (f : Lp 𝕜 p μ) ∞ μ).toReal ≤
          A * (eLpNorm (f : Lp 𝕜 p μ) 2 μ).toReal)

end Spec
end ExpandedFA.PartIV.GrothendieckBound
