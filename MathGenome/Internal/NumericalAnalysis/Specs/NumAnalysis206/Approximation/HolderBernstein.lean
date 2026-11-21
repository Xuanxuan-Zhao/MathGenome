import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic.Linarith

/-! Independent statements for the quantitative Bernstein step of W53,
`paper.tex`, the final paragraph of its proof (lines 2012–2023).
The continuous maps below carry the uniform norm on the indicated closed interval.
All real powers use `Real.rpow`. The definitions are canonical shared objects,
not assumed approximation or moment certificates. -/
noncomputable section
open scoped BigOperators unitInterval

namespace NumAnalysis206.HolderBernstein

/-- The algebraic Bernstein polynomial, including the harmless `n = 0` convention
in Mathlib's sampling map `bernstein.z`. -/
def unitPolynomial (n : ℕ) (f : C(I, ℝ)) : Polynomial ℝ :=
  ∑ k : Fin (n + 1), Polynomial.C (f (bernstein.z k)) * bernsteinPolynomial ℝ n k

/-- The affine parametrization of `[a,b]` by `[0,1]`. -/
def affineParam (a b : ℝ) (hab : a ≤ b) : C(I, Set.Icc a b) where
  toFun t := ⟨a + (b - a) * (t : ℝ), by
    constructor
    · have := mul_nonneg (sub_nonneg.mpr hab) t.property.1
      linarith
    · have := mul_le_mul_of_nonneg_left t.property.2 (sub_nonneg.mpr hab)
      linarith⟩
  continuous_toFun := (continuous_const.add
    (continuous_const.mul continuous_subtype_val)).subtype_mk _

/-- Pull a function on `[a,b]` back to the unit interval. -/
def pullback (a b : ℝ) (hab : a ≤ b) (f : C(Set.Icc a b, ℝ)) : C(I, ℝ) :=
  f.comp (affineParam a b hab)

/-- Normalize a point of a nondegenerate interval. -/
def normalize (a b : ℝ) (hab : a < b) : C(Set.Icc a b, I) where
  toFun x := ⟨((x : ℝ) - a) / (b - a), by
    constructor
    · exact div_nonneg (sub_nonneg.mpr x.property.1) (sub_nonneg.mpr hab.le)
    · apply (div_le_one (sub_pos.mpr hab)).2
      linarith [x.property.2]⟩
  continuous_toFun := ((continuous_subtype_val.sub continuous_const).div_const _).subtype_mk _

/-- The transported algebraic polynomial on the original interval. -/
def intervalPolynomial (a b : ℝ) (hab : a < b) (n : ℕ)
    (f : C(Set.Icc a b, ℝ)) : Polynomial ℝ :=
  (unitPolynomial n (pullback a b hab.le f)).comp
    (Polynomial.C (b - a)⁻¹ * (Polynomial.X - Polynomial.C a))

/-- Its continuous restriction to `[a,b]`. -/
def intervalApproximation (a b : ℝ) (hab : a < b) (n : ℕ)
    (f : C(Set.Icc a b, ℝ)) : C(Set.Icc a b, ℝ) :=
  (intervalPolynomial a b hab n f).toContinuousMapOn (Set.Icc a b)

end NumAnalysis206.HolderBernstein

namespace Specs.HolderBernstein
open NumAnalysis206.HolderBernstein

universe u

def weightedMoment : Prop :=
  ∀ {ι : Type u} [Fintype ι] (w d : ι → ℝ),
  (∀ i, 0 ≤ w i) → (∑ i, w i = 1) →
  ∀ {α : ℝ}, 0 < α → α ≤ 1 →
  (∑ i, w i * |d i| ^ α) ≤ (∑ i, w i * (d i) ^ 2) ^ (α / 2)

def bernsteinMoment : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ x : I, ∀ {α : ℝ}, 0 < α → α ≤ 1 →
    (∑ k : Fin (n + 1), bernstein n k x * |(x : ℝ) - bernstein.z k| ^ α)
      ≤ (4 * (n : ℝ)) ^ (-α / 2)

def pointwiseError : Prop :=
  ∀ (f : C(I, ℝ)) {α L : ℝ}, 0 < α → α ≤ 1 → 0 ≤ L →
    (∀ s t : I, |f t - f s| ≤ L * |(t : ℝ) - s| ^ α) →
    ∀ {n : ℕ}, 1 ≤ n → ∀ x : I,
    |bernsteinApproximation n f x - f x| ≤ L * (4 * (n : ℝ)) ^ (-α / 2)

def uniformError : Prop :=
  ∀ (f : C(I, ℝ)) {α L : ℝ}, 0 < α → α ≤ 1 → 0 ≤ L →
    (∀ s t : I, |f t - f s| ≤ L * |(t : ℝ) - s| ^ α) →
    ∀ {n : ℕ}, 1 ≤ n →
    ‖bernsteinApproximation n f - f‖ ≤ L * (4 * (n : ℝ)) ^ (-α / 2)

def polynomialEvaluation : Prop :=
  ∀ (n : ℕ) (f : C(I, ℝ)) (x : I),
    (unitPolynomial n f).eval (x : ℝ) = bernsteinApproximation n f x

def polynomialDegree : Prop :=
  ∀ (n : ℕ) (f : C(I, ℝ)), (unitPolynomial n f).natDegree ≤ n

def affineHolder : Prop :=
  ∀ (a b : ℝ) (hab : a < b) (f : C(Set.Icc a b, ℝ)) {α L : ℝ},
    (∀ s t : Set.Icc a b, |f t - f s| ≤ L * |(t : ℝ) - s| ^ α) →
    ∀ s t : I, |pullback a b hab.le f t - pullback a b hab.le f s| ≤
      (L * (b - a) ^ α) * |(t : ℝ) - s| ^ α

def intervalEvaluation : Prop :=
  ∀ (a b : ℝ) (hab : a < b) (n : ℕ) (f : C(Set.Icc a b, ℝ))
    (x : Set.Icc a b),
    intervalApproximation a b hab n f x =
      bernsteinApproximation n (pullback a b hab.le f) (normalize a b hab x)

def intervalDegree : Prop :=
  ∀ (a b : ℝ) (hab : a < b) (n : ℕ) (f : C(Set.Icc a b, ℝ)),
    (intervalPolynomial a b hab n f).natDegree ≤ n

def intervalUniformError : Prop :=
  ∀ (a b : ℝ) (hab : a < b) (f : C(Set.Icc a b, ℝ)) {α L : ℝ},
    0 < α → α ≤ 1 → 0 ≤ L →
    (∀ s t : Set.Icc a b, |f t - f s| ≤ L * |(t : ℝ) - s| ^ α) →
    ∀ {n : ℕ}, 1 ≤ n →
    ‖intervalApproximation a b hab n f - f‖ ≤
      (L * (b - a) ^ α) * (4 * (n : ℝ)) ^ (-α / 2)

end Specs.HolderBernstein
