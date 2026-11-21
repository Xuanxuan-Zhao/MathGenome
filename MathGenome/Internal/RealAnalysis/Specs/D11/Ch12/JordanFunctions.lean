import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.BvDefinition
import Mathlib.Analysis.Normed.Group.Real

/-! Independent statements for paper.tex, Chapter 12, Jordan decomposition.
Functions are represented on ℝ and every conclusion is restricted to [a,b].
The upstream interval-domain extension covers arbitrary functions on the subtype.
We allow a=b as well as the source's a<b. -/
namespace Specs.D11.Ch12
open Set

abbrev jordanComponent_type := (ℝ → ℝ) → ℝ → ℝ → ℝ

noncomputable def jordanPositive_value : jordanComponent_type :=
  fun F a x => ((variationFunction_value F a x).toReal + F x - F a) / 2

noncomputable def jordanNegative_value : jordanComponent_type :=
  fun F a x => ((variationFunction_value F a x).toReal - F x + F a) / 2

/-- The displayed canonical components, including monotonicity, normalization,
nonnegativity, and finite bounds. -/
def jordan_decomposition_type : Prop :=
  ∀ (F : ℝ → ℝ) {a b : ℝ}, a ≤ b → BV_value F a b →
    EqOn F (fun x => F a + jordanPositive_value F a x - jordanNegative_value F a x)
      (Icc a b) ∧
    MonotoneOn (jordanPositive_value F a) (Icc a b) ∧
    MonotoneOn (jordanNegative_value F a) (Icc a b) ∧
    jordanPositive_value F a a = 0 ∧ jordanNegative_value F a a = 0 ∧
    ∀ x ∈ Icc a b,
      0 ≤ jordanPositive_value F a x ∧
      jordanPositive_value F a x ≤ (variation_value F a b).toReal ∧
      0 ≤ jordanNegative_value F a x ∧
      jordanNegative_value F a x ≤ (variation_value F a b).toReal

/-- The real function is BV precisely when it is a difference of two bounded
nondecreasing real functions on its original compact interval. -/
def jordan_iff_type : Prop :=
  ∀ (F : ℝ → ℝ) {a b : ℝ}, a ≤ b →
    (BV_value F a b ↔ ∃ G H : ℝ → ℝ,
      MonotoneOn G (Icc a b) ∧ MonotoneOn H (Icc a b) ∧
      BddAbove (G '' Icc a b) ∧ BddBelow (G '' Icc a b) ∧
      BddAbove (H '' Icc a b) ∧ BddBelow (H '' Icc a b) ∧
      EqOn F (fun x => G x - H x) (Icc a b))

end Specs.D11.Ch12
