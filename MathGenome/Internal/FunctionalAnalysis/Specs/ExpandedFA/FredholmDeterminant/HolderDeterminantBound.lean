import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.ClassicalDefinitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The determinant and coefficient part of `fa2:p2:fredholm-holder`.
The entire order assertion is allocated to HolderEntireOrder. Constants M,H may
vanish; their nonnegativity follows from the bounds on a nondegenerate interval.
The n-th scalar coefficient is the n-th Fredholm summand evaluated at z=1. -/
open MeasureTheory
namespace ExpandedFA.FredholmDeterminant.HolderDeterminantBound.Spec

abbrev Interval (a b : ℝ) := Set.Icc a b

noncomputable def bound (a b M H α : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ ((n : ℝ) / 2) * M * H ^ (n - 1) *
    ((b - a) / ((n - 1 : ℕ) : ℝ)) ^ (α * ((n - 1 : ℕ) : ℝ))

def Bounded {a b : ℝ} (k : C(Interval a b × Interval a b, ℂ)) (M : ℝ) : Prop :=
  ∀ x y, ‖k (x,y)‖ ≤ M

def HolderSecond {a b : ℝ} (k : C(Interval a b × Interval a b, ℂ)) (H α : ℝ) : Prop :=
  ∀ x y z, ‖k (x,y) - k (x,z)‖ ≤ H * |(y : ℝ) - (z : ℝ)| ^ α

def HolderFirst {a b : ℝ} (k : C(Interval a b × Interval a b, ℂ)) (H α : ℝ) : Prop :=
  ∀ x y z, ‖k (x,z) - k (y,z)‖ ≤ H * |(x : ℝ) - (y : ℝ)| ^ α

def SecondVariableBound : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (k : C(Interval a b × Interval a b, ℂ)) (M H α : ℝ),
    0 < α → α ≤ 1 → Bounded k M → HolderSecond k H α →
    ∀ (n : ℕ), 2 ≤ n → ∀ (x y : Fin n → Interval a b),
      ‖(Matrix.of (fun i j => k (x i, y j))).det‖ ≤ bound a b M H α n

def FirstVariableBound : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (k : C(Interval a b × Interval a b, ℂ)) (M H α : ℝ),
    0 < α → α ≤ 1 → Bounded k M → HolderFirst k H α →
    ∀ (n : ℕ), 2 ≤ n → ∀ (x y : Fin n → Interval a b),
      ‖(Matrix.of (fun i j => k (x i, y j))).det‖ ≤ bound a b M H α n

def CoefficientBound : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (μ : Measure (Interval a b)) [IsFiniteMeasure μ]
    (k : C(Interval a b × Interval a b, ℂ)) (M H α : ℝ),
    0 < α → α ≤ 1 → Bounded k M → (HolderSecond k H α ∨ HolderFirst k H α) →
    ∀ (n : ℕ), 2 ≤ n →
      ‖ClassicalDefinitions.Spec.DeterminantTermValue μ k 1 n‖ ≤
        (μ.real Set.univ) ^ n / (n.factorial : ℝ) * bound a b M H α n

/-- Identifies the coefficient used in CoefficientBound with the coefficient
of z^n in the original summand, without an extra sign convention. -/
def CoefficientIdentification : Prop :=
  ∀ (a b : ℝ) (μ : Measure (Interval a b))
    (k : C(Interval a b × Interval a b, ℂ)) (z : ℂ) (n : ℕ),
    ClassicalDefinitions.Spec.DeterminantTermValue μ k z n =
      z ^ n * ClassicalDefinitions.Spec.DeterminantTermValue μ k 1 n

end ExpandedFA.FredholmDeterminant.HolderDeterminantBound.Spec
