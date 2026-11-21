import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.RegularProblem

/-! The first two assertions of paper.tex, d13:10:separation.
Real classical solutions are ambient representatives on the actual closed
interval; within derivatives at its endpoints have the one-sided meaning.
No boundary conditions are imposed on the solutions in this proposition. -/
noncomputable section
open Set
namespace Specs.D13Unified.Ch10.Separation
open RegularProblem

abbrev derivative (P : Problem) (y : ℝ → ℝ) := derivWithin y (intervalValue P)
def flux (P : Problem) (y : ℝ → ℝ) (x : ℝ) : ℝ := P.p x * derivative P y x

/-- The original real Sturm–Liouville differential expression. -/
def expression (P : Problem) (y : ℝ → ℝ) (x : ℝ) : ℝ :=
  -derivWithin (flux P y) (intervalValue P) x + P.q x * y x

/-- The classical equation `-(p y')' + q y = λ w y` on [a,b]. -/
def IsRealSolution (P : Problem) (lam : ℝ) (y : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 y (intervalValue P) ∧
  ∀ x ∈ intervalValue P,
    expression P y x = lam * P.w x * y x

/-- Nonzero in the actual solution space, irrespective of off-interval values. -/
def Nonzero (P : Problem) (y : ℝ → ℝ) : Prop :=
  ∃ x ∈ intervalValue P, y x ≠ 0

/-- Linear independence of the restrictions as real functions on [a,b]. -/
def Independent (P : Problem) (u v : ℝ → ℝ) : Prop :=
  ∀ α β : ℝ, (∀ x ∈ intervalValue P, α * u x + β * v x = 0) → α = 0 ∧ β = 0

/-- Both zeros belong to the actual interval and no zero lies between them. -/
def ConsecutiveZeros (P : Problem) (u : ℝ → ℝ) (c d : ℝ) : Prop :=
  c ∈ intervalValue P ∧ d ∈ intervalValue P ∧ c < d ∧ u c = 0 ∧ u d = 0 ∧
  ∀ x ∈ Ioo c d, u x ≠ 0

def SimpleZeros : Prop :=
  ∀ (P : Problem) (lam : ℝ) (y : ℝ → ℝ), IsRealSolution P lam y → Nonzero P y →
    (∀ x ∈ intervalValue P, ¬(y x = 0 ∧ flux P y x = 0)) ∧
    ∀ c ∈ intervalValue P, y c = 0 →
      derivative P y c ≠ 0 ∧
      ∃ ε > 0, ∀ x ∈ intervalValue P, |x - c| < ε → y x = 0 → x = c

def EqualParameterSeparation : Prop :=
  ∀ (P : Problem) (lam : ℝ) (u v : ℝ → ℝ),
    IsRealSolution P lam u → IsRealSolution P lam v → Independent P u v →
    ∀ c d : ℝ, ConsecutiveZeros P u c d → ∃! x : ℝ, x ∈ Ioo c d ∧ v x = 0

end Specs.D13Unified.Ch10.Separation
