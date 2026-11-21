import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.Conventions
import Mathlib.Analysis.Convex.Basic

/-!
Independent statements for the noncircular positivity stage of
`fa2:p2:cstar-positive` (paper.tex:12235–12280).

All algebras are complex and may be nonunital or zero. `PositiveValue` is
self-adjointness and nonnegative complex spectrum in the C*-unitization,
with precisely the original norm and involution. A square is written `b * b`
to cover nonunital algebras. Convexity and cone scalars are real. The operator
criterion uses the full complex quadratic value, so it requires both its
imaginary part to vanish and its real part to be nonnegative. No normality,
separability, nonzero-space, representation or order estimate is assumed.
-/

namespace ExpandedFA.CStar.PositiveConeSquareRoots.Spec
universe u
open Conventions.Spec
open scoped InnerProductSpace

def SelfAdjointSquareCharacterization : Prop :=
  ∀ (A : Type u) [NonUnitalCStarAlgebra A] (a : A),
    PositiveValue A a ↔ ∃ b : A, IsSelfAdjoint b ∧ a = b * b

def StarSquareCharacterization : Prop :=
  ∀ (A : Type u) [NonUnitalCStarAlgebra A] (a : A),
    PositiveValue A a ↔ ∃ x : A, a = star x * x

/-- Closedness is in the given norm topology, and properness includes zero. -/
def ClosedProperConvexCone : Prop :=
  ∀ (A : Type u) [NonUnitalCStarAlgebra A],
    PositiveValue A 0 ∧
    (∀ a b : A, PositiveValue A a → PositiveValue A b → PositiveValue A (a + b)) ∧
    (∀ (r : ℝ) (a : A), 0 ≤ r → PositiveValue A a → PositiveValue A (r • a)) ∧
    Convex ℝ {a : A | PositiveValue A a} ∧
    IsClosed {a : A | PositiveValue A a} ∧
    (∀ a : A, PositiveValue A a → PositiveValue A (-a) → a = 0)

def UniquePositiveSquareRoot : Prop :=
  ∀ (A : Type u) [NonUnitalCStarAlgebra A] (a : A),
    PositiveValue A a → ∃! b : A, PositiveValue A b ∧ b * b = a

def OperatorQuadraticCharacterization : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H),
    PositiveValue (H →L[ℂ] H) T ↔
      ∀ x : H, ⟪x, T x⟫_ℂ ∈ NonnegativeScalarsValue

end ExpandedFA.CStar.PositiveConeSquareRoots.Spec
