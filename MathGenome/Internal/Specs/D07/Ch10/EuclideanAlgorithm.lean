import MathGenome.Internal.Specs.D07.Ch10.EuclideanDefinition
import MathGenome.Internal.Specs.D07.Ch10.GcdLcm

/-!
Independent specification of K07.10.euclidean_algorithm (paper.tex:1890–1913).
The ring is a commutative nontrivial domain. Division data have exactly the
well-founded relation and division properties of the source, with no stronger
multiplicative size axiom and no uniqueness assumption.
-/

universe u

namespace Specs.D07.Ch10.EuclideanAlgorithm

open Specs.D07.Ch10.EuclideanDefinition Specs.D07.Ch10.GcdLcm

/-- A finite execution of valid Euclidean divisions. The arguments are the current
pair, the terminal remainder, and the number of divisions. A terminal pair is
`(g, 0)`, so `g` is literally the remainder preceding the final zero.
Quotients may be chosen independently at every step.
The case `(0, 0)` has the explicitly stipulated output zero. -/
inductive DivisionRun {R : Type u} [CommRing R] [IsDomain R] (d : EuclideanData R) :
    R → R → R → ℕ → Prop where
  | stop (a : R) : DivisionRun d a 0 a 0
  | step {a b q r g : R} {n : ℕ} (hb : b ≠ 0)
      (division : a = q * b + r) (decrease : r = 0 ∨ d.smaller r b)
      (tail : DivisionRun d b r g n) : DivisionRun d a b g (n + 1)

/-- Every input pair has a finite execution, for every choice of division data. -/
def AlgorithmTerminates : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (d : EuclideanData R) (a b : R),
    ∃ g n, DivisionRun d a b g n

/-- Even when different valid quotients are chosen at different stages, an
infinite sequence of divisions must encounter a divisor equal to zero. Here `s 0` and
`s 1` are the initial inputs and `s (n+2)` is the next remainder. -/
def NoInfiniteDivisions : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (d : EuclideanData R) (s : ℕ → R),
    (∀ n, s (n + 1) ≠ 0 → ∃ q : R,
      s n = q * s (n + 1) + s (n + 2) ∧
        (s (n + 2) = 0 ∨ d.smaller (s (n + 2)) (s (n + 1)))) →
    ∃ n, s (n + 1) = 0

/-- The common divisors are unchanged by one division. -/
def CommonDivisorsStep : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b q r c : R),
    a = q * b + r → ((c ∣ a ∧ c ∣ b) ↔ (c ∣ b ∧ c ∣ r))

/-- Correctness of every completed run, without normalization of its output. -/
def RunCorrect : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (d : EuclideanData R)
      (a b g : R) (n : ℕ),
    DivisionRun d a b g n →
      IsGcd R a b g ∧ ∃ x y : R, g = x * a + y * b

/-- The terminal remainder is nonzero unless both initial inputs are zero. -/
def LastNonzero : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (d : EuclideanData R)
      (a b g : R) (n : ℕ),
    DivisionRun d a b g n → (g ≠ 0 ↔ a ≠ 0 ∨ b ≠ 0)

/-- Existence follows from the existential Euclidean hypothesis itself;
there is no additional assumed gcd or Bezout structure. -/
def ExtendedGcdExists : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R], IsEuclidean R →
    ∀ a b : R, ∃ g : R, IsGcd R a b g ∧ ∃ x y : R, g = x * a + y * b

/-- The specified zero-input conventions, including the all-zero input. -/
def ZeroInputs : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (d : EuclideanData R) (a : R),
    DivisionRun d a 0 a 0 ∧ DivisionRun d 0 0 0 0

/-- Two different quotients and remainders for the same absolute-value size.
`natAbs` is integer absolute value viewed as a natural number. -/
def IntegerNonuniqueDivision : Prop :=
  (5 : ℤ) = 2 * 2 + 1 ∧ (5 : ℤ) = 3 * 2 + (-1) ∧
    (1 : ℤ).natAbs < (2 : ℤ).natAbs ∧
    (-1 : ℤ).natAbs < (2 : ℤ).natAbs ∧
    (2 : ℤ) ≠ 3 ∧ (1 : ℤ) ≠ -1

/-- Ordinary nonnegative division selects the first of those possibilities. -/
def NonnegativeIntegerConvention : Prop :=
  (5 : ℤ) / 2 = 2 ∧ (5 : ℤ) % 2 = 1 ∧
    ∀ q r : ℤ, 5 = q * 2 + r → 0 ≤ r → r < 2 → q = 2 ∧ r = 1

end Specs.D07.Ch10.EuclideanAlgorithm
