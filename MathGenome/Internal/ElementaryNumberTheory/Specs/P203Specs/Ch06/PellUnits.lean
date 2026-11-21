import Mathlib.NumberTheory.Pell
import Mathlib.Analysis.Real.Sqrt

/-! The integral-coefficient order of paper.tex, Chapter 6, lines 2700–2711.
`Zsqrtd D` is the standard ring of pairs of integers, for every positive
nonsquare integer D; squarefreeness is not required. -/
namespace P203Specs.Ch06.PellUnits

/-- Type of the family of integer-coefficient quadratic rings. -/
def IntegralOrderType := ℤ → Type

abbrev IntegralQuadratic (D : ℤ) := Zsqrtd D

/-- Evaluation in the positive real square root. -/
noncomputable def realValue (D : ℤ) (z : IntegralQuadratic D) : ℝ :=
  z.re + z.im * Real.sqrt (D : ℝ)

/-- The source's conjugation, on integer coefficients. -/
def conjugate {D : ℤ} (z : IntegralQuadratic D) : IntegralQuadratic D := star z

/-- The source's integer-valued norm. -/
def norm {D : ℤ} (z : IntegralQuadratic D) : ℤ := Zsqrtd.norm z

/-- The real evaluation as a ring homomorphism. -/
noncomputable def realEmbedding (D : ℤ) (hD : 0 < D) : IntegralQuadratic D →+* ℝ :=
  Zsqrtd.lift ⟨Real.sqrt (D : ℝ), by
    simpa only [← pow_two] using Real.sq_sqrt (show (0 : ℝ) ≤ D by exact_mod_cast hD.le)⟩

/-- Integer pairs, conjugation, and the norm have exactly the stated formulas. -/
def CoefficientFormulas : Prop :=
  ∀ (D x y : ℤ),
    realValue D (⟨x, y⟩ : IntegralQuadratic D) = (x : ℝ) + y * Real.sqrt (D : ℝ) ∧
    conjugate (⟨x, y⟩ : IntegralQuadratic D) = ⟨x, -y⟩ ∧
    norm (⟨x, y⟩ : IntegralQuadratic D) = x ^ 2 - D * y ^ 2

/-- The pair model embeds faithfully in the reals, with exactly Z[sqrt(D)] as image. -/
def RealModel : Prop :=
  ∀ (D : ℤ) (hD : 0 < D), ¬IsSquare D →
    Function.Injective (realValue D) ∧
    (∀ z, realEmbedding D hD z = realValue D z) ∧
    Set.range (realValue D) = {r : ℝ | ∃ x y : ℤ, r = x + y * Real.sqrt (D : ℝ)}

/-- Conjugation is multiplicative and norm is its real product and is multiplicative. -/
def NormLaws : Prop :=
  ∀ (D : ℤ) (_hD : 0 < D) (z w : IntegralQuadratic D),
    conjugate (z * w) = conjugate z * conjugate w ∧
    norm (z * w) = norm z * norm w ∧
    (norm z : ℝ) = realValue D z * realValue D (conjugate z)

def UnitCriterion : Prop :=
  ∀ (D : ℤ) (z : IntegralQuadratic D), IsUnit z ↔ norm z = 1 ∨ norm z = -1

/-- The explicit inverse remains in the integer-coefficient ring, for both signs. -/
def SignedInverse : Prop :=
  ∀ (D : ℤ) (z : IntegralQuadratic D) (ε : ℤ),
    (ε = 1 ∨ ε = -1) → norm z = ε →
    z * ((ε : IntegralQuadratic D) * conjugate z) = 1 ∧
    ((ε : IntegralQuadratic D) * conjugate z) * z = 1

def UnitsInverse : Prop :=
  ∀ (D : ℤ) (u : (IntegralQuadratic D)ˣ),
    (↑(u⁻¹) : IntegralQuadratic D) =
      ((norm (u : IntegralQuadratic D) : ℤ) : IntegralQuadratic D) *
        conjugate (u : IntegralQuadratic D)

/-- The coordinate identities of the source, including the nonzero real denominator. -/
def UnitCoordinates : Prop :=
  ∀ (D : ℤ), 0 < D → ∀ (z : IntegralQuadratic D) (ε : ℤ),
    (ε = 1 ∨ ε = -1) → norm z = ε →
    realValue D z ≠ 0 ∧
    (z.re : ℝ) = (realValue D z + (ε : ℝ) / realValue D z) / 2 ∧
    (z.im : ℝ) = (realValue D z - (ε : ℝ) / realValue D z) /
      (2 * Real.sqrt (D : ℝ))

/-- For either norm sign, the source's real ordering agrees with positive coordinates. -/
def PositiveCoordinates : Prop :=
  ∀ (D : ℤ), 0 < D → ∀ (z : IntegralQuadratic D), IsUnit z →
    (1 < realValue D z ↔ 0 < z.re ∧ 0 < z.im)

/-- Norm-one objects and Pell solutions correspond bijectively. -/
def PellCorrespondence : Prop :=
  ∀ (D : ℤ),
    (∀ a : Pell.Solution₁ D, norm (a : IntegralQuadratic D) = 1) ∧
    (∀ z : IntegralQuadratic D, norm z = 1 →
      ∃! a : Pell.Solution₁ D, (a : IntegralQuadratic D) = z)

/-- The standard Pell multiplication is the multiplication in this same order. -/
def PellMultiplication : Prop :=
  ∀ (D : ℤ) (_hD : 0 < D) (a b : Pell.Solution₁ D),
    ((a * b : Pell.Solution₁ D) : IntegralQuadratic D) =
      (a : IntegralQuadratic D) * (b : IntegralQuadratic D) ∧
    (a * b).x = a.x * b.x + D * (a.y * b.y) ∧
    (a * b).y = a.x * b.y + a.y * b.x ∧
    realValue D ((a * b : Pell.Solution₁ D) : IntegralQuadratic D) =
      realValue D (a : IntegralQuadratic D) * realValue D (b : IntegralQuadratic D)

end P203Specs.Ch06.PellUnits
