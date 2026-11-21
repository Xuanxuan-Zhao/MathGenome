import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Independent specification of the explicit-formula part of K07.15.small_degrees
(paper.tex:4444–4448). Coefficients and radicals live in one specified field F.
The quadratic formula only requires 2 ≠ 0. The remaining identities apply to
every characteristic-zero field; existence of radical
choices is asserted in every algebraically closed such field, hence in any
chosen algebraic closure of the original coefficient field via its algebraMap.
Polynomial equalities retain every root with its multiplicity, including zeros
and coincident roots. No ordering or reality of intermediate radicals is assumed. -/

namespace Specs.D07.Ch15.SmallDegreesCubicQuarticFormulas

open Polynomial
universe u v

def QuadraticFormula : Prop :=
  ∀ (F : Type u) [Field F] [NeZero (2 : F)] (a b c s : F), a ≠ 0 →
    s ^ 2 = b ^ 2 - 4 * a * c →
    C a * X ^ 2 + C b * X + C c =
      C a * (X - C ((-b + s) / (2 * a))) * (X - C ((-b - s) / (2 * a)))

def QuadraticChoices : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] [IsAlgClosed F] (a b c : F),
    ∃ s : F, s ^ 2 = b ^ 2 - 4 * a * c

def CubicDepression : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (a b c y : F),
    (y - a / 3) ^ 3 + a * (y - a / 3) ^ 2 + b * (y - a / 3) + c =
      y ^ 3 + (b - a ^ 2 / 3) * y + (2 * a ^ 3 / 27 - a * b / 3 + c)

def CardanoChoices : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] [IsAlgClosed F] (p q : F),
    ∃ d u ζ : F, d ^ 2 = q ^ 2 / 4 + p ^ 3 / 27 ∧
      u ^ 3 = -q / 2 + d ∧ IsPrimitiveRoot ζ 3

def CardanoRelations : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (p q d u : F),
    d ^ 2 = q ^ 2 / 4 + p ^ 3 / 27 → u ^ 3 = -q / 2 + d → u ≠ 0 →
    let v := -p / (3 * u)
    v ^ 3 = -q / 2 - d ∧ u ^ 3 + v ^ 3 = -q ∧ 3 * u * v = -p

/-- The ordered three linear factors give all roots, counted with multiplicity. -/
def CubicFactorization : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (p q u v ζ : F),
    IsPrimitiveRoot ζ 3 → u ^ 3 + v ^ 3 = -q → 3 * u * v = -p →
    X ^ 3 + C p * X + C q =
      (X - C (u + v)) * (X - C (ζ * u + ζ ^ 2 * v)) *
        (X - C (ζ ^ 2 * u + ζ * v))

/-- The factors above have exactly the source's ζ^j u + ζ^(-j) v indexing. -/
def CubicIndexing : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (u v ζ : F),
    IsPrimitiveRoot ζ 3 → ∀ j : Fin 3,
    ζ ^ (j.val : ℤ) * u + ζ ^ (-(j.val : ℤ)) * v =
      (![u + v, ζ * u + ζ ^ 2 * v, ζ ^ 2 * u + ζ * v] : Fin 3 → F) j

def CardanoFactorization : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (p q d u ζ : F),
    d ^ 2 = q ^ 2 / 4 + p ^ 3 / 27 → u ^ 3 = -q / 2 + d →
    u ≠ 0 → IsPrimitiveRoot ζ 3 →
    let v := -p / (3 * u)
    X ^ 3 + C p * X + C q =
      (X - C (u + v)) * (X - C (ζ * u + ζ ^ 2 * v)) *
        (X - C (ζ ^ 2 * u + ζ * v))

/-- Direct formulation with the exact integer-exponent enumeration in the source. -/
def CardanoIndexedFactorization : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (p q d u ζ : F),
    d ^ 2 = q ^ 2 / 4 + p ^ 3 / 27 → u ^ 3 = -q / 2 + d →
    u ≠ 0 → IsPrimitiveRoot ζ 3 →
    let v := -p / (3 * u)
    X ^ 3 + C p * X + C q =
      ∏ j : Fin 3, (X - C (ζ ^ (j.val : ℤ) * u + ζ ^ (-(j.val : ℤ)) * v))

/-- The exceptional choice u=0 forces p=0; any cube root of -q works,
including w=0 when q=0. -/
def CardanoZeroBranch : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (p q d u ζ : F),
    d ^ 2 = q ^ 2 / 4 + p ^ 3 / 27 → u ^ 3 = -q / 2 + d →
    u = 0 → IsPrimitiveRoot ζ 3 →
    p = 0 ∧ ∀ w : F, w ^ 3 = -q →
      X ^ 3 + C p * X + C q =
        (X - C w) * (X - C (ζ * w)) * (X - C (ζ ^ 2 * w))

def CubeRootChoices : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] [IsAlgClosed F] (q : F),
    ∃ w : F, w ^ 3 = -q

def QuarticDepression : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (a b c d y : F),
    (y - a / 4) ^ 4 + a * (y - a / 4) ^ 3 + b * (y - a / 4) ^ 2 +
      c * (y - a / 4) + d =
    y ^ 4 + (b - 3 * a ^ 2 / 8) * y ^ 2 +
      (c - a * b / 2 + a ^ 3 / 8) * y +
      (d - a * c / 4 + a ^ 2 * b / 16 - 3 * a ^ 4 / 256)

/-- q=0: first solve the quadratic in y², then take two square roots. -/
def BiquadraticChoices : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] [IsAlgClosed F] (p r : F),
    ∃ t s₁ s₂ : F, t ^ 2 = p ^ 2 - 4 * r ∧
      s₁ ^ 2 = (-p + t) / 2 ∧ s₂ ^ 2 = (-p - t) / 2

def BiquadraticFactorization : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (p r t s₁ s₂ : F),
    t ^ 2 = p ^ 2 - 4 * r → s₁ ^ 2 = (-p + t) / 2 → s₂ ^ 2 = (-p - t) / 2 →
    X ^ 4 + C p * X ^ 2 + C r =
      (X - C s₁) * (X - C (-s₁)) * (X - C s₂) * (X - C (-s₂))

/-- Ferrari's resolvent is a genuine cubic, available by the cubic formulas. -/
def ResolventExists : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] [IsAlgClosed F] (p q r : F),
    ∃ z : F, q ^ 2 = 4 * (2 * z - p) * (z ^ 2 - r)

def FerrariChoices : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] [IsAlgClosed F] (p q r z : F),
    q ≠ 0 → q ^ 2 = 4 * (2 * z - p) * (z ^ 2 - r) →
    ∃ u : F, u ^ 2 = 2 * z - p ∧ u ≠ 0

def FerrariRelations : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (p q r z u : F),
    q ≠ 0 → q ^ 2 = 4 * (2 * z - p) * (z ^ 2 - r) →
    u ^ 2 = 2 * z - p →
    (2 * z - p ≠ 0 ∧ u ≠ 0 ∧
      let v := -q / (2 * u)
      v ^ 2 = z ^ 2 - r ∧ 2 * u * v = -q)

/-- Both the source difference of squares and its two quadratic factors. -/
def FerrariFactorization : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (p q r z u : F),
    q ≠ 0 → q ^ 2 = 4 * (2 * z - p) * (z ^ 2 - r) →
    u ^ 2 = 2 * z - p →
    let v := -q / (2 * u)
    X ^ 4 + C p * X ^ 2 + C q * X + C r =
      (X ^ 2 + C z) ^ 2 - (C u * X + C v) ^ 2 ∧
    X ^ 4 + C p * X ^ 2 + C q * X + C r =
      (X ^ 2 - C u * X + C (z - v)) * (X ^ 2 + C u * X + C (z + v))

def FerrariQuadraticChoices : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] [IsAlgClosed F] (z u v : F),
    ∃ s t : F, s ^ 2 = u ^ 2 - 4 * (z - v) ∧ t ^ 2 = u ^ 2 - 4 * (z + v)

/-- Solving the two quadratics supplies all four roots, with multiplicity. -/
def FerrariFourRoots : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (p q r z u s t : F),
    q ≠ 0 → q ^ 2 = 4 * (2 * z - p) * (z ^ 2 - r) →
    u ^ 2 = 2 * z - p →
    let v := -q / (2 * u)
    s ^ 2 = u ^ 2 - 4 * (z - v) → t ^ 2 = u ^ 2 - 4 * (z + v) →
    X ^ 4 + C p * X ^ 2 + C q * X + C r =
      (X - C ((u + s) / 2)) * (X - C ((u - s) / 2)) *
      (X - C ((-u + t) / 2)) * (X - C ((-u - t) / 2))

/-- Application to coefficients over K, with the actual specified embedding into
an arbitrary algebraic closure. Characteristic zero of the closure is derived. -/
def CubicInAlgebraicClosure : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [CharZero K]
    [Algebra K Ω] [IsAlgClosure K Ω] (p q : K),
    let ι := algebraMap K Ω
    ∃ d u ζ : Ω, d ^ 2 = (ι q) ^ 2 / 4 + (ι p) ^ 3 / 27 ∧
      u ^ 3 = -(ι q) / 2 + d ∧ IsPrimitiveRoot ζ 3 ∧
      (u ≠ 0 →
        X ^ 3 + C (ι p) * X + C (ι q) =
          ∏ j : Fin 3, (X - C (ζ ^ (j.val : ℤ) * u +
            ζ ^ (-(j.val : ℤ)) * (-(ι p) / (3 * u))))) ∧
      (u = 0 → p = 0 ∧ ∃ w : Ω, w ^ 3 = -(ι q) ∧
        X ^ 3 + C (ι p) * X + C (ι q) =
          (X - C w) * (X - C (ζ * w)) * (X - C (ζ ^ 2 * w)))

/-- The two quartic branches over the embedded original coefficient field,
with every radical choice and the resulting four linear factors explicit. -/
def QuarticInAlgebraicClosure : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [CharZero K]
    [Algebra K Ω] [IsAlgClosure K Ω] (p q r : K),
    let ι := algebraMap K Ω
    (q = 0 → ∃ t s₁ s₂ : Ω, t ^ 2 = (ι p) ^ 2 - 4 * (ι r) ∧
      s₁ ^ 2 = (-(ι p) + t) / 2 ∧ s₂ ^ 2 = (-(ι p) - t) / 2 ∧
      X ^ 4 + C (ι p) * X ^ 2 + C (ι q) * X + C (ι r) =
        (X - C s₁) * (X - C (-s₁)) * (X - C s₂) * (X - C (-s₂))) ∧
    (q ≠ 0 → ∃ z u s t : Ω,
      (ι q) ^ 2 = 4 * (2 * z - ι p) * (z ^ 2 - ι r) ∧
      u ^ 2 = 2 * z - ι p ∧ u ≠ 0 ∧
      let v := -(ι q) / (2 * u)
      s ^ 2 = u ^ 2 - 4 * (z - v) ∧ t ^ 2 = u ^ 2 - 4 * (z + v) ∧
      X ^ 4 + C (ι p) * X ^ 2 + C (ι q) * X + C (ι r) =
        (X - C ((u + s) / 2)) * (X - C ((u - s) / 2)) *
        (X - C ((-u + t) / 2)) * (X - C ((-u - t) / 2)))

end Specs.D07.Ch15.SmallDegreesCubicQuarticFormulas
