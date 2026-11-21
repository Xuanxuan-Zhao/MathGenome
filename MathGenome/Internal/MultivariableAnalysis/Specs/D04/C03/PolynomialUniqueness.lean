import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.HigherInterfaces
import Mathlib.Algebra.MvPolynomial.Degrees

/-! Independent specification for finite polynomial uniqueness. Coordinate
polynomials have real coefficients, and evaluation uses the canonical Euclidean
coordinates. The degree bound applies separately to every output coordinate.
Little-o is punctured, so dimension zero has a separate evaluation statement. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace Specs.D04.C03.PolynomialUniqueness
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C03.HigherInterfaces.Model
namespace Model

abbrev CoordinatePolynomial (n m : ℕ) := Fin m → MvPolynomial (Fin n) ℝ

def coordinatePolynomialEval {n m : ℕ} (p : CoordinatePolynomial n m) (h : E n) : E m :=
  WithLp.toLp 2 (fun i => MvPolynomial.eval (fun j => h j) (p i))

/-- A polynomial function of total degree at most k, including the zero function. -/
def PolynomialFunctionDegreeLE {n m : ℕ} (k : ℕ) (Q : E n → E m) : Prop :=
  ∃ p : CoordinatePolynomial n m, (∀ i, (p i).totalDegree ≤ k) ∧ Q = coordinatePolynomialEval p

end Model
open Model

abbrev CoordinatePolynomialType := ℕ → ℕ → Type
def CoordinatePolynomialValue : CoordinatePolynomialType := Model.CoordinatePolynomial
abbrev coordinatePolynomialEvalType := {n m : ℕ} → CoordinatePolynomial n m → E n → E m
def coordinatePolynomialEvalValue : coordinatePolynomialEvalType := @Model.coordinatePolynomialEval
abbrev PolynomialFunctionDegreeLEType := {n m : ℕ} → ℕ → (E n → E m) → Prop
def PolynomialFunctionDegreeLEValue : PolynomialFunctionDegreeLEType := @Model.PolynomialFunctionDegreeLE

def polynomialFunctionDegreeLE_diagonalType : Prop :=
  ∀ {n m : ℕ} (r : ℕ) (T : Differential (E n) (E m) r),
    PolynomialFunctionDegreeLE r (differentialDiagonal T)

def polynomialFunctionDegreeLE_taylorPolynomialType : Prop :=
  ∀ {n m : ℕ} (k : ℕ) (f : E n → E m) (a : E n),
    PolynomialFunctionDegreeLE k (taylorPolynomial k f a)

def coordinatePolynomialEval_injectiveType : Prop :=
  ∀ {n m : ℕ}, Function.Injective (@coordinatePolynomialEval n m)

def coordinatePolynomial_coeff_uniqueType : Prop :=
  ∀ {n m : ℕ} (p q : CoordinatePolynomial n m),
    coordinatePolynomialEval p = coordinatePolynomialEval q →
    ∀ (i : Fin m) (α : Fin n →₀ ℕ), (p i).coeff α = (q i).coeff α

def coordinatePolynomial_zero_of_isLittleOType : Prop :=
  ∀ {n m : ℕ}, 0 < n → ∀ (k : ℕ) (p : CoordinatePolynomial n m),
    (∀ i, (p i).totalDegree ≤ k) →
    (coordinatePolynomialEval p =o[𝓝[≠] 0] (fun h => ‖h‖^k)) → p = 0

def polynomialFunction_zero_of_isLittleOType : Prop :=
  ∀ {n m : ℕ}, 0 < n → ∀ (k : ℕ) (Q : E n → E m),
    PolynomialFunctionDegreeLE k Q →
    (Q =o[𝓝[≠] 0] (fun h => ‖h‖^k)) → Q = 0

def polynomialFunction_eq_of_sub_isLittleOType : Prop :=
  ∀ {n m : ℕ}, 0 < n → ∀ (k : ℕ) (P Q : E n → E m),
    PolynomialFunctionDegreeLE k P → PolynomialFunctionDegreeLE k Q →
    ((fun h => P h - Q h) =o[𝓝[≠] 0] (fun h => ‖h‖^k)) → P = Q

def functions_dimension_zero_eq_iffType : Prop :=
  ∀ {Y : Type} (P Q : E 0 → Y), P = Q ↔ P 0 = Q 0

/-- Direct evaluation gives the arithmetic value equalities in dimension zero;
none of these assertions is inferred from a punctured limit. -/
def taylorPolynomial_dimension_zero_addType : Prop :=
  ∀ {m : ℕ} (k : ℕ) (f g : E 0 → E m) (a h : E 0),
    taylorPolynomial k (fun x => f x + g x) a h =
      taylorPolynomial k f a h + taylorPolynomial k g a h

def taylorPolynomial_dimension_zero_operationType : Prop :=
  ∀ {m p q : ℕ} (k : ℕ) (B : E m → E p → E q)
    (f : E 0 → E m) (g : E 0 → E p) (a h : E 0),
    taylorPolynomial k (fun x => B (f x) (g x)) a h =
      B (taylorPolynomial k f a h) (taylorPolynomial k g a h)

def taylorPolynomial_dimension_zero_compType : Prop :=
  ∀ {m p : ℕ} (k : ℕ) (f : E 0 → E m) (g : E m → E p) (a h : E 0),
    taylorPolynomial k (g ∘ f) a h =
      taylorPolynomial k g (f a) (taylorPolynomial k f a h - f a)

def taylorPolynomial_dimension_zero_reciprocalType : Prop :=
  ∀ (k : ℕ) (f : E 0 → ℝ) (a h : E 0), f a ≠ 0 →
    taylorPolynomial k (fun x => (f x)⁻¹) a h =
      ∑ j ∈ Finset.range (k+1), (-(taylorPolynomial k f a h - f a))^j / (f a)^(j+1)

end Specs.D04.C03.PolynomialUniqueness
