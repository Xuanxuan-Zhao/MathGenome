import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.PolynomialUniqueness
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.BilinearRules
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-! Independent finite Taylor arithmetic. Truncation deletes exactly those
monomials whose total degree exceeds k. All Taylor selectors are the canonical
upstream objects. Positive-order hypotheses are pointwise for addition and
bilinear arithmetic, and C^k on compatible open domains for composition.
The scalar reciprocal and quotient retain the same pointwise hypotheses,
with base-point nonvanishing. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace Specs.D04.C03.TaylorArithmetic
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C03.HigherInterfaces.Model
open Specs.D04.C03.PolynomialUniqueness.Model
namespace Model

/-- Literal deletion of monomials above the specified total degree. -/
def truncate {n : ℕ} (k : ℕ) (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ := by
  classical
  exact AddMonoidAlgebra.ofCoeff (Finsupp.filter
    (fun α : Fin n →₀ ℕ => α.sum (fun _ r => r) ≤ k) p.coeff)

def multilinearPolynomial {n : ℕ} (r : ℕ) (c : (Fin r → Fin n) → ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ j : Fin r → Fin n, MvPolynomial.C (c j) * ∏ s : Fin r, MvPolynomial.X (j s)

/-- Coordinate expansion of the canonical Taylor tensors, without selecting
polynomial witnesses through an existence theorem. -/
def taylorCoordinates {n m : ℕ} (k : ℕ) (f : E n → E m) (a : E n) :
    CoordinatePolynomial n m := fun i =>
  ∑ r ∈ Finset.range (k+1), MvPolynomial.C ((r.factorial : ℝ)⁻¹) *
    multilinearPolynomial r (fun j => higherDifferential r f a (fun s => standardBasis n (j s)) i)

def scalarTaylorCoordinates {n : ℕ} (k : ℕ) (f : E n → ℝ) (a : E n) :
    MvPolynomial (Fin n) ℝ :=
  ∑ r ∈ Finset.range (k+1), MvPolynomial.C ((r.factorial : ℝ)⁻¹) *
    multilinearPolynomial r (fun j => higherDifferential r f a (fun s => standardBasis n (j s)))

def bilinearCoordinates {n m p q : ℕ} (B : E m →ₗ[ℝ] E p →ₗ[ℝ] E q)
    (P : CoordinatePolynomial n m) (Q : CoordinatePolynomial n p) : CoordinatePolynomial n q :=
  fun i => ∑ j : Fin m, ∑ l : Fin p,
    MvPolynomial.C (B (standardBasis m j) (standardBasis p l) i) * P j * Q l

def compositionCoordinates {n m p : ℕ} (P : CoordinatePolynomial m p)
    (Q : CoordinatePolynomial n m) (b : E m) : CoordinatePolynomial n p :=
  fun i => MvPolynomial.eval₂Hom MvPolynomial.C (fun j => Q j - MvPolynomial.C (b j)) (P i)

def reciprocalCoordinates {n : ℕ} (k : ℕ) (P : MvPolynomial (Fin n) ℝ) (c : ℝ) :
    MvPolynomial (Fin n) ℝ :=
  truncate k (∑ j ∈ Finset.range (k+1),
    MvPolynomial.C ((c^(j+1))⁻¹) * (-(P - MvPolynomial.C c))^j)

/-- Precisely the order-zero and positive-order hypotheses for the Peano theorem. -/
def TaylorHypothesis {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) (U : Set X) (f : X → Y) (a : X) : Prop :=
  if k = 0 then IsOpen U ∧ a ∈ U ∧ ContinuousAt f a else TimesDifferentiableAt k U f a

end Model
open Model

abbrev truncateType := {n : ℕ} → ℕ → MvPolynomial (Fin n) ℝ → MvPolynomial (Fin n) ℝ
def truncateValue : truncateType := @truncate
abbrev multilinearPolynomialType := {n : ℕ} → (r : ℕ) → ((Fin r → Fin n) → ℝ) → MvPolynomial (Fin n) ℝ
def multilinearPolynomialValue : multilinearPolynomialType := @multilinearPolynomial
abbrev taylorCoordinatesType := {n m : ℕ} → ℕ → (E n → E m) → E n → CoordinatePolynomial n m
def taylorCoordinatesValue : taylorCoordinatesType := @taylorCoordinates
abbrev scalarTaylorCoordinatesType := {n : ℕ} → ℕ → (E n → ℝ) → E n → MvPolynomial (Fin n) ℝ
def scalarTaylorCoordinatesValue : scalarTaylorCoordinatesType := @scalarTaylorCoordinates
abbrev bilinearCoordinatesType := {n m p q : ℕ} → (E m →ₗ[ℝ] E p →ₗ[ℝ] E q) → CoordinatePolynomial n m → CoordinatePolynomial n p → CoordinatePolynomial n q
def bilinearCoordinatesValue : bilinearCoordinatesType := @bilinearCoordinates
abbrev compositionCoordinatesType := {n m p : ℕ} → CoordinatePolynomial m p → CoordinatePolynomial n m → E m → CoordinatePolynomial n p
def compositionCoordinatesValue : compositionCoordinatesType := @compositionCoordinates
abbrev reciprocalCoordinatesType := {n : ℕ} → ℕ → MvPolynomial (Fin n) ℝ → ℝ → MvPolynomial (Fin n) ℝ
def reciprocalCoordinatesValue : reciprocalCoordinatesType := @reciprocalCoordinates
abbrev TaylorHypothesisType := {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → ℕ → Set X → (X → Y) → X → Prop
def TaylorHypothesisValue : TaylorHypothesisType := @TaylorHypothesis

section Generic
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def taylorPolynomial_addType : Prop := ∀ {X Y : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (k : ℕ) (U : Set X) (f g : X → Y) (a h : X),
  TimesDifferentiableAt k U f a → TimesDifferentiableAt k U g a →
  taylorPolynomial k (fun x => f x + g x) a h =
    taylorPolynomial k f a h + taylorPolynomial k g a h
end Generic

def truncate_coeffType : Prop := ∀ {n : ℕ} (k : ℕ) (p : MvPolynomial (Fin n) ℝ)
  (α : Fin n →₀ ℕ), (truncate k p).coeff α =
    if α.sum (fun _ r => r) ≤ k then p.coeff α else 0

def truncate_degreeType : Prop := ∀ {n : ℕ} (k : ℕ) (p : MvPolynomial (Fin n) ℝ),
  (truncate k p).totalDegree ≤ k

def taylorCoordinates_evalType : Prop := ∀ {n m : ℕ} (k : ℕ) (f : E n → E m) (a h : E n),
  coordinatePolynomialEval (taylorCoordinates k f a) h = taylorPolynomial k f a h

def scalarTaylorCoordinates_evalType : Prop := ∀ {n : ℕ} (k : ℕ) (f : E n → ℝ) (a h : E n),
  MvPolynomial.eval (fun j => h j) (scalarTaylorCoordinates k f a) = taylorPolynomial k f a h

def taylorPolynomial_bilinearType : Prop := ∀ {n m p q : ℕ} (k : ℕ)
  (B : E m →ₗ[ℝ] E p →ₗ[ℝ] E q) (U : Set (E n))
  (f : E n → E m) (g : E n → E p) (a h : E n),
  TaylorHypothesis k U f a → TaylorHypothesis k U g a →
  taylorPolynomial k (fun x => B (f x) (g x)) a h =
    coordinatePolynomialEval (fun i => truncate k
      (bilinearCoordinates B (taylorCoordinates k f a) (taylorCoordinates k g a) i)) h

def taylorPolynomial_compType : Prop := ∀ {n m p : ℕ} (k : ℕ), 1 ≤ k →
  ∀ (U : Set (E n)) (V : Set (E m)) (f : E n → E m) (g : E m → E p) (a h : E n),
  IsOpen U → IsOpen V → a ∈ U → MapsTo f U V → CrOn k U f → CrOn k V g →
  taylorPolynomial k (g ∘ f) a h = coordinatePolynomialEval (fun i => truncate k
    (compositionCoordinates (taylorCoordinates k g (f a)) (taylorCoordinates k f a) (f a) i)) h

def taylorPolynomial_comp_zeroType : Prop := ∀ {X Y Z : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] (f : X → Y) (g : Y → Z) (a h : X),
  taylorPolynomial 0 (g ∘ f) a h = g (f a)

def taylorPolynomial_reciprocalType : Prop := ∀ {n : ℕ} (k : ℕ)
  (U : Set (E n)) (q : E n → ℝ) (a h : E n),
  TaylorHypothesis k U q a → q a ≠ 0 →
  taylorPolynomial k (fun x => (q x)⁻¹) a h =
    MvPolynomial.eval (fun j => h j) (reciprocalCoordinates k (scalarTaylorCoordinates k q a) (q a))

def taylorPolynomial_quotientType : Prop := ∀ {n m : ℕ} (k : ℕ)
  (U : Set (E n)) (f : E n → E m) (q : E n → ℝ) (a h : E n),
  TaylorHypothesis k U f a → TaylorHypothesis k U q a → q a ≠ 0 →
  taylorPolynomial k (fun x => (q x)⁻¹ • f x) a h =
    coordinatePolynomialEval (fun i => truncate k
      (reciprocalCoordinates k (scalarTaylorCoordinates k q a) (q a) * taylorCoordinates k f a i)) h

def truncate_addType : Prop := ∀ {n : ℕ} (k : ℕ) (p q : MvPolynomial (Fin n) ℝ),
  truncate k (p+q) = truncate k p + truncate k q

def truncate_idempotentType : Prop := ∀ {n : ℕ} (k : ℕ) (p : MvPolynomial (Fin n) ℝ),
  truncate k (truncate k p) = truncate k p

def truncate_eq_selfType : Prop := ∀ {n : ℕ} (k : ℕ) (p : MvPolynomial (Fin n) ℝ),
  p.totalDegree ≤ k → truncate k p = p

def truncate_dimension_zeroType : Prop := ∀ (k : ℕ) (p : MvPolynomial (Fin 0) ℝ),
  truncate k p = p

end Specs.D04.C03.TaylorArithmetic
