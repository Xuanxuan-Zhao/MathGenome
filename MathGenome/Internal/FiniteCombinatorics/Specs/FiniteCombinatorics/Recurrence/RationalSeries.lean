import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Recurrence.InitialValues
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.GeneratingSeries
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Independent specification of paper.tex, p204:W14.
All statements retain arbitrary commutative coefficient rings, including rings
with zero divisors. The polynomial degree is `WithBot ℕ`, so zero is covered.
-/
noncomputable section
open scoped BigOperators
universe u
namespace Specs.FiniteCombinatorics.Recurrence

def denominatorType : Type (u + 1) :=
  ∀ {R : Type u} [CommRing R] {r : ℕ}, (Fin r → R) → Polynomial R

def denominatorValue : denominatorType :=
  fun {_} [_] {r} c =>
    1 - ∑ j : Fin r, Polynomial.C (c j) * Polynomial.X ^ (r - (j : ℕ))

/-- A canonical numerator parametrized by exactly the r initial values.
The recurrence's canonical sequence is used only to define the construction;
the theorems below assert its degree and its identity for every solution. -/
def numeratorType : Type (u + 1) :=
  ∀ {R : Type u} [CommRing R] {r : ℕ}, (Fin r → R) → (Fin r → R) → Polynomial R

def numeratorValue : numeratorType :=
  fun {_} [_] {r} c init => PowerSeries.trunc r
    ((denominatorValue c : PowerSeries _) *
      Series.ogfValue (sequenceValue c init))

def denominator_constant : Prop :=
  ∀ {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R),
    PowerSeries.constantCoeff (denominatorValue c : PowerSeries R) = 1

def numerator_degree : Prop :=
  ∀ {R : Type u} [CommRing R] {r : ℕ} (c init : Fin r → R),
    (numeratorValue c init).degree < (r : WithBot ℕ)

def product_coefficients_vanish : Prop :=
  ∀ {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) (a : ℕ → R),
    IsSolutionValue c a → ∀ n : ℕ, r ≤ n →
      PowerSeries.coeff n ((denominatorValue c : PowerSeries R) * Series.ogfValue a) = 0

def rational_product : Prop :=
  ∀ {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) (_hr : 1 ≤ r)
    (init : Fin r → R) (a : ℕ → R),
    IsSolutionValue c a → (∀ i : Fin r, a i = init i) →
      (denominatorValue c : PowerSeries R) * Series.ogfValue a =
        (numeratorValue c init : PowerSeries R)

def unique_numerator : Prop :=
  ∀ {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) (_hr : 1 ≤ r)
    (a : ℕ → R), IsSolutionValue c a →
      ∃! P : Polynomial R, P.degree < (r : WithBot ℕ) ∧
        (denominatorValue c : PowerSeries R) * Series.ogfValue a = (P : PowerSeries R)

def rational_quotient : Prop :=
  ∀ {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R) (_hr : 1 ≤ r)
    (init : Fin r → R) (a : ℕ → R),
    IsSolutionValue c a → (∀ i : Fin r, a i = init i) →
      Series.ogfValue a = (numeratorValue c init : PowerSeries R) *
        PowerSeries.invOfUnit (denominatorValue c : PowerSeries R) (1 : Rˣ)

/-- Explicitly records that equal initial data give the same numerator. -/
def numerator_initial_dependence : Prop :=
  ∀ {R : Type u} [CommRing R] {r : ℕ} (c : Fin r → R)
    (a b : ℕ → R), (∀ i : Fin r, a i = b i) →
      numeratorValue c (fun i => a i) = numeratorValue c (fun i => b i)

end Specs.FiniteCombinatorics.Recurrence
