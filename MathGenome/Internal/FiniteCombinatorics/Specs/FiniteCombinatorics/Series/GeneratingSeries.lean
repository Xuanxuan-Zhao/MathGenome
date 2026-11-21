import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Nat.Factorial.Basic

/-!
Shared formal-series interface for Definition 2.1 (p204:W10).
All series are Mathlib `PowerSeries`; no topology or convergence is involved.
The expected values here give the canonical constructions independently of the
candidate implementation and can be reused by downstream Specs.
-/

noncomputable section

universe u

namespace Specs.FiniteCombinatorics.Series

/-- Expected type and value of the ordinary generating series construction. -/
def ogfType : Type (u + 1) :=
  ∀ {R : Type u} [CommRing R], (ℕ → R) → PowerSeries R

def ogfValue : ogfType :=
  fun {_} [_] a => PowerSeries.mk a

/-- Expected type and value of the exponential generating series construction. -/
def egfType : Type (u + 1) :=
  ∀ {R : Type u} [CommRing R] [Algebra ℚ R], (ℕ → R) → PowerSeries R

def egfValue : egfType :=
  fun {R} [_] [_] a =>
    PowerSeries.mk (fun n => a n * algebraMap ℚ R ((Nat.factorial n : ℚ)⁻¹))

/-- Equality of formal series means equality of all coefficients. -/
def coefficient_extensionality : Prop :=
  ∀ {R : Type u} [CommRing R] (A B : PowerSeries R),
    A = B ↔ ∀ n : ℕ, PowerSeries.coeff n A = PowerSeries.coeff n B

def ogf_coefficients : Prop :=
  ∀ {R : Type u} [CommRing R] (a : ℕ → R) (n : ℕ),
    PowerSeries.coeff n (ogfValue a) = a n

def egf_coefficients : Prop :=
  ∀ {R : Type u} [CommRing R] [Algebra ℚ R] (a : ℕ → R) (n : ℕ),
    PowerSeries.coeff n (egfValue a) =
      a n * algebraMap ℚ R ((Nat.factorial n : ℚ)⁻¹)

/-- Every formal series is the OGF of its sequence of coefficients. -/
def ogf_reconstruction : Prop :=
  ∀ {R : Type u} [CommRing R] (A : PowerSeries R),
    ogfValue (fun n => PowerSeries.coeff n A) = A

end Specs.FiniteCombinatorics.Series
