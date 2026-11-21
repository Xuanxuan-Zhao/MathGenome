import Mathlib.Algebra.Polynomial.Roots

/-!
Independent specification of K07.11.root_bound, paper.tex:2410–2440.

All polynomials are the formal `Polynomial R` used by the upstream entries.
The coefficient ring is any commutative domain, including finite domains.
The degree is bottom-valued; each numerical bound explicitly assumes the
polynomial is nonzero and has degree n. No splitting or field assumption is
made. The sum is over a finite enumeration of exactly the actual roots.
The multiplicity characterization identifies the library number with the
largest exponent of the corresponding monic linear factor.
-/

universe u

namespace Specs.D07.Ch11.RootBound

open Polynomial

/-- Finiteness concerns the actual zeros of evaluation. -/
def RootsFinite : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (f : Polynomial R), f ≠ 0 →
    Set.Finite {a : R | f.eval a = 0}

/-- The whole set of distinct roots has cardinality at most the degree.
Finiteness is included so that `ncard` cannot mask an infinite set. -/
def DistinctRootBound : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (f : Polynomial R) (n : ℕ),
    f ≠ 0 → f.degree = (n : WithBot ℕ) →
      Set.Finite {a : R | f.eval a = 0} ∧ {a : R | f.eval a = 0}.ncard ≤ n

/-- The root multiset enumerates precisely the actual roots, and its counts
are the multiplicities. This bridge requires a nonzero polynomial. -/
def RootMultisetCorrect : Prop := by
  classical
  exact ∀ (R : Type u) [CommRing R] [IsDomain R] (f : Polynomial R), f ≠ 0 →
    ∀ a : R, (a ∈ f.roots ↔ f.eval a = 0) ∧
      f.roots.count a = f.rootMultiplicity a

/-- In particular the exponent m itself divides, and no exponent above m does.
The equivalence specifies maximality rather than merely a numerical bound. -/
def MultiplicityCharacterization : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (f : Polynomial R), f ≠ 0 →
    ∀ (a : R) (k : ℕ),
      (X - C a) ^ k ∣ f ↔ k ≤ f.rootMultiplicity a

/-- Sum each actual root's maximal multiplicity once, with no assumption
that the polynomial splits. The root set is finite by `RootsFinite`. -/
def MultiplicitySumBound : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (f : Polynomial R) (n : ℕ),
    f ≠ 0 → f.degree = (n : WithBot ℕ) →
      ∀ s : Finset R, (∀ a : R, a ∈ s ↔ f.eval a = 0) →
        (∑ a ∈ s, f.rootMultiplicity a) ≤ n

/-- Zero vanishes everywhere and has no largest linear-factor exponent.
This is independent of any default library root multiset or multiplicity. -/
def ZeroPolynomialException : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a : R),
    (0 : Polynomial R).eval a = 0 ∧
    (∀ k : ℕ, (X - C a) ^ k ∣ (0 : Polynomial R)) ∧
    ¬ ∃ m : ℕ, ∀ k : ℕ, (X - C a) ^ k ∣ (0 : Polynomial R) ↔ k ≤ m

end Specs.D07.Ch11.RootBound
