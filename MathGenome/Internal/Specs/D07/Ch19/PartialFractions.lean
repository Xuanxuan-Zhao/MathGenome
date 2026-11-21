import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Coprime.Basic

/-!
Independent statements for K07.19.partial_fractions, paper.tex:5516–5567.
The rational-function field is the fraction field of the formal polynomial ring.
`Fin r` includes the empty factorization. A coefficient indexed by `j : Fin (e i)`
is the paper's a_{i,j+1}; in particular the last index is the highest pole.
Degree uses bottom for the zero polynomial, so zero numerators are allowed.
-/

universe u

namespace Specs.D07.Ch19.PartialFractions

noncomputable section

open Polynomial
open scoped BigOperators

def denominator {F : Type u} [Field F] {r : ℕ}
    (p : Fin r → Polynomial F) (e : Fin r → ℕ) : Polynomial F :=
  ∏ i, p i ^ e i

abbrev Form (F : Type u) [Field F] (r : ℕ) (e : Fin r → ℕ) :=
  Polynomial F × ((i : Fin r) → Fin (e i) → Polynomial F)

/-- The literal rational-function identity, with all normalization bounds. -/
def IsDecomposition {F : Type u} [Field F] {r : ℕ}
    (f : Polynomial F) (p : Fin r → Polynomial F) (e : Fin r → ℕ)
    (ha : Form F r e) : Prop :=
  (∀ i j, (ha.2 i j).degree < (p i).degree) ∧
  algebraMap (Polynomial F) (FractionRing (Polynomial F)) f /
      algebraMap (Polynomial F) (FractionRing (Polynomial F)) (denominator p e) =
    algebraMap (Polynomial F) (FractionRing (Polynomial F)) ha.1 +
      ∑ i, ∑ j : Fin (e i),
        algebraMap (Polynomial F) (FractionRing (Polynomial F)) (ha.2 i j) /
          algebraMap (Polynomial F) (FractionRing (Polynomial F)) (p i) ^ (j.val + 1)

/-- Existence and joint uniqueness of the polynomial part and every numerator.
Reduction is unnecessary for this assertion, and is imposed below for nonvanishing. -/
def NormalizedPartialFractions : Prop :=
  ∀ (F : Type u) [Field F] (r : ℕ) (p : Fin r → Polynomial F)
    (e : Fin r → ℕ) (f : Polynomial F),
    (∀ i, (p i).Monic) → (∀ i, Irreducible (p i)) →
    Function.Injective p → (∀ i, 0 < e i) →
    ∃! ha : Form F r e, IsDecomposition f p e ha

/-- The factored denominator is monic and nonzero; it is one exactly for
the empty list of irreducible factors with positive multiplicities. -/
def DenominatorNormalization : Prop :=
  ∀ (F : Type u) [Field F] (r : ℕ) (p : Fin r → Polynomial F)
    (e : Fin r → ℕ),
    (∀ i, (p i).Monic) → (∀ i, Irreducible (p i)) → (∀ i, 0 < e i) →
      (denominator p e).Monic ∧ denominator p e ≠ 0 ∧
        (denominator p e = 1 ↔ r = 0)

/-- A reduced numerator and denominator have no missing highest-order pole. -/
def TopNumeratorsNonzero : Prop :=
  ∀ (F : Type u) [Field F] (r : ℕ) (p : Fin r → Polynomial F)
    (e : Fin r → ℕ) (f : Polynomial F)
    (hm : ∀ i, (p i).Monic) (hi : ∀ i, Irreducible (p i))
    (hd : Function.Injective p) (he : ∀ i, 0 < e i),
    IsCoprime f (denominator p e) →
    ∀ ha : Form F r e, IsDecomposition f p e ha →
      ∀ i, ha.2 i ⟨e i - 1, Nat.sub_lt (he i) (by decide)⟩ ≠ 0

/-- The empty factorization has denominator one and polynomial part f. -/
def EmptyDenominator : Prop :=
  ∀ (F : Type u) [Field F] (f : Polynomial F)
    (p : Fin 0 → Polynomial F) (e : Fin 0 → ℕ) (ha : Form F 0 e),
    denominator p e = 1 ∧ (IsDecomposition f p e ha ↔ ha.1 = f)

/-- Zero has zero polynomial part and zero numerators, including empty sums. -/
def ZeroNumerator : Prop :=
  ∀ (F : Type u) [Field F] (r : ℕ) (p : Fin r → Polynomial F)
    (e : Fin r → ℕ),
    (∀ i, (p i).Monic) → (∀ i, Irreducible (p i)) →
    Function.Injective p → (∀ i, 0 < e i) →
    ∀ ha : Form F r e, IsDecomposition 0 p e ha →
      ha = (0, fun _ _ => 0)

end

end Specs.D07.Ch19.PartialFractions
