import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.Algebraic.Defs

/-!
Independent statements for K07.13.frobenius, paper.tex:3887–3896.

The absolute map is the p-power map in an arbitrary characteristic-p field.
The relative map uses the cardinality q of the specified finite base, with
the chosen embedding recorded by Algebra K L. The ambient extension may be
infinite: only algebraicity is assumed. Preimages are obtained in the actual
embedded simple intermediate fields, rather than in an unrelated field copy.
No assertion that absolute Frobenius fixes a larger finite base is made.
-/

universe u v

namespace Specs.D07.Ch13.Frobenius

def AbsoluteEndomorphism : Prop :=
  ∀ (F : Type u) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p],
    ∃ φ : F →+* F, (∀ x : F, φ x = x ^ p) ∧ Function.Injective φ

def AbsoluteFiniteBijective : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p],
    Function.Bijective (fun x : F => x ^ p)

/-- Relative Frobenius already defines an endomorphism without algebraicity. -/
def RelativeEndomorphism : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [Finite K]
    (q : ℕ), Nat.card K = q →
      ∃ Φ : L →ₐ[K] L, ∀ x : L, Φ x = x ^ q

def RelativeBaseFixation : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [Finite K]
    (q : ℕ), Nat.card K = q →
      ∀ c : K, (algebraMap K L c) ^ q = algebraMap K L c

/-- For each algebraic element, its finite simple field contains a preimage.
There is no finite-dimensionality hypothesis on L/K. -/
def FiniteSimplePreimages : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [Finite K]
    (q : ℕ), Nat.card K = q → ∀ a : L, IsAlgebraic K a →
      Finite (IntermediateField.adjoin K {a}) ∧
        ∃ b : IntermediateField.adjoin K {a}, (b : L) ^ q = a

def RelativeSurjective : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [Finite K]
    [Algebra.IsAlgebraic K L] (q : ℕ), Nat.card K = q →
      Function.Surjective (fun x : L => x ^ q)

def RelativeAutomorphism : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [Finite K]
    [Algebra.IsAlgebraic K L] (q : ℕ), Nat.card K = q →
      ∃ Φ : L ≃ₐ[K] L, ∀ x : L, Φ x = x ^ q

end Specs.D07.Ch13.Frobenius
