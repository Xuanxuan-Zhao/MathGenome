import MathGenome.Internal.Specs.D07.Ch13.Existence
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
Independent statements for K07.13.galois_group, paper.tex:3950–3957.

The base embedding is always the specified `Algebra K L`. The embedded
statement uses exactly the upstream root field in the fixed algebraic
closure, not an independently chosen field of the same cardinality.
The general statement also applies to any finite extension over this base.
The exponent is the cardinality q of K, rather than its characteristic.

Normality, separability, finite degree, and finite automorphism group are
conclusions. Bijectivity of the powers indexed by `Fin n` asserts both that
all automorphisms are powers and that the first n powers are distinct.
The case n = 1, including the trivial automorphism group, is retained.
-/

universe u v

namespace Specs.D07.Ch13.GaloisGroup

/-- The full relative finite-field Galois-group conclusion. -/
def GaloisDescription (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] (q n : ℕ) : Prop :=
  Normal K L ∧ Algebra.IsSeparable K L ∧ FiniteDimensional K L ∧
    IsGalois K L ∧ Finite (L ≃ₐ[K] L) ∧
    Nat.card (L ≃ₐ[K] L) = n ∧ IsCyclic (L ≃ₐ[K] L) ∧
    ∃ Φ : L ≃ₐ[K] L,
      (∀ x : L, Φ x = x ^ q) ∧
      orderOf Φ = n ∧ Φ ^ n = 1 ∧
      Function.Bijective (fun j : Fin n => Φ ^ (j : ℕ))

/-- No normality, separability, or Galois hypothesis is imposed. -/
def FiniteExtensionGaloisGroup : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Finite K] [Finite L] (q n : ℕ),
    Nat.card K = q → Module.finrank K L = n → GaloisDescription K L q n

/-- L is the particular field F_(q^n) already constructed in Ω. -/
def EmbeddedGaloisGroup : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Finite K] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]
    (q n : ℕ), Nat.card K = q → 1 ≤ n →
    GaloisDescription K (Existence.rootFieldValue K Ω q n) q n

end Specs.D07.Ch13.GaloisGroup
