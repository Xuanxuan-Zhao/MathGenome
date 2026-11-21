import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
Independent specifications for the finite-field portion of Theorem nt:B02
(paper.tex:447–487). A `Field` is nontrivial. Positive natural exponents encode
the source's integers f ≥ 1. The exponent is the dimension over the canonical
embedded prime field, not just an exponent in an abstract factorization.
-/

universe u v

namespace P203Specs.Ch02.FiniteFields

/-- The characteristic is a positive prime, and the size is its positive power,
with that exponent equal to the finite dimension over the prime field. -/
def CharacteristicAndCardinality : Prop :=
  ∀ (F : Type u) [Field F] [Finite F],
    ∃ (p f : ℕ) (hp : p.Prime) (hc : CharP F p),
      letI : Fact p.Prime := ⟨hp⟩
      letI : CharP F p := hc
      letI := ZMod.algebra F p
      ringChar F = p ∧ FiniteDimensional (ZMod p) F ∧
        1 ≤ f ∧ Module.finrank (ZMod p) F = f ∧ Nat.card F = p ^ f

/-- Every positive prime power occurs, including f = 1 and p = 2. -/
def Existence : Prop :=
  ∀ (p f : ℕ), p.Prime → 1 ≤ f →
    ∃ (F : Type) (_ : Field F), Finite F ∧ Nat.card F = p ^ f

/-- The cardinalities alone imply characteristic p, and there is an isomorphism
commuting with the canonical embeddings of ZMod p. Characteristic-p structures
are conclusions, not extra assumptions. No uniqueness of the isomorphism is
asserted. Both fields may live in arbitrary, different universes. -/
def Uniqueness : Prop :=
  ∀ (p f : ℕ) (hp : p.Prime), 1 ≤ f →
    ∀ (E : Type u) (L : Type v) [Field E] [Field L] [Finite E] [Finite L],
      Nat.card E = p ^ f → Nat.card L = p ^ f →
      ∃ (hcE : CharP E p) (hcL : CharP L p),
        letI : Fact p.Prime := ⟨hp⟩
        letI : CharP E p := hcE
        letI : CharP L p := hcL
        letI := ZMod.algebra E p
        letI := ZMod.algebra L p
        Nonempty (E ≃ₐ[ZMod p] L)

end P203Specs.Ch02.FiniteFields
