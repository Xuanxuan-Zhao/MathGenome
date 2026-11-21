import Mathlib.FieldTheory.Finite.Trace

/-!
Independent statements for K07.20.hilbert90_additive, paper.tex:6008–6030.
`Algebra.trace` and `Algebra.norm` are the multiplication-operator trace
and determinant. A generator is specified by membership of every
automorphism in its cyclic subgroup. No assumption on the characteristic
or invertibility of the degree is made. The finite-field statements apply
to arbitrary compatible copies of the fields, with q = Nat.card K; the
extension degree n is determined by the embedding (and is positive).
-/

universe u v
namespace Specs.D07.Ch20.Hilbert90Additive

noncomputable section

def AdditiveHilbert90 : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L),
    (∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) →
    ∀ a : L, Algebra.trace K L a = 0 ↔ ∃ b : L, a = b - σ b

def FiniteFieldAdditive : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L]
    [Finite K] [Finite L] [Algebra K L] (a : L),
    Algebra.trace K L a = 0 ↔ ∃ b : L, a = b ^ Nat.card K - b

def FiniteFieldMultiplicative : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L]
    [Finite K] [Finite L] [Algebra K L] (a : L),
    a ≠ 0 →
      (Algebra.norm K a = 1 ↔ ∃ c : Lˣ, a = (c : L) ^ (Nat.card K - 1))

end
end Specs.D07.Ch20.Hilbert90Additive
