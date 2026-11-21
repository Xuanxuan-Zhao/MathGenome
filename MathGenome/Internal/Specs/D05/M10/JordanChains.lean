import MathGenome.Internal.Specs.D05.M10.Rational
import MathGenome.Internal.Specs.D05.M10.Nilpotent

/-! Independent statements of K05.10.jordan_chains, paper.tex:1541–1549.
The sigma index retains each chain as a distinct block. Indices within a
chain increase from the killed vector towards its successive preimages.
The field is arbitrary, and no nonzero-space hypothesis is imposed. -/

noncomputable section
open Polynomial
open scoped BigOperators

namespace Specs.D05.M10.JordanChains

/-- The reversed residue powers form a chain basis in the actual quotient. -/
def quotient_chain_basis : Prop :=
  ∀ {K : Type*} [Field K] (a : ℕ), 0 < a →
    ∃ b : Module.Basis (Fin a) K (AdjoinRoot (X ^ a : K[X])),
      (∀ j, b j = AdjoinRoot.mk (X ^ a : K[X]) (X ^ (a - 1 - j.val))) ∧
      (∀ j, j.val = 0 → AdjoinRoot.root (X ^ a : K[X]) * b j = 0) ∧
      (∀ j k, j.val = k.val + 1 →
        AdjoinRoot.root (X ^ a : K[X]) * b j = b k)

/-- A basis, rather than a merely spanning collection of preimages, is the
full conclusion. Positive lengths exclude empty individual chains, while
the outer family can be empty. The final equality counts all basis vectors. -/
def jordan_chain_basis : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (N : Module.End K V), IsNilpotent N →
    ∃ (r : ℕ) (a : Fin r → ℕ), (∀ i, 0 < a i) ∧
      ∃ b : Module.Basis (Σ i, Fin (a i)) K V,
        (∀ i (j : Fin (a i)), j.val = 0 → N (b ⟨i, j⟩) = 0) ∧
        (∀ i (j k : Fin (a i)), j.val = k.val + 1 →
          N (b ⟨i, j⟩) = b ⟨i, k⟩) ∧
        (∑ i, a i) = Module.finrank K V

/-- The zero space admits the empty union as a chain basis. -/
def zero_space : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (N : Module.End K V), Module.finrank K V = 0 →
      ∃ b : Module.Basis (Σ _ : Fin 0, Fin 1) K V,
        ∀ i, N (b i) = 0

end Specs.D05.M10.JordanChains
