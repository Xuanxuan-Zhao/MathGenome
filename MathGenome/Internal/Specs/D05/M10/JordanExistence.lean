import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Polynomial.Splits

/-! Jordan form over the named field (paper.tex:1551–1560).
Blocks are indexed by `Fin r`; the sigma index lists each block's coordinates
in increasing order. Rows index output coordinates, columns index inputs.
No scalar extension or nonzero-dimension hypothesis is used. -/
noncomputable section
open scoped BigOperators Classical
namespace Specs.D05.M10.JordanExistence

/-- A block diagonal matrix with diagonal μ and superdiagonal 1 in each block.
Comparing the natural coordinates avoids dependent casts between distinct blocks. -/
def jordanMatrix {K : Type*} [Field K] {r : ℕ}
    (a : Fin r → ℕ) (μ : Fin r → K) :
    Matrix (Σ i, Fin (a i)) (Σ i, Fin (a i)) K :=
  fun i j => if i.1 = j.1 then
    if i.2.val = j.2.val then μ j.1 else
      if i.2.val + 1 = j.2.val then 1 else 0
    else 0

/-- Chains are ordered from killed vectors to their successive preimages. -/
def exists_chain_basis : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V), T.charpoly.Splits →
    ∃ (r : ℕ) (a : Fin r → ℕ) (μ : Fin r → K), (∀ i, 0 < a i) ∧
      ∃ b : Module.Basis (Σ i, Fin (a i)) K V,
        (∀ i (j : Fin (a i)), j.val = 0 → T (b ⟨i, j⟩) = μ i • b ⟨i, j⟩) ∧
        (∀ i (j k : Fin (a i)), j.val = k.val + 1 →
          T (b ⟨i, j⟩) = μ i • b ⟨i, j⟩ + b ⟨i, k⟩) ∧
        (∑ i, a i) = Module.finrank K V

/-- Full matrix conclusion, with positive individual block sizes and empty
block families allowed, in particular when V is zero. -/
def jordan_form : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V), T.charpoly.Splits →
    ∃ (r : ℕ) (a : Fin r → ℕ) (μ : Fin r → K), (∀ i, 0 < a i) ∧
      ∃ b : Module.Basis (Σ i, Fin (a i)) K V,
        LinearMap.toMatrix b b T = jordanMatrix a μ ∧
        (∑ i, a i) = Module.finrank K V

end Specs.D05.M10.JordanExistence
