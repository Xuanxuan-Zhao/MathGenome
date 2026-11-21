import MathGenome.Internal.Specs.D05.M11.Radicals
import MathGenome.Internal.Specs.D05.M11.Polarization
import MathGenome.Internal.Specs.D05.M02.BasisExtension
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
K05.11.diagonal_congruence, paper.tex:1688–1697. The radical is the
upstream left radical; for the symmetric forms in the existence theorem it
also equals the right radical. Orthogonality here means vanishing off the
diagonal, with no positivity or nondegeneracy condition. `(2 : K) ≠ 0`
is the field's characteristic-not-two hypothesis. The auxiliary statements
apply to every finite orthogonal basis, including the empty basis.
-/
namespace Specs.D05.M11.DiagonalCongruence

open Module

/-- In an orthogonal basis the radical equations are coordinate times diagonal
entry equal to zero. -/
def mem_radical_iff_coordinates : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]
    (B : LinearMap.BilinForm K V) (b : Basis I K V)
    (_hO : ∀ i j, i ≠ j → B (b i) (b j) = 0) (x : V),
    x ∈ Radicals.leftRadical_value B ↔ ∀ i, b.repr x i * B (b i) (b i) = 0

/-- Precisely the zero-diagonal basis directions span the radical. -/
def radical_eq_span : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]
    (B : LinearMap.BilinForm K V) (b : Basis I K V)
    (_hO : ∀ i j, i ≠ j → B (b i) (b j) = 0),
    Radicals.leftRadical_value B =
      Submodule.span K (b '' {i | B (b i) (b i) = 0})

/-- The selected vectors themselves, with their original indices retained,
form a basis of the radical as a subspace of the original space. -/
def radical_basis : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]
    (B : LinearMap.BilinForm K V) (b : Basis I K V)
    (_hO : ∀ i j, i ≠ j → B (b i) (b j) = 0),
    ∃ c : Basis {i : I // B (b i) (b i) = 0} K (Radicals.leftRadical_value B),
      ∀ i, (c i : V) = b i

/-- Full source conclusion, including degenerate forms and the zero space. -/
def orthogonal_basis_radical : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (_hTwo : (2 : K) ≠ 0) (B : LinearMap.BilinForm K V) (_hB : B.IsSymm),
    ∃ b : Basis (Fin (finrank K V)) K V,
      (∀ i j, i ≠ j → B (b i) (b j) = 0) ∧
      ∃ c : Basis {i : Fin (finrank K V) // B (b i) (b i) = 0} K
          (Radicals.leftRadical_value B),
        ∀ i, (c i : V) = b i

end Specs.D05.M11.DiagonalCongruence
