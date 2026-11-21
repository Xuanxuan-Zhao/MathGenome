import MathGenome.Internal.Specs.D05.M11.Alternating
import MathGenome.Internal.Specs.D05.M11.Radicals

/-! K05.11.symplectic_blocks (paper.tex:1722–1731).
All fields, including characteristic two. Rank means the dimension of the image
of the original form curried into the algebraic dual. The matrix convention is
B(b i,b j). The finite index lists each pair consecutively, then the zero block. -/
namespace Specs.D05.M11.SymplecticBlocks
open Module
open scoped BigOperators

abbrev Coordinates (K : Type*) (r s : ℕ) := (Fin r → K × K) × (Fin s → K)
abbrev BlockIndex (r s : ℕ) := (Fin r × Fin 2) ⊕ Fin s

/-- The two-dimensional block, with the paper's sign and slot order. -/
def J (K : Type*) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

/-- A direct sum of r copies of J followed by an s-dimensional zero block. -/
def blockMatrix (K : Type*) [Field K] (r s : ℕ) :
    Matrix (BlockIndex r s) (BlockIndex r s) K := fun a b =>
  match a, b with
  | .inl (i, j), .inl (k, l) => if i = k then J K j l else 0
  | _, _ => 0

/-- Evaluation of the block form on full coordinate vectors. -/
def blockValue {K : Type*} [Field K] {r s : ℕ}
    (x y : Coordinates K r s) : K :=
  ∑ i, ((x.1 i).1 * (y.1 i).2 - (x.1 i).2 * (y.1 i).1)

/-- A genuine coordinate isomorphism, not an assumed decomposition certificate. -/
def normal_coordinates : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V), B.IsAlt →
    ∃ r s : ℕ, ∃ e : V ≃ₗ[K] Coordinates K r s,
      ∀ x y, B x y = blockValue (e x) (e y)

/-- The original space has an actual basis with exactly the asserted matrix. -/
def normal_basis : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V), B.IsAlt →
    ∃ r s : ℕ, ∃ b : Basis (BlockIndex r s) K V,
      (∀ i j, B (b i) (b j) = blockMatrix K r s i j) ∧
      Module.finrank K V = 2 * r + s ∧
      Module.finrank K (LinearMap.range B) = 2 * r ∧
      Specs.D05.M11.Radicals.leftRadical_value B =
        Submodule.span K (Set.range (fun z : Fin s => b (.inr z)))

/-- The zero block is precisely the radical; the other coordinates vanish. -/
def radical_coordinates : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {r s : ℕ} (B : LinearMap.BilinForm K V)
    (e : V ≃ₗ[K] Coordinates K r s),
    (∀ x y, B x y = blockValue (e x) (e y)) →
    ∀ x, x ∈ Specs.D05.M11.Radicals.leftRadical_value B ↔ (e x).1 = 0

/-- Evenness of the form's rank, without a characteristic restriction. -/
def even_rank : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V), B.IsAlt →
      Even (Module.finrank K (LinearMap.range B))

/-- Nondegeneracy is of the original form, not of a chosen block. -/
def even_dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V),
    B.IsAlt → B.Nondegenerate → Even (Module.finrank K V)

end Specs.D05.M11.SymplecticBlocks
