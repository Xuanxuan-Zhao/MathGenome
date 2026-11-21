import MathGenome.Internal.Specs.D05.M02.BasisExtension
import MathGenome.Internal.Specs.D05.M12.GramSchmidt

/-!
Independent statements for K05.12.on_basis, paper.tex:1981–1987.

The basis is a Mathlib `Module.Basis`, orthonormal for the shared
first-slot-linear inner product. A list has type `Fin m → V`, so extending
it means preserving every entry, in its original order, as an initial
segment of the resulting basis. All assertions include dimension zero.
No completeness assumption is added.
-/

namespace Specs.D05.M12.OnBasis

/-- Every finite-dimensional real or complex inner-product space has a finite
orthonormal basis, indexed by its dimension. -/
def exists_orthonormal_basis : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V],
    ∃ b : Module.Basis (Fin (Module.finrank F V)) F V,
      _root_.D05.orthonormalFamily (F := F) b

/-- The given orthonormal list is retained as the initial segment, with no
rescaling or permutation of its entries. -/
def extend_orthonormal_list : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] {m : ℕ} (e : Fin m → V),
    _root_.D05.orthonormalFamily (F := F) e →
      ∃ h : m ≤ Module.finrank F V,
        ∃ b : Module.Basis (Fin (Module.finrank F V)) F V,
          _root_.D05.orthonormalFamily (F := F) b ∧
          ∀ i : Fin m, b (Fin.castLE h i) = e i

/-- In dimension zero the required basis is the empty list. -/
def empty_basis : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V], Module.finrank F V = 0 →
      ∃ b : Module.Basis (Fin 0) F V,
        _root_.D05.orthonormalFamily (F := F) b

end Specs.D05.M12.OnBasis
