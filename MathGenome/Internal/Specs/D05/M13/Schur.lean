import MathGenome.Internal.Specs.D05.M10.Triangularization
import MathGenome.Internal.Specs.D05.M12.GramSchmidt
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Independent statements of K05.13.schur, paper.tex:2227–2233.
The ordered basis is indexed by `Fin n`; an upper triangular matrix has zero
entries at row i, column j whenever j < i. `OrthonormalBasis` is compatible
with the paper's convention `h(u,v) = inner F v u`. No normality or positive
dimension assumption is imposed. -/

noncomputable section
namespace Specs.D05.M13.Schur

/-- Gram–Schmidt can triangularize in the same dimension while preserving the
entire invariant flag of any supplied triangularizing basis. -/
def orthonormalize_triangular_basis : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    {n : ℕ} (T : Module.End F V) (b : Module.Basis (Fin n) F V),
    (LinearMap.toMatrix b b T).IsUpperTriangular →
    ∃ e : OrthonormalBasis (Fin n) F V,
      (LinearMap.toMatrix e.toBasis e.toBasis T).IsUpperTriangular ∧
      ∀ k : ℕ, k ≤ n →
        Submodule.span F (e '' {i | i.val < k}) =
          Submodule.span F (b '' {i | i.val < k})

/-- Over either real or complex scalars, triangularizability suffices. -/
def triangularizable_orthonormal : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] (T : Module.End F V),
    Specs.D05.M10.Triangularization.HasUpperTriangularBasis T →
    ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) F V),
      (LinearMap.toMatrix e.toBasis e.toBasis T).IsUpperTriangular

/-- Every complex endomorphism has an orthonormal upper triangular basis,
including the unique endomorphism of the zero space. -/
def schur : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V),
    ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℂ V),
      (LinearMap.toMatrix e.toBasis e.toBasis T).IsUpperTriangular

end Specs.D05.M13.Schur
