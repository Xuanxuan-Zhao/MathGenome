import MathGenome.Internal.Specs.D05.M13.Schur
import MathGenome.Internal.Specs.D05.M10.SimultaneousTriangular

/-! Independent statements for K05.13.simultaneous_schur,
paper.tex:2379–2385. Matrices use ordered `Fin n` bases and vanish strictly
below the diagonal. Orthonormality uses the existing inner product; swapping
its arguments to the paper's first-slot-linear convention does not change it.
The family may be empty or infinite and the space may have dimension zero. -/

noncomputable section
namespace Specs.D05.M13.SimultaneousSchur

/-- A single orthonormalization preserves the common flag and triangularizes
every operator in the supplied family. This also applies over the real field
when a common triangularizing basis is already given. -/
def orthonormalize_common_triangular_basis : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    {n : ℕ} (S : Set (Module.End F V)) (b : Module.Basis (Fin n) F V),
    (∀ T ∈ S, (LinearMap.toMatrix b b T).IsUpperTriangular) →
    ∃ e : OrthonormalBasis (Fin n) F V,
      (∀ T ∈ S, (LinearMap.toMatrix e.toBasis e.toBasis T).IsUpperTriangular) ∧
      ∀ k : ℕ, k ≤ n →
        Submodule.span F (e '' {i | i.val < k}) =
          Submodule.span F (b '' {i | i.val < k})

/-- Every arbitrary commuting set of complex endomorphisms admits one common
orthonormal upper triangular basis, with no spectral or normality hypothesis. -/
def simultaneous_schur : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (S : Set (Module.End ℂ V)),
    S.Pairwise Commute →
    ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℂ V),
      ∀ T ∈ S, (LinearMap.toMatrix e.toBasis e.toBasis T).IsUpperTriangular

/-- The equivalent arbitrary indexed version, allowing repeated operators and
placing no finiteness assumption on the index type. -/
def simultaneous_schur_indexed : Prop :=
  ∀ {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : ι → Module.End ℂ V),
    (Pairwise fun i j => Commute (T i) (T j)) →
    ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℂ V),
      ∀ i, (LinearMap.toMatrix e.toBasis e.toBasis (T i)).IsUpperTriangular

end Specs.D05.M13.SimultaneousSchur
