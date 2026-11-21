import MathGenome.Internal.Specs.D07.Ch17.SchurNonscalar
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Independent specification of K07.17.schur_scalar, paper.tex:4801–4823.
The commutant is exactly the centralizer subalgebra fixed by SchurNonscalar.
Irreducibility includes nonzeroness. No finiteness of the group is assumed.
-/
namespace Specs.D07.Ch17.SchurScalar

universe u v w

/-- Every equivariant endomorphism is a unique scalar multiple of the identity. -/
def UniqueScalar : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    [IsAlgClosed K] [FiniteDimensional K V] (ρ : Representation K G V),
    Representation.IsIrreducible ρ →
    ∀ T : SchurNonscalar.endomorphismAlgebraValue K G V ρ,
      ∃! a : K, (T : Module.End K V) = a • (1 : Module.End K V)

/-- The canonical scalar map itself is a K-algebra isomorphism. -/
def ScalarMapIsomorphism : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    [IsAlgClosed K] [FiniteDimensional K V] (ρ : Representation K G V),
    Representation.IsIrreducible ρ →
    ∃ e : K ≃ₐ[K] SchurNonscalar.endomorphismAlgebraValue K G V ρ,
      e.toAlgHom = Algebra.ofId K (SchurNonscalar.endomorphismAlgebraValue K G V ρ)

/-- The dimension-one consequence stated at the end of the source proof. -/
def EndomorphismFinrank : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    [IsAlgClosed K] [FiniteDimensional K V] (ρ : Representation K G V),
    Representation.IsIrreducible ρ →
    Module.finrank K (SchurNonscalar.endomorphismAlgebraValue K G V ρ) = 1

end Specs.D07.Ch17.SchurScalar
