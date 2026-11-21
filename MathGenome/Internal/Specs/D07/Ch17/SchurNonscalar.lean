import MathGenome.Internal.Specs.D07.Ch17.IrreducibleDefinition
import MathGenome.Internal.Specs.D07.Ch17.KernelsImages
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
Independent specification of K07.17.schur_nonscalar (paper.tex:4780–4799).
The group, field, and vector spaces in Schur's lemma are arbitrary. In
particular, there are no dimension, cardinality, or algebraic-closedness
assumptions. The equivalence has the given intertwiner as its underlying map.
The endomorphism algebra is the actual centralizer subalgebra of End_K(V),
with its inherited addition, scalar multiplication, identity, and composition.
A division algebra is expressed as a nontrivial algebra whose nonzero elements
are units. This formulation does not choose an inverse operation.
-/
namespace Specs.D07.Ch17.SchurNonscalar

universe u v w x

/-- Every nonzero intertwiner between irreducibles is an equivariant linear isomorphism. -/
def NonzeroIntertwinerEquivalence : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W) (T : V →ₗ[K] W),
    Representation.IsIrreducible ρ → Representation.IsIrreducible σ →
    ρ.IsIntertwiningMap σ T → T ≠ 0 →
    ∃ e : ρ.Equiv σ, e.toLinearMap = T

/-- The source's End_G(V), as a subalgebra of all linear endomorphisms. -/
def EndomorphismAlgebraType : Type (max u v w + 1) :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V],
    Representation K G V → Subalgebra K (Module.End K V)

abbrev endomorphismAlgebraValue : EndomorphismAlgebraType.{u,v,w} :=
  fun K _ _ _ _ _ _ ρ => Subalgebra.centralizer K (Set.range ρ)

/-- Membership in this concrete subalgebra means exactly equivariance. -/
def EndomorphismAlgebraCharacterization : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (T : Module.End K V),
    T ∈ endomorphismAlgebraValue K G V ρ ↔ ρ.IsIntertwiningMap ρ T

/-- The endomorphism algebra of any irreducible representation is a division algebra. -/
def DivisionAlgebra : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V), Representation.IsIrreducible ρ →
    Nontrivial (endomorphismAlgebraValue K G V ρ) ∧
    ∀ T : endomorphismAlgebraValue K G V ρ, T ≠ 0 → IsUnit T

/-- On the original real C₄ representation, J is a nonzero nonscalar
endomorphism, despite irreducibility, and satisfies J² = -I. -/
def RealNonscalarExample : Prop :=
  let ρ := IrreducibleDefinition.rotationValue ℝ
  let J := IrreducibleDefinition.quarterTurn ℝ
  Representation.IsIrreducible ρ ∧ ρ.IsIntertwiningMap ρ J ∧
    J ≠ 0 ∧ J ^ 2 = -1 ∧ ¬ ∃ a : ℝ, J = a • (1 : Module.End ℝ (ℝ × ℝ))

end Specs.D07.Ch17.SchurNonscalar
