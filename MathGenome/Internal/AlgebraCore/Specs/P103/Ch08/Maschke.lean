import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.RepresentationModules
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.Semisimple
import Mathlib.RepresentationTheory.Semisimple

/-! Independent statements for the nonmodular conclusions of paper.tex,
Theorem 8.3. No dimension assumption is made except in the finite decomposition.
The algebra-linear equivalences below are equivariant direct-sum decompositions;
`Π₀` is the finite-support direct sum, even for an infinite index set.
The summands carry their inherited group-algebra action, and `ofModule` restricts
this action to the group. Irreducibility includes nonzeroness. -/

noncomputable section
universe u v w
namespace P103.Ch08.MaschkeSpecs
open scoped MonoidAlgebra

/-- Every invariant subspace has an invariant linear direct complement. -/
def invariantComplementType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V),
    (Nat.card G : k) ≠ 0 → ∀ U : Subrepresentation ρ,
      ∃ W : Subrepresentation ρ, IsCompl U.toSubmodule W.toSubmodule

/-- Semisimplicity of the corresponding module, without dimension restrictions. -/
def semisimpleType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V),
    (Nat.card G : k) ≠ 0 → IsSemisimpleModule k[G] ρ.asModule

/-- Arbitrary-dimensional decomposition into nonzero irreducibles. The
index set can be infinite, and can be empty for the zero representation. -/
def directSumType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V),
    (Nat.card G : k) ≠ 0 →
      ∃ (s : Set (Submodule k[G] ρ.asModule))
        (_ : ρ.asModule ≃ₗ[k[G]] Π₀ U : s, U.1),
        ∀ U : s, IsSimpleModule k[G] U.1 ∧
          @Irreducible k G (RestrictScalars k k[G] U.1) _ _ _
            (RestrictScalars.module k k[G] U.1) (Representation.ofModule (k := k) (G := G) U.1)

/-- Finite-dimensional representations have finite decompositions, with
nonzero irreducible summands. `n = 0` is permitted. -/
def finiteDirectSumType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V), (Nat.card G : k) ≠ 0 →
      ∃ (n : ℕ) (S : Fin n → Submodule k[G] ρ.asModule)
        (_ : ρ.asModule ≃ₗ[k[G]] Π₀ i : Fin n, S i),
        ∀ i, IsSimpleModule k[G] (S i) ∧
          @Irreducible k G (RestrictScalars k k[G] (S i)) _ _ _
            (RestrictScalars.module k k[G] (S i)) (Representation.ofModule (k := k) (G := G) (S i))

end P103.Ch08.MaschkeSpecs
