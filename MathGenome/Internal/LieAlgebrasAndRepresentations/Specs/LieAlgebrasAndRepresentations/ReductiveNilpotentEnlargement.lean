import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep

/-!
LA-I09, notes/005/lie-algebras-and-representations.tex:4362–4471.
The ground field is complex.  The semisimple summand uses the radical-zero
definition, and nilpotence is internal nilpotence of the nilpotent summand.
Integer weights are taken in a chosen basis of the entire abelian summand;
in particular its action is simultaneously diagonalizable.  The embedding
has the original algebra as its domain, with its original bracket.
-/

noncomputable section
universe u

namespace Specs.LieAlgebrasAndRepresentations.ReductiveNilpotentEnlargement

open Module DiagonalEnlargementStep

/-- An actual finite-dimensional semidirect product containing `G`. -/
structure Enlargement (G : Type u) [LieRing G] [LieAlgebra ℂ G] where
  S : Type u
  T : Type u
  N : Type u
  [lieRingS : LieRing S]
  [lieAlgebraS : LieAlgebra ℂ S]
  [finiteS : FiniteDimensional ℂ S]
  [lieRingT : LieRing T]
  [lieAlgebraT : LieAlgebra ℂ T]
  [finiteT : FiniteDimensional ℂ T]
  [abelianT : IsLieAbelian T]
  [lieRingN : LieRing N]
  [lieAlgebraN : LieAlgebra ℂ N]
  [finiteN : FiniteDimensional ℂ N]
  semisimple : SolvableRadical.IsSemisimple_value ℂ S
  nilpotent : LieRing.IsNilpotent N
  action : (S × T) →ₗ⁅ℂ⁆ LieDerivation ℂ N N
  rank : ℕ
  basis : Basis (Fin rank) ℂ T
  integer_weights : HasIntegerWeights basis (centerAction action)
  embedding : G →ₗ⁅ℂ⁆ (N ⋊⁅action⁆ (S × T))
  injective : Function.Injective embedding

attribute [instance] Enlargement.lieRingS Enlargement.lieAlgebraS Enlargement.finiteS
  Enlargement.lieRingT Enlargement.lieAlgebraT Enlargement.finiteT Enlargement.abelianT
  Enlargement.lieRingN Enlargement.lieAlgebraN Enlargement.finiteN

/-- The original proposition, with no extra reduction or spectral premises. -/
def enlargement_type : Prop :=
  ∀ (G : Type u) [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G],
    Nonempty (Enlargement G)

end Specs.LieAlgebrasAndRepresentations.ReductiveNilpotentEnlargement
