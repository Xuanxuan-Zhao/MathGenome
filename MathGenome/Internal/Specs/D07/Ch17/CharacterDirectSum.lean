import MathGenome.Internal.Specs.D07.Ch17.Characters
import MathGenome.Internal.Specs.D07.Ch17.DirectSums
import MathGenome.Internal.Specs.D07.Ch17.Examples

/-!
Independent specification for K07.17.character_direct_sum,
paper.tex:4917–4936. The field and group are arbitrary. Finite dimension
is required only for characters; the permutation space has the canonical
basis of formal point masses and is finite dimensional when X is finite.
Neither the group order nor the characteristic is restricted. Empty bases
and the empty G-set are included.
-/
namespace Specs.D07.Ch17.CharacterDirectSum

universe u v w x t z

noncomputable section

/-- In concatenated finite bases, the product action has the two given
matrices on the diagonal and zero off-diagonal blocks. -/
def ProductMatrix : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    (ι : Type t) (κ : Type z)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι K V) (c : Module.Basis κ K W)
    (ρ : Representation K G V) (σ : Representation K G W) (g : G),
    LinearMap.toMatrix (b.prod c) (b.prod c) ((ρ.prod σ) g) =
      Matrix.fromBlocks (LinearMap.toMatrix b b (ρ g)) 0 0
        (LinearMap.toMatrix c c (σ g))

/-- The source's sum of characters, with no characteristic hypothesis. -/
def CharacterAdditivity : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (ρ : Representation K G V) (σ : Representation K G W) (g : G),
    Characters.characterValue K G (V × W) (ρ.prod σ) g =
      Characters.characterValue K G V ρ g + Characters.characterValue K G W σ g

/-- Row y, column x is 1 precisely when y = gx. In particular the diagonal
entry for x is 1 precisely when gx = x. -/
def PermutationMatrix : Prop := by
  classical
  exact ∀ (K : Type u) (G : Type v) (X : Type w)
    [Field K] [Group G] [MulAction G X] [Fintype X] (g : G) (y x : X),
    LinearMap.toMatrix (MonoidAlgebra.basis X K) (MonoidAlgebra.basis X K)
      (Examples.permutationValue K G X g) y x = if g • x = y then 1 else 0

/-- Fixed basis points are counted in the natural numbers and then cast to K.
This counts points, rather than the dimension of an operator's fixed space. -/
def PermutationCharacter : Prop :=
  ∀ (K : Type u) (G : Type v) (X : Type w)
    [Field K] [Group G] [MulAction G X] [Finite X],
    letI : FiniteDimensional K (MonoidAlgebra K X) :=
      Module.Finite.of_basis (MonoidAlgebra.basis X K)
    ∀ g : G, Characters.characterValue K G (MonoidAlgebra K X)
      (Examples.permutationValue K G X) g = (Nat.card {x : X // g • x = x} : K)

end
end Specs.D07.Ch17.CharacterDirectSum
