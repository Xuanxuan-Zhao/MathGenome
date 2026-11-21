import MathGenome.Internal.D07.Ch17.Characters
import MathGenome.Internal.D07.Ch17.DirectSums
import MathGenome.Internal.D07.Ch17.Examples
import MathGenome.Internal.Specs.D07.Ch17.CharacterDirectSum

/-! Character additivity and fixed-point counts over arbitrary fields. -/
namespace D07.Ch17.CharacterDirectSum

universe u v w x t z

noncomputable section

open Specs.D07.Ch17.CharacterDirectSum

theorem product_matrix : ProductMatrix.{u,v,w,x,t,z} := by
  intro K G V W ι κ _ _ _ _ _ _ _ _ _ _ b c ρ σ g
  exact LinearMap.toMatrix_prodMap b c (ρ g) (σ g)

theorem character_direct_sum : CharacterAdditivity.{u,v,w,x} := by
  intro K G V W _ _ _ _ _ _ _ _ ρ σ g
  change LinearMap.trace K (V × W) ((ρ g).prodMap (σ g)) =
    LinearMap.trace K V (ρ g) + LinearMap.trace K W (σ g)
  exact LinearMap.trace_prodMap' (ρ g) (σ g)

theorem permutation_matrix : PermutationMatrix.{u,v,w} := by
  classical
  intro K G X _ _ _ _ g y x
  rw [LinearMap.toMatrix_apply]
  change (Examples.permutation K G X g (MonoidAlgebra.single x 1)).coeff y = _
  rw [Examples.permutation_on_basis]
  simp [Finsupp.single_apply]

theorem permutation_character : PermutationCharacter.{u,v,w} := by
  classical
  intro K G X _ _ _ _
  let : Fintype X := Fintype.ofFinite X
  let : FiniteDimensional K (MonoidAlgebra K X) :=
    Module.Finite.of_basis (MonoidAlgebra.basis X K)
  intro g
  change LinearMap.trace K (MonoidAlgebra K X) (Examples.permutation K G X g) = _
  rw [LinearMap.trace_eq_matrix_trace K (MonoidAlgebra.basis X K)]
  change (∑ x : X, LinearMap.toMatrix (MonoidAlgebra.basis X K)
    (MonoidAlgebra.basis X K) (Specs.D07.Ch17.Examples.permutationValue K G X g) x x) = _
  calc
    _ = ∑ x : X, if g • x = x then (1 : K) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact permutation_matrix K G X g x x
    _ = _ := by simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

end
end D07.Ch17.CharacterDirectSum
