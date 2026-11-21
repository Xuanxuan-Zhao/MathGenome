import MathGenome.Internal.D07.Ch01.ElementaryGroupLaws
import MathGenome.Internal.D07.Ch02.SymmetricOrder
import MathGenome.Internal.Specs.D07.Ch02.Cayley
import Mathlib.Data.Fintype.EquivFin

/-!
# Cayley's embedding

`K07.02.cayley`: left multiplication gives a permutation, associativity
gives a homomorphism, and evaluation at the identity proves injectivity.
For finite groups the upstream relabelling isomorphism gives the map to `S_n`.
-/

namespace D07.Ch02.Cayley

universe u

theorem cayley : Specs.D07.Ch02.Cayley.CayleyEmbedding.{u} := by
  intro G _
  let L : G → Equiv.Perm G := fun g =>
    { toFun := fun x => g * x
      invFun := fun x => g⁻¹ * x
      left_inv := fun x => inv_mul_cancel_left g x
      right_inv := fun x => mul_inv_cancel_left g x }
  let ρ : G →* Equiv.Perm G :=
    { toFun := L
      map_one' := by
        ext x
        exact one_mul x
      map_mul' := by
        intro g h
        ext x
        exact mul_assoc g h x }
  refine ⟨ρ, ?_, fun _ _ => rfl⟩
  intro g h hgh
  have he := congrArg (fun σ : Equiv.Perm G => σ 1) hgh
  change g * 1 = h * 1 at he
  simpa only [mul_one] using he

theorem finite_cayley : Specs.D07.Ch02.Cayley.FiniteCayleyEmbedding.{u} := by
  intro G _ _ n hn
  classical
  let : Fintype G := Fintype.ofFinite G
  let b : G ≃ Fin n := Fintype.equivFinOfCardEq
    ((Nat.card_eq_fintype_card (α := G)).symm.trans hn)
  obtain ⟨ρ, hρ, _⟩ := cayley G
  obtain ⟨e, _⟩ := D07.Ch02.SymmetricOrder.relabelling_iso G (Fin n) b
  exact ⟨e.toMonoidHom.comp ρ, e.injective.comp hρ⟩

end D07.Ch02.Cayley
