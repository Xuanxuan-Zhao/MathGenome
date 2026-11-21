import MathGenome.Internal.D07.Ch02.PermutationConvention
import MathGenome.Internal.Specs.D07.Ch02.SymmetricOrder

/-!
# Counting and relabelling permutations

`K07.02.symmetric_order`: counting includes the empty set; relabelling is
conjugation by a bijection, on arbitrary sets.
-/

namespace D07.Ch02.SymmetricOrder

universe u v

theorem symmetric_cardinality :
    Specs.D07.Ch02.SymmetricOrder.SymmetricCardinality.{u} := by
  classical
  intro X _ n hn
  letI : Fintype X := Fintype.ofFinite X
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hn]

theorem relabelling_iso :
    Specs.D07.Ch02.SymmetricOrder.RelabellingIso.{u, v} := by
  intro X Y b
  exact ⟨b.permCongrHom, fun _ _ => rfl⟩

end D07.Ch02.SymmetricOrder
