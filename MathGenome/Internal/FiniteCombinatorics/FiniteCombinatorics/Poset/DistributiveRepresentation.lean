import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Poset.DistributiveRepresentation
import Mathlib.Order.Birkhoff

namespace FiniteCombinatorics.Poset

/-- The library's irreducibility predicate agrees with the source, including
exclusion of the bottom element. -/
theorem joinIrreducible_iff_supIrred {L : Type*} [SemilatticeSup L] [OrderBot L]
    (j : L) : JoinIrreducible j ↔ SupIrred j := by
  constructor
  · rintro ⟨hne, hj⟩
    refine ⟨fun hmin => hne hmin.eq_bot, ?_⟩
    intro u v h
    exact (hj u v h.symm).imp Eq.symm Eq.symm
  · rintro hj
    refine ⟨hj.ne_bot, ?_⟩
    intro u v h
    exact (hj.2 h.symm).imp Eq.symm Eq.symm

/-- Finite distributive lattices are the lattices of lower sets of their
nonzero join-irreducibles, with the maps prescribed in W06. -/
theorem distributive_representation :
    Specs.FiniteCombinatorics.Poset.DistributiveRepresentation := by
  intro L _ _ _
  classical
  let : Fintype L := Fintype.ofFinite L
  let eJ : {j : L // SupIrred j} ≃o JoinIrreducibles L :=
    { toFun := fun j => ⟨j, (joinIrreducible_iff_supIrred (j : L)).2 j.property⟩
      invFun := fun j => ⟨j, (joinIrreducible_iff_supIrred (j : L)).1 j.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  let e : L ≃o LowerSet (JoinIrreducibles L) :=
    OrderIso.lowerSetSupIrred.trans (LowerSet.map eJ)
  refine ⟨e, ?_, ?_, e.map_sup, e.map_inf⟩
  · intro x j
    change j ∈ LowerSet.map eJ (OrderIso.lowerSetSupIrred x) ↔ _
    rw [LowerSet.mem_map]
    rfl
  · intro S
    change ((eJ ⁻¹' (S : Set (JoinIrreducibles L))).toFinset.sup
      (fun j => (j : L))) = _
    apply le_antisymm
    · apply Finset.sup_le
      intro j hj
      have hjS : j ∈ eJ ⁻¹' (S : Set (JoinIrreducibles L)) := Set.mem_toFinset.1 hj
      exact Finset.le_sup_of_le (((S : Set (JoinIrreducibles L)).toFinite.mem_toFinset).2 hjS) le_rfl
    · apply Finset.sup_le
      intro j hj
      have hjS : j ∈ S := ((S : Set (JoinIrreducibles L)).toFinite.mem_toFinset).1 hj
      exact Finset.le_sup_of_le
        (b := eJ.symm j) (Set.mem_toFinset.2 (show eJ.symm j ∈
          eJ ⁻¹' (S : Set (JoinIrreducibles L)) from hjS)) le_rfl

end FiniteCombinatorics.Poset
