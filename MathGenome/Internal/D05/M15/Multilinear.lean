import MathGenome.Internal.D05.M03.LinearMap
import MathGenome.Internal.Specs.D05.M15.Multilinear

/-! K05.15.multilinear: slotwise linearity, pointwise structure and finite expansion. -/

namespace D05.M15.Multilinear

open scoped BigOperators

/-- The paper's multilinear maps, using the canonical dependent-family type. -/
abbrev multilinearMap (K I : Type*) (V : I → Type*) (W : Type*) [Field K]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup W] [Module K W] := MultilinearMap K V W

theorem multilinearMap_iff_axioms :
    Specs.D05.M15.Multilinear.multilinearMap_iff_axioms := by
  intro K I V W _ _ _ _ _ _ b
  constructor
  · rintro ⟨B, rfl⟩
    exact ⟨B.map_update_add, B.map_update_smul⟩
  · rintro ⟨hadd, hsmul⟩
    exact ⟨MultilinearMap.mk' b hadd hsmul, rfl⟩

theorem slot_linear : Specs.D05.M15.Multilinear.slot_linear := by
  intro K I V W _ _ _ _ _ _ b m i
  exact ⟨b.toLinearMap m i, fun _ => rfl⟩

theorem pointwise_vector_space : Specs.D05.M15.Multilinear.pointwise_vector_space := by
  intro K I V W _ _ _ _ _
  exact ⟨inferInstance, (fun _ _ _ => rfl), (fun _ _ _ => rfl), (fun _ => rfl)⟩

theorem nullary_equivalence : Specs.D05.M15.Multilinear.nullary_equivalence := by
  intro K I V W _ _ _ _ _ _
  exact ⟨MultilinearMap.constLinearEquivOfIsEmpty (R := K) (S := K) (M₁ := V) (M₂ := W),
    (fun _ _ => rfl), (fun _ => rfl)⟩

theorem map_coord_zero : Specs.D05.M15.Multilinear.map_coord_zero := by
  intro K I V W _ _ _ _ _ b m i hi
  exact b.map_coord_zero i hi

theorem map_zero : Specs.D05.M15.Multilinear.map_zero := by
  intro K I V W _ _ _ _ _ _ b
  exact b.map_zero

theorem map_scalar_product : Specs.D05.M15.Multilinear.map_scalar_product := by
  intro K I V W _ _ _ _ _ _ b a m
  exact b.map_smul_univ a m

theorem map_finite_combination : Specs.D05.M15.Multilinear.map_finite_combination := by
  intro K I V W A _ _ _ _ _ _ b s a e
  classical
  rw [b.map_sum_finset (fun i j => a i j • e i j) s]
  exact Finset.sum_congr rfl (fun r _ => b.map_smul_univ (fun i => a i (r i))
    (fun i => e i (r i)))

end D05.M15.Multilinear
