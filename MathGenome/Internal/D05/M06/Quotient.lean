import MathGenome.Internal.Specs.D05.M06.Quotient

/-! K05.06.quotient: algebraic quotient spaces with their coset formulas. -/

namespace D05.M06.Quotient

/-- The paper's `V/U` is the algebraic quotient by the given submodule. -/
abbrev quotientSpace (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) := V ⧸ U

theorem relation_equivalence : Specs.D05.M06.Quotient.relation_equivalence := by
  intro K V _ _ _ U
  refine ⟨?_, ?_, ?_⟩
  · intro v
    simpa only [sub_self] using U.zero_mem
  · intro v w h
    simpa only [neg_sub] using U.neg_mem h
  · intro v w z hvw hwz
    simpa only [sub_add_sub_cancel] using U.add_mem hvw hwz

theorem relation_bridge : Specs.D05.M06.Quotient.relation_bridge := by
  intro K V _ _ _ U v w
  exact U.quotientRel_def

theorem representative_eq_iff : Specs.D05.M06.Quotient.representative_eq_iff := by
  intro K V _ _ _ U v w
  exact Submodule.Quotient.eq U

theorem class_eq_coset : Specs.D05.M06.Quotient.class_eq_coset := by
  intro K V _ _ _ U v
  apply Set.ext
  intro w
  change (Submodule.Quotient.mk w : V ⧸ U) = Submodule.Quotient.mk v ↔ _
  rw [Submodule.Quotient.eq]
  constructor
  · intro h
    refine ⟨w - v, h, ?_⟩
    rw [add_comm v, sub_add_cancel]
  · rintro ⟨u, hu, rfl⟩
    simpa only [add_sub_cancel_left] using hu

theorem addition_well_defined : Specs.D05.M06.Quotient.addition_well_defined := by
  intro K V _ _ _ U v v' w w' hv hw
  simpa only [sub_add_sub_comm] using U.add_mem hv hw

theorem smul_well_defined : Specs.D05.M06.Quotient.smul_well_defined := by
  intro K V _ _ _ U a v v' h
  simpa only [smul_sub] using U.smul_mem a h

theorem quotient_operations : Specs.D05.M06.Quotient.quotient_operations := by
  intro K V _ _ _ U
  exact ⟨fun v w => (Submodule.Quotient.mk_add U).symm,
    fun a v => (Submodule.Quotient.mk_smul U a v).symm⟩

theorem quotient_vector_space : Specs.D05.M06.Quotient.quotient_vector_space := by
  intro K V _ _ _ U
  exact ⟨⟨inferInstance⟩, ⟨inferInstance⟩,
    fun a x y => smul_add a x y, fun a b x => add_smul a b x,
    fun a b x => mul_smul a b x, fun x => one_smul K x⟩

theorem zero_coset : Specs.D05.M06.Quotient.zero_coset := by
  intro K V _ _ _ U
  refine ⟨Submodule.Quotient.mk_zero U, ?_⟩
  exact Set.ext fun _ => Submodule.Quotient.mk_eq_zero U

theorem neg_coset : Specs.D05.M06.Quotient.neg_coset := by
  intro K V _ _ _ U v
  exact (Submodule.Quotient.mk_neg U).symm

theorem every_class_representative : Specs.D05.M06.Quotient.every_class_representative := by
  intro K V _ _ _ U x
  exact Submodule.Quotient.mk_surjective U x

end D05.M06.Quotient
