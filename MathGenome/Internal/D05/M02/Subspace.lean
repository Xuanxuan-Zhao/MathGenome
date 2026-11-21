import MathGenome.Internal.Specs.D05.M02.Subspace

/-! K05.02.subspace: the subspace criterion and its inherited structures. -/

namespace D05.M02.Subspace

theorem subspace_iff_closed : Specs.D05.M02.Subspace.subspace_iff_closed := by
  intro K V _ _ _ U
  constructor
  · rintro ⟨S, rfl⟩
    exact ⟨S.zero_mem, fun _ _ hu hv => S.add_mem hu hv,
      fun a _ hu => S.smul_mem a hu⟩
  · rintro ⟨hzero, hadd, hsmul⟩
    refine ⟨{
      carrier := U
      zero_mem' := hzero
      add_mem' := ?_
      smul_mem' := ?_
    }, rfl⟩
    · intro u v hu hv
      exact hadd u v hu hv
    · intro a u hu
      exact hsmul a u hu

theorem neg_mem_of_smul_closed : Specs.D05.M02.Subspace.neg_mem_of_smul_closed := by
  intro K V _ _ _ U hsmul u hu
  simpa only [neg_one_smul] using hsmul (-1 : K) u hu

theorem inherited_vector_space : Specs.D05.M02.Subspace.inherited_vector_space := by
  intro K V _ _ _ S
  exact ⟨⟨inferInstance⟩, ⟨inferInstance⟩, rfl,
    fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem linear_inclusion : Specs.D05.M02.Subspace.linear_inclusion := by
  intro K V _ _ _ S
  exact ⟨S.subtype, fun _ => rfl, Subtype.coe_injective⟩

end D05.M02.Subspace
