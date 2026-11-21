import MathGenome.Internal.Specs.D05.M02.Independence
import MathGenome.Internal.D05.M02.Span

/-! K05.02.independence: finite-support relations and indexed subfamilies. -/

namespace D05.M02.Independence

/-- Canonical linear independence; the index type retains repeated occurrences. -/
abbrev independent (K V I : Type*) [Field K] [AddCommGroup V] [Module K V]
    (v : I → V) : Prop := LinearIndependent K v

theorem independent_iff_finsupp_relation :
    Specs.D05.M02.Independence.independent_iff_finsupp_relation := by
  intro K V I _ _ _ v
  rw [linearIndependent_iff]
  constructor
  · intro h a ha i
    have hzero : a = 0 := h a ha
    simp only [hzero, Finsupp.zero_apply]
  · intro h a ha
    exact Finsupp.ext (h a ha)

theorem independent_iff_finset_relation :
    Specs.D05.M02.Independence.independent_iff_finset_relation := by
  intro K V I _ _ _ v
  exact linearIndependent_iff'

theorem empty_family : Specs.D05.M02.Independence.empty_family := by
  intro K V I _ _ _ _ v
  exact linearIndependent_empty_type

theorem zero_entry_relation : Specs.D05.M02.Independence.zero_entry_relation := by
  intro K V I _ _ _ v j hj
  classical
  refine ⟨Finsupp.single j 1, ?_, ?_, ?_, ?_⟩
  · simp
  · intro i hi
    simp [hi]
  · change Finsupp.linearCombination K v (Finsupp.single j 1) = 0
    simp [hj]
  · simp

theorem not_independent_of_zero_entry :
    Specs.D05.M02.Independence.not_independent_of_zero_entry := by
  intro K V I _ _ _ v j hj h
  exact h.ne_zero j hj

theorem repeated_entry_relation :
    Specs.D05.M02.Independence.repeated_entry_relation := by
  intro K V I _ _ _ v i j hij hv
  classical
  let a : I →₀ K := Finsupp.single i 1 - Finsupp.single j 1
  have hai : a i = 1 := by simp [a, hij]
  refine ⟨a, hai, ?_, ?_, ?_, ?_⟩
  · simp [a, Ne.symm hij]
  · intro k hki hkj
    simp [a, hki, hkj]
  · change Finsupp.linearCombination K v a = 0
    simp [a, hv]
  · intro ha
    have : (0 : K) = 1 := by simpa only [ha, Finsupp.zero_apply] using hai
    exact zero_ne_one this

theorem not_independent_of_repeated_entry :
    Specs.D05.M02.Independence.not_independent_of_repeated_entry := by
  intro K V I _ _ _ v i j hij hv h
  exact hij (h.injective hv)

theorem subfamily : Specs.D05.M02.Independence.subfamily := by
  intro K V I J _ _ _ v f hf hv
  exact hv.comp f hf

theorem restriction : Specs.D05.M02.Independence.restriction := by
  intro K V I _ _ _ v S hv
  exact hv.comp Subtype.val Subtype.val_injective

theorem dependent_iff_mem_span_others :
    Specs.D05.M02.Independence.dependent_iff_mem_span_others := by
  intro K V I _ _ _ v
  classical
  simp only [linearIndependent_iff_notMem_span, not_forall, not_not]

/-- Solve a nontrivial relation for an entry with nonzero coefficient. Conversely,
a combination of the other indexed entries contradicts the span criterion. -/
theorem finite_list_dependent_iff :
    Specs.D05.M02.Independence.finite_list_dependent_iff := by
  intro K V _ _ _ n v
  classical
  constructor
  · intro hv
    obtain ⟨c, hc, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hv
    refine ⟨j, fun i => -(c j)⁻¹ * c i, ?_⟩
    have hrel : c j • v j + ∑ i ∈ Finset.univ.erase j, c i • v i = 0 := by
      rw [Finset.add_sum_erase Finset.univ (fun i => c i • v i) (Finset.mem_univ j)]
      exact hc
    have hsolve : c j • v j = -(∑ i ∈ Finset.univ.erase j, c i • v i) :=
      eq_neg_of_add_eq_zero_left hrel
    calc
      v j = (c j)⁻¹ • (c j • v j) := by
        rw [smul_smul, inv_mul_cancel₀ hj, one_smul]
      _ = ∑ i ∈ Finset.univ.erase j, (-(c j)⁻¹ * c i) • v i := by
        rw [hsolve]
        simp only [smul_neg, Finset.smul_sum, smul_smul, neg_mul, neg_smul,
          Finset.sum_neg_distrib]
  · rintro ⟨j, a, ha⟩
    apply dependent_iff_mem_span_others v |>.mpr
    refine ⟨j, ?_⟩
    rw [ha]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨i, ?_, rfl⟩
    simpa only [Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and] using
      (Finset.mem_erase.mp hi).1

end D05.M02.Independence
