import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.BaseChange
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ExtCharacterization
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.FlatBaseChange

/-! DP-08: grade under flat and faithfully flat scalar extension.
The proof uses the regular-length definition. Flatness preserves weak
regularity; if properness is lost, the target grade is infinity.
For equality, a maximal regular sequence remains maximal: its terminal
quotient has a nonzero element annihilated by I, and faithful flatness
preserves this element as `1 ⊗ m`, annihilated by the extended ideal. -/

universe u
open scoped TensorProduct Pointwise
open RingTheory.Sequence
namespace AdvCommAlg.Depth

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

lemma map_smul_top_eq_top (I : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M]
    (hI : I • (⊤ : Submodule R M) = ⊤) :
    I.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] M)) = ⊤ := by
  have : Subsingleton (M ⧸ (I • (⊤ : Submodule R M))) :=
    Submodule.Quotient.subsingleton_iff.mpr hI
  have : Subsingleton ((S ⊗[R] M) ⧸
      (I.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] M)))) :=
    (TensorProduct.tensorQuotMapSMulEquivTensorQuot M S I).injective.subsingleton
  exact Submodule.Quotient.subsingleton_iff.mp inferInstance

/-- Flat scalar extension can only increase grade. -/
theorem grade_le_flatBaseChange [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Flat R S] (I : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    grade I M ≤ grade (I.map (algebraMap R S)) (S ⊗[R] M) := by
  by_cases hJ : I.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] M)) = ⊤
  · rw [grade_of_smul_eq_top _ _ hJ]
    exact le_top
  have hI : I • (⊤ : Submodule R M) ≠ ⊤ := fun h => hJ (map_smul_top_eq_top I M h)
  rw [grade_of_smul_ne_top I M hI, grade_of_smul_ne_top _ _ hJ]
  apply sSup_le
  rintro _ ⟨xs, hxs, hmem, rfl⟩
  have hmemS : ∀ a ∈ xs.map (algebraMap R S), a ∈ I.map (algebraMap R S) := by
    intro a ha
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
    exact Ideal.mem_map_of_mem _ (hmem r hr)
  have hproper : (⊤ : Submodule S (S ⊗[R] M)) ≠
      Ideal.ofList (xs.map (algebraMap R S)) • ⊤ := by
    apply Ne.symm
    exact ne_top_of_le_ne_top hJ (Submodule.smul_mono_left (Ideal.span_le.mpr hmemS))
  have hreg : IsRegular (S ⊗[R] M) (xs.map (algebraMap R S)) :=
    ⟨hxs.toIsWeaklyRegular.of_flat_of_isBaseChange
      (IsBaseChange.of_equiv (f := TensorProduct.mk R S M 1)
        (LinearEquiv.refl S _) (fun _ => rfl)), hproper⟩
  have hle := le_sSup (s := { (ys.length : ℕ∞) | (ys : List S)
    (_ : RegularSequence.Regular (S ⊗[R] M) ys) (_ : ∀ a ∈ ys, a ∈ I.map (algebraMap R S)) })
    ⟨xs.map (algebraMap R S), hreg, hmemS, rfl⟩
  simpa only [List.length_map] using hle


/-- A grade-zero witness survives as a nonzero pure tensor under faithful flatness. -/
lemma grade_zero_faithfullyFlatBaseChange [IsNoetherianRing R]
    [Module.FaithfullyFlat R S] (I : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) (hg : grade I M = 0) :
    ∀ a ∈ I.map (algebraMap R S), ¬ IsSMulRegular (S ⊗[R] M) a := by
  obtain ⟨m, hm, hmn⟩ := (Submodule.ne_bot_iff _).mp
    ((grade_zero_iff_annihilator_ne_bot I M hI).mp hg)
  have hkill : I.map (algebraMap R S) ≤
      (Submodule.span S {(1 : S) ⊗ₜ[R] m}).annihilator := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change (algebraMap R S) r ∈ (Submodule.span S {(1 : S) ⊗ₜ[R] m}).annihilator
    rw [Submodule.mem_annihilator_span_singleton]
    have hz := (Submodule.mem_torsionBySet_iff _ _).mp hm ⟨r, hr⟩
    calc
      _ = ((algebraMap R S r) • (1 : S)) ⊗ₜ[R] m := TensorProduct.smul_tmul' _ _ _
      _ = (r • (1 : S)) ⊗ₜ[R] m := by rw [algebraMap_smul]
      _ = (1 : S) ⊗ₜ[R] (r • m) := TensorProduct.smul_tmul _ _ _
      _ = 0 := by rw [hz, TensorProduct.tmul_zero]
  intro a ha hreg
  have hz : a • ((1 : S) ⊗ₜ[R] m) = 0 := by
    simpa only [Submodule.mem_annihilator_span_singleton] using hkill ha
  exact hmn ((Module.FaithfullyFlat.one_tmul_eq_zero_iff R M (A := S) m).mp
    (hreg.right_eq_zero_of_smul hz))


/-- Faithful scalar extension preserves maximality, even against elements of `IS`
which do not come from elements of `I`. -/
lemma maximalRegular_faithfullyFlatBaseChange [IsNoetherianRing R]
    [IsNoetherianRing S] [Module.FaithfullyFlat R S]
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) (xs : List R)
    (hmax : MaximalRegular I M xs) :
    MaximalRegular (I.map (algebraMap R S)) (S ⊗[R] M) (xs.map (algebraMap R S)) := by
  induction xs generalizing M with
  | nil =>
    have hg : grade I M = 0 := by
      apply (grade_zero_iff_no_regular I M hI).mpr
      intro a ha hreg
      apply hmax.2.2 a ha
      refine ⟨(isWeaklyRegular_singleton_iff M a).mpr hreg, ?_⟩
      exact (ne_top_of_le_ne_top hI (Submodule.smul_mono_left
        (Ideal.span_le.mpr (by simpa using ha)))).symm
    refine ⟨hmax.1.of_faithfullyFlat_of_isBaseChange
      (IsBaseChange.of_equiv (f := TensorProduct.mk R S M 1)
        (LinearEquiv.refl S _) (fun _ => rfl)), ?_, ?_⟩
    · simp
    · intro a ha hreg
      exact grade_zero_faithfullyFlatBaseChange I M hI hg a ha
        ((isWeaklyRegular_singleton_iff (S ⊗[R] M) a).mp hreg.toIsWeaklyRegular)
  | cons a xs ih =>
    have hreg := (isRegular_cons_iff M a xs).mp hmax.1
    have ha : a ∈ I := hmax.2.1 a (by simp)
    have htail : MaximalRegular I (QuotSMulTop a M) xs := by
      refine ⟨hreg.2, fun b hb => hmax.2.1 b (by simp [hb]), ?_⟩
      intro b hb hbad
      exact hmax.2.2 b hb ((isRegular_cons_iff M a (xs ++ [b])).mpr ⟨hreg.1, hbad⟩)
    have htailS := ih (QuotSMulTop a M)
      (ideal_smul_quotSMulTop_ne_top I M a ha hI) htail
    refine ⟨hmax.1.of_faithfullyFlat_of_isBaseChange
      (IsBaseChange.of_equiv (f := TensorProduct.mk R S M 1)
        (LinearEquiv.refl S _) (fun _ => rfl)), ?_, ?_⟩
    · intro b hb
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
      exact Ideal.mem_map_of_mem _ (hmax.2.1 r hr)
    · intro b hb hbad
      apply htailS.2.2 b hb
      have hbadTail := (isRegular_cons_iff (S ⊗[R] M) ((algebraMap R S) a)
        (xs.map (algebraMap R S) ++ [b])).mp (by simpa using hbad)
      exact ((QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop a M S).isRegular_congr _).mp
        hbadTail.2

/-- Faithfully flat scalar extension preserves grade, including infinite grade. -/
theorem grade_eq_faithfullyFlatBaseChange [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.FaithfullyFlat R S] (I : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    grade I M = grade (I.map (algebraMap R S)) (S ⊗[R] M) := by
  by_cases hI : I • (⊤ : Submodule R M) = ⊤
  · rw [grade_of_smul_eq_top I M hI,
      grade_of_smul_eq_top _ _ (map_smul_top_eq_top I M hI)]
  have hnontrivial : Nontrivial M := by
    by_contra hn
    have : Subsingleton M := not_nontrivial_iff_subsingleton.mp hn
    exact hI (Subsingleton.elim _ _)
  have hJ : I.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] M)) ≠ ⊤ :=
    (IsBaseChange.of_equiv (f := TensorProduct.mk R S M 1)
      (LinearEquiv.refl S _) (fun _ => rfl)).map_smul_top_ne_top_iff_of_faithfullyFlat R M I |>.mpr hI
  obtain ⟨xs, hmax⟩ := exists_maximalRegular_extension I M hI []
    ((RegularSequence.regular_nil_iff M).mpr hnontrivial) (by simp)
  have hlen := maximalRegular_length_eq_grade I M hI xs (by simpa using hmax)
  have hlenS := maximalRegular_length_eq_grade (I.map (algebraMap R S)) (S ⊗[R] M)
    hJ (xs.map (algebraMap R S))
    (maximalRegular_faithfullyFlatBaseChange I M hI xs (by simpa using hmax))
  simpa only [List.length_map, hlen] using hlenS

end AdvCommAlg.Depth
