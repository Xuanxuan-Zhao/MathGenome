import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ExtCharacterization
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.RegularQuotient

/-! Grade under regular quotients and quotient scalars (DP-05). -/

universe u v w
open scoped Pointwise
open RingTheory.Sequence
namespace AdvCommAlg.Depth

section Scalars
variable {R : Type u} {S : Type w} [CommRing R] [CommRing S] [Algebra R S]
variable (U : Type v) [AddCommGroup U] [Module R U] [Module S U]
variable [IsScalarTower R S U]

lemma regular_map_algebraMap_iff (xs : List R) :
    IsRegular U (xs.map (algebraMap R S)) ↔ IsRegular U xs := by
  exact (AddEquiv.refl U).isRegular_congr <| List.forall₂_map_left_iff.mpr <|
    List.forall₂_same.mpr fun r _ => algebraMap_smul S r

theorem grade_map_of_surjective (hf : Function.Surjective (algebraMap R S))
    (I : Ideal R) : grade (I.map (algebraMap R S)) U = grade I U := by
  classical
  have htop : I.map (algebraMap R S) • (⊤ : Submodule S U) = ⊤ ↔
      I • (⊤ : Submodule R U) = ⊤ := by
    rw [← Submodule.restrictScalars_eq_top_iff R,
      Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  by_cases hI : I • (⊤ : Submodule R U) = ⊤
  · rw [grade_of_smul_eq_top _ _ hI, grade_of_smul_eq_top _ _ (htop.mpr hI)]
  · rw [grade_of_smul_ne_top _ _ hI,
      grade_of_smul_ne_top _ _ (mt htop.mp hI)]
    congr 1
    ext n
    constructor
    · rintro ⟨ys, hy, hmem, rfl⟩
      have hlift : ∀ y : {y // y ∈ ys}, ∃ x : R, x ∈ I ∧ algebraMap R S x = y :=
        fun y => (Ideal.mem_map_iff_of_surjective _ hf).mp (hmem y y.property)
      choose f hfI hfe using hlift
      let xs := ys.attach.map f
      have he : xs.map (algebraMap R S) = ys := by
        dsimp [xs]
        rw [List.map_map]
        simpa only [Function.comp_def, hfe] using ys.attach_map_subtype_val
      refine ⟨xs, (regular_map_algebraMap_iff U xs).mp (he.symm ▸ hy), ?_, ?_⟩
      · intro x hx
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
        exact hfI y
      · simp [xs]
    · rintro ⟨xs, hx, hmem, rfl⟩
      refine ⟨xs.map (algebraMap R S), (regular_map_algebraMap_iff U xs).mpr hx, ?_, by simp⟩
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      exact Ideal.mem_map_of_mem _ (hmem x hx)

end Scalars

theorem grade_quotient_scalars {R : Type u} [CommRing R] (A I : Ideal R)
    (U : Type v) [AddCommGroup U] [Module R U]
    (hA : Module.IsTorsionBySet R U A) :
    letI := hA.module
    grade (I.map (Ideal.Quotient.mk A)) U = grade I U := by
  letI := hA.module
  exact grade_map_of_surjective U Ideal.Quotient.mk_surjective I

section RegularQuotient
variable {R : Type u} [CommRing R]
variable (M : Type u) [AddCommGroup M] [Module R M]

lemma regular_append_iff (xs ys : List R) :
    IsRegular M (xs ++ ys) ↔ IsWeaklyRegular M xs ∧
      IsRegular (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) ys := by
  have ht : Ideal.ofList ys • (⊤ : Submodule R (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M))) = ⊤ ↔
      Ideal.ofList (xs ++ ys) • (⊤ : Submodule R M) = ⊤ := by
    rw [← Submodule.comap_injective_of_surjective (Submodule.mkQ_surjective
      (Ideal.ofList xs • (⊤ : Submodule R M))) |>.eq_iff]
    simp only [Submodule.comap_top, Submodule.comap_smul_top_of_surjective _ _
      (Submodule.mkQ_surjective _), Submodule.ker_mkQ, Ideal.ofList_append,
      Submodule.sup_smul, sup_comm]
  simp only [isRegular_iff, isWeaklyRegular_append_iff]
  rw [ne_comm (a := (⊤ : Submodule R M)),
    ne_comm (a := (⊤ : Submodule R (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M))))]
  simp only [ne_eq, ht, and_assoc]

variable [IsNoetherianRing R] [Module.Finite R M]

theorem grade_quotient_regular (I : Ideal R)
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) (xs : List R)
    (hx : IsRegular M xs) (hmem : ∀ x ∈ xs, x ∈ I) :
    grade I (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) = grade I M - xs.length := by
  obtain ⟨ys, hmax⟩ := exists_maximalRegular_extension I M hI xs hx hmem
  let Q := M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)
  have hqI : I • (⊤ : Submodule R Q) ≠ ⊤ := by
    intro he
    apply hI
    have h := congrArg (Submodule.comap (Submodule.mkQ
      (Ideal.ofList xs • (⊤ : Submodule R M)))) he
    have hle : Ideal.ofList xs • (⊤ : Submodule R M) ≤ I • ⊤ :=
      Submodule.smul_mono_left (Ideal.span_le.mpr hmem)
    simpa [Submodule.comap_smul_top_of_surjective I _ (Submodule.mkQ_surjective _),
      sup_eq_left.mpr hle] using h
  have hmaxQ : MaximalRegular I Q ys := by
    refine ⟨((regular_append_iff M xs ys).mp hmax.1).2, ?_, ?_⟩
    · exact fun a ha => hmax.2.1 a (List.mem_append_right xs ha)
    · intro a ha hbad
      exact hmax.2.2 a ha (by
        rw [List.append_assoc]
        exact (regular_append_iff M xs (ys ++ [a])).mpr ⟨hx.toIsWeaklyRegular, hbad⟩)
  rw [← maximalRegular_length_eq_grade I M hI _ hmax,
    ← maximalRegular_length_eq_grade I Q hqI _ hmaxQ, List.length_append, Nat.cast_add]
  simp

theorem grade_regular_quotient (I : Ideal R)
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) (xs : List R)
    (hx : IsRegular M xs) (hmem : ∀ x ∈ xs, x ∈ I) :
    grade (I.map (Ideal.Quotient.mk (Ideal.ofList xs)))
        (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) =
      grade I (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) ∧
    grade I (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) = grade I M - xs.length := by
  exact ⟨grade_map_of_surjective _ Ideal.Quotient.mk_surjective I,
    grade_quotient_regular M I hI xs hx hmem⟩

theorem depth_regular_quotient [IsLocalRing R] (xs : List R)
    (hx : IsRegular M xs) (hmem : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R) :
    letI := regularQuotientLocalRing xs hmem
    depth (R ⧸ Ideal.ofList xs) (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) =
      depth R M - xs.length := by
  letI := regularQuotientLocalRing xs hmem
  letI : Nontrivial M := hx.nontrivial
  have hI : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson _)).symm
  change grade (IsLocalRing.maximalIdeal (R ⧸ Ideal.ofList xs)) _ =
    grade (IsLocalRing.maximalIdeal R) M - xs.length
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (Ideal.ofList xs))
    Ideal.Quotient.mk_surjective]
  exact (grade_regular_quotient M _ hI xs hx hmem).1.trans
    (grade_regular_quotient M _ hI xs hx hmem).2

end RegularQuotient
end AdvCommAlg.Depth
