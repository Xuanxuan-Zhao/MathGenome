import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.CompletedFlatnessLocality
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! Theorem 7.5: flatness, faithful flatness, maximal fibers and locality.
The library flatness theorem uses the ideal criterion, exactness of completion
and its tensor comparison. The Jacobson assertion uses the convergent geometric
series in the complete ring. Fibers containing I are obtained by composing
evaluation modulo I with reduction modulo m; the other fibers vanish because
any maximal ideal over the extended m would contract to m and contain I.
-/
universe u

namespace P103.Ch07.CompletedFlatnessLocality
noncomputable section
open P103.Adic P103.Specs.Ch07.CompletedQuotients
open P103.Specs.Ch07.CompletedFlatnessLocality

theorem flat : flatType.{u} := by
  intro R _ _ I
  exact AdicCompletion.flat_of_isNoetherian I

theorem extendedIdeal_le_jacobson : extendedIdeal_le_jacobsonType.{u} := by
  intro R _ _ I
  let := AdicCompletion.isAdicComplete_self I I.fg_of_isNoetherianRing
  simpa only [Ideal.jacobson_bot] using
    IsAdicComplete.le_jacobson_bot (extendedIdeal I)

/-- Reduction modulo any ideal containing I, not only maximal ideals. -/
def reduction {R : Type u} [CommRing R] (I m : Ideal R) (h : I ≤ m) :
    Completion I R →+* (R ⧸ m) :=
  (Ideal.Quotient.factor h).comp (AdicCompletion.evalOneₐ I).toRingHom

lemma reduction_of {R : Type u} [CommRing R] (I m : Ideal R) (h : I ≤ m) (r : R) :
    reduction I m h (algebraMap R (Completion I R) r) = Ideal.Quotient.mk m r :=
  rfl

lemma reduction_surjective {R : Type u} [CommRing R] (I m : Ideal R) (h : I ≤ m) :
    Function.Surjective (reduction I m h) :=
  (Ideal.Quotient.factor_surjective h).comp (AdicCompletion.evalOneₐ_surjective I)

lemma reduction_kernel {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I m : Ideal R) (h : I ≤ m) :
    RingHom.ker (reduction I m h) = m.map (algebraMap R (Completion I R)) := by
  have hk : RingHom.ker (Ideal.Quotient.factor h) = m.map (Ideal.Quotient.mk I) := by
    ext x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [RingHom.mem_ker, Ideal.Quotient.factor_mk,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr h]
  rw [reduction, ← RingHom.comap_ker, hk]
  rw [← AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk,
    ← Ideal.map_map, Ideal.comap_map_of_surjective'
      (AdicCompletion.evalOneₐ I).toRingHom (AdicCompletion.evalOneₐ_surjective I),
    AdicCompletion.ker_evalOneₐ_eq_map I I.fg_of_isNoetherianRing,
    sup_eq_left]
  exact Ideal.map_mono h

theorem maximal_fiber : maximal_fiberType.{u} := by
  intro R _ _ I m _ h
  let e := (Ideal.quotEquivOfEq (reduction_kernel I m h).symm).trans
    (RingHom.quotientKerEquivOfSurjective (reduction_surjective I m h))
  exact ⟨e, fun _ => rfl⟩

/-- A maximal ideal not containing I extends to the unit ideal. -/
lemma extension_eq_top_of_not_le {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I m : Ideal R) (hm : m.IsMaximal) (h : ¬ I ≤ m) :
    m.map (algebraMap R (Completion I R)) = ⊤ := by
  by_contra hproper
  obtain ⟨n, hn, hmn⟩ := Ideal.exists_le_maximal _ hproper
  let := hn
  have hc : m = n.comap (algebraMap R (Completion I R)) :=
    hm.eq_of_le (Ideal.comap_ne_top _ hn.ne_top)
      (Ideal.map_le_iff_le_comap.mp hmn)
  have hi : I ≤ n.comap (algebraMap R (Completion I R)) :=
    Ideal.map_le_iff_le_comap.mp
      ((extendedIdeal_le_jacobson R I).trans (Ring.jacobson_le_of_isMaximal n))
  exact h (hc.symm ▸ hi)

theorem maximal_fiber_zero : maximal_fiber_zeroType.{u} := by
  intro R _ _ I m hm h
  exact Ideal.Quotient.subsingleton_iff.mpr (extension_eq_top_of_not_le I m hm h)

theorem faithfullyFlat_iff : faithfullyFlat_iffType.{u} := by
  intro R _ _ I
  constructor
  · intro hf
    rw [Ring.jacobson_eq_sInf_isMaximal]
    apply le_sInf
    intro m hm
    by_contra h
    have ht := extension_eq_top_of_not_le I m hm h
    apply hf.submodule_ne_top hm
    simp only [Ideal.smul_top_eq_map, ht, Submodule.restrictScalars_top]
  · intro hi
    refine { toFlat := flat R I, submodule_ne_top := ?_ }
    intro m hm ht
    let := hm
    have him : I ≤ m := hi.trans (Ring.jacobson_le_of_isMaximal m)
    have hm' := AdicCompletion.isMaximal_map_of_le I m him I.fg_of_isNoetherianRing
    apply hm'.ne_top
    simpa only [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] using ht

theorem local_ring : localType.{u} := by
  intro R _ _ _ m hm
  have he : m = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hm
  subst m
  refine ⟨inferInstance, ?_, ?_⟩
  · exact AdicCompletion.isMaximal_map_of_le _ _ le_rfl
      (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
  · intro n hn
    exact (IsLocalRing.eq_maximalIdeal hn).trans AdicCompletion.maximalIdeal_eq_map

theorem residueField : residueFieldType.{u} := by
  intro R _ _ _ m hm
  obtain ⟨e, he⟩ := maximal_fiber R m m hm le_rfl
  refine ⟨e.symm, fun r => ?_⟩
  exact e.symm_apply_eq.mpr (he r).symm

theorem zeroIdeal : zeroIdealType.{u} := by
  intro R _
  exact ⟨(AdicCompletion.ofAlgEquiv (⊥ : Ideal R)).toRingEquiv, fun _ => rfl⟩

theorem topIdeal : topIdealType.{u} := by
  intro R _
  exact IsHausdorff.subsingleton
    (inferInstance : IsHausdorff (⊤ : Ideal R) (Completion ⊤ R))

end
end P103.Ch07.CompletedFlatnessLocality
