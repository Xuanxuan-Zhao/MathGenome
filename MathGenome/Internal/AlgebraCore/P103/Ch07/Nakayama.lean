import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.Nakayama
import MathGenome.Internal.AlgebraCore.P103.Ch03.Nakayama
import MathGenome.Internal.AlgebraCore.P103.Ch03.JacobsonRadical

namespace P103.Ch07.Nakayama

open P103.Specs.Ch07.Nakayama

theorem maximal_intersection : maximal_intersectionType := by
  intro R _
  exact P103.Ch03.JacobsonRadical.maximal_intersection R

theorem one_sub_isUnit : one_sub_isUnitType := by
  intro R _ a ha
  exact P103.Ch03.JacobsonRadical.one_sub_isUnit R a ha

theorem local_nonunits : local_nonunitsType := by
  intro R _ _ m hm
  have heq := IsLocalRing.eq_maximalIdeal hm
  refine ⟨hm.ne_top, ?_, ?_, ?_⟩
  · rw [heq]
    rfl
  · intro J hJ
    rw [heq]
    exact IsLocalRing.le_maximalIdeal hJ
  · intro J hJ
    exact (IsLocalRing.eq_maximalIdeal hJ).trans heq.symm

theorem local_iff_unique_maximal : local_iff_unique_maximalType := by
  intro R _
  constructor
  · intro h
    let := h
    exact IsLocalRing.maximal_ideal_unique R
  · exact IsLocalRing.of_unique_max_ideal

theorem nonunits_ideal_unique : nonunits_ideal_uniqueType := by
  intro R _ m hm hcarrier
  have : Nontrivial R := nontrivial_of_ne (0 : R) 1 (by
    intro h
    apply hm
    exact m.eq_top_iff_one.mpr (h ▸ m.zero_mem))
  have : IsLocalRing R := IsLocalRing.of_nonunits_add (by
    intro a b ha hb
    rw [← hcarrier] at ha hb ⊢
    exact m.add_mem ha hb)
  have heq : m = IsLocalRing.maximalIdeal R := by
    ext a
    change a ∈ m ↔ a ∈ nonunits R
    rw [← hcarrier]
    rfl
  have hmax : m.IsMaximal := heq ▸ IsLocalRing.maximalIdeal.isMaximal R
  have hlocal := local_nonunits R m hmax
  exact ⟨inferInstance, hmax, hlocal.2.2.1, hlocal.2.2.2⟩

theorem local_iff_nonunits_ideal : local_iff_nonunits_idealType := by
  intro R _
  constructor
  · intro h
    let := h
    exact ⟨IsLocalRing.maximalIdeal R,
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top, rfl⟩
  · rintro ⟨m, hm, hc⟩
    exact (nonunits_ideal_unique R m hm hc).1

/-- Specialize the accepted arbitrary-ring theorem to commutative rings. -/
theorem sup_iff : sup_iffType := by
  intro R M _ _ _ _ I hI N
  exact P103.Ch03.Nakayama.sup_iff R M I hI N

theorem eq_zero : eq_zeroType := by
  intro R M _ _ _ _ I hI hIM
  exact P103.Ch03.Nakayama.eq_zero R M I hI hIM

theorem generators_lift : generators_liftType := by
  intro R M _ _ _ _ I hI ι g x hx hg
  exact P103.Ch03.Nakayama.generators_lift R M I hI ι g x hx hg

/-- The library finite-generation argument gives r ∈ 1+I with rM=0.
Writing a=1-r gives the precise scalar used in Krull intersection. -/
theorem determinant_trick : determinant_trickType := by
  intro R M _ _ _ _ I hIM
  obtain ⟨r, hr, hkill⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
      I (⊤ : Submodule R M) Module.Finite.fg_top hIM.ge
  refine ⟨1 - r, ?_, ?_⟩
  · simpa only [neg_sub] using I.neg_mem hr
  · intro m
    simpa only [sub_sub_cancel] using hkill m Submodule.mem_top

end P103.Ch07.Nakayama
