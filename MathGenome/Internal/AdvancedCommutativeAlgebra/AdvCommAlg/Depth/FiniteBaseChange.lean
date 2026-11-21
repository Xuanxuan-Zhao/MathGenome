import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.LocalDetection
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.FiniteBaseChange

/-! Finite changes of rings, DP-08. A maximal R-regular list is maximal over S:
its terminal quotient has a nonzero element annihilated by I, hence also by IS.
This proves the grade comparison including the infinite case. -/
universe u
open scoped Pointwise
open RingTheory.Sequence
namespace AdvCommAlg.Depth

variable {R S : Type u} [CommRing R] [CommRing S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S] [Module.Finite R S]
variable (N : Type u) [AddCommGroup N] [Module R N] [Module S N]
variable [IsScalarTower R S N] [Module.Finite S N]

theorem grade_finite_algebra (I : Ideal R) :
    grade I N = grade (I.map (algebraMap R S)) N := by
  have : Module.Finite R N := Module.Finite.trans S N
  have htop : I.map (algebraMap R S) • (⊤ : Submodule S N) = ⊤ ↔
      I • (⊤ : Submodule R N) = ⊤ := by
    rw [← Submodule.restrictScalars_eq_top_iff R,
      Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  by_cases hI : I • (⊤ : Submodule R N) = ⊤
  · rw [grade_of_smul_eq_top _ _ hI, grade_of_smul_eq_top _ _ (htop.mpr hI)]
  have : Nontrivial N := by
    by_contra h
    have := not_nontrivial_iff_subsingleton.mp h
    exact hI (Subsingleton.elim _ _)
  obtain ⟨xs, hmax⟩ := exists_maximalRegular_extension I N hI []
    (IsRegular.nil R N) (by simp)
  simp only [List.nil_append] at hmax
  let ys := xs.map (algebraMap R S)
  let P : Submodule S N := Ideal.ofList ys • ⊤
  have hP : P.restrictScalars R = Ideal.ofList xs • (⊤ : Submodule R N) := by
    simp only [P, ys, ← Ideal.map_ofList, Ideal.smul_restrictScalars,
      Submodule.restrictScalars_top]
  let Q := N ⧸ (Ideal.ofList xs • (⊤ : Submodule R N))
  let U := N ⧸ P
  let e : Q ≃ₗ[R] U := (Submodule.quotEquivOfEq _ _ hP.symm).trans
    (Submodule.Quotient.restrictScalarsEquiv R P)
  have hQI : I • (⊤ : Submodule R Q) ≠ ⊤ :=
    ideal_smul_listQuotient_ne_top N I hI xs hmax.2.1
  have hz : grade I Q = 0 := by
    rw [grade_quotient_regular N I hI xs hmax.1 hmax.2.1,
      ← maximalRegular_length_eq_grade I N hI xs hmax]
    simp
  have ht := (grade_zero_iff_annihilator_ne_bot I Q hQI).mp hz
  obtain ⟨x, hx, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ht
  have hkill : I.map (algebraMap R S) ≤ (⊥ : Submodule S U).colon {e x} := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, Submodule.mem_bot,
      algebraMap_smul, ← e.map_smul]
    exact congrArg e ((Submodule.mem_torsionBySet_iff _ _).mp hx ⟨a, ha⟩) |>.trans e.map_zero
  have hmaxS : MaximalRegular (I.map (algebraMap R S)) N ys := by
    refine ⟨(regular_map_algebraMap_iff N xs).mpr hmax.1, ?_, ?_⟩
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact Ideal.mem_map_of_mem _ (hmax.2.1 b hb)
    · intro a ha hreg
      have hr := ((regular_append_iff N ys [a]).mp hreg).2.toIsWeaklyRegular
      have hinj : IsSMulRegular U a := (isWeaklyRegular_singleton_iff U a).mp hr
      have hezero : e x = 0 := hinj.right_eq_zero_of_smul (by
        simpa only [Submodule.mem_colon_singleton, Submodule.mem_bot] using hkill ha)
      exact hxne (e.injective (hezero.trans e.map_zero.symm))
  rw [← maximalRegular_length_eq_grade I N hI xs hmax,
    ← maximalRegular_length_eq_grade _ N (mt htop.mp hI) ys hmaxS]
  simp [ys]

omit [IsNoetherianRing R] [IsNoetherianRing S] in
/-- In a finite algebra over a local ring, the primes containing mS are
exactly the maximal ideals. This also covers the zero algebra. -/
lemma map_maximal_le_iff [IsLocalRing R] (p : PrimeSpectrum S) :
    (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ p.asIdeal ↔
      p.asIdeal.IsMaximal := by
  rw [Ideal.map_le_iff_le_comap]
  constructor
  · intro h
    have he : IsLocalRing.maximalIdeal R = p.asIdeal.under R :=
      (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le
        (Ideal.comap_ne_top _ p.isPrime.ne_top) h
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under p.asIdeal
      (he ▸ IsLocalRing.maximalIdeal.isMaximal R)
  · intro h
    let := h
    have he := IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) p.asIdeal)
    exact he.ge

/-- All maximal ideals are included; a localization outside the support has
infinite depth and does not change the infimum. -/
theorem depth_eq_iInf_maximal_localDepth [IsLocalRing R] :
    depth R N = ⨅ (p : PrimeSpectrum S) (_ : p.asIdeal.IsMaximal),
      depth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal N) := by
  rw [depth_eq_grade, grade_finite_algebra (S := S) N, grade_eq_iInf_localDepth N]
  simp_rw [map_maximal_le_iff (R := R)]
  apply le_antisymm
  · apply le_iInf₂
    intro p hp
    by_cases hs : p ∈ Module.support S N
    · exact iInf_le_of_le p (iInf_le_of_le hp (iInf_le _ hs))
    · have := Module.notMem_support_iff.mp hs
      rw [depth_eq_top_of_subsingleton]
      exact le_top
  · apply le_iInf
    intro p
    apply le_iInf
    intro hp
    apply le_iInf
    intro _
    exact iInf_le_of_le p (iInf_le _ hp)

/-- If S is nonzero the infimum above is attained, including when N = 0. -/
theorem exists_maximal_localDepth_eq_depth [IsLocalRing R] [Nontrivial S] :
    ∃ p : PrimeSpectrum S, p.asIdeal.IsMaximal ∧
      depth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal N) =
        depth R N := by
  let T := {p : PrimeSpectrum S // p.asIdeal.IsMaximal}
  have : Nonempty T := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (α := S)
    exact ⟨⟨⟨m, hm.isPrime⟩, hm⟩⟩
  obtain ⟨p, hp⟩ := ENat.exists_eq_iInf (fun p : T =>
    depth (Localization.AtPrime p.val.asIdeal) (LocalizedModule.AtPrime p.val.asIdeal N))
  refine ⟨p.val, p.property, ?_⟩
  rw [depth_eq_iInf_maximal_localDepth (S := S) N]
  simpa only [T, iInf_subtype] using hp

end AdvCommAlg.Depth
