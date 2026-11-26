import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.GradeFromLocalCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedTorsion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalCohomologyBaseChange
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.LocalDetection
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.Linear
import Mathlib.RingTheory.Regular.Category

open CategoryTheory HomologicalComplex
open scoped Pointwise

namespace CommutativeAlgebraNotes

universe u

variable {R : Type u} [CommRing R]

/-- Scalar multiplication on a module induces the same scalar on local cohomology. -/
private theorem localCohomology_map_smul_id (I : Ideal R) (M : ModuleCat.{u} R)
    (n : ℕ) (a : R) :
    (localCohomology I (n : ℤ)).map (a • 𝟙 M) =
      a • 𝟙 ((localCohomology I (n : ℤ)).obj M) := by
  let F := idealTorsionFunctor.{u} I
  let P := injectiveResolution M
  let K := (F.mapHomologicalComplex (.up ℕ)).obj P.cocomplex
  let e : (F.rightDerived n).obj M ⟶ K.homology n := (P.isoRightDerivedObj F n).hom
  let i : M ⟶ P.cocomplex.X 0 := P.ι.f 0
  have hι : i ≫ (a • 𝟙 P.cocomplex).f 0 = (a • 𝟙 M) ≫ i := by
    change i ≫ (a • 𝟙 _) = (a • 𝟙 M) ≫ i
    rw [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]
  have hK : (F.mapHomologicalComplex (.up ℕ)).map (a • 𝟙 P.cocomplex) =
      a • 𝟙 K := by
    apply HomologicalComplex.hom_ext
    intro i
    apply ModuleCat.hom_ext
    ext x
    rfl
  have hH : (homologyFunctor (ModuleCat.{u} R) (.up ℕ) n).map (a • 𝟙 K) =
      a • 𝟙 (K.homology n) := by
    let G := shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n
    have hG : G.map (a • 𝟙 K) = a • 𝟙 (G.obj K) :=
      ShortComplex.hom_ext _ _ rfl rfl rfl
    change ShortComplex.homologyMap (G.map (a • 𝟙 K)) = _
    rw [hG, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
    rfl
  have he := P.isoRightDerivedObj_hom_naturality (a • 𝟙 M) P _ hι F n
  change (F.rightDerived n).map (a • 𝟙 M) ≫ e =
    e ≫ (homologyFunctor _ _ n).map ((F.mapHomologicalComplex _).map (a • 𝟙 P.cocomplex)) at he
  change (F.rightDerived n).map (a • 𝟙 M) = a • 𝟙 ((F.rightDerived n).obj M)
  have : Mono e := inferInstanceAs (Mono (P.isoRightDerivedObj F n).hom)
  apply (cancel_mono e).mp
  rw [he, hK, hH]
  change e ≫ (a • 𝟙 (K.homology n)) = (a • 𝟙 ((F.rightDerived n).obj M)) ≫ e
  rw [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]

variable [IsNoetherianRing R]

/-- On ideal-power torsion, an injective action by a member of the ideal forces vanishing. -/
private theorem localCohomology_subsingleton_of_mono_smul (I : Ideal R)
    (M : ModuleCat.{u} R) (n : ℕ) {a : R} (ha : a ∈ I)
    (h : Mono ((localCohomology I (n : ℤ)).map (a • 𝟙 M))) :
    Subsingleton ((localCohomology I (n : ℤ)).obj M) := by
  let H := (localCohomology I (n : ℤ)).obj M
  rw [localCohomology_map_smul_id] at h
  have hreg : IsSMulRegular H a := (ModuleCat.mono_iff_injective _).mp h
  refine ⟨fun x y => ?_⟩
  have vanishes (z : H) : z = 0 := by
    obtain ⟨k, _, hk⟩ := localCohomology_isPowerTorsion I (n : ℤ) M z
    exact (hreg.pow k).right_eq_zero_of_smul (hk (a ^ k) (Ideal.pow_mem_pow ha k))
  rw [vanishes x, vanishes y]

private theorem localCohomology_nontrivial_at_grade (I : Ideal R) (d : ℕ)
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hI : I • (⊤ : Submodule R M) ≠ ⊤)
    (hd : AdvCommAlg.Depth.grade I M = (d : ℕ∞)) :
    Nontrivial ((localCohomology I (d : ℤ)).obj M) ∧
      ∀ q : ℕ, q < d → Subsingleton ((localCohomology I (q : ℤ)).obj M) := by
  classical
  induction d generalizing M with
  | zero =>
    have hAnn := (AdvCommAlg.Depth.grade_zero_iff_annihilator_ne_bot I M hI).mp (by simpa using hd)
    have hle : Submodule.torsionBySet R M (I : Set R) ≤ idealTorsion I M := by
      intro x hx
      refine (mem_idealTorsion I x).mpr ⟨1, le_rfl, fun a ha => ?_⟩
      exact (Submodule.mem_torsionBySet_iff _ x).mp hx ⟨a, by simpa using ha⟩
    have : Nontrivial ((idealTorsionFunctor I).obj M) :=
      Submodule.nontrivial_iff_ne_bot.mpr (ne_bot_of_le_ne_bot hAnn hle)
    let e := (LocalCohomologySequence.degreeZeroIso I).app M
    exact ⟨Function.Injective.nontrivial
      ((ModuleCat.mono_iff_injective e.inv).mp inferInstance), fun q hq => by omega⟩
  | succ d ih =>
    have hex : ∃ a ∈ I, IsSMulRegular M a := by
      by_contra! hn
      have hz := (AdvCommAlg.Depth.grade_zero_iff_no_regular I M hI).mpr hn
      exact (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d) : ((d + 1 : ℕ) : ℕ∞) ≠ 0)
        (hd.symm.trans hz)
    obtain ⟨a, ha, hreg⟩ := hex
    have hmem : ∀ x ∈ [a], x ∈ I := by simpa using ha
    have hproper : Ideal.ofList [a] • (⊤ : Submodule R M) ≠ ⊤ :=
      ne_top_of_le_ne_top hI (Submodule.smul_mono_left (Ideal.span_le.mpr hmem))
    have hregular : RingTheory.Sequence.IsRegular M [a] :=
      ⟨(RingTheory.Sequence.isWeaklyRegular_singleton_iff M a).mpr hreg, hproper.symm⟩
    let S := M.smulShortComplex a
    have hS : S.ShortExact := hreg.smulShortComplex_shortExact
    have hK : Ideal.ofList [a] • (⊤ : Submodule R M) = a • (⊤ : Submodule R M) := by
      rw [Ideal.ofList_singleton, Submodule.ideal_span_singleton_smul]
    have hQI : I • (⊤ : Submodule R S.X₃) ≠ ⊤ := by
      have h := AdvCommAlg.Depth.ideal_smul_listQuotient_ne_top M I hI [a] hmem
      rw [hK] at h
      exact h
    have hdQ : AdvCommAlg.Depth.grade I S.X₃ = (d : ℕ∞) := by
      change AdvCommAlg.Depth.grade I (M ⧸ (a • (⊤ : Submodule R M))) = (d : ℕ∞)
      have h := (AdvCommAlg.Depth.grade_regular_quotient M I hI [a] hregular hmem).2
      rw [hK, hd] at h
      simpa using h
    let : Module.Finite R S.X₃ :=
      inferInstanceAs (Module.Finite R (M ⧸ (a • (⊤ : Submodule R M))))
    obtain ⟨hQ, hvanishQ⟩ := ih S.X₃ hQI hdQ
    have hvanish : ∀ q : ℕ, q < d + 1 →
        Subsingleton ((localCohomology I (q : ℤ)).obj M) := by
      intro q hq
      apply localCohomology_subsingleton_of_mono_smul I M q ha
      change Mono ((localCohomology I (q : ℤ)).map S.f)
      cases q with
      | zero => exact LocalCohomologySequence.mono_zero I hS
      | succ q =>
        have hz := ModuleCat.isZero_iff_subsingleton.mpr (hvanishQ q (by omega))
        have he := (localCohomology_exact I hS (q : ℤ)).2.2
        have hm := he.exact.mono_g (hz.eq_zero_of_src _)
        exact hm
    refine ⟨?_, hvanish⟩
    have hz := ModuleCat.isZero_iff_subsingleton.mpr (hvanish d (Nat.lt_succ_self d))
    have he := (localCohomology_exact I hS (d : ℤ)).2.1
    have hm := he.exact.mono_g (hz.eq_zero_of_src _)
    let := hQ
    exact Function.Injective.nontrivial ((ModuleCat.mono_iff_injective _).mp hm)

/-- Grade is the first degree with nonzero local cohomology, with infinite
grade when all degrees vanish. -/
theorem grade_eq_inf_localCohomology :
    Specs.CommutativeAlgebraNotes.GradeFromLocalCohomology.gradeEqInfLocalCohomologyType.{u} := by
  intro R _ _ I M _
  classical
  by_cases hI : I • (⊤ : Submodule R M) = ⊤
  · have hdisj : PrimeSpectrum.zeroLocus (I : Set R) ∩ Module.support R M = ∅ := by
      let : Subsingleton (M ⧸ (I • ⊤ : Submodule R M)) := Submodule.Quotient.subsingleton_iff.mpr hI
      rw [Set.inter_comm, ← Module.support_quotient I, Module.support_eq_empty]
    rw [AdvCommAlg.Depth.grade_eq_iInf_localDepth M I]
    have hnone (p : PrimeSpectrum R) (hpI : I ≤ p.asIdeal) (hpM : p ∈ Module.support R M) :
        False := by
      have hp : p ∈ PrimeSpectrum.zeroLocus (I : Set R) ∩ Module.support R M := ⟨hpI, hpM⟩
      simp [hdisj] at hp
    have htop : (⨅ (p : PrimeSpectrum R) (_ : I ≤ p.asIdeal) (_ : p ∈ Module.support R M),
        AdvCommAlg.Depth.depth (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M)) = ⊤ := by
      exact top_unique (le_iInf fun p => le_iInf fun hpI => le_iInf fun hpM =>
        (hnone p hpI hpM).elim)
    rw [htop]
    have hz (q : ℕ) : Subsingleton ((localCohomology I (q : ℤ)).obj M) :=
      Module.support_eq_empty_iff.mp
        (Set.eq_empty_of_subset_empty (hdisj ▸ localCohomologySupportSubset I (q : ℤ) M))
    let : IsEmpty {q : ℕ // Nontrivial ((localCohomology I (q : ℤ)).obj M)} :=
      ⟨fun q => (not_nontrivial_iff_subsingleton.mpr (hz q.val)) q.property⟩
    simp
  · let : Nontrivial M := not_subsingleton_iff_nontrivial.mp
      (fun h => hI (@Subsingleton.elim _ (inferInstanceAs (Subsingleton (Submodule R M))) _ _))
    obtain ⟨xs, hxs⟩ := AdvCommAlg.Depth.exists_maximalRegular_extension I M hI []
      (RingTheory.Sequence.IsRegular.nil R M) (by simp)
    rw [List.nil_append] at hxs
    have hd : AdvCommAlg.Depth.grade I M = (xs.length : ℕ∞) :=
      (AdvCommAlg.Depth.maximalRegular_length_eq_grade I M hI xs hxs).symm
    obtain ⟨hnt, hvanish⟩ := localCohomology_nontrivial_at_grade I xs.length M hI hd
    rw [hd]
    symm
    apply ENat.iInf_eq_natCast_iff.mpr
    refine ⟨⟨⟨xs.length, hnt⟩, rfl⟩, fun q => ?_⟩
    exact_mod_cast Nat.le_of_not_gt fun h => (not_nontrivial_iff_subsingleton.mpr
      (hvanish q.val h)) q.property

end CommutativeAlgebraNotes
