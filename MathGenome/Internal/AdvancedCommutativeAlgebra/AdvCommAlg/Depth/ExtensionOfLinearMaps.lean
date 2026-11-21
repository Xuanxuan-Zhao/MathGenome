import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ExtCharacterization
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.ExtensionOfLinearMaps
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Category.ModuleCat.Projective

universe u
open CategoryTheory CategoryTheory.Abelian
namespace AdvCommAlg.Depth

variable {R : Type u} [CommRing R]

@[simp] theorem restrictionMap_apply (I : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] (f : R →ₗ[R] M) (x : I) :
    restrictionMap I M f x = f (x : R) := rfl

@[simp] theorem evaluationAtOne_apply (M : Type u) [AddCommGroup M] [Module R M]
    (f : R →ₗ[R] M) : evaluationAtOne M f = f 1 := rfl

@[simp] theorem restrictionMap_evaluationAtOne_symm (I : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] (m : M) (x : I) :
    restrictionMap I M ((evaluationAtOne M).symm m) x = (x : R) • m := rfl

/-- The beginning of the contravariant Ext sequence, with projective middle term. -/
private lemma ext_zero_one_iff (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (M : ModuleCat.{u} R) [Projective S.X₂] :
    (Subsingleton (Ext S.X₃ M 0) ∧ Subsingleton (Ext S.X₃ M 1)) ↔
      Function.Bijective ((Ext.mk₀ S.f).precomp M (zero_add 0)) := by
  have hex := Ext.contravariant_sequence_exact₂' hS M 0
  have := hS.epi_g
  have hi := Ext.precomp_mk₀_injective_of_epi M S.g
  have hz : Subsingleton (Ext S.X₃ M 0) ↔
      Function.Injective ((Ext.mk₀ S.f).precomp M (zero_add 0)) := by
    constructor
    · intro h
      exact (AddCommGrpCat.mono_iff_injective _).mp
        (hex.mono_g ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr h).eq_zero_of_src _))
    · intro h
      let : Mono (AddCommGrpCat.ofHom ((Ext.mk₀ S.f).precomp M (zero_add 0))) :=
        (AddCommGrpCat.mono_iff_injective _).mpr h
      have hf := hex.mono_g_iff.mp inferInstance
      apply subsingleton_of_forall_eq 0
      intro x
      apply hi
      have hx := congrArg (fun f => f x) hf
      simpa using hx
  rw [hz, Ext.one_subsingleton_iff_of_projective M S hS inferInstance]
  rfl

/-- The grade threshold two is precisely vanishing in Ext degrees zero and one. -/
private lemma grade_ge_two_iff_ext [IsNoetherianRing R] (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    (2 : ℕ∞) ≤ grade I M ↔
      Subsingleton (Ext (ModuleCat.of R (R ⧸ I)) M 0) ∧
        Subsingleton (Ext (ModuleCat.of R (R ⧸ I)) M 1) := by
  have hd : grade I M = (ModuleCat.of R (R ⧸ I)).depth M := by
    simpa only [Ideal.annihilator_quotient] using
      grade_eq_extDepth (ModuleCat.of R (R ⧸ I)) M
  rw [hd]
  constructor
  · intro h
    exact ⟨ModuleCat.subsingleton_ext_of_lt_depth (lt_of_lt_of_le (by norm_num) h),
      ModuleCat.subsingleton_ext_of_lt_depth (lt_of_lt_of_le (by norm_num) h)⟩
  · rintro ⟨h0, h1⟩
    apply le_sSup
    intro i hi
    have hi' : i < 2 := by exact_mod_cast hi
    match i with
    | 0 => exact h0
    | 1 => exact h1
    | n + 2 => omega

/-- Under Ext⁰ = Hom, precomposition with the inclusion is literal restriction. -/
private lemma ext_precomp_bijective_iff (I : Ideal R) (M : ModuleCat.{u} R) :
    Function.Bijective
      ((Ext.mk₀ (ModuleCat.ofHom I.subtype)).precomp M (zero_add 0)) ↔
      Function.Bijective (restrictionMap I M) := by
  let eR : Ext (ModuleCat.of R R) M 0 ≃+ (R →ₗ[R] M) :=
    Ext.addEquiv₀.trans (ModuleCat.homLinearEquiv (S := R)).toAddEquiv
  let eI : Ext (ModuleCat.of R I) M 0 ≃+ (I →ₗ[R] M) :=
    Ext.addEquiv₀.trans (ModuleCat.homLinearEquiv (S := R)).toAddEquiv
  have hcomm (x : Ext (ModuleCat.of R R) M 0) :
      eI ((Ext.mk₀ (ModuleCat.ofHom I.subtype)).precomp M (zero_add 0) x) =
        restrictionMap I M (eR x) := by
    obtain ⟨f, rfl⟩ := Ext.addEquiv₀.symm.surjective x
    simp only [Ext.precomp, Ext.bilinearComp_apply_apply, Ext.addEquiv₀_symm_apply,
      Ext.mk₀_comp_mk₀]
    simp only [eI, eR, AddEquiv.trans_apply, ← Ext.addEquiv₀_symm_apply,
      AddEquiv.apply_symm_apply]
    rfl
  constructor
  · rintro ⟨hinj, hsurj⟩
    constructor
    · intro f g hfg
      have h := hinj (a₁ := eR.symm f) (a₂ := eR.symm g)
        (eI.injective (by simpa only [hcomm, eR.apply_symm_apply] using hfg))
      exact eR.symm.injective h
    · intro f
      obtain ⟨x, hx⟩ := hsurj (eI.symm f)
      exact ⟨eR x, by simpa only [hcomm, eI.apply_symm_apply] using congrArg eI hx⟩
  · rintro ⟨hinj, hsurj⟩
    constructor
    · intro x y hxy
      apply eR.injective
      apply hinj
      simpa only [hcomm] using congrArg eI hxy
    · intro x
      obtain ⟨f, hf⟩ := hsurj (eI x)
      refine ⟨eR.symm f, eI.injective ?_⟩
      simpa only [hcomm, eR.apply_symm_apply] using hf

/-- DP-15: the actual restriction homomorphism is bijective exactly at grade ≥ 2. -/
theorem grade_ge_two_iff_restriction_bijective [IsNoetherianRing R] (I : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (2 : ℕ∞) ≤ grade I M ↔ Function.Bijective (restrictionMap I M) := by
  let S := ModuleCat.shortComplexOfCompEqZero I.subtype I.mkQ
    (LinearMap.exact_subtype_mkQ I).linearMap_comp_eq_zero
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (LinearMap.exact_subtype_mkQ I) I.subtype_injective I.mkQ_surjective
  have : Projective S.X₂ := inferInstanceAs (Projective (ModuleCat.of R R))
  exact (grade_ge_two_iff_ext I (ModuleCat.of R M)).trans
    ((ext_zero_one_iff S hS (ModuleCat.of R M)).trans (ext_precomp_bijective_iff I _))

/-- Equivalent formulation exhibiting an isomorphism whose map is restriction. -/
theorem grade_ge_two_iff_restriction_isomorphism [IsNoetherianRing R] (I : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (2 : ℕ∞) ≤ grade I M ↔
      ∃ e : (R →ₗ[R] M) ≃ₗ[R] (I →ₗ[R] M), e.toLinearMap = restrictionMap I M := by
  rw [grade_ge_two_iff_restriction_bijective]
  constructor
  · intro h
    exact ⟨LinearEquiv.ofBijective (restrictionMap I M) h, rfl⟩
  · rintro ⟨e, he⟩
    rw [← he]
    exact e.bijective

end AdvCommAlg.Depth
