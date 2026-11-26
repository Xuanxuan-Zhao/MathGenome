import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MinimalInjectiveResolutionSocles
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.MatlisDualFunctor
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.Type
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AdvCommAlg.Gorenstein AdvCommAlg.Depth

namespace CommutativeAlgebraNotes

open MinimalInjectiveResolutionSoclesSpecs

universe u

variable {R : Type u} [CommRing R]

/-- An injective resolution obtained by taking the injective hull of each actual cosyzygy. -/
abbrev MinimalInjectiveResolution (X : ModuleCat.{u} R) := resolutionValue X

private theorem range_inclusion_eq_ker_differential
    (H : EnvelopeChoice (R := R)) (X : ModuleCat.{u} R) (n : ℕ) :
    (inclusion H X n).hom.range = (differential H X n).hom.ker := by
  change _ = LinearMap.ker ((inclusion H X (n + 1)).hom.comp (quotient H X n).hom)
  have hinj : Function.Injective (inclusion H X (n + 1)).hom :=
    (H (cosyzygy H X (n + 1))).isEnvelope.injective
  rw [LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hinj)]
  exact (Submodule.ker_mkQ _).symm

private theorem range_differential (H : EnvelopeChoice (R := R)) (X : ModuleCat.{u} R)
    (n : ℕ) : (differential H X n).hom.range = (inclusion H X (n + 1)).hom.range := by
  change LinearMap.range ((inclusion H X (n + 1)).hom.comp (quotient H X n).hom) = _
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _))

private theorem cocomplex_exactAt_succ (H : EnvelopeChoice (R := R))
    (X : ModuleCat.{u} R) (n : ℕ) : (cocomplex H X).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change ((cocomplex H X).d n (n + 1)).hom.range =
    ((cocomplex H X).d (n + 1) (n + 1 + 1)).hom.ker
  rw [cocomplex_d, cocomplex_d, range_differential, range_inclusion_eq_ker_differential]

private theorem augmentation_quasiIso (H : EnvelopeChoice (R := R))
    (X : ModuleCat.{u} R) : QuasiIso (augmentation H X) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff,
      ShortComplex.quasiIso_iff_of_zeros _ rfl
        (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) 0 X 0 1) rfl]
    constructor
    · apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
      change ((augmentation H X).f 0).hom.range = ((cocomplex H X).d 0 (0 + 1)).hom.ker
      rw [augmentation_f_zero, cocomplex_d]
      exact range_inclusion_eq_ker_differential H X 0
    · change Mono ((augmentation H X).f 0)
      rw [augmentation_f_zero]
      exact (ModuleCat.mono_iff_injective (inclusion H X 0)).mpr
        (H (cosyzygy H X 0)).isEnvelope.injective
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · exact cocomplex_exactAt_succ H X n
    · exact CochainComplex.exactAt_succ_single_obj _ _

theorem exists_minimalInjectiveResolution [IsLocalRing R] [IsNoetherianRing R]
    (X : ModuleCat.{u} R) :
    Nonempty (MinimalInjectiveResolution X) := by
  let H : EnvelopeChoice (R := R) := fun Y => (exists_injectiveEnvelope R Y).some
  exact ⟨⟨H, augmentation_quasiIso H X⟩⟩

variable [IsLocalRing R]

/-- Every vector annihilated by the maximal ideal belongs to an essential submodule. -/
private theorem socle_le_range_of_essential {U V : Type u}
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    {i : U →ₗ[R] V} (hi : IsEssential i) :
    Socle R V ≤ LinearMap.range i := by
  intro x hx
  by_cases h : x = 0
  · simp [h]
  obtain ⟨r, hr, hrx⟩ := (essential_iff_scalar i).mp hi x h
  have hu : IsUnit r := IsLocalRing.notMem_maximalIdeal.mp
    (fun hm => hrx ((mem_socle_iff x).mp hx r hm))
  exact ((LinearMap.range i).smul_mem_iff_of_isUnit hu).mp hr

theorem minimalInjectiveResolution_residueHom_differential_zero
    [IsNoetherianRing R]
    {X : ModuleCat.{u} R} (J : MinimalInjectiveResolution X) (i j : ℕ)
    (f : residueObject R ⟶ J.toInjectiveResolution.cocomplex.X i) :
    f ≫ J.toInjectiveResolution.cocomplex.d i j = 0 := by
  by_cases h : i + 1 = j
  · subst j
    change residueObject R ⟶ term J.envelopes X i at f
    change f ≫ (cocomplex J.envelopes X).d i (i + 1) = 0
    rw [cocomplex_d]
    apply ModuleCat.hom_ext
    ext z
    change (inclusion J.envelopes X (i + 1)).hom
      ((quotient J.envelopes X i).hom (f.hom z)) = 0
    have hs : f.hom z ∈ Socle R (term J.envelopes X i) :=
      (Submodule.mem_torsionBySet_iff _ _).mpr fun a =>
        LinearMap.congr_fun (residueHom_torsion _ (x := f.hom) (a := a)) z
    have hrange := socle_le_range_of_essential
      (J.envelopes (cosyzygy J.envelopes X i)).isEnvelope.essential hs
    exact ((inclusion J.envelopes X (i + 1)).hom.congr_arg
      ((Submodule.Quotient.mk_eq_zero _).2 hrange)).trans (map_zero _)
  · rw [J.toInjectiveResolution.cocomplex.shape i j h, comp_zero]

omit [IsLocalRing R] in
private theorem extMk_zero_degree_eq_zero
    {A X : ModuleCat.{u} R} (I : InjectiveResolution X) (f : A ⟶ I.cocomplex.X 0)
    (hf : f ≫ I.cocomplex.d 0 1 = 0) (hz : I.extMk f 1 rfl hf = 0) :
    f = 0 := by
  simp only [← I.extEquivCohomologyClass.apply_eq_iff_eq,
    InjectiveResolution.extEquivCohomologyClass_extMk,
    InjectiveResolution.extEquivCohomologyClass_zero,
    CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff] at hz
  rw [CochainComplex.HomComplex.Cocycle.fromSingleMk_mem_coboundaries_iff
    _ _ _ _ _ (-1) (by decide)] at hz
  obtain ⟨g, hg⟩ := hz
  have hZ := CochainComplex.isZero_of_isStrictlyGE I.cochainComplex 0 (-1) (by decide)
  rw [hZ.eq_of_tgt g 0, zero_comp] at hg
  exact (cancel_mono (I.cochainComplexXIso 0 0 rfl).inv).mp (by simpa using hg.symm)

private def residueHomToExt [IsNoetherianRing R] {X : ModuleCat.{u} R}
    (J : MinimalInjectiveResolution X) (n : ℕ) :
    (residueObject R ⟶ J.toInjectiveResolution.cocomplex.X n) →ₗ[R] ResidueExt X n where
  toFun f := J.toInjectiveResolution.extMk f (n + 1) rfl
    (minimalInjectiveResolution_residueHom_differential_zero J n (n + 1) f)
  map_add' f g := (J.toInjectiveResolution.add_extMk f g (n + 1) rfl _ _).symm
  map_smul' r f := (J.toInjectiveResolution.smul_extMk r f (n + 1) rfl _).symm

private theorem residueHomToExt_bijective [IsNoetherianRing R] {X : ModuleCat.{u} R}
    (J : MinimalInjectiveResolution X) (n : ℕ) : Function.Bijective (residueHomToExt J n) := by
  constructor
  · apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro f hf
    change J.toInjectiveResolution.extMk f (n + 1) rfl
      (minimalInjectiveResolution_residueHom_differential_zero J n (n + 1) f) = 0 at hf
    cases n with
    | zero => exact extMk_zero_degree_eq_zero _ _ _ hf
    | succ n =>
      obtain ⟨g, hg⟩ := (J.toInjectiveResolution.extMk_eq_zero_iff _ _ rfl _ n rfl).mp hf
      exact hg.symm.trans (minimalInjectiveResolution_residueHom_differential_zero J n (n + 1) g)
  · intro α
    obtain ⟨f, hf, he⟩ := J.toInjectiveResolution.extMk_surjective α (n + 1) rfl
    exact ⟨f, he⟩

/-- The class of a cocycle corresponds to its value at the residue class of one. -/
theorem minimalInjectiveResolution_residueExt_socle
    [IsNoetherianRing R]
    {X : ModuleCat.{u} R} (J : MinimalInjectiveResolution X) (n : ℕ) :
    ∃ e : ResidueExt X n ≃ₗ[IsLocalRing.ResidueField R]
        Socle R (J.toInjectiveResolution.cocomplex.X n),
      ∀ (f : residueObject R ⟶ J.toInjectiveResolution.cocomplex.X n)
        (hf : f ≫ J.toInjectiveResolution.cocomplex.d n (n + 1) = 0),
        (e (J.toInjectiveResolution.extMk f (n + 1) rfl hf)).val = f.hom 1 := by
  let L := LinearEquiv.ofBijective (residueHomToExt J n) (residueHomToExt_bijective J n)
  let eR : ResidueHom R (J.toInjectiveResolution.cocomplex.X n) ≃ₗ[R] ResidueExt X n :=
    (ModuleCat.homLinearEquiv (S := R)).symm.trans L
  let e := residueLinearEquiv R eR
  obtain ⟨s, hs⟩ := homSocleEquiv R (J.toInjectiveResolution.cocomplex.X n)
  refine ⟨e.symm.trans s, fun f hf => ?_⟩
  have he : e f.hom = J.toInjectiveResolution.extMk f (n + 1) rfl hf := rfl
  rw [← he]
  exact (congrArg Subtype.val (congrArg s (e.symm_apply_apply f.hom))).trans (hs f.hom)

end CommutativeAlgebraNotes
