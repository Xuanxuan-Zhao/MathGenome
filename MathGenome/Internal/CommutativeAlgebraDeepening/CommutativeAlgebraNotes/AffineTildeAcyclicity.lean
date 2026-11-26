import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.AffineTildeAcyclicity
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalizationOfInjectives
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.TorsionOfInjectives
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.FlasqueAcyclicity
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafCohomology
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AdvancedHomologicalAlgebra.SheafTheory
open Specs.CommutativeAlgebraNotes.AffineTildeAcyclicity

namespace CommutativeAlgebraNotes

universe u

variable {R : CommRingCat.{u}}

private abbrev sectionsSheaf (M : ModuleCat.{u} R) :=
  modulesSpecToSheaf.obj (tilde M)

private abbrev res (M : ModuleCat.{u} R) {V W : (Spec R).Opens} (h : V ≤ W) :=
  (sectionsSheaf M).presheaf.map (homOfLE h).op

private lemma res_toOpen (M : ModuleCat.{u} R) {V W : (Spec R).Opens} (h : V ≤ W)
    (x : M) : res M h (tilde.toOpen M W x) = tilde.toOpen M V x :=
  congr($(tilde.toOpen_res M W V (homOfLE h)) x)

private lemma res_res (M : ModuleCat.{u} R) {U V W : (Spec R).Opens} (h : U ≤ V)
    (k : V ≤ W) (s : (sectionsSheaf M).presheaf.obj (op W)) :
    res M h (res M k s) = res M (h.trans k) s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private abbrev D (f : R) : (Spec R).Opens := PrimeSpectrum.basicOpen f

private lemma toOpen_basic_eq_zero (M : ModuleCat.{u} R) (f : R) (x : M) :
    tilde.toOpen M (D f) x = 0 ↔ ∃ n : ℕ, f ^ n • x = 0 := by
  rw [show tilde.toOpen M (D f) x = (tilde.toOpen M (D f)).hom x from rfl,
    IsLocalizedModule.eq_zero_iff (Submonoid.powers f) (tilde.toOpen M (D f)).hom]
  exact ⟨fun ⟨⟨_, n, rfl⟩, hn⟩ => ⟨n, hn⟩,
    fun ⟨n, hn⟩ => ⟨⟨_, n, rfl⟩, hn⟩⟩

section Flasque
variable [IsNoetherianRing R] (Q : ModuleCat.{u} R) [Injective Q]

private lemma toOpen_basic_surjective (f : R) :
    Function.Surjective (tilde.toOpen Q (D f)) := by
  have : Module.Injective R Q := (Module.injective_iff_injective_object R Q).mpr inferInstance
  exact (localizationAway_surjective_ker f (tilde.toOpen Q (D f)).hom).1

/-- Choose a representative on a principal open which vanishes on the other open
whenever the given section vanishes on the overlap. -/
private lemma lift_preserving_zero (f : R) (V : (Spec R).Opens)
    (s : (sectionsSheaf Q).presheaf.obj (op (D f))) (hs :
      res Q (inf_le_left : D f ⊓ V ≤ D f) s = 0) :
    ∃ x : Q, tilde.toOpen Q (D f) x = s ∧ tilde.toOpen Q V x = 0 := by
  have : Module.Injective R Q := (Module.injective_iff_injective_object R Q).mpr inferInstance
  let T := idealTorsion (Ideal.span {(f : R)}) Q
  let loc := (tilde.toOpen Q (D f)).hom
  have hT : LinearMap.ker loc = T := (localizationAway_surjective_ker f loc).2
  let inj : Module.Injective R T := idealTorsion_injective _ inferInstance
  obtain ⟨p, hp⟩ := inj.out T.subtype T.subtype_injective (LinearMap.id : T →ₗ[R] T)
  obtain ⟨y, hy⟩ := toOpen_basic_surjective Q f s
  let x : Q := y - (p y : Q)
  have hx : p x = 0 := by
    dsimp [x]
    rw [map_sub]
    exact sub_eq_zero.mpr (hp (p y)).symm
  have hloc : tilde.toOpen Q (D f) x = s := by
    have hpy : (p y : Q) ∈ LinearMap.ker loc := hT.symm ▸ (p y).property
    change loc x = s
    rw [map_sub, LinearMap.mem_ker.mp hpy, sub_zero]
    exact hy
  refine ⟨x, hloc, ?_⟩
  apply TopCat.Presheaf.IsSheaf.section_ext (sectionsSheaf Q).2
  intro z hz
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hzg, hgV : D g ≤ V⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hz V.2
  refine ⟨D g, hgV, hzg, ?_⟩
  rw [res_toOpen, map_zero, toOpen_basic_eq_zero]
  have hfg : tilde.toOpen Q (D (f * g)) x = 0 := by
    have hle : D (f * g) ≤ D f ⊓ V :=
      (PrimeSpectrum.basicOpen_mul f g).trans_le (inf_le_inf le_rfl hgV)
    calc
      tilde.toOpen Q (D (f * g)) x =
          res Q hle (res Q (inf_le_left : D f ⊓ V ≤ D f) (tilde.toOpen Q (D f) x)) := by
            rw [res_res, res_toOpen]
      _ = 0 := by rw [hloc, hs, map_zero]
  obtain ⟨n, hn⟩ := (toOpen_basic_eq_zero Q (f * g) x).mp hfg
  refine ⟨n, ?_⟩
  have hz' : g ^ n • x ∈ T := by
    rw [← hT, LinearMap.mem_ker]
    apply (toOpen_basic_eq_zero Q f _).mpr
    exact ⟨n, by simpa only [mul_pow, mul_smul] using hn⟩
  have hz'' := hp ⟨g ^ n • x, hz'⟩
  change p (g ^ n • x) = (⟨g ^ n • x, hz'⟩ : T) at hz''
  rw [map_smul, hx, smul_zero] at hz''
  exact (congrArg Subtype.val hz'').symm

private lemma toOpen_sup_surjective (f : R) (V : (Spec R).Opens)
    (hV : Function.Surjective (tilde.toOpen Q V)) :
    Function.Surjective (tilde.toOpen Q (D f ⊔ V)) := by
  intro s
  let W := D f ⊔ V
  let h₁ : D f ≤ W := le_sup_left
  let h₂ : V ≤ W := le_sup_right
  obtain ⟨a, ha⟩ := hV (res Q h₂ s)
  let t := s - tilde.toOpen Q W a
  have ht : res Q h₂ t = 0 := by
    change res Q h₂ (s - tilde.toOpen Q W a) = 0
    rw [map_sub, res_toOpen, ha, sub_self]
  obtain ⟨b, hb₁, hb₂⟩ := lift_preserving_zero Q f V (res Q h₁ t) (by
    rw [res_res, ← res_res Q (inf_le_right : D f ⊓ V ≤ V) h₂, ht, map_zero])
  refine ⟨a + b, (sectionsSheaf Q).eq_of_locally_eq₂ (homOfLE h₁) (homOfLE h₂)
    le_rfl _ _ ?_ ?_⟩
  · change res Q h₁ (tilde.toOpen Q W (a + b)) = res Q h₁ s
    rw [res_toOpen, map_add, hb₁]
    change tilde.toOpen Q (D f) a + res Q h₁ (s - tilde.toOpen Q W a) = res Q h₁ s
    rw [map_sub, res_toOpen, add_sub_cancel]
  · change res Q h₂ (tilde.toOpen Q W (a + b)) = res Q h₂ s
    rw [res_toOpen, map_add, ha, hb₂, add_zero]

private lemma exists_finset_basicOpen (U : (Spec R).Opens) :
    ∃ s : Finset R, s.sup D = U := by
  classical
  have : NoetherianSpace (Spec R) := inferInstanceAs (NoetherianSpace (PrimeSpectrum R))
  have hCompact : IsCompact (U : Set (Spec R)) := NoetherianSpace.isCompact _
  have hBasis (x : U) : ∃ f : R, x.1 ∈ D f ∧ D f ≤ U := by
    obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hfU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open x.2 U.2
    exact ⟨f, hxf, hfU⟩
  choose f hfx hfU using hBasis
  obtain ⟨t, ht⟩ := hCompact.elim_finite_subcover (fun i => (D (f i) : Set (Spec R)))
    (fun _ => (D _).2) (fun x hx => Set.mem_iUnion_of_mem ⟨x, hx⟩ (hfx ⟨x, hx⟩))
  refine ⟨t.image f, le_antisymm (Finset.sup_le ?_) ?_⟩
  · intro g hg
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
    exact hfU i
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
    have hle : D (f i) ≤ (t.image f).sup D := Finset.le_sup (Finset.mem_image_of_mem f hi)
    exact hle hxi

/-- Every section of an injective module's associated sheaf extends from the module. -/
theorem tildeSectionsSurjective : TildeSectionsSurjective.{u} := by
  intro R _ Q _ U
  classical
  obtain ⟨s, rfl⟩ := exists_finset_basicOpen U
  induction s using Finset.induction_on with
  | empty =>
    intro t
    refine ⟨0, TopCat.Presheaf.IsSheaf.section_ext (sectionsSheaf Q).2 ?_⟩
    intro x hx
    simp at hx
  | @insert f s hf ih =>
    rw [Finset.sup_insert]
    exact toOpen_sup_surjective Q f _ ih

/-- An injective module over a Noetherian ring yields a flasque module sheaf. -/
theorem tildeFlasque : TildeFlasque.{u} := by
  intro R _ Q _ V W h s
  obtain ⟨x, hx⟩ := tildeSectionsSurjective R Q V s
  exact ⟨tilde.toOpen Q W x, (res_toOpen Q h x).trans hx⟩

end Flasque


section Exact

open TopCat.Presheaf
open private AlgebraicGeometry.StructureSheaf.toStalkₗ' from Mathlib.AlgebraicGeometry.StructureSheaf

set_option backward.isDefEq.respectTransparency false

private instance modulesSpecToSheaf_additive : (modulesSpecToSheaf (R := R)).Additive :=
  ⟨by intros; rfl⟩

private abbrev stalk (x : Spec R) :=
  TopCat.Sheaf.forget (ModuleCat.{u} R) (Spec R) ⋙ stalkFunctor (ModuleCat.{u} R) x

private def moduleToStalk (M : ModuleCat.{u} R) (x : Spec R) :
    M ⟶ (stalk x).obj (sectionsSheaf M) :=
  tilde.toOpen M ⊤ ≫ (sectionsSheaf M).presheaf.germ ⊤ x (by simp)

private lemma moduleToStalk_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (x : Spec R) :
    moduleToStalk M x ≫ (stalk x).map (modulesSpecToSheaf.map (tilde.map f)) =
      f ≫ moduleToStalk N x := by
  unfold moduleToStalk
  rw [Category.assoc]
  change tilde.toOpen M ⊤ ≫ (sectionsSheaf M).presheaf.germ ⊤ x _ ≫
    (stalkFunctor (ModuleCat.{u} R) x).map (modulesSpecToSheaf.map (tilde.map f)).hom =
    f ≫ tilde.toOpen N ⊤ ≫ (sectionsSheaf N).presheaf.germ ⊤ x _
  rw [stalkFunctor_map_germ, tilde.toOpen_map_app_assoc]

private instance moduleToStalk_isLocalized (M : ModuleCat.{u} R) (x : Spec R) :
    IsLocalizedModule x.asIdeal.primeCompl (moduleToStalk M x).hom := by
  let e := (stalkFunctor (ModuleCat.{u} R) x).mapIso (tilde.modulesSpecToSheafIso M)
  have heq : moduleToStalk M x ≫ e.hom = AlgebraicGeometry.StructureSheaf.toStalkₗ' R M x := by
    unfold moduleToStalk AlgebraicGeometry.StructureSheaf.toStalkₗ'
    rw [Category.assoc, Functor.mapIso_hom, stalkFunctor_map_germ]
    simp [tilde.toOpen]
  have heq' : AlgebraicGeometry.StructureSheaf.toStalkₗ' R M x ≫ e.inv = moduleToStalk M x :=
    (Iso.comp_inv_eq e).mpr heq.symm
  rw [← heq']
  exact IsLocalizedModule.of_linearEquiv _ (AlgebraicGeometry.StructureSheaf.toStalkₗ' R M x).hom e.symm.toLinearEquiv

private lemma map_stalk_tilde {M N : ModuleCat.{u} R} (f : M ⟶ N) (x : Spec R) :
    ((stalk x).map (modulesSpecToSheaf.map (tilde.map f))).hom =
      IsLocalizedModule.map x.asIdeal.primeCompl (moduleToStalk M x).hom (moduleToStalk N x).hom
        f.hom := by
  apply IsLocalizedModule.ext x.asIdeal.primeCompl (moduleToStalk M x).hom
    (IsLocalizedModule.map_units (moduleToStalk N x).hom)
  rw [IsLocalizedModule.map_comp]
  exact congrArg ModuleCat.Hom.hom (moduleToStalk_naturality f x)

private theorem tilde_map_exact (R : CommRingCat.{u}) (T : ShortComplex (ModuleCat.{u} R))
    (hT : T.Exact) : (T.map (tilde.functor R)).Exact := by
  apply (modulesSpecToSheaf (R := R)).reflects_exact_of_faithful
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr
  intro x
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  change Function.Exact (((stalk x).map (modulesSpecToSheaf.map (tilde.map T.f))).hom)
    (((stalk x).map (modulesSpecToSheaf.map (tilde.map T.g))).hom)
  rw [map_stalk_tilde, map_stalk_tilde]
  exact IsLocalizedModule.map_exact x.asIdeal.primeCompl (moduleToStalk T.X₁ x).hom
    (moduleToStalk T.X₂ x).hom (moduleToStalk T.X₃ x).hom T.f.hom T.g.hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hT)


/-- Exactness of the associated sheaf construction, checked at localized stalks. -/
theorem tildeExact : TildeExact.{u} := by
  intro R _ S hS
  have h : ∀ T : ShortComplex (ModuleCat.{u} R), T.ShortExact →
      (T.map (tilde.functor R)).ShortExact :=
    ((tilde.functor R).exact_tfae.out 2 1).mp (tilde_map_exact R)
  exact h S hS

end Exact


private instance tilde_preservesHomology (R : CommRingCat.{u}) :
    (tilde.functor R).PreservesHomology :=
  ((tilde.functor R).exact_tfae.out 2 3).mp (tilde_map_exact R)

theorem tildeFlasqueResolution : TildeFlasqueResolution.{u} := by
  intro R _ M I
  let F := tilde.functor R
  let G := moduleSpecΓFunctor (R := R)
  refine ⟨inferInstance, fun n => tildeFlasque R (I.cocomplex.X n), ?_⟩
  let e : F ⋙ G ≅ 𝟭 (ModuleCat.{u} R) := (tilde.toTildeΓNatIso (R := R)).symm
  exact ⟨(Functor.mapHomologicalComplexCompIso e (.up ℕ)).app I.cocomplex ≪≫
    (Functor.mapHomologicalComplexIdIso _ (.up ℕ)).app I.cocomplex⟩

section Cohomology

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open HomologicalComplex
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.SheafCohomology
open AdvancedHomologicalAlgebra

attribute [local instance] HasDerivedCategory.standard

private abbrev evalOpen (R : CommRingCat.{u}) (U : (Spec R).Opens) :=
  SheafOfModules.evaluation.{u} (Spec R).ringCatSheaf (op U)

private instance evalOpen_additive (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    (evalOpen R U).Additive where
  map_add := by intros; rfl

private instance tilde_eval_additive (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    (tilde.functor R ⋙ evalOpen R U).Additive where
  map_add := by
    intro M N g h
    change (evalOpen R U).map ((tilde.functor R).map (g + h)) =
      (evalOpen R U).map ((tilde.functor R).map g) +
      (evalOpen R U).map ((tilde.functor R).map h)
    rw [(tilde.functor R).map_add, (evalOpen R U).map_add]

private lemma tilde_basic_map_eq {M N : ModuleCat.{u} R} (g : M ⟶ N) (f : R) :
    ((modulesSpecToSheaf.map (tilde.map g)).1.app (op (D f))).hom =
      IsLocalizedModule.map (Submonoid.powers f) (tilde.toOpen M (D f)).hom
        (tilde.toOpen N (D f)).hom g.hom := by
  apply IsLocalizedModule.ext (Submonoid.powers f) (tilde.toOpen M (D f)).hom
    (IsLocalizedModule.map_units (tilde.toOpen N (D f)).hom)
  rw [IsLocalizedModule.map_comp]
  exact congrArg ModuleCat.Hom.hom (tilde.toOpen_map_app g (D f))

-- Evaluation has coefficients in the section ring. Its underlying additive
-- groups and maps are the same as for the R-linear localization maps.
private lemma tilde_eval_preservesHomology (R : CommRingCat.{u}) (f : R) :
    (tilde.functor R ⋙ evalOpen R (D f)).PreservesHomology := by
  apply ((tilde.functor R ⋙ evalOpen R (D f)).exact_tfae.out 2 3).mp
  intro S hS
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  change Function.Exact (((modulesSpecToSheaf.map (tilde.map S.f)).1.app (op (D f))).hom)
    (((modulesSpecToSheaf.map (tilde.map S.g)).1.app (op (D f))).hom)
  rw [tilde_basic_map_eq, tilde_basic_map_eq]
  exact IsLocalizedModule.map_exact (Submonoid.powers f) (tilde.toOpen S.X₁ (D f)).hom
    (tilde.toOpen S.X₂ (D f)).hom (tilde.toOpen S.X₃ (D f)).hom S.f.hom S.g.hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS)

private lemma tilde_sectionCohomology_basic [IsNoetherianRing R] (M : ModuleCat.{u} R)
    (f : R) (n : ℕ) (hn : 0 < n) :
    IsZero ((sectionCohomology (Spec R).ringCatSheaf (D f) n).obj (tilde M)) := by
  let I := injectiveResolution M
  let e := ComplexShape.embeddingUpIntGE 0
  let J := I.cocomplex.extend e
  let ι : (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M ⟶ J :=
    (extendSingleIso e M (0 : ℕ) (0 : ℤ) rfl).inv ≫ extendMap I.ι e
  letI hι : QuasiIso ι := by dsimp [ι]; infer_instance
  let F := tilde.functor R
  letI : F.PreservesHomology := tilde_preservesHomology R
  let G := evalOpen R (D f)
  letI : G.Additive := evalOpen_additive R (D f)
  letI : G.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive G
  letI : PreservesFiniteLimits G := inferInstanceAs (PreservesFiniteLimits (evalOpen R (D f)))
  let K : CochainComplex (Spec R).Modules ℤ := (F.mapHomologicalComplex (.up ℤ)).obj J
  letI : K.IsStrictlyGE 0 := by
    change ((F.mapHomologicalComplex (.up ℤ)).obj (I.cocomplex.extend e)).IsStrictlySupported e
    infer_instance
  let κ : (CochainComplex.singleFunctor (Spec R).Modules 0).obj (tilde M) ⟶ K :=
    (F.mapCochainComplexSingleFunctor 0).inv.app M ≫ (F.mapHomologicalComplex (.up ℤ)).map ι
  have hκ : QuasiIso κ := by
    let t := (F.mapCochainComplexSingleFunctor 0).app M
    have ht : QuasiIso t.inv := by infer_instance
    have hφ : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map ι) :=
      quasiIso_map_of_preservesHomology ι F
    exact quasiIso_comp t.inv _
  have hAcyclic (q : ℤ) := by
    have hFlasque : IsFlasque (Spec R).ringCatSheaf (K.X q) := by
      have : Injective (J.X q) := inferInstance
      exact tildeFlasque R (J.X q)
    apply (AcyclicTermComparison.rightVanishing _ _ G _).mpr
    intro m
    exact FlasqueAcyclicity.flasqueAcyclic (Spec R).ringCatSheaf (D f) _ hFlasque m
  let comparison := resolutionModelMap (I := K) G κ hκ n
  have : IsIso comparison := SheafCohomology.resolutionModelMap_isIso (I := K) G κ hκ hAcyclic n
  let E := F ⋙ G
  letI : E.Additive := tilde_eval_additive R (D f)
  letI : E.PreservesHomology := tilde_eval_preservesHomology R f
  have hSource : ((E.mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)).ExactAt (n : ℤ) := by
    apply ExactAt.of_isZero
    exact E.map_isZero (isZero_single_obj_X (.up ℤ) 0 M (n : ℤ) (by exact_mod_cast hn.ne'))
  let φ := (E.mapHomologicalComplex (.up ℤ)).map ι
  have hTgt : ((E.mapHomologicalComplex (.up ℤ)).obj J).ExactAt (n : ℤ) :=
    (quasiIsoAt_iff_exactAt φ (n : ℤ) hSource).mp inferInstance
  let i := (Functor.mapHomologicalComplexCompIso (Iso.refl E) (.up ℤ)).app J
  exact (hTgt.isZero_homology).of_iso ((asIso comparison).symm ≪≫
    (homologyFunctor _ (.up ℤ) (n : ℤ)).mapIso i)

/-- A distinguished open is acyclic both for ambient derived sections and
for derived global sections on the actual open subspace. -/
theorem tildeBasicOpenAcyclic : TildeBasicOpenAcyclic.{u} := by
  intro R _ M f n hn
  have h := tilde_sectionCohomology_basic M f n hn
  obtain ⟨e, -⟩ := SheafCohomology.locality (Spec R).ringCatSheaf (D f)
  exact ⟨h, h.of_iso ((e n).app (tilde M)).symm⟩

/-- Positive cohomology on the whole affine spectrum vanishes. -/
theorem tildeAffineAcyclic : TildeAffineAcyclic.{u} := by
  intro R _ M n hn
  have h : D (1 : R) = (⊤ : (Spec R).Opens) := PrimeSpectrum.basicOpen_one
  exact h ▸ tilde_sectionCohomology_basic M (1 : R) n hn

private lemma basicOpen_finset_prod (s : Finset R) :
    D (∏ f ∈ s, f) = s.inf D := by
  classical
  induction s using Finset.induction_on with
  | empty => exact PrimeSpectrum.basicOpen_one
  | @insert f s hf ih =>
    rw [Finset.prod_insert hf, Finset.inf_insert]
    calc
      D (f * ∏ g ∈ s, g) = D f ⊓ D (∏ g ∈ s, g) := PrimeSpectrum.basicOpen_mul _ _
      _ = D f ⊓ s.inf D := congrArg (D f ⊓ ·) ih

theorem tildeBasicOpenIntersectionAcyclic : TildeBasicOpenIntersectionAcyclic.{u} := by
  intro R _ M s n hn
  exact basicOpen_finset_prod s ▸ tildeBasicOpenAcyclic R M (∏ f ∈ s, f) n hn

open AdvancedHomologicalAlgebra.SheafUniverseTransport
open Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients

/-- In a common universe the coefficient lift is removed by the sectionwise
linear isomorphism `ULift.moduleEquiv`. -/
private def unliftCoefficients (R : CommRingCat.{u}) (M : (Spec R).Modules) :
    (liftSheafCoefficients.{u,u,u,u} (Spec R).ringCatSheaf).obj M ≅ M :=
  (SheafOfModules.fullyFaithfulForget (Spec R).ringCatSheaf).preimageIso
    (PresheafOfModules.isoMk (fun _ => ULift.moduleEquiv.toModuleIso) (by intros; rfl))

theorem tildeBasicOpenCoefficientAcyclic : TildeBasicOpenCoefficientAcyclic.{u} := by
  intro R _ M f n hn
  have h := tilde_sectionCohomology_basic M f n hn
  change IsZero ((sectionCohomology (Spec R).ringCatSheaf (D f) n).obj
    ((liftSheafCoefficients.{u,u,u,u} (Spec R).ringCatSheaf).obj (tilde M)))
  exact h.of_iso ((sectionCohomology (Spec R).ringCatSheaf (D f) n).mapIso
    (unliftCoefficients R (tilde M)))

end Cohomology

end CommutativeAlgebraNotes
