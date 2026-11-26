import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedTorsionExtComparison
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalCohomologyExactSequence
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.DerivedTorsion
import Batteries.Tactic.OpenPrivate

/-! Derived ideal torsion and compatibility of its Ext comparison with the
long exact sequence. -/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits HomologicalComplex
open CochainComplex HomComplex
open scoped ZeroObject

namespace CommutativeAlgebraNotes

open Specs.CommutativeAlgebraNotes.DerivedTorsion
open Specs.CommutativeAlgebraNotes.DerivedTorsionExtComparison
open Specs.CommutativeAlgebraNotes.LocalCohomologyExactSequence
open Specs.AdvancedHomologicalAlgebra.ExtInjectiveHorseshoe
open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom (injectiveClassMap)
open AdvancedHomologicalAlgebra.ExtShiftedHom (classToDerived_mk)
open AdvancedHomologicalAlgebra.LieHochschildSerre (mapExtendIso mapExtendIso_hom_f)

open private smul_one_quotient quotientOne_smul_eq_zero from
  MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedTorsionExtComparison

universe v u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [Small.{v} R]

abbrev extStageBoundary : extStageBoundaryType.{v,u} :=
  @Specs.CommutativeAlgebraNotes.DerivedTorsion.extStageBoundary.{v,u}

abbrev extPowerBoundary : extPowerBoundaryType.{v,u} :=
  @Specs.CommutativeAlgebraNotes.DerivedTorsion.extPowerBoundary.{v,u}

abbrev extPowerGraded : extPowerGradedType.{v,u} :=
  @Specs.CommutativeAlgebraNotes.DerivedTorsion.extPowerGraded.{v,u}

theorem extPowerι_boundary : extPowerBoundaryOnStagesType.{v,u} := by
  intro R _ _ I S hS q n
  exact (isColimitOfPreserves ((evaluation _ _).obj S.X₃)
    (colimit.isColimit (extPowerDiagram I q))).fac _ n

theorem localCohomology_degree : localCohomologyDegreeType.{v,u} := by
  exact ⟨localCohomology_of_nonneg, localCohomology_of_neg⟩

theorem localCohomology_exact : exactSequenceType.{v,u} :=
  LocalCohomologySequence.exact

theorem localCohomology_naturality : naturalityType.{v,u} :=
  LocalCohomologySequence.naturality

theorem localCohomology_extGraded : gradedExtComparisonType.{v,u} := by
  intro R _ _ _ I q
  cases q with
  | ofNat q =>
    obtain ⟨α, _, _⟩ := derivedTorsionExtComparison.{v,u}
    exact ⟨α I q⟩
  | negSucc _ =>
    let C := ModuleCat.{v} R ⥤ ModuleCat.{v} R
    let e : (0 : C) ≅ ⊥_ C := (isZero_zero _).isoIsInitial initialIsInitial
    let ec := HasColimit.isoOfNatIso ((CategoryTheory.Functor.const ℕ).mapIso e)
    exact ⟨e ≪≫ colimitConstInitial.symm ≪≫ ec.symm⟩

/-- Every element of local cohomology is killed by a positive power of the support ideal. -/
theorem localCohomology_isPowerTorsion : powerTorsionType.{v,u} := by
  intro R _ _ _ I q M x
  cases q with
  | negSucc q =>
    have h := ((CategoryTheory.Functor.isZero_iff (0 : ModuleCat.{v} R ⥤ ModuleCat.{v} R)).1
        (isZero_zero _) M)
    have hx : x = 0 := by
      have he := h.eq_of_src (𝟙 ((localCohomology I (.negSucc q)).obj M)) 0
      simpa using ConcreteCategory.congr_hom he x
    exact ⟨1, le_rfl, fun a _ => by rw [hx, smul_zero]⟩
  | ofNat q =>
    let Q := injectiveResolution M
    let K := torsionComplex I Q
    let e := Q.isoRightDerivedObj (idealTorsionFunctor I) q
    obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ q)).1 inferInstance (e.hom x)
    let z := K.iCycles q y
    obtain ⟨n, hn, hkill⟩ := (mem_idealTorsion I z.val).1 z.property
    refine ⟨n, hn, fun a ha => ?_⟩
    have hz : a • z = 0 := Subtype.ext (hkill a ha)
    have hy' : a • y = 0 := by
      apply (ModuleCat.mono_iff_injective (K.iCycles q)).1 inferInstance
      rw [map_smul, map_zero]
      exact hz
    apply (ModuleCat.mono_iff_injective e.hom).1 inferInstance
    rw [map_smul, map_zero]
    calc
      a • e.hom x = a • K.homologyπ q y := congrArg (fun t : K.homology q => a • t) hy.symm
      _ = 0 := by rw [← map_smul, hy', map_zero]

/-- A map out of a quotient by a power of the ideal lands in the torsion submodule. -/
private def factorThroughTorsion (I : Ideal R) (n : ℕ) {M : ModuleCat.{v} R}
    (f : powerQuotient I n ⟶ M) : powerQuotient I n ⟶ (idealTorsionFunctor I).obj M :=
  ModuleCat.ofHom (f.hom.codRestrict _ fun x => (mem_idealTorsion I _).2
    ⟨n + 1, Nat.succ_pos n, fun a ha => by
      obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective (I ^ (n + 1) : Ideal R)
        (quotientLinearEquiv I n x)
      have hx : x = r • quotientOne I n := by
        apply (quotientLinearEquiv I n).injective
        rw [map_smul, quotientOne, LinearEquiv.apply_symm_apply, smul_one_quotient, hr]
      change a • f x = 0
      rw [← map_smul, hx, smul_comm a r, quotientOne_smul_eq_zero I n ha, smul_zero,
        map_zero]⟩)

/-- The homology morphism associated to a morphism landing in the cycles. -/
private def classOfCycle {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} R) c) {D : ModuleCat.{v} R}
    {i j : ι} (hij : c.Rel i j) (f : D ⟶ K.X i) (hf : f ≫ K.d i j = 0) :
    D ⟶ K.homology i :=
  K.liftCycles f j (c.next_eq' hij) hf ≫ K.homologyπ i

omit [Small.{v} R] in
private lemma classOfCycle_apply (K : CochainComplex (ModuleCat.{v} R) ℕ)
    (i : ℕ) {D : ModuleCat.{v} R} (f : D ⟶ K.X i) (hf : f ≫ K.d i (i + 1) = 0) (x : D) :
    classOfCycle K (show (ComplexShape.up ℕ).Rel i (i + 1) from rfl) f hf x =
      cycleClass K i (f x) (by
        simpa using ConcreteCategory.congr_hom hf x) := by
  let j := i + 1
  let h : (ComplexShape.up ℕ).next i = j := (ComplexShape.up ℕ).next_eq' rfl
  let z : (K.sc i).moduleCatLeftHomologyData.K := ⟨f x, by
    change K.d i ((ComplexShape.up ℕ).next i) (f x) = 0
    rw [h]
    simpa using ConcreteCategory.congr_hom hf x⟩
  have he : K.liftCycles f j h hf x = (K.sc i).moduleCatCyclesIso.inv z := by
    apply (ModuleCat.mono_iff_injective (K.iCycles i)).1 inferInstance
    rw [← ModuleCat.comp_apply, liftCycles_i]
    exact ((K.sc i).moduleCatCyclesIso_inv_iCycles_apply z).symm
  change K.homologyπ i (K.liftCycles f j h hf x) = K.homologyπ i _
  rw [he]

omit [Small.{v} R] in
private lemma mapExtendIso_inv_f (I : Ideal R) {M : ModuleCat.{v} R}
    (P : InjectiveResolution M) (q : ℕ) :
    (mapExtendIso (idealTorsionFunctor I) ComplexShape.embeddingUpNat P.cocomplex).inv.f
        (q : ℤ) =
      ((torsionComplex I P).extendXIso ComplexShape.embeddingUpNat
          (rfl : ComplexShape.embeddingUpNat.f q = (q : ℤ))).hom ≫
        (idealTorsionFunctor I).map (P.cochainComplexXIso q q rfl).inv := by
  let F := idealTorsionFunctor I
  let e := ComplexShape.embeddingUpNat
  let K := torsionComplex I P
  let T := mapExtendIso F e P.cocomplex
  have h : T.hom.f (q : ℤ) =
      F.map (P.cochainComplexXIso q q rfl).hom ≫
        (K.extendXIso e (rfl : e.f q = (q : ℤ))).inv :=
    mapExtendIso_hom_f F e P.cocomplex (rfl : e.f q = (q : ℤ))
  change T.inv.f (q : ℤ) = _
  have hcomp : T.hom.f (q : ℤ) ≫ T.inv.f (q : ℤ) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
  have hcomp' : T.inv.f (q : ℤ) ≫ T.hom.f (q : ℤ) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  let : Epi (T.hom.f (q : ℤ)) := epi_of_epi_fac hcomp'
  apply (cancel_epi (T.hom.f (q : ℤ))).1
  rw [hcomp, h, Category.assoc, Iso.inv_hom_id_assoc, ← F.map_comp, Iso.hom_inv_id, F.map_id]
  rfl

omit [Small.{v} R] in
private lemma extendResolutionIso_classOfCycle (I : Ideal R) {M D : ModuleCat.{v} R}
    (P : InjectiveResolution M) (q : ℕ) (f : D ⟶ (torsionComplex I P).X q)
    (hf : f ≫ (torsionComplex I P).d q (q + 1) = 0) :
    let F := idealTorsionFunctor I
    let L := (F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex
    let g := f ≫ F.map (P.cochainComplexXIso q q rfl).inv
    let hg : g ≫ L.d (q : ℤ) ((q + 1 : ℕ) : ℤ) = 0 := by
      rw [Functor.mapHomologicalComplex_obj_d, P.cochainComplex_d (q : ℤ)
        ((q + 1 : ℕ) : ℤ) q (q + 1) rfl rfl, Functor.map_comp, Functor.map_comp,
        Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
      have hw : f ≫ F.map (P.cocomplex.d q (q + 1)) = 0 := hf
      rw [reassoc_of% hw, zero_comp]
    classOfCycle (torsionComplex I P) (show (ComplexShape.up ℕ).Rel q (q + 1) from rfl) f hf ≫
        (extendResolutionIso I q P).hom =
      classOfCycle L
        (show (ComplexShape.up ℤ).Rel (q : ℤ) ((q + 1 : ℕ) : ℤ) from rfl) g hg := by
  let F := idealTorsionFunctor I
  let e := ComplexShape.embeddingUpNat
  let K := torsionComplex I P
  let L := (F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex
  let hi : e.f q = (q : ℤ) := rfl
  let T : L ≅ K.extend e := mapExtendIso F e P.cocomplex
  intro F' L' g hg
  have hr := (show (ComplexShape.up ℕ).Rel q (q + 1) from rfl)
  have hr' := (show (ComplexShape.up ℤ).Rel (q : ℤ) ((q + 1 : ℕ) : ℤ) from rfl)
  rw [classOfCycle, extendResolutionIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  change (_ ≫ K.homologyπ q) ≫ (K.extendHomologyIso e hi).inv ≫
    homologyMap T.inv (q : ℤ) = _
  rw [Category.assoc, homologyπ_extendHomologyIso_inv_assoc, homologyπ_naturality, classOfCycle]
  have he :
      K.liftCycles f (q + 1) ((ComplexShape.up ℕ).next_eq' hr) hf ≫
          (K.extendCyclesIso e hi).inv ≫ cyclesMap T.inv (q : ℤ) =
        L.liftCycles g ((q + 1 : ℕ) : ℤ) ((ComplexShape.up ℤ).next_eq' hr') hg := by
    apply (cancel_mono (L.iCycles (q : ℤ))).mp
    simp only [Category.assoc, cyclesMap_i, extendCyclesIso_inv_iCycles_assoc,
      liftCycles_i_assoc, liftCycles_i]
    have hT : T.inv.f (q : ℤ) = (K.extendXIso e hi).hom ≫
        F.map (P.cochainComplexXIso q q rfl).inv := mapExtendIso_inv_f I P q
    rw [hT, Iso.inv_hom_id_assoc]
  change ((K.liftCycles f (q + 1) ((ComplexShape.up ℕ).next_eq' hr) hf ≫
    (K.extendCyclesIso e hi).inv) ≫ cyclesMap T.inv (q : ℤ)) ≫ L.homologyπ (q : ℤ) =
    L.liftCycles g ((q + 1 : ℕ) : ℤ) ((ComplexShape.up ℤ).next_eq' hr') hg ≫ L.homologyπ (q : ℤ)
  rw [Category.assoc _ (K.extendCyclesIso e hi).inv, he]

local instance : HasDerivedCategory (ModuleCat.{v} R) := HasDerivedCategory.standard _

private lemma injectiveClassMap_eq_ext_hom {X M : ModuleCat.{v} R}
    (P : InjectiveResolution M) (q : ℕ) (z : Cocycle (Stalk X) P.cochainComplex (q : ℤ)) :
    injectiveClassMap X M P.cochainComplex P.ι' inferInstance (q : ℤ) (.mk z) =
      (P.extEquivCohomologyClass.symm (.mk z) : Ext X M q).hom := by
  rw [P.extEquivCohomologyClass_symm_mk_hom, injectiveClassMap, classToDerived_mk]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, ShiftedHom.mk₀_id_comp, ShiftedHom.comp_mk₀,
    ShiftedHom.map, Category.assoc]
  erw [Category.comp_id]

private lemma factorThroughTorsion_comp (I : Ideal R) (n : ℕ) {M N : ModuleCat.{v} R}
    (f : powerQuotient I n ⟶ M) (g : M ⟶ N) :
    factorThroughTorsion I n (f ≫ g) =
      factorThroughTorsion I n f ≫ (idealTorsionFunctor I).map g := rfl

private lemma factorThroughTorsion_zero (I : Ideal R) (n : ℕ) (M : ModuleCat.{v} R) :
    factorThroughTorsion I n (0 : powerQuotient I n ⟶ M) = 0 := rfl

private def extendedCocycle {X : ModuleCat.{v} R} {K : CochainComplex (ModuleCat.{v} R) ℤ}
    {q : ℤ} (f : X ⟶ K.X q) (hf : f ≫ K.d q (q + 1) = 0) : Cocycle (Stalk X) K q :=
  Cocycle.fromSingleMk f (zero_add q) (q + 1) rfl hf

private lemma comparison_on_extended_resolution [IsNoetherianRing R]
    (α : extPowerComparisonType.{v,u}) (hα : extPowerComparisonOnCocycles α)
    (I : Ideal R) (q n : ℕ) {M : ModuleCat.{v} R} (P : InjectiveResolution M)
    (f : powerQuotient I n ⟶ P.cochainComplex.X (q : ℤ))
    (hf : f ≫ P.cochainComplex.d (q : ℤ) ((q : ℤ) + 1) = 0) :
    let F := idealTorsionFunctor I
    let L := (F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex
    let g := factorThroughTorsion I n f
    let hg : g ≫ L.d (q : ℤ) ((q + 1 : ℕ) : ℤ) = 0 := by
      change g ≫ F.map (P.cochainComplex.d (q : ℤ) ((q : ℤ) + 1)) = 0
      rw [← factorThroughTorsion_comp, hf, factorThroughTorsion_zero]
    let x : extStage I q M n := P.extEquivCohomologyClass.symm (.mk (extendedCocycle f hf))
    (resolutionIso I q P).hom ((α I q).inv.app M ((extPowerι I q n).app M x)) =
      classOfCycle L
        (show (ComplexShape.up ℤ).Rel (q : ℤ) ((q + 1 : ℕ) : ℤ) from rfl) g hg
        (quotientOne I n) := by
  intro F L g hg x
  let f₀ := f ≫ (P.cochainComplexXIso q q rfl).hom
  have hf₀ : f₀ ≫ P.cocomplex.d q (q + 1) = 0 := by
    apply (cancel_mono (P.cochainComplexXIso (q + 1 : ℕ) (q + 1) rfl).inv).mp
    change (f ≫ (P.cochainComplexXIso q q rfl).hom) ≫ P.cocomplex.d q (q + 1) ≫ _ = 0 ≫ _
    simp only [Category.assoc, ← P.cochainComplex_d (q : ℤ) ((q + 1 : ℕ) : ℤ)
      q (q + 1) rfl rfl, zero_comp]
    exact hf
  have he : f₀ ≫ (P.cochainComplexXIso q q rfl).inv = f := by
    change (f ≫ (P.cochainComplexXIso q q rfl).hom) ≫ (P.cochainComplexXIso q q rfl).inv = f
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hext : x = P.extMk f₀ (q + 1) rfl hf₀ := by
    change P.extEquivCohomologyClass.symm (.mk (extendedCocycle f hf)) = _
    unfold InjectiveResolution.extMk
    apply congrArg P.extEquivCohomologyClass.symm
    apply congrArg CohomologyClass.mk
    apply Cocycle.ext
    exact congrArg (fun t => Cochain.fromSingleMk t (zero_add (q : ℤ))) he.symm
  let g₀ := factorThroughTorsion I n f₀
  have hg₀ : g₀ ≫ (torsionComplex I P).d q (q + 1) = 0 := by
    change g₀ ≫ F.map (P.cocomplex.d q (q + 1)) = 0
    rw [← factorThroughTorsion_comp, hf₀, factorThroughTorsion_zero]
  have hval : (g₀ (quotientOne I n)).val = f₀ (quotientOne I n) := rfl
  have hcycle : (torsionComplex I P).d q (q + 1) (g₀ (quotientOne I n)) = 0 := by
    simpa using ConcreteCategory.congr_hom hg₀ (quotientOne I n)
  rw [hext, hα I q n P f₀ hf₀ _ hcycle hval]
  let K := torsionComplex I P
  let e : ((F.rightDerived q).obj M) ≅ K.homology q := P.isoRightDerivedObj F q
  let t : K.homology q ≅ L.homology (q : ℤ) := extendResolutionIso I q P
  change (e.inv ≫ e.hom ≫ t.hom) (cycleClass K q _ hcycle) = _
  rw [Iso.inv_hom_id_assoc]
  have hcomp := extendResolutionIso_classOfCycle I P q g₀ hg₀
  have hfactor : g₀ ≫ F.map (P.cochainComplexXIso q q rfl).inv = g := by
    rw [← factorThroughTorsion_comp, he]
  have hclass :
      classOfCycle (torsionComplex I P) (show (ComplexShape.up ℕ).Rel q (q + 1) from rfl) g₀ hg₀ ≫
        (extendResolutionIso I q P).hom =
      classOfCycle L
        (show (ComplexShape.up ℤ).Rel (q : ℤ) ((q + 1 : ℕ) : ℤ) from rfl) g hg := by
    refine hcomp.trans ?_
    congr 1
  have heval := classOfCycle_apply K q g₀ hg₀ (quotientOne I n)
  refine (congrArg (fun c : K.homology q => t.hom c) heval.symm).trans ?_
  exact ConcreteCategory.congr_hom hclass (quotientOne I n)

private lemma compare_stage_boundary [IsNoetherianRing R]
    (α : extPowerComparisonType.{v,u}) (hα : extPowerComparisonOnCocycles α)
    (I : Ideal R) {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    (q n : ℕ) :
    (extPowerι I q n).app S.X₃ ≫ (α I q).inv.app S.X₃ ≫ LocalCohomologySequence.δ I hS (q : ℤ) =
      extStageBoundary I hS q n ≫ (extPowerι I (q + 1) n).app S.X₁ ≫ (α I (q + 1)).inv.app S.X₁ := by
  let P := injectiveResolution S.X₁
  let Q := injectiveResolution S.X₃
  obtain ⟨H, hH⟩ := existsResolvingRow hS P Q
  let F := idealTorsionFunctor I
  let T := H.row
  let K := T.map (F.mapHomologicalComplex (.up ℤ))
  let hK : K.ShortExact := mappedShortExact I hH.2.2.2
  let U := powerQuotient I n
  let k : ℤ := q
  have hk : k + 1 = ((q + 1 : ℕ) : ℤ) := rfl
  apply (cancel_mono (resolutionIso I (q + 1) P).hom).mp
  have hδ := LocalCohomologySequence.δ_on_horseshoe I hS P Q H hH q
  change LocalCohomologySequence.δ I hS (q : ℤ) ≫ (resolutionIso I (q + 1) P).hom =
    (resolutionIso I q Q).hom ≫ hK.δ k (k + 1) rfl at hδ
  simp only [Category.assoc, hδ]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro (x : Ext U S.X₃ q)
  obtain ⟨f, hf, rfl⟩ := Q.extMk_surjective x (q + 1) rfl
  let z := f ≫ (Q.cochainComplexXIso q q rfl).inv
  have hz : z ≫ T.X₃.d k (k + 1) = 0 := by
    change (f ≫ (Q.cochainComplexXIso q q rfl).inv) ≫ Q.cochainComplex.d (q : ℤ) (k + 1) = 0
    rw [hk, Q.cochainComplex_d _ _ q (q + 1) rfl rfl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hf, zero_comp]
  let σ := (hH.2.2.2 k).some
  let b : U ⟶ T.X₂.X k := z ≫ σ.s
  have hb : b ≫ T.g.f k = z := by
    have hs : σ.s ≫ T.g.f k = 𝟙 (T.X₃.X k) := σ.s_g
    change (z ≫ σ.s) ≫ T.g.f k = z
    rw [Category.assoc, hs, Category.comp_id]
  have hd : (b ≫ T.X₂.d k (k + 1)) ≫ T.g.f (k + 1) = 0 := by
    rw [Category.assoc, ← T.g.comm, ← Category.assoc, hb, hz]
  let h₁ : (T.map (eval _ (.up ℤ) (k + 1))).ShortExact := hH.1.map_of_exact _
  let h₂ : (T.map (eval _ (.up ℤ) (k + 1 + 1))).ShortExact := hH.1.map_of_exact _
  let : Mono (T.f.f (k + 1 + 1)) := h₂.mono_f
  let : Mono (T.map (eval _ (.up ℤ) (k + 1))).f := h₁.mono_f
  let a : U ⟶ T.X₁.X (k + 1) := h₁.exact.lift (b ≫ T.X₂.d k (k + 1)) hd
  have ha : a ≫ T.f.f (k + 1) = b ≫ T.X₂.d k (k + 1) := h₁.exact.lift_f _ _
  have hac : a ≫ T.X₁.d (k + 1) (k + 1 + 1) = 0 := by
    apply (cancel_mono (T.f.f (k + 1 + 1))).mp
    rw [Category.assoc, ← T.f.comm, ← Category.assoc, ha, Category.assoc, d_comp_d,
      comp_zero, zero_comp]
  let zc := extendedCocycle (K := T.X₃) (q := k) z hz
  let ac := extendedCocycle (K := T.X₁) (q := k + 1) a hac
  let bc := Cochain.fromSingleMk b (zero_add k)
  have hbc : bc.comp (Cochain.ofHom T.g) (add_zero k) = zc.1 := by
    change (Cochain.fromSingleMk b (zero_add k)).comp (Cochain.ofHom T.g) (add_zero k) =
      Cochain.fromSingleMk z (zero_add k)
    rw [← Cochain.fromSingleMk_postcomp, hb]
  have hac' : HomComplex.δ k (k + 1) bc = (ac.postcomp T.f).1 := by
    change HomComplex.δ k (k + 1) (Cochain.fromSingleMk b (zero_add k)) =
      (Cochain.fromSingleMk a (zero_add (k + 1))).comp (Cochain.ofHom T.f) (add_zero (k + 1))
    rw [Cochain.δ_fromSingleMk _ _ _ (k + 1) (zero_add (k + 1)),
      ← Cochain.fromSingleMk_postcomp, ha]
  have hExt := AdvancedHomologicalAlgebra.ExtBoundarySigns.ordinary_second
    (ModuleCat.{v} R) S hS H.row hH.1 H.map inferInstance hH.2.2.1 inferInstance
    U k zc ac bc hbc hac'
  let ez : extStage I q S.X₃ n := Q.extEquivCohomologyClass.symm (.mk zc)
  let ea : extStage I (q + 1) S.X₁ n := P.extEquivCohomologyClass.symm (.mk ac)
  have hez : ez = Q.extMk f (q + 1) rfl hf := rfl
  have hea : extStageBoundary I hS q n ez = ea := by
    apply Ext.ext
    change (ez.comp hS.extClass rfl).hom = ea.hom
    rw [Ext.comp_hom, hS.extClass_hom]
    exact ((injectiveClassMap_eq_ext_hom P (q + 1) ac).symm.trans
      (hExt.trans (congrArg (fun t => ShiftedHom.comp t hS.singleδ (add_comm 1 k))
        (injectiveClassMap_eq_ext_hom Q q zc)))).symm
  change hK.δ k (k + 1) rfl ((resolutionIso I q Q).hom
      ((α I q).inv.app S.X₃ ((extPowerι I q n).app S.X₃ (Q.extMk f (q + 1) rfl hf)))) =
    (resolutionIso I (q + 1) P).hom ((α I (q + 1)).inv.app S.X₁
      ((extPowerι I (q + 1) n).app S.X₁
        (extStageBoundary I hS q n (Q.extMk f (q + 1) rfl hf))))
  rw [← hez, hea, comparison_on_extended_resolution α hα I q n Q z hz,
    comparison_on_extended_resolution α hα I (q + 1) n P a hac]
  let z' := factorThroughTorsion I n z
  let b' := factorThroughTorsion I n b
  let a' := factorThroughTorsion I n a
  have hz' : z' ≫ K.X₃.d k (k + 1) = 0 := by
    change z' ≫ F.map (T.X₃.d k (k + 1)) = 0
    rw [← factorThroughTorsion_comp, hz, factorThroughTorsion_zero]
  have hb' : b' ≫ K.g.f k = z' := by
    change b' ≫ F.map (T.g.f k) = z'
    rw [← factorThroughTorsion_comp, hb]
  have ha' : a' ≫ K.f.f (k + 1) = b' ≫ K.X₂.d k (k + 1) := by
    change a' ≫ F.map (T.f.f (k + 1)) = b' ≫ F.map (T.X₂.d k (k + 1))
    rw [← factorThroughTorsion_comp, ha, factorThroughTorsion_comp]
  have hnext : (ComplexShape.up ℤ).next (k + 1) = k + 1 + 1 :=
    (ComplexShape.up ℤ).next_eq' rfl
  exact ConcreteCategory.congr_hom (hK.δ_eq k (k + 1) rfl z' hz' b' hb' a' ha'
    (k + 1 + 1) hnext) (quotientOne I n)

/-- The Ext-limit isomorphism carries the cochain boundary to postcomposition
by the extension class at each stage and hence on the colimit. -/
theorem localCohomology_extBoundaryComparison : extPowerBoundaryComparisonType.{v,u} := by
  obtain ⟨α, hα, hedge⟩ := derivedTorsionExtComparison.{v,u}
  refine ⟨α, hα, hedge, ?_⟩
  intro R _ _ _ I S hS q
  have hc : (α I q).inv.app S.X₃ ≫ LocalCohomologySequence.δ I hS (q : ℤ) =
      extPowerBoundary I hS q ≫ (α I (q + 1)).inv.app S.X₁ := by
    apply (isColimitOfPreserves ((evaluation _ _).obj S.X₃)
      (colimit.isColimit (extPowerDiagram I q))).hom_ext
    intro n
    change (extPowerι I q n).app S.X₃ ≫ _ = (extPowerι I q n).app S.X₃ ≫ _
    rw [← Category.assoc _ (extPowerBoundary I hS q), extPowerι_boundary]
    simpa only [Category.assoc] using compare_stage_boundary α hα I hS q n
  change LocalCohomologySequence.δ I hS (q : ℤ) ≫ _ = _
  calc
    _ = (α I q).hom.app S.X₃ ≫
        ((α I q).inv.app S.X₃ ≫ LocalCohomologySequence.δ I hS (q : ℤ)) ≫
          (α I (q + 1)).hom.app S.X₁ := by
        simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    _ = _ := by rw [hc]; simp

end

end CommutativeAlgebraNotes
