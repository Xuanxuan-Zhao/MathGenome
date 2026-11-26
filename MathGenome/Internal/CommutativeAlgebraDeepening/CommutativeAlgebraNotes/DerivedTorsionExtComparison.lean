import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.IdealTorsion
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.DerivedTorsionExtComparison
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.LinearAlgebra.Isomorphisms

/-! Comparison between derived sections with support and the Ext colimit. -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open Specs.CommutativeAlgebraNotes.DerivedTorsionExtComparison

namespace CommutativeAlgebraNotes

universe v u

noncomputable section

variable {R : Type u} [CommRing R] [Small.{v} R] (I : Ideal R)

private lemma powerQuotientMap_one {m n : ℕ} (h : m ≤ n) :
    powerQuotientMap.{v} I h (quotientOne I n) = quotientOne I m := by
  change (quotientLinearEquiv I m).symm
    (Submodule.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ h)) (quotientLinearEquiv I n ((quotientLinearEquiv I n).symm 1))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

omit [Small.{v} R] in
private lemma smul_one_quotient (n : ℕ) (r : R) :
    r • (1 : R ⧸ I ^ (n + 1)) = Submodule.Quotient.mk r := by
  change r • Submodule.Quotient.mk 1 = _
  rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]

private lemma quotientOne_smul_eq_zero (n : ℕ) {a : R} (ha : a ∈ I ^ (n + 1)) :
    a • quotientOne.{v} I n = 0 := by
  apply (quotientLinearEquiv I n).injective
  rw [map_smul, quotientOne, LinearEquiv.apply_symm_apply, map_zero, smul_one_quotient]
  exact Submodule.Quotient.mk_eq_zero _ |>.mpr ha

private lemma powerQuotient_hom_ext {n : ℕ} {M : ModuleCat.{v} R}
    {f g : powerQuotient I n ⟶ M}
    (h : f (quotientOne I n) = g (quotientOne I n)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective (I ^ (n + 1) : Ideal R)
    (quotientLinearEquiv I n y)
  have hy : y = r • quotientOne I n := by
    apply (quotientLinearEquiv I n).injective
    rw [map_smul, quotientOne, LinearEquiv.apply_symm_apply, smul_one_quotient, hr]
  change f y = g y
  simp only [hy, map_smul, h]

private def homOfTorsionElement (n : ℕ) {M : ModuleCat.{v} R} (x : M)
    (hx : ∀ a ∈ I ^ (n + 1), a • x = 0) : powerQuotient I n ⟶ M :=
  ModuleCat.ofHom (((I ^ (n + 1) : Ideal R).liftQ (LinearMap.toSpanSingleton R M x)
    (fun a ha => hx a ha)).comp (quotientLinearEquiv I n).toLinearMap)

private lemma homOfTorsionElement_one (n : ℕ) {M : ModuleCat.{v} R} (x : M)
    (hx : ∀ a ∈ I ^ (n + 1), a • x = 0) :
    homOfTorsionElement I n x hx (quotientOne I n) = x := by
  change ((I ^ (n + 1) : Ideal R).liftQ (LinearMap.toSpanSingleton R M x) (fun a ha => hx a ha))
    (quotientLinearEquiv I n ((quotientLinearEquiv I n).symm 1)) = x
  rw [LinearEquiv.apply_symm_apply]
  change (1 : R) • x = x
  exact one_smul R x

private def evalTorsion (n : ℕ) {M : ModuleCat.{v} R} :
    (powerQuotient I n ⟶ M) →ₗ[R] idealTorsion I M where
  toFun f := ⟨f (quotientOne I n), (mem_idealTorsion I _).2
    ⟨n + 1, Nat.succ_pos n, fun a ha => by
      rw [← map_smul, quotientOne_smul_eq_zero I n ha, map_zero]⟩⟩
  map_add' _f _g := by apply Subtype.ext; rfl
  map_smul' a f := by apply Subtype.ext; rfl

private lemma evalTorsion_exists {M : ModuleCat.{v} R} (x : idealTorsion I M) :
    ∃ (n : ℕ) (f : powerQuotient I n ⟶ M), evalTorsion I n f = x := by
  obtain ⟨_ | n, hn, hx⟩ := (mem_idealTorsion I x.val).1 x.property
  · omega
  · exact ⟨n, homOfTorsionElement I n x.val hx,
      Subtype.ext (homOfTorsionElement_one I n x.val hx)⟩

private lemma evalTorsion_injective (n : ℕ) {M : ModuleCat.{v} R} :
    Function.Injective (evalTorsion I n (M := M)) :=
  fun _ _ h => powerQuotient_hom_ext I (congrArg Subtype.val h)

open HomologicalComplex

section CycleClasses

omit [Small.{v} R]

variable (K : CochainComplex (ModuleCat.{v} R) ℕ)

private lemma next_up (q : ℕ) : (ComplexShape.up ℕ).next q = q + 1 :=
  (ComplexShape.up ℕ).next_eq' rfl

private lemma prev_up (q : ℕ) : (ComplexShape.up ℕ).prev q = q - 1 := by
  cases q with
  | zero => exact (ComplexShape.up ℕ).prev_eq_self' 0 (by simp)
  | succ q => exact (ComplexShape.up ℕ).prev_eq' rfl

private def moduleCycle (q : ℕ) (x : K.X q) (hx : K.d q (q + 1) x = 0) :
    K.cycles q := (K.sc q).moduleCatCyclesIso.inv ⟨x, by
      change K.d q ((ComplexShape.up ℕ).next q) x = 0
      rwa [next_up]⟩

private lemma moduleCycle_i (q : ℕ) (x : K.X q) (hx : K.d q (q + 1) x = 0) :
    K.iCycles q (moduleCycle K q x hx) = x :=
  (K.sc q).moduleCatCyclesIso_inv_iCycles_apply _

private lemma cycleClass_surj (q : ℕ) (z : K.homology q) :
    ∃ (x : K.X q) (hx : K.d q (q + 1) x = 0), cycleClass K q x hx = z := by
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ q)).1 inferInstance z
  let x := (K.sc q).moduleCatCyclesIso.hom c
  have hx : K.d q (q + 1) x.val = 0 := by
    have h := x.property
    change K.d q ((ComplexShape.up ℕ).next q) x.val = 0 at h
    rwa [next_up] at h
  exact ⟨x.val, hx, by
    change K.homologyπ q ((K.sc q).moduleCatCyclesIso.inv x) = K.homologyπ q c
    have he := ConcreteCategory.congr_hom ((K.sc q).moduleCatCyclesIso.hom_inv_id) c
    exact congrArg (fun z : (K.sc q).cycles => K.homologyπ q z) he⟩

private lemma cycleClass_eq_zero (q : ℕ) (x : K.X q) (hx : K.d q (q + 1) x = 0) :
    cycleClass K q x hx = 0 ↔ ∃ y : K.X (q - 1), K.d (q - 1) q y = x := by
  let S := K.sc q
  let c : S.moduleCatLeftHomologyData.K := ⟨x, by
    change K.d q ((ComplexShape.up ℕ).next q) x = 0
    rwa [next_up]⟩
  change S.homologyπ (S.moduleCatCyclesIso.inv c) = 0 ↔ _
  have hπ := S.moduleCatCyclesIso_inv_π_apply c
  change S.homologyπ (S.moduleCatCyclesIso.inv c) =
    S.moduleCatHomologyIso.inv (Submodule.Quotient.mk c) at hπ
  let e := S.moduleCatHomologyIso.inv
  have he := (ModuleCat.mono_iff_injective e).1
    (show Mono e from inferInstanceAs (Mono S.moduleCatHomologyIso.inv))
  rw [hπ]
  change e (Submodule.Quotient.mk c) = 0 ↔ _
  have he' : e (Submodule.Quotient.mk c) = 0 ↔ Submodule.Quotient.mk c = 0 :=
    ⟨fun hz => he (hz.trans (map_zero e.hom).symm),
      fun hz => (congrArg (fun t : S.moduleCatLeftHomologyData.H => e t) hz).trans (map_zero e.hom)⟩
  rw [he']
  erw [Submodule.Quotient.mk_eq_zero]
  change (∃ y : K.X ((ComplexShape.up ℕ).prev q), S.moduleCatToCycles y = c) ↔ _
  have he (y : K.X ((ComplexShape.up ℕ).prev q)) :
      S.moduleCatToCycles y = c ↔ K.d ((ComplexShape.up ℕ).prev q) q y = x :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  simp only [he]
  conv_rhs => rw [← prev_up q]

variable {K} {L : CochainComplex (ModuleCat.{v} R) ℕ}

private lemma cycleClass_map (φ : K ⟶ L) (q : ℕ)
    (x : K.X q) (hx : K.d q (q + 1) x = 0) :
    homologyMap φ q (cycleClass K q x hx) =
      cycleClass L q (φ.f q x) (by rw [← ModuleCat.comp_apply, φ.comm,
        ModuleCat.comp_apply, hx, map_zero]) := by
  have he : cyclesMap φ q (moduleCycle K q x hx) =
      moduleCycle L q (φ.f q x) (by rw [← ModuleCat.comp_apply, φ.comm,
        ModuleCat.comp_apply, hx, map_zero]) := by
    apply (ModuleCat.mono_iff_injective (L.iCycles q)).1 inferInstance
    rw [← ModuleCat.comp_apply, cyclesMap_i, ModuleCat.comp_apply, moduleCycle_i, moduleCycle_i]
  change homologyMap φ q (K.homologyπ q (moduleCycle K q x hx)) = L.homologyπ q _
  rw [← ModuleCat.comp_apply, homologyπ_naturality, ModuleCat.comp_apply, he]
  rfl

end CycleClasses

section InjectiveComparison

variable {M : ModuleCat.{v} R} (Q : InjectiveResolution M) (q n : ℕ)

private abbrev ExtCocycle :=
  LinearMap.ker (Linear.rightComp R (powerQuotient I n) (Q.cocomplex.d q (q + 1)))

private def cocycleExt :
    ExtCocycle I Q q n →ₗ[R] Ext (powerQuotient I n) M q where
  toFun f := Q.extMk f.val (q + 1) rfl f.property
  map_add' _f _g := (Q.add_extMk _ _ _ _ _ _).symm
  map_smul' r f := (Q.smul_extMk r f.val (q + 1) rfl _).symm

private lemma cocycleExt_surj : Function.Surjective (cocycleExt I Q q n) := by
  intro e
  obtain ⟨f, hf, rfl⟩ := Q.extMk_surjective e (q + 1) rfl
  exact ⟨⟨f, hf⟩, rfl⟩

private lemma evalTorsion_natural {A B : ModuleCat.{v} R}
    (g : A ⟶ B) (f : powerQuotient I n ⟶ A) :
    evalTorsion I n (f ≫ g) = (idealTorsionFunctor I).map g (evalTorsion I n f) := rfl

private def cocycleEval : ExtCocycle I Q q n →ₗ[R] (torsionComplex I Q).homology q :=
  let K := torsionComplex I Q
  let η := K.sc q
  let e : ExtCocycle I Q q n →ₗ[R] η.moduleCatLeftHomologyData.K :=
    ((evalTorsion I n).comp (ExtCocycle I Q q n).subtype).codRestrict _ (fun f => by
      change K.d q ((ComplexShape.up ℕ).next q) (evalTorsion I n f.val) = 0
      rw [next_up]
      change (idealTorsionFunctor I).map (Q.cocomplex.d q (q + 1)) (evalTorsion I n f.val) = 0
      rw [← evalTorsion_natural I n, show f.val ≫ Q.cocomplex.d q (q + 1) = 0 from f.property,
        map_zero]; rfl)
  (K.homologyπ q).hom.comp (η.moduleCatCyclesIso.inv.hom.comp e)

private lemma cocycleEval_apply (f : ExtCocycle I Q q n) :
    cocycleEval I Q q n f = cycleClass (torsionComplex I Q) q (evalTorsion I n f.val)
      (by change (idealTorsionFunctor I).map (Q.cocomplex.d q (q + 1)) (evalTorsion I n f.val) = 0
          rw [← evalTorsion_natural I n, show f.val ≫ Q.cocomplex.d q (q + 1) = 0 from f.property,
            map_zero]; rfl) := rfl

open CochainComplex HomComplex in
private lemma extMk_zero_iff (f : powerQuotient I n ⟶ Q.cocomplex.X 0)
    (hf : f ≫ Q.cocomplex.d 0 1 = 0) :
    Q.extMk f 1 rfl hf = 0 ↔ f = 0 := by
  rw [← Q.extEquivCohomologyClass.apply_eq_iff_eq]
  simp only [InjectiveResolution.extEquivCohomologyClass_extMk,
    InjectiveResolution.extEquivCohomologyClass_zero, CohomologyClass.mk_eq_zero_iff]
  rw [Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (-1) (by simp)]
  constructor
  · rintro ⟨g, hg⟩
    have hgzero : g = 0 :=
      (CochainComplex.isZero_of_isStrictlyGE Q.cochainComplex 0 (-1)).eq_of_tgt _ _
    apply (cancel_mono (Q.cochainComplexXIso 0 0 rfl).inv).mp
    simpa [hgzero] using hg.symm
  · rintro rfl
    exact ⟨0, by simp⟩

private lemma cocycleExt_ker_le :
    LinearMap.ker (cocycleExt I Q q n) ≤ LinearMap.ker (cocycleEval I Q q n) := by
  intro f hf
  change Q.extMk f.val (q + 1) rfl f.property = 0 at hf
  rw [LinearMap.mem_ker, cocycleEval_apply]
  apply (cycleClass_eq_zero (torsionComplex I Q) q _ _).2
  cases q with
  | zero =>
    have h := (extMk_zero_iff I Q n f.val f.property).1 hf
    exact ⟨0, by simp [h]; rfl⟩
  | succ q =>
    obtain ⟨g, hg⟩ := (Q.extMk_eq_zero_iff _ _ _ _ q rfl).1 hf
    refine ⟨evalTorsion I n g, ?_⟩
    change (idealTorsionFunctor I).map (Q.cocomplex.d q (q + 1)) (evalTorsion I n g) = _
    rw [← evalTorsion_natural, hg]

private def extToTorsionHomology :
    extStage I q M n ⟶ (torsionComplex I Q).homology q :=
  ModuleCat.ofHom ((cocycleExt I Q q n).liftOfSurjective (cocycleExt_surj I Q q n)
    ⟨cocycleEval I Q q n, cocycleExt_ker_le I Q q n⟩)

private lemma extToTorsionHomology_extMk (f : powerQuotient I n ⟶ Q.cocomplex.X q)
    (hf : f ≫ Q.cocomplex.d q (q + 1) = 0) :
    extToTorsionHomology I Q q n (Q.extMk f (q + 1) rfl hf) =
      cycleClass (torsionComplex I Q) q (evalTorsion I n f)
        (by change (idealTorsionFunctor I).map (Q.cocomplex.d q (q + 1)) (evalTorsion I n f) = 0
            rw [← evalTorsion_natural I n, hf, map_zero]; rfl) := by
  change ((cocycleExt I Q q n).liftOfSurjective (cocycleExt_surj I Q q n)
    ⟨cocycleEval I Q q n, cocycleExt_ker_le I Q q n⟩) ((cocycleExt I Q q n) ⟨f, hf⟩) = _
  rw [LinearMap.equivOfSurjective_apply]
  rfl

end InjectiveComparison

section PointwiseComparison

variable {M N : ModuleCat.{v} R} (Q : InjectiveResolution M) (q : ℕ)

private lemma evalTorsion_transition {m n : ℕ} (h : m ≤ n) {A : ModuleCat.{v} R}
    (f : powerQuotient I m ⟶ A) :
    evalTorsion I n (powerQuotientMap I h ≫ f) = evalTorsion I m f := by
  apply Subtype.ext
  change f (powerQuotientMap I h (quotientOne I n)) = f (quotientOne I m)
  rw [powerQuotientMap_one]

private lemma extToTorsionHomology_transition {m n : ℕ} (a : m ⟶ n) :
    ((extPowerDiagram I q).map a).app M ≫ extToTorsionHomology I Q q n =
      extToTorsionHomology I Q q m := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨f, hf, rfl⟩ := Q.extMk_surjective z (q + 1) rfl
  change extToTorsionHomology I Q q n
      ((Ext.mk₀ (powerQuotientMap I (leOfHom a))).comp (Q.extMk f (q + 1) rfl hf) (zero_add q)) =
    extToTorsionHomology I Q q m (Q.extMk f (q + 1) rfl hf)
  rw [Q.mk₀_comp_extMk, extToTorsionHomology_extMk, extToTorsionHomology_extMk]
  congr 1
  exact evalTorsion_transition I (leOfHom a) f

private lemma extToTorsionHomology_natural {Q' : InjectiveResolution N}
    {g : M ⟶ N} (φ : Q.Hom Q' g) (n : ℕ) :
    ((extPowerDiagram I q).obj n).map g ≫ extToTorsionHomology I Q' q n =
      extToTorsionHomology I Q q n ≫
        homologyMap (((idealTorsionFunctor I).mapHomologicalComplex (.up ℕ)).map φ.hom) q := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨f, hf, rfl⟩ := Q.extMk_surjective z (q + 1) rfl
  change extToTorsionHomology I Q' q n ((Q.extMk f (q + 1) rfl hf).comp (Ext.mk₀ g) (add_zero q)) =
    homologyMap (((idealTorsionFunctor I).mapHomologicalComplex (.up ℕ)).map φ.hom) q
      (extToTorsionHomology I Q q n (Q.extMk f (q + 1) rfl hf))
  rw [Q.extMk_comp_mk₀ f (q + 1) rfl hf φ, extToTorsionHomology_extMk,
    extToTorsionHomology_extMk]
  erw [cycleClass_map]
  rfl

/-- On the common injective resolution, every torsion cohomology class comes from a stage. -/
private lemma extToTorsionHomology_surj (z : (torsionComplex I Q).homology q) :
    ∃ (n : ℕ) (e : extStage I q M n), extToTorsionHomology I Q q n e = z := by
  obtain ⟨x, hx, rfl⟩ := cycleClass_surj (torsionComplex I Q) q z
  obtain ⟨n, f, hfx⟩ := evalTorsion_exists I x
  have hf : f ≫ Q.cocomplex.d q (q + 1) = 0 := by
    apply evalTorsion_injective I n
    rw [evalTorsion_natural, map_zero, hfx]
    exact hx
  refine ⟨n, Q.extMk f (q + 1) rfl hf, ?_⟩
  rw [extToTorsionHomology_extMk]
  congr 1

/-- A cycle whose evaluation is a torsion boundary becomes a boundary at a finite stage. -/
private lemma extToTorsionHomology_eventually_zero (n : ℕ) (e : extStage I q M n)
    (he : extToTorsionHomology I Q q n e = 0) :
    ∃ (k : ℕ) (a : n ⟶ k), ((extPowerDiagram I q).map a).app M e = 0 := by
  obtain ⟨f, hf, rfl⟩ := Q.extMk_surjective e (q + 1) rfl
  rw [extToTorsionHomology_extMk] at he
  obtain ⟨y, hy⟩ := (cycleClass_eq_zero (torsionComplex I Q) q _ _).1 he
  cases q with
  | zero =>
    have hzero : (torsionComplex I Q).d 0 0 = 0 :=
      (torsionComplex I Q).shape 0 0 (by decide)
    rw [hzero] at hy
    have h' : evalTorsion I n f = 0 :=
      hy.symm.trans (by simp; rfl)
    have h : f = 0 := evalTorsion_injective I n (h'.trans (map_zero (evalTorsion I n)).symm)
    subst f
    exact ⟨n, 𝟙 n, by simp⟩
  | succ q =>
    change (idealTorsionFunctor I).map (Q.cocomplex.d q (q + 1)) y = evalTorsion I n f at hy
    obtain ⟨m, g, hg⟩ := evalTorsion_exists I y
    let k := max n m
    let a : n ⟶ k := homOfLE (le_max_left n m)
    let b : m ⟶ k := homOfLE (le_max_right n m)
    refine ⟨k, a, ?_⟩
    change (Ext.mk₀ (powerQuotientMap I (leOfHom a))).comp (Q.extMk f (q + 2) rfl hf) (zero_add (q + 1)) = 0
    rw [Q.mk₀_comp_extMk]
    apply (Q.extMk_eq_zero_iff _ _ _ _ q rfl).2
    refine ⟨powerQuotientMap I (leOfHom b) ≫ g, ?_⟩
    apply evalTorsion_injective I k
    rw [evalTorsion_natural, evalTorsion_transition, evalTorsion_transition, hg, hy]

private def extTorsionCocone (q : ℕ) : Cocone (extPowerDiagram.{v} I q) where
  pt := (idealTorsionFunctor I).rightDerived q
  ι :=
    { app := fun n =>
        { app M := extToTorsionHomology I (injectiveResolution M) q n ≫
            ((injectiveResolution M).isoRightDerivedObj (idealTorsionFunctor I) q).inv
          naturality {M N} f := by
            let Q := injectiveResolution M
            let Q' := injectiveResolution N
            let φ : Q.Hom Q' f :=
              ⟨InjectiveResolution.desc f Q' Q, by exact InjectiveResolution.desc_commutes_zero f Q' Q⟩
            change ((extPowerDiagram I q).obj n).map f ≫
                (extToTorsionHomology I Q' q n ≫ (Q'.isoRightDerivedObj (idealTorsionFunctor I) q).inv) =
              (extToTorsionHomology I Q q n ≫ (Q.isoRightDerivedObj (idealTorsionFunctor I) q).inv) ≫
                ((idealTorsionFunctor I).rightDerived q).map f
            erw [← Category.assoc, extToTorsionHomology_natural I Q q φ n, Category.assoc,
              Category.assoc, InjectiveResolution.isoRightDerivedObj_inv_naturality
                f Q Q' φ.hom (by simpa using φ.ι_f_zero_comp_hom_f_zero) (idealTorsionFunctor I) q]
            rfl }
      naturality m n a := by
        apply NatTrans.ext
        funext M
        change ((extPowerDiagram I q).map a).app M ≫
            (extToTorsionHomology I (injectiveResolution M) q n ≫
              ((injectiveResolution M).isoRightDerivedObj (idealTorsionFunctor I) q).inv) =
          (extToTorsionHomology I (injectiveResolution M) q m ≫
            ((injectiveResolution M).isoRightDerivedObj (idealTorsionFunctor I) q).inv) ≫ 𝟙 _
        erw [Category.comp_id, ← Category.assoc, extToTorsionHomology_transition] }

private lemma extTorsionCocone_app (q n : ℕ) {M : ModuleCat.{v} R} (Q : InjectiveResolution M) :
    ((extTorsionCocone I q).ι.app n).app M =
      extToTorsionHomology I Q q n ≫ (Q.isoRightDerivedObj (idealTorsionFunctor I) q).inv := by
  let Q₀ := injectiveResolution M
  let φ : Q₀.Hom Q (𝟙 M) :=
    ⟨InjectiveResolution.desc (𝟙 M) Q Q₀, by exact InjectiveResolution.desc_commutes_zero (𝟙 M) Q Q₀⟩
  have h₁ := extToTorsionHomology_natural I Q₀ q φ n
  have h₂ := InjectiveResolution.isoRightDerivedObj_inv_naturality (𝟙 M) Q₀ Q
    φ.hom (by simpa using φ.ι_f_zero_comp_hom_f_zero) (idealTorsionFunctor I) q
  change ((extPowerDiagram I q).obj n).map (𝟙 M) ≫ extToTorsionHomology I Q q n =
    extToTorsionHomology I Q₀ q n ≫
      homologyMap (((idealTorsionFunctor I).mapHomologicalComplex (.up ℕ)).map φ.hom) q at h₁
  erw [((extPowerDiagram I q).obj n).map_id M, Category.id_comp] at h₁
  erw [((idealTorsionFunctor I).rightDerived q).map_id M, Category.comp_id] at h₂
  change extToTorsionHomology I Q₀ q n ≫ _ = _
  erw [h₂, ← Category.assoc, ← h₁]
  rfl

private def extTorsionCoconeIsColimit (q : ℕ) : IsColimit (extTorsionCocone.{v} I q) := by
  apply evaluationJointlyReflectsColimits
  intro M
  apply isColimitOfReflects (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})
  let D := (extPowerDiagram I q ⋙ (evaluation _ _).obj M) ⋙
    forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{v}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits
      (forget AddCommGrpCat.{v})
  letI := reflectsColimit_of_reflectsIsomorphisms D (forget AddCommGrpCat.{v})
  apply isColimitOfReflects (forget AddCommGrpCat.{v})
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    let Q := injectiveResolution M
    let e := Q.isoRightDerivedObj (idealTorsionFunctor I) q
    obtain ⟨n, z, hz⟩ := extToTorsionHomology_surj I Q q (e.hom x)
    refine ⟨n, z, ?_⟩
    change x = ((extTorsionCocone I q).ι.app n).app M z
    rw [extTorsionCocone_app I q n Q]
    change x = e.inv (extToTorsionHomology I Q q n z)
    rw [hz]
    exact (ConcreteCategory.congr_hom e.hom_inv_id x).symm
  · intro n x y h
    let Q := injectiveResolution M
    change ((extTorsionCocone I q).ι.app n).app M x =
      ((extTorsionCocone I q).ι.app n).app M y at h
    rw [extTorsionCocone_app I q n Q] at h
    let e := Q.isoRightDerivedObj (idealTorsionFunctor I) q
    change e.inv (extToTorsionHomology I Q q n x) =
      e.inv (extToTorsionHomology I Q q n y) at h
    have hxy := (ModuleCat.mono_iff_injective
      (Q.isoRightDerivedObj (idealTorsionFunctor I) q).inv).1 inferInstance h
    have hzero : extToTorsionHomology I Q q n (x - y) = 0 := by
      change (extToTorsionHomology I Q q n).hom (x - y) = 0
      exact ((extToTorsionHomology I Q q n).hom.map_sub x y).trans (sub_eq_zero.mpr hxy)
    obtain ⟨k, a, ha⟩ := extToTorsionHomology_eventually_zero I Q q n (x - y) hzero
    refine ⟨k, a, ?_⟩
    change ((extPowerDiagram I q).map a).app M x = ((extPowerDiagram I q).map a).app M y
    let f := ((extPowerDiagram I q).map a).app M
    change f.hom (x - y) = 0 at ha
    exact sub_eq_zero.mp ((f.hom.map_sub x y).symm.trans ha)

private def extPowerComparisonIso (q : ℕ) :
    (idealTorsionFunctor.{v} I).rightDerived q ≅ extPowerColimit I q :=
  IsColimit.coconePointUniqueUpToIso (extTorsionCoconeIsColimit I q)
    (colimit.isColimit (extPowerDiagram I q))

private lemma extPowerι_comparison_inv (q n : ℕ) :
    extPowerι.{v} I q n ≫ (extPowerComparisonIso I q).inv = (extTorsionCocone I q).ι.app n :=
  (colimit.isColimit (extPowerDiagram I q)).fac (extTorsionCocone I q) n

end PointwiseComparison

section DegreeZero

open CochainComplex HomComplex

private lemma extMk_comp_augmentation {M : ModuleCat.{v} R}
    (Q : InjectiveResolution M) {A : ModuleCat.{v} R} (f : A ⟶ M)
    (hf : (f ≫ Q.ι.f 0) ≫ Q.cocomplex.d 0 1 = 0) :
    Q.extMk (f ≫ Q.ι.f 0) 1 rfl hf = Ext.mk₀ f := by
  let := HasDerivedCategory.standard (ModuleCat.{v} R)
  have hc : Cocycle.fromSingleMk
      ((f ≫ Q.ι.f 0) ≫ (Q.cochainComplexXIso 0 0 rfl).inv) (zero_add (0 : ℤ)) 1 (by simp)
      (by simp [Q.cochainComplex_d 0 1 0 1 rfl rfl, reassoc_of% hf]) =
      Cocycle.ofHom ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map f ≫ Q.ι') := by
    apply Subtype.ext
    apply (Cochain.fromSingleEquiv (zero_add (0 : ℤ))).injective
    rw [Cocycle.fromSingleMk_coe, Cochain.fromSingleEquiv_fromSingleMk]
    simp only [Cochain.fromSingleEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk, Cocycle.ofHom_coe,
      Cochain.ofHom_v, HomologicalComplex.comp_f, Q.ι'_f_zero]
    change _ = (singleObjXSelf (.up ℤ) 0 A).inv ≫
      ((HomologicalComplex.single _ (.up ℤ) 0).map f).f 0 ≫
        (singleObjXSelf (.up ℤ) 0 M).hom ≫ Q.ι.f 0 ≫ _
    rw [← Category.assoc (((HomologicalComplex.single _ (.up ℤ) 0).map f).f 0),
      HomologicalComplex.single_map_f_self]
    erw [Category.assoc f]
  have hs {L K : CochainComplex (ModuleCat.{v} R) ℤ} (g : L ⟶ K) :
      Cocycle.equivHomShift.symm (Cocycle.ofHom g) = ShiftedHom.mk₀ 0 rfl g := by
    ext i
    simp [Cocycle.equivHomShift_symm_apply, Cocycle.homOf_f, Cochain.rightShift_v,
      ShiftedHom.mk₀, CategoryTheory.shiftFunctorZero', CochainComplex.shiftFunctorZero_inv_app_f,
      CochainComplex.shiftFunctorObjXIso]
    rfl
  apply Ext.homEquiv.injective
  change (Q.extMk (f ≫ Q.ι.f 0) 1 rfl hf).hom = (Ext.mk₀ f).hom
  rw [Q.extMk_hom, Ext.mk₀_hom]
  simp only [Int.natCast_zero] at *
  erw [hc, hs, ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp_mk₀, ShiftedHom.mk₀_comp_mk₀]
  congr 1
  simp only [Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
  erw [← (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{v} R) 0).hom.naturality_assoc f]
  simp

private def extZeroTorsion (n : ℕ) (M : ModuleCat.{v} R) :
    extStage I 0 M n ⟶ (idealTorsionFunctor I).obj M :=
  ModuleCat.ofHom ((evalTorsion I n).comp (Ext.linearEquiv₀ (R := R)).toLinearMap)

private lemma extZeroTorsion_mk₀ (n : ℕ) {M : ModuleCat.{v} R}
    (f : powerQuotient I n ⟶ M) : extZeroTorsion I n M (Ext.mk₀ f) = evalTorsion I n f := by
  change evalTorsion I n (Ext.linearEquiv₀ (R := R) (Ext.mk₀ f)) = _
  congr 1
  exact (Ext.linearEquiv₀ (R := R)).symm.injective
    ((Ext.linearEquiv₀ (R := R)).symm_apply_apply (Ext.mk₀ f))

private def extZeroTorsionCocone : Cocone (extPowerDiagram.{v} I 0) where
  pt := idealTorsionFunctor I
  ι :=
    { app n :=
        { app := extZeroTorsion I n
          naturality {M N} f := by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro z
            obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).2 z
            change extZeroTorsion I n N ((Ext.mk₀ g).comp (Ext.mk₀ f) (zero_add 0)) =
              (idealTorsionFunctor I).map f (extZeroTorsion I n M (Ext.mk₀ g))
            rw [Ext.mk₀_comp_mk₀, extZeroTorsion_mk₀, extZeroTorsion_mk₀]
            rfl }
      naturality m n a := by
        apply NatTrans.ext
        funext M
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 z
        change extZeroTorsion I n M
            ((Ext.mk₀ (powerQuotientMap I (leOfHom a))).comp (Ext.mk₀ f) (zero_add 0)) =
          extZeroTorsion I m M (Ext.mk₀ f)
        rw [Ext.mk₀_comp_mk₀, extZeroTorsion_mk₀, extZeroTorsion_mk₀, evalTorsion_transition] }

private lemma extZeroTorsion_toDerived (n : ℕ) (M : ModuleCat.{v} R) :
    extZeroTorsion I n M ≫ (idealTorsionFunctor I).toRightDerivedZero.app M =
      ((extTorsionCocone I 0).ι.app n).app M := by
  let Q := injectiveResolution M
  rw [extTorsionCocone_app I 0 n Q, Q.toRightDerivedZero_eq]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 z
  have hf : (f ≫ Q.ι.f 0) ≫ Q.cocomplex.d 0 1 = 0 := by
    erw [Category.assoc, Q.ι_f_zero_comp_complex_d, comp_zero]
  change (Q.isoRightDerivedObj (idealTorsionFunctor I) 0).inv
    ((torsionComplex I Q).homologyπ 0
      (Q.toRightDerivedZero' (idealTorsionFunctor I) (extZeroTorsion I n M (Ext.mk₀ f)))) =
    (Q.isoRightDerivedObj (idealTorsionFunctor I) 0).inv
      (extToTorsionHomology I Q 0 n (Ext.mk₀ f))
  apply congrArg (fun z : (torsionComplex I Q).homology 0 =>
    (Q.isoRightDerivedObj (idealTorsionFunctor I) 0).inv z)
  rw [extZeroTorsion_mk₀, ← extMk_comp_augmentation Q f hf, extToTorsionHomology_extMk]
  have hx : (torsionComplex I Q).d 0 1 (evalTorsion I n (f ≫ Q.ι.f 0)) = 0 := by
    change (idealTorsionFunctor I).map (Q.cocomplex.d 0 1) (evalTorsion I n (f ≫ Q.ι.f 0)) = 0
    erw [← evalTorsion_natural I n, hf, map_zero]
    rfl
  change (torsionComplex I Q).homologyπ 0
      (Q.toRightDerivedZero' (idealTorsionFunctor I) (evalTorsion I n f)) =
    (torsionComplex I Q).homologyπ 0
      (moduleCycle (torsionComplex I Q) 0 (evalTorsion I n (f ≫ Q.ι.f 0)) hx)
  apply congrArg (fun y : (torsionComplex I Q).cycles 0 => (torsionComplex I Q).homologyπ 0 y)
  apply (ModuleCat.mono_iff_injective ((torsionComplex I Q).iCycles 0)).1 inferInstance
  erw [moduleCycle_i]
  have h := ConcreteCategory.congr_hom
    (Q.toRightDerivedZero'_comp_iCycles (idealTorsionFunctor I)) (evalTorsion I n f)
  exact h.trans (evalTorsion_natural I n (Q.ι.f 0) f).symm

private def extPowerZeroComparison :
    extPowerColimit.{v} I 0 ⟶ idealTorsionFunctor I :=
  colimit.desc _ (extZeroTorsionCocone I)

private lemma extPowerZeroComparison_app (n : ℕ) (M : ModuleCat.{v} R) :
    (extPowerι I 0 n).app M ≫ (extPowerZeroComparison I).app M = extZeroTorsion I n M := by
  have h := colimit.ι_desc (extZeroTorsionCocone I) n
  exact NatTrans.congr_app h M

end DegreeZero

/-- Derived sections with support are the directed colimit of the Ext functors
of the positive-power quotients. The comparison is normalized by evaluation
at the residue class of 1 on every injective resolution. -/
theorem derivedTorsionExtComparison :
    Specs.CommutativeAlgebraNotes.DerivedTorsionExtComparison.extPowerComparison.{v,u} := by
  refine ⟨fun {_} _ _ _ I q => extPowerComparisonIso I q, ?_, ?_⟩
  · intro R _ _ _ I q n M Q f hf x hx h
    have he := NatTrans.congr_app (extPowerι_comparison_inv I q n) M
    change _ = _
    have hw := ConcreteCategory.congr_hom he (Q.extMk f (q + 1) rfl hf)
    change (extPowerComparisonIso I q).inv.app M
        ((extPowerι I q n).app M (Q.extMk f (q + 1) rfl hf)) = _ at hw
    rw [hw, extTorsionCocone_app I q n Q]
    change (Q.isoRightDerivedObj (idealTorsionFunctor I) q).inv (extToTorsionHomology I Q q n
      (Q.extMk f (q + 1) rfl hf)) = _
    rw [extToTorsionHomology_extMk]
    have heval : evalTorsion I n f = x := Subtype.ext h.symm
    subst x
    rfl
  · intro R _ _ _ I
    have hc : extPowerZeroComparison I ≫ (idealTorsionFunctor I).toRightDerivedZero =
        (extPowerComparisonIso I 0).inv := by
      apply colimit.hom_ext
      intro n
      apply NatTrans.ext
      funext M
      change (extPowerι I 0 n).app M ≫ ((extPowerZeroComparison I).app M ≫
          (idealTorsionFunctor I).toRightDerivedZero.app M) =
        (extPowerι I 0 n).app M ≫ (extPowerComparisonIso I 0).inv.app M
      rw [← Category.assoc, extPowerZeroComparison_app, extZeroTorsion_toDerived]
      exact (NatTrans.congr_app (extPowerι_comparison_inv I 0 n) M).symm
    let (M : ModuleCat.{v} R) : IsIso ((extPowerZeroComparison I).app M) := by
      apply (ConcreteCategory.isIso_iff_bijective ((extPowerZeroComparison I).app M)).mpr
      constructor
      · have hm := NatTrans.congr_app hc M
        apply (ModuleCat.mono_iff_injective _).1
        exact mono_of_mono_fac hm
      · intro x
        obtain ⟨n, f, hf⟩ := evalTorsion_exists I x
        refine ⟨(extPowerι I 0 n).app M (Ext.mk₀ f), ?_⟩
        exact (ConcreteCategory.congr_hom (extPowerZeroComparison_app I n M) (Ext.mk₀ f)).trans
          ((extZeroTorsion_mk₀ I n f).trans hf)
    let := NatIso.isIso_of_isIso_app (extPowerZeroComparison I)
    refine ⟨asIso (extPowerZeroComparison I), hc, ?_⟩
    intro n M
    change (extPowerι I 0 n).app M ≫ (extPowerZeroComparison I).app M ≫
      (idealTorsionInclusion I).app M = _
    rw [← Category.assoc, extPowerZeroComparison_app]
    rfl

end

end CommutativeAlgebraNotes
