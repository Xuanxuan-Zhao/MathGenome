import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.KProjectiveClosure
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.KProjectiveInvariance
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

open CategoryTheory HomologicalComplex CochainComplex.HomComplex

open CochainComplex (mappingCone)

universe u v w z

namespace DerivedFormalization.RightDGModule

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}
variable {M N P : RightDGModule A}

open Specs.DerivedFormalization.DG.HomComplex (HomotopyEquation)

open private acyclic_iff_boundaries gradedHom_ext_apply
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.KProjectiveClosure

/-- Postcomposition by a strict right dg module map on Hom complexes. -/
abbrev homComplexMap (P : RightDGModule A) (f : M ⟶ N) :
    homComplex P M ⟶ homComplex P N :=
  Specs.DerivedFormalization.DG.KProjectiveInvariance.homComplexMap P f

/-- An acyclic K-projective module admits a right-linear contraction. -/
theorem IsKProjective.contractible_of_acyclic (hP : P.IsKProjective) (hacyclic : P.Acyclic) :
    ∃ h : GradedHom P P (-1),
      HomotopyEquation (𝟙 P) (0 : P ⟶ P) h := by
  have boundaries := (acyclic_iff_boundaries (homComplex P P)).mp (hP P hacyclic) (-1)
  rw [show (-1 : ℤ) + 1 = 0 by decide] at boundaries
  obtain ⟨h, hh⟩ := boundaries (strictCycle (𝟙 P)).val (strictCycle (𝟙 P)).property
  refine ⟨h, fun a i x => ?_⟩
  have he := congrArg (fun g : GradedHom P P 0 => g.app a i i (add_zero i) x) hh
  rw [boundary_component] at he
  change _ = (CochainComplex.HomComplex.Cochain.ofHom ((𝟙 P : P ⟶ P).app a)).v i i
    (add_zero i) x at he
  rw [CochainComplex.HomComplex.Cochain.ofHom_v] at he
  simpa only [RightDGModuleModel.zero_app, HomologicalComplex.zero_f,
    ModuleCat.hom_zero, LinearMap.zero_apply, sub_zero] using he.symm

@[simp] private theorem gradedHom_add_app {r : ℤ} (g h : GradedHom M N r)
    (a : A.Obj) (i q : ℤ) (e : i+r = q) (x : (M.complex a).X i) :
    (g + h).app a i q e x = g.app a i q e x + h.app a i q e x := by
  change (g.val a + h.val a).v i q e x = _
  simp only [Cochain.add_v, ModuleCat.hom_add, LinearMap.add_apply]

@[simp] private theorem gradedHom_smul_app {r : ℤ} (c : k) (g : GradedHom M N r)
    (a : A.Obj) (i q : ℤ) (e : i+r = q) (x : (M.complex a).X i) :
    (c • g).app a i q e x = c • g.app a i q e x := by
  change (c • g.val a).v i q e x = _
  simp only [Cochain.smul_v, ModuleCat.hom_smul, LinearMap.smul_apply]

@[simp] private theorem gradedHom_neg_app {r : ℤ} (g : GradedHom M N r)
    (a : A.Obj) (i q : ℤ) (e : i+r = q) (x : (M.complex a).X i) :
    (-g).app a i q e x = -g.app a i q e x := by
  change (-g.val a).v i q e x = _
  simp only [Cochain.neg_v, ModuleCat.hom_neg, LinearMap.neg_apply]

/-- Postcomposition acts by applying the strict map to each homogeneous component. -/
theorem homComplexMap_app (f : M ⟶ N) {r : ℤ} (g : GradedHom P M r)
    (a : A.Obj) (i q : ℤ) (e : i+r = q) (x : (P.complex a).X i) :
    GradedHom.app ((homComplexMap P f).f r g) a i q e x =
      (f.app a).f q (g.app a i q e x) := by
  change GradedHom.app ((dgCategory A).comp 0 r r (zero_add r) (strictCycle f).val g)
    a i q e x = _
  rw [compositionFormula 0 r r (zero_add r) _ _ a i q q e (add_zero q)]
  change (Cochain.ofHom (f.app a)).v q q (add_zero q) (g.app a i q e x) = _
  rw [Cochain.ofHom_v]

private def coneHomTarget (f : M ⟶ N) (r : ℤ) :
    GradedHom P (cone f) r →ₗ[k] GradedHom P N r where
  toFun g := GradedHom.mk
    (fun a i q e => g.app a i q e ≫ ModuleCat.ofHom (LinearMap.fst _ _ _))
    (by
      intro a b i j n ir nr h hi hn x z
      exact congrArg Prod.fst (g.comm_act i j n ir nr h hi hn x z))
  map_add' g h := gradedHom_ext_apply fun a i q e x =>
    show ((g + h).app a i q e x).1 = (g.app a i q e x).1 + (h.app a i q e x).1 by
      rw [gradedHom_add_app]
      rfl
  map_smul' c g := gradedHom_ext_apply fun a i q e x =>
    show ((c • g).app a i q e x).1 = c • (g.app a i q e x).1 by
      rw [gradedHom_smul_app]
      rfl

@[simp] private theorem coneHomTarget_app (f : M ⟶ N) {r : ℤ} (g : GradedHom P (cone f) r)
    (a : A.Obj) (i q : ℤ) (e : i+r = q) (x : (P.complex a).X i) :
    (coneHomTarget f r g).app a i q e x = (g.app a i q e x).1 := rfl

private def coneHomSourceApp (f : M ⟶ N) {r : ℤ} (g : GradedHom P (cone f) r)
    (a : A.Obj) (i q : ℤ) (e : i+(r+1) = q) :
    (P.complex a).X i ⟶ (M.complex a).X q := by
  obtain rfl : (i+r)+1 = q := by omega
  exact g.app a i (i+r) rfl ≫ ModuleCat.ofHom (LinearMap.snd _ _ _)

@[simp] private theorem coneHomSourceApp_apply (f : M ⟶ N) {r : ℤ} (g : GradedHom P (cone f) r)
    (a : A.Obj) (i q : ℤ) (e : i+(r+1) = q+1) (x : (P.complex a).X i) :
    coneHomSourceApp f g a i (q+1) e x = (g.app a i q (by omega) x).2 := by
  obtain rfl : i+r = q := by omega
  rfl

private def coneHomSource (f : M ⟶ N) (r : ℤ) :
    GradedHom P (cone f) r →ₗ[k] GradedHom P M (r+1) where
  toFun g := GradedHom.mk (coneHomSourceApp f g) (by
    intro a b i j n ir nr h hi hn x z
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, p+1 = ir := ⟨ir-1, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q : ℤ, q+1 = nr := ⟨nr-1, by omega⟩
    simp only [coneHomSourceApp_apply]
    exact congrArg Prod.snd (g.comm_act i j n p q h (by omega) (by omega) x z))
  map_add' g h := by
    apply gradedHom_ext_apply
    intro a i q e x
    obtain ⟨j, rfl⟩ : ∃ j : ℤ, j+1 = q := ⟨q-1, by omega⟩
    change coneHomSourceApp f (g+h) a i (j+1) e x =
      coneHomSourceApp f g a i (j+1) e x + coneHomSourceApp f h a i (j+1) e x
    simp only [coneHomSourceApp_apply]
    rfl
  map_smul' c g := by
    apply gradedHom_ext_apply
    intro a i q e x
    obtain ⟨j, rfl⟩ : ∃ j : ℤ, j+1 = q := ⟨q-1, by omega⟩
    change coneHomSourceApp f (c • g) a i (j+1) e x = c • coneHomSourceApp f g a i (j+1) e x
    simp only [coneHomSourceApp_apply]
    rfl

@[simp] private theorem coneHomSource_app (f : M ⟶ N) {r : ℤ} (g : GradedHom P (cone f) r)
    (a : A.Obj) (i q : ℤ) (e : i+r = q) (x : (P.complex a).X i) :
    (coneHomSource f r g).app a i (q+1) (by omega) x = (g.app a i q e x).2 :=
  coneHomSourceApp_apply f g a i q (by omega) x

private def coneHomPair (f : M ⟶ N) {r : ℤ} (b : GradedHom P N r) (a : GradedHom P M (r+1)) :
    GradedHom P (cone f) r :=
  GradedHom.mk (fun o i q e => ModuleCat.ofHom
    ((b.app o i q e).hom.prod (a.app o i (q+1) (by omega)).hom)) (by
      intro o p i j n ir nr h hi hn x z
      exact Prod.ext (b.comm_act i j n ir nr h hi hn x z)
        (a.comm_act i j n (ir+1) (nr+1) h (by omega) (by omega) x z))

private theorem coneHomSource_pair (f : M ⟶ N) {r : ℤ}
    (b : GradedHom P N r) (a : GradedHom P M (r+1)) :
    coneHomSource f r (coneHomPair f b a) = a := by
  apply gradedHom_ext_apply
  intro o i q e x
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, j+1 = q := ⟨q-1, by omega⟩
  rw [coneHomSource_app f _ o i j (by omega)]
  rfl

private theorem coneHomTarget_pair (f : M ⟶ N) {r : ℤ}
    (b : GradedHom P N r) (a : GradedHom P M (r+1)) :
    coneHomTarget f r (coneHomPair f b a) = b := by
  apply gradedHom_ext_apply
  intro o i q e x
  rw [coneHomTarget_app]
  rfl

private theorem coneHom_ext (f : M ⟶ N) {r : ℤ} {g h : GradedHom P (cone f) r}
    (ht : coneHomTarget f r g = coneHomTarget f r h)
    (hs : coneHomSource f r g = coneHomSource f r h) : g = h := by
  apply gradedHom_ext_apply
  intro a i q e x
  apply Prod.ext
  · simpa only [coneHomTarget_app] using congrArg (fun b : GradedHom P N r => b.app a i q e x) ht
  · simpa only [coneHomSource_app f _ a i q e] using
      congrArg (fun b : GradedHom P M (r+1) => b.app a i (q+1) (by omega) x) hs

private theorem differential_app {r : ℤ} (g : GradedHom M N r)
    (a : A.Obj) (i q : ℤ) (e : i+r = q) (x : (M.complex a).X i) :
    GradedHom.app ((homComplex M N).d r (r+1) g) a i (q+1) (by omega) x =
      (N.complex a).d q (q+1) (g.app a i q e x) -
        r.negOnePow • g.app a (i+1) (q+1) (by omega) ((M.complex a).d i (i+1) x) := by
  subst q
  exact differentialFormula r g a i (i+r+1) (by omega) x

private theorem coneHomTarget_d (f : M ⟶ N) {r : ℤ} (g : GradedHom P (cone f) r) :
    coneHomTarget f (r+1) ((homComplex P (cone f)).d r (r+1) g) =
      (homComplex P N).d r (r+1) (coneHomTarget f r g) +
        (homComplexMap P f).f (r+1) (coneHomSource f r g) := by
  apply gradedHom_ext_apply
  intro a i q e x
  obtain rfl : (i+r)+1 = q := by omega
  rw [coneHomTarget_app, differential_app _ _ _ _ rfl, cone_d,
    gradedHom_add_app, differential_app _ _ _ _ rfl, homComplexMap_app,
    coneHomTarget_app, coneHomTarget_app, coneHomSource_app] <;> try omega
  change _ + _ - r.negOnePow • (g.app a (i+1) (i+r+1) (by omega)
    ((P.complex a).d i (i+1) x)).1 = _
  abel

private theorem coneHomSource_d (f : M ⟶ N) {r : ℤ} (g : GradedHom P (cone f) r) :
    coneHomSource f (r+1) ((homComplex P (cone f)).d r (r+1) g) =
      -(homComplex P M).d (r+1) (r+1+1) (coneHomSource f r g) := by
  apply gradedHom_ext_apply
  intro a i q e x
  obtain rfl : ((i+r)+1)+1 = q := by omega
  rw [coneHomSource_app, differential_app _ _ _ _ rfl, cone_d,
    gradedHom_neg_app, differential_app _ _ _ _ (by omega : i + (r+1) = i+r+1),
    coneHomSource_app, coneHomSource_app, Int.negOnePow_succ, Units.neg_smul] <;> try omega
  change -_ - r.negOnePow • (g.app a (i+1) (i+r+1) (by omega)
    ((P.complex a).d i (i+1) x)).2 = _
  abel

open CochainComplex.mappingCone in
private noncomputable def coneComparisonComponent (f : M ⟶ N) (r : ℤ) :
    (homComplex P (cone f)).X r ⟶ (mappingCone (homComplexMap P f)).X r :=
  ModuleCat.ofHom (coneHomSource f r) ≫ (inl (homComplexMap P f)).v (r+1) r (by omega) +
    ModuleCat.ofHom (coneHomTarget f r) ≫ (inr (homComplexMap P f)).f r

open CochainComplex.mappingCone in
private theorem coneComparisonComponent_fst (f : M ⟶ N) (r : ℤ) :
    coneComparisonComponent (P := P) f r ≫ (fst (homComplexMap P f)).1.v r (r+1) rfl =
      ModuleCat.ofHom (coneHomSource f r) := by
  simp [coneComparisonComponent, Preadditive.add_comp, Category.assoc]

open CochainComplex.mappingCone in
private theorem coneComparisonComponent_snd (f : M ⟶ N) (r : ℤ) :
    coneComparisonComponent (P := P) f r ≫ (snd (homComplexMap P f)).v r r (add_zero r) =
      ModuleCat.ofHom (coneHomTarget f r) := by
  simp [coneComparisonComponent, Preadditive.add_comp, Category.assoc]

open CochainComplex.mappingCone in
private noncomputable def coneComparison (P : RightDGModule A) (f : M ⟶ N) :
    homComplex P (cone f) ⟶ mappingCone (homComplexMap P f) :=
  CochainComplex.ofHom (coneComparisonComponent f) (by
    intro r
    let φ := homComplexMap P f
    apply ext_to φ (r+1) (r+1+1) rfl
    · rw [Category.assoc, d_fst_v φ r (r+1) (r+1+1) rfl rfl, Preadditive.comp_neg,
        ← Category.assoc, coneComparisonComponent_fst,
        Category.assoc, coneComparisonComponent_fst]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro g
      exact (coneHomSource_d f g).symm
    · rw [Category.assoc, d_snd_v φ r (r+1) rfl, Preadditive.comp_add, ← Category.assoc,
        coneComparisonComponent_fst, ← Category.assoc, coneComparisonComponent_snd,
        Category.assoc, coneComparisonComponent_snd]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro g
      exact (add_comm _ _).trans (coneHomTarget_d f g).symm)

open CochainComplex.mappingCone in
private theorem coneComparison_isIso (P : RightDGModule A) (f : M ⟶ N) :
    IsIso (coneComparison P f) := by
  have h (r : ℤ) : IsIso ((coneComparison P f).f r) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · intro g h eq
      apply coneHom_ext f
      · have e := congrArg (fun z => (snd (homComplexMap P f)).v r r (add_zero r) z) eq
        change ((coneComparisonComponent f r) ≫ (snd (homComplexMap P f)).v r r (add_zero r)) g =
          ((coneComparisonComponent f r) ≫ (snd (homComplexMap P f)).v r r (add_zero r)) h at e
        rw [coneComparisonComponent_snd] at e
        exact e
      · have e := congrArg (fun z => (fst (homComplexMap P f)).1.v r (r+1) rfl z) eq
        change ((coneComparisonComponent f r) ≫ (fst (homComplexMap P f)).1.v r (r+1) rfl) g =
          ((coneComparisonComponent f r) ≫ (fst (homComplexMap P f)).1.v r (r+1) rfl) h at e
        rw [coneComparisonComponent_fst] at e
        exact e
    · intro z
      refine ⟨coneHomPair f ((snd (homComplexMap P f)).v r r (add_zero r) z) ((fst (homComplexMap P f)).1.v r (r+1) rfl z), ?_⟩
      change (inl (homComplexMap P f)).v (r+1) r (by omega) (coneHomSource f r (coneHomPair f _ _)) +
        (inr (homComplexMap P f)).f r (coneHomTarget f r (coneHomPair f _ _)) = z
      rw [coneHomSource_pair, coneHomTarget_pair]
      have eq := CategoryTheory.congr_fun (id_X (homComplexMap P f) r (r+1) rfl) z
      exact eq
  exact Hom.isIso_of_components _

private theorem mappingCone_quasiIso
    {X Y : ModuleCochain.{u,z} k} (φ : X ⟶ Y) (h : (mappingCone φ).Acyclic) :
    QuasiIso φ := by
  apply (HomologicalComplex.mem_quasiIso_iff _).1
  apply (HomotopyCategory.quotient_map_mem_quasiIso_iff φ).1
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ObjectProperty.trW.mk (HomotopyCategory.subcategoryAcyclic (ModuleCat.{z} k))
    (HomotopyCategory.mappingCone_triangleh_distinguished φ)
    ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 h)

/-- A K-projective source sends a quasi-isomorphism to a quasi-isomorphism on Hom. -/
theorem IsKProjective.homComplexMap_quasiIso {P M N : RightDGModule A}
    (f : M ⟶ N) (hP : P.IsKProjective)
    (hf : IsQuasiIso f) : QuasiIso (homComplexMap P f) := by
  have h := hP (RightDGModule.cone f) ((quasiIso_iff_cone_acyclic f).1 hf)
  have := coneComparison_isIso P f
  let e := asIso (coneComparison P f)
  apply mappingCone_quasiIso (homComplexMap P f)
  intro r
  exact (exactAt_iff_of_quasiIsoAt e.hom r).1 (h r)

open Specs.DerivedFormalization.DG.Basic (zeroShort cyclesZero h0Hom classOf)

private abbrev zeroShortMap {X Y : ModuleCochain.{u,z} k} (φ : X ⟶ Y) :
    zeroShort X ⟶ zeroShort Y :=
  (shortComplexFunctor' _ _ (-1) 0 1).map φ

private noncomputable def zeroCohomologyMap {X Y : ModuleCochain.{u,z} k} (φ : X ⟶ Y) :
    ModuleCat.of k (h0Hom X) ⟶ ModuleCat.of k (h0Hom Y) :=
  (zeroShort X).moduleCatHomologyIso.inv ≫ ShortComplex.homologyMap (zeroShortMap φ) ≫
    (zeroShort Y).moduleCatHomologyIso.hom

private theorem zeroCohomologyMap_classOf {X Y : ModuleCochain.{u,z} k} (φ : X ⟶ Y)
    (x : cyclesZero X) (y : cyclesZero Y) (h : φ.f 0 x.val = y.val) :
    zeroCohomologyMap φ (classOf x) = classOf y := by
  let x' := (zeroShort X).moduleCatCyclesIso.inv x
  let y' := (zeroShort Y).moduleCatCyclesIso.inv y
  have hc : ShortComplex.cyclesMap (zeroShortMap φ) x' = y' := by
    apply (ModuleCat.mono_iff_injective (zeroShort Y).iCycles).1 inferInstance
    have e := CategoryTheory.congr_fun (ShortComplex.cyclesMap_i (zeroShortMap φ)) x'
    change (zeroShort Y).iCycles (ShortComplex.cyclesMap (zeroShortMap φ) x') =
      φ.f 0 ((zeroShort X).iCycles x') at e
    rw [e]
    have hx := CategoryTheory.congr_fun (zeroShort X).moduleCatCyclesIso_inv_iCycles x
    have hy := CategoryTheory.congr_fun (zeroShort Y).moduleCatCyclesIso_inv_iCycles y
    change (zeroShort X).iCycles x' = x.val at hx
    change (zeroShort Y).iCycles y' = y.val at hy
    rw [hx, hy, h]
  have hx := CategoryTheory.congr_fun (zeroShort X).moduleCatCyclesIso_inv_π x
  change (zeroShort X).homologyπ x' = (zeroShort X).moduleCatHomologyIso.inv (classOf x) at hx
  have hy := CategoryTheory.congr_fun (zeroShort Y).π_moduleCatCyclesIso_hom y'
  change (zeroShort Y).moduleCatHomologyIso.hom ((zeroShort Y).homologyπ y') =
    classOf ((zeroShort Y).moduleCatCyclesIso.hom y') at hy
  have hy' : (zeroShort Y).moduleCatCyclesIso.hom y' = y :=
    CategoryTheory.congr_fun (zeroShort Y).moduleCatCyclesIso.inv_hom_id y
  change (zeroShort Y).moduleCatHomologyIso.hom
    (ShortComplex.homologyMap (zeroShortMap φ) ((zeroShort X).moduleCatHomologyIso.inv (classOf x))) =
    classOf y
  have e := CategoryTheory.congr_fun (ShortComplex.homologyπ_naturality (zeroShortMap φ)) x'
  change ShortComplex.homologyMap (zeroShortMap φ) ((zeroShort X).homologyπ x') =
    (zeroShort Y).homologyπ (ShortComplex.cyclesMap (zeroShortMap φ) x') at e
  rw [← hx, e, hc, hy, hy']

private theorem zeroCohomologyMap_bijective {X Y : ModuleCochain.{u,z} k}
    (φ : X ⟶ Y) (h : QuasiIsoAt φ 0) : Function.Bijective (zeroCohomologyMap φ) := by
  rw [← ConcreteCategory.isIso_iff_bijective]
  have hs : ShortComplex.QuasiIso (zeroShortMap φ) :=
    (quasiIsoAt_iff' φ (-1) 0 1
      ((ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl))
      ((ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel 0 1 from rfl))).1 h
  exact IsIso.comp_isIso' (zeroShort X).moduleCatHomologyIso.isIso_inv
    (IsIso.comp_isIso' ((ShortComplex.quasiIso_iff (zeroShortMap φ)).1 hs)
      (zeroShort Y).moduleCatHomologyIso.isIso_hom)

private theorem homComplexMap_strictCycle (f : M ⟶ N) (g : P ⟶ M) :
    (homComplexMap P f).f 0 (strictCycle g).val = (strictCycle (g ≫ f)).val := by
  apply Subtype.ext
  exact funext fun a => (Cochain.ofHom_comp (g.app a) (f.app a)).symm

private theorem zeroCohomologyMap_homotopyClass (f : M ⟶ N) (g : P ⟶ M) :
    zeroCohomologyMap (homComplexMap P f) (homotopyClass g) = homotopyClass (g ≫ f) :=
  zeroCohomologyMap_classOf _ _ _ (homComplexMap_strictCycle f g)

/-- A quasi-isomorphism between K-projectives has a strict inverse up to
right-linear homotopies in both composite directions. -/
theorem IsKProjective.homotopyEquivalence_of_quasiIso (f : M ⟶ N)
    (hM : M.IsKProjective) (hN : N.IsKProjective) (hf : IsQuasiIso f) :
    ∃ g : N ⟶ M, ∃ h₁ : GradedHom M M (-1), ∃ h₂ : GradedHom N N (-1),
      HomotopyEquation (f ≫ g) (𝟙 M) h₁ ∧ HomotopyEquation (g ≫ f) (𝟙 N) h₂ := by
  have h₁ := zeroCohomologyMap_bijective (homComplexMap M f)
    ((hM.homComplexMap_quasiIso f hf).quasiIsoAt 0)
  have h₂ := zeroCohomologyMap_bijective (homComplexMap N f)
    ((hN.homComplexMap_quasiIso f hf).quasiIsoAt 0)
  obtain ⟨x, hx⟩ := h₂.surjective (homotopyClass (𝟙 N))
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  let g : N ⟶ M := strictMap c
  have hg : homotopyClass g = classOf c := by
    change classOf (strictCycle (strictMap c)) = _
    rw [strictCycle_strictMap]
  have hgf : homotopyClass (g ≫ f) = homotopyClass (𝟙 N) := by
    rw [← zeroCohomologyMap_homotopyClass, hg]
    exact hx
  have hfg : homotopyClass (f ≫ g) = homotopyClass (𝟙 M) := by
    apply h₁.injective
    rw [zeroCohomologyMap_homotopyClass, zeroCohomologyMap_homotopyClass,
      Category.assoc, Category.id_comp]
    let F := toHomotopyCategory A
    change F.map (f ≫ (g ≫ f)) = F.map f
    rw [F.map_comp]
    rw [show F.map (g ≫ f) = F.map (𝟙 N) from hgf, F.map_id, Category.comp_id]
  obtain ⟨h, hh⟩ := (homotopyCriterion _ _).1 hfg
  obtain ⟨j, hj⟩ := (homotopyCriterion _ _).1 hgf
  exact ⟨g, h, j, hh, hj⟩

end DerivedFormalization.RightDGModule
