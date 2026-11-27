import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoproducts
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CompactRepresentables
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped DirectSum

universe u v w t j o m

namespace DerivedFormalization.RightDGModule

open Specs.DerivedFormalization.DG.CompactRepresentables
open Specs.DerivedFormalization.DG.Derived (HomotopyCategoryLaws)
open Specs.DerivedFormalization.DG.Basic (zeroShort h0Hom)
open private representable_kProjective from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFreeKProjective
open private act_assoc_at from MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.ShiftCone
open private act_id_reindexed id_comp_reindexed from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFree

noncomputable section

set_option maxHeartbeats 1400000

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}

section Evaluation

variable (a : A.Obj) (n : ℤ) (N : RightDGModule A)

/-- The value of a homogeneous right-linear map on the shifted identity. -/
private def cellEval (r : ℤ) : GradedHom (freeCell a n) N r →ₗ[k] (N.complex a).X (n+r) where
  toFun f := f.app a n (n+r) rfl (cellGenerator a n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def cellExtend (r : ℤ) (x : (N.complex a).X (n+r)) :
    GradedHom (freeCell a n) N r :=
  GradedHom.mk (fun b i q h => ModuleCat.ofHom (N.act (n+r) (i + -n) q (by omega) x)) (by
    intro b c i j l ir lr h hi hl y z
    change N.act (n+r) (l + -n) lr _ x
        (A.comp (i + -n) j (l + -n) _ y z) =
      N.act ir j lr _ (N.act (n+r) (i + -n) ir _ x y) z
    exact (act_assoc_at N (n+r) (i + -n) j ir (l + -n) lr
      (by omega) (by omega) (by omega) x y z).symm)

private theorem cellEval_extend (r : ℤ) (x : (N.complex a).X (n+r)) :
    cellEval a n N r (cellExtend a n N r x) = x := by
  change N.act (n+r) (n + -n) (n+r) _
      x (((A.hom a a).XIsoOfEq (by omega : (0 : ℤ) = n + -n)).hom (A.id a)) = x
  exact act_id_reindexed N a (n+r) (n + -n) (by omega) x

private theorem cellEval_injective (r : ℤ) : Function.Injective (cellEval a n N r) := by
  intro f g hfg
  apply GradedHom.ext
  intro b i q h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let j := i + -n
  have e : n+j = i := by dsimp [j]; omega
  have hmul : (freeCell a n).act n j i e (cellGenerator a n) x = x := by
    change A.comp (n + -n) (i + -n) (i + -n) _ (cellGenerator a n) x = x
    change A.comp (n + -n) (i + -n) (i + -n) _
      (((A.hom a a).XIsoOfEq (by omega : (0 : ℤ) = n + -n)).hom (A.id a)) x = x
    exact id_comp_reindexed (n + -n) (i + -n) (i + -n) (by omega) rfl x
  have hf := f.comm_act n j i (n+r) q e rfl h (cellGenerator a n) x
  have hg := g.comm_act n j i (n+r) q e rfl h (cellGenerator a n) x
  rw [hmul] at hf hg
  change f.app b i q h x = g.app b i q h x
  rw [hf, hg]
  exact congrArg (fun z => N.act (n+r) j q (by omega) z x) hfg

private def cellEvalEquiv (r : ℤ) : GradedHom (freeCell a n) N r ≃ₗ[k] (N.complex a).X (n+r) :=
  LinearEquiv.ofBijective (cellEval a n N r)
    ⟨cellEval_injective a n N r, fun x => ⟨_, cellEval_extend a n N r x⟩⟩

private theorem cellEval_d (r : ℤ) (f : GradedHom (freeCell a n) N r) :
    cellEval a n N (r+1) ((homComplex (freeCell a n) N).d r (r+1) f) =
      (N.complex a).d (n+r) (n+(r+1)) (cellEval a n N r f) := by
  change GradedHom.app ((homComplex _ _).d r (r+1) f) a n (n+(r+1)) rfl _ = _
  rw [differentialFormula, cellGenerator_d, map_zero, smul_zero, sub_zero]
  rfl

section Adequate

variable {B : DGCategory.{u,max v w,w} k} (a : B.Obj) (n : ℤ) (N : RightDGModule B)

private def cellShortIso :
    zeroShort (homComplex (freeCell a n) N) ≅ (N.complex a).sc' (n + -1) n (n+1) :=
  ShortComplex.isoMk (LinearEquiv.toModuleIso (cellEvalEquiv a n N (-1)))
    (LinearEquiv.toModuleIso ((cellEvalEquiv a n N 0).trans
      (((N.complex a).XIsoOfEq (add_zero n)).toLinearEquiv)))
    (LinearEquiv.toModuleIso (cellEvalEquiv a n N 1))
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (N.complex a).d (n + -1) n (cellEval a n N (-1) x) =
        ((N.complex a).XIsoOfEq (add_zero n)).hom
          (cellEval a n N 0 ((homComplex _ _).d (-1) 0 x))
      have hd := cellEval_d a n N (-1) x
      change cellEval a n N 0 ((homComplex _ _).d (-1) 0 x) = _ at hd
      rw [hd, ← ModuleCat.comp_apply, d_comp_XIsoOfEq_hom])
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (N.complex a).d n (n+1)
        (((N.complex a).XIsoOfEq (add_zero n)).hom (cellEval a n N 0 x)) =
        cellEval a n N 1 ((homComplex _ _).d 0 1 x)
      have hd := cellEval_d a n N 0 x
      change cellEval a n N 1 ((homComplex _ _).d 0 1 x) = _ at hd
      rw [hd, ← ModuleCat.comp_apply, XIsoOfEq_hom_comp_d]
      rfl)

private def cellCohomologyIso :
    ModuleCat.of k (h0Hom (homComplex (freeCell a n) N)) ≅ (N.complex a).homology n :=
  (zeroShort _).moduleCatHomologyIso.symm ≪≫
    (ShortComplex.homologyFunctor (ModuleCat k)).mapIso (cellShortIso a n N) ≪≫
    ((N.complex a).homologyIsoSc' (n + -1) n (n+1)
      (ComplexShape.prev_eq' _ (show n + -1 + 1 = n by omega)) (ComplexShape.next_eq' _ rfl)).symm

private theorem cellCohomologyIso_class (f : freeCell a n ⟶ N) :
    ∃ x : (N.complex a).cycles n, (N.complex a).iCycles n x = (f.app a).f n (cellGenerator a n) ∧
      (cellCohomologyIso.{u,v,w} a n N).hom (homotopyClass f) = (N.complex a).homologyπ n x := by
  let H := zeroShort (homComplex (freeCell a n) N)
  let C := N.complex a
  let E := cellShortIso a n N
  let z : H.moduleCatLeftHomologyData.K := strictCycle f
  let hp := ComplexShape.prev_eq' (ComplexShape.up ℤ) (show n + -1 + 1 = n by omega)
  let hn := ComplexShape.next_eq' (ComplexShape.up ℤ) (show n + 1 = n + 1 from rfl)
  let eK := C.cyclesIsoSc' (n + -1) n (n+1) hp hn
  let eH := C.homologyIsoSc' (n + -1) n (n+1) hp hn
  let x := eK.inv (ShortComplex.cyclesMap E.hom (H.moduleCatCyclesIso.inv z))
  refine ⟨x, ?_, ?_⟩
  · have h : H.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap E.hom ≫ eK.inv ≫ C.iCycles n =
        H.moduleCatLeftHomologyData.i ≫ E.hom.τ₂ := by
      rw [C.cyclesIsoSc'_inv_iCycles, ShortComplex.cyclesMap_i,
        ← Category.assoc, H.moduleCatCyclesIso_inv_iCycles]
    have he := CategoryTheory.congr_fun h z
    change C.iCycles n x =
      ((C.XIsoOfEq (add_zero n)).hom (GradedHom.app (strictCycle f).val a n (n+0) rfl
        (cellGenerator a n))) at he
    rw [he]
    change ((CochainComplex.HomComplex.Cochain.ofHom (f.app a)).v n (n+0) rfl ≫
      (C.XIsoOfEq (add_zero n)).hom) (cellGenerator a n) = _
    rw [CochainComplex.HomComplex.Cochain.v_comp_XIsoOfEq_hom,
      CochainComplex.HomComplex.Cochain.ofHom_v]
  · have h : H.moduleCatLeftHomologyData.π ≫ H.moduleCatHomologyIso.inv ≫
        ShortComplex.homologyMap E.hom ≫ eH.inv =
        H.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap E.hom ≫ eK.inv ≫ C.homologyπ n := by
      rw [← Category.assoc H.moduleCatLeftHomologyData.π, ← H.moduleCatCyclesIso_inv_π,
        Category.assoc, ShortComplex.homologyπ_naturality_assoc, C.π_homologyIsoSc'_inv]
    exact CategoryTheory.congr_fun h z

private theorem cellKProjective : IsKProjective (freeCell a n) :=
  (representable_kProjective a).shift (-n)

variable (h : HomotopyCategoryLaws B)

private theorem cellQBijective :
    Function.Bijective ((Q B h).map :
      h0Hom (homComplex (freeCell a n) N) → ((Q B h).obj (freeCell a n) ⟶ (Q B h).obj N)) :=
  IsKProjective.Q_map_bijective h (N := N) (cellKProjective a n)

variable [S : Preadditive (D B h)]

private def cellLocalizationEquiv (hadd : LocalizationMapAdditive h S) :
    h0Hom (homComplex (freeCell a n) N) ≃+
      ((Q B h).obj (freeCell a n) ⟶ (Q B h).obj N) where
  toEquiv := Equiv.ofBijective _ (cellQBijective.{u,v,w} a n N h)
  map_add' f g := hadd (freeCell a n) N f g

private def cellDerivedEquiv (hadd : LocalizationMapAdditive h S) :
    ((Q B h).obj (freeCell a n) ⟶ (Q B h).obj N) ≃+ (N.complex a).homology n := by
  let l : h0Hom (homComplex (freeCell a n) N) ≃ₗ[k] (N.complex a).homology n :=
    (cellCohomologyIso.{u,v,w} a n N).toLinearEquiv
  exact (cellLocalizationEquiv.{u,v,w} a n N h hadd).symm.trans l.toAddEquiv

private theorem cellDerivedEquiv_class (hadd : LocalizationMapAdditive h S)
    (f : freeCell a n ⟶ N) :
    ∃ x : (N.complex a).cycles n, (N.complex a).iCycles n x = (f.app a).f n (cellGenerator a n) ∧
      cellDerivedEquiv.{u,v,w} a n N h hadd ((Q B h).map (homotopyClass f)) =
        (N.complex a).homologyπ n x := by
  obtain ⟨x, hx, he⟩ := cellCohomologyIso_class.{u,v,w} a n N f
  refine ⟨x, hx, ?_⟩
  change (cellCohomologyIso.{u,v,w} a n N).hom
    ((cellLocalizationEquiv.{u,v,w} a n N h hadd).symm
      ((cellLocalizationEquiv.{u,v,w} a n N h hadd) (homotopyClass f))) = _
  rw [AddEquiv.symm_apply_apply, he]

private theorem cellDerivedEquiv_natural (hadd : LocalizationMapAdditive h S)
    {T : RightDGModule B} (f : N ⟶ T)
    (g : (Q B h).obj (freeCell a n) ⟶ (Q B h).obj N) :
    cellDerivedEquiv.{u,v,w} a n T h hadd (g ≫ (Q B h).map (homotopyClass f)) =
      homologyMap (f.app a) n (cellDerivedEquiv.{u,v,w} a n N h hadd g) := by
  obtain ⟨z, rfl⟩ := (cellQBijective.{u,v,w} a n N h).surjective g
  obtain ⟨p, rfl⟩ := homotopyClass_surjective z
  have hpf : (Q B h).map (homotopyClass (p ≫ f)) =
      (Q B h).map (homotopyClass p) ≫ (Q B h).map (homotopyClass f) :=
    (toHomotopyCategory B ⋙ Q B h).map_comp p f
  rw [← hpf]
  obtain ⟨x, hx, he⟩ := cellDerivedEquiv_class.{u,v,w} a n N h hadd p
  obtain ⟨y, hy, hy'⟩ := cellDerivedEquiv_class.{u,v,w} a n T h hadd (p ≫ f)
  change cellDerivedEquiv.{u,v,w} a n T h hadd ((Q B h).map (homotopyClass (p ≫ f))) = _
  rw [hy', he]
  have hc : cyclesMap (f.app a) n x = y := by
    apply (ModuleCat.mono_iff_injective _).1 (inferInstance : Mono ((T.complex a).iCycles n))
    rw [← ModuleCat.comp_apply, cyclesMap_i, ModuleCat.comp_apply, hx, hy]
    rfl
  rw [← hc, ← ModuleCat.comp_apply, ← homologyπ_naturality]
  rfl

end Adequate

end Evaluation

open Specs.DerivedFormalization.DG.AmbientDerived (category strictInput)
open Specs.DerivedFormalization.DG.CoefficientLiftComparison (homologyIso evaluateHomology)

private def precomposeIso {C : Type o} [Category.{m} C] [Preadditive C]
    {P R N : C} (i : P ≅ R) : (P ⟶ N) ≃+ (R ⟶ N) where
  toEquiv := i.homFromEquiv
  map_add' := by
    intro f g
    change i.inv ≫ (f + g) = i.inv ≫ f + i.inv ≫ g
    exact Preadditive.comp_add _ _ _ _ _ _

local instance (B : DGCategory.{u,v,w} k) : Preadditive (K B) :=
  inferInstanceAs (Preadditive ((dgCategory B).H0))

/-- Derived maps from `h_a[-n]` are computed by evaluating on the shifted
identity. The coefficient lift identifies this cohomology with the original one. -/
theorem shiftedRepresentableHom : ShiftedRepresentableHom.{u,v,w,t} := by
  intro k _ A h
  let B := category.{u,v,w,t} A
  let L := strictInput.{u,v,w,t} A
  let S := derivedPreadditive.{u,max v t,w} B h
  let _ := S
  have hadd : LocalizationMapAdditive h S := by
    let _ : (Q B h).Additive := derivedLocalization_additive.{u,max v t,w} B h
    intro M N f g
    let f₀ : @Quiver.Hom (K B) (instCategoryK B).toCategoryStruct.toQuiver M N := f
    let g₀ : @Quiver.Hom (K B) (instCategoryK B).toCategoryStruct.toQuiver M N := g
    exact (Q B h).map_add (f := f₀) (g := g₀)
  refine ⟨S, hadd, ?_⟩
  intro a n
  have hr : L.obj (representable (A := A) a) = representable (A := B) a :=
    DG.CoefficientLift.representableComparison.{u,v,w,max w t} A a
  let s : L.obj (freeCell a n) ≅ freeCell (A := B) a n :=
    DG.CoefficientLift.shiftIso.{u,v,w,max w t} (representable a) (-n)
  let J := toHomotopyCategory B ⋙ Q B h
  let e := fun N => cellDerivedEquiv.{u,max v t,w} a n N h hadd
  let d (N : RightDGModule A) : ((L.obj N).complex a).homology n ≃ₗ[k]
      (N.complex a).homology n :=
    (homologyIso.{u,v,max w t} (N.complex a) n).toLinearEquiv.trans ULift.moduleEquiv
  let e₀ (N : RightDGModule A) :=
    (precomposeIso (N := J.obj (L.obj N)) (J.mapIso s)).trans
      ((e (L.obj N)).trans (d N).toAddEquiv)
  refine ⟨hr, s, e, e₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro b i x
    rfl
  · intro N f
    exact cellDerivedEquiv_class.{u,max v t,w} (B := B) a n N h hadd f
  · intro N T f g
    exact cellDerivedEquiv_natural.{u,max v t,w} (B := B) a n N h hadd f g
  · intro N g
    change d N (e (L.obj N) (J.map s.inv ≫ g)) = _
    simp only [d, evaluateHomology, RightDGModuleModel.id_app, homologyMap_id,
      Category.id_comp]
    rfl
  · intro N T f g
    let l : J.obj (freeCell a n) ⟶ J.obj (L.obj (freeCell a n)) := J.map s.inv
    let g₀ : J.obj (L.obj (freeCell a n)) ⟶ J.obj (L.obj N) := g
    let b : J.obj (L.obj N) ⟶ J.obj (L.obj T) := J.map (L.map f)
    let z := e (L.obj N) (l ≫ g₀)
    have hen := cellDerivedEquiv_natural.{u,max v t,w} (B := B) a n (L.obj N) h hadd
      (L.map f) (l ≫ g₀)
    have he := (DG.CoefficientLift.homologyComparison.{u,v,max w t} (k := k)).2 (f.app a) n
    change d T (e (L.obj T) (l ≫ g₀ ≫ b)) = homologyMap (f.app a) n (d N z)
    calc
      _ = d T (e (L.obj T) ((l ≫ g₀) ≫ b)) :=
        congrArg (fun p => d T (e (L.obj T) p)) (Category.assoc l g₀ b).symm
      _ = d T (homologyMap ((L.map f).app a) n z) := congrArg (d T) hen
      _ = _ := congrArg ULift.down (CategoryTheory.congr_fun he z)

section Coproducts

variable {C : Type o} [Category.{m} C] [Preadditive C] {I : Type j} {F : I → C}

private theorem coproductHomMap_of [DecidableEq I] (P : C) (c : Cofan F) (i : I) (f : P ⟶ F i) :
    coproductHomMap P c (DirectSum.of _ i f) = f ≫ c.inj i := by
  classical
  exact DirectSum.toAddMonoid_of _ _ _

private def cofanProjection {c : Cofan F} (hc : IsColimit c) (i : I) : c.pt ⟶ F i := by
  classical
  exact Cofan.IsColimit.desc hc (fun l => if e : l = i then eqToHom (congrArg F e) else 0)

private theorem inj_projection_same {c : Cofan F} (hc : IsColimit c) (i : I) :
    c.inj i ≫ cofanProjection hc i = 𝟙 (F i) := by
  classical
  simp [cofanProjection, Cofan.IsColimit.fac]

private theorem inj_projection_ne {c : Cofan F} (hc : IsColimit c) {i l : I} (e : l ≠ i) :
    c.inj l ≫ cofanProjection hc i = 0 := by
  classical
  simp [cofanProjection, Cofan.IsColimit.fac, e]

private theorem coproductHomMap_injective (P : C) {c : Cofan F} (hc : IsColimit c) :
    Function.Injective (coproductHomMap P c) := by
  classical
  intro x y h
  apply DFinsupp.ext
  intro i
  let ev : (⨁ l, P ⟶ F l) →+ (P ⟶ F i) :=
    { toFun := fun x => x i, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have he : (Preadditive.rightComp P (cofanProjection hc i)).comp (coproductHomMap P c) = ev := by
    apply DirectSum.addHom_ext
    intro l f
    change coproductHomMap P c (DirectSum.of _ l f) ≫ cofanProjection hc i =
      (DirectSum.of (fun l => P ⟶ F l) l f) i
    rw [coproductHomMap_of, Category.assoc]
    by_cases hli : l = i
    · subst l
      rw [inj_projection_same, Category.comp_id, DirectSum.of_eq_same]
    · rw [inj_projection_ne hc hli, comp_zero, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hli)]
  exact (DFunLike.congr_fun he x).symm.trans
    ((congrArg (fun z => z ≫ cofanProjection hc i) h).trans (DFunLike.congr_fun he y))

private theorem nonzeroSummandsSmall [LocallySmall.{v} C] {c : Cofan F} (hc : IsColimit c) :
    Small.{v} {i : I // ¬ IsZero (F i)} := by
  let e (i : {i : I // ¬ IsZero (F i)}) : c.pt ⟶ c.pt :=
    cofanProjection hc i.val ≫ c.inj i.val
  apply small_of_injective (f := e)
  intro i l h
  apply Subtype.ext
  by_contra hn
  have h' := congrArg (fun f => c.inj i.val ≫ f ≫ cofanProjection hc i.val) h
  change c.inj i.val ≫ (cofanProjection hc i.val ≫ c.inj i.val) ≫ cofanProjection hc i.val =
    c.inj i.val ≫ (cofanProjection hc l.val ≫ c.inj l.val) ≫ cofanProjection hc i.val at h'
  simp only [← Category.assoc] at h'
  rw [inj_projection_same, inj_projection_ne hc hn, Category.id_comp,
    zero_comp, zero_comp, inj_projection_same] at h'
  exact i.property ((IsZero.iff_id_eq_zero _).mpr h')

private theorem coproductHomMap_surjective_of_cover (P : C) {c : Cofan F} (hc : IsColimit c)
    {J : Type*} {G : J → C} {d : Cofan G} (hd : IsColimit d) (f : J → I)
    (E : ∀ j, G j ≅ F (f j)) (cover : ∀ i, ¬ IsZero (F i) → ∃ j, f j = i)
    (hsurj : Function.Surjective (coproductHomMap P d)) :
    Function.Surjective (coproductHomMap P c) := by
  classical
  let s := Cofan.IsColimit.desc hd (fun j => (E j).hom ≫ c.inj (f j))
  have hs (j : J) : d.inj j ≫ s = (E j).hom ≫ c.inj (f j) := Cofan.IsColimit.fac hd _ j
  have hf (i : I) : ∃ z : F i ⟶ d.pt, z ≫ s = c.inj i := by
    by_cases hi : IsZero (F i)
    · exact ⟨0, by rw [zero_comp]; exact hi.eq_of_src _ _⟩
    · obtain ⟨j, rfl⟩ := cover i hi
      exact ⟨(E j).inv ≫ d.inj j, by rw [Category.assoc, hs, Iso.inv_hom_id_assoc]⟩
  choose z hz using hf
  let r := Cofan.IsColimit.desc hc z
  have hr : r ≫ s = 𝟙 c.pt := by
    apply Cofan.IsColimit.hom_ext hc
    intro i
    rw [← Category.assoc, Cofan.IsColimit.fac hc z, hz, Category.comp_id]
  let dsum : (⨁ j, P ⟶ G j) →+ (⨁ i, P ⟶ F i) :=
    DirectSum.toAddMonoid (fun j => (DirectSum.of (fun i => P ⟶ F i) (f j)).comp
      (Preadditive.rightComp P (E j).hom))
  have he : (coproductHomMap P c).comp dsum =
      (Preadditive.rightComp P s).comp (coproductHomMap P d) := by
    apply DirectSum.addHom_ext
    intro j x
    change coproductHomMap P c (dsum (DirectSum.of _ j x)) =
      coproductHomMap P d (DirectSum.of _ j x) ≫ s
    rw [show dsum (DirectSum.of _ j x) = DirectSum.of (fun i => P ⟶ F i) (f j) (x ≫ (E j).hom) from
      DirectSum.toAddMonoid_of _ _ _, coproductHomMap_of, coproductHomMap_of, Category.assoc,
      Category.assoc, hs]
  intro g
  obtain ⟨x, hx⟩ := hsurj (g ≫ r)
  refine ⟨dsum x, ?_⟩
  change ((coproductHomMap P c).comp dsum) x = g
  rw [he]
  change coproductHomMap P d x ≫ s = g
  rw [hx, Category.assoc, hr, Category.comp_id]

end Coproducts

open Specs.DerivedFormalization.DG.IndexedSemiFree (StrictSum summand)
open Specs.DerivedFormalization.DG.DerivedCoproducts (derivedCofan)

private theorem exists_cycle (C : ModuleCochain.{u,v} k) (x : C.X 0)
    (hx : C.d 0 1 x = 0) : ∃ y : C.cycles 0, C.iCycles 0 y = x := by
  let z : (C.sc 0).moduleCatLeftHomologyData.K := ⟨x, by
    change C.d 0 ((ComplexShape.up ℤ).next 0) x = 0
    rw [(ComplexShape.up ℤ).next_eq' (show (0 : ℤ) + 1 = 1 from rfl)]
    exact hx⟩
  exact ⟨(C.sc 0).moduleCatCyclesIso.inv z,
    CategoryTheory.congr_fun (C.sc 0).moduleCatCyclesIso_inv_iCycles z⟩

section RealizedSum

variable {B : DGCategory.{u,max v w,w} k} (h : HomotopyCategoryLaws B)
variable [S : Preadditive (D B h)]
variable {I : Type j} {F : I → RightDGModule B} {U : RightDGModule B}

/-- The coordinates of a cycle have finite support, and each is a cycle.
Its cohomology class is the corresponding finite sum of classes. -/
private theorem realizedSum_surjective (hadd : LocalizationMapAdditive h S) (a : B.Obj) (b : StrictSum F U) :
    Function.Surjective (@coproductHomMap (D B h) inferInstance S _ _
      ((Q B h).obj (freeCell a 0)) (derivedCofan h b)) := by
  classical
  let e (N : RightDGModule B) := cellDerivedEquiv.{u,v,w} (B := B) a 0 N h hadd
  let c : Cofan (fun i => (Q B h).obj (F i)) := derivedCofan h b
  change Function.Surjective (coproductHomMap ((Q B h).obj (freeCell a 0)) c)
  intro g
  obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective ((U.complex a).homologyπ 0)).1
    inferInstance (e U g)
  let xi := b.coordinates a 0 ((U.complex a).iCycles 0 x)
  have hi (i : I) : ((F i).complex a).d 0 1 (xi i) = 0 := by
    change ((F i).complex a).d 0 (0+1) _ = 0
    have hz := CategoryTheory.congr_fun ((U.complex a).iCycles_d 0 (0+1)) x
    change (U.complex a).d 0 (0+1) ((U.complex a).iCycles 0 x) = 0 at hz
    rw [← b.coordinate_d a 0, hz, map_zero]
    rfl
  choose z hz using fun i => exists_cycle ((F i).complex a) (xi i) (hi i)
  let zz (i : I) := cyclesMap ((b.inclusion i).app a) 0 (z i)
  have hsum : (∑ i ∈ xi.support, zz i) = x := by
    apply (ModuleCat.mono_iff_injective _).1 (inferInstance : Mono ((U.complex a).iCycles 0))
    apply (b.coordinates a 0).injective
    change b.coordinates a 0 (((U.complex a).iCycles 0).hom (∑ i ∈ xi.support, zz i)) = xi
    rw [map_sum, map_sum]
    apply DFinsupp.ext
    intro j
    rw [DFinsupp.finsetSum_apply]
    have H (i : I) : b.coordinates a 0 ((U.complex a).iCycles 0 (zz i)) =
        summand F a 0 i (xi i) := by
      dsimp [zz]
      rw [← ModuleCat.comp_apply, cyclesMap_i, ModuleCat.comp_apply, hz, b.coordinate_inclusion]
    simp only [H]
    rw [Finset.sum_eq_single j]
    · exact DFinsupp.single_eq_same
    · intro i _ hij
      exact DFinsupp.single_eq_of_ne (Ne.symm hij)
    · intro hj
      simp only [DFinsupp.notMem_support_iff.mp hj, map_zero, DFinsupp.zero_apply]
  let P := (Q B h).obj (freeCell a 0)
  let m : (⨁ i, P ⟶ (Q B h).obj (F i)) →+ (P ⟶ (Q B h).obj U) := coproductHomMap P c
  let q (i : I) := (e (F i)).symm (((F i).complex a).homologyπ 0 (z i))
  let v (i : I) := DirectSum.of (fun i => P ⟶ (Q B h).obj (F i)) i (q i)
  have H (i : I) : e U (m (v i)) = (U.complex a).homologyπ 0 (zz i) := by
    have hmap : m (v i) = q i ≫ (Q B h).map (homotopyClass (b.inclusion i)) :=
      coproductHomMap_of P c i (q i)
    have hen := cellDerivedEquiv_natural.{u,v,w} (B := B) a 0 (F i) h hadd (b.inclusion i) (q i)
    calc
      _ = homologyMap ((b.inclusion i).app a) 0 (e (F i) (q i)) :=
        (congrArg (e U) hmap).trans hen
      _ = homologyMap ((b.inclusion i).app a) 0 (((F i).complex a).homologyπ 0 (z i)) :=
        congrArg _ ((e (F i)).apply_symm_apply _)
      _ = _ := CategoryTheory.congr_fun (homologyπ_naturality ((b.inclusion i).app a) 0) (z i)
  refine ⟨∑ i ∈ xi.support, v i, (e U).injective ?_⟩
  let W := (e U).toAddMonoidHom.comp m
  change W (∑ i ∈ xi.support, v i) = e U g
  calc
    _ = ∑ i ∈ xi.support, W (v i) := map_sum W _ _
    _ = ∑ i ∈ xi.support, ((U.complex a).homologyπ 0).hom (zz i) :=
      Finset.sum_congr rfl (fun i _ => H i)
    _ = ((U.complex a).homologyπ 0).hom (∑ i ∈ xi.support, zz i) :=
      (map_sum ((U.complex a).homologyπ 0).hom _ _).symm
    _ = _ := (congrArg ((U.complex a).homologyπ 0).hom hsum).trans hx

end RealizedSum

private def shiftZeroIso (M : RightDGModule A) : shift M 0 ≅ M := by
  let e (a : A.Obj) := (CategoryTheory.shiftFunctorZero (ModuleCochain.{u,v} k) ℤ).app
    (M.complex a)
  refine DG.CoefficientLift.isoOfComponents
    (fun a i => (asIso ((e a).hom.f i)).toLinearEquiv) ?_ ?_
  · intro a i x
    exact (CategoryTheory.congr_fun ((e a).hom.comm i (i+1)) x).symm
  · intro a b i j n h x z
    change (e a).hom.f n ((shift M 0).act i j n h x z) =
      M.act i j n h ((e b).hom.f i x) z
    let e' := (CategoryTheory.shiftFunctorZero (CochainComplex (ModuleCat.{v} k) ℤ) ℤ).hom
    change (e'.app (M.complex a)).f n ((shift M 0).act i j n h x z) =
      M.act i j n h ((e'.app (M.complex b)).f i x) z
    dsimp only [e']
    rw [CochainComplex.shiftFunctorZero_hom_app_f, CochainComplex.shiftFunctorZero_hom_app_f]
    have aux (p q : ℤ) (hp : p = i) (hq : q = n) (y : (M.complex b).X p) :
        ((M.complex a).XIsoOfEq hq).hom (M.act p j q (by omega) y z) =
          M.act i j n h (((M.complex b).XIsoOfEq hp).hom y) z := by
      subst p q
      simp
    exact aux (i+0) (n+0) (add_zero _) (add_zero _) x

private theorem coproductHomMap_surjective_of_iso {C : Type o} [Category.{m} C] [Preadditive C]
    {I : Type j} {F : I → C} (c : Cofan F) {P R : C} (s : P ≅ R)
    (hsurj : Function.Surjective (coproductHomMap P c)) :
    Function.Surjective (coproductHomMap R c) := by
  classical
  let d := DirectSum.map (fun i => (precomposeIso (N := F i) s).toAddMonoidHom)
  have he : (coproductHomMap R c).comp d =
      (precomposeIso (N := c.pt) s).toAddMonoidHom.comp (coproductHomMap P c) := by
    apply DirectSum.addHom_ext
    intro i x
    change coproductHomMap R c (d (DirectSum.of _ i x)) =
      s.inv ≫ coproductHomMap P c (DirectSum.of _ i x)
    rw [show d (DirectSum.of (fun i => P ⟶ F i) i x) =
      DirectSum.of (fun i => R ⟶ F i) i (s.inv ≫ x) from
      DirectSum.map_of _ _ _, coproductHomMap_of, coproductHomMap_of]
    exact Category.assoc _ _ _
  intro g
  obtain ⟨x, hx⟩ := hsurj ((precomposeIso s).symm g)
  refine ⟨d x, ?_⟩
  change ((coproductHomMap R c).comp d) x = _
  rw [he]
  change precomposeIso s (coproductHomMap P c x) = _
  rw [hx, AddEquiv.apply_symm_apply]

/-- Representables are compact at each adequate coefficient level. An existing
coproduct has only a small set of nonzero summands, since its projections and
inclusions distinguish those summands by endomorphisms of the coproduct. -/
theorem representableCompact : RepresentableCompact.{u,v,w,t,j} := by
  intro k _ A h
  dsimp only
  intro S hadd a I F c hc
  let B := category.{u,v,w,t} A
  let q := Q B h
  let _ : Preadditive (D B h) := S
  let Jq := toHomotopyCategory B ⋙ q
  let s : Jq.obj (freeCell a 0) ≅ Jq.obj (representable (A := B) a) :=
    Jq.mapIso (shiftZeroIso (representable (A := B) a))
  let F₀ : I → D B h := F
  let c' : @Cofan I (D B h) inferInstance F₀ := c
  have hc' : IsColimit c' := hc
  change Function.Bijective (coproductHomMap (C := D B h) (q.obj (representable (A := B) a)) c')
  refine ⟨coproductHomMap_injective _ hc', coproductHomMap_surjective_of_iso c' s ?_⟩
  let E := kProjectiveLocalizationEquivalence.{u,max v t,w} B h
  let _ : LocallySmall.{max v w t} (D B h) := locallySmall_of_faithful E.inverse
  let L := {i : I // ¬ IsZero (F₀ i)}
  let _ : Small.{max v w t} L := nonzeroSummandsSmall (C := D B h) hc'
  let J := Shrink.{max v w t} L
  let e : J ≃ L := (equivShrink L).symm
  let f (i : J) : I := (e i).val
  have cover (i : I) (hi : ¬ IsZero (F₀ i)) : ∃ l : J, f l = i :=
    ⟨e.symm ⟨i, hi⟩, congrArg Subtype.val (e.apply_symm_apply ⟨i, hi⟩)⟩
  have := Localization.essSurj q (quasiIsomorphisms B)
  let M (i : J) : RightDGModule B := q.objPreimage (F₀ (f i))
  let E₀ (i : J) : q.obj (M i) ≅ F₀ (f i) := q.objObjPreimageIso (F₀ (f i))
  let b := DG.IndexedSums.nativeSum M
  obtain ⟨hd⟩ := nativeExistingDerivedCoproduct.{u,max v t,w,max v w t} h b
  let d : @Cofan J (D B h) inferInstance (fun i => q.obj (M i)) := derivedCofan h b
  have hd' : IsColimit d := hd
  exact coproductHomMap_surjective_of_cover _ hc' hd' f E₀ cover
    (realizedSum_surjective.{u,max v t,w,max v w t} (B := B) h hadd a b)

end

end DerivedFormalization.RightDGModule
