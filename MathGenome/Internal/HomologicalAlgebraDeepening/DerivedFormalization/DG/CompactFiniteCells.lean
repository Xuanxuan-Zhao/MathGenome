import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CompactFiniteCells
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.FiniteCellApproximation
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactTelescope
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactRepresentables
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CellLift
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoefficientLift
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u v w j m o t s

namespace DerivedFormalization.RightDGModule

open Specs.DerivedFormalization.DG
open CompactFiniteCells
open CompactRepresentables (IsCompact coproductHomMap LocalizationMapAdditive)
open FiniteCellApproximation
open IndexedSemiFree (Presentation StrictSum summand)
open DerivedKProjective (derivedCategoryInstance)
open private coproductHomMap_of coproductHomMap_injective nonzeroSummandsSmall
  coproductHomMap_surjective_of_cover from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactRepresentables

noncomputable section

set_option linter.style.haveILetI false

private theorem compact_of_retract {C : Type o} [Category.{m} C] [Preadditive C]
    {X Y : C} (r : Retract X Y) (hY : IsCompact.{j,_,_} Y) : IsCompact.{j,_,_} X := by
  classical
  intro I F c hc
  refine ⟨coproductHomMap_injective X hc, ?_⟩
  let l : (⨁ i, Y ⟶ F i) →+ (⨁ i, X ⟶ F i) :=
    DirectSum.map fun i => Preadditive.leftComp (F i) r.i
  have hl : (coproductHomMap X c).comp l =
      (Preadditive.leftComp c.pt r.i).comp (coproductHomMap Y c) := by
    apply DirectSum.addHom_ext
    intro i f
    change coproductHomMap X c (l (DirectSum.of _ i f)) =
      r.i ≫ coproductHomMap Y c (DirectSum.of _ i f)
    rw [show l (DirectSum.of _ i f) = DirectSum.of (fun i => X ⟶ F i) i (r.i ≫ f) from
      DirectSum.map_of _ _ _, coproductHomMap_of, coproductHomMap_of, Category.assoc]
  intro f
  obtain ⟨g, hg⟩ := (hY c hc).surjective (r.r ≫ f)
  refine ⟨l g, ?_⟩
  change ((coproductHomMap X c).comp l) g = f
  rw [hl]
  change r.i ≫ coproductHomMap Y c g = f
  rw [hg, r.retract_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem compact_preservesCoproducts {C : Type o} [Category.{max j m} C] [Preadditive C]
    {X : C} (hX : IsCompact.{j,_,_} X) : CompactTelescope.Compact.{j,_,_} X := by
  classical
  intro I
  let H := CompactTelescope.homGroup X
  have (F : I → C) : PreservesColimit (Discrete.functor F) H := by
    constructor
    intro c hc
    apply Nonempty.intro
    let e := AddEquiv.ofBijective (coproductHomMap X c) (hX c hc)
    let q : Cofan (fun i => H.obj (F i)) := Cofan.mk (H.obj c.pt) (fun i => H.map (Cofan.inj c i))
    have eq (i : I) (x : X ⟶ F i) :
        e (DirectSum.of (fun i => X ⟶ F i) i x) = x ≫ Cofan.inj c i :=
      coproductHomMap_of X c i x
    let desc (d : Cofan (fun i => H.obj (F i))) :=
      DirectSum.toAddMonoid (fun i => (d.inj i).hom)
    have hq : IsColimit q := by
      refine Cofan.IsColimit.mk q (fun d => AddCommGrpCat.ofHom ((desc d).comp e.symm.toAddMonoidHom)) ?_ ?_
      · intro d i
        apply AddCommGrpCat.ext
        intro x
        change desc d (e.symm (x ≫ Cofan.inj c i)) = (d.inj i) x
        rw [← eq i x, AddEquiv.symm_apply_apply]
        exact DirectSum.toAddMonoid_of _ _ _
      · intro d g hg
        have hcomp : g.hom.comp e.toAddMonoidHom = desc d := by
          apply DirectSum.addHom_ext
          intro i x
          change g (e (DirectSum.of (fun i => X ⟶ F i) i x)) = _
          calc
            g (e (DirectSum.of (fun i => X ⟶ F i) i x)) = g (x ≫ Cofan.inj c i) :=
              congrArg (fun z : X ⟶ c.pt => g z) (eq i x)
            _ = (d.inj i) x := CategoryTheory.congr_fun (hg i) x
            _ = _ := (DirectSum.toAddMonoid_of (fun l => (d.inj l).hom) i x).symm
        apply AddCommGrpCat.ext
        intro x
        change g x = desc d (e.symm x)
        exact (congrArg g (e.apply_symm_apply x).symm).trans
          (DFunLike.congr_fun hcomp (e.symm x))
    let eqC : Cofan.mk c.pt (Cofan.inj c) ≅ c := Cofan.ext (Iso.refl _) (by simp)
    exact IsColimit.ofIsoColimit ((isColimitMapCoconeCofanMkEquiv H F _).symm hq)
      (Functor.mapIso (Cocone.functoriality _ H) eqC)
  exact preservesColimitsOfShape_of_discrete H

set_option backward.isDefEq.respectTransparency false in
private theorem exists_addGroup_colimit_representative {J : Type j} [Category.{m} J]
    [IsFiltered J] {D : J ⥤ AddCommGrpCat.{o}} {c : Cocone D}
    [PreservesColimit D (forget AddCommGrpCat.{o})] (hc : IsColimit c) (x : c.pt) :
    ∃ (i : J) (y : D.obj i), c.ι.app i y = x := by
  let G := forget (AddCommGrpCat.{o})
  let hx : (G.mapCocone c).pt := x
  obtain ⟨i, y, hy⟩ := Types.jointly_surjective_of_isColimit (isColimitOfPreserves G hc) hx
  refine ⟨i, y, ?_⟩
  change c.ι.app i y = x at hy
  exact hy

section StrictMaps

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}
variable {P N : RightDGModule A} (F : Presentation.{u,v,w,j} P)

private def namedGenerator (l : ℕ) (i : F.index l) :
    (P.complex ((F.family l).object i)).X ((F.family l).degree i) :=
  ((F.into (l + 1)).app _).f _ ((F.extension l).generator i)

set_option backward.isDefEq.respectTransparency false in
private theorem hom_ext_on_generators {f g : P ⟶ N}
    (h : ∀ l (i : F.index l), (f.app _).f _ (namedGenerator F l i) =
      (g.app _).f _ (namedGenerator F l i)) : f = g := by
  classical
  letI : DecidableEq (Σ l : ℕ, F.index l) := Classical.decEq _
  obtain ⟨D, _⟩ := DG.CellReindex.directSumDecomposition F
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  let e := D.coordinates a n
  have he : ((f.app a).f n).hom.comp e.symm.toLinearMap =
      ((g.app a).f n).hom.comp e.symm.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro ⟨l, i⟩
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    change (f.app a).f n (e.symm (summand _ a n ⟨l, i⟩ x)) =
      (g.app a).f n (e.symm (summand _ a n ⟨l, i⟩ x))
    rw [← D.cell ⟨l, i⟩ a n x]
    change (f.app a).f n (e.symm (e (CellReindex.cellToModule F ⟨l, i⟩ a n x))) =
      (g.app a).f n (e.symm (e (CellReindex.cellToModule F ⟨l, i⟩ a n x)))
    simp only [LinearEquiv.symm_apply_apply]
    let b := (F.family l).object i
    let d := (F.family l).degree i
    let m := n + -d
    have hdeg : d + m = n := by dsimp [m]; omega
    change (A.hom a b).X m at x
    have hx : ((A.hom a b).XIsoOfEq (by omega : m = n + -d)).hom x = x := by
      simp
      rfl
    have hf := DG.CellReindex.cellMapFormula F l i a m n hdeg x
    rw [hx] at hf
    have hfm : CellReindex.cellToModule F ⟨l, i⟩ a n x =
        P.act d m n hdeg (namedGenerator F l i) x := by
      change ((F.into (l+1)).app a).f n (CellReindex.cellToSuccessor F l i a n x) = _
      rw [hf, (F.into (l+1)).comm_act]
      rfl
    rw [hfm, f.comm_act, g.comm_act, h l i]
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    using LinearMap.congr_fun he (e x)

variable {I : Type*} {Y : I → RightDGModule A} {U : RightDGModule A}

private def strictSumProjection (b : StrictSum Y U) (i : I) : U ⟶ Y i where
  app a := CochainComplex.ofHom (fun n => ModuleCat.ofHom
    ((DirectSum.component k I (fun l => ((Y l).complex a).X n) i).comp
      (b.coordinates a n).toLinearMap)) (by
        intro n
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact (b.coordinate_d a n x i).symm)
  comm_act m n q h x f := b.coordinate_act m n q h x f i

private theorem strictSumProjection_apply (b : StrictSum Y U) (i : I)
    (a : A.Obj) (n : ℤ) (x : (U.complex a).X n) :
    ((strictSumProjection b i).app a).f n x = b.coordinates a n x i := rfl

private theorem strictSumProjection_inclusion_same (b : StrictSum Y U) (i : I) :
    b.inclusion i ≫ strictSumProjection b i = 𝟙 (Y i) := by
  classical
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change b.coordinates a n (((b.inclusion i).app a).f n x) i = x
  rw [b.coordinate_inclusion]
  exact DFinsupp.single_eq_same

private theorem strictSumProjection_inclusion_ne (b : StrictSum Y U) {i l : I} (h : l ≠ i) :
    b.inclusion l ≫ strictSumProjection b i = 0 := by
  classical
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change b.coordinates a n (((b.inclusion l).app a).f n x) i = 0
  rw [b.coordinate_inclusion]
  exact DFinsupp.single_eq_of_ne h.symm

private def truncateSum (b : StrictSum Y U) (E : Finset I) : U ⟶ U := by
  classical
  exact DG.IndexedSums.desc b (fun i => if i ∈ E then b.inclusion i else 0)

private theorem inclusion_truncateSum (b : StrictSum Y U) (E : Finset I) (i : I)
    [Decidable (i ∈ E)] :
    b.inclusion i ≫ truncateSum b E = if i ∈ E then b.inclusion i else 0 := by
  classical
  by_cases hi : i ∈ E <;> simp [truncateSum, hi]

private theorem truncateSum_projection (b : StrictSum Y U) (E : Finset I) (i : I)
    [Decidable (i ∈ E)] :
    truncateSum b E ≫ strictSumProjection b i =
      if i ∈ E then strictSumProjection b i else 0 := by
  classical
  apply DG.IndexedSums.hom_ext b
  intro l
  rw [← Category.assoc, inclusion_truncateSum]
  by_cases hli : l = i
  · subst l
    by_cases hi : i ∈ E <;> simp [hi]
  · by_cases hi : i ∈ E <;> by_cases hl : l ∈ E <;>
      simp [hi, hl, strictSumProjection_inclusion_ne b hli]

private theorem map_truncateSum_eq_self (F : Presentation.{u,v,w,j} P)
    (b : StrictSum Y U) (f : P ⟶ U) (E : Finset I)
    (hE : ∀ l (i : F.index l) t, b.coordinates _ _ ((f.app _).f _ (namedGenerator F l i)) t ≠ 0 → t ∈ E) :
    f ≫ truncateSum b E = f := by
  classical
  apply hom_ext_on_generators F
  intro l i
  let a := (F.family l).object i
  let n := (F.family l).degree i
  let x := (f.app a).f n (namedGenerator F l i)
  change ((truncateSum b E).app a).f n x = x
  apply (b.coordinates a n).injective
  apply DFinsupp.ext
  intro l'
  change ((truncateSum b E ≫ strictSumProjection b l').app a).f n x =
    b.coordinates a n x l'
  rw [truncateSum_projection]
  by_cases hi : l' ∈ E
  · rw [ite_eq_left hi, strictSumProjection_apply]
  · rw [ite_eq_right hi, RightDGModuleModel.zero_app, HomologicalComplex.zero_f]
    exact (not_ne_iff.mp (fun h => hi (hE l i l' h))).symm

end StrictMaps

section DerivedMaps

variable {k : Type u} [CommRing k] {A : DGCategory.{u,max v w,w} k}
variable (h : Derived.HomotopyCategoryLaws A)

private abbrev strictLocalization : RightDGModule A ⥤ D A h :=
  toHomotopyCategory A ⋙ Q A h

variable [S : Preadditive (D A h)]

private theorem strictLocalization_map_zero (hadd : LocalizationMapAdditive h S)
    (M N : RightDGModule A) :
    (strictLocalization h).map (0 : M ⟶ N) = 0 := by
  have hc : HomComplex.homotopyClass (0 : M ⟶ N) = 0 := by
    have he : HomComplex.strictCycle (0 : M ⟶ N) = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      funext a
      change CochainComplex.HomComplex.Cochain.ofHom (0 : M.complex a ⟶ N.complex a) = 0
      simp
    rw [HomComplex.homotopyClass, he]
    exact map_zero (Submodule.mkQ _)
  change (Q A h).map (HomComplex.homotopyClass (0 : M ⟶ N)) = 0
  rw [hc]
  have hh := hadd M N 0 0
  rw [add_zero] at hh
  exact (add_left_cancel ((add_zero _).trans hh)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem realizedSum_compact_of_finiteCell (hadd : LocalizationMapAdditive h S)
    {P : RightDGModule A} (hP : IndexedSemiFree.finiteCell P)
    {I : Type j} {Y : I → RightDGModule A} {U : RightDGModule A} (b : StrictSum Y U) :
    Function.Surjective (@coproductHomMap (D A h) inferInstance S _ _
      ((Q A h).obj P) (DerivedCoproducts.derivedCofan h b)) := by
  classical
  let R := strictLocalization h
  let c : Cofan (fun i => (Q A h).obj (Y i)) := DerivedCoproducts.derivedCofan h b
  obtain ⟨hc⟩ := nativeExistingDerivedCoproduct.{u,v,w,j} h b
  let hc' : IsColimit c := hc
  obtain ⟨F, hF⟩ := hP
  letI := hF
  letI : Fintype (Σ l, F.index l) := Fintype.ofFinite _
  intro f
  change ∃ x, coproductHomMap ((Q A h).obj P) c x = f
  have hp := (IsSemiFree.isKProjective (show IndexedSemiFree.semiFree P from ⟨F⟩)).Q_map_bijective (N := U) h
  obtain ⟨g, hg⟩ := hp.surjective f
  obtain ⟨g, rfl⟩ := homotopyClass_surjective g
  have hg' : R.map g = f := hg
  let E : Finset I := Finset.univ.biUnion fun i : Σ l, F.index l =>
    (b.coordinates _ _ ((g.app _).f _ (namedGenerator F i.1 i.2))).support
  have hE (l : ℕ) (i : F.index l) (t : I)
      (ht : b.coordinates _ _ ((g.app _).f _ (namedGenerator F l i)) t ≠ 0) : t ∈ E :=
    Finset.mem_biUnion.mpr ⟨⟨l, i⟩, Finset.mem_univ _, DFinsupp.mem_support_iff.mpr ht⟩
  let e := truncateSum b E
  have hge : g ≫ e = g := map_truncateSum_eq_self F b g E hE
  have he (i : I) : c.inj i ≫ R.map e = if i ∈ E then c.inj i else 0 := by
    change R.map (b.inclusion i) ≫ R.map e = _
    rw [← R.map_comp, inclusion_truncateSum]
    by_cases hi : i ∈ E
    · simp only [hi, ite_true]
      rfl
    · simp only [hi, ite_false]
      exact strictLocalization_map_zero h hadd _ _
  have hsum : R.map e = ∑ i ∈ E, R.map (strictSumProjection b i) ≫ c.inj i := by
    apply Cofan.IsColimit.hom_ext hc'
    intro i
    rw [he, Preadditive.comp_sum]
    have hh (l : I) : c.inj i ≫ R.map (strictSumProjection b l) ≫ c.inj l =
        if i = l then c.inj i else 0 := by
      rw [← Category.assoc]
      change (R.map (b.inclusion i) ≫ R.map (strictSumProjection b l)) ≫ c.inj l = _
      rw [← R.map_comp]
      by_cases hli : i = l
      · subst l
        rw [strictSumProjection_inclusion_same, R.map_id, Category.id_comp, ite_eq_left rfl]
      · rw [strictSumProjection_inclusion_ne _ hli, strictLocalization_map_zero h hadd,
          zero_comp, ite_eq_right hli]
    simp only [hh]
    exact (Finset.sum_ite_eq E i (fun _ => c.inj i)).symm
  let z (i : I) := DirectSum.of (fun i => (Q A h).obj P ⟶ (Q A h).obj (Y i)) i
    (f ≫ R.map (strictSumProjection b i))
  refine ⟨∑ i ∈ E, z i, ?_⟩
  calc
    _ = ∑ i ∈ E, (f ≫ R.map (strictSumProjection b i)) ≫ c.inj i := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact coproductHomMap_of _ c i _
    _ = f ≫ R.map e := by rw [hsum, Preadditive.comp_sum]; simp only [Category.assoc]
    _ = f := by rw [← hg', ← R.map_comp, hge]

/-- The localization of a finite-cell module is compact for any existing coproduct. -/
private theorem compact_of_finiteCell (hadd : LocalizationMapAdditive h S)
    {P : RightDGModule A} (hP : IndexedSemiFree.finiteCell P) :
    IsCompact.{j,_,_} ((Q A h).obj P) := by
  classical
  intro I Y c hc
  refine ⟨coproductHomMap_injective _ hc, ?_⟩
  let E := kProjectiveLocalizationEquivalence.{u,v,w} A h
  letI : LocallySmall.{max v w} (D A h) := locallySmall_of_faithful E.inverse
  let L := {i : I // ¬ IsZero (Y i)}
  letI : Small.{max v w} L := nonzeroSummandsSmall hc
  let J := Shrink.{max v w} L
  let e : J ≃ L := (equivShrink L).symm
  let i (l : J) : I := (e l).val
  have cover (l : I) (hl : ¬ IsZero (Y l)) : ∃ j : J, i j = l :=
    ⟨e.symm ⟨l, hl⟩, congrArg Subtype.val (e.apply_symm_apply ⟨l, hl⟩)⟩
  have := Localization.essSurj (Q A h) (quasiIsomorphisms A)
  let N (l : J) := (Q A h).objPreimage (Y (i l))
  let iso (l : J) := (Q A h).objObjPreimageIso (Y (i l))
  let b := DG.IndexedSums.nativeSum N
  obtain ⟨hd⟩ := nativeExistingDerivedCoproduct.{u,v,w,max v w} h b
  exact coproductHomMap_surjective_of_cover _ hc hd i iso cover
    (realizedSum_compact_of_finiteCell h hadd hP b)

end DerivedMaps

section PresentationColimit

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}
variable {P : RightDGModule A} (F : Presentation.{u,v,w,j} P)

private abbrev stageStep (i : ℕ) := (F.extension i).inclusion

private def presentationCocone : Cocone (Functor.ofSequence (stageStep F)) where
  pt := P
  ι := NatTrans.ofSequence F.into (by
    intro n
    rw [Functor.ofSequence_map_homOfLE_succ]
    change stageStep F n ≫ F.into (n+1) = F.into n ≫ 𝟙 P
    rw [Category.comp_id]
    exact F.compatible n)

open private isIso_of_degreewise_isIso from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Telescope

set_option backward.isDefEq.respectTransparency false in
private def presentationCoconeIsColimit : IsColimit (presentationCocone F) := by
  let G := Functor.ofSequence (stageStep F)
  let c := colimitCocone G
  let hc := colimitCoconeIsColimit G
  let p := hc.desc (presentationCocone F)
  have hp (l : ℕ) : c.ι.app l ≫ p = F.into l := hc.fac _ l
  have iso (a : A.Obj) (n : ℤ) : IsIso ((p.app a).f n) := by
    let V := RightDGModuleModel.degree (A := A) a n
    let U₁ := forget₂ (ModuleCat.{v} k) AddCommGrpCat.{v}
    let U₂ := forget AddCommGrpCat.{v}
    letI : PreservesFilteredColimitsOfSize.{0,0} U₂ :=
      preservesSmallestFilteredColimits_of_preservesFilteredColimits.{v,v} _
    let d := U₂.mapCocone (U₁.mapCocone (V.mapCocone c))
    have hd : IsColimit d :=
      isColimitOfPreserves U₂ (isColimitOfPreserves U₁ (colimitCoconeIsColimitDegree G a n))
    have equation (l : ℕ) (x : (G.obj l).complex a |>.X n) :
        (p.app a).f n (d.ι.app l x) = ((F.into l).app a).f n x := by
      exact congrArg (fun z : F.stage l ⟶ P => (z.app a).f n x) (hp l)
    have rep (x : (c.pt.complex a).X n) : ∃ (l : ℕ) (y : (F.stage l).complex a |>.X n),
        d.ι.app l y = x := by
      exact Types.jointly_surjective_of_isColimit hd x
    have hbij : Function.Bijective ((p.app a).f n) := by
      constructor
      · intro x y hxy
        obtain ⟨i, xi, rfl⟩ := rep x
        obtain ⟨l, xl, rfl⟩ := rep y
        let p := max i l
        let fi : i ⟶ p := homOfLE (le_max_left i l)
        let fl : l ⟶ p := homOfLE (le_max_right i l)
        have hf (j : ℕ) (f : j ⟶ p) (z : (G.obj j).complex a |>.X n) :
            ((F.into p).app a).f n ((G.map f |>.app a).f n z) =
              ((F.into j).app a).f n z := by
          have e := (presentationCocone F).w f
          exact congrArg (fun m : F.stage j ⟶ P => (m.app a).f n z) e
        rw [equation, equation, ← hf i fi xi, ← hf l fl xl] at hxy
        exact (Types.FilteredColimit.isColimit_eq_iff _ hd).mpr
          ⟨p, fi, fl, F.injective p a n hxy⟩
      · intro x
        obtain ⟨i, xi, hxi⟩ := F.exhaustive a n x
        exact ⟨d.ι.app i xi, (equation i xi).trans hxi⟩
    exact (ConcreteCategory.isIso_iff_bijective _).2 hbij
  letI : IsIso p := isIso_of_degreewise_isIso p iso
  exact IsColimit.ofIsoColimit hc (Cocone.ext (asIso p) hp)

end PresentationColimit

section DerivedFactorization

open CategoryTheory.Pretriangulated

variable {k : Type u} [CommRing k] {A : DGCategory.{u,max v w,w} k}
variable (h : Derived.HomotopyCategoryLaws A)

set_option backward.isDefEq.respectTransparency false in
private theorem derivedPreadditive_unique (S S' : Preadditive (D A h)) : S = S' := by
  letI := Derived.homotopyCategory A h
  letI := derivedCategoryInstance A h
  obtain ⟨SK, AK, ZK, LK, hS, TK, _, _, _, HP, _, SD, AD, ZD, LD, qS, TD, _⟩ :=
    nativeDerivedTriangulation.{u,v,w} A h
  letI : HasShift (D A h) ℤ := SD
  letI : Preadditive (D A h) := AD
  letI : HasZeroObject (D A h) := ZD
  letI : ∀ n : ℤ, (shiftFunctor (D A h) n).Additive := LD
  letI : Pretriangulated (D A h) := TD
  exact Subsingleton.elim S S'

set_option backward.isDefEq.respectTransparency false in
private theorem factors_through_stage [S : Preadditive (D A h)]
    {X : D A h} (hX : IsCompact.{max v w,_,_} X)
    {P : RightDGModule A} (F : Presentation.{u,max v w,w,j} P)
    (f : X ⟶ (Q A h).obj P) :
    ∃ (n : ℕ) (g : X ⟶ (Q A h).obj (F.stage n)),
      g ≫ (strictLocalization h).map (F.into n) = f := by
  letI := Derived.homotopyCategory A h
  letI := derivedCategoryInstance A h
  let R := strictLocalization h
  let b := DG.IndexedSums.sumRealization F.stage (fun _ _ => inferInstance)
  let hU := DG.IndexedSums.isColimit b
  let L := presentationCocone F
  let p := Telescope.telescopeComparison (stageStep F) hU L
  have hp := telescope_quasiIso (stageStep F) hU (presentationCoconeIsColimit F)
  let e := DerivedKProjective.replacementIso h p hp
  obtain ⟨S', hT⟩ := nativeCompactTelescope.{u,v,w} A h
  have hEq := derivedPreadditive_unique h S S'
  have hC : @CompactTelescope.Compact.{max v w,_,_} (D A h) inferInstance S' X :=
    hEq ▸ compact_preservesCoproducts.{max v w,max u (v+1) (w+1), _} hX
  obtain ⟨_, _, hfac⟩ := hT X hC (stageStep F) hU
  obtain ⟨n, g, hg⟩ := hfac (f ≫ e.inv)
  have eq (n : ℕ) : CompactTelescope.telescopeStage (stageStep F) hU n ≫ p = F.into n := by
    dsimp only [CompactTelescope.telescopeStage, p, Telescope.telescopeComparison]
    rw [Category.assoc, coneInclusion_coneComparison, Telescope.inj_sumToSequence]
    rfl
  refine ⟨n, g, ?_⟩
  have hr : g ≫ R.map (CompactTelescope.telescopeStage (stageStep F) hU n) = f ≫ e.inv := hg
  change g ≫ R.map (F.into n) = f
  rw [← eq n, R.map_comp, ← Category.assoc, hr]
  change (f ≫ e.inv) ≫ e.hom = f
  simp

open private hom_eq_of_heq from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoefficientLift

set_option backward.isDefEq.respectTransparency false in
private theorem factors_through_finiteCell
    [S : Preadditive (D A h)]
    {X : D A h} (hX : IsCompact.{max v w,_,_} X)
    {P : RightDGModule A} (F : Presentation.{u,max v w,w,max v w} P)
    (n : ℕ) (f : X ⟶ (Q A h).obj (F.stage n)) :
    ∃ (L : RightDGModule A) (_ : IndexedSemiFree.finiteCell L) (i : L ⟶ F.stage n)
      (g : X ⟶ (Q A h).obj L), g ≫ (strictLocalization h).map i = f := by
  letI := Derived.homotopyCategory A h
  letI := derivedCategoryInstance A h
  let Q₀ := Derived.quotient A h
  let R₀ := strictLocalization h
  obtain ⟨T, HS, PR, hTo, hTm, _, _, hCol⟩ :=
    (stageHomComparison.{u,v,w,max v w,0}).1 A h
  have hSS := derivedPreadditive_unique h S PR
  letI : HasShift (Derived.derivedCategory A h) ℤ := HS
  letI : Preadditive (Derived.derivedCategory A h) := PR
  let sh := shiftFunctor (Derived.derivedCategory A h) (0 : ℤ)
  let V : RightDGModule A ⥤ Derived.derivedCategory A h := (𝟭 _) ⋙ T ⋙ Q₀ ⋙ sh
  let η : T ≅ toHomotopyCategory A := NatIso.ofComponents (fun M => eqToIso (hTo M))
    (fun {M N} f => hom_eq_of_heq (hTo M) (hTo N) (hTm f))
  let e : V ≅ R₀ :=
    Functor.isoWhiskerLeft (T ⋙ Q₀) (shiftFunctorZero (Derived.derivedCategory A h) ℤ) ≪≫
      Functor.isoWhiskerRight η Q₀
  obtain ⟨G, _⟩ := DG.CellReindex.directSumDecomposition F
  obtain ⟨_, hNE, hDir⟩ := closedCellsDirected.{u,max v w,w,max v w} F G n
  letI : Nonempty (ClosedCells G n) := hNE
  letI : IsDirectedOrder (ClosedCells G n) := ⟨hDir⟩
  obtain ⟨B, hB⟩ := stageSubmodulesExist.{u,max v w,w,max v w} F G n
  have hX' : @IsCompact.{max v w,_,_} (D A h) inferInstance PR X := hSS ▸ hX
  obtain ⟨hc⟩ := hCol X hX' F G n B 0
  let Gr := AddCommGrpCat.{max u (v+1) (w+1)}
  letI : PreservesFilteredColimitsOfSize.{max v w,max v w} (forget Gr) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u (v+1) (w+1),max u (v+1) (w+1),max v w,max v w} _
  let y : X ⟶ V.obj (F.stage n) := f ≫ e.inv.app (F.stage n)
  obtain ⟨E, g, hg⟩ := exists_addGroup_colimit_representative hc y
  let i : B.diagram.obj E ⟶ F.stage n := B.inclusion.app E
  have hg' : g ≫ V.map i = f ≫ e.inv.app (F.stage n) := hg
  refine ⟨B.diagram.obj E, hB E, i, g ≫ e.hom.app _, ?_⟩
  calc
    _ = g ≫ V.map i ≫ e.hom.app (F.stage n) := by
      rw [Category.assoc, ← e.hom.naturality i]
    _ = _ := by
      rw [← Category.assoc, hg', Category.assoc, e.inv_hom_id_app]
      exact Category.comp_id f

set_option backward.isDefEq.respectTransparency false in
/-- In the native derived category at an adequate bound, the compact objects
are precisely the retracts of the images of finite-cell semi-free modules. -/
theorem nativeCompactFiniteCells : NativeCompactFiniteCells.{u,v,w,j} := by
  intro k _ A h
  dsimp only
  intro S hS X
  letI := Derived.homotopyCategory A h
  letI := derivedCategoryInstance A h
  letI : Preadditive (D A h) := S
  have := Localization.essSurj (Q A h) (quasiIsomorphisms A)
  let nativeCompact_of_retract (Y : D A h)
      (hR : IsFiniteCellRetract (𝟭 (RightDGModule A)) h Y) : IsCompact.{j,_,_} Y := by
    obtain ⟨P, hP, ⟨r⟩⟩ := hR
    exact compact_of_retract r (compact_of_finiteCell h hS hP)
  refine ⟨⟨?_, ?_⟩, nativeCompact_of_retract X⟩
  · intro hX
    let M := (Q A h).objPreimage X
    obtain ⟨P, p, ⟨F⟩, _, hp⟩ := unboundedSemiFreeResolutionInUniverse.{u,v,w} k A M
    let e := (DerivedKProjective.replacementIso h p hp) ≪≫ (Q A h).objObjPreimageIso X
    obtain ⟨n, f, hf⟩ := factors_through_stage h hX F e.inv
    obtain ⟨L, hL, i, g, hg⟩ := factors_through_finiteCell h hX F n f
    refine ⟨L, hL, ⟨⟨g, (strictLocalization h).map i ≫ (strictLocalization h).map (F.into n) ≫ e.hom, ?_⟩⟩⟩
    rw [← Category.assoc, ← Category.assoc, hg, hf, e.inv_hom_id]
  · rintro ⟨P, hP, ⟨r⟩⟩
    exact compact_of_retract r (compact_of_finiteCell h hS hP)

end DerivedFactorization

private theorem retract_iff_of_fullyFaithful {C : Type*} {D : Type*}
    [Category* C] [Category* D] {F : C ⥤ D} (hF : F.FullyFaithful)
    {X Y : C} {Z : D} (e : F.obj Y ≅ Z) :
    Nonempty (Retract X Y) ↔ Nonempty (Retract (F.obj X) Z) := by
  constructor
  · rintro ⟨r⟩
    exact ⟨(r.map F).trans (Retract.ofIso e)⟩
  · rintro ⟨r⟩
    let r' := r.trans (Retract.ofIso e.symm)
    refine ⟨⟨hF.preimage r'.i, hF.preimage r'.r, hF.map_injective ?_⟩⟩
    rw [F.map_comp, hF.map_preimage, hF.map_preimage, r'.retract, F.map_id]

section Coefficients

open AmbientDerived (category strictInput)
open CoefficientLift (liftCategory liftFunctor)
open DerivedCoefficientLift (Descent strictTransition)

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}

set_option backward.isDefEq.respectTransparency false in
private theorem finiteCellRetract_lift_iff
    (h : Derived.HomotopyCategoryLaws (liftCategory.{u,v,w,t} A))
    (X : D (liftCategory.{u,v,w,t} A) h) :
    IsFiniteCellRetract (𝟭 (RightDGModule (liftCategory.{u,v,w,t} A))) h X ↔
      IsFiniteCellRetract (liftFunctor.{u,v,w,t} A) h X := by
  let B := liftCategory.{u,v,w,t} A
  let T := liftFunctor.{u,v,w,t} A
  letI := Derived.homotopyCategory B h
  letI := derivedCategoryInstance B h
  let R : RightDGModule B ⥤ D B h := toHomotopyCategory B ⋙ Q B h
  constructor
  · rintro ⟨P, hP, ⟨r⟩⟩
    obtain ⟨M, hM, ⟨e⟩⟩ := (DG.CellLift.finiteCellTransport.{u,v,w,t} P).mp hP
    exact ⟨M, hM, ⟨r.trans (Retract.ofIso (R.mapIso e.symm))⟩⟩
  · rintro ⟨P, hP, r⟩
    exact ⟨T.obj P, (DG.CellLift.finiteCellTransport.{u,v,w,t} (T.obj P)).mpr
      ⟨P, hP, ⟨Iso.refl _⟩⟩, r⟩

set_option backward.isDefEq.respectTransparency false in
/-- The finite-cell module for the retraction can be taken over the original
dg category, with both retract maps in its adequate derived category. -/
theorem originalCompactFiniteCells : OriginalCompactFiniteCells.{u,v,w,j,t} := by
  intro k _ A
  dsimp only
  intro h S hS X
  obtain ⟨e, hC⟩ := nativeCompactFiniteCells.{u,max v t,w,j}
    (category.{u,v,w,t} A) h S hS X
  have hl := finiteCellRetract_lift_iff.{u,v,w,max w t} h X
  exact ⟨e.trans hl, fun hR => hC (hl.mpr hR)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The transition from an adequate native bound to a larger coefficient bound
preserves and reflects compactness. -/
theorem nativeCompactnessComparison : NativeCompactnessComparison.{u,v,w,s} := by
  intro k _ A
  dsimp only
  intro h h'
  let B := liftCategory.{u,max v w,w,s} A
  let T := liftFunctor.{u,max v w,w,s} A
  letI := Derived.homotopyCategory A h
  letI := Derived.homotopyCategory B h'
  letI := derivedCategoryInstance A h
  letI := derivedCategoryInstance B h'
  obtain ⟨⟨d, hd, _, _⟩, _⟩ := DG.DerivedCoefficientLift.nativeDerivedCoefficientTransition.{u,v,w,s} A h h'
  obtain ⟨hD⟩ := hd.2
  refine ⟨d, hd, ?_⟩
  intro S S' hS hS' X
  rw [(nativeCompactFiniteCells.{u,v,w,0} A h S hS X).1,
    (nativeCompactFiniteCells.{u,max v s,w,0} B h' S' hS' (d.D.obj X)).1,
    finiteCellRetract_lift_iff.{u,max v w,w,s}]
  constructor
  · rintro ⟨M, hM, r⟩
    exact ⟨M, hM, (retract_iff_of_fullyFaithful hD (d.representedIso M)).mp r⟩
  · rintro ⟨M, hM, r⟩
    exact ⟨M, hM, (retract_iff_of_fullyFaithful hD (d.representedIso M)).mpr r⟩

set_option backward.isDefEq.respectTransparency false in
/-- The transition between two adequate derived categories of the same original
dg category preserves and reflects compactness. -/
theorem ambientCompactnessComparison : AmbientCompactnessComparison.{u,v,w,t,s} := by
  intro k _ A
  dsimp only
  intro h h'
  let B := category.{u,v,w,t} A
  let C := category.{u,v,w,max t s} A
  let U := strictInput.{u,v,w,t} A
  let V := strictInput.{u,v,w,max t s} A
  let T := strictTransition.{u,v,w,t,s} A
  letI := Derived.homotopyCategory B h
  letI := Derived.homotopyCategory C h'
  letI := derivedCategoryInstance B h
  letI := derivedCategoryInstance C h'
  obtain ⟨d, hd, _, _⟩ := DG.DerivedCoefficientLift.derivedCoefficientTransition.{u,v,w,t,s} A h h'
  have h0 : Derived.HomotopyCategoryLaws A := ⟨instCategoryK A, rfl⟩
  obtain ⟨alpha, _, _⟩ := DG.DerivedCoefficientLift.derivedCoefficientTransitionOnInputs.{u,v,w,t,s} A h0 h h'
  obtain ⟨hD⟩ := hd.2
  refine ⟨d, hd, ?_⟩
  intro S S' hS hS' X
  have iso (M : RightDGModule A) :
      d.D.obj ((Q B h).obj (U.obj M)) ≅ (Q C h').obj (V.obj M) :=
    d.representedIso (U.obj M) ≪≫ (strictLocalization h').mapIso (alpha.app M)
  rw [(originalCompactFiniteCells.{u,v,w,0,t} A h S hS X).1,
    (originalCompactFiniteCells.{u,v,w,0,max t s} A h' S' hS' (d.D.obj X)).1]
  constructor
  · rintro ⟨M, hM, r⟩
    exact ⟨M, hM, (retract_iff_of_fullyFaithful hD (iso M)).mp r⟩
  · rintro ⟨M, hM, r⟩
    exact ⟨M, hM, (retract_iff_of_fullyFaithful hD (iso M)).mpr r⟩

end Coefficients

end

end DerivedFormalization.RightDGModule
