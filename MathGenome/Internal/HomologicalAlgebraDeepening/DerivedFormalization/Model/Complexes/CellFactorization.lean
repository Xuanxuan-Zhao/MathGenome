import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.Complexes.Generators
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.CellFactorization
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Prod
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered

open CategoryTheory CategoryTheory.MorphismProperty

universe u

namespace DerivedFormalization.Model.Complexes

/-- A sequential composite of pushouts of coproducts of sphere inclusions. -/
noncomputable def iCell (A : Type u) [Ring A] : MorphismProperty (Cochains A) :=
  ((coproducts.{u} (I A)).pushouts).transfiniteCompositionsOfShape ℕ

/-- A sequential composite of pushouts of coproducts of zero-to-disk maps. -/
noncomputable def jCell (A : Type u) [Ring A] : MorphismProperty (Cochains A) :=
  ((coproducts.{u} (J A)).pushouts).transfiniteCompositionsOfShape ℕ


open CategoryTheory.Limits HomologicalComplex HomotopicalAlgebra
open Specs.ComplexCellFactorization

section SequentialFactorization

variable {A : Type u} [Ring A]
variable {S T : ℤ → Cochains A} (g : ∀ n, S n ⟶ T n)

/-- A functorial choice of a stage and a map to the original target. -/
private structure AttachmentStage (C : Type*) [Category* C] where
  obj : Arrow C ⥤ C
  projection : obj ⟶ Arrow.rightFunc

private def AttachmentStage.toArrow (s : AttachmentStage (Cochains A)) :
    Arrow (Cochains A) ⥤ Arrow (Cochains A) where
  obj f := Arrow.mk (s.projection.app f)
  map φ := Arrow.homMk (s.obj.map φ) φ.right (s.projection.naturality φ)
  map_id _ := Arrow.hom_ext _ _ (s.obj.map_id _) rfl
  map_comp φ ψ := Arrow.hom_ext _ _ (s.obj.map_comp φ ψ) rfl

private noncomputable def AttachmentStage.next (s : AttachmentStage (Cochains A)) :
    AttachmentStage (Cochains A) where
  obj := s.toArrow ⋙ SmallObject.functor g ⋙ Arrow.leftFunc
  projection :=
    { app f := SmallObject.πFunctorObj g (s.projection.app f)
      naturality _ _ φ := SmallObject.functorMap_π g (s.toArrow.map φ) }

private noncomputable def AttachmentStage.inclusion (s : AttachmentStage (Cochains A)) :
    s.obj ⟶ (s.next g).obj where
  app f := SmallObject.ιFunctorObj g (s.projection.app f)
  naturality _ _ φ := (SmallObject.ιFunctorObj_naturality g (s.toArrow.map φ)).symm

private noncomputable def attachmentStage : ℕ → AttachmentStage (Cochains A)
  | 0 => ⟨Arrow.leftFunc, Arrow.leftToRight⟩
  | n + 1 => (attachmentStage n).next g

private noncomputable abbrev attachmentDiagram : ℕ ⥤ Arrow (Cochains A) ⥤ Cochains A :=
  Functor.ofSequence (fun n ↦ (attachmentStage g n).inclusion g)

private noncomputable def attachmentProjections :
    attachmentDiagram g ⟶ (Functor.const ℕ).obj Arrow.rightFunc :=
  NatTrans.ofSequence (fun n ↦ (attachmentStage g n).projection) (fun n ↦ by
    erw [Functor.ofSequence_map_homOfLE_succ]
    apply NatTrans.ext
    funext f
    exact (SmallObject.ιFunctorObj_πFunctorObj g _).trans (Category.comp_id _).symm)

private noncomputable def attachmentCocone : Cocone (attachmentDiagram g) :=
  Cocone.mk Arrow.rightFunc (attachmentProjections g)

private noncomputable def attachmentComposite (f : Arrow (Cochains A)) :
    CategoryTheory.TransfiniteCompositionOfShape ℕ ((colimit.ι (attachmentDiagram g) 0).app f) where
  F := attachmentDiagram g ⋙ (evaluation _ _).obj f
  isoBot := Iso.refl _
  isWellOrderContinuous :=
    { nonempty_isColimit n hn := by
        cases n with
        | zero => exact (hn.not_isMin isMin_bot).elim
        | succ n => exact (Order.not_isSuccLimit_succ n hn).elim }
  incl := (((evaluation _ _).obj f).mapCocone (colimit.cocone (attachmentDiagram g))).ι
  isColimit := isColimitOfPreserves ((evaluation _ _).obj f) (colimit.isColimit _)

private lemma attachmentColimit_projection (f : Arrow (Cochains A)) (n : ℕ) :
    (attachmentComposite g f).incl.app n ≫
      (colimit.desc (attachmentDiagram g) (attachmentCocone g)).app f =
        (attachmentStage g n).projection.app f :=
  colimit.ι_desc_app _ _ n f

private lemma attachmentColimit_step (f : Arrow (Cochains A)) (n : ℕ) :
    (attachmentComposite g f).F.map (homOfLE (n.le_add_right 1)) =
      SmallObject.ιFunctorObj g ((attachmentStage g n).projection.app f) := by
  change ((attachmentDiagram g).map _).app f = _
  erw [Functor.ofSequence_map_homOfLE_succ]
  rfl

private lemma sequentialFactorization
    (compact : ∀ (i : ℤ) (F : ℕ ⥤ Cochains A) {c : Cocone F}, IsColimit c →
      ∀ a : S i ⟶ c.pt, ∃ (n : ℕ) (t : S i ⟶ F.obj n), t ≫ c.ι.app n = a) :
    ∃ F : FunctorialFactorizationData
      (((coproducts.{u} (ofHoms g)).pushouts).transfiniteCompositionsOfShape ℕ) (ofHoms g).rlp,
      ∀ f : Arrow (Cochains A),
        IsSequentialCellFactorization g (F.i.app f) (F.p.app f) := by
  let F : FunctorialFactorizationData
      (((coproducts.{u} (ofHoms g)).pushouts).transfiniteCompositionsOfShape ℕ) (ofHoms g).rlp :=
    { Z := colimit (attachmentDiagram g)
      i := colimit.ι (attachmentDiagram g) 0
      p := colimit.desc (attachmentDiagram g) (attachmentCocone g)
      fac := colimit.ι_desc (attachmentCocone g) 0
      hi f := ⟨{
        toTransfiniteCompositionOfShape := attachmentComposite g f
        map_mem n _ := by
          change ((coproducts.{u} (ofHoms g)).pushouts)
            ((attachmentComposite g f).F.map (homOfLE (n.le_add_right 1)))
          rw [attachmentColimit_step]
          exact (SmallObject.attachCellsιFunctorObj g _).pushouts_coproducts }⟩
      hp f := by
        intro X Y v hv
        cases hv with
        | mk i =>
          constructor
          intro a b sq
          let c := attachmentComposite g f
          obtain ⟨n, t, ht⟩ := compact i c.F c.isColimit a
          change t ≫ c.incl.app n = a at ht
          have comm : t ≫ (attachmentStage g n).projection.app f = g i ≫ b := by
            erw [← attachmentColimit_projection g f n, ← Category.assoc, ht, sq.w]
          obtain ⟨l, hl, hr⟩ := SmallObject.ιFunctorObj_extension g t b ⟨comm⟩
          refine ⟨⟨{
            l := l ≫ c.incl.app (n + 1)
            fac_left := by
              have step : (SmallObject.ιFunctorObj g ((attachmentStage g n).projection.app f)) ≫
                  c.incl.app (n + 1) = c.incl.app n := by
                have h := c.incl.naturality (homOfLE (n.le_add_right 1))
                erw [attachmentColimit_step g f n] at h
                exact h.trans (Category.comp_id _)
              erw [← Category.assoc, hl, Category.assoc, step, ht]
            fac_right := by
              erw [Category.assoc, attachmentColimit_projection g f (n + 1)]
              exact hr }⟩⟩ }
  refine ⟨F, fun f ↦ ⟨attachmentComposite g f, ?_⟩⟩
  intro n
  let c := attachmentComposite g f
  let stageSpec (q : c.F.obj n ⟶ f.right) : Prop :=
    ∃ e : SmallObject.functorObj g q ≅ c.F.obj (n + 1),
      SmallObject.ιFunctorObj g q ≫ e.hom = c.F.map (homOfLE (n.le_add_right 1)) ∧
        e.hom ≫ c.incl.app (n + 1) ≫ F.p.app f = SmallObject.πFunctorObj g q
  change stageSpec (c.incl.app n ≫ F.p.app f)
  apply Eq.mpr (congrArg stageSpec (attachmentColimit_projection g f n))
  refine ⟨Iso.refl _, ?_, ?_⟩
  · exact (Category.comp_id _).trans (attachmentColimit_step g f n).symm
  · exact (Category.id_comp _).trans (attachmentColimit_projection g f (n + 1))

end SequentialFactorization


private lemma sphereFactorsThroughStage {A : Type u} [Ring A] (i : ℤ)
    (F : ℕ ⥤ Cochains A) {c : Cocone F} (hc : IsColimit c) (a : sphere A i ⟶ c.pt) :
    ∃ (n : ℕ) (t : sphere A i ⟶ F.obj n), t ≫ c.ι.app n = a := by
  let U (j : ℤ) := eval (ModuleCat.{u} A) (ComplexShape.up ℤ) j ⋙ forget (ModuleCat.{u} A)
  let : PreservesColimitsOfShape ℕ (forget (ModuleCat.{u} A)) :=
    (preservesSmallestFilteredColimits_of_preservesFilteredColimits.{u, u}
      (forget (ModuleCat.{u} A))).preserves_filtered_colimits ℕ
  have hU (j : ℤ) : IsColimit ((U j).mapCocone c) := by
    dsimp only [U]
    exact isColimitOfPreserves _ hc
  let z := sphereHomEquiv i a
  obtain ⟨n, x, hx⟩ := Types.jointly_surjective_of_isColimit (hU i) z.val
  change (c.ι.app n).f i x = z.val at hx
  have closed : (c.ι.app n).f (i + 1) ((F.obj n).d i (i + 1) x) =
      (c.ι.app n).f (i + 1) 0 := by
    have h := congrArg (fun m : (F.obj n).X i ⟶ c.pt.X (i + 1) ↦ m x)
      ((c.ι.app n).comm i (i + 1))
    change c.pt.d i (i + 1) ((c.ι.app n).f i x) =
      (c.ι.app n).f (i + 1) ((F.obj n).d i (i + 1) x) at h
    rw [hx, z.property] at h
    rw [map_zero]
    exact h.symm
  obtain ⟨m, φ, hφ⟩ := (Types.FilteredColimit.isColimit_eq_iff' (hU (i + 1))
    ((F.obj n).d i (i + 1) x) (0 : (F.obj n).X (i + 1))).mp closed
  change (F.map φ).f (i + 1) ((F.obj n).d i (i + 1) x) = (F.map φ).f (i + 1) 0 at hφ
  have closed' : (F.obj m).d i (i + 1) ((F.map φ).f i x) = 0 := by
    have h := congrArg (fun k : (F.obj n).X i ⟶ (F.obj m).X (i + 1) ↦ k x)
      ((F.map φ).comm i (i + 1))
    simpa only [ModuleCat.comp_apply, hφ, map_zero] using h
  let t := (sphereHomEquiv i (X := F.obj m)).symm ⟨(F.map φ).f i x, closed'⟩
  refine ⟨m, t, (sphereHomEquiv i).injective (Subtype.ext ?_)⟩
  rw [sphereHomEquiv_comp, show (sphereHomEquiv i t).val = (F.map φ).f i x from
    congrArg Subtype.val (Equiv.apply_symm_apply _ _)]
  exact (congrArg (fun k : F.obj n ⟶ c.pt ↦ k.f i x) (c.w φ)).trans hx

/-- Functorial factorization by successive free sphere attachments. -/
theorem iCellFactorization : iFactorizationType.{u} := by
  intro A _
  exact sequentialFactorization (iGenerator A) (fun n F _ hc ↦ sphereFactorsThroughStage (n + 1) F hc)

/-- Functorial factorization by successive free disk attachments. -/
theorem jCellFactorization : jFactorizationType.{u} := by
  intro A _
  apply sequentialFactorization (jGenerator A)
  intro n F c hc a
  exact ⟨0, 0, by
    rw [zero_comp]
    exact (Limits.isZero_zero (Cochains A)).eq_of_src _ _⟩


section DiskAttachments

variable {A : Type u} [Ring A]

private noncomputable def diskContraction (n : ℤ) : Homotopy (𝟙 (disk A n)) 0 := by
  let r := ComplexShape.up_mk n (n + 1) rfl
  let e₀ : (disk A n).X n ≅ ModuleCat.of A A := doubleXIso₀ (𝟙 (ModuleCat.of A A)) r
  let e₁ : (disk A n).X (n + 1) ≅ ModuleCat.of A A :=
    doubleXIso₁ (𝟙 (ModuleCat.of A A)) r (by omega)
  let h (i j : ℤ) : (disk A n).X i ⟶ (disk A n).X j :=
    if w : i = n + 1 ∧ j = n then
      eqToHom (congrArg (disk A n).X w.1) ≫ e₁.hom ≫ e₀.inv ≫
        eqToHom (congrArg (disk A n).X w.2.symm)
    else 0
  refine ⟨h, ?_, ?_⟩
  · intro i j w
    apply dite_eq_right
    rintro ⟨rfl, rfl⟩
    exact w r
  · intro i
    change 𝟙 ((disk A n).X i) = dNext i h + prevD i h + 0
    rw [dNext_eq h (ComplexShape.up_mk i (i + 1) rfl),
      prevD_eq h (ComplexShape.up_mk (i - 1) i (by omega)), add_zero]
    have hd : (disk A n).d n (n + 1) = e₀.hom ≫ e₁.inv := by
      change (double (𝟙 (ModuleCat.of A A)) r).d n (n + 1) = _
      rw [double_d _ _ (by omega), Category.id_comp]
      rfl
    have hh : h (n + 1) n = e₁.hom ≫ e₀.inv := by
      unfold h
      rw [dite_eq_left ⟨rfl, rfl⟩]
      change 𝟙 _ ≫ e₁.hom ≫ e₀.inv ≫ 𝟙 _ = _
      rw [Category.id_comp, Category.comp_id]
    by_cases hi₀ : i = n
    · subst i
      have hz : h n (n - 1) = 0 := dite_eq_right (by omega)
      rw [hd, hh, hz, zero_comp, add_zero]
      exact (by simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id])
    · by_cases hi₁ : i = n + 1
      · subst i
        have hz : h (n + 1 + 1) (n + 1) = 0 := dite_eq_right (by omega)
        have hn : n + 1 - 1 = n := by omega
        rw [hz, comp_zero, zero_add]
        erw [hn, hh, hd]
        exact (by simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id])
      · exact (isZero_double_X _ r i hi₀ hi₁).eq_of_src _ _

private noncomputable def degreeCofan {K : Type u} {D : K → Cochains A}
    (c : Cofan D) (i : ℤ) : Cofan (fun k ↦ (D k).X i) :=
  Cofan.mk (c.pt.X i) (fun k ↦ (c.inj k).f i)

private noncomputable def degreeCofanIsColimit {K : Type u} {D : K → Cochains A}
    (c : Cofan D) (hc : IsColimit c) (i : ℤ) : IsColimit (degreeCofan c i) := by
  let E := eval (ModuleCat.{u} A) (ComplexShape.up ℤ) i
  let c' := Cofan.mk c.pt c.inj
  have hc' : IsColimit c' := IsColimit.ofIsoColimit hc (Cofan.ext (Iso.refl _) (by simp [c']))
  exact isColimitCofanMkObjOfIsColimit E _ _ hc'

private noncomputable def coproductContraction {K : Type u} {D : K → Cochains A}
    (c : Cofan D) (hc : IsColimit c) (contract : ∀ k, Homotopy (𝟙 (D k)) 0) :
    Homotopy (𝟙 c.pt) 0 := by
  let h (i j : ℤ) : c.pt.X i ⟶ c.pt.X j :=
    Cofan.IsColimit.desc (degreeCofanIsColimit c hc i)
      (fun k ↦ (contract k).hom i j ≫ (c.inj k).f j)
  have hinj (i j : ℤ) (k : K) :
      (c.inj k).f i ≫ h i j = (contract k).hom i j ≫ (c.inj k).f j :=
    Cofan.IsColimit.fac (degreeCofanIsColimit c hc i) _ k
  refine ⟨h, ?_, ?_⟩
  · intro i j hij
    apply Cofan.IsColimit.hom_ext (degreeCofanIsColimit c hc i)
    intro k
    change (c.inj k).f i ≫ h i j = (c.inj k).f i ≫ 0
    rw [hinj, (contract k).zero _ _ hij, zero_comp, comp_zero]
  · intro i
    apply Cofan.IsColimit.hom_ext (degreeCofanIsColimit c hc i)
    intro k
    change (c.inj k).f i ≫ 𝟙 _ = (c.inj k).f i ≫ (dNext i h + prevD i h + 0)
    let hNext := ComplexShape.up_mk i (i + 1) rfl
    let hPrev := ComplexShape.up_mk (i - 1) i (by omega)
    have hk := (contract k).comm i
    change 𝟙 ((D k).X i) = dNext i (contract k).hom + prevD i (contract k).hom + 0 at hk
    rw [add_zero, dNext_eq _ hNext, prevD_eq _ hPrev] at hk
    rw [add_zero, Preadditive.comp_add, dNext_eq h hNext, prevD_eq h hPrev,
      reassoc_of% ((c.inj k).comm _ _), hinj, reassoc_of% (hinj i (i - 1) k),
      (c.inj k).comm, ← Category.assoc, ← Category.assoc, ← Preadditive.add_comp,
      ← hk, Category.id_comp, Category.comp_id]

private lemma jAttachmentSourceIsZero {X Y : Cochains A} {f : X ⟶ Y}
    (a : AttachCells.{u} (jGenerator A) f) : IsZero a.cofan₁.pt := by
  have h : 𝟙 a.cofan₁.pt = 0 := by
    apply Cofan.IsColimit.hom_ext a.isColimit₁
    intro k
    exact (Limits.isZero_zero (Cochains A)).eq_of_src _ _
  exact (IsZero.iff_id_eq_zero _).2 h

private noncomputable def jAttachmentIsCoproduct {X Y : Cochains A} {f : X ⟶ Y}
    (a : AttachCells.{u} (jGenerator A) f) : IsColimit (BinaryCofan.mk f a.g₂) :=
  isCoproductOfIsInitialIsPushout f a.g₂ a.g₁ a.m
    (jAttachmentSourceIsZero a).isInitial a.isPushout.isColimit

/-- A disk attachment is the coproduct of the old complex and a contractible disk sum. -/
theorem jAttachment : jAttachmentType.{u} := by
  intro A _ X Y f a
  let h := jAttachmentIsCoproduct a
  refine ⟨⟨(coprodIsCoprod X a.cofan₂.pt).coconePointUniqueUpToIso h, ?_, ?_⟩, ?_⟩
  · exact IsColimit.comp_coconePointUniqueUpToIso_hom _ h ⟨WalkingPair.left⟩
  · exact IsColimit.comp_coconePointUniqueUpToIso_hom _ h ⟨WalkingPair.right⟩
  · exact ⟨coproductContraction a.cofan₂ a.isColimit₂ (fun k ↦ diskContraction (a.π k))⟩


/-- The colimit of the disk attachments adds the coproduct indexed by all the stages' cells. -/
theorem jCellDecomposition : jCellDecompositionType.{u} := by
  classical
  intro A _ X Y f hf
  obtain ⟨c⟩ := hf
  let h : RelativeCellComplex.{u} (fun _ : ℕ ↦ jGenerator A) f :=
    { toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape
      attachCells n hn := ((nonempty_attachCells_iff _ _).mpr (c.map_mem n hn)).some }
  let D (k : h.Cells) := disk A k.i
  let P := X ⨿ ∐ D
  let a (n : ℕ) := h.attachCells n (not_isMax n)
  let inc (k : h.Cells) : D k ⟶ P := Sigma.ι D k ≫ coprod.inr
  let σ (n : ℕ) : (a n).cofan₂.pt ⟶ P :=
    Cofan.IsColimit.desc (a n).isColimit₂ (fun k ↦ inc ⟨n, not_isMax n, k⟩)
  let e (n : ℕ) (m : h.F.obj n ⟶ P) : h.F.obj (n + 1) ⟶ P :=
    (a n).isPushout.desc m (σ n) ((jAttachmentSourceIsZero (a n)).eq_of_src _ _)
  let η : ∀ n, h.F.obj n ⟶ P :=
    Nat.rec (h.isoBot.hom ≫ coprod.inl) (fun n z ↦ e n z)
  have hstep (n : ℕ) :
      h.F.map (homOfLE (n.le_add_right 1)) ≫ η (n + 1) = η n :=
    (a n).isPushout.inl_desc _ _ _
  have hcell (k : h.Cells) : (h.attachCells k.j k.hj).cell k.k ≫ η (k.j + 1) = inc k := by
    obtain ⟨n, hn, k⟩ := k
    change (a n).cell k ≫ e n (η n) = inc ⟨n, hn, k⟩
    have hdesc := (a n).isPushout.inr_desc (η n) (σ n)
      ((jAttachmentSourceIsZero (a n)).eq_of_src _ _)
    erw [AttachCells.cell_def, Category.assoc, hdesc]
    exact Cofan.IsColimit.fac (a n).isColimit₂ _ k
  let ηc : Cocone h.F := Cocone.mk P (NatTrans.ofSequence η (fun n ↦ by
    exact (hstep n).trans (Category.comp_id _).symm))
  let v := h.isColimit.desc ηc
  let w : P ⟶ Y := coprod.desc f (Sigma.desc (fun k ↦ k.ι))
  have hv (n : ℕ) : h.incl.app n ≫ v = η n := h.isColimit.fac ηc n
  have hv₀ : f ≫ v = coprod.inl := by
    calc
      f ≫ v = (h.isoBot.inv ≫ h.incl.app ⊥) ≫ v := congrArg (· ≫ v) h.fac.symm
      _ = coprod.inl := by
        erw [Category.assoc, hv]
        exact h.isoBot.inv_hom_id_assoc _
  have hv₁ (k : h.Cells) : k.ι ≫ v = inc k := by
    erw [RelativeCellComplex.Cells.ι, Category.assoc, hv, hcell]
  have hw₀ : coprod.inl ≫ w = f := coprod.inl_desc _ _
  have hw₁ (k : h.Cells) : inc k ≫ w = k.ι := by
    dsimp [inc, w]
    rw [Category.assoc, coprod.inr_desc, Sigma.ι_comp_desc]
  refine ⟨h.Cells, fun k ↦ k.i, ⟨⟨{
    hom := w
    inv := v
    hom_inv_id := ?_
    inv_hom_id := ?_ }, hw₀⟩, ?_⟩⟩
  · apply coprod.hom_ext
    · change coprod.inl ≫ (w ≫ v) = coprod.inl ≫ 𝟙 P
      rw [← Category.assoc, hw₀, hv₀, Category.comp_id]
    · apply Sigma.hom_ext
      intro k
      change inc k ≫ (w ≫ v) = inc k ≫ 𝟙 P
      rw [← Category.assoc, hw₁, hv₁, Category.comp_id]
  · apply h.hom_ext
    · erw [← Category.assoc, hv₀, hw₀, Category.comp_id]
    · intro k
      erw [← Category.assoc, hv₁, hw₁, Category.comp_id]
  · exact ⟨coproductContraction _ (coproductIsCoproduct D)
      (fun k ↦ diskContraction k.i)⟩

end DiskAttachments


section SphereAttachments

variable {A : Type u} [Ring A]

private lemma iGeneratorUpperIsIso (n : ℤ) :
    IsIso ((iGenerator A n).f (n + 1)) := by
  let e : (sphere A (n + 1)).X (n + 1) ≅ ModuleCat.of A A :=
    singleObjXSelf (ComplexShape.up ℤ) (n + 1) (ModuleCat.of A A)
  let r := ComplexShape.up_mk n (n + 1) rfl
  let d : (disk A n).X (n + 1) ≅ ModuleCat.of A A :=
    doubleXIso₁ (𝟙 (ModuleCat.of A A)) r (by omega)
  have he : (iGenerator A n).f (n + 1) = e.hom ≫ d.inv :=
    mkHomFromSingle_f d.inv (fun k _ ↦ by
      erw [double_d_eq_zero₀ (𝟙 (ModuleCat.of A A)) r (n + 1) k (by omega), comp_zero])
  rw [he]
  infer_instance

private lemma sphereDegreeIsZero (n m : ℤ) (h : m ≠ n) : IsZero ((sphere A n).X m) :=
  isZero_single_obj_X (ComplexShape.up ℤ) n (ModuleCat.of A A) m h

private lemma diskDegreeIsZero (n m : ℤ) (h₀ : m ≠ n) (h₁ : m ≠ n + 1) :
    IsZero ((disk A n).X m) :=
  isZero_double_X (𝟙 (ModuleCat.of A A)) (ComplexShape.up_mk n (n + 1) rfl) m h₀ h₁

private noncomputable def diskGeneratorInDegree (n m : ℤ) (h : n = m) : (disk A n).X m :=
  h ▸ diskGenerator A n

/-- A degree component of a disk is determined by its attaching sphere and its lower generator. -/
private lemma diskDegreeHomExt (n m : ℤ) {M : ModuleCat.{u} A}
    {t₁ t₂ : (disk A n).X m ⟶ M}
    (hs : (iGenerator A n).f m ≫ t₁ = (iGenerator A n).f m ≫ t₂)
    (hb : ∀ h : n = m, t₁ (diskGeneratorInDegree n m h) = t₂ (diskGeneratorInDegree n m h)) :
    t₁ = t₂ := by
  by_cases h₀ : n = m
  · subst m
    let e : (disk A n).X n ≅ ModuleCat.of A A :=
      doubleXIso₀ (𝟙 (ModuleCat.of A A)) (ComplexShape.up_mk n (n + 1) rfl)
    apply (cancel_epi e.inv).mp
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    exact hb rfl
  · by_cases h₁ : n + 1 = m
    · subst m
      have := iGeneratorUpperIsIso (A := A) n
      exact (cancel_epi ((iGenerator A n).f (n + 1))).mp hs
    · exact (diskDegreeIsZero n m (Ne.symm h₀) (Ne.symm h₁)).eq_of_src _ _

/-- A map on the attaching sphere and an image of the lower generator extend to the disk
in a given degree. Only the datum in that degree contributes. -/
private lemma diskDegreeHomExists (n m : ℤ) {M : ModuleCat.{u} A}
    (s : (sphere A (n + 1)).X m ⟶ M) (b : (n = m) → M) :
    ∃ t : (disk A n).X m ⟶ M, (iGenerator A n).f m ≫ t = s ∧
      ∀ h : n = m, t (diskGeneratorInDegree n m h) = b h := by
  by_cases h₀ : n = m
  · subst m
    let e : (disk A n).X n ≅ ModuleCat.of A A :=
      doubleXIso₀ (𝟙 (ModuleCat.of A A)) (ComplexShape.up_mk n (n + 1) rfl)
    refine ⟨e.hom ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton A M (b rfl)),
      (sphereDegreeIsZero (n + 1) n (by omega)).eq_of_src _ _, fun h ↦ ?_⟩
    have he : e.hom (e.inv (1 : A)) = 1 :=
      congrArg (fun k : ModuleCat.of A A ⟶ ModuleCat.of A A ↦ k 1) e.inv_hom_id
    change LinearMap.toSpanSingleton A M (b rfl) (e.hom (e.inv 1)) = b rfl
    rw [he, LinearMap.toSpanSingleton_apply_one]
  · by_cases h₁ : n + 1 = m
    · subst m
      have := iGeneratorUpperIsIso (A := A) n
      refine ⟨inv ((iGenerator A n).f (n + 1)) ≫ s, ?_, fun h ↦ (h₀ h).elim⟩
      simp
    · exact ⟨0, (sphereDegreeIsZero (n + 1) m (Ne.symm h₁)).eq_of_src _ _,
        fun h ↦ (h₀ h).elim⟩

private lemma attachingSphereRelation {X Y : Cochains A} {f : X ⟶ Y}
    (a : AttachCells.{u} (iGenerator A) f) (i : a.ι) :
    iGenerator A (a.π i) ≫ a.cell i = (a.cofan₁.inj i ≫ a.g₁) ≫ f := by
  rw [AttachCells.cell_def, ← a.hm_assoc, Category.assoc, a.isPushout.w]

private lemma sphereAttachmentInDegree {X Y : Cochains A} {f : X ⟶ Y}
    (a : AttachCells.{u} (iGenerator A) f) (n : ℤ) :
    ∃ e : (X.X n × ({i : a.ι // a.π i = n} →₀ A)) ≃ₗ[A] Y.X n,
      (∀ x : X.X n, e (x, 0) = f.f n x) ∧
      ∀ i : {i : a.ι // a.π i = n},
        e (0, Finsupp.single i 1) =
          (a.cell i.val).f n (diskGeneratorInDegree (a.π i.val) n i.property) := by
  classical
  let K := {i : a.ι // a.π i = n}
  let M := ModuleCat.of A (X.X n × (K →₀ A))
  let E := eval (ModuleCat.{u} A) (ComplexShape.up ℤ) n
  let old : X.X n ⟶ M := ModuleCat.ofHom (LinearMap.inl A (X.X n) (K →₀ A))
  let basis (i : K) : M := (0, Finsupp.single i 1)
  let gen (i : K) : Y.X n :=
    (a.cell i.val).f n (diskGeneratorInDegree (a.π i.val) n i.property)
  let u : M ⟶ Y.X n :=
    ModuleCat.ofHom ((f.f n).hom.coprod (Finsupp.linearCombination A gen))
  have hu₀ (x : X.X n) : u (x, 0) = f.f n x := by
    change _ + (Finsupp.linearCombination A gen) 0 = _
    rw [map_zero, add_zero]
    rfl
  have hu₁ (i : K) : u (basis i) = gen i := by
    change (f.f n) 0 + Finsupp.linearCombination A gen (Finsupp.single i 1) = _
    rw [map_zero, zero_add, Finsupp.linearCombination_single, one_smul]
  have huold : old ≫ u = f.f n := ModuleCat.hom_ext (LinearMap.ext hu₀)
  have hp : IsPushout (a.g₁.f n) (a.m.f n) (f.f n) (a.g₂.f n) := a.isPushout.map E
  let s (i : a.ι) := (a.cofan₁.inj i ≫ a.g₁).f n ≫ old
  choose t ht htgen using (fun i : a.ι ↦
    diskDegreeHomExists (a.π i) n (s i) (fun h ↦ basis ⟨i, h⟩))
  let right : a.cofan₂.pt.X n ⟶ M := Cofan.IsColimit.desc (degreeCofanIsColimit _ a.isColimit₂ n) t
  have hright (i : a.ι) : (a.cofan₂.inj i).f n ≫ right = t i :=
    Cofan.IsColimit.fac (degreeCofanIsColimit _ a.isColimit₂ n) t i
  have comm : a.g₁.f n ≫ old = a.m.f n ≫ right := by
    apply Cofan.IsColimit.hom_ext (degreeCofanIsColimit _ a.isColimit₁ n)
    intro i
    have hm := congrArg (fun v ↦ v.f n) (a.hm i)
    change (a.cofan₁.inj i).f n ≫ a.m.f n =
      (iGenerator A (a.π i)).f n ≫ (a.cofan₂.inj i).f n at hm
    change (a.cofan₁.inj i).f n ≫ a.g₁.f n ≫ old =
      (a.cofan₁.inj i).f n ≫ a.m.f n ≫ right
    erw [reassoc_of% hm, hright, ht]
    rfl
  let v := hp.desc old right comm
  have hv₀ : f.f n ≫ v = old := hp.inl_desc _ _ _
  have hvcell (i : a.ι) : (a.cell i).f n ≫ v = t i := by
    change ((a.cofan₂.inj i).f n ≫ a.g₂.f n) ≫ v = t i
    rw [Category.assoc, hp.inr_desc, hright]
  have hvgen (i : K) : v (gen i) = basis i :=
    (congrArg (fun k : (disk A (a.π i.val)).X n ⟶ M ↦
      k (diskGeneratorInDegree (a.π i.val) n i.property)) (hvcell i.val)).trans
      (htgen i.val i.property)
  have uv : u ≫ v = 𝟙 M := by
    apply ModuleCat.hom_ext
    apply LinearMap.prod_ext
    · apply LinearMap.ext
      intro x
      change v (u (x, 0)) = (x, (0 : K →₀ A))
      rw [hu₀]
      exact congrArg (fun k : X.X n ⟶ M ↦ k x) hv₀
    · apply Finsupp.lhom_ext
      intro i r
      rw [← Finsupp.smul_single_one i r, map_smul, map_smul]
      congr 1
      change v (u (basis i)) = basis i
      rw [hu₁, hvgen]
  have vu : v ≫ u = 𝟙 (Y.X n) := by
    apply hp.hom_ext
    · rw [← Category.assoc, hv₀, huold, Category.comp_id]
    · apply Cofan.IsColimit.hom_ext (degreeCofanIsColimit _ a.isColimit₂ n)
      intro i
      change (a.cell i).f n ≫ (v ≫ u) = (a.cell i).f n ≫ 𝟙 _
      rw [← Category.assoc, hvcell, Category.comp_id]
      apply diskDegreeHomExt (a.π i) n
      · have hrel := congrArg (fun k ↦ k.f n) (attachingSphereRelation a i)
        change (iGenerator A (a.π i)).f n ≫ (a.cell i).f n =
          ((a.cofan₁.inj i ≫ a.g₁).f n) ≫ f.f n at hrel
        erw [← Category.assoc, ht, hrel]
        change ((a.cofan₁.inj i ≫ a.g₁).f n ≫ old) ≫ u = _
        rw [Category.assoc, huold]
      · intro hi
        change u (t i (diskGeneratorInDegree (a.π i) n hi)) = gen ⟨i, hi⟩
        rw [htgen, hu₁]
  exact ⟨Iso.toLinearEquiv ⟨u, v, uv, vu⟩, hu₀, hu₁⟩

/-- A sphere attachment adds a free homogeneous generator for each disk's lower end,
whose differential is the image of the corresponding attaching sphere. -/
theorem iAttachment : iAttachmentType.{u} := by
  classical
  intro A _ X Y f a
  choose e he₀ he₁ using (sphereAttachmentInDegree a)
  refine ⟨e, he₀, fun i ↦ ⟨he₁ (a.π i) ⟨i, rfl⟩, ?_⟩⟩
  rw [he₁ (a.π i) ⟨i, rfl⟩]
  change Y.d (a.π i) (a.π i + 1)
      ((a.cell i).f (a.π i) (diskHomEquiv (a.π i) (𝟙 _))) = _
  have h := sphereHomEquiv_iGenerator_comp (a.π i) (a.cell i)
  erw [attachingSphereRelation a i, sphereHomEquiv_comp] at h
  have hd := diskHomEquiv_comp (a.π i) (𝟙 (disk A (a.π i))) (a.cell i)
  erw [Category.id_comp] at hd
  erw [← hd]
  exact h.symm

end SphereAttachments

end DerivedFormalization.Model.Complexes
