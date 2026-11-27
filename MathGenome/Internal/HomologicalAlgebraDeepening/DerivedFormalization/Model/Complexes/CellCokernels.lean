import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.Complexes.CellFactorization
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.CellCokernels
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.CategoryTheory.Limits.Constructions.ZeroObjects
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty ZeroObject
open HomologicalComplex HomotopicalAlgebra

universe u

namespace DerivedFormalization.Model.Complexes

open Specs.ComplexCellCokernels

variable {A : Type u} [Ring A]

/-- Factoring the zero-source map by disk cells gives a surjection from a contractible complex. -/
private theorem contractibleCovers (E : Cochains A) :
    ∃ (D : Cochains A) (p : D ⟶ E),
      degreewiseSurjective A p ∧ Nonempty (Homotopy (𝟙 D) 0) := by
  obtain ⟨F, _⟩ := jCellFactorization A
  let a := Arrow.mk (0 : (0 : Cochains A) ⟶ E)
  let p := F.p.app a
  have hp := F.hp a
  change (J A).rlp p at hp
  rw [j_rlp] at hp
  obtain ⟨K, degree, ⟨e, _⟩, ⟨h⟩⟩ := jCellDecomposition A _ (F.hi a)
  let e' := (zeroCoprodIso _).symm ≪≫ e
  refine ⟨_, p, hp, ⟨?_⟩⟩
  simpa [Category.assoc] using (h.compLeft e'.inv).compRight e'.hom

theorem iCellCokernel_isKProjective : kProjectiveType.{u} := by
  intro A _ X Y f hf
  refine ⟨fun {E} g hE ↦ ?_⟩
  obtain ⟨D, p, hp, ⟨hD⟩⟩ := contractibleCovers E
  have hD' : D.Acyclic := by
    intro k
    apply (exactAt_iff_isZero_homology _ _).2
    apply (IsZero.iff_id_eq_zero _).2
    simpa using hD.homologyMap_eq k
  have hq : QuasiIso p :=
    (quasiIso_iff p).2 fun k ↦ (quasiIsoAt_iff_exactAt p k (hD' k)).2 (hE k)
  have hr : (I A).rlp p := by
    rw [i_rlp]
    exact ⟨hp, hq⟩
  have hLift : HasLiftingProperty f p :=
    (transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp (I A) ℕ f hf) p hr
  have sq : CommSq (0 : X ⟶ D) f p (cokernel.π f ≫ g) := ⟨by simp⟩
  let t := cokernel.desc f sq.lift (by simp)
  have ht : t ≫ p = g := by
    apply (cancel_epi (cokernel.π f)).1
    simp [t]
  refine ⟨(Homotopy.ofEq ht.symm).trans ?_⟩
  simpa using (hD.compLeft t).compRight p

theorem isKProjective_iff_homComplex_acyclic : kProjectiveIffHomAcyclicType.{u} := by
  intro A _ P
  constructor
  · intro hP E hE n
    apply (exactAt_iff_isZero_homology _ _).2
    have hShift : (E⟦n⟧).Acyclic := by
      rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hE ⊢
      exact ObjectProperty.prop_of_iso _
        (((HomotopyCategory.quotient _ _).commShiftIso n).symm.app E)
        ((HomotopyCategory.subcategoryAcyclic (ModuleCat A)).le_shift n _ hE)
    apply AddCommGrpCat.isZero_iff_subsingleton.2
    refine ⟨fun x y ↦ ?_⟩
    let e := CochainComplex.HomComplex.homologyAddEquiv P E n
    apply e.injective
    have hz (a : CochainComplex.HomComplex.CohomologyClass P E n) : a = 0 := by
      obtain ⟨z, rfl⟩ := CochainComplex.HomComplex.CohomologyClass.mk_surjective a
      apply (CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff z).2
      apply (CochainComplex.HomComplex.CohomologyClass.toHom_mk_eq_zero_iff z).1
      rw [CochainComplex.HomComplex.CohomologyClass.toHom_mk,
        HomotopyCategory.quotient_map_eq_zero_iff]
      exact hP.nonempty_homotopy_zero _ hShift
    exact (hz _).trans (hz _).symm
  · intro h
    refine ⟨fun {E} f hE ↦ ?_⟩
    let z := CochainComplex.HomComplex.Cocycle.equivHomShift
      (f ≫ ((shiftFunctorZero (Cochains A) ℤ).app E).inv)
    have hzero : IsZero ((CochainComplex.HomComplex P E).homology 0) :=
      (h E hE 0).isZero_homology
    have hclass : CochainComplex.HomComplex.CohomologyClass.mk z = 0 := by
      let e := CochainComplex.HomComplex.homologyAddEquiv P E 0
      have hsub := AddCommGrpCat.isZero_iff_subsingleton.1 hzero
      exact e.symm.injective (hsub.elim _ _)
    have hz := congrArg CochainComplex.HomComplex.CohomologyClass.toHom hclass
    rw [CochainComplex.HomComplex.CohomologyClass.toHom_mk, map_zero,
      HomotopyCategory.quotient_map_eq_zero_iff] at hz
    obtain ⟨H⟩ := hz
    have H' : Homotopy (f ≫ ((shiftFunctorZero (Cochains A) ℤ).app E).inv) 0 := by
      simpa [z] using H
    exact ⟨by simpa using H'.compRight ((shiftFunctorZero (Cochains A) ℤ).app E).hom⟩

theorem iCellCokernel_homAcyclic : homAcyclicType.{u} := by
  intro A _ X Y f hf
  exact (isKProjective_iff_homComplex_acyclic A _).1 (iCellCokernel_isKProjective A f hf)

private abbrev moduleLifting (A : Type u) [Ring A] : MorphismProperty (ModuleCat.{u} A) :=
  (epimorphisms (ModuleCat.{u} A)).llp

private theorem attachment_component_lifting {X Y : Cochains A} {f : X ⟶ Y}
    (a : AttachCells.{u} (iGenerator A) f) (k : ℤ) : moduleLifting A (f.f k) := by
  classical
  obtain ⟨e, he, _⟩ := iAttachment A f a
  let M := ModuleCat.of A ({i : a.ι // a.π i = k} →₀ A)
  have : Projective M := ModuleCat.projective_of_free Finsupp.basisSingleOne
  intro U V p hp
  have : Epi p := hp
  refine ⟨fun {t b} sq ↦ ?_⟩
  let v : M ⟶ Y.X k := ModuleCat.ofHom
    ((e k).toLinearMap.comp (LinearMap.inr A (X.X k) M))
  let s := Projective.factorThru (v ≫ b) p
  have hs : s ≫ p = v ≫ b := Projective.factorThru_comp _ _
  let l : Y.X k ⟶ U := ModuleCat.ofHom ((t.hom.coprod s.hom).comp (e k).symm.toLinearMap)
  refine CommSq.HasLift.mk' ⟨l, ?_, ?_⟩
  · apply ModuleCat.hom_ext
    ext x
    change l (f.f k x) = t x
    rw [← he k x]
    change t ((e k).symm (e k (x, 0))).1 +
      s ((e k).symm (e k (x, 0))).2 = t x
    simp
  · apply ModuleCat.hom_ext
    ext y
    obtain ⟨⟨x, m⟩, rfl⟩ := (e k).surjective y
    change p (t ((e k).symm (e k (x, m))).1 +
      s ((e k).symm (e k (x, m))).2) = b (e k (x, m))
    rw [LinearEquiv.symm_apply_apply, map_add]
    have ht : p (t x) = b (e k (x, 0)) := by
      have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom sq.w) x
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, he k x] using h
    have hm : p (s m) = b (e k (0, m)) :=
      DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hs) m
    rw [ht, hm, ← map_add, ← map_add]
    simp

private abbrev attachmentMaps (A : Type u) [Ring A] :=
  (coproducts.{u} (I A)).pushouts

private theorem attachmentMap_component_lifting (k : ℤ) :
    attachmentMaps A ≤ (moduleLifting A).inverseImage
      (eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k) := by
  intro X Y f hf
  obtain ⟨a⟩ := (nonempty_attachCells_iff (iGenerator A) f).2 hf
  exact attachment_component_lifting a k

private theorem component_lifting_of_transfinite {J : Type} [LinearOrder J] [SuccOrder J]
    [OrderBot J] [WellFoundedLT J]
    {X Y : Cochains A} {f : X ⟶ Y} (hf : (attachmentMaps A).TransfiniteCompositionOfShape J f)
    (k : ℤ) : moduleLifting A (f.f k) := by
  let E := eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k
  have : PreservesWellOrderContinuousOfShape J E :=
    ⟨fun j _ ↦ inferInstanceAs (PreservesColimitsOfShape (Set.Iio j)
      (eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k))⟩
  have h : (moduleLifting A).TransfiniteCompositionOfShape J (E.map f) :=
    (hf.ofLE (attachmentMap_component_lifting k)).map
  exact transfiniteCompositionsOfShape_le (moduleLifting A) J (E.map f) ⟨h⟩

private theorem splitMono_of_moduleLifting {X Y : ModuleCat.{u} A} {g : X ⟶ Y}
    (hg : moduleLifting A g) : IsSplitMono g := by
  have hl : HasLiftingProperty g (0 : X ⟶ (0 : ModuleCat A)) := hg _ (by infer_instance)
  have sq : CommSq (𝟙 X) g (0 : X ⟶ (0 : ModuleCat A)) 0 := ⟨by simp⟩
  exact ⟨⟨⟨sq.lift, sq.fac_left⟩⟩⟩

theorem iCell_degreewiseSplitMono : degreewiseSplitMonoType.{u} := by
  intro A _ X Y f hf k
  obtain ⟨h⟩ := hf
  exact splitMono_of_moduleLifting (component_lifting_of_transfinite h k)


/-- A disk modulo its upper sphere is the sphere in its lower degree. -/
private noncomputable def diskQuotient (n : ℤ) : disk A n ⟶ sphere A n :=
  (diskHomEquiv n).symm (sphereHomEquiv n (𝟙 (sphere A n))).val

private theorem sphereHomEquiv_zero {Z : Cochains A} (n : ℤ) :
    (sphereHomEquiv n (0 : sphere A n ⟶ Z)).val = 0 := by
  change ((singleObjXSelf (ComplexShape.up ℤ) n (ModuleCat.of A A)).inv ≫
    (0 : sphere A n ⟶ Z).f n) (1 : A) = 0
  erw [ModuleCat.comp_apply, zero_f_apply]
  rfl

private theorem diskQuotient_condition (n : ℤ) :
    iGenerator A n ≫ diskQuotient n = 0 := by
  apply (sphereHomEquiv (n + 1)).injective
  apply Subtype.ext
  rw [sphereHomEquiv_iGenerator_comp, sphereHomEquiv_zero, diskQuotient,
    Equiv.apply_symm_apply]
  exact (sphereHomEquiv n (𝟙 (sphere A n))).property

private noncomputable def diskQuotientDesc (n : ℤ) {Z : Cochains A} (q : disk A n ⟶ Z)
    (hq : iGenerator A n ≫ q = 0) : sphere A n ⟶ Z :=
  (sphereHomEquiv n).symm ⟨diskHomEquiv n q, by
    rw [← sphereHomEquiv_iGenerator_comp, hq, sphereHomEquiv_zero]⟩

private theorem diskQuotient_fac (n : ℤ) {Z : Cochains A} (q : disk A n ⟶ Z)
    (hq : iGenerator A n ≫ q = 0) :
    diskQuotient n ≫ diskQuotientDesc n q hq = q := by
  apply (diskHomEquiv n).injective
  rw [diskHomEquiv_comp, diskQuotient, Equiv.apply_symm_apply, ← sphereHomEquiv_comp,
    Category.id_comp, diskQuotientDesc, Equiv.apply_symm_apply]

private theorem diskQuotient_epi (n : ℤ) : Epi (diskQuotient (A := A) n) := by
  constructor
  intro Z v w h
  apply (sphereHomEquiv n).injective
  apply Subtype.ext
  have hh := congrArg (diskHomEquiv n) h
  simpa only [diskHomEquiv_comp, diskQuotient, Equiv.apply_symm_apply,
    ← sphereHomEquiv_comp, Category.id_comp] using hh

private noncomputable def attachmentCokernelIso {X Y : Cochains A} {f : X ⟶ Y}
    (a : AttachCells.{u} (iGenerator A) f) :
    cokernel f ≅ ∐ (fun i : a.ι ↦ sphere A (a.π i)) := by
  let S : a.ι → Cochains A := fun i ↦ sphere A (a.π i)
  let p : a.cofan₂.pt ⟶ ∐ S := Cofan.IsColimit.desc a.isColimit₂
    (fun i ↦ diskQuotient (a.π i) ≫ Sigma.ι S i)
  have hp (i : a.ι) : a.cofan₂.inj i ≫ p = diskQuotient (a.π i) ≫ Sigma.ι S i :=
    Cofan.IsColimit.fac a.isColimit₂ _ i
  have w : a.m ≫ p = 0 := by
    apply Cofan.IsColimit.hom_ext a.isColimit₁
    intro i
    rw [a.hm_assoc, hp, ← Category.assoc, diskQuotient_condition]
    simp
  haveI : Epi p := by
    constructor
    intro Z v z hh
    apply Sigma.hom_ext
    intro i
    have := diskQuotient_epi (A := A) (a.π i)
    apply (cancel_epi (diskQuotient (A := A) (a.π i))).1
    rw [← Category.assoc, ← Category.assoc, ← hp i, Category.assoc,
      Category.assoc, hh]
  let hc : IsColimit (CokernelCofork.ofπ p w) :=
    CokernelCofork.IsColimit.ofπ' p w (fun {Z} q hq ↦ by
      have kill (i : a.ι) : iGenerator A (a.π i) ≫ a.cofan₂.inj i ≫ q = 0 := by
        rw [← a.hm_assoc, hq, comp_zero]
      refine ⟨Sigma.desc (fun i ↦ diskQuotientDesc (a.π i) (a.cofan₂.inj i ≫ q) (kill i)), ?_⟩
      apply Cofan.IsColimit.hom_ext a.isColimit₂
      intro i
      rw [← Category.assoc, hp, Category.assoc, Sigma.ι_comp_desc, diskQuotient_fac])
  haveI := isIso_cokernel_map_of_isPushout a.isPushout.flip
  exact (asIso (cokernel.map a.m f a.g₁ a.g₂ a.isPushout.flip.w)).symm ≪≫
    (cokernelIsCokernel a.m).coconePointUniqueUpToIso hc

/-- Passing to the cokernel of the same initial object is a pushout. -/
private theorem cokernelSquare {C : Type*} [Category* C] [HasZeroMorphisms C]
    [HasCokernels C] {X Y Z : C} (b : X ⟶ Y) (g : Y ⟶ Z) (c : X ⟶ Z)
    (w : b ≫ g = c) :
    IsPushout (cokernel.π b) g (cokernel.map b c (𝟙 X) g (by simpa using w))
      (cokernel.π c) := by
  have hw : cokernel.π b ≫ cokernel.map b c (𝟙 X) g (by simpa using w) =
      g ≫ cokernel.π c := by simp
  apply IsPushout.of_isColimit' ⟨hw⟩
  apply PushoutCocone.IsColimit.mk hw
    (fun s ↦ cokernel.desc c s.inr (by
      rw [← w, Category.assoc, ← s.condition, cokernel.condition_assoc, zero_comp]))
  · intro s
    apply (cancel_epi (cokernel.π b)).1
    rw [← Category.assoc, hw, Category.assoc, cokernel.π_desc, s.condition]
  · intro s
    exact cokernel.π_desc _ _ _
  · intro s m _ hm
    apply (cancel_epi (cokernel.π c)).1
    simpa using hm

variable {X Y : Cochains A} {f : X ⟶ Y}

private noncomputable def stageMap (h : CategoryTheory.TransfiniteCompositionOfShape ℕ f)
    (n : ℕ) : X ⟶ h.F.obj n :=
  h.isoBot.inv ≫ h.F.map (homOfLE (Nat.zero_le n) : 0 ⟶ n)

@[reassoc]
private theorem stageMap_comp (h : CategoryTheory.TransfiniteCompositionOfShape ℕ f)
    {n m : ℕ} (a : n ⟶ m) : stageMap h n ≫ h.F.map a = stageMap h m := by
  simp only [stageMap, Category.assoc, ← h.F.map_comp]
  rfl

@[reassoc]
private theorem stageMap_incl (h : CategoryTheory.TransfiniteCompositionOfShape ℕ f)
    (n : ℕ) : stageMap h n ≫ h.incl.app n = f := by
  simp only [stageMap, Category.assoc, NatTrans.naturality, Functor.const_obj_map]
  exact h.fac

private noncomputable abbrev quotientStages (h : CategoryTheory.TransfiniteCompositionOfShape ℕ f) :
    ℕ ⥤ Cochains A :=
  (show ℕ ⥤ Arrow (Cochains A) from
    { obj := fun n ↦ Arrow.mk (stageMap h n)
      map := fun a ↦ Arrow.homMk (𝟙 _) (h.F.map a) (by simp [stageMap_comp])
      map_id := fun n ↦ Arrow.hom_ext _ _ rfl (h.F.map_id n)
      map_comp := fun a b ↦ Arrow.hom_ext _ _ (by simp) (h.F.map_comp a b) }) ⋙ coker _

private theorem quotientStages_pushout (h : CategoryTheory.TransfiniteCompositionOfShape ℕ f)
    {n m : ℕ} (a : n ⟶ m) :
    IsPushout (cokernel.π (stageMap h n)) (h.F.map a) ((quotientStages h).map a)
      (cokernel.π (stageMap h m)) :=
  cokernelSquare _ _ _ (stageMap_comp h a)

private noncomputable def quotientInclusions
    (h : CategoryTheory.TransfiniteCompositionOfShape ℕ f) :
    quotientStages h ⟶ (Functor.const ℕ).obj (cokernel f) where
  app n := cokernel.map (stageMap h n) f (𝟙 _) (h.incl.app n) (by simp [stageMap_incl])
  naturality n m a := by
    apply (cancel_epi (cokernel.π (stageMap h n))).1
    change cokernel.π (stageMap h n) ≫
      (quotientStages h).map a ≫ cokernel.map (stageMap h m) f (𝟙 X) (h.incl.app m)
        (by simp [stageMap_incl]) =
      cokernel.π (stageMap h n) ≫ cokernel.map (stageMap h n) f (𝟙 X) (h.incl.app n)
        (by simp [stageMap_incl]) ≫ 𝟙 _
    rw [(quotientStages_pushout h a).w_assoc, cokernel.π_desc_assoc, cokernel.π_desc,
      Category.comp_id, ← Category.assoc]
    simp

private theorem quotientInclusions_pushout (h : CategoryTheory.TransfiniteCompositionOfShape ℕ f)
    (n : ℕ) :
    IsPushout (cokernel.π (stageMap h n)) (h.incl.app n) ((quotientInclusions h).app n)
      (cokernel.π f) :=
  cokernelSquare _ _ _ (stageMap_incl h n)

private noncomputable def quotientStageColimit
    (h : CategoryTheory.TransfiniteCompositionOfShape ℕ f) :
    IsColimit (Cocone.mk _ (quotientInclusions h)) := by
  let original (s : Cocone (quotientStages h)) : Cocone h.F :=
    Cocone.mk s.pt
      { app := fun n ↦ cokernel.π (stageMap h n) ≫ s.ι.app n
        naturality := fun n m a ↦ by
          change h.F.map a ≫ cokernel.π (stageMap h m) ≫ s.ι.app m =
            (cokernel.π (stageMap h n) ≫ s.ι.app n) ≫ 𝟙 _
          rw [← (quotientStages_pushout h a).w_assoc, s.w a, Category.comp_id] }
  let d (s : Cocone (quotientStages h)) : cokernel f ⟶ s.pt :=
    cokernel.desc f (h.isColimit.desc (original s)) (by
      calc
        f ≫ h.isColimit.desc (original s) =
            h.isoBot.inv ≫ h.incl.app 0 ≫ h.isColimit.desc (original s) := by
          rw [← Category.assoc]
          exact congrArg (· ≫ h.isColimit.desc (original s)) h.fac.symm
        _ = h.isoBot.inv ≫ cokernel.π (stageMap h 0) ≫ s.ι.app 0 := by
          rw [h.isColimit.fac (original s) 0]
        _ = 0 := by
          have eq : h.isoBot.inv = stageMap h 0 := by simp [stageMap]
          rw [eq, cokernel.condition_assoc, zero_comp])
  refine ⟨d, ?_, ?_⟩
  · intro s n
    apply (cancel_epi (cokernel.π (stageMap h n))).1
    change cokernel.π (stageMap h n) ≫ (quotientInclusions h).app n ≫ d s = _
    rw [(quotientInclusions_pushout h n).w_assoc]
    simp only [d, cokernel.π_desc, h.isColimit.fac]
    rfl
  · intro s m hm
    apply (cancel_epi (cokernel.π f)).1
    simp only [d, cokernel.π_desc]
    apply h.isColimit.hom_ext
    intro n
    rw [h.isColimit.fac]
    change h.incl.app n ≫ cokernel.π f ≫ m = cokernel.π (stageMap h n) ≫ s.ι.app n
    rw [← (quotientInclusions_pushout h n).w_assoc]
    exact congrArg (cokernel.π (stageMap h n) ≫ ·) (hm n)

private theorem quotientStages_zero (h : CategoryTheory.TransfiniteCompositionOfShape ℕ f) :
    IsZero ((quotientStages h).obj 0) := by
  change IsZero (cokernel (stageMap h 0))
  have : IsIso (stageMap h 0) := by
    simpa [stageMap] using (inferInstance : IsIso h.isoBot.inv)
  exact (isZero_zero _).of_iso (cokernel.ofEpi (stageMap h 0))

private theorem component_lifting_of_pushout {X₁ X₂ Y₁ Y₂ : Cochains A}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ Y₁} {r : X₂ ⟶ Y₂} {b : Y₁ ⟶ Y₂}
    (sq : IsPushout t l r b) (k : ℤ) (hl : moduleLifting A (l.f k)) :
    moduleLifting A (r.f k) := by
  let E := eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k
  exact (pushouts_le (P := moduleLifting A)) (E.map r)
    ((moduleLifting A).pushouts_mk (E.map_isPushout sq) hl)

private theorem quotientInclusions_lifting
    (h : (attachmentMaps A).TransfiniteCompositionOfShape ℕ f) (n : ℕ) (k : ℤ) :
    moduleLifting A (((quotientInclusions h.toTransfiniteCompositionOfShape).app n).f k) := by
  let : OrderBot (Set.Ici n) := Set.Ici.orderBot
  exact component_lifting_of_pushout (quotientInclusions_pushout _ n) k
    (component_lifting_of_transfinite (h.ici n) k)

theorem iCellCokernel_filtration : filtrationType.{u} := by
  intro A _ X Y f hf
  obtain ⟨h⟩ := hf
  let c := h.toTransfiniteCompositionOfShape
  refine ⟨quotientStages c, quotientInclusions c, quotientStages_zero c,
    ⟨quotientStageColimit c⟩, fun n k ↦ splitMono_of_moduleLifting
      (quotientInclusions_lifting h n k), ?_⟩
  intro n
  let a := homOfLE (Nat.le_succ n)
  have hm : attachmentMaps A (c.F.map a) := h.map_mem n (not_isMax_iff.2 ⟨n + 1, by omega⟩)
  obtain ⟨attach⟩ := (nonempty_attachCells_iff (iGenerator A) (c.F.map a)).2 hm
  have sq := quotientStages_pushout c a
  refine ⟨fun k ↦ splitMono_of_moduleLifting
    (component_lifting_of_pushout sq k (attachment_component_lifting attach k)), ?_⟩
  have := isIso_cokernel_map_of_isPushout sq.flip
  exact ⟨attach.ι, attach.π,
    ⟨(asIso (cokernel.map _ _ _ _ sq.flip.w)).symm ≪≫ attachmentCokernelIso attach⟩⟩

theorem iCellCokernel_degreewiseProjective : degreewiseProjectiveType.{u} := by
  intro A _ X Y f hf k
  obtain ⟨h⟩ := hf
  let c := h.toTransfiniteCompositionOfShape
  let g := ((quotientInclusions c).app 0).f k
  have hg : moduleLifting A g := quotientInclusions_lifting h 0 k
  have hz : IsZero (((quotientStages c).obj 0).X k) :=
    (eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k).map_isZero (quotientStages_zero c)
  constructor
  intro M N b p hp
  have hLift : HasLiftingProperty g p := hg p hp
  have sq : CommSq (0 : ((quotientStages c).obj 0).X k ⟶ M) g p b :=
    ⟨hz.eq_of_src _ _⟩
  exact ⟨sq.lift, sq.fac_right⟩

end DerivedFormalization.Model.Complexes
