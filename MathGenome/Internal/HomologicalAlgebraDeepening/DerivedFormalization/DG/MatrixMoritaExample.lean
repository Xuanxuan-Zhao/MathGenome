import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.MatrixMoritaExample
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactGenerators
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFreeKProjective
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.CategoryTheory.Conj
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Localization
import Mathlib.RingTheory.Morita.Matrix

import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.EndomorphismGenerator
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex

set_option linter.style.haveILetI false
open Specs.DerivedFormalization.DG
open Specs.DerivedFormalization.DG.MatrixMoritaExample
open DerivedFormalization.RightDGModule (GradedHom)

universe u v z j

namespace DerivedFormalization.MatrixMoritaExample

noncomputable section

variable {k : Type u} [Field k]

private abbrev point : (fieldCategory k).Obj := PUnit.unit
private abbrev space (k : Type u) [Field k] (m : ℕ) := (freeModule k m).complex point

private theorem freeTerm_subsingleton (m : ℕ) {i : ℤ} (hi : i ≠ 0) :
    Subsingleton ((space k m).X i) := by
  constructor
  intro x y
  apply DFinsupp.ext
  intro a
  exact (subsingleton_zeroTerm (ModuleCat.of k k) hi).elim _ _

private def coordinates (m : ℕ) : (space k m).X 0 ≃ₗ[k] (Fin m → k) :=
  DFinsupp.linearEquivFunOnFintype.trans
    ((LinearEquiv.piCongrRight fun _ =>
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of k k)).toLinearEquiv)).trans
      (LinearEquiv.piCongrLeft k (fun _ => k) Equiv.ulift))

private theorem proveFreeTerms : FreeTerms.{u} := by
  intro k _ m
  exact ⟨⟨coordinates m⟩, fun _ => freeTerm_subsingleton m⟩

private theorem free_d (m : ℕ) (i j : ℤ) : (space k m).d i j = 0 := by
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      exact (space k m).shape _ _ (by decide)
    · exact ModuleCat.hom_ext (LinearMap.ext fun x => (freeTerm_subsingleton (k := k) m hj).elim _ _)
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx : x = 0 := (freeTerm_subsingleton (k := k) m hi).elim _ _
    simp [hx]

private theorem free_act_zero (m : ℕ) (x : (space k m).X 0)
    (a : (fieldCategory k).hom point point |>.X 0) :
    (freeModule k m).act (a := point) (b := point) 0 0 0 rfl x a =
      readZero (ModuleCat.of k k) 0 a • x := by
  apply DFinsupp.ext
  intro p
  change zeroProduct (k := k) k 0 0 0 (x p) a = _
  rw [zeroProduct_apply, mul_comm, ← smul_eq_mul]
  change writeZero (ModuleCat.of k k) 0
    (readZero (ModuleCat.of k k) 0 a • readZero (ModuleCat.of k k) 0 (x p)) =
      readZero (ModuleCat.of k k) 0 a • x p
  rw [map_smul, write_read]

private abbrev gradedEnd (k : Type u) [Field k] (m : ℕ) (i : ℤ) :=
  GradedHom (freeModule k m) (freeModule k m) i

private theorem gradedEnd_subsingleton (m : ℕ) {r : ℤ} (hr : r ≠ 0) :
    Subsingleton (gradedEnd k m r) := by
  constructor
  intro f g
  apply GradedHom.ext
  intro a i j h
  cases a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  by_cases hi : i = 0
  · exact (freeTerm_subsingleton m (i := j) (by omega)).elim _ _
  · have hx : x = 0 := (freeTerm_subsingleton m hi).elim _ _
    simp [hx]

private def evaluation (m : ℕ) : gradedEnd k m 0 →ₗ[k] Module.End k ((space k m).X 0) where
  toFun f := (f.app point 0 0 rfl).hom
  map_add' f g := by
    change (((f.val point + g.val point).v 0 0 rfl)).hom = _
    rw [Cochain.add_v, ModuleCat.hom_add]
  map_smul' c f := by
    change (((c • f.val point).v 0 0 rfl)).hom = _
    rw [Cochain.smul_v, ModuleCat.hom_smul]
    rfl

private theorem evaluation_injective (m : ℕ) : Function.Injective (evaluation (k := k) m) := by
  intro f g hfg
  apply GradedHom.ext
  intro a i j h
  cases a
  have hij : j = i := by omega
  subst j
  by_cases hi : i = 0
  · subst i
    exact ModuleCat.hom_ext hfg
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx : x = 0 := (freeTerm_subsingleton (k := k) m hi).elim _ _
    rw [hx, map_zero, map_zero]

private def extend (m : ℕ) (f : Module.End k ((space k m).X 0)) :
    freeModule k m ⟶ freeModule k m where
  app a := by
    cases a
    refine CochainComplex.ofHom (fun i => if hi : i = 0 then
      ((space k m).XIsoOfEq hi).hom ≫ ModuleCat.ofHom f ≫ ((space k m).XIsoOfEq hi).inv
      else 0) ?_
    intro i
    rw [free_d, comp_zero, zero_comp]
  comm_act := by
    intro a b i j n h x r
    cases a; cases b
    by_cases hn : n = 0
    · by_cases hi : i = 0
      · have hj : j = 0 := by omega
        subst i j n
        change f ((freeModule k m).act (a := point) (b := point) 0 0 0 rfl x r) =
          (freeModule k m).act (a := point) (b := point) 0 0 0 rfl (f x) r
        rw [free_act_zero, free_act_zero, map_smul]
      · have hx : x = 0 := (freeTerm_subsingleton m hi).elim _ _
        subst x
        simp
    · exact (freeTerm_subsingleton m hn).elim _ _

private def endEvaluation (m : ℕ) : gradedEnd k m 0 ≃ₗ[k] Module.End k ((space k m).X 0) :=
  LinearEquiv.ofBijective (evaluation m) ⟨evaluation_injective m, fun f =>
    ⟨HomComplex.ofStrict (extend m f), by
      change (Cochain.ofHom ((extend m f).app point) |>.v 0 0 rfl).hom = f
      rw [Cochain.ofHom_v]
      rfl⟩⟩

private abbrev endCategory (k : Type u) [Field k] (m : ℕ) :=
  EndomorphismGenerator.endomorphismCategory.{u,u,u,u} (freeModule k m)

private def matrixCoordinates (m : ℕ) (i : ℤ) :
    gradedEnd k m i ≃ₗ[k] zeroTerm (ModuleCat.of k (Matrix (Fin m) (Fin m) k)) i := by
  by_cases hi : i = 0
  · subst i
    exact (endEvaluation m).trans ((coordinates m).conj.trans
      (LinearMap.toMatrixAlgEquiv'.toLinearEquiv.trans
        (singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of k (Matrix (Fin m) (Fin m) k))).symm.toLinearEquiv))
  · letI := gradedEnd_subsingleton (k := k) m hi
    letI := subsingleton_zeroTerm (ModuleCat.of k (Matrix (Fin m) (Fin m) k)) hi
    exact LinearEquiv.ofSubsingleton _ _

private theorem matrixCoordinates_zero (m : ℕ) (f : gradedEnd k m 0) :
    matrixCoordinates m 0 f =
      writeZero (ModuleCat.of k (Matrix (Fin m) (Fin m) k)) 0
        (LinearMap.toMatrixAlgEquiv' ((coordinates m).conjAlgEquiv k (evaluation m f))) := by
  rw [writeZero_zero]
  unfold matrixCoordinates
  split
  · rfl
  · contradiction

private theorem evaluation_comp (m : ℕ) (f g : gradedEnd k m 0) :
    evaluation m (HomComplex.compose _ _ _ 0 0 0 rfl f g) =
      evaluation m f * evaluation m g := by
  apply LinearMap.ext
  intro x
  exact RightDGModule.compositionFormula 0 0 0 rfl f g point 0 0 0 rfl rfl x

set_option backward.isDefEq.respectTransparency false in
private def matrixComparison (m : ℕ) :
    DGFunctorModel (endCategory k m) (matrixCategory k m) where
  obj := id
  map a b := (Hom.isoOfComponents (fun i => (matrixCoordinates m i).toModuleIso)
    (by
      intro i j h
      have e : i + 1 = j := h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      by_cases hi : i = 0
      · exact (subsingleton_zeroTerm (ModuleCat.of k (Matrix (Fin m) (Fin m) k))
          (i := j) (by omega)).elim _ _
      · have hx : x = 0 := (gradedEnd_subsingleton (k := k) m hi).elim _ _
        rw [hx, map_zero, map_zero])).hom
  map_id a := by
    change matrixCoordinates m 0 (HomComplex.ofStrict (𝟙 (freeModule k m))) = writeZero _ 0 1
    rw [matrixCoordinates_zero]
    congr 1
    have h : evaluation m (HomComplex.ofStrict (𝟙 (freeModule k m))) = 1 := rfl
    rw [h, map_one, map_one]
  map_comp := by
    intro a b c i j n h f g
    change gradedEnd k m i at f
    change gradedEnd k m j at g
    change matrixCoordinates m n (HomComplex.compose _ _ _ i j n h f g) =
      zeroProduct (Matrix (Fin m) (Fin m) k) i j n (matrixCoordinates m i f) (matrixCoordinates m j g)
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · have hn : n = 0 := by omega
        subst i j n
        rw [zeroProduct_apply, matrixCoordinates_zero, matrixCoordinates_zero m f,
          matrixCoordinates_zero m g, read_write, read_write, evaluation_comp, map_mul, map_mul]
      · obtain rfl : g = 0 := (gradedEnd_subsingleton (k := k) m hj).elim _ _
        rw [map_zero, map_zero, map_zero, zeroProduct_zero_right]
    · obtain rfl : f = 0 := (gradedEnd_subsingleton (k := k) m hi).elim _ _
      rw [map_zero, LinearMap.zero_apply, map_zero, map_zero, zeroProduct_zero_left]

private theorem proveMatrixEndomorphisms : MatrixEndomorphisms.{u} := by
  intro k _ m _
  refine ⟨matrixComparison m, Function.bijective_id, ?_⟩
  intro a b
  dsimp [matrixComparison]
  infer_instance

section Generator

open RightDGModule (toHomotopyCategory directSumIsColimit IsKProjective
  nativeExistingDerivedCoproduct strictShift instCategoryK kProjectiveLocalizationEquivalence)
open Derived (HomotopyCategoryLaws)
open DerivedKProjective (derivedCategoryInstance)
open CompactRepresentables (IsCompact LocalizationMapAdditive coproductHomMap)
open DerivedCoproducts (derivedCofan)
open private representable_kProjective from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFreeKProjective
open private cellDerivedEquiv shiftZeroIso cofanProjection inj_projection_same inj_projection_ne
  coproductHomMap_injective coproductHomMap_surjective_of_iso coproductHomMap_of
  coproductHomMap_surjective_of_cover realizedSum_surjective nonzeroSummandsSmall
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactRepresentables
open private localizedAcyclicIsZero from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CompactGenerators
open scoped DirectSum

private abbrev family (k : Type u) [Field k] (m : ℕ) (_ : ULift.{u} (Fin m)) := regular k

private theorem free_kProjective (m : ℕ) : KProjective.isKProjective (freeModule k m) :=
  IsKProjective.coproduct _ (directSumIsColimit (family k m)) fun _ => representable_kProjective point

variable (h : HomotopyCategoryLaws (fieldCategory k))

local notation "D₀" => RightDGModule.D (fieldCategory k) h
local notation "Q₀" => RightDGModule.Q (fieldCategory k) h

local instance : Category (HomComplex.homotopyCategory (fieldCategory k)) := instCategoryK _

variable [S : Preadditive (RightDGModule.D (fieldCategory k) h)]

private theorem nativeRegularCompact (hadd : LocalizationMapAdditive h S) :
    CompactFiniteCells.CompactAt.{u,u,j,u} h S ((Q₀).obj (regular k)) := by
  classical
  intro I F c hc
  let P : D₀ := (Q₀).obj (regular k)
  let _ : Preadditive D₀ := S
  let F' : I → D₀ := F
  let c' : @Cofan I D₀ inferInstance F' := c
  have hc' : IsColimit c' := hc
  change Function.Bijective (coproductHomMap (C := D₀) P c')
  refine ⟨coproductHomMap_injective _ hc', ?_⟩
  let Jq := toHomotopyCategory (fieldCategory k) ⋙ Q₀
  apply coproductHomMap_surjective_of_iso c' (Jq.mapIso (shiftZeroIso (regular k)))
  letI : (Q₀).EssSurj := Localization.essSurj Q₀ (RightDGModule.quasiIsomorphisms (fieldCategory k))
  -- Only the nonzero summands require representatives in the coefficient universe.
  let E := kProjectiveLocalizationEquivalence.{u,u,u} (fieldCategory k) h
  letI : LocallySmall.{u} D₀ := locallySmall_of_faithful E.inverse
  let L := {i : I // ¬ IsZero (F' i)}
  letI : Small.{u} L := nonzeroSummandsSmall hc'
  let J := Shrink.{u} L
  let e : J ≃ L := (equivShrink L).symm
  let f (i : J) := (e i).val
  let M (i : J) := (Q₀).objPreimage (F' (f i))
  let b := DG.IndexedSums.nativeSum M
  obtain ⟨hd⟩ := nativeExistingDerivedCoproduct.{u,u,u,u} h b
  let d : @Cofan J D₀ inferInstance (fun i => (Q₀).obj (M i)) := derivedCofan h b
  have hd' : IsColimit d := hd
  refine coproductHomMap_surjective_of_cover _ hc' hd' f
    (fun i => (Q₀).objObjPreimageIso (F' (f i))) ?_
    (realizedSum_surjective.{u,u,u,u} h hadd point b)
  intro i hi
  exact ⟨e.symm ⟨i, hi⟩, congrArg Subtype.val (e.apply_symm_apply ⟨i, hi⟩)⟩

omit S in
private theorem finiteCoproductCompact {C : Type*} [Category C] [Preadditive C]
    {J : Type u} [Fintype J] {F : J → C} {d : Cofan F} (hd : IsColimit d)
    (hF : ∀ j, IsCompact.{j,_,_} (F j)) : IsCompact.{j,_,_} d.pt := by
  classical
  intro I X c hc
  refine ⟨coproductHomMap_injective _ hc, ?_⟩
  intro f
  choose x hx using fun j => (hF j c hc).surjective (d.inj j ≫ f)
  let p (j : J) : d.pt ⟶ F j := cofanProjection hd j
  let l (j : J) := DirectSum.map fun i => Preadditive.leftComp (X i) (p j)
  have hl (j : J) : (coproductHomMap d.pt c).comp (l j) =
      (Preadditive.leftComp c.pt (p j)).comp (coproductHomMap (F j) c) := by
    apply DirectSum.addHom_ext
    intro i g
    change coproductHomMap d.pt c (l j (DirectSum.of _ i g)) = p j ≫ coproductHomMap (F j) c (DirectSum.of _ i g)
    dsimp only [l]
    rw [DirectSum.map_of, coproductHomMap_of, coproductHomMap_of]
    exact Category.assoc _ _ _
  have he (j : J) : coproductHomMap d.pt c (l j (x j)) = p j ≫ d.inj j ≫ f := by
    exact (DFunLike.congr_fun (hl j) (x j)).trans (congrArg (p j ≫ ·) (hx j))
  refine ⟨∑ j, l j (x j), ?_⟩
  rw [map_sum]
  simp only [he]
  apply Cofan.IsColimit.hom_ext hd
  intro j
  rw [Preadditive.comp_sum, Finset.sum_eq_single j]
  · rw [← Category.assoc, inj_projection_same hd j, Category.id_comp]
  · intro l _ hlj
    rw [← Category.assoc, inj_projection_ne hd (Ne.symm hlj), zero_comp]
  · simp

private theorem free_compact (m : ℕ) (hadd : LocalizationMapAdditive h S) :
    CompactFiniteCells.CompactAt.{u,u,j,u} h S ((Q₀).obj (freeModule k m)) := by
  let b := DG.IndexedSums.nativeSum (family k m)
  obtain ⟨hd⟩ := nativeExistingDerivedCoproduct.{u,u,u,u} h b
  let d : @Cofan (ULift.{u} (Fin m)) D₀ inferInstance (fun _ => (Q₀).obj (regular k)) :=
    derivedCofan h b
  have hd' : IsColimit d := hd
  exact @finiteCoproductCompact D₀ inferInstance S _ _ _ d hd' (fun _ => @nativeRegularCompact _ _ h S hadd)

set_option backward.isDefEq.respectTransparency false in
private theorem free_detects (m : ℕ) (hm : 2 ≤ m) (hadd : LocalizationMapAdditive h S) :
    EndomorphismGenerator.ShiftedModuleDetectsZero (freeModule k m) h := by
  classical
  intro Y hy
  let i : ULift.{u} (Fin m) := ⟨⟨0, by omega⟩⟩
  let b := DG.IndexedSums.nativeSum (family k m)
  let p : freeModule k m ⟶ regular k := DG.IndexedSums.desc b
    (fun j => if j = i then 𝟙 (regular k) else 0)
  have hp : b.inclusion i ≫ p = 𝟙 (regular k) := by
    rw [DG.IndexedSums.inclusion_desc, ite_eq_left rfl]
  letI : (Q₀).EssSurj := Localization.essSurj Q₀ (RightDGModule.quasiIsomorphisms (fieldCategory k))
  let N := (Q₀).objPreimage Y
  let e := (Q₀).objObjPreimageIso Y
  have hN : Module.acyclic N := by
    intro a n
    cases a
    let T := strictShift (A := fieldCategory k) (-n) ⋙ toHomotopyCategory _ ⋙ Q₀
    let f := T.map (b.inclusion i)
    let g := T.map p
    have hfg : f ≫ g = 𝟙 _ := by rw [← T.map_comp, hp, T.map_id]
    have hsub : Subsingleton ((Q₀).obj (SemiFree.cell (A := fieldCategory k) point n) ⟶ (Q₀).obj N) :=
      ⟨fun x y => by
        have hh : (g ≫ x) ≫ e.hom = (g ≫ y) ≫ e.hom := (hy (-n)).elim _ _
        have hxy : g ≫ x = g ≫ y := (Iso.cancel_iso_hom_right _ _ e).mp hh
        have H := congrArg (f ≫ ·) hxy
        change f ≫ (g ≫ x) = f ≫ (g ≫ y) at H
        have H' : (f ≫ g) ≫ x = (f ≫ g) ≫ y := by
          rw [Category.assoc, Category.assoc]
          exact H
        rw [hfg, Category.id_comp, Category.id_comp] at H'
        exact H' ⟩
    apply (exactAt_iff_isZero_homology _ _).2
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact (cellDerivedEquiv.{u,u,u} point n N h hadd).toEquiv.subsingleton_congr.mp hsub
  have hz : IsZero ((Q₀).obj N) :=
    @localizedAcyclicIsZero.{u,u,u} k _ (fieldCategory k) h S hadd N hN
  exact hz.of_iso e.symm

private theorem proveFreeGenerator : FreeGenerator.{u,j} := by
  intro k _ m hm
  refine ⟨free_kProjective m, ?_⟩
  intro h S hadd
  exact ⟨@free_compact _ _ h S m hadd, @free_detects _ _ h S m hm hadd⟩

end Generator

section Zigzag

variable {A B : DGCategoryModel.{u,v,z} k}

private theorem h0_bijective (F : DGFunctorModel A B) (a b : A.Obj)
    (hq : QuasiIso (F.map a b)) :
    Function.Bijective ((DGFunctor.H0 F).map (X := a) (Y := b)) := by
  let S := Basic.zeroShort (A.hom a b)
  let T := Basic.zeroShort (B.hom (F.obj a) (F.obj b))
  let φ : S ⟶ T :=
    (shortComplexFunctor' (ModuleCat.{v} k) (ComplexShape.up ℤ) (-1) 0 1).map (F.map a b)
  let g := ShortComplex.leftHomologyMapData φ S.moduleCatLeftHomologyData T.moduleCatLeftHomologyData
  have hφ : ShortComplex.QuasiIso φ :=
    (quasiIsoAt_iff' (F.map a b) (-1) 0 1
      (ComplexShape.prev_eq' _ (show (-1 : ℤ) + 1 = 0 from rfl))
      (ComplexShape.next_eq' _ (show (0 : ℤ) + 1 = 1 from rfl))).mp inferInstance
  have hi : IsIso g.φH := g.quasiIso_iff.mp hφ
  have hmap : (DGFunctor.H0 F).map (X := a) (Y := b) = fun x => g.φH x := by
    funext x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (Basic.boundariesZero (A.hom a b)) x
    have hcycles : g.φK y = Basic.cycleMap F y := by
      apply Subtype.ext
      exact CategoryTheory.congr_fun g.commi y
    change Basic.h0Map F (Basic.classOf y) = g.φH (Basic.classOf y)
    rw [DGFunctor.h0Map_mk]
    exact ((CategoryTheory.congr_fun g.commπ y).trans (congrArg Basic.classOf hcycles)).symm
  rw [hmap]
  exact (ConcreteCategory.isIso_iff_bijective g.φH).mp hi

private def mapEndAlgebra (F : DGFunctorModel A B) (hF : DGFunctor.IsQuasiEquivalence F)
    (a : DGCategory.H0 A) : End a ≃ₐ[k] End ((DGFunctor.H0 F).obj a) := by
  let G := DGFunctor.H0 F
  let l : End a →ₗ[k] End (G.obj a) :=
    { toFun := G.mapEnd a
      map_add' := fun f g => End.ext (G.map_add (f := f.asHom) (g := g.asHom))
      map_smul' := fun c f => End.ext (G.map_smul c f.asHom) }
  have hl : Function.Bijective l :=
    (End.homEquiv.symm.bijective.comp (h0_bijective F a a (hF.1 a a))).comp End.homEquiv.bijective
  exact AlgEquiv.ofLinearEquiv (LinearEquiv.ofBijective l hl)
    (map_one (G.mapEnd a)) (map_mul (G.mapEnd a))

private def conjugateEnd {a b : DGCategory.H0 B} (e : a ≅ b) : End a ≃ₐ[k] End b := by
  let l : End a ≃ₗ[k] End b :=
    { toEquiv := e.conj.toEquiv
      map_add' := by
        intro f g
        apply End.ext
        simp [Preadditive.add_comp, Preadditive.comp_add]
      map_smul' := by
        intro r f
        apply End.ext
        simp [Linear.smul_comp, Linear.comp_smul] }
  exact AlgEquiv.ofLinearEquiv l (map_one e.conj) (map_mul e.conj)

private theorem zigzagEnd (h : QuasiEquivalenceZigzag A B) (a : DGCategory.H0 A) :
    ∃ b : DGCategory.H0 B, Nonempty (End a ≃ₐ[k] End b) := by
  induction h with
  | refl => exact ⟨a, ⟨AlgEquiv.refl⟩⟩
  | forward _ F hF ih =>
    obtain ⟨b, ⟨e⟩⟩ := ih
    exact ⟨F.obj b, ⟨e.trans (mapEndAlgebra F hF b)⟩⟩
  | backward _ F hF ih =>
    obtain ⟨b, ⟨e⟩⟩ := ih
    let G := DGFunctor.H0 F
    have hG : G.EssSurj := ((DGFunctor.isQuasiEquivalence_iff F).mp hF).2
    obtain ⟨c, ⟨s⟩⟩ := hG.mem_essImage b
    exact ⟨c, ⟨e.trans ((conjugateEnd s).symm.trans (mapEndAlgebra F hF c).symm)⟩⟩

private def degreeZeroEndEquiv (p : DGCategory.H0 A) (R : Type u) [Ring R] [Algebra k R]
    (e : R ≃ₗ[k] (A.hom p p).X 0)
    (dPrev : (A.hom p p).d (-1) 0 = 0) (dNext : (A.hom p p).d 0 1 = 0)
    (mapId : e 1 = A.id p)
    (mapComp : ∀ x y : R, e (x * y) = A.comp 0 0 0 rfl (e x) (e y)) :
    R ≃ₐ[k] End p := by
  let C := A.hom p p
  let l : R →ₗ[k] Basic.cyclesZero C :=
    e.toLinearMap.codRestrict _ (fun x => by
      change (A.hom p p).d 0 1 (e x) = 0
      rw [dNext]
      rfl)
  let m : R →ₗ[k] (p ⟶ p) := (Basic.boundariesZero C).mkQ.comp l
  have hb : Basic.boundariesZero C = ⊥ := by
    have h : (Basic.zeroShort C).moduleCatToCycles = 0 := by
      ext x
      change (A.hom p p).d (-1) 0 x = 0
      rw [dPrev]
      rfl
    rw [Basic.boundariesZero, h, LinearMap.range_zero]
  have hm : Function.Bijective m := by
    constructor
    · intro x y hxy
      have he : l x = l y := by
        change (Basic.boundariesZero C).mkQ (l x) = (Basic.boundariesZero C).mkQ (l y) at hxy
        exact (LinearMap.ker_eq_bot.mp (by rw [Submodule.ker_mkQ, hb])) hxy
      exact e.injective (congrArg (fun a : Basic.cyclesZero C => a.val) he)
    · intro y
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (Basic.boundariesZero C) y
      exact ⟨e.symm x.val, congrArg Basic.classOf (Subtype.ext (e.apply_symm_apply x.val))⟩
  let endEquiv := (LinearEquiv.ofBijective m hm).trans (End.linearEquiv (R := k)).symm
  refine AlgEquiv.ofLinearEquiv endEquiv ?_ ?_
  · apply End.ext
    change Basic.classOf (l 1) = Basic.classOf (Basic.cycleId A p)
    exact congrArg Basic.classOf (Subtype.ext mapId)
  · intro x y
    apply End.ext
    change Basic.classOf (l (x * y)) = Basic.h0Comp A (Basic.classOf (l x)) (Basic.classOf (l y))
    rw [DGCategory.h0Comp_mk]
    exact congrArg Basic.classOf (Subtype.ext (mapComp x y))

private abbrev algebraPoint (R : Type u) [Ring R] [Algebra k R] :
    DGCategory.H0 (algebraCategory.{u,z} (k := k) R) := PUnit.unit

private abbrev liftedAlgebraPoint (R : Type u) [Ring R] [Algebra k R] :
    DGCategory.H0 (liftedAlgebraCategory.{u,v,z} (k := k) R) := PUnit.unit

private def algebraToEnd (R : Type u) [Ring R] [Algebra k R] :
    R ≃ₐ[k] End (algebraPoint (k := k) R) := by
  let e := (singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of k R)).toLinearEquiv.symm
  refine degreeZeroEndEquiv (algebraPoint R) R e rfl rfl rfl ?_
  intro x y
  change writeZero _ 0 (x * y) = zeroProduct R 0 0 0 (writeZero _ 0 x) (writeZero _ 0 y)
  simp

private def liftedAlgebraToEnd (R : Type u) [Ring R] [Algebra k R] :
    R ≃ₐ[k] End (liftedAlgebraPoint (k := k) R) := by
  let e := (singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of k R)).toLinearEquiv.symm
  refine degreeZeroEndEquiv (liftedAlgebraPoint R) R (e.trans ULift.moduleEquiv.symm) rfl rfl rfl ?_
  intro x y
  change ULift.up (writeZero _ 0 (x * y)) =
    ULift.up (zeroProduct R 0 0 0 (writeZero _ 0 x) (writeZero _ 0 y))
  exact congrArg ULift.up (by simp)

private theorem noZigzagOfMatrixEnds {m : ℕ} (hm : 2 ≤ m)
    {a : DGCategory.H0 A} {b : DGCategory.H0 B}
    (fieldEnd : k ≃ₐ[k] End a) (matrixEnd : Matrix (Fin m) (Fin m) k ≃ₐ[k] End b)
    (hB : Subsingleton (DGCategory.H0 B)) :
    ¬ QuasiEquivalenceZigzag A B := by
  intro h
  obtain ⟨c, ⟨e⟩⟩ := zigzagEnd h a
  obtain rfl : c = b := hB.elim _ _
  have hd := ((fieldEnd.trans e).trans matrixEnd.symm).toLinearEquiv.finrank_eq
  rw [Module.finrank_self, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at hd
  nlinarith

/-- The endomorphism dimensions obstruct a zigzag at every common Hom bound. -/
theorem noQuasiEquivalenceZigzag : NoQuasiEquivalenceZigzag.{u,v,z} := by
  intro k _ m hm
  have hP : Subsingleton PUnit.{z+1} := inferInstance
  exact ⟨noZigzagOfMatrixEnds hm (algebraToEnd k) (algebraToEnd _) hP,
    noZigzagOfMatrixEnds hm (liftedAlgebraToEnd k) (liftedAlgebraToEnd _) hP⟩

end Zigzag

section Localization

open CoefficientLiftComparison (restrictModule restrictMap)
open RightDGModule (K D Q homotopyClass_surjective quasiIsomorphisms_homotopyClass
  toHomotopyCategory)
open DerivedKProjective (derivedCategoryInstance)
open Derived (HomotopyCategoryLaws)
open private quasiIsomorphisms_eq_trW from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedTriangles

@[reducible] private def restrictGraded {A B : DGCategoryModel.{u,u,u} k} (F : DGFunctorModel A B)
    {M N : RightDGModuleModel B} {r : ℤ} (f : GradedHom M N r) :
    GradedHom (restrictModule F M) (restrictModule F N) r :=
  ⟨fun a => f.val (F.obj a), by
    intro a b i j n ir nr h hi hn x z
    exact f.comm_act i j n ir nr h hi hn x ((F.map a b).f j z)⟩

@[reducible] private def restrictionDG {A B : DGCategoryModel.{u,u,u} k} (F : DGFunctorModel A B) :
    DGFunctorModel (HomComplex.dgModuleCategory B) (HomComplex.dgModuleCategory A) where
  obj := restrictModule F
  map _ _ :=
    { f := fun _ => ModuleCat.ofHom
        { toFun := restrictGraded F
          map_add' := fun _ _ => Subtype.ext rfl
          map_smul' := fun _ _ => Subtype.ext rfl }
      comm' := fun _ _ _ => ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext rfl) }
  map_id _ := Subtype.ext rfl
  map_comp _ _ _ _ _ _ := Subtype.ext rfl

private def matrixRestriction (m : ℕ) :
    K (matrixCategory k m) ⥤ K (endCategory k m) :=
  DGFunctor.H0 (restrictionDG (matrixComparison m))

private theorem matrixRestriction_map {m : ℕ} {M N : RightDGModuleModel (matrixCategory k m)}
    (f : M ⟶ N) :
    (matrixRestriction m).map (HomComplex.homotopyClass f) =
      HomComplex.homotopyClass (restrictMap (matrixComparison m) f) := by
  change Basic.h0Map (restrictionDG (matrixComparison m)) (Basic.classOf (HomComplex.strictCycle f)) =
    Basic.classOf (HomComplex.strictCycle (restrictMap (matrixComparison m) f))
  rw [DGFunctor.h0Map_mk]
  exact congrArg Basic.classOf (Subtype.ext (Subtype.ext rfl))

set_option backward.isDefEq.respectTransparency false in
private theorem matrixRestriction_bijective (m : ℕ) (M N : K (matrixCategory k m)) :
    Function.Bijective ((matrixRestriction m).map (X := M) (Y := N)) := by
  apply h0_bijective
  let F := restrictionDG (matrixComparison (k := k) m)
  suffices ∀ r, IsIso ((F.map M N).f r) by
    letI := this
    haveI : IsIso (F.map M N) := Hom.isIso_of_components _
    infer_instance
  intro r
  apply (ConcreteCategory.isIso_iff_bijective _).2
  change Function.Bijective (restrictGraded (matrixComparison m) (M := M) (N := N) (r := r))
  constructor
  · intro f g h
    apply Subtype.ext
    have H := congrArg (fun g : GradedHom (restrictModule (matrixComparison m) M)
      (restrictModule (matrixComparison m) N) r => g.val) h
    exact H
  · intro f
    refine ⟨⟨f.val, ?_⟩, Subtype.ext rfl⟩
    intro a b i j n ir nr h hi hn x z
    let z' := (matrixCoordinates m j).symm z
    have hz : ((matrixComparison m).map a b).f j z' = z :=
      (matrixCoordinates m j).apply_symm_apply z
    have hf := f.comm_act (a := a) (b := b) i j n ir nr h hi hn x z'
    change (f.val a).v n nr hn (M.act i j n h x (((matrixComparison m).map a b).f j z')) =
      N.act ir j nr _ ((f.val b).v i ir hi x) (((matrixComparison m).map a b).f j z') at hf
    rwa [hz] at hf

set_option backward.isDefEq.respectTransparency false in
private def matrixComparisonInverse (m : ℕ) :
    DGFunctorModel (matrixCategory k m) (endCategory k m) where
  obj := id
  map a b :=
    let F := (matrixComparison m).map a b
    haveI : IsIso F := by dsimp [F, matrixComparison]; infer_instance
    inv F
  map_id a := by
    let F := matrixComparison (k := k) m
    haveI : IsIso (F.map a a) := by dsimp [F, matrixComparison]; infer_instance
    apply (matrixCoordinates m 0).injective
    change (F.map a a).f 0 ((inv (F.map a a)).f 0 ((matrixCategory k m).id a)) =
      (F.map a a).f 0 ((endCategory k m).id a)
    rw [F.map_id]
    exact CategoryTheory.congr_fun (congrArg (fun f => f.f 0) (IsIso.inv_hom_id (F.map a a))) _
  map_comp := by
    intro a b c i j n h x y
    let F := matrixComparison (k := k) m
    letI : ∀ a b, IsIso (F.map a b) := fun a b => by dsimp [F, matrixComparison]; infer_instance
    have hinv (a b : (endCategory k m).Obj) (r : ℤ) (z : ((matrixCategory k m).hom a b).X r) :
        (F.map a b).f r ((inv (F.map a b)).f r z) = z :=
      CategoryTheory.congr_fun (congrArg (fun f => f.f r) (IsIso.inv_hom_id (F.map a b))) z
    apply (matrixCoordinates m n).injective
    change (F.map a c).f n ((inv (F.map a c)).f n _) =
      (F.map a c).f n ((endCategory k m).comp i j n h ((inv (F.map b c)).f i x) ((inv (F.map a b)).f j y))
    rw [F.map_comp, hinv, hinv, hinv]

private theorem matrixRestriction_essSurj (m : ℕ) :
    (matrixRestriction (k := k) m).EssSurj := by
  constructor
  intro M
  let F := matrixComparison (k := k) m
  let N := restrictModule (matrixComparisonInverse m) M
  refine ⟨N, ⟨(toHomotopyCategory _).mapIso (?_ : restrictModule F N ≅ M)⟩⟩
  refine DG.CoefficientLift.isoOfComponents (fun _ _ => LinearEquiv.refl k _) (by intros; rfl) ?_
  intro a b i j n h x z
  haveI : IsIso (F.map a b) := by dsimp [F, matrixComparison]; infer_instance
  have hz : (inv (F.map a b)).f j ((F.map a b).f j z) = z :=
    CategoryTheory.congr_fun (congrArg (fun f => f.f j) (IsIso.hom_inv_id (F.map a b))) z
  change M.act i j n h x ((inv (F.map a b)).f j ((F.map a b).f j z)) = M.act i j n h x z
  rw [hz]

private theorem matrixRestriction_quasiIso (m : ℕ)
    {M N : K (matrixCategory k m)} (f : M ⟶ N) :
    Derived.quasiIsomorphisms (endCategory k m) ((matrixRestriction m).map f) ↔
      Derived.quasiIsomorphisms (matrixCategory k m) f := by
  obtain ⟨g, rfl⟩ := homotopyClass_surjective f
  rw [matrixRestriction_map]
  exact (quasiIsomorphisms_homotopyClass (restrictMap (matrixComparison m) g)).trans
    (quasiIsomorphisms_homotopyClass g).symm

private def matrixLocalizer (m : ℕ) :
    LocalizerMorphism (RightDGModule.quasiIsomorphisms (matrixCategory k m))
      (RightDGModule.quasiIsomorphisms (endCategory k m)) :=
  ⟨matrixRestriction m, fun _ _ f hf => (matrixRestriction_quasiIso m f).2 hf⟩

private theorem matrixLocalizer_isLocalizedEquivalence (m : ℕ) :
    (matrixLocalizer (k := k) m).IsLocalizedEquivalence := by
  let L := matrixLocalizer (k := k) m
  letI : L.functor.IsEquivalence :=
    { faithful := ⟨fun {M N} => (matrixRestriction_bijective m M N).1⟩
      full := ⟨fun {M N} => (matrixRestriction_bijective m M N).2⟩
      essSurj := matrixRestriction_essSurj m }
  letI : (RightDGModule.quasiIsomorphisms (endCategory k m)).RespectsIso := by
    rw [quasiIsomorphisms_eq_trW]
    infer_instance
  letI : L.IsInduced := ⟨by
    ext X Y f
    exact matrixRestriction_quasiIso m f⟩
  exact L.isLocalizedEquivalence_of_isInduced

end Localization

section Ordinary

open MulOpposite

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open private act_assoc_at from MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.ShiftCone

variable {k : Type u} [Field k] {R : Type u} [Ring R] [Algebra k R]
private abbrev degreeZeroCategory (k : Type u) [Field k] (R : Type u) [Ring R] [Algebra k R] :=
  algebraCategory.{u,u} (k := k) R
private abbrev ordinaryPoint : (degreeZeroCategory k R).Obj := PUnit.unit

private abbrev underlying (M : RightDGModuleModel (degreeZeroCategory k R)) (i : ℤ) :=
  (M.complex ordinaryPoint).X i

private def scalarAction (M : RightDGModuleModel (degreeZeroCategory k R)) (i : ℤ)
    (r : Rᵐᵒᵖ) (x : underlying M i) : underlying M i :=
  M.act (a := ordinaryPoint) (b := ordinaryPoint) i 0 i (add_zero i) x
    (writeZero (ModuleCat.of k R) 0 r.unop)

set_option backward.isDefEq.respectTransparency false in
@[instance_reducible] private def moduleOfAction (M : RightDGModuleModel (degreeZeroCategory k R)) (i : ℤ) :
    Module Rᵐᵒᵖ (underlying M i) := by
  refine
    { smul := scalarAction M i
      one_smul := fun x => M.act_id ordinaryPoint i x
      mul_smul := ?_
      smul_zero := ?_
      smul_add := ?_
      add_smul := ?_
      zero_smul := ?_ }
  · intro r s x
    change scalarAction M i (r*s) x = scalarAction M i r (scalarAction M i s x)
    unfold scalarAction
    have h := act_assoc_at M (a := ordinaryPoint) (b := ordinaryPoint) (c := ordinaryPoint)
      i 0 0 i 0 i (add_zero i) rfl (add_zero i) x
      (writeZero (ModuleCat.of k R) 0 s.unop) (writeZero (ModuleCat.of k R) 0 r.unop)
    change _ = M.act i 0 i _ x
      (zeroProduct R 0 0 0 (writeZero (ModuleCat.of k R) 0 s.unop)
        (writeZero (ModuleCat.of k R) 0 r.unop)) at h
    rw [zeroProduct_apply, read_write, read_write] at h
    exact h.symm
  · intro r
    change scalarAction M i r 0 = 0
    unfold scalarAction
    rw [map_zero, LinearMap.zero_apply]
  · intro r x y
    change scalarAction M i r (x+y) = scalarAction M i r x + scalarAction M i r y
    unfold scalarAction
    rw [map_add, LinearMap.add_apply]
  · intro r s x
    change scalarAction M i (r+s) x = scalarAction M i r x + scalarAction M i s x
    unfold scalarAction
    rw [MulOpposite.unop_add, map_add, map_add]
  · intro x
    change scalarAction M i 0 x = 0
    unfold scalarAction
    rw [MulOpposite.unop_zero, map_zero, map_zero]

private theorem scalarAction_algebraMap (M : RightDGModuleModel (degreeZeroCategory k R))
    (i : ℤ) (c : k) (x : underlying M i) :
    scalarAction M i (algebraMap k Rᵐᵒᵖ c) x = c • x := by
  unfold scalarAction
  have e : (algebraMap k Rᵐᵒᵖ c).unop = c • (1 : R) := by
    rw [Algebra.algebraMap_eq_smul_one]
    rfl
  rw [e, map_smul, map_smul]
  exact congrArg (c • ·) (M.act_id ordinaryPoint i x)

@[reducible] private def moduleOfDegree (M : RightDGModuleModel (degreeZeroCategory k R)) (i : ℤ) :
    ModuleCat.{u} Rᵐᵒᵖ :=
  letI := moduleOfAction M i
  ModuleCat.of Rᵐᵒᵖ (underlying M i)

private theorem scalarAction_d (M : RightDGModuleModel (degreeZeroCategory k R))
    (i j : ℤ) (r : Rᵐᵒᵖ) (x : underlying M i) :
    (M.complex ordinaryPoint).d i j (scalarAction M i r x) =
      scalarAction M j r ((M.complex ordinaryPoint).d i j x) := by
  by_cases h : i + 1 = j
  · subst j
    unfold scalarAction
    rw [M.leibniz i 0 i (add_zero i)]
    have hz : ((degreeZeroCategory k R).hom ordinaryPoint ordinaryPoint).d 0 (0+1)
      (writeZero (ModuleCat.of k R) 0 r.unop) = 0 := rfl
    rw [hz, map_zero, smul_zero, add_zero]
  · rw [(M.complex _).shape i j h]
    change (0 : (M.complex ordinaryPoint).X i ⟶ (M.complex ordinaryPoint).X j) _ =
      scalarAction M j r 0
    unfold scalarAction
    rw [map_zero, LinearMap.zero_apply]
    rfl

private def complexOfAction (M : RightDGModuleModel (degreeZeroCategory k R)) :
    CochainComplex (ModuleCat.{u} Rᵐᵒᵖ) ℤ where
  X := moduleOfDegree M
  d i j := by
    letI := moduleOfAction M i
    letI := moduleOfAction M j
    exact ModuleCat.ofHom
      { toFun := fun x => (M.complex ordinaryPoint).d i j x
        map_add' := map_add _
        map_smul' := scalarAction_d M i j }
  shape i j h := ModuleCat.hom_ext (LinearMap.ext fun x => by
    change (M.complex ordinaryPoint).d i j x = 0
    rw [(M.complex ordinaryPoint).shape i j h]
    rfl)
  d_comp_d' i j n _ _ := ModuleCat.hom_ext (LinearMap.ext fun x => by
    exact CategoryTheory.congr_fun ((M.complex ordinaryPoint).d_comp_d i j n) x)

private abbrev scalarRestriction (k : Type u) [Field k] (R : Type u) [Ring R] [Algebra k R] :
    ModuleCat.{u} Rᵐᵒᵖ ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (algebraMap k Rᵐᵒᵖ)

private abbrev OrdinaryComplex (R : Type u) [Ring R] := CochainComplex (ModuleCat.{u} Rᵐᵒᵖ) ℤ

private abbrev underlyingComplex (C : OrdinaryComplex R) :=
  ((scalarRestriction k R).mapHomologicalComplex (ComplexShape.up ℤ)).obj C

private def rightScalar (V : ModuleCat.{u} Rᵐᵒᵖ) :
    (scalarRestriction k R).obj V →ₗ[k] R →ₗ[k] (scalarRestriction k R).obj V where
  toFun x :=
    { toFun := fun r => op r • x
      map_add' := fun r s => add_smul (op r) (op s) x
      map_smul' := fun c r => by
        change op (c • r) • x = (algebraMap k Rᵐᵒᵖ c) • (op r • x)
        rw [← mul_smul, Algebra.smul_def]
        exact congrArg (fun r : Rᵐᵒᵖ => r • x) (by
          change op (algebraMap k R c * r) = op (r * algebraMap k R c)
          rw [Algebra.commutes]) }
  map_add' x y := LinearMap.ext fun r => smul_add (op r) x y
  map_smul' c x := LinearMap.ext fun r => by
    change op r • ((algebraMap k Rᵐᵒᵖ c) • x) = (algebraMap k Rᵐᵒᵖ c) • (op r • x)
    rw [← mul_smul, ← mul_smul, Algebra.commutes]

private def complexAction (C : OrdinaryComplex R) (i j n : ℤ) (h : i+j=n) :
    (underlyingComplex (k := k) C).X i →ₗ[k] zeroTerm (ModuleCat.of k R) j →ₗ[k]
      (underlyingComplex (k := k) C).X n :=
  if hj : j = 0 then
    let t : i = n := by omega
    LinearMap.compr₂
      (LinearMap.compl₂ (rightScalar (C.X i)) (readZero (ModuleCat.of k R) j).hom)
        (((scalarRestriction k R).map (C.XIsoOfEq t).hom).hom)
  else 0

private theorem complexAction_atZero (C : OrdinaryComplex R) (i : ℤ)
    (x : (underlyingComplex (k := k) C).X i)
    (z : zeroTerm (ModuleCat.of k R) 0) :
    complexAction C i 0 i (add_zero i) x z = SMul.smul (M := Rᵐᵒᵖ) (α := C.X i) (op (readZero (ModuleCat.of k R) 0 z : R)) x := by
  unfold complexAction
  rw [dite_eq_left rfl]
  rfl

private theorem complexAction_assoc (C : OrdinaryComplex R)
    (i j l p q n : ℤ) (hp : i+j=p) (hq : j+l=q) (hn : p+l=n)
    (x : (underlyingComplex (k := k) C).X i)
    (y : zeroTerm (ModuleCat.of k R) j) (z : zeroTerm (ModuleCat.of k R) l) :
    complexAction C p l n hn (complexAction C i j p hp x y) z =
      complexAction C i q n (by omega) x (zeroProduct R j l q y z) := by
  by_cases hj : j = 0
  · by_cases hl : l = 0
    · subst j l
      have e₁ : p = i := by omega
      have e₂ : q = 0 := by omega
      have e₃ : n = i := by omega
      cases e₁; cases e₂; cases e₃
      rw [complexAction_atZero (k := k) (R := R), complexAction_atZero (k := k) (R := R), complexAction_atZero (k := k) (R := R),
        zeroProduct_apply (k := k) R, read_write (ModuleCat.of k R)]
      let x' : C.X i := x
      have he := mul_smul (op (readZero (ModuleCat.of k R) 0 z : R))
        (op (readZero (ModuleCat.of k R) 0 y : R)) x'
      exact he.symm
    · have hz : z = 0 := (subsingleton_zeroTerm (ModuleCat.of k R) hl).elim _ _
      rw [hz, map_zero, zeroProduct_zero_right, map_zero]
  · have hy : y = 0 := (subsingleton_zeroTerm (ModuleCat.of k R) hj).elim _ _
    rw [hy, map_zero, map_zero, LinearMap.zero_apply, zeroProduct_zero_left, map_zero]

set_option backward.isDefEq.respectTransparency false in
@[reducible] private def moduleOfComplex (C : OrdinaryComplex R) : RightDGModuleModel (degreeZeroCategory k R) where
  complex _ := underlyingComplex C
  act := complexAction C
  act_id _ i x := by
    change complexAction C i 0 i (add_zero i) x (writeZero (ModuleCat.of k R) 0 1) = x
    rw [complexAction_atZero, read_write]
    let x' : C.X i := x
    have he := one_smul (Rᵐᵒᵖ) x'
    exact he
  act_assoc _ _ _ x y z := complexAction_assoc C _ _ _ _ _ _ rfl rfl rfl x y z
  leibniz := by
    intro a b i j n h x z
    have hz : ((degreeZeroCategory k R).hom a b).d j (j+1) z = 0 := rfl
    rw [hz, map_zero, smul_zero, add_zero]
    by_cases hj : j = 0
    · subst j
      have hn : n = i := by omega
      cases hn
      change (underlyingComplex (k := k) C).d i (i+1) (complexAction C _ _ _ _ x z) =
        complexAction C _ _ _ _ ((underlyingComplex (k := k) C).d i (i+1) x) z
      rw [complexAction_atZero, complexAction_atZero]
      exact ((C.d i (i+1)).hom.map_smul (op (readZero (ModuleCat.of k R) 0 z)) (x : C.X i))
    · have hz : z = 0 := (subsingleton_zeroTerm (ModuleCat.of k R) hj).elim _ _
      rw [hz, map_zero, map_zero, map_zero]

private theorem complexCochain_comm {C D : OrdinaryComplex R}
    (s : ℤ) (f : CochainComplex.HomComplex.Cochain C D s) {a b : (degreeZeroCategory k R).Obj}
    (i j n ir nr : ℤ) (h : i+j=n) (hi : i+s=ir) (hn : n+s=nr)
    (x : ((moduleOfComplex (k := k) C).complex b).X i) (z : ((degreeZeroCategory k R).hom a b).X j) :
    ((scalarRestriction k R).map (f.v n nr hn)) ((moduleOfComplex (k := k) C).act i j n h x z) =
      (moduleOfComplex (k := k) D).act ir j nr (by omega)
        (((scalarRestriction k R).map (f.v i ir hi)) x) z := by
  by_cases hj : j = 0
  · subst j
    have eq₁ : n = i := by omega
    have eq₂ : nr = ir := by omega
    cases eq₁; cases eq₂
    change ((scalarRestriction k R).map (f.v i ir hi)) (complexAction C i 0 i (add_zero i) x z) =
      complexAction D ir 0 ir (add_zero ir) (((scalarRestriction k R).map (f.v i ir hi)) x) z
    rw [complexAction_atZero, complexAction_atZero]
    exact ((f.v i ir hi).hom.map_smul (op (readZero (ModuleCat.of k R) 0 z)) (x : C.X i))
  · have hz : z = 0 := (subsingleton_zeroTerm (ModuleCat.of k R) hj).elim _ _
    rw [hz, map_zero, map_zero, map_zero]

open CochainComplex.HomComplex
open _root_.DerivedFormalization.RightDGModule (GradedHom K D Q toHomotopyCategory)

private def moduleMapOfChainMap {C D : OrdinaryComplex R} (f : C ⟶ D) :
    moduleOfComplex (k := k) C ⟶ moduleOfComplex (k := k) D where
  app _ := ((scalarRestriction k R).mapHomologicalComplex (ComplexShape.up ℤ)).map f
  comm_act := by
    intro a b i j n h x z
    have h' := complexCochain_comm (k := k) 0 (Cochain.ofHom f) (a := a) (b := b)
      i j n i n h (add_zero i) (add_zero n) x z
    rw [Cochain.ofHom_v, Cochain.ofHom_v] at h'
    exact h'

private def complexToDGModules : OrdinaryComplex R ⥤ RightDGModuleModel (degreeZeroCategory k R) where
  obj := moduleOfComplex
  map := moduleMapOfChainMap
  map_id _ := RightDGModuleModel.hom_ext (fun _ => rfl)
  map_comp _ _ := RightDGModuleModel.hom_ext (fun _ => rfl)

private def gradedMapOfCochain {C D : OrdinaryComplex R} {s : ℤ} (f : Cochain C D s) :
    GradedHom (moduleOfComplex (k := k) C) (moduleOfComplex (k := k) D) s :=
  GradedHom.mk (fun _ _ _ h => (scalarRestriction k R).map (f.v _ _ h))
    (complexCochain_comm (k := k) s f)

private def linearComponentOfGradedMap {C D : OrdinaryComplex R} {s : ℤ}
    (g : GradedHom (moduleOfComplex (k := k) C) (moduleOfComplex (k := k) D) s)
    (i j : ℤ) (h : i+s=j) : C.X i ⟶ D.X j :=
  ModuleCat.ofHom
    { toFun := fun x => g.app ordinaryPoint i j h x
      map_add' := (g.app ordinaryPoint i j h).hom.map_add
      map_smul' := fun r x => by
        have hh := g.comm_act (a := ordinaryPoint) (b := ordinaryPoint) i 0 i j j
          (add_zero i) h h x (writeZero (ModuleCat.of k R) 0 r.unop)
        change g.app ordinaryPoint i j h
            (complexAction C i 0 i (add_zero i) x (writeZero (ModuleCat.of k R) 0 r.unop)) =
          complexAction D j 0 j (add_zero j) (g.app ordinaryPoint i j h x)
            (writeZero (ModuleCat.of k R) 0 r.unop) at hh
        rw [complexAction_atZero, complexAction_atZero, read_write, op_unop] at hh
        exact hh }

private def cochainOfGradedMap {C D : OrdinaryComplex R} {s : ℤ}
    (g : GradedHom (moduleOfComplex (k := k) C) (moduleOfComplex (k := k) D) s) :
    Cochain C D s :=
  Cochain.mk (linearComponentOfGradedMap g)

private def chainMapOfModuleMap {C D : OrdinaryComplex R}
    (g : moduleOfComplex (k := k) C ⟶ moduleOfComplex (k := k) D) : C ⟶ D where
  f i := linearComponentOfGradedMap (HomComplex.ofStrict g) i i (add_zero i)
  comm' i j _ := ModuleCat.hom_ext (LinearMap.ext fun x =>
    CategoryTheory.congr_fun ((g.app ordinaryPoint).comm i j) x)

private theorem moduleMapOfChainMap_chainMapOfModuleMap {C D : OrdinaryComplex R}
    (g : moduleOfComplex (k := k) C ⟶ moduleOfComplex (k := k) D) :
    moduleMapOfChainMap (chainMapOfModuleMap g) = g := by
  apply RightDGModuleModel.hom_ext
  intro a
  cases a
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

private def moduleOfComplexOfActionIso (M : RightDGModuleModel (degreeZeroCategory k R)) :
    moduleOfComplex (k := k) (complexOfAction M) ≅ M := by
  refine DG.CoefficientLift.isoOfComponents (fun a i => ?_) ?_ ?_
  · cases a
    refine { toEquiv := Equiv.refl _, map_add' := fun _ _ => rfl, map_smul' := ?_ }
    intro c x
    exact scalarAction_algebraMap M i c x
  · intro a i x
    cases a
    rfl
  · intro a b i j n h x z
    cases a; cases b
    change complexAction (complexOfAction M) i j n h x z =
      M.act (a := ordinaryPoint) (b := ordinaryPoint) i j n h x z
    by_cases hj : j = 0
    · subst j
      have hn : n = i := by omega
      cases hn
      rw [complexAction_atZero]
      change M.act (a := ordinaryPoint) (b := ordinaryPoint) i 0 i (add_zero i) x
          (writeZero (ModuleCat.of k R) 0 (readZero (ModuleCat.of k R) 0 z)) = _
      rw [write_read]
    · have hz : z = 0 := (subsingleton_zeroTerm (ModuleCat.of k R) hj).elim _ _
      rw [hz, map_zero, map_zero]

private theorem ordinaryBoundary {C D : OrdinaryComplex R}
    (a : Cochain C D (-1)) (i : ℤ) (x : C.X i) :
    (δ (-1) 0 a).v i i (add_zero i) x =
      D.d (i-1) i (a.v i (i-1) (by omega) x) + a.v (i+1) i (by omega) (C.d i (i+1) x) := by
  rw [δ_v (-1) 0 (by decide) _ i i (add_zero i) (i-1) (i+1) rfl rfl]
  simp only [Int.negOnePow_zero, one_smul, ModuleCat.hom_add, LinearMap.add_apply,
    ModuleCat.comp_apply]

private theorem complexToDGModules_homotopy_iff {C D : OrdinaryComplex R} (f g : C ⟶ D) :
    RightDGModule.homotopyClass (moduleMapOfChainMap (k := k) f) =
      RightDGModule.homotopyClass (moduleMapOfChainMap (k := k) g) ↔ Nonempty (Homotopy f g) := by
  rw [RightDGModule.homotopyCriterion]
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨(Cochain.equivHomotopy f g).symm ⟨cochainOfGradedMap h, ?_⟩⟩
    apply Cochain.ext
    intro i j hij
    have hj : j = i := by omega
    cases hj
    rw [Cochain.ofHom_v, Cochain.add_v, Cochain.ofHom_v]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change f.f i x = (δ (-1) 0 (cochainOfGradedMap h)).v i i (add_zero i) x + g.f i x
    rw [ordinaryBoundary]
    exact sub_eq_iff_eq_add.mp (hh ordinaryPoint i x)
  · rintro ⟨h⟩
    let a := (Cochain.equivHomotopy f g h).val
    refine ⟨gradedMapOfCochain (k := k) a, ?_⟩
    intro p i x
    cases p
    have eq := CategoryTheory.congr_fun
      (Cochain.congr_v ((Cochain.equivHomotopy f g h).property) i i (add_zero i)) (x : C.X i)
    simp only [Cochain.ofHom_v, Cochain.add_v, ModuleCat.hom_add, LinearMap.add_apply] at eq
    change f.f i x = (δ (-1) 0 a).v i i (add_zero i) x + g.f i x at eq
    rw [ordinaryBoundary] at eq
    exact sub_eq_iff_eq_add.mpr eq

/-- The usual homotopy category of cochains of right `R`-modules. -/
private abbrev ordinaryHomotopy (R : Type u) [Ring R] :=
  HomotopyCategory (ModuleCat.{u} Rᵐᵒᵖ) (ComplexShape.up ℤ)

private abbrev qOrd (R : Type u) [Ring R] :=
  HomotopyCategory.quotient (ModuleCat.{u} Rᵐᵒᵖ) (ComplexShape.up ℤ)

private def homotopyFromComplexes : ordinaryHomotopy R ⥤ K (degreeZeroCategory k R) :=
  CategoryTheory.Quotient.lift (_root_.homotopic _ _)
    (complexToDGModules ⋙ toHomotopyCategory (degreeZeroCategory k R))
    (fun _ _ f g h => (complexToDGModules_homotopy_iff (k := k) f g).2 h)

@[simp] private theorem homotopyFromComplexes_map {C D : OrdinaryComplex R} (f : C ⟶ D) :
    (homotopyFromComplexes (k := k) (R := R)).map ((qOrd R).map f) =
      RightDGModule.homotopyClass (moduleMapOfChainMap (k := k) f) := rfl

private theorem homotopyFromComplexes_equivalence : (homotopyFromComplexes (k := k) (R := R)).IsEquivalence := by
  constructor
  · constructor
    intro C D x y h
    obtain ⟨f, rfl⟩ := (qOrd R).map_surjective x
    obtain ⟨g, rfl⟩ := (qOrd R).map_surjective y
    obtain ⟨s⟩ := (complexToDGModules_homotopy_iff (k := k) f g).1 h
    exact HomotopyCategory.eq_of_homotopy _ _ s
  · constructor
    intro C D x
    obtain ⟨f, rfl⟩ := RightDGModule.homotopyClass_surjective x
    refine ⟨(qOrd R).map (chainMapOfModuleMap f), ?_⟩
    rw [homotopyFromComplexes_map, moduleMapOfChainMap_chainMapOfModuleMap]
  · constructor
    intro M
    exact ⟨(qOrd R).obj (complexOfAction M),
      ⟨(toHomotopyCategory _).mapIso (moduleOfComplexOfActionIso M)⟩⟩

private theorem homotopyFromComplexes_quasiIso {C D : ordinaryHomotopy R} (f : C ⟶ D) :
    RightDGModule.quasiIsomorphisms (degreeZeroCategory k R) ((homotopyFromComplexes (k := k)).map f) ↔
      HomotopyCategory.quasiIso _ _ f := by
  obtain ⟨g, rfl⟩ := (qOrd R).map_surjective f
  rw [homotopyFromComplexes_map, RightDGModule.quasiIsomorphisms_homotopyClass,
    HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
  letI : PreservesFiniteLimits (scalarRestriction k R) := ⟨by
    intro J _ _
    exact ⟨fun {F} => ModuleCat.preservesLimit_restrictScalars _ F⟩⟩
  letI : PreservesFiniteColimits (scalarRestriction k R) := ⟨by
    intro J _ _
    exact ⟨fun {F} => ModuleCat.preservesColimit_restrictScalars _ F⟩⟩
  constructor
  · intro h
    exact (quasiIso_map_iff_of_preservesHomology g (scalarRestriction k R)).1 (h ordinaryPoint)
  · intro h a
    exact (quasiIso_map_iff_of_preservesHomology g (scalarRestriction k R)).2 h

open private quasiIsomorphisms_eq_trW from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedTriangles

private abbrev ordinaryDerived (R : Type u) [Ring R] :=
  (HomotopyCategory.quasiIso (ModuleCat.{u} Rᵐᵒᵖ) (ComplexShape.up ℤ)).Localization

/-- For an algebra in degree zero, the right dg module localization agrees
with the usual derived category of right modules over the algebra. -/
private def derivedFromComplexes (h : Derived.HomotopyCategoryLaws (degreeZeroCategory k R)) :
    ordinaryDerived R ≌ D (degreeZeroCategory k R) h := by
  let W := HomotopyCategory.quasiIso (ModuleCat.{u} Rᵐᵒᵖ) (ComplexShape.up ℤ)
  let V := RightDGModule.quasiIsomorphisms (degreeZeroCategory k R)
  let F := homotopyFromComplexes (k := k) (R := R)
  have e : V.inverseImage F = W := by ext; exact homotopyFromComplexes_quasiIso _
  let L := LocalizerMorphism.ofEq e.symm
  letI : V.RespectsIso := by dsimp only [V]; rw [quasiIsomorphisms_eq_trW]; infer_instance
  letI : L.functor.IsEquivalence := homotopyFromComplexes_equivalence
  letI : L.IsInduced := ⟨e⟩
  letI : L.IsLocalizedEquivalence := L.isLocalizedEquivalence_of_isInduced
  exact (L.localizedFunctor W.Q (Q _ h)).asEquivalence

private abbrev leftDerived (S : Type u) [Ring S] :=
  (HomotopyCategory.quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ)).Localization

private def liftModuleEquivalence {S T : Type u} [Ring S] [Ring T]
    (E : ModuleCat.{u} S ≌ ModuleCat.{u} T) : leftDerived S ≌ leftDerived T := by
  let V := ModuleCat.{u} S
  let W := ModuleCat.{u} T
  let c := ComplexShape.up ℤ
  letI : E.functor.Additive := E.functor.additive_of_preserves_binary_products
  let F := E.functor.mapHomotopyCategory c
  let VQ := HomotopyCategory.quasiIso V c
  let WQ := HomotopyCategory.quasiIso W c
  have H : WQ.inverseImage F = VQ := by
    ext C D f
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient V c).map_surjective f
    change WQ (F.map ((HomotopyCategory.quotient V c).map g)) ↔ VQ ((HomotopyCategory.quotient V c).map g)
    rw [Functor.mapHomotopyCategory_map]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).trans
      ((HomologicalComplex.mem_quasiIso_iff _).trans
        ((quasiIso_map_iff_of_preservesHomology g E.functor).trans
          ((HomologicalComplex.mem_quasiIso_iff g).symm.trans
            (HomotopyCategory.quotient_map_mem_quasiIso_iff g).symm)))
  let L := LocalizerMorphism.ofEq H.symm
  letI : F.EssSurj := ⟨fun C => by
    let E' := E.mapHomologicalComplex c
    let D := E'.functor.objPreimage C.as
    let e := E'.functor.objObjPreimageIso C.as
    exact ⟨(HomotopyCategory.quotient V c).obj D,
      ⟨(HomotopyCategory.quotient W c).mapIso e⟩⟩⟩
  letI : F.IsEquivalence :=
    { faithful := inferInstanceAs ((E.functor.mapHomotopyCategory c).Faithful)
      full := inferInstanceAs ((E.functor.mapHomotopyCategory c).Full)
      essSurj := inferInstance }
  letI : L.functor.IsEquivalence := ‹F.IsEquivalence›
  letI : L.IsInduced := ⟨H⟩
  letI : L.IsLocalizedEquivalence := L.isLocalizedEquivalence_of_isInduced
  exact (L.localizedFunctor VQ.Q WQ.Q).asEquivalence

private def unopField (k : Type u) [Field k] : kᵐᵒᵖ ≃+* k where
  toEquiv := MulOpposite.opEquiv.symm
  map_add' _ _ := rfl
  map_mul' x y := mul_comm y.unop x.unop

private def matrixOrdinaryEquivalence (k : Type u) [Field k] (m : ℕ) (i : Fin m) :
    ordinaryDerived (Matrix (Fin m) (Fin m) k) ≌ ordinaryDerived k := by
  let h : ModuleCat.{u} kᵐᵒᵖ ≌ ModuleCat.{u} k :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv (unopField k).symm
  let e : ModuleCat.{u} k ≌ ModuleCat.{u} (Matrix (Fin m) (Fin m) k) :=
    ModuleCat.matrixEquivalence k i
  let j : ModuleCat.{u} (Matrix (Fin m) (Fin m) k) ≌ ModuleCat.{u} (Matrix (Fin m) (Fin m) k)ᵐᵒᵖ :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv (Matrix.transposeRingEquiv (Fin m) k).symm
  exact (liftModuleEquivalence (h.trans (e.trans j))).symm

private theorem proveDerivedCategoriesEquivalent : DerivedCategoriesEquivalent.{u} := by
  intro k _ m hm hM hB
  let i : Fin m := ⟨0, by omega⟩
  let _ : Category (Derived.derivedCategory _ hM) := DerivedKProjective.derivedCategoryInstance _ hM
  let _ : Category (Derived.derivedCategory _ hB) := DerivedKProjective.derivedCategoryInstance _ hB
  exact ⟨(derivedFromComplexes hM).symm.trans
    ((matrixOrdinaryEquivalence k m i).trans (derivedFromComplexes hB))⟩

end Ordinary

open EndomorphismGenerator (AmbientEndomorphismEquivalence EndomorphismLiftComparison
  NativeEndomorphismEquivalence)

theorem freeTerms_conditional.{fieldLevel}
    (_ : AmbientEndomorphismEquivalence.{fieldLevel,fieldLevel,fieldLevel,fieldLevel})
    (_ : EndomorphismLiftComparison.{fieldLevel,fieldLevel,fieldLevel,fieldLevel})
    (_ : NativeEndomorphismEquivalence.{fieldLevel,fieldLevel,fieldLevel,fieldLevel}) :
    FreeTerms.{fieldLevel} :=
  proveFreeTerms

theorem matrixEndomorphisms_conditional.{fieldLevel}
    (_ : AmbientEndomorphismEquivalence.{fieldLevel,fieldLevel,fieldLevel,fieldLevel})
    (_ : EndomorphismLiftComparison.{fieldLevel,fieldLevel,fieldLevel,fieldLevel})
    (_ : NativeEndomorphismEquivalence.{fieldLevel,fieldLevel,fieldLevel,fieldLevel}) :
    MatrixEndomorphisms.{fieldLevel} :=
  proveMatrixEndomorphisms

theorem freeGenerator_conditional.{fieldLevel,indexLevel}
    (_ : AmbientEndomorphismEquivalence.{fieldLevel,fieldLevel,fieldLevel,fieldLevel})
    (_ : EndomorphismLiftComparison.{fieldLevel,fieldLevel,fieldLevel,fieldLevel})
    (_ : NativeEndomorphismEquivalence.{fieldLevel,fieldLevel,fieldLevel,fieldLevel}) :
    FreeGenerator.{fieldLevel,indexLevel} :=
  proveFreeGenerator

theorem derivedMatrixMorita_conditional.{fieldLevel}
    (_ : AmbientEndomorphismEquivalence.{fieldLevel,fieldLevel,fieldLevel,fieldLevel})
    (_ : EndomorphismLiftComparison.{fieldLevel,fieldLevel,fieldLevel,fieldLevel})
    (native : NativeEndomorphismEquivalence.{fieldLevel,fieldLevel,fieldLevel,fieldLevel}) :
    DerivedMatrixMorita.{fieldLevel} := by
  intro k _ m hm
  dsimp only
  intro s hA hB hM S d hadd hr hc he
  obtain ⟨hp, h⟩ := proveFreeGenerator.{fieldLevel,fieldLevel} k m hm
  obtain ⟨hcompact, hdetect⟩ := h hB S hadd
  have ht := native (freeModule k m) s hA hB S d hadd hr hc he hp hcompact hdetect
  letI := DerivedKProjective.derivedCategoryInstance _ hA
  letI := DerivedKProjective.derivedCategoryInstance _ hB
  letI := DerivedKProjective.derivedCategoryInstance _ hM
  letI := ht
  let L := matrixLocalizer (k := k) m
  letI : L.IsLocalizedEquivalence := matrixLocalizer_isLocalizedEquivalence m
  let qM := RightDGModule.Q _ hM
  let qA := RightDGModule.Q _ hA
  let R := L.localizedFunctor qM qA
  haveI : R.IsEquivalence := by dsimp [R]; infer_instance
  have hmap (a b) : IsIso ((matrixComparison (k := k) m).map a b) := by
    dsimp [matrixComparison]
    infer_instance
  refine ⟨ht, matrixComparison m, matrixRestriction m, R, Function.bijective_id, hmap,
    (fun _ => rfl), (fun f => heq_of_eq (matrixRestriction_map f)), ?_, ?_⟩
  · exact ⟨(L.catCommSq qM qA).iso.symm⟩
  · exact (R.asEquivalence.trans d.tensor.asEquivalence).isEquivalence_functor

theorem derivedCategoriesEquivalent_conditional.{fieldLevel}
    (_ : AmbientEndomorphismEquivalence.{fieldLevel,fieldLevel,fieldLevel,fieldLevel})
    (_ : EndomorphismLiftComparison.{fieldLevel,fieldLevel,fieldLevel,fieldLevel})
    (_ : NativeEndomorphismEquivalence.{fieldLevel,fieldLevel,fieldLevel,fieldLevel}) :
    DerivedCategoriesEquivalent.{fieldLevel} :=
  proveDerivedCategoriesEquivalent

end

end DerivedFormalization.MatrixMoritaExample

universe v8_closure_fe12665ef493fb41_u0 v8_closure_fe12665ef493fb41_u1
theorem _root_.«DerivedFormalization».«MatrixMoritaExample».«derivedCategoriesEquivalent» : _root_.«Specs».«DerivedFormalization».«DG».«MatrixMoritaExample».«DerivedCategoriesEquivalent».{v8_closure_fe12665ef493fb41_u0} :=
  @_root_.«DerivedFormalization».«MatrixMoritaExample».«derivedCategoriesEquivalent_conditional».{v8_closure_fe12665ef493fb41_u0} (@_root_.«DerivedFormalization».«DGBimodule».«ambientEndomorphismEquivalence».{v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0}) (@_root_.«DerivedFormalization».«DGBimodule».«endomorphismLiftComparison».{v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0}) (@_root_.«DerivedFormalization».«DGBimodule».«nativeEndomorphismEquivalence».{v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0})
theorem _root_.«DerivedFormalization».«MatrixMoritaExample».«derivedMatrixMorita» : _root_.«Specs».«DerivedFormalization».«DG».«MatrixMoritaExample».«DerivedMatrixMorita».{v8_closure_fe12665ef493fb41_u0} :=
  @_root_.«DerivedFormalization».«MatrixMoritaExample».«derivedMatrixMorita_conditional».{v8_closure_fe12665ef493fb41_u0} (@_root_.«DerivedFormalization».«DGBimodule».«ambientEndomorphismEquivalence».{v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0}) (@_root_.«DerivedFormalization».«DGBimodule».«endomorphismLiftComparison».{v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0}) (@_root_.«DerivedFormalization».«DGBimodule».«nativeEndomorphismEquivalence».{v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0})
theorem _root_.«DerivedFormalization».«MatrixMoritaExample».«freeGenerator» : _root_.«Specs».«DerivedFormalization».«DG».«MatrixMoritaExample».«FreeGenerator».{v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u1} :=
  @_root_.«DerivedFormalization».«MatrixMoritaExample».«freeGenerator_conditional».{v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u1} (@_root_.«DerivedFormalization».«DGBimodule».«ambientEndomorphismEquivalence».{v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0}) (@_root_.«DerivedFormalization».«DGBimodule».«endomorphismLiftComparison».{v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0}) (@_root_.«DerivedFormalization».«DGBimodule».«nativeEndomorphismEquivalence».{v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0})
theorem _root_.«DerivedFormalization».«MatrixMoritaExample».«freeTerms» : _root_.«Specs».«DerivedFormalization».«DG».«MatrixMoritaExample».«FreeTerms».{v8_closure_fe12665ef493fb41_u0} :=
  @_root_.«DerivedFormalization».«MatrixMoritaExample».«freeTerms_conditional».{v8_closure_fe12665ef493fb41_u0} (@_root_.«DerivedFormalization».«DGBimodule».«ambientEndomorphismEquivalence».{v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0}) (@_root_.«DerivedFormalization».«DGBimodule».«endomorphismLiftComparison».{v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0}) (@_root_.«DerivedFormalization».«DGBimodule».«nativeEndomorphismEquivalence».{v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0})
theorem _root_.«DerivedFormalization».«MatrixMoritaExample».«matrixEndomorphisms» : _root_.«Specs».«DerivedFormalization».«DG».«MatrixMoritaExample».«MatrixEndomorphisms».{v8_closure_fe12665ef493fb41_u0} :=
  @_root_.«DerivedFormalization».«MatrixMoritaExample».«matrixEndomorphisms_conditional».{v8_closure_fe12665ef493fb41_u0} (@_root_.«DerivedFormalization».«DGBimodule».«ambientEndomorphismEquivalence».{v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0}) (@_root_.«DerivedFormalization».«DGBimodule».«endomorphismLiftComparison».{v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0}) (@_root_.«DerivedFormalization».«DGBimodule».«nativeEndomorphismEquivalence».{v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0, v8_closure_fe12665ef493fb41_u0})
