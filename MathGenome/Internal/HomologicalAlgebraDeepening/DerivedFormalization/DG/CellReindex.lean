import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.IndexedCellAttachment
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CellReindex

open CategoryTheory
open scoped DirectSum

universe u v w j t r

namespace DerivedFormalization.DG.CellReindex

open Specs.DerivedFormalization.DG.CellReindex
open Specs.DerivedFormalization.DG.IndexedSemiFree
open Specs.DerivedFormalization.DG

noncomputable section

section DirectSumMaps

variable {k : Type u} [CommRing k] {I : Type j} {J : Type t}
variable {V : I → Type r} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

private def restrictSum (f : J → I) (hf : Function.Injective f) :
    (⨁ i, V i) →ₗ[k] ⨁ s, V (f s) where
  toFun := DFinsupp.comapDomain f hf
  map_add' := DFinsupp.comapDomain_add f hf
  map_smul' := DFinsupp.comapDomain_smul f hf

private theorem restrictSum_apply (f : J → I) (hf : Function.Injective f)
    (x : ⨁ i, V i) (s : J) : restrictSum (k := k) f hf x s = x (f s) :=
  DFinsupp.comapDomain_apply f hf x s

private def extendSum (f : J → I) :
    (⨁ s, V (f s)) →ₗ[k] ⨁ i, V i := by
  classical
  exact DirectSum.toModule k J _ fun s => DirectSum.lof k I V (f s)

private theorem extendSum_lof (f : J → I) (s : J) (x : V (f s)) :
    haveI := Classical.decEq J
    haveI := Classical.decEq I
    extendSum (k := k) f (DirectSum.lof k J (fun s => V (f s)) s x) =
      DirectSum.lof k I V (f s) x := by
  classical
  exact DirectSum.toModule_lof (R := k) (φ := fun s => DirectSum.lof k I V (f s)) s x

private theorem extendSum_apply (f : J → I) (hf : Function.Injective f)
    (x : ⨁ s, V (f s)) (s : J) : extendSum (k := k) f x (f s) = x s := by
  classical
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero]; rfl
  | of i z =>
    change extendSum f (DirectSum.lof k J (fun s => V (f s)) i z) (f s) = _
    rw [extendSum_lof]
    by_cases h : i = s
    · subst i
      exact (DirectSum.lof_apply k (f s) z).trans (DirectSum.of_eq_same (β := fun s => V (f s)) s z).symm
    · exact (DirectSum.of_eq_of_ne (f i) (f s) z (fun e => h (hf e).symm)).trans
        (DirectSum.of_eq_of_ne (β := fun s => V (f s)) i s z (Ne.symm h)).symm
  | add x y hx hy => rw [map_add, DFinsupp.add_apply, DFinsupp.add_apply, hx, hy]

private theorem extendSum_off_range (f : J → I) (x : ⨁ s, V (f s)) {i : I}
    (hi : i ∉ Set.range f) : extendSum (k := k) f x i = 0 := by
  classical
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero]; rfl
  | of s z =>
    change extendSum f (DirectSum.lof k J (fun s => V (f s)) s z) i = 0
    rw [extendSum_lof]
    exact DirectSum.of_eq_of_ne (f s) i z (fun e => hi ⟨s, e.symm⟩)
  | add x y hx hy => rw [map_add, DFinsupp.add_apply, hx, hy, add_zero]

end DirectSumMaps

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
variable {P Q M : RightDGModuleModel A} {I : Type j} {J : Type t} {C : CellFamily P I}

theorem zeroCells : ZeroCells.{u,v,w,j} := by
  intro k _ A P I C i hi
  refine ⟨?_, ?_⟩
  · simpa only [hi, map_zero] using (P.act_id (C.object i) (C.degree i + 1) (C.boundary i)).symm
  · intro a n x
    simpa only [hi, map_zero, LinearMap.zero_apply] using (A.toData.id_comp _ x).symm

private theorem cellGenerator_eq_zero (a : A.Obj) (n : ℤ) :
    SemiFree.generator a n = 0 ↔ A.id a = 0 := by
  let e := (A.hom a a).XIsoOfEq (by omega : (0 : ℤ) = n + -n)
  change e.hom (A.id a) = 0 ↔ _
  constructor
  · intro h
    have hinv (x : (A.hom a a).X 0) : e.inv (e.hom x) = x :=
      congrArg (fun f : (A.hom a a).X 0 ⟶ (A.hom a a).X 0 => f x) e.hom_inv_id
    rw [← hinv (A.id a), h, map_zero]
  · intro h
    rw [h, map_zero]

private theorem generator_coordinate_self (E : Attachment C Q) (i : I) :
    ((E.coordinates (C.object i) (C.degree i) (E.generator i)).2 i) =
      SemiFree.generator (C.object i) (C.degree i) := by
  classical
  rw [IndexedCellAttachment.generator_coordinates]
  exact DirectSum.lof_apply k i _

theorem generatorSeparation : GeneratorSeparation.{u,v,w,j} := by
  classical
  intro k _ A P Q I C E
  constructor
  · intro i
    rw [← cellGenerator_eq_zero (C.object i) (C.degree i)]
    constructor
    · intro h
      rw [← generator_coordinate_self E i, h, map_zero]
      rfl
    · intro h
      apply (E.coordinates (C.object i) (C.degree i)).injective
      rw [IndexedCellAttachment.generator_coordinates, h, map_zero, map_zero]
      rfl
  · intro i s h
    apply Subtype.ext
    by_contra hne
    let nonzero (z : Σ a : A.Obj, Σ n : ℤ, (Q.complex a).X n) : Prop :=
      (E.coordinates z.1 z.2.1 z.2.2).2 i.val ≠ 0
    have hi : nonzero ⟨C.object i, C.degree i, E.generator i⟩ := by
      change (E.coordinates (C.object i) (C.degree i) (E.generator i)).2 i.val ≠ 0
      rw [generator_coordinate_self]
      exact fun h => i.property ((cellGenerator_eq_zero (C.object i) (C.degree i)).mp h)
    have hs : nonzero ⟨C.object s, C.degree s, E.generator s⟩ := (congrArg nonzero h).mp hi
    apply hs
    change (E.coordinates (C.object s) (C.degree s) (E.generator s)).2 i.val = 0
    rw [IndexedCellAttachment.generator_coordinates]
    exact DirectSum.of_eq_of_ne s.val i.val _ hne

theorem cellMapFormula : CellMapFormula.{u,v,w,j} := by
  intro k _ A M F l i a m n h f
  apply ((F.extension l).coordinates a n).injective
  exact (LinearEquiv.apply_symm_apply _ _).trans
    (IndexedCellAttachment.generator_mul (F.extension l) i a m n h f).symm

section Restriction

variable (e : J ≃ NonzeroIndex C)

private abbrev retained (i : J) : I := (e i).val

private theorem retained_injective : Function.Injective (retained e) :=
  Subtype.val_injective.comp e.injective

private theorem zero_of_not_retained (a : A.Obj) (n : ℤ) (i : I)
    (hi : i ∉ Set.range (retained e)) (x : ((cells C i).complex a).X n) : x = 0 := by
  classical
  apply (zeroCells C i ?_).2 a n x
  by_contra h
  exact hi ⟨e.symm ⟨i, h⟩, congrArg Subtype.val (e.apply_symm_apply ⟨i, h⟩)⟩

private theorem extend_restrict_cells (a : A.Obj) (n : ℤ) (x : CellTerm C a n) :
    extendSum (k := k) (retained e) (restrictSum (k := k) (retained e) (retained_injective e) x) = x := by
  apply DFinsupp.ext
  intro i
  by_cases hi : i ∈ Set.range (retained e)
  · obtain ⟨s, rfl⟩ := hi
    rw [extendSum_apply _ (retained_injective e), restrictSum_apply]
  · rw [extendSum_off_range _ _ hi, zero_of_not_retained e a n i hi (x i)]

private def restrictCells (a : A.Obj) (n : ℤ) :
    CellTerm C a n ≃ₗ[k] CellTerm (reindexFamily C (retained e)) a n :=
  LinearEquiv.ofBijective (restrictSum (retained e) (retained_injective e))
    ⟨Function.LeftInverse.injective (extend_restrict_cells e a n), fun y => by
      refine ⟨extendSum (k := k) (retained e) y, DFinsupp.ext fun s => ?_⟩
      exact extendSum_apply (k := k) (V := fun i => ((cells C i).complex a).X n)
        _ (retained_injective e) y s⟩

private theorem restrictCells_apply (a : A.Obj) (n : ℤ) (x : CellTerm C a n) (s : J) :
    restrictCells e a n x s = x (retained e s) := rfl

private theorem restrictCells_summand (a : A.Obj) (n : ℤ) (s : J)
    (x : ((cells C (retained e s)).complex a).X n) :
    restrictCells e a n (summand (cells C) a n (retained e s) x) =
      summand (cells (reindexFamily C (retained e))) a n s x := by
  classical
  exact DFinsupp.comapDomain_single _ (retained_injective e) _ _

private theorem boundaryMap_extend (a : A.Obj) (n : ℤ)
    (x : CellTerm (reindexFamily C (retained e)) a n) :
    boundaryMap C a n (extendSum (k := k) (retained e) x) =
      boundaryMap (reindexFamily C (retained e)) a n x := by
  classical
  let V (i : I) : Type v := ((cells C i).complex a).X n
  let L : CellTerm (reindexFamily C (retained e)) a n →ₗ[k] CellTerm C a n :=
    extendSum (V := fun i => ((cells C i).complex a).X n) (retained e)
  change boundaryMap C a n (L x) = _
  have hL : (boundaryMap C a n).comp L = boundaryMap (reindexFamily C (retained e)) a n := by
    apply DirectSum.linearMap_ext
    intro s
    apply LinearMap.ext
    intro z
    change boundaryMap C a n
      (L (DirectSum.lof k J (fun s => V (retained e s)) s z)) =
      boundaryMap (reindexFamily C (retained e)) a n
        (DirectSum.lof k J (fun s => ((cells (reindexFamily C (retained e)) s).complex a).X n) s z)
    have hh : L (DirectSum.lof k J (fun s => V (retained e s)) s z) =
        DirectSum.lof k I V (retained e s) z :=
      extendSum_lof (V := fun i => ((cells C i).complex a).X n) (retained e) s z
    rw [hh]
    have hOld := DirectSum.toModule_lof (R := k)
      (φ := fun i => P.act (C.degree i + 1) (n + -C.degree i) (n+1) (by omega) (C.boundary i))
      (retained e s) (show ((cells C (retained e s)).complex a).X n from z)
    let D := reindexFamily C (retained e)
    have hNew := DirectSum.toModule_lof (R := k)
      (φ := fun i => P.act (D.degree i + 1) (n + -D.degree i) (n+1) (by omega) (D.boundary i))
      s (show ((cells D s).complex a).X n from z)
    exact hOld.trans hNew.symm
  exact congrArg (fun f : CellTerm (reindexFamily C (retained e)) a n →ₗ[k]
    (P.complex a).X (n+1) => f x) hL

private theorem boundaryMap_restrict (a : A.Obj) (n : ℤ) (x : CellTerm C a n) :
    boundaryMap (reindexFamily C (retained e)) a n (restrictCells e a n x) = boundaryMap C a n x :=
  (boundaryMap_extend e a n _).symm.trans (congrArg _ (extend_restrict_cells e a n x))

/-- Keep the strict inclusion while restricting the graded coordinates to nonzero cells. -/
private def restrictAttachment (E : Attachment C Q) :
    Attachment (reindexFamily C (retained e)) Q where
  inclusion := E.inclusion
  coordinates a n := (E.coordinates a n).trans ((LinearEquiv.refl k _).prodCongr (restrictCells e a n))
  coordinate_inclusion a n x := by
    exact (congrArg ((LinearEquiv.refl k _).prodCongr (restrictCells e a n))
      (E.coordinate_inclusion a n x)).trans (Prod.ext rfl (map_zero (restrictCells e a n)))
  coordinate_d a n x := by
    have h := E.coordinate_d a n x
    dsimp only at h ⊢
    refine ⟨?_, ?_⟩
    · change (E.coordinates a (n+1) ((Q.complex a).d n (n+1) x)).1 =
        (P.complex a).d n (n+1) (E.coordinates a n x).1 +
          boundaryMap (reindexFamily C (retained e)) a n (restrictCells e a n (E.coordinates a n x).2)
      rw [boundaryMap_restrict]
      exact h.1
    · exact fun s => h.2 (retained e s)
  coordinate_act m n q h x f := by
    have hc := E.coordinate_act m n q h x f
    exact ⟨hc.1, fun s => hc.2 (retained e s)⟩

private theorem restrictAttachment_generator (E : Attachment C Q) (s : J) :
    (restrictAttachment e E).generator s = E.generator (retained e s) := by
  apply ((restrictAttachment e E).coordinates (C.object (retained e s)) (C.degree (retained e s))).injective
  refine (IndexedCellAttachment.generator_coordinates (restrictAttachment e E) s).trans ?_
  let a := C.object (retained e s)
  let n := C.degree (retained e s)
  let z := SemiFree.generator a n
  change (0, summand (cells (reindexFamily C (retained e))) a n s z) =
    ( (E.coordinates a n (E.generator (retained e s))).1,
      restrictCells e a n (E.coordinates a n (E.generator (retained e s))).2 )
  rw [IndexedCellAttachment.generator_coordinates, restrictCells_summand]

end Restriction

theorem reindex : Reindex.{u,v,w,j,t} := by
  intro k _ A M F hs
  let e (l : ℕ) : Shrink.{t} (NonzeroIndex (F.family l)) ≃ NonzeroIndex (F.family l) :=
    (equivShrink (NonzeroIndex (F.family l))).symm
  let R : Reindexing.{u,v,w,j,t} F :=
    { index := fun l => Shrink.{t} (NonzeroIndex (F.family l))
      original := e
      extension := fun l => restrictAttachment (e l) (F.extension l)
      inclusion := fun _ => rfl
      previous_coordinate := fun _ _ _ _ => rfl
      cell_coordinate := fun _ _ _ _ _ => rfl
      generator := fun l => restrictAttachment_generator (e l) (F.extension l) }
  refine ⟨R, fun h => ?_⟩
  let f (s : Σ l, R.index l) : Σ l, F.index l := ⟨s.1, R.original s.1 s.2⟩
  apply Finite.of_injective f
  rintro ⟨l, x⟩ ⟨m, y⟩ hxy
  have hl : l = m := congrArg Sigma.fst hxy
  subst m
  exact congrArg (Sigma.mk l) (retained_injective (e l) (Sigma.mk.inj_iff.mp hxy).2.eq)

theorem normalize : Normalize.{u,v,w,j} := by
  intro k _ A M F
  apply reindex.{u,v,w,j,max v w} F
  intro l
  exact small_of_injective (generatorSeparation (F.extension l)).2

section Small

private def realizeSmall (F : Presentation.{u,v,w,v} M) : SmallRealization (M := M) F where
  successor l := IndexedCellAttachment.comparisonIso
    (IndexedCellAttachment.nativeAttachment (smallFamily (F.family l))) (F.extension l)
  inclusion l := IndexedCellAttachment.inclusion_comparisonIso _ _
  coordinate l a n x := by
    let D := F.extension l
    let E := IndexedCellAttachment.nativeAttachment (smallFamily (F.family l))
    let e := IndexedCellAttachment.comparisonIso E D
    change (e.inv.app a).f n x = D.coordinates a n x
    have h := IndexedCellAttachment.comparisonIso_coordinates E D a n ((e.inv.app a).f n x)
    have he : (e.hom.app a).f n ((e.inv.app a).f n x) = x :=
      congrArg (fun f : F.stage (l+1) ⟶ F.stage (l+1) => (f.app a).f n x) e.inv_hom_id
    rw [he] at h
    exact h.symm

theorem toSmall : ToSmall.{u,v,w,j} := by
  intro k _ A M F h
  obtain ⟨R, hR⟩ := reindex.{u,v,w,j,v} F h
  exact ⟨R, ⟨realizeSmall R.toPresentation⟩, hR⟩

private def concreteAttachment (F : SemiFree.Presentation M) (l : ℕ) :
    Attachment (indexedFamily (A := A) (F.family l)) (F.stage (l+1)) where
  inclusion := SemiFree.inclusion (F.family l) ≫ (F.successor l).hom
  coordinates a n := ((RightDGModuleModel.degree a n).mapIso (F.successor l).symm).toLinearEquiv
  coordinate_inclusion a n x := by
    let e := F.successor l
    let f := SemiFree.inclusion (F.family l)
    change (e.inv.app a).f n ((e.hom.app a).f n ((f.app a).f n x)) = (x, 0)
    exact congrArg (fun g : SemiFree.attach (F.family l) ⟶ SemiFree.attach (F.family l) =>
      (g.app a).f n ((f.app a).f n x)) e.hom_inv_id
  coordinate_d a n x := by
    let e := F.successor l
    let E := IndexedCellAttachment.nativeAttachment (F.family l)
    have hc := E.coordinate_d a n ((e.inv.app a).f n x)
    have h := CategoryTheory.congr_fun ((e.inv.app a).comm n (n+1)) x
    change (SemiFree.attachComplex (F.family l) a).d n (n+1) ((e.inv.app a).f n x) =
      (e.inv.app a).f (n+1) (((F.stage (l+1)).complex a).d n (n+1) x) at h
    dsimp only at hc ⊢
    exact ⟨(congrArg Prod.fst h.symm).trans hc.1, fun i => (congrArg (fun z => z.2 i) h.symm).trans (hc.2 i)⟩
  coordinate_act m n q h x f := by
    let e := F.successor l
    let E := IndexedCellAttachment.nativeAttachment (F.family l)
    have hc := E.coordinate_act m n q h ((e.inv.app _).f m x) f
    have he := e.inv.comm_act m n q h x f
    exact ⟨(congrArg Prod.fst he).trans hc.1, fun i => (congrArg (fun z => z.2 i) he).trans (hc.2 i)⟩

theorem fromSmall : FromSmall.{u,v,w} := by
  intro k _ A M F
  exact ⟨concreteAttachment F, fun _ => rfl, fun _ _ _ _ => rfl⟩

theorem finiteCellComparison : FiniteCellComparison.{u,v,w} := by
  intro k _ A M
  constructor
  · rintro ⟨F, hF⟩
    have hs (l : ℕ) : Small.{v} (NonzeroIndex (F.family l)) := by
      have : Finite (NonzeroIndex (F.family l)) :=
        Finite.of_injective (fun i : NonzeroIndex (F.family l) => (⟨l, i.val⟩ : Σ l, F.index l))
          (fun _ _ h => Subtype.ext (Sigma.mk.inj_iff.mp h).2.eq)
      let := Fintype.ofFinite (NonzeroIndex (F.family l))
      exact small_of_injective (Fintype.equivFin (NonzeroIndex (F.family l))).injective
    obtain ⟨R, ⟨S⟩, hf⟩ := toSmall F hs
    exact ⟨S.toPresentation, hf hF⟩
  · rintro ⟨F, hF⟩
    let G := indexedPresentation F (concreteAttachment F) (fun _ => rfl)
    obtain ⟨R, hR⟩ := normalize G
    exact ⟨R.toPresentation, hR hF⟩

end Small

section Decomposition

variable (F : Presentation.{u,v,w,j} M)

private abbrev AllTerms (a : A.Obj) (n : ℤ) := SumTerm (allCells F) a n

private def levelIndex (N : ℕ) (s : F.index N) : Σ l, F.index l := ⟨N, s⟩

private theorem levelIndex_injective (N : ℕ) : Function.Injective (levelIndex F N) :=
  fun _ _ h => (Sigma.mk.inj_iff.mp h).2.eq

private abbrev stageIndexEmbedding (N : ℕ) (s : StageIndex F N) : Σ l, F.index l :=
  ⟨s.1.val, s.2⟩

private theorem stageIndexEmbedding_injective (N : ℕ) :
    Function.Injective (stageIndexEmbedding F N) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ h
  have he : i = j := Fin.ext (congrArg Sigma.fst h)
  subst j
  exact congrArg (Sigma.mk i) (Sigma.mk.inj_iff.mp h).2.eq

private def extendLevel (N : ℕ) (a : A.Obj) (n : ℤ) :
    CellTerm (F.family N) a n →ₗ[k] AllTerms F a n :=
  extendSum (V := fun s => ((allCells F s).complex a).X n) (levelIndex F N)

private theorem extendLevel_self (N : ℕ) (a : A.Obj) (n : ℤ)
    (x : CellTerm (F.family N) a n) (i : F.index N) :
    extendLevel F N a n x ⟨N,i⟩ = x i :=
  extendSum_apply (V := fun s => ((allCells F s).complex a).X n)
    (levelIndex F N) (levelIndex_injective F N) x i

private theorem extendLevel_other (N : ℕ) (a : A.Obj) (n : ℤ)
    (x : CellTerm (F.family N) a n) (s : Σ l, F.index l) (hs : s.1 ≠ N) :
    extendLevel F N a n x s = 0 :=
  extendSum_off_range (V := fun s => ((allCells F s).complex a).X n)
    (levelIndex F N) x (fun ⟨_,he⟩ => hs (congrArg Sigma.fst he).symm)

/-- Give a stage its graded coordinates with zeroes at all later stages. -/
private def stageEncoding (a : A.Obj) (n : ℤ) :
    (N : ℕ) → ((F.stage N).complex a).X n →ₗ[k] AllTerms F a n
  | 0 => 0
  | N+1 => ((stageEncoding a n N).comp (LinearMap.fst k _ _) +
        (extendLevel F N a n).comp (LinearMap.snd k _ _)).comp
      ((F.extension N).coordinates a n).toLinearMap

private theorem stageEncoding_succ (a : A.Obj) (n : ℤ) (N : ℕ)
    (x : ((F.stage (N+1)).complex a).X n) :
    stageEncoding F a n (N+1) x =
      stageEncoding F a n N ((F.extension N).coordinates a n x).1 +
      extendLevel F N a n ((F.extension N).coordinates a n x).2 := rfl

private theorem stageEncoding_bounded (a : A.Obj) (n : ℤ) (N : ℕ)
    (x : ((F.stage N).complex a).X n) (s : Σ l, F.index l) (hs : N ≤ s.1) :
    stageEncoding F a n N x s = 0 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [stageEncoding_succ, DFinsupp.add_apply, ih _ (by omega),
      extendLevel_other _ _ _ _ _ _ (by omega), add_zero]

private theorem stageEncoding_old (a : A.Obj) (n : ℤ) (N : ℕ)
    (x : ((F.stage (N+1)).complex a).X n) (s : Σ l, F.index l) (hs : s.1 ≠ N) :
    stageEncoding F a n (N+1) x s =
      stageEncoding F a n N ((F.extension N).coordinates a n x).1 s := by
  rw [stageEncoding_succ, DFinsupp.add_apply, extendLevel_other _ _ _ _ _ _ hs, add_zero]

private theorem stageEncoding_new (a : A.Obj) (n : ℤ) (N : ℕ)
    (x : ((F.stage (N+1)).complex a).X n) (i : F.index N) :
    stageEncoding F a n (N+1) x ⟨N,i⟩ = ((F.extension N).coordinates a n x).2 i := by
  rw [stageEncoding_succ, DFinsupp.add_apply,
    stageEncoding_bounded _ _ _ _ _ _ (Nat.le_refl N), extendLevel_self, zero_add]

private theorem stageEncoding_injective (a : A.Obj) (n : ℤ) (N : ℕ) :
    Function.Injective (stageEncoding F a n N) := by
  induction N with
  | zero => intro x y _; exact (F.bottom a n x).trans (F.bottom a n y).symm
  | succ N ih =>
    intro x y h
    apply ((F.extension N).coordinates a n).injective
    apply Prod.ext
    · apply ih
      apply DFinsupp.ext
      intro s
      by_cases hs : s.1 = N
      · rw [stageEncoding_bounded _ _ _ _ _ _ (by omega),
            stageEncoding_bounded _ _ _ _ _ _ (by omega)]
      · simpa only [stageEncoding_old _ _ _ _ _ _ hs] using
          congrArg (fun z : AllTerms F a n => z s) h
    · apply DFinsupp.ext
      intro i
      simpa only [stageEncoding_new] using
        congrArg (fun z : AllTerms F a n => z ⟨N,i⟩) h

private theorem stageEncoding_inclusion (a : A.Obj) (n : ℤ) (N : ℕ)
    (x : ((F.stage N).complex a).X n) :
    stageEncoding F a n (N+1) (((F.extension N).inclusion.app a).f n x) =
      stageEncoding F a n N x := by
  rw [stageEncoding_succ, (F.extension N).coordinate_inclusion]
  change stageEncoding F a n N x + extendLevel F N a n 0 = _
  rw [map_zero, add_zero]

private theorem stageEncoding_successorCell (a : A.Obj) (n : ℤ) (N : ℕ) (i : F.index N)
    (x : ((cells (F.family N) i).complex a).X n) :
    stageEncoding F a n (N+1) (cellToSuccessor F N i a n x) =
      summand (allCells F) a n ⟨N,i⟩ x := by
  classical
  have h : (F.extension N).coordinates a n (cellToSuccessor F N i a n x) =
      (0, summand (cells (F.family N)) a n i x) :=
    LinearEquiv.apply_symm_apply _ _
  rw [stageEncoding_succ, h]
  change stageEncoding F a n N 0 + extendLevel F N a n (summand (cells (F.family N)) a n i x) = _
  rw [map_zero, zero_add]
  exact extendSum_lof (V := fun s => ((allCells F s).complex a).X n) (levelIndex F N) i x

private theorem stageInclusion_refl {N : ℕ} :
    stageInclusion F (Nat.le_refl N) = 𝟙 (F.stage N) :=
  Functor.OfSequence.map_id _ N

private theorem stageInclusion_succ {l N : ℕ} (h : l ≤ N) :
    stageInclusion F (Nat.le.step h) = stageInclusion F h ≫ (F.extension N).inclusion := by
  unfold stageInclusion
  rw [Functor.OfSequence.map_comp _ l N (N+1) h (Nat.le_succ N),
    Functor.OfSequence.map_le_succ]

private theorem stageInclusion_into {l N : ℕ} (h : l ≤ N) :
    stageInclusion F h ≫ F.into N = F.into l := by
  induction N with
  | zero =>
    have he : l = 0 := Nat.eq_zero_of_le_zero h
    subst l
    rw [stageInclusion_refl, Category.id_comp]
  | succ N ih =>
    by_cases hh : l ≤ N
    · rw [stageInclusion_succ F hh, Category.assoc, F.compatible, ih hh]
    · have he : l = N+1 := by omega
      subst l
      rw [stageInclusion_refl, Category.id_comp]

private theorem stageEncoding_cell (a : A.Obj) (n : ℤ) (N : ℕ) (s : StageIndex F N)
    (x : ((stageCells F N s).complex a).X n) :
    stageEncoding F a n N (cellToStage F N s a n x) =
      summand (allCells F) a n (stageIndexEmbedding F N s) x := by
  induction N with
  | zero => exact Fin.elim0 s.1
  | succ N ih =>
    rcases s with ⟨⟨l,hl⟩, i⟩
    by_cases h : l < N
    · have he : cellToStage F (N+1) ⟨⟨l,hl⟩,i⟩ a n x =
          (((F.extension N).inclusion.app a).f n (cellToStage F N ⟨⟨l,h⟩,i⟩ a n x)) := by
        unfold cellToStage
        rw [stageInclusion_succ F (Nat.succ_le_of_lt h)]
        rfl
      rw [he, stageEncoding_inclusion]
      exact ih ⟨⟨l,h⟩,i⟩ x
    · have he : l = N := by omega
      subst l
      have he : cellToStage F (N+1) ⟨⟨N,hl⟩,i⟩ a n x = cellToSuccessor F N i a n x := by
        unfold cellToStage
        rw [stageInclusion_refl]
        rfl
      rw [he]
      exact stageEncoding_successorCell F a n N i x

private theorem stageEncoding_act (N : ℕ) {a b : A.Obj} (m n q : ℤ) (h : m+n=q)
    (x : ((F.stage N).complex b).X m) (f : (A.hom a b).X n) (s : Σ l, F.index l) :
    stageEncoding F a q N ((F.stage N).act m n q h x f) s =
      (allCells F s).act m n q h (stageEncoding F b m N x s) f := by
  induction N with
  | zero => change (0 : ((allCells F s).complex a).X q) = (allCells F s).act m n q h 0 f
            rw [map_zero, LinearMap.zero_apply]
  | succ N ih =>
    have hc := (F.extension N).coordinate_act m n q h x f
    dsimp only at hc
    rcases s with ⟨l,i⟩
    by_cases hl : l = N
    · subst l
      rw [stageEncoding_new, stageEncoding_new]
      exact hc.2 i
    · rw [stageEncoding_old _ _ _ _ _ _ hl, stageEncoding_old _ _ _ _ _ _ hl, hc.1]
      exact ih ((F.extension N).coordinates b m x).1

private def extendStage (N : ℕ) (a : A.Obj) (n : ℤ) :
    SumTerm (stageCells F N) a n →ₗ[k] AllTerms F a n :=
  extendSum (V := fun s => ((allCells F s).complex a).X n) (stageIndexEmbedding F N)

private def restrictStage (N : ℕ) (a : A.Obj) (n : ℤ) :
    AllTerms F a n →ₗ[k] SumTerm (stageCells F N) a n :=
  restrictSum (V := fun s => ((allCells F s).complex a).X n)
    (stageIndexEmbedding F N) (stageIndexEmbedding_injective F N)

private theorem extendStage_apply (N : ℕ) (a : A.Obj) (n : ℤ)
    (x : SumTerm (stageCells F N) a n) (s : StageIndex F N) :
    extendStage F N a n x (stageIndexEmbedding F N s) = x s :=
  extendSum_apply (V := fun s => ((allCells F s).complex a).X n)
    (stageIndexEmbedding F N) (stageIndexEmbedding_injective F N) x s

private theorem extendStage_restrictStage (N : ℕ) (a : A.Obj) (n : ℤ)
    (x : AllTerms F a n) (hx : ∀ s : Σ l, F.index l, N ≤ s.1 → x s = 0) :
    extendStage F N a n (restrictStage F N a n x) = x := by
  apply DFinsupp.ext
  rintro ⟨l,i⟩
  by_cases h : l < N
  · let s : StageIndex F N := ⟨⟨l,h⟩,i⟩
    exact extendStage_apply F N a n (restrictStage F N a n x) s
  · refine (extendSum_off_range (V := fun s => ((allCells F s).complex a).X n)
      (stageIndexEmbedding F N) (restrictStage F N a n x) ?_).trans (hx ⟨l,i⟩ (Nat.le_of_not_gt h)).symm
    rintro ⟨s,hs⟩
    have he : s.1.val = l := congrArg Sigma.fst hs
    exact h (he ▸ s.1.isLt)

private theorem extendStage_summand (N : ℕ) (a : A.Obj) (n : ℤ) (s : StageIndex F N)
    (x : ((stageCells F N s).complex a).X n) :
    extendStage F N a n (summand (stageCells F N) a n s x) =
      summand (allCells F) a n (stageIndexEmbedding F N s) x :=
  extendSum_lof (V := fun s => ((allCells F s).complex a).X n) (stageIndexEmbedding F N) s x

private theorem sumTerm_bound (a : A.Obj) (n : ℤ) (x : AllTerms F a n) :
    ∃ N : ℕ, ∀ s : Σ l, F.index l, N ≤ s.1 → x s = 0 := by
  classical
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, fun _ _ => rfl⟩
  | of s x =>
    refine ⟨s.1 + 1, fun t ht => DirectSum.of_eq_of_ne (β := fun r => ((allCells F r).complex a).X n) s t x ?_⟩
    intro h
    have he := congrArg Sigma.fst h
    omega
  | add x y hx hy =>
    obtain ⟨N,hN⟩ := hx
    obtain ⟨L,hL⟩ := hy
    refine ⟨max N L, fun s hs => ?_⟩
    rw [DFinsupp.add_apply, hN s ((le_max_left N L).trans hs),
      hL s ((le_max_right N L).trans hs), add_zero]

private def stageDecoding (N : ℕ) (a : A.Obj) (n : ℤ) :
    SumTerm (stageCells F N) a n →ₗ[k] ((F.stage N).complex a).X n := by
  letI : DecidableEq (StageIndex F N) := Classical.decEq _
  exact DirectSum.toModule k (StageIndex F N) _ fun s => cellToStage F N s a n

private theorem stageDecoding_summand (N : ℕ) (a : A.Obj) (n : ℤ) (s : StageIndex F N)
    (x : ((stageCells F N s).complex a).X n) :
    stageDecoding F N a n (summand (stageCells F N) a n s x) = cellToStage F N s a n x := by
  let _ : DecidableEq (StageIndex F N) := Classical.decEq _
  exact DirectSum.toModule_lof (R := k) (φ := fun s => cellToStage F N s a n) s x

private theorem stageEncoding_decoding (N : ℕ) (a : A.Obj) (n : ℤ)
    (x : SumTerm (stageCells F N) a n) :
    stageEncoding F a n N (stageDecoding F N a n x) = extendStage F N a n x := by
  let _ : DecidableEq (StageIndex F N) := Classical.decEq _
  have h : (stageEncoding F a n N).comp (stageDecoding F N a n) = extendStage F N a n := by
    apply DirectSum.linearMap_ext
    intro s
    apply LinearMap.ext
    intro y
    change stageEncoding F a n N (stageDecoding F N a n (summand (stageCells F N) a n s y)) =
      extendStage F N a n (summand (stageCells F N) a n s y)
    rw [stageDecoding_summand, stageEncoding_cell, extendStage_summand]
  exact DFunLike.congr_fun h x

private def stageCoordinates (N : ℕ) (a : A.Obj) (n : ℤ) :
    ((F.stage N).complex a).X n ≃ₗ[k] SumTerm (stageCells F N) a n :=
  LinearEquiv.ofBijective ((restrictStage F N a n).comp (stageEncoding F a n N)) (by
    constructor
    · intro x y h
      have hx := extendStage_restrictStage F N a n (stageEncoding F a n N x)
        (stageEncoding_bounded F a n N x)
      have hy := extendStage_restrictStage F N a n (stageEncoding F a n N y)
        (stageEncoding_bounded F a n N y)
      apply stageEncoding_injective F a n N
      exact hx.symm.trans ((congrArg (extendStage F N a n) h).trans hy)
    · intro x
      refine ⟨stageDecoding F N a n x, DFinsupp.ext fun s => ?_⟩
      change stageEncoding F a n N (stageDecoding F N a n x) (stageIndexEmbedding F N s) = x s
      rw [stageEncoding_decoding, extendStage_apply])

private theorem stageCoordinates_apply (N : ℕ) (a : A.Obj) (n : ℤ)
    (x : ((F.stage N).complex a).X n) (s : StageIndex F N) :
    stageCoordinates F N a n x s = stageEncoding F a n N x (stageIndexEmbedding F N s) := rfl

private theorem stageCoordinates_cell (N : ℕ) (s : StageIndex F N) (a : A.Obj) (n : ℤ)
    (x : ((stageCells F N s).complex a).X n) :
    stageCoordinates F N a n (cellToStage F N s a n x) =
      summand (stageCells F N) a n s x := by
  apply DFinsupp.ext
  intro t
  rw [stageCoordinates_apply, stageEncoding_cell, ← extendStage_summand, extendStage_apply]

/-- Sum the cell maps into the full module. The domain has finite support. -/
private def moduleDecoding (a : A.Obj) (n : ℤ) :
    AllTerms F a n →ₗ[k] (M.complex a).X n := by
  letI : DecidableEq (Σ l, F.index l) := Classical.decEq _
  exact DirectSum.toModule k (Σ l, F.index l) _ fun s => cellToModule F s a n

private theorem moduleDecoding_summand (a : A.Obj) (n : ℤ) (s : Σ l, F.index l)
    (x : ((allCells F s).complex a).X n) :
    moduleDecoding F a n (summand (allCells F) a n s x) = cellToModule F s a n x := by
  let _ : DecidableEq (Σ l, F.index l) := Classical.decEq _
  exact DirectSum.toModule_lof (R := k) (φ := fun s => cellToModule F s a n) s x

private theorem moduleDecoding_extendStage (N : ℕ) (a : A.Obj) (n : ℤ)
    (x : SumTerm (stageCells F N) a n) :
    moduleDecoding F a n (extendStage F N a n x) =
      ((F.into N).app a).f n (stageDecoding F N a n x) := by
  let _ : DecidableEq (StageIndex F N) := Classical.decEq _
  have h : (moduleDecoding F a n).comp (extendStage F N a n) =
      (((F.into N).app a).f n).hom.comp (stageDecoding F N a n) := by
    apply DirectSum.linearMap_ext
    intro s
    apply LinearMap.ext
    intro y
    change moduleDecoding F a n (extendStage F N a n (summand (stageCells F N) a n s y)) =
      ((F.into N).app a).f n (stageDecoding F N a n (summand (stageCells F N) a n s y))
    rw [extendStage_summand, moduleDecoding_summand, stageDecoding_summand]
    exact congrArg (fun f : F.stage (s.1.val+1) ⟶ M =>
      (f.app a).f n (cellToSuccessor F s.1.val s.2 a n y))
      (stageInclusion_into F (Nat.succ_le_of_lt s.1.isLt)).symm
  exact DFunLike.congr_fun h x

private theorem stageDecoding_restrictStage (N : ℕ) (a : A.Obj) (n : ℤ)
    (x : ((F.stage N).complex a).X n) :
    stageDecoding F N a n (restrictStage F N a n (stageEncoding F a n N x)) = x := by
  apply stageEncoding_injective F a n N
  rw [stageEncoding_decoding, extendStage_restrictStage F N a n _ (stageEncoding_bounded F a n N x)]

private theorem moduleDecoding_stageEncoding (N : ℕ) (a : A.Obj) (n : ℤ)
    (x : ((F.stage N).complex a).X n) :
    moduleDecoding F a n (stageEncoding F a n N x) = ((F.into N).app a).f n x := by
  calc
    moduleDecoding F a n (stageEncoding F a n N x) =
        moduleDecoding F a n (extendStage F N a n (restrictStage F N a n (stageEncoding F a n N x))) :=
      congrArg (moduleDecoding F a n)
        (extendStage_restrictStage F N a n _ (stageEncoding_bounded F a n N x)).symm
    _ = ((F.into N).app a).f n x := by
      rw [moduleDecoding_extendStage, stageDecoding_restrictStage]

/-- Every finite sum comes from one stage, and the stage inclusions are injective. -/
private theorem moduleDecoding_bijective (a : A.Obj) (n : ℤ) :
    Function.Bijective (moduleDecoding F a n) := by
  constructor
  · apply (injective_iff_map_eq_zero (moduleDecoding F a n)).mpr
    intro x hx
    obtain ⟨N,hN⟩ := sumTerm_bound F a n x
    let y := restrictStage F N a n x
    have hy : extendStage F N a n y = x := extendStage_restrictStage F N a n x hN
    have hz : ((F.into N).app a).f n (stageDecoding F N a n y) = 0 := by
      rw [← moduleDecoding_extendStage, hy, hx]
    have hz' : stageDecoding F N a n y = 0 := by
      apply F.injective N a n
      rw [hz, map_zero]
    rw [← hy, ← stageEncoding_decoding, hz', map_zero]
  · intro x
    obtain ⟨N,y,hy⟩ := F.exhaustive a n x
    exact ⟨stageEncoding F a n N y, (moduleDecoding_stageEncoding F N a n y).trans hy⟩

private def moduleCoordinates (a : A.Obj) (n : ℤ) : (M.complex a).X n ≃ₗ[k] AllTerms F a n :=
  (LinearEquiv.ofBijective (moduleDecoding F a n) (moduleDecoding_bijective F a n)).symm

private theorem moduleCoordinates_into (N : ℕ) (a : A.Obj) (n : ℤ)
    (x : ((F.stage N).complex a).X n) :
    moduleCoordinates F a n (((F.into N).app a).f n x) = stageEncoding F a n N x :=
  (LinearEquiv.symm_apply_eq
    (e := LinearEquiv.ofBijective _ (moduleDecoding_bijective F a n))).mpr
      (moduleDecoding_stageEncoding F N a n x).symm

private def gradedDecomposition : GradedDecomposition (M := M) F where
  stageCoordinates := stageCoordinates F
  coordinates := moduleCoordinates F
  stage_cell := stageCoordinates_cell F
  cell s a n x :=
    (LinearEquiv.symm_apply_eq
      (e := LinearEquiv.ofBijective _ (moduleDecoding_bijective F a n))).mpr
        (moduleDecoding_summand F a n s x).symm
  into N a n x s := by
    rw [moduleCoordinates_into]
    by_cases h : s.1 < N
    · rw [dite_eq_left h, stageCoordinates_apply]
    · rw [dite_eq_right h, stageEncoding_bounded _ _ _ _ _ _ (by omega)]
  stage_coordinate_act N {a b} m n q h x f s :=
    stageEncoding_act F N m n q h x f (stageIndexEmbedding F N s)
  coordinate_act {a b} m n q h x f s := by
    obtain ⟨N,y,hy⟩ := F.exhaustive b m x
    rw [← hy, ← (F.into N).comm_act, moduleCoordinates_into, moduleCoordinates_into]
    exact stageEncoding_act F N m n q h y f s

theorem directSumDecomposition : DirectSumDecomposition.{u,v,w,j} := by
  intro k _ A M F
  exact ⟨gradedDecomposition F, fun a n x =>
    ⟨(moduleCoordinates F a n x).finite_support, sumTerm_bound F a n (moduleCoordinates F a n x)⟩⟩

end Decomposition

end

end DerivedFormalization.DG.CellReindex
