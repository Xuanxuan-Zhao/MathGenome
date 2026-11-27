import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CellReindex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CellLift
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u v w j t

namespace DerivedFormalization.DG.CellLift

open Specs.DerivedFormalization.DG.CellLift
open Specs.DerivedFormalization.DG.IndexedSemiFree
open Specs.DerivedFormalization.DG.CellReindex
open Specs.DerivedFormalization.DG.CoefficientLift
open IndexedCellAttachment (liftAttachment)
open private liftTerm_summand from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.IndexedSums
open private boundaryMap_summand from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.IndexedCellAttachment

noncomputable section

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
  {M : RightDGModuleModel A}

private theorem hom_ext {P Q : RightDGModuleModel A} {f g : P ⟶ Q}
    (h : ∀ a n x, (f.app a).f n x = (g.app a).f n x) : f = g := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro n
  exact ModuleCat.hom_ext (LinearMap.ext (h a n))

private abbrev liftExtensions (F : Presentation.{u,v,w,j} M) : LiftedExtensions.{u,v,w,j,t} F where
  extension l := liftAttachment (F.extension l)
  inclusion _ := rfl

/-- Coefficient transport on the very stages and maps of the given presentation. -/
abbrev liftPresentation (F : Presentation.{u,v,w,j} M) :
    Presentation.{u,max v t,w,j} (liftModule.{u,v,w,t} M) :=
  (liftExtensions F).toPresentation

private theorem projection_exact {P Q S : RightDGModuleModel A} {I : Type j}
    {C : CellFamily P I} (E : Attachment C Q) (s : StrictSum (cells C) S) (a : A.Obj) (n : ℤ) :
    Function.Injective ((E.inclusion.app a).f n) ∧
      Function.Surjective (((IndexedCellAttachment.projection E s).app a).f n) ∧
      ∀ x, ((IndexedCellAttachment.projection E s).app a).f n x = 0 ↔
        ∃ y, (E.inclusion.app a).f n y = x := by
  refine ⟨?_, fun z => ⟨_, IndexedCellAttachment.projection_section E s a n z⟩, ?_⟩
  · intro x y h
    exact congrArg Prod.fst ((E.coordinate_inclusion a n x).symm.trans
      ((congrArg (E.coordinates a n) h).trans (E.coordinate_inclusion a n y)))
  · intro x
    rw [← (s.coordinates a n).map_eq_zero_iff, IndexedCellAttachment.projection_coordinates]
    constructor
    · intro h
      refine ⟨(E.coordinates a n x).1, (E.coordinates a n).injective ?_⟩
      rw [E.coordinate_inclusion]
      exact Prod.ext rfl h.symm
    · rintro ⟨y, rfl⟩
      rw [E.coordinate_inclusion]

private theorem isCokernel_of_projection {P Q S : RightDGModuleModel A} {I : Type j}
    {C : CellFamily P I} (E : Attachment C Q) (s : StrictSum (cells C) S)
    (p : Q ⟶ S) (hp : p = IndexedCellAttachment.projection E s) (h : E.inclusion ≫ p = 0) :
    Nonempty (IsColimit (CokernelCofork.ofπ p h)) := by
  subst p
  exact ⟨IndexedCellAttachment.projectionIsCokernel E s⟩

private theorem attachmentLaws (F : Presentation.{u,v,w,j} M) :
    AttachmentLaws (liftExtensions.{u,v,w,j,t} F) := by
  refine ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun l => IndexedCellAttachment.liftAttachment_generator (F.extension l), ?_⟩
  intro l
  let E := F.extension l
  let D := liftAttachment.{u,v,w,j,t} E
  let s := IndexedSums.sumRealization (cells (F.family l)) (IndexedCellAttachment.termsSmall E)
  let r := IndexedSums.liftStrictSum.{u,v,w,j,t} s
  let p := IndexedCellAttachment.projection E s
  have hp : liftMap.{u,v,w,t} p = IndexedCellAttachment.projection D r := by
    apply hom_ext
    intro a n x
    apply (r.coordinates a n).injective
    refine Eq.trans ?_ (IndexedCellAttachment.projection_coordinates D r a n x).symm
    apply DFinsupp.ext
    intro i
    apply ULift.ext
    exact congrArg (fun z => z i) (IndexedCellAttachment.projection_coordinates E s a n x.down)
  have h' : D.inclusion ≫ liftMap.{u,v,w,t} p = 0 :=
    hp ▸ IndexedCellAttachment.inclusion_projection D r
  refine ⟨_, s, r, p, IndexedCellAttachment.inclusion_projection E s, h',
    ⟨IndexedCellAttachment.projectionIsCokernel E s⟩, ⟨IndexedSums.isColimit r⟩, isCokernel_of_projection D r _ hp h',
    fun _ => rfl, fun _ _ _ _ => rfl, IndexedCellAttachment.projection_coordinates E s, ?_, ?_⟩
  · rw [hp]
    exact IndexedCellAttachment.projection_coordinates D r
  · rw [hp]
    exact projection_exact D r

private theorem lift_stageInclusion (F : Presentation.{u,v,w,j} M) {l N : ℕ} (h : l ≤ N) :
    stageInclusion (liftPresentation.{u,v,w,j,t} F) h =
      liftMap.{u,v,w,t} (stageInclusion F h) := by
  let T := liftFunctor.{u,v,w,t} A
  induction N, h using Nat.le_induction with
  | base =>
    unfold stageInclusion
    rw [Functor.OfSequence.map_id, Functor.OfSequence.map_id]
    exact (T.map_id _).symm
  | succ N h ih =>
    have hs (G : Presentation M) :
        stageInclusion G (h.trans (Nat.le_succ N)) =
          stageInclusion G h ≫ (G.extension N).inclusion := by
      unfold stageInclusion
      rw [Functor.OfSequence.map_comp _ l N (N+1) h (Nat.le_succ N),
        Functor.OfSequence.map_le_succ]
    have hs' : stageInclusion (liftPresentation.{u,v,w,j,t} F) (h.trans (Nat.le_succ N)) =
        stageInclusion (liftPresentation.{u,v,w,j,t} F) h ≫
          ((liftPresentation.{u,v,w,j,t} F).extension N).inclusion := by
      unfold stageInclusion
      rw [Functor.OfSequence.map_comp _ l N (N+1) h (Nat.le_succ N),
        Functor.OfSequence.map_le_succ]
    rw [hs', hs, ih]
    exact (T.map_comp _ _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem lift_cellToSuccessor (F : Presentation.{u,v,w,j} M)
    (l : ℕ) (i : F.index l) (a : A.Obj) (n : ℤ) (x : ((cells (F.family l) i).complex a).X n) :
    cellToSuccessor (liftPresentation.{u,v,w,j,t} F) l i a n (ULift.up x) =
      ULift.up (cellToSuccessor F l i a n x) := by
  let D := (liftPresentation.{u,v,w,j,t} F).extension l
  apply (D.coordinates a n).injective
  have h := ((F.extension l).coordinates a n).apply_symm_apply
    (0, summand (cells (F.family l)) a n i x)
  change D.coordinates a n ((D.coordinates a n).symm
    (0, summand (cells (liftPresentation.{u,v,w,j,t} F |>.family l)) a n i (ULift.up x))) = _
  rw [LinearEquiv.apply_symm_apply]
  have h' : D.coordinates a n (ULift.up (cellToSuccessor F l i a n x)) =
      (ULift.up (0 : ((F.stage l).complex a).X n),
        IndexedSums.liftTerm.{u,v,w,j,t} (cells (F.family l)) a n
          (summand (cells (F.family l)) a n i x)) :=
    congrArg ((ULift.moduleEquiv.symm : _ ≃ₗ[k] _).prodCongr
      (IndexedSums.liftTerm.{u,v,w,j,t} (cells (F.family l)) a n)) h
  refine Eq.trans ?_ h'.symm
  apply Prod.ext
  · rfl
  · exact (liftTerm_summand (F := cells (F.family l)) i a n x).symm

set_option backward.isDefEq.respectTransparency false in
private def liftDecomposition (F : Presentation.{u,v,w,j} M) (D : GradedDecomposition F) :
    GradedDecomposition (liftPresentation.{u,v,w,j,t} F) where
  stageCoordinates N a n := ULift.moduleEquiv.trans
    ((D.stageCoordinates N a n).trans (IndexedSums.liftTerm.{u,v,w,j,t} (stageCells F N) a n))
  coordinates a n := ULift.moduleEquiv.trans
    ((D.coordinates a n).trans (IndexedSums.liftTerm.{u,v,w,j,t} (allCells F) a n))
  stage_cell N s a n x := by
    have h : cellToStage (liftPresentation.{u,v,w,j,t} F) N s a n x =
        ULift.up (cellToStage F N s a n x.down) := by
      unfold cellToStage
      change ((stageInclusion (liftPresentation.{u,v,w,j,t} F) _).app a).f n
        (cellToSuccessor (liftPresentation.{u,v,w,j,t} F) s.1.val s.2 a n x) = _
      rw [lift_stageInclusion]
      apply ULift.ext
      exact congrArg (fun y =>
        ((stageInclusion F (Nat.succ_le_of_lt s.1.isLt)).app a).f n y.down)
        (lift_cellToSuccessor.{u,v,w,j,t} F s.1.val s.2 a n x.down)
    rw [h]
    change IndexedSums.liftTerm.{u,v,w,j,t} (stageCells F N) a n
      (D.stageCoordinates N a n (cellToStage F N s a n x.down)) = _
    refine (congrArg (IndexedSums.liftTerm.{u,v,w,j,t} (stageCells F N) a n)
      (D.stage_cell N s a n x.down)).trans ?_
    exact liftTerm_summand (F := stageCells F N) s a n x.down
  cell s a n x := by
    have h : cellToModule (liftPresentation.{u,v,w,j,t} F) s a n x =
        ULift.up (cellToModule F s a n x.down) := by
      unfold cellToModule
      change ((liftMap.{u,v,w,t} (F.into (s.1+1))).app a).f n
        (cellToSuccessor (liftPresentation.{u,v,w,j,t} F) s.1 s.2 a n x) = _
      exact congrArg (fun y => ((liftMap.{u,v,w,t} (F.into (s.1+1))).app a).f n y)
        (lift_cellToSuccessor.{u,v,w,j,t} F s.1 s.2 a n x.down)
    rw [h]
    change IndexedSums.liftTerm.{u,v,w,j,t} (allCells F) a n
      (D.coordinates a n (cellToModule F s a n x.down)) = _
    refine (congrArg (IndexedSums.liftTerm.{u,v,w,j,t} (allCells F) a n)
      (D.cell s a n x.down)).trans ?_
    exact liftTerm_summand (F := allCells F) s a n x.down
  into N a n x s := by
    apply ULift.ext
    by_cases h : s.1 < N
    · rw [dite_eq_left h]
      exact (D.into N a n x.down s).trans (dite_eq_left h)
    · rw [dite_eq_right h]
      exact (D.into N a n x.down s).trans (dite_eq_right h)
  stage_coordinate_act N {a b} m n q h x f s := ULift.ext
    (D.stage_coordinate_act N m n q h x.down f.down s)
  coordinate_act {a b} m n q h x f s := ULift.ext (D.coordinate_act m n q h x.down f.down s)

theorem presentationTransport : PresentationTransport.{u,v,w,j,t} := by
  intro k _ A M F
  obtain ⟨D, hD⟩ := CellReindex.directSumDecomposition F
  refine ⟨liftExtensions F, attachmentLaws F, ⟨D, liftDecomposition F D, ?_⟩⟩
  refine ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, ?_⟩
  intro a n x
  obtain ⟨hf, N, hN⟩ := hD a n x.down
  refine ⟨hf.subset (fun i hi hz => hi (ULift.ext hz)), N, fun i hi => ULift.ext (hN i hi)⟩

theorem semiFreeTransport : SemiFreeTransport.{u,v,w,t} := by
  rintro k _ A M ⟨F⟩
  obtain ⟨R, _⟩ := CellReindex.normalize (liftPresentation.{u,v,w,max v w,t} F)
  exact ⟨R.toPresentation⟩

section Pullback

variable {P : RightDGModuleModel A}
  {Q R : RightDGModuleModel (liftCategory.{u,v,w,t} A)}
  {I : Type j} {J : Type v} {C : CellFamily Q I}
  (r : J ≃ I) (e : liftModule.{u,v,w,t} P ≅ Q)

private abbrev pulledFamily :=
  Specs.DerivedFormalization.DG.IndexedCellAttachment.liftFamily.{u,v,w,v,t}
    (pullbackFamily C r e)

private def relabelCells (a : A.Obj) (n : ℤ) :
    CellTerm C a n ≃ₗ[k] CellTerm (pulledFamily (C := C) r e) a n :=
  DirectSum.lequivCongrLeft k r.symm

private theorem relabelCells_apply (a : A.Obj) (n : ℤ)
    (y : CellTerm C a n) (i : J) :
    relabelCells r e a n y i = y (r i) :=
  DirectSum.lequivCongrLeft_apply k r.symm y i

private theorem relabelCells_symm_summand (a : A.Obj) (n : ℤ) (i : J)
    (y : ((cells C (r i)).complex a).X n) :
    (relabelCells r e a n).symm
      (summand (cells (pulledFamily (C := C) r e)) a n i y) =
        summand (cells C) a n (r i) y := by
  classical
  exact DirectSum.lequivCongrLeft_symm_lof k

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_boundaryMap (a : A.Obj) (n : ℤ)
    (y : CellTerm C a n) :
    boundaryMap (pulledFamily (C := C) r e) a n (relabelCells r e a n y) =
      (e.inv.app a).f (n+1) (boundaryMap C a n y) := by
  let B := pulledFamily (C := C) r e
  let f := ((e.inv.app a).f (n+1)).hom
  let h := relabelCells (C := C) r e a n
  suffices hb : boundaryMap B a n = f.comp ((boundaryMap C a n).comp h.symm.toLinearMap) by
    change boundaryMap B a n (h y) = _
    rw [hb]
    exact congrArg (fun z => f (boundaryMap C a n z)) (h.symm_apply_apply y)
  classical
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro z
  change boundaryMap B a n (summand (cells B) a n i z) =
    f (boundaryMap C a n (h.symm (summand (cells B) a n i z)))
  rw [relabelCells_symm_summand r e, boundaryMap_summand, boundaryMap_summand]
  exact (e.inv.comm_act (C.degree (r i)+1) (n + -C.degree (r i)) (n+1)
    (by omega) (C.boundary (r i)) z).symm

set_option backward.isDefEq.respectTransparency false in
private def pullbackAttachment (E : Attachment C R) :
    Attachment (pulledFamily (C := C) r e) R where
  inclusion := e.hom ≫ E.inclusion
  coordinates a n := (E.coordinates a n).trans
    ((((RightDGModuleModel.degree a n).mapIso e.symm).toLinearEquiv).prodCongr (relabelCells r e a n))
  coordinate_inclusion a n x := by
    let y := (e.hom.app a).f n x
    change ((e.inv.app a).f n (E.coordinates a n ((E.inclusion.app a).f n y)).1,
      relabelCells r e a n (E.coordinates a n ((E.inclusion.app a).f n y)).2) = (x, 0)
    rw [E.coordinate_inclusion, map_zero]
    exact Prod.ext (congrArg (fun g : liftModule.{u,v,w,t} P ⟶ liftModule.{u,v,w,t} P =>
      (g.app a).f n x) e.hom_inv_id) rfl
  coordinate_d a n x := by
    have hd := E.coordinate_d a n x
    dsimp only at hd ⊢
    constructor
    · let y := E.coordinates a n x
      change (e.inv.app a).f (n+1) (E.coordinates a (n+1) ((R.complex a).d n (n+1) x)).1 =
        ((liftModule.{u,v,w,t} P).complex a).d n (n+1) ((e.inv.app a).f n y.1) +
          boundaryMap (pulledFamily (C := C) r e) a n (relabelCells r e a n y.2)
      rw [hd.1, map_add, pullback_boundaryMap]
      exact congrArg (fun z => z + (e.inv.app a).f (n+1) (boundaryMap C a n y.2))
        (CategoryTheory.congr_fun ((e.inv.app a).comm n (n+1)) y.1).symm
    · intro i
      change relabelCells r e a (n+1) (E.coordinates a (n+1) ((R.complex a).d n (n+1) x)).2 i =
        ((cells C (r i)).complex a).d n (n+1) (relabelCells r e a n (E.coordinates a n x).2 i)
      rw [relabelCells_apply, relabelCells_apply]
      exact hd.2 (r i)
  coordinate_act {a b} m n q h x f := by
    have ha := E.coordinate_act m n q h x f
    dsimp only at ha ⊢
    constructor
    · change (e.inv.app a).f q (E.coordinates a q (R.act m n q h x f)).1 =
        (liftModule.{u,v,w,t} P).act m n q h ((e.inv.app b).f m (E.coordinates b m x).1) f
      rw [ha.1]
      exact e.inv.comm_act m n q h (E.coordinates b m x).1 f
    · intro i
      change relabelCells r e a q (E.coordinates a q (R.act m n q h x f)).2 i =
        (cells C (r i)).act m n q h (relabelCells r e b m (E.coordinates b m x).2 i) f
      rw [relabelCells_apply, relabelCells_apply]
      exact ha.2 (r i)

end Pullback

section Terminal

variable {P Q : RightDGModuleModel A}

/-- A strict map that is bijective in every degree has a strict inverse. -/
private def isoOfDegreewiseBijective (f : P ⟶ Q)
    (hf : ∀ a n, Function.Bijective ((f.app a).f n)) : P ≅ Q :=
  CoefficientLift.isoOfComponents
    (fun a n => LinearEquiv.ofBijective ((f.app a).f n).hom (hf a n))
    (fun a n x => (CategoryTheory.congr_fun ((f.app a).comm n (n+1)) x).symm)
    (fun _ _ _ _ x g => f.comm_act _ _ _ _ x g)

private theorem isoOfDegreewiseBijective_hom (f : P ⟶ Q) (hf) :
    (isoOfDegreewiseBijective f hf).hom = f :=
  hom_ext fun _ _ _ => rfl

private theorem exists_terminal_stage (F : Presentation.{u,v,w,j} M)
    (hF : Finite (Σ l, F.index l)) : ∃ N, IsIso (F.into N) := by
  classical
  have := hF
  obtain ⟨b, hb⟩ := (Set.finite_range (fun i : Σ l, F.index l => i.1)).bddAbove
  let N := b + 1
  have hN (i : Σ l, F.index l) : i.1 < N := Nat.lt_succ_of_le (hb ⟨i, rfl⟩)
  obtain ⟨D, _⟩ := CellReindex.directSumDecomposition F
  have hbij (a : A.Obj) (n : ℤ) : Function.Bijective ((F.into N).app a |>.f n) := by
    refine ⟨F.injective N a n, ?_⟩
    intro x
    let f : StageIndex F N → Σ l, F.index l := fun i => ⟨i.1.val, i.2⟩
    have hf : Function.Injective f := by
      rintro ⟨⟨l, hl⟩, i⟩ ⟨⟨m, hm⟩, z⟩ h
      obtain rfl : l = m := congrArg Sigma.fst h
      obtain rfl : i = z := (Sigma.mk.inj_iff.mp h).2.eq
      rfl
    let y : SumTerm (stageCells F N) a n := DFinsupp.comapDomain f hf (D.coordinates a n x)
    let z := (D.stageCoordinates N a n).symm y
    refine ⟨z, (D.coordinates a n).injective (DFinsupp.ext fun i => ?_)⟩
    rw [D.into, dite_eq_left (hN i), LinearEquiv.apply_symm_apply]
    exact DFinsupp.comapDomain_apply f hf (D.coordinates a n x) ⟨⟨i.1, hN i⟩, i.2⟩
  refine ⟨N, ?_⟩
  rw [← isoOfDegreewiseBijective_hom (F.into N) hbij]
  infer_instance

private theorem isZero_of_terms (h : ∀ a n (x : (P.complex a).X n), x = 0) : IsZero P := by
  rw [IsZero.iff_id_eq_zero]
  exact hom_ext h

end Terminal

section DescendedStages

variable {L : RightDGModuleModel (liftCategory.{u,v,w,t} A)}
  (F : Presentation.{u,max v t,w,j} L)

private abbrev StageComparison (l : ℕ) :=
  Σ P : RightDGModuleModel A, liftModule.{u,v,w,t} P ≅ F.stage l

private def nativeSuccessor {l : ℕ} {J : Type v}
    (s : StageComparison F l) (r : J ≃ F.index l) : RightDGModuleModel A :=
  Specs.DerivedFormalization.DG.SemiFree.attach (smallFamily (pullbackFamily (F.family l) r s.2))

private def nativeExtension {l : ℕ} {J : Type v}
    (s : StageComparison F l) (r : J ≃ F.index l) :
    Attachment (pullbackFamily (F.family l) r s.2) (nativeSuccessor F s r) :=
  IndexedCellAttachment.nativeAttachment (smallFamily (pullbackFamily (F.family l) r s.2))

private def successorComparison {l : ℕ} {J : Type v}
    (s : StageComparison F l) (r : J ≃ F.index l) :
    liftModule.{u,v,w,t} (nativeSuccessor F s r) ≅ F.stage (l+1) :=
  IndexedCellAttachment.comparisonIso (liftAttachment (nativeExtension F s r))
    (pullbackAttachment r s.2 (F.extension l))

private theorem successorComparison_inclusion {l : ℕ} {J : Type v}
    (s : StageComparison F l) (r : J ≃ F.index l) :
    liftMap.{u,v,w,t} (nativeExtension F s r).inclusion ≫ (successorComparison F s r).hom =
      s.2.hom ≫ (F.extension l).inclusion :=
  IndexedCellAttachment.inclusion_comparisonIso _ _

private def descendStages {J : ℕ → Type v} (r : ∀ l, J l ≃ F.index l)
    (s₀ : StageComparison F 0) : ∀ l, StageComparison F l
  | 0 => s₀
  | l+1 =>
    let s := descendStages r s₀ l
    ⟨nativeSuccessor F s (r l), successorComparison F s (r l)⟩

end DescendedStages

set_option backward.isDefEq.respectTransparency false in
theorem finiteDescent : FiniteDescent.{u,v,w,j,t} := by
  intro k _ A L F hF
  classical
  have := hF
  have hfin (l : ℕ) : Finite (F.index l) :=
    Finite.of_injective (fun i => (⟨l, i⟩ : Σ m, F.index m))
      (fun _ _ h => (Sigma.mk.inj_iff.mp h).2.eq)
  let (l : ℕ) : Fintype (F.index l) := Fintype.ofFinite _
  let J (l : ℕ) : Type v := ULift.{v} (Fin (Fintype.card (F.index l)))
  let r (l : ℕ) : J l ≃ F.index l := Equiv.ulift.trans (Fintype.equivFin _).symm
  obtain ⟨Z, _, _, hZ⟩ := IndexedSums.emptyFamily (fun i : PEmpty.{1} => (isEmptyElim i : RightDGModuleModel A))
  let e₀ : liftModule.{u,v,w,t} Z ≅ F.stage 0 :=
    (isZero_of_terms (P := liftModule.{u,v,w,t} Z)
      (fun a n x => ULift.ext (hZ a n x.down))).iso (isZero_of_terms F.bottom)
  let s := descendStages F r ⟨Z, e₀⟩
  obtain ⟨N, hN⟩ := exists_terminal_stage F hF
  let T := liftFunctor.{u,v,w,t} A
  let ff := CoefficientLift.liftFullyFaithful.{u,v,w,t} A
  let P := (s N).1
  let terminal : liftModule.{u,v,w,t} P ≅ L := (s N).2 ≪≫ asIso (F.into N)
  let into (l : ℕ) : (s l).1 ⟶ P :=
    ff.preimage ((s l).2.hom ≫ F.into l ≫ terminal.inv)
  have hInto (l : ℕ) :
      T.map (into l) ≫ terminal.hom = (s l).2.hom ≫ F.into l := by
    dsimp only [into]
    rw [ff.map_preimage]
    simp
  let ext (l : ℕ) :
      Attachment (pullbackFamily (F.family l) (r l) (s l).2) (s (l+1)).1 :=
    nativeExtension F (s l) (r l)
  have hExt (l : ℕ) : T.map (ext l).inclusion ≫ (s (l+1)).2.hom =
      (s l).2.hom ≫ (F.extension l).inclusion :=
    successorComparison_inclusion F (s l) (r l)
  have hTop : into N = 𝟙 P := by
    apply ff.map_injective
    apply (cancel_mono terminal.hom).1
    rw [hInto, T.map_id, Category.id_comp]
    rfl
  let G : Presentation.{u,v,w,v} P :=
    { stage := fun l => (s l).1
      bottom := hZ
      index := J
      family := fun l => pullbackFamily (F.family l) (r l) (s l).2
      extension := ext
      into := into
      compatible := fun l => by
        apply ff.map_injective
        apply (cancel_mono terminal.hom).1
        rw [T.map_comp, Category.assoc, hInto, hInto, ← Category.assoc, hExt,
          Category.assoc, F.compatible]
      injective := fun l a n x y h => by
        have hx := congrArg (fun f : T.obj (s l).1 ⟶ L => (f.app a).f n (ULift.up x)) (hInto l)
        have hy := congrArg (fun f : T.obj (s l).1 ⟶ L => (f.app a).f n (ULift.up y)) (hInto l)
        change (terminal.hom.app a).f n (ULift.up (((into l).app a).f n x)) =
          ((F.into l).app a).f n (((s l).2.hom.app a).f n (ULift.up x)) at hx
        change (terminal.hom.app a).f n (ULift.up (((into l).app a).f n y)) =
          ((F.into l).app a).f n (((s l).2.hom.app a).f n (ULift.up y)) at hy
        rw [h] at hx
        have he := F.injective l a n (hx.symm.trans hy)
        let degree := RightDGModuleModel.degree (A := liftCategory.{u,v,w,t} A) a n
        have hu : (ULift.up x : ((T.obj (s l).1).complex a).X n) = ULift.up y :=
          ((degree.mapIso (s l).2).toLinearEquiv.injective) he
        exact congrArg ULift.down hu
      exhaustive := fun a n x =>
        ⟨N, x, by rw [hTop]; rfl⟩ }
  refine ⟨P, G, Finite.of_equiv _ (Equiv.sigmaCongrRight r).symm, ?_⟩
  exact ⟨⟨r, fun l => (s l).2, fun _ => rfl, hExt, terminal, hInto⟩⟩

/-- Postcomposition by a strict isomorphism retains all stages and cell data. -/
private def presentationOfIso {Q : RightDGModuleModel A} (F : Presentation.{u,v,w,j} M)
    (e : M ≅ Q) : Presentation.{u,v,w,j} Q where
  stage := F.stage
  bottom := F.bottom
  index := F.index
  family := F.family
  extension := F.extension
  into l := F.into l ≫ e.hom
  compatible l := by rw [← Category.assoc, F.compatible]
  injective l a n := ((RightDGModuleModel.degree a n).mapIso e).toLinearEquiv.injective.comp
    (F.injective l a n)
  exhaustive a n x := by
    obtain ⟨l, y, hy⟩ := F.exhaustive a n ((e.inv.app a).f n x)
    refine ⟨l, y, ?_⟩
    change (e.hom.app a).f n (((F.into l).app a).f n y) = x
    rw [hy]
    exact congrArg (fun f : Q ⟶ Q => (f.app a).f n x) e.inv_hom_id

theorem finiteCellTransport : FiniteCellTransport.{u,v,w,t} := by
  intro k _ A L
  constructor
  · rintro ⟨F, hF⟩
    obtain ⟨M, G, hG, ⟨D⟩⟩ := finiteDescent F hF
    obtain ⟨R, hR⟩ := CellReindex.normalize G
    exact ⟨M, ⟨R.toPresentation, hR hG⟩, ⟨D.terminal⟩⟩
  · rintro ⟨M, ⟨F, hF⟩, ⟨e⟩⟩
    let G := presentationOfIso (liftPresentation.{u,v,w,max v w,t} F) e
    obtain ⟨R, hR⟩ := CellReindex.normalize G
    exact ⟨R.toPresentation, hR hF⟩

end

end DerivedFormalization.DG.CellLift
