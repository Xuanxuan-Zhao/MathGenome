import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ShiftCone
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Yoneda
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.IndexedSemiFree

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v w j

namespace DerivedFormalization.RightDGModule

open Specs.DerivedFormalization.DG

noncomputable section

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}

abbrev freeCell (a : A.Obj) (n : ℤ) := SemiFree.cell a n
abbrev cellGenerator (a : A.Obj) (n : ℤ) := SemiFree.generator a n
abbrev CellFamily (P : RightDGModule A) (I : Type v) := SemiFree.CellFamily P I
abbrev directSum {I : Type v} (F : I → RightDGModule A) := SemiFree.directSum F
abbrev sumInclusion {I : Type v} (F : I → RightDGModule A) (s : I) := SemiFree.sumInclusion F s

variable {P : RightDGModule A} {I : Type v} (C : CellFamily P I)

abbrev attachCells := SemiFree.attach C
abbrev cellSum := SemiFree.cellSum C
abbrev attachInclusion := SemiFree.inclusion C
abbrev attachProjection := SemiFree.projection C
abbrev attachedGenerator (s : I) := SemiFree.attachedGenerator C s

abbrev SmallSemiFreePresentation (M : RightDGModule A) := SemiFree.Presentation M
def IsSmallSemiFree (M : RightDGModule A) : Prop := Nonempty (SmallSemiFreePresentation M)
def IsSmallFiniteCell (M : RightDGModule A) : Prop :=
  ∃ F : SmallSemiFreePresentation M, Finite (Σ l, F.index l)

abbrev IndexedStrictSum := @IndexedSemiFree.StrictSum.{u,v,w,j}
abbrev IndexedCellFamily := @IndexedSemiFree.CellFamily.{u,v,w,j}
abbrev IndexedAttachment := @IndexedSemiFree.Attachment.{u,v,w,j}
abbrev indexedCellGenerator := @IndexedSemiFree.Attachment.generator.{u,v,w,j}

abbrev SemiFreePresentation := @IndexedSemiFree.Presentation.{u,v,w,j}

def IsSemiFree (M : RightDGModule A) : Prop :=
  Nonempty (SemiFreePresentation.{u,v,w,max v w} M)

def IsFiniteCell (M : RightDGModule A) : Prop :=
  ∃ F : SemiFreePresentation.{u,v,w,max v w} M, Finite (Σ l, F.index l)

@[simp] theorem attachInclusion_f (a : A.Obj) (i : ℤ) (x : (P.complex a).X i) :
    ((attachInclusion C).app a).f i x = (x, 0) := rfl

@[simp] theorem attachProjection_f (a : A.Obj) (i : ℤ)
    (x : ((attachCells C).complex a).X i) :
    ((attachProjection C).app a).f i x = x.2 := rfl

private theorem id_comp_reindexed {a b : A.Obj} (q j r : ℤ)
    (hq : (0 : ℤ) = q) (hr : j = r) (f : (A.hom b a).X j) :
    A.comp q j r (by omega) ((A.hom a a).XIsoOfEq hq |>.hom (A.id a)) f =
      ((A.hom b a).XIsoOfEq hr).hom f := by
  subst q r
  exact A.toData.id_comp j f

theorem cellGenerator_mul (a : A.Obj) (n : ℤ) (b : A.Obj) (j : ℤ) (f : (A.hom b a).X j) :
    (freeCell a n).act n j (n+j) rfl (cellGenerator a n) f =
      ((A.hom b a).XIsoOfEq (by omega : j = n+j + -n)).hom f :=
  id_comp_reindexed (n + -n) j (n+j + -n) (by omega) (by omega) f

@[simp] theorem cellGenerator_d (a : A.Obj) (n : ℤ) :
    ((freeCell a n).complex a).d n (n+1) (cellGenerator a n) = 0 := by
  change ((-n).negOnePow • (A.hom a a).d (n + -n) (n+1 + -n))
    (((A.hom a a).XIsoOfEq (by omega : (0 : ℤ) = n + -n)).hom (A.id a)) = 0
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
  rw [← ModuleCat.comp_apply, XIsoOfEq_hom_comp_d]
  rw [← d_comp_XIsoOfEq_hom _ (by omega : (1 : ℤ) = n+1 + -n) 0]
  rw [ModuleCat.comp_apply, A.toData.d_id, map_zero, smul_zero]

theorem cellGeneratorLaws : SemiFree.CellGeneratorLaws.{u,v,w} := by
  intro k _ A a n
  exact ⟨cellGenerator_d a n, cellGenerator_mul a n⟩

theorem attachmentMatrix : SemiFree.AttachmentMatrix.{u,v,w} := by
  intro k _ A P I C
  refine ⟨SemiFree.attachComplex_d C, fun _ _ _ _ _ _ _ _ => rfl, ?_⟩
  intro a i x
  rw [← ModuleCat.comp_apply, d_comp_d]
  rfl

private theorem act_id_reindexed (P : RightDGModule A) (a : A.Obj) (i q : ℤ)
    (h : (0 : ℤ) = q) (x : (P.complex a).X i) :
    P.act i q i (by omega) x ((A.hom a a).XIsoOfEq h |>.hom (A.id a)) = x := by
  subst q
  exact P.act_id a i x

@[simp] theorem attachedGenerator_d (s : I) :
    ((attachCells C).complex (C.object s)).d (C.degree s) (C.degree s+1) (attachedGenerator C s) =
      ((attachInclusion C).app (C.object s)).f (C.degree s+1) (C.boundary s) := by
  let a := C.object s
  let n := C.degree s
  let e := cellGenerator a n
  let y := SemiFree.summand (SemiFree.cells C) a n s e
  change (SemiFree.attachComplex C a).d n (n+1) (0, y) = (C.boundary s, 0)
  rw [SemiFree.attachComplex_d]
  apply Prod.ext
  · change (P.complex a).d n (n+1) 0 + SemiFree.attachingMap C a n y = C.boundary s
    rw [map_zero, zero_add]
    unfold y
    rw [SemiFree.attachingMap_summand]
    exact act_id_reindexed P a (n+1) _ (by dsimp [n]; omega) (C.boundary s)
  · change ((SemiFree.directSum (SemiFree.cells C)).complex a).d n (n+1) y = 0
    unfold y
    rw [SemiFree.directSum_d_summand]
    change SemiFree.summand (SemiFree.cells C) a (n+1) s
      (((freeCell a n).complex a).d n (n+1) (cellGenerator a n)) = 0
    rw [cellGenerator_d, map_zero]

theorem attachedGenerator_mul (s : I) (a : A.Obj) (j q : ℤ) (h : C.degree s+j = q)
    (f : (A.hom a (C.object s)).X j) :
    (attachCells C).act (C.degree s) j q h (attachedGenerator C s) f =
      (0, SemiFree.summand (SemiFree.cells C) a q s
        (((A.hom a (C.object s)).XIsoOfEq (by omega : j = q + -C.degree s)).hom f)) := by
  subst q
  let n := C.degree s
  let b := C.object s
  change (P.act n j (n+j) rfl 0 f,
    SemiFree.sumAct (SemiFree.cells C) n j (n+j) rfl
      (SemiFree.summand (SemiFree.cells C) b n s (cellGenerator b n)) f) = _
  rw [map_zero, LinearMap.zero_apply, SemiFree.sumAct_summand]
  exact congrArg (fun x => ((0 : (P.complex a).X (n+j)),
    SemiFree.summand (SemiFree.cells C) a (n+j) s x)) (cellGenerator_mul b n a j f)

theorem attachedGenerator_mul_d (s : I) (a : A.Obj) (j q : ℤ) (h : C.degree s+j = q)
    (f : (A.hom a (C.object s)).X j) :
    ((attachCells C).complex a).d q (q+1)
      ((attachCells C).act (C.degree s) j q h (attachedGenerator C s) f) =
      ((attachInclusion C).app a).f (q+1)
        (P.act (C.degree s+1) j (q+1) (by omega) (C.boundary s) f) +
        (C.degree s).negOnePow • (attachCells C).act (C.degree s) (j+1) (q+1) (by omega)
          (attachedGenerator C s) ((A.hom a (C.object s)).d j (j+1) f) := by
  rw [(attachCells C).leibniz, attachedGenerator_d, (attachInclusion C).comm_act]

theorem attachmentFormula : SemiFree.AttachmentFormula.{u,v,w} := by
  intro k _ A P I C s
  exact ⟨attachedGenerator_d C s, fun a j q h f =>
    ⟨attachedGenerator_mul C s a j q h f, attachedGenerator_mul_d C s a j q h f⟩⟩

theorem sumFiniteSupport : SemiFree.FiniteSupport.{u,v,w} := by
  intro k _ A I F a i x
  exact x.finite_support


section Coproduct

variable (F : I → RightDGModule A) {N : RightDGModule A} (g : ∀ s, F s ⟶ N)

private def sumDescLinear (a : A.Obj) (i : ℤ) :
    SemiFree.SumTerm F a i →ₗ[k] (N.complex a).X i := by
  classical
  exact DirectSum.toModule k I _ (fun s => ((g s).app a |>.f i).hom)

@[simp] private theorem sumDescLinear_summand (a : A.Obj) (i : ℤ) (s : I)
    (x : ((F s).complex a).X i) :
    sumDescLinear F g a i (SemiFree.summand F a i s x) = ((g s).app a).f i x := by
  classical
  exact DirectSum.toModule_lof (R := k) (φ := fun t => ((g t).app a |>.f i).hom) s x

/-- Extend a family of strict maps over a sum by linearity. -/
def sumDesc : directSum F ⟶ N where
  app a := CochainComplex.ofHom (fun i => ModuleCat.ofHom (sumDescLinear F g a i)) (by
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (N.complex a).d i (i+1) (sumDescLinear F g a i x) =
      sumDescLinear F g a (i+1) (((directSum F).complex a).d i (i+1) x)
    induction x using SemiFree.sum_induction F with
    | zero => simp
    | single s x =>
      rw [SemiFree.directSum_d_summand, sumDescLinear_summand, sumDescLinear_summand]
      exact CategoryTheory.congr_fun ((g s).app a |>.comm i (i+1)) x
    | add x y hx hy => simp only [map_add, hx, hy])
  comm_act {a b} i j n h x f := by
    change sumDescLinear F g a n (SemiFree.sumAct F i j n h x f) =
      N.act i j n h (sumDescLinear F g b i x) f
    induction x using SemiFree.sum_induction F with
    | zero => simp
    | single s x =>
      rw [SemiFree.sumAct_summand, sumDescLinear_summand, sumDescLinear_summand]
      exact (g s).comm_act i j n h x f
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

@[reassoc (attr := simp)] theorem sumInclusion_desc (s : I) :
    sumInclusion F s ≫ sumDesc F g = g s := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact sumDescLinear_summand F g a i s x

theorem sum_hom_ext {f₁ f₂ : directSum F ⟶ N}
    (h : ∀ s, sumInclusion F s ≫ f₁ = sumInclusion F s ≫ f₂) : f₁ = f₂ := by
  classical
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro s
  exact congrArg (fun (f : F s ⟶ N) => ((f.app a).f i).hom) (h s)

/-- The direct sum with its specified summand inclusions is a strict coproduct. -/
def directSumIsColimit : IsColimit (Cofan.mk (directSum F) (sumInclusion F)) :=
  Cofan.IsColimit.mk _ (fun s => sumDesc F s.inj)
    (fun s i => sumInclusion_desc F s.inj i)
    (fun s _m h => sum_hom_ext F fun i => (h i).trans (sumInclusion_desc F s.inj i).symm)

end Coproduct

theorem directSumCoproduct : SemiFree.Coproduct.{u,v,w} := by
  intro k _ A I F
  exact ⟨directSumIsColimit F⟩

section Quotient

variable {N : RightDGModule A} (g : attachCells C ⟶ N)

private theorem zero_on_previous (hg : attachInclusion C ≫ g = 0) (a : A.Obj) (i : ℤ) (y : (P.complex a).X i) :
    (g.app a).f i (y, 0) = 0 :=
  congrArg (fun (f : P ⟶ N) => (f.app a).f i y) hg

private theorem apply_eq_apply_second (hg : attachInclusion C ≫ g = 0) (a : A.Obj) (i : ℤ) (x : SemiFree.AttachTerm C a i) :
    (g.app a).f i x = (g.app a).f i (0, x.2) := by
  have eq : (x.1, 0) + (0, x.2) = x := by simp
  calc
    (g.app a).f i x = (g.app a).f i ((x.1, 0) + (0, x.2)) := congrArg _ eq.symm
    _ = (g.app a).f i (0, x.2) := by rw [map_add, zero_on_previous C g hg, zero_add]

/-- A strict map annihilating the previous stage factors through the projection. -/
def attachQuotientDesc (hg : attachInclusion C ≫ g = 0) : cellSum C ⟶ N where
  app a := CochainComplex.ofHom
    (fun i => ModuleCat.ofHom (((g.app a).f i).hom.comp (LinearMap.inr k _ _))) (by
      intro i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (N.complex a).d i (i+1) ((g.app a).f i (0, x)) =
        (g.app a).f (i+1) (0, ((cellSum C).complex a).d i (i+1) x)
      calc
        _ = (g.app a).f (i+1) ((SemiFree.attachComplex C a).d i (i+1) (0, x)) :=
          CategoryTheory.congr_fun ((g.app a).comm i (i+1)) ((0, x) : SemiFree.AttachTerm C a i)
        _ = _ := by
          rw [apply_eq_apply_second C g hg a (i+1), SemiFree.attachComplex_d])
  comm_act {a b} i j n h x f := by
    change (g.app a).f n (0, (cellSum C).act i j n h x f) =
      N.act i j n h ((g.app b).f i (0, x)) f
    have eq := g.comm_act i j n h ((0, x) : SemiFree.AttachTerm C b i) f
    change (g.app a).f n (P.act i j n h 0 f, (cellSum C).act i j n h x f) = _ at eq
    rwa [map_zero, LinearMap.zero_apply] at eq

theorem attachProjection_desc (hg : attachInclusion C ≫ g = 0) : attachProjection C ≫ attachQuotientDesc C g hg = g := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (apply_eq_apply_second C g hg a i x).symm

end Quotient

theorem attachInclusion_projection : attachInclusion C ≫ attachProjection C = 0 := rfl

def attachmentIsCokernel :
    IsColimit (CokernelCofork.ofπ (attachProjection C) (attachInclusion_projection C)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun g h => attachQuotientDesc C g h) (fun g h => attachProjection_desc C g h) (by
      intro N g hg m h
      apply RightDGModuleModel.hom_ext
      intro a
      apply HomologicalComplex.Hom.ext
      funext i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact congrArg (fun (f : attachCells C ⟶ N) => (f.app a).f i (0, x)) h)

theorem attachmentQuotient : SemiFree.AttachmentQuotient.{u,v,w} := by
  intro k _ A P I C
  refine ⟨?_, attachInclusion_projection C, ⟨attachmentIsCokernel C⟩⟩
  intro a i
  refine ⟨fun _ _ h => congrArg Prod.fst h, fun x => ⟨(0, x), rfl⟩, ?_⟩
  intro x
  change x.2 = 0 ↔ ∃ y : (P.complex a).X i, (y, 0) = x
  exact ⟨fun h => ⟨x.1, Prod.ext rfl h.symm⟩,
    fun ⟨y, h⟩ => (congrArg Prod.snd h).symm⟩


section PresentationSupport

variable {M : RightDGModule A} (F : SmallSemiFreePresentation M) (a : A.Obj) (i : ℤ)

private def stageCellSumMap (j : ℕ) :
    SemiFree.SumTerm (SemiFree.cells (F.family j)) a i →ₗ[k] SemiFree.PresentationTerm F a i := by
  classical
  exact DirectSum.toModule k (F.index j) _ fun s =>
    DirectSum.lof k _ (fun t : Σ l, F.index l =>
      ((SemiFree.cells (F.family t.1) t.2).complex a).X i) ⟨j, s⟩

private theorem presentationSumMap_stage (j : ℕ)
    (y : SemiFree.SumTerm (SemiFree.cells (F.family j)) a i) :
    SemiFree.presentationSumMap F a i (stageCellSumMap F a i j y) =
      (((F.successor j).hom ≫ F.into (j+1)).app a).f i (0, y) := by
  classical
  induction y using SemiFree.sum_induction (SemiFree.cells (F.family j)) with
  | zero =>
    change _ = (((F.successor j).hom ≫ F.into (j+1)).app a).f i 0
    simp
  | single s z =>
    unfold stageCellSumMap SemiFree.presentationSumMap
    rw [SemiFree.summand, DirectSum.toModule_lof, DirectSum.toModule_lof]
    rfl
  | add y z hy hz =>
    rw [map_add, map_add, hy, hz, ← map_add]
    simp

private theorem presentationSumMap_stage_into (j : ℕ) (x : ((F.stage j).complex a).X i) :
    ∃ y : SemiFree.PresentationTerm F a i,
      SemiFree.presentationSumMap F a i y = ((F.into j).app a).f i x := by
  induction j with
  | zero =>
    refine ⟨0, ?_⟩
    rw [map_zero, F.bottom a i x, map_zero]
  | succ j ih =>
    let p := ((F.successor j).inv.app a).f i x
    have hp : ((F.successor j).hom.app a).f i p = x :=
      congrArg (fun (f : F.stage (j+1) ⟶ F.stage (j+1)) => (f.app a).f i x)
        (F.successor j).inv_hom_id
    obtain ⟨y, hy⟩ := ih p.1
    refine ⟨y + stageCellSumMap F a i j p.2, ?_⟩
    rw [map_add, hy, presentationSumMap_stage]
    have h := congrArg (fun (f : F.stage j ⟶ M) => (f.app a).f i p.1) (F.compatible j)
    change (((F.successor j).hom ≫ F.into (j+1)).app a).f i (p.1, 0) =
      ((F.into j).app a).f i p.1 at h
    rw [← h, ← map_add]
    have hpair : (p.1, 0) + (0, p.2) = p := by simp
    rw [hpair]
    exact congrArg ((F.into (j+1)).app a |>.f i) hp

end PresentationSupport

/-- Every homogeneous element has finite support in the cells of the entire filtration. -/
theorem presentationFiniteSupport : SemiFree.PresentationFiniteSupport.{u,v,w} := by
  intro k _ A M F a i x
  obtain ⟨j, z, hz⟩ := F.exhaustive a i x
  obtain ⟨y, hy⟩ := presentationSumMap_stage_into F a i j z
  exact ⟨y, hy.trans hz, y.finite_support⟩

end
end DerivedFormalization.RightDGModule
