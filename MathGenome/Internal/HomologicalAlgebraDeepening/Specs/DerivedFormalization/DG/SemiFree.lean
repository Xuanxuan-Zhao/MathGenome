import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.ShiftCone
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.Yoneda
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Limits.Shapes.Products

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u v w

namespace Specs.DerivedFormalization.DG.SemiFree

open _root_.DerivedFormalization
open ShiftCone (shift)
open Yoneda (representable)

noncomputable section

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}

/-- A homogeneous free cell with its usual cochain differential. -/
abbrev cell (a : A.Obj) (n : ℤ) := shift (representable a) (-n)

/-- The shifted identity is the distinguished generator of the cell. -/
def generator (a : A.Obj) (n : ℤ) : ((cell a n).complex a).X n :=
  (A.hom a a).XIsoOfEq (by omega : (0 : ℤ) = n + -n) |>.hom (A.id a)

/-- A set of cells and their closed attaching elements in the preceding module.
The index type is small in the universe of the modules, with no finiteness condition. -/
structure CellFamily (P : RightDGModuleModel A) (I : Type v) where
  object : I → A.Obj
  degree : I → ℤ
  boundary (s : I) : (P.complex (object s)).X (degree s + 1)
  closed (s : I) : (P.complex (object s)).d (degree s + 1) (degree s + 1 + 1) (boundary s) = 0

section Sum

variable {I : Type v} (F : I → RightDGModuleModel A)

abbrev SumTerm (a : A.Obj) (i : ℤ) := ⨁ s : I, ((F s).complex a).X i

def sumStep (a : A.Obj) (i : ℤ) :
    ModuleCat.of k (SumTerm F a i) ⟶ ModuleCat.of k (SumTerm F a (i+1)) :=
  ModuleCat.ofHom (DirectSum.lmap fun s => ((F s).complex a).d i (i+1) |>.hom)

private theorem d_d_apply (C : ModuleCochain.{u,v} k) (i j l : ℤ) (x : C.X i) :
    C.d j l (C.d i j x) = 0 := by
  rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_d]
  rfl

@[reducible] def sumComplex (a : A.Obj) : ModuleCochain.{u,v} k :=
  CochainComplex.of (fun i => ModuleCat.of k (SumTerm F a i)) (sumStep F a) (by
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro s
    exact d_d_apply ((F s).complex a) i (i+1) (i+1+1) (x s))

def sumAct {a b : A.Obj} (i j n : ℤ) (h : i+j = n) :
    SumTerm F b i →ₗ[k] (A.hom a b).X j →ₗ[k] SumTerm F a n :=
  LinearMap.flip
    { toFun := fun f => DirectSum.lmap fun s => ((F s).act i j n h).flip f
      map_add' := by
        intro f g
        apply LinearMap.ext
        intro x
        apply DFinsupp.ext
        intro s
        exact map_add ((F s).act i j n h (x s)) f g
      map_smul' := by
        intro c f
        apply LinearMap.ext
        intro x
        apply DFinsupp.ext
        intro s
        exact map_smul ((F s).act i j n h (x s)) c f }

@[simp] theorem sumAct_apply {a b : A.Obj} (i j n : ℤ) (h : i+j = n)
    (x : SumTerm F b i) (f : (A.hom a b).X j) (s : I) :
    sumAct F i j n h x f s = (F s).act i j n h (x s) f := rfl

/-- Strict sums, with finite support at each object and degree. -/
@[reducible] def directSum : RightDGModuleModel A where
  complex := sumComplex F
  act := sumAct F
  act_id a i x := DFinsupp.ext fun s => (F s).act_id a i (x s)
  act_assoc i j l x f g := DFinsupp.ext fun s => (F s).act_assoc i j l (x s) f g
  leibniz {a b} i j n h x f := by
    change (sumComplex F a).d n (n+1) (sumAct F i j n h x f) =
      sumAct F (i+1) j (n+1) _ ((sumComplex F b).d i (i+1) x) f +
        i.negOnePow • sumAct F i (j+1) (n+1) _ x ((A.hom a b).d j (j+1) f)
    simp only [sumComplex, CochainComplex.of_d]
    apply DFinsupp.ext
    intro s
    exact (F s).leibniz i j n h (x s) f

@[simp] theorem directSum_d (a : A.Obj) (i : ℤ) (x : SumTerm F a i) (s : I) :
    ((directSum F).complex a).d i (i+1) x s = ((F s).complex a).d i (i+1) (x s) := by
  change CochainComplex.of.d (fun j => ModuleCat.of k (SumTerm F a j))
    (sumStep F a) i (i+1) x s = _
  rw [CochainComplex.of_d]
  rfl

@[reducible] def summand (a : A.Obj) (i : ℤ) (s : I) :
    ((F s).complex a).X i →ₗ[k] SumTerm F a i := by
  classical
  exact DirectSum.lof k I (fun t => ((F t).complex a).X i) s

theorem directSum_d_summand (a : A.Obj) (i : ℤ) (s : I) (x : ((F s).complex a).X i) :
    ((directSum F).complex a).d i (i+1) (summand F a i s x) =
      summand F a (i+1) s (((F s).complex a).d i (i+1) x) := by
  classical
  change CochainComplex.of.d (fun j => ModuleCat.of k (SumTerm F a j))
    (sumStep F a) i (i+1) _ = _
  rw [CochainComplex.of_d]
  exact DirectSum.lmap_lof (R := k) (fun t => ((F t).complex a).d i (i+1) |>.hom) s x

theorem sumAct_summand {a b : A.Obj} (i j n : ℤ) (h : i+j = n) (s : I)
    (x : ((F s).complex b).X i) (f : (A.hom a b).X j) :
    sumAct F i j n h (summand F b i s x) f = summand F a n s ((F s).act i j n h x f) := by
  classical
  exact DirectSum.lmap_lof (R := k) (fun t => ((F t).act i j n h).flip f) s x

theorem sum_induction {a : A.Obj} {i : ℤ} {motive : SumTerm F a i → Prop}
    (x : SumTerm F a i) (zero : motive 0)
    (single : ∀ s y, motive (summand F a i s y))
    (add : ∀ x y, motive x → motive y → motive (x+y)) : motive x := by
  classical
  exact DirectSum.induction_on x zero single add

def sumInclusion (s : I) : F s ⟶ directSum F where
  app a :=
    { f := fun i => ModuleCat.ofHom (summand F a i s)
      comm' := by
        intro i j h
        obtain rfl : i+1 = j := h
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact directSum_d_summand F a i s x }
  comm_act i j n h x f := (sumAct_summand F i j n h s x f).symm

end Sum


section Attachment

variable {P : RightDGModuleModel A} {I : Type v} (C : CellFamily P I)

abbrev cells (s : I) := cell (C.object s) (C.degree s)
abbrev cellSum := directSum (cells C)

/-- The off-diagonal differential sends a homogeneous multiple of a cell to
the same multiple of its prescribed boundary. -/
def attachingMap (a : A.Obj) (i : ℤ) :
    ((cellSum C).complex a).X i →ₗ[k] (P.complex a).X (i+1) := by
  classical
  exact DirectSum.toModule k I ((P.complex a).X (i+1)) fun s =>
      P.act (C.degree s + 1) (i + -C.degree s) (i+1) (by omega) (C.boundary s)

theorem attachingMap_summand (a : A.Obj) (i : ℤ) (s : I)
    (x : ((cells C s).complex a).X i) :
    attachingMap C a i (summand (cells C) a i s x) =
      P.act (C.degree s + 1) (i + -C.degree s) (i+1) (by omega) (C.boundary s) x := by
  classical
  exact DirectSum.toModule_lof (R := k)
    (φ := fun t => P.act (C.degree t+1) (i + -C.degree t) (i+1) (by omega) (C.boundary t)) s x

private theorem attachingMap_d_at (s : I) (a : A.Obj) (q r p : ℤ)
    (hr : q+1 = r) (hp : C.degree s+1+q = p)
    (x : (A.hom a (C.object s)).X q) :
    (P.complex a).d p (p+1) (P.act (C.degree s+1) q p hp (C.boundary s) x) +
      P.act (C.degree s+1) r (p+1) (by omega) (C.boundary s)
        ((-C.degree s).negOnePow • (A.hom a (C.object s)).d q r x) = 0 := by
  subst r
  rw [P.leibniz, C.closed, map_zero, LinearMap.zero_apply, zero_add]
  simp [Int.negOnePow_succ, Units.smul_def, map_zsmul]

theorem attachingMap_d (a : A.Obj) (i : ℤ) (y : ((cellSum C).complex a).X i) :
    (P.complex a).d (i+1) (i+1+1) (attachingMap C a i y) +
      attachingMap C a (i+1) (((cellSum C).complex a).d i (i+1) y) = 0 := by
  induction y using sum_induction (cells C) with
  | zero => simp
  | single s x =>
    rw [directSum_d_summand, attachingMap_summand, attachingMap_summand]
    change _ + P.act _ _ _ _ (C.boundary s)
      (((-C.degree s).negOnePow • (A.hom a (C.object s)).d
        (i + -C.degree s) (i+1 + -C.degree s)) x) = 0
    simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
    exact attachingMap_d_at C s a _ _ _ (by omega) (by omega) x
  | add x y hx hy =>
    simp only [map_add]
    rw [add_add_add_comm, hx, hy, add_zero]

private theorem attachingMap_act_at (s : I) {a b : A.Obj} (q j t p n : ℤ)
    (ht : q+j = t) (hp : C.degree s+1+q = p) (hn : p+j = n)
    (x : (A.hom b (C.object s)).X q) (f : (A.hom a b).X j) :
    P.act (C.degree s+1) t n (by omega) (C.boundary s) (A.comp q j t ht x f) =
      P.act p j n hn (P.act (C.degree s+1) q p hp (C.boundary s) x) f := by
  subst t p n
  exact (P.act_assoc (C.degree s+1) q j (C.boundary s) x f).symm

theorem attachingMap_act {a b : A.Obj} (i j n : ℤ) (h : i+j = n)
    (x : ((cellSum C).complex b).X i) (f : (A.hom a b).X j) :
    attachingMap C a n ((cellSum C).act i j n h x f) =
      P.act (i+1) j (n+1) (by omega) (attachingMap C b i x) f := by
  induction x using sum_induction (cells C) with
  | zero => simp
  | single s x =>
    change attachingMap C a n (sumAct (cells C) i j n h _ f) = _
    rw [sumAct_summand, attachingMap_summand, attachingMap_summand]
    exact attachingMap_act_at C s _ _ _ _ _ (by omega) (by omega) (by omega) x f
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply]
    exact congrArg₂ (· + ·) hx hy

abbrev AttachTerm (a : A.Obj) (i : ℤ) :=
  (P.complex a).X i × ((cellSum C).complex a).X i

def attachStep (a : A.Obj) (i : ℤ) :
    ModuleCat.of k (AttachTerm C a i) ⟶ ModuleCat.of k (AttachTerm C a (i+1)) :=
  ModuleCat.ofHom
    ((((P.complex a).d i (i+1)).hom.comp (LinearMap.fst _ _ _) +
        (attachingMap C a i).comp (LinearMap.snd _ _ _)).prod
      ((((cellSum C).complex a).d i (i+1)).hom.comp (LinearMap.snd _ _ _)))

@[reducible] def attachComplex (a : A.Obj) : ModuleCochain.{u,v} k :=
  CochainComplex.of (fun i => ModuleCat.of k (AttachTerm C a i)) (attachStep C a) (by
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · change (P.complex a).d (i+1) (i+1+1)
        ((P.complex a).d i (i+1) x.1 + attachingMap C a i x.2) +
          attachingMap C a (i+1) (((cellSum C).complex a).d i (i+1) x.2) = 0
      rw [map_add, d_d_apply, zero_add, attachingMap_d]
    · exact d_d_apply ((cellSum C).complex a) i (i+1) (i+1+1) x.2)

@[simp] theorem attachComplex_d (a : A.Obj) (i : ℤ) (x : AttachTerm C a i) :
    (attachComplex C a).d i (i+1) x =
      ((P.complex a).d i (i+1) x.1 + attachingMap C a i x.2,
        ((cellSum C).complex a).d i (i+1) x.2) := by
  change CochainComplex.of.d (fun j => ModuleCat.of k (AttachTerm C a j))
    (attachStep C a) i (i+1) x = _
  rw [CochainComplex.of_d]
  rfl

def attachAct {a b : A.Obj} (i j n : ℤ) (h : i+j = n) :
    AttachTerm C b i →ₗ[k] (A.hom a b).X j →ₗ[k] AttachTerm C a n where
  toFun x := (P.act i j n h x.1).prod ((cellSum C).act i j n h x.2)
  map_add' x y := by
    apply LinearMap.ext
    intro f
    change (P.act i j n h (x.1+y.1) f, (cellSum C).act i j n h (x.2+y.2) f) =
      (P.act i j n h x.1 f, (cellSum C).act i j n h x.2 f) +
      (P.act i j n h y.1 f, (cellSum C).act i j n h y.2 f)
    simp only [map_add, LinearMap.add_apply, Prod.mk_add_mk]
  map_smul' c x := by
    apply LinearMap.ext
    intro f
    change (P.act i j n h (c • x.1) f, (cellSum C).act i j n h (c • x.2) f) =
      c • (P.act i j n h x.1 f, (cellSum C).act i j n h x.2 f)
    simp only [map_smul, LinearMap.smul_apply, Prod.smul_mk]

/-- Attach all the cells simultaneously, using the graded direct sum. -/
@[reducible] def attach : RightDGModuleModel A where
  complex := attachComplex C
  act := attachAct C
  act_id a i x := Prod.ext (P.act_id a i x.1) ((cellSum C).act_id a i x.2)
  act_assoc i j l x f g :=
    Prod.ext (P.act_assoc i j l x.1 f g) ((cellSum C).act_assoc i j l x.2 f g)
  leibniz {a b} i j n h x f := by
    change (attachComplex C a).d n (n+1) (attachAct C i j n h x f) =
      attachAct C (i+1) j (n+1) _ ((attachComplex C b).d i (i+1) x) f +
        i.negOnePow • attachAct C i (j+1) (n+1) _ x ((A.hom a b).d j (j+1) f)
    rw [attachComplex_d, attachComplex_d]
    apply Prod.ext
    · change (P.complex a).d n (n+1) (P.act i j n h x.1 f) +
        attachingMap C a n ((cellSum C).act i j n h x.2 f) =
          P.act (i+1) j (n+1) _ ((P.complex b).d i (i+1) x.1 + attachingMap C b i x.2) f +
            i.negOnePow • P.act i (j+1) (n+1) _ x.1 ((A.hom a b).d j (j+1) f)
      rw [P.leibniz, attachingMap_act]
      simp only [map_add, LinearMap.add_apply]
      rw [add_right_comm]
    · exact (cellSum C).leibniz i j n h x.2 f

/-- The inclusion of the preceding stage. -/
@[reducible] def inclusion : P ⟶ attach C where
  app a := CochainComplex.ofHom (fun i => ModuleCat.ofHom (LinearMap.inl k _ _)) (by
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (attachComplex C a).d i (i+1) (x, 0) = ((P.complex a).d i (i+1) x, 0)
    rw [attachComplex_d, map_zero, map_zero, add_zero])
  comm_act i j n h x f := by
    change (P.act i j n h x f, 0) = (P.act i j n h x f, (cellSum C).act i j n h 0 f)
    rw [map_zero, LinearMap.zero_apply]

/-- Projection to the direct sum of shifted representables. -/
@[reducible] def projection : attach C ⟶ cellSum C where
  app a := CochainComplex.ofHom (fun i => ModuleCat.ofHom (LinearMap.snd k _ _)) (by
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((cellSum C).complex a).d i (i+1) x.2 =
      ((attachComplex C a).d i (i+1) x).2
    rw [attachComplex_d])
  comm_act _ _ _ _ _ _ := rfl

end Attachment

/-- A chosen countable filtration by cell extensions. Stage zero in this type
is the zero module preceding the first set of cells. -/
structure Presentation (M : RightDGModuleModel A) where
  stage : ℕ → RightDGModuleModel A
  bottom (a : A.Obj) (i : ℤ) (x : ((stage 0).complex a).X i) : x = 0
  index : ℕ → Type v
  family (j : ℕ) : CellFamily (stage j) (index j)
  successor (j : ℕ) : attach (family j) ≅ stage (j+1)
  into (j : ℕ) : stage j ⟶ M
  compatible (j : ℕ) : inclusion (family j) ≫ (successor j).hom ≫ into (j+1) = into j
  injective (j : ℕ) (a : A.Obj) (i : ℤ) : Function.Injective ((into j).app a |>.f i)
  exhaustive (a : A.Obj) (i : ℤ) (x : (M.complex a).X i) :
    ∃ j y, ((into j).app a).f i y = x

def semiFree (M : RightDGModuleModel A) : Prop := Nonempty (Presentation M)

def finiteCell (M : RightDGModuleModel A) : Prop :=
  ∃ F : Presentation M, Finite (Σ j, F.index j)


section AttachmentLaws

variable {P : RightDGModuleModel A} {I : Type v}

def attachedGenerator (C : CellFamily P I) (s : I) :
    ((attach C).complex (C.object s)).X (C.degree s) :=
  (0, summand (cells C) (C.object s) (C.degree s) s (generator (C.object s) (C.degree s)))

end AttachmentLaws

def Coproduct : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type v} (F : I → RightDGModuleModel A),
    Nonempty (IsColimit (Cofan.mk (directSum F) (sumInclusion F)))

def FiniteSupport : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {I : Type v} (F : I → RightDGModuleModel A) (a : A.Obj) (i : ℤ)
    (x : SumTerm F a i), Set.Finite {s : I | x s ≠ 0}

def CellGeneratorLaws : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k} (a : A.Obj) (n : ℤ),
    ((cell a n).complex a).d n (n+1) (generator a n) = 0 ∧
      ∀ (b : A.Obj) (j : ℤ) (f : (A.hom b a).X j),
        (cell a n).act n j (n+j) rfl (generator a n) f =
          ((A.hom b a).XIsoOfEq (by omega : j = n+j + -n)).hom f

def AttachmentMatrix : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P : RightDGModuleModel A} {I : Type v} (C : CellFamily P I),
    (∀ (a : A.Obj) (i : ℤ) (x : AttachTerm C a i),
      ((attach C).complex a).d i (i+1) x =
        ((P.complex a).d i (i+1) x.1 + attachingMap C a i x.2,
          ((cellSum C).complex a).d i (i+1) x.2)) ∧
    (∀ (a b : A.Obj) (i j n : ℤ) (h : i+j = n) (x : AttachTerm C b i) (f : (A.hom a b).X j),
      (attach C).act i j n h x f = (P.act i j n h x.1 f, (cellSum C).act i j n h x.2 f)) ∧
    (∀ (a : A.Obj) (i : ℤ) (x : AttachTerm C a i),
      ((attach C).complex a).d (i+1) (i+1+1) (((attach C).complex a).d i (i+1) x) = 0)

def AttachmentFormula : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P : RightDGModuleModel A} {I : Type v} (C : CellFamily P I) (s : I),
    let e := attachedGenerator C s
    let n := C.degree s
    let b := C.object s
    ((attach C).complex b).d n (n+1) e = ((inclusion C).app b).f (n+1) (C.boundary s) ∧
      ∀ (a : A.Obj) (j q : ℤ) (h : n+j = q) (f : (A.hom a b).X j),
        (attach C).act n j q h e f =
          (0, summand (cells C) a q s (((A.hom a b).XIsoOfEq (by omega : j = q + -n)).hom f)) ∧
        ((attach C).complex a).d q (q+1) ((attach C).act n j q h e f) =
          ((inclusion C).app a).f (q+1) (P.act (n+1) j (q+1) (by omega) (C.boundary s) f) +
            n.negOnePow • (attach C).act n (j+1) (q+1) (by omega) e ((A.hom a b).d j (j+1) f)

def AttachmentQuotient : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P : RightDGModuleModel A} {I : Type v} (C : CellFamily P I),
    (∀ (a : A.Obj) (i : ℤ),
      Function.Injective ((inclusion C).app a |>.f i) ∧
      Function.Surjective ((projection C).app a |>.f i) ∧
      ∀ x : AttachTerm C a i, ((projection C).app a).f i x = 0 ↔
        ∃ y : (P.complex a).X i, ((inclusion C).app a).f i y = x) ∧
    ∃ h : inclusion C ≫ projection C = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ (projection C) h))


section PresentationSupport

variable {M : RightDGModuleModel A} (F : Presentation M) (a : A.Obj) (i : ℤ)

abbrev PresentationTerm :=
  ⨁ s : (Σ j, F.index j), ((cells (F.family s.1) s.2).complex a).X i

/-- The graded map given by taking a cell multiple at one stage into the full module. -/
def presentationCellMap (s : Σ j, F.index j) :
    ((cells (F.family s.1) s.2).complex a).X i →ₗ[k] (M.complex a).X i :=
  (((F.successor s.1).hom ≫ F.into (s.1+1)).app a |>.f i).hom.comp
    ((LinearMap.inr k _ _).comp (summand (cells (F.family s.1)) a i s.2))

/-- Evaluate a finitely supported family of multiples of the cells of a presentation. -/
def presentationSumMap : PresentationTerm F a i →ₗ[k] (M.complex a).X i := by
  classical
  exact DirectSum.toModule k _ _ (presentationCellMap F a i)

end PresentationSupport

def PresentationFiniteSupport : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M : RightDGModuleModel A} (F : Presentation M) (a : A.Obj) (i : ℤ)
    (x : (M.complex a).X i),
    ∃ y : PresentationTerm F a i, presentationSumMap F a i y = x ∧
      Set.Finite {s : (Σ j, F.index j) | y s ≠ 0}

section BindingTypes

set_option linter.checkUnivs false

abbrev cellFamily := @CellFamily
abbrev presentation := @Presentation

def CellType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k},
    A.Obj → ℤ → RightDGModuleModel A

def GeneratorType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k} (a : A.Obj) (n : ℤ),
    ((cell a n).complex a).X n

def CellFamilyType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k},
    RightDGModuleModel A → Type v → Type (max v w)

def DirectSumType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k} {I : Type v},
    (I → RightDGModuleModel A) → RightDGModuleModel A

def SumInclusionType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k} {I : Type v}
    (F : I → RightDGModuleModel A) (s : I), F s ⟶ directSum F

def AttachType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P : RightDGModuleModel A} {I : Type v}, CellFamily P I → RightDGModuleModel A

def InclusionType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P : RightDGModuleModel A} {I : Type v} (C : CellFamily P I), P ⟶ attach C

def ProjectionType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P : RightDGModuleModel A} {I : Type v} (C : CellFamily P I), attach C ⟶ cellSum C

def AttachedGeneratorType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P : RightDGModuleModel A} {I : Type v} (C : CellFamily P I) (s : I),
    ((attach C).complex (C.object s)).X (C.degree s)

def PresentationType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k},
    RightDGModuleModel A → Type (max u w (v+1))

def ModulePredicate :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}, RightDGModuleModel A → Prop

end BindingTypes

end
end Specs.DerivedFormalization.DG.SemiFree
