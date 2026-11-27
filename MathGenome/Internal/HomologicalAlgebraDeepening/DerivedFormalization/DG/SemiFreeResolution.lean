import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CellReindex
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CoefficientLiftComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.SemiFreeResolution
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.LinearAlgebra.Quotient.Basic

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v w

namespace DerivedFormalization.RightDGModule

open Specs.DerivedFormalization.DG

noncomputable section

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}

private theorem square_zero (C : ModuleCochain.{u,v} k) (i j l : ℤ) (x : C.X i) :
    C.d j l (C.d i j x) = 0 := by
  rw [← ModuleCat.comp_apply, d_comp_d]
  rfl

section Extension

variable {P M : RightDGModule A} {I : Type v} (C : CellFamily P I)
  (p : P ⟶ M) (image : ∀ s, (M.complex (C.object s)).X (C.degree s))

private def onCells (a : A.Obj) (i : ℤ) :
    SemiFree.SumTerm (SemiFree.cells C) a i →ₗ[k] (M.complex a).X i := by
  classical
  exact DirectSum.toModule k I _ fun s =>
    M.act (C.degree s) (i + -C.degree s) i (by omega) (image s)

@[simp] private theorem onCells_summand (a : A.Obj) (i : ℤ) (s : I)
    (x : ((SemiFree.cells C s).complex a).X i) :
    onCells C image a i (SemiFree.summand (SemiFree.cells C) a i s x) =
      M.act (C.degree s) (i + -C.degree s) i (by omega) (image s) x := by
  classical
  exact DirectSum.toModule_lof (R := k) (φ := fun s =>
    M.act (C.degree s) (i + -C.degree s) i (by omega) (image s)) s x

private theorem onCells_act {a b : A.Obj} (i j n : ℤ) (h : i+j = n)
    (x : SemiFree.SumTerm (SemiFree.cells C) b i) (f : (A.hom a b).X j) :
    onCells C image a n (SemiFree.sumAct (SemiFree.cells C) i j n h x f) =
      M.act i j n h (onCells C image b i x) f := by
  induction x using SemiFree.sum_induction (SemiFree.cells C) with
  | zero => simp
  | single s x =>
    rw [SemiFree.sumAct_summand, onCells_summand, onCells_summand]
    have assoc (q t : ℤ) (hd : C.degree s + q = i) (ht : q+j = t)
        (y : (A.hom b (C.object s)).X q) :
        M.act i j n h (M.act (C.degree s) q i hd (image s) y) f =
          M.act (C.degree s) t n (by omega) (image s) (A.comp q j t ht y f) := by
      subst n t i
      exact M.act_assoc (C.degree s) q j (image s) y f
    exact (assoc (i + -C.degree s) (n + -C.degree s) (by omega) (by omega) x).symm
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

private theorem onCells_d
    (comm : ∀ s, (M.complex (C.object s)).d (C.degree s) (C.degree s+1) (image s) =
      (p.app (C.object s)).f (C.degree s+1) (C.boundary s))
    (a : A.Obj) (i : ℤ) (x : SemiFree.SumTerm (SemiFree.cells C) a i) :
    (M.complex a).d i (i+1) (onCells C image a i x) =
      (p.app a).f (i+1) (SemiFree.attachingMap C a i x) +
        onCells C image a (i+1) (((cellSum C).complex a).d i (i+1) x) := by
  induction x using SemiFree.sum_induction (SemiFree.cells C) with
  | zero => simp
  | single s x =>
    rw [SemiFree.directSum_d_summand, SemiFree.attachingMap_summand,
      onCells_summand, onCells_summand, M.leibniz, comm, p.comm_act]
    congr 1
    have step (q r t : ℤ) (hr : q+1 = r) (ht : C.degree s+q+1 = t)
        (y : (A.hom a (C.object s)).X q) :
        (C.degree s).negOnePow •
          M.act (C.degree s) (q+1) t (by omega) (image s)
            ((A.hom a (C.object s)).d q (q+1) y) =
          M.act (C.degree s) r t (by omega) (image s)
            (((-C.degree s).negOnePow • (A.hom a (C.object s)).d q r) y) := by
      subst r t
      rw [Int.negOnePow_neg]
      simp only [ModuleCat.hom_smul, LinearMap.smul_apply, Units.smul_def, map_zsmul]
    exact step (i + -C.degree s) (i+1 + -C.degree s) (i+1) (by omega) (by omega) x
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    abel

private def extensionLinear (a : A.Obj) (i : ℤ) :
    SemiFree.AttachTerm C a i →ₗ[k] (M.complex a).X i :=
  ((p.app a).f i).hom.comp (LinearMap.fst k _ _) +
    (onCells C image a i).comp (LinearMap.snd k _ _)

private def extendOverCells
    (comm : ∀ s, (M.complex (C.object s)).d (C.degree s) (C.degree s+1) (image s) =
      (p.app (C.object s)).f (C.degree s+1) (C.boundary s)) : attachCells C ⟶ M where
  app a := CochainComplex.ofHom (fun i => ModuleCat.ofHom (extensionLinear C p image a i)) (by
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (M.complex a).d i (i+1) (extensionLinear C p image a i x) =
      extensionLinear C p image a (i+1) ((SemiFree.attachComplex C a).d i (i+1) x)
    rw [SemiFree.attachComplex_d]
    change (M.complex a).d i (i+1) ((p.app a).f i x.1 + onCells C image a i x.2) =
      (p.app a).f (i+1) ((P.complex a).d i (i+1) x.1 + SemiFree.attachingMap C a i x.2) +
        onCells C image a (i+1) (((cellSum C).complex a).d i (i+1) x.2)
    rw [map_add, onCells_d C p image comm, map_add, add_assoc]
    congr 1
    exact CategoryTheory.congr_fun ((p.app a).comm i (i+1)) x.1)
  comm_act {a b} i j n h x f := by
    change (p.app a).f n (P.act i j n h x.1 f) +
      onCells C image a n (SemiFree.sumAct (SemiFree.cells C) i j n h x.2 f) =
      M.act i j n h ((p.app b).f i x.1 + onCells C image b i x.2) f
    rw [p.comm_act, onCells_act, map_add, LinearMap.add_apply]

@[simp] private theorem inclusion_extendOverCells
    (comm : ∀ s, (M.complex (C.object s)).d (C.degree s) (C.degree s+1) (image s) =
      (p.app (C.object s)).f (C.degree s+1) (C.boundary s)) :
    attachInclusion C ≫ extendOverCells C p image comm = p := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (p.app a).f i x + onCells C image a i 0 = _
  rw [map_zero, add_zero]

@[simp] private theorem extendOverCells_generator
    (comm : ∀ s, (M.complex (C.object s)).d (C.degree s) (C.degree s+1) (image s) =
      (p.app (C.object s)).f (C.degree s+1) (C.boundary s)) (s : I) :
    ((extendOverCells C p image comm).app (C.object s)).f (C.degree s)
      (attachedGenerator C s) = image s := by
  change (p.app (C.object s)).f (C.degree s) 0 +
    onCells C image (C.object s) (C.degree s)
      (SemiFree.summand (SemiFree.cells C) (C.object s) (C.degree s) s
        (cellGenerator (C.object s) (C.degree s))) = _
  rw [map_zero, zero_add, onCells_summand]
  have eq (q : ℤ) (h : 0 = q) :
      M.act (C.degree s) q (C.degree s) (by omega) (image s)
        (((A.hom (C.object s) (C.object s)).XIsoOfEq h).hom (A.id (C.object s))) =
      image s := by
    subst q
    exact M.act_id (C.object s) (C.degree s) (image s)
  exact eq _ (by omega)

end Extension

section Stages

variable {A : DGCategory.{u,max v w,w} k}
variable (M : RightDGModule A)

private def zeroModule : RightDGModule A where
  complex _ := CochainComplex.of (fun _ => ModuleCat.of k (PUnit : Type (max v w))) (fun _ => 0) (by simp)
  act _ _ _ _ := 0
  act_id _ _ _ := Subsingleton.elim (α := PUnit) _ _
  act_assoc _ _ _ _ _ _ := rfl
  leibniz := by intros; simp

private structure CellIndex {P : RightDGModule A} (p : P ⟶ M) where
  object : A.Obj
  degree : ℤ
  boundary : (P.complex object).X (degree+1)
  image : (M.complex object).X degree
  closed : (P.complex object).d (degree+1) (degree+1+1) boundary = 0
  comm : (M.complex object).d degree (degree+1) image = (p.app object).f (degree+1) boundary

private def cellsFor {P : RightDGModule A} (p : P ⟶ M) : CellFamily P (CellIndex M p) where
  object s := s.object
  degree s := s.degree
  boundary s := s.boundary
  closed s := s.closed

private def extendMap {P : RightDGModule A} (p : P ⟶ M) : attachCells (cellsFor M p) ⟶ M :=
  extendOverCells (cellsFor M p) p (fun s => s.image) (fun s => s.comm)

-- Starting with the zero module makes the first cell family the cycles of the target.
private def stageOver : ℕ → Σ P : RightDGModule A, P ⟶ M
  | 0 => ⟨zeroModule (A := A), 0⟩
  | j + 1 => ⟨_, extendMap M (stageOver j).2⟩

private abbrev stage (j : ℕ) := (stageOver M j).1
private abbrev stageMap (j : ℕ) := (stageOver M j).2
private abbrev stageCells (j : ℕ) := cellsFor M (stageMap M j)

private def stageInclusion (j : ℕ) : stage M j ⟶ stage M (j+1) :=
  attachInclusion (stageCells M j)

private theorem stageInclusion_comm (j : ℕ) :
    stageInclusion M j ≫ stageMap M (j+1) = stageMap M j :=
  inclusion_extendOverCells (stageCells M j) (stageMap M j) _ (fun s => s.comm)

private def diagram : ℕ ⥤ RightDGModule A := Functor.ofSequence (stageInclusion M)

private theorem diagram_map_succ (j : ℕ) :
    (diagram M).map (homOfLE (Nat.le_succ j)) = stageInclusion M j :=
  Functor.ofSequence_map_homOfLE_succ (stageInclusion M) j

private def coconeToTarget : Cocone (diagram M) where
  pt := M
  ι := NatTrans.ofSequence (fun j => stageMap M j) (by
    intro j
    rw [diagram_map_succ]
    change stageInclusion M j ≫ stageMap M (j+1) = stageMap M j ≫ 𝟙 M
    rw [Category.comp_id, stageInclusion_comm])

private abbrev resolution : RightDGModule A := (colimitCocone (diagram M)).pt
private abbrev inclusion (j : ℕ) : stage M j ⟶ resolution M :=
  (colimitCocone (diagram M)).ι.app j

private def augmentation : resolution M ⟶ M :=
  (colimitCoconeIsColimit (diagram M)).desc (coconeToTarget M)

@[simp] private theorem inclusion_augmentation (j : ℕ) :
    inclusion M j ≫ augmentation M = stageMap M j :=
  (colimitCoconeIsColimit (diagram M)).fac _ _

private theorem inclusion_comm (j : ℕ) :
    stageInclusion M j ≫ inclusion M (j+1) = inclusion M j := by
  have eq := (colimitCocone (diagram M)).w (homOfLE (Nat.le_succ j))
  rw [diagram_map_succ] at eq
  exact eq

end Stages

section SequentialColimit

variable (F : ℕ ⥤ ModuleCat.{v} k)
variable (r : ∀ i, F.obj (i+1) ⟶ F.obj i)

private def retractTo (j : ℕ) (i : ℕ) : F.obj i ⟶ F.obj j :=
  match i with
  | 0 => F.map (homOfLE (Nat.zero_le j))
  | i+1 =>
    if h : i+1 ≤ j then F.map (homOfLE h)
    else r i ≫ retractTo j i

private theorem retractTo_of_le {i j : ℕ} (h : i ≤ j) :
    retractTo F r j i = F.map (homOfLE h) := by
  cases i with
  | zero => rfl
  | succ i => simp only [retractTo, dite_eq_left h]

private theorem retractTo_naturality
    (hr : ∀ i, F.map (homOfLE (Nat.le_succ i)) ≫ r i = 𝟙 _) (j i : ℕ) :
    F.map (homOfLE (Nat.le_succ i)) ≫ retractTo F r j (i+1) = retractTo F r j i := by
  by_cases h : i+1 ≤ j
  · rw [retractTo_of_le F r h, retractTo_of_le F r ((Nat.le_succ i).trans h),
      ← F.map_comp, homOfLE_comp]
  · rw [retractTo, dite_eq_right h, ← Category.assoc, hr, Category.id_comp]

private theorem colimitInclusion_injective
    (hr : ∀ i, F.map (homOfLE (Nat.le_succ i)) ≫ r i = 𝟙 _)
    {c : Cocone F} (hc : IsColimit c) (j : ℕ) :
    Function.Injective (c.ι.app j) := by
  let t : Cocone F :=
    ⟨F.obj j, NatTrans.ofSequence (retractTo F r j) fun i => by
      change _ = retractTo F r j i ≫ 𝟙 _
      rw [Category.comp_id, retractTo_naturality F r hr]⟩
  have eq : c.ι.app j ≫ hc.desc t = 𝟙 _ := by
    rw [hc.fac]
    change retractTo F r j j = 𝟙 _
    rw [retractTo_of_le F r le_rfl]
    exact F.map_id j
  intro x y hxy
  exact (CategoryTheory.congr_fun eq x).symm.trans
    ((congrArg (hc.desc t) hxy).trans (CategoryTheory.congr_fun eq y))

-- In each degree the ranges form a directed family and their union is the colimit.
private theorem colimitInclusions_exhaustive {c : Cocone F} (hc : IsColimit c) (x : c.pt) :
    ∃ j y, c.ι.app j y = x := by
  let R (j : ℕ) : Submodule k c.pt := (c.ι.app j).hom.range
  have monotone : Monotone R := by
    intro i j hij y hy
    obtain ⟨z, rfl⟩ := hy
    refine ⟨F.map (homOfLE hij) z, ?_⟩
    exact CategoryTheory.congr_fun (c.w (homOfLE hij)) z
  let S : Submodule k c.pt := ⨆ j, R j
  have hq : (ModuleCat.ofHom S.mkQ : c.pt ⟶ ModuleCat.of k (c.pt ⧸ S)) = 0 := by
    apply hc.hom_ext
    intro j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    change S.mkQ (c.ι.app j y) = 0
    exact Submodule.Quotient.mk_eq_zero S |>.2 ((le_iSup R j) ⟨y, rfl⟩)
  have hx : x ∈ S :=
    Submodule.Quotient.mk_eq_zero S |>.1 (CategoryTheory.congr_fun hq x)
  exact (Submodule.mem_iSup_of_directed R monotone.directed_le).1 hx

end SequentialColimit

section Resolution

variable {A : DGCategory.{u,max v w,w} k} (M : RightDGModule A)

private theorem inclusion_injective (j : ℕ) (a : A.Obj) (i : ℤ) :
    Function.Injective ((inclusion M j).app a |>.f i) := by
  let F := diagram M ⋙ degree (A := A) a i
  let r (j : ℕ) : F.obj (j+1) ⟶ F.obj j := by
    change ModuleCat.of k (SemiFree.AttachTerm (stageCells M j) a i) ⟶ (stage M j).complex a |>.X i
    exact ModuleCat.ofHom (LinearMap.fst k ((stage M j).complex a |>.X i)
      (SemiFree.SumTerm (SemiFree.cells (stageCells M j)) a i))
  have hr (j : ℕ) : F.map (homOfLE (Nat.le_succ j)) ≫ r j = 𝟙 _ := by
    change (degree (A := A) a i).map ((diagram M).map (homOfLE (Nat.le_succ j))) ≫ r j = _
    rw [diagram_map_succ]
    rfl
  exact colimitInclusion_injective F r hr (colimitCoconeIsColimitDegree (diagram M) a i) j

private theorem inclusion_exhaustive (a : A.Obj) (i : ℤ) (x : ((resolution M).complex a).X i) :
    ∃ j y, ((inclusion M j).app a).f i y = x :=
  colimitInclusions_exhaustive _ (colimitCoconeIsColimitDegree (diagram M) a i) x

private def presentation : SmallSemiFreePresentation (resolution M) where
  stage := stage M
  bottom _ _ _ := Subsingleton.elim (α := PUnit) _ _
  index j := CellIndex M (stageMap M j)
  family := stageCells M
  successor _ := Iso.refl _
  into := inclusion M
  compatible j := by
    change stageInclusion M j ≫ 𝟙 _ ≫ inclusion M (j+1) = inclusion M j
    rw [Category.id_comp, inclusion_comm]
  injective := inclusion_injective M
  exhaustive := inclusion_exhaustive M

private theorem stage_cell_lift (j : ℕ) (a : A.Obj) (n : ℤ)
    (z : ((stage M j).complex a).X (n+1)) (hz : ((stage M j).complex a).d (n+1) (n+1+1) z = 0)
    (x : (M.complex a).X n)
    (hx : (M.complex a).d n (n+1) x = ((stageMap M j).app a).f (n+1) z) :
    ∃ y : ((resolution M).complex a).X n,
      ((resolution M).complex a).d n (n+1) y = ((inclusion M j).app a).f (n+1) z ∧
      ((augmentation M).app a).f n y = x := by
  let s : CellIndex M (stageMap M j) := ⟨a, n, z, x, hz, hx⟩
  let e : ((stage M (j+1)).complex a).X n := attachedGenerator (stageCells M j) s
  refine ⟨((inclusion M (j+1)).app a).f n e, ?_, ?_⟩
  · have hcomm := CategoryTheory.congr_fun (((inclusion M (j+1)).app a).comm n (n+1)) e
    simp only [ModuleCat.comp_apply] at hcomm
    rw [hcomm]
    have hd : ((stage M (j+1)).complex a).d n (n+1) e =
      ((stageInclusion M j).app a).f (n+1) z := attachedGenerator_d (stageCells M j) s
    rw [hd]
    exact congrArg (fun (f : stage M j ⟶ resolution M) => (f.app a).f (n+1) z)
      (inclusion_comm M j)
  · have h := congrArg (fun (f : stage M (j+1) ⟶ M) => (f.app a).f n e)
      (inclusion_augmentation M (j+1))
    refine h.trans ?_
    exact extendOverCells_generator (stageCells M j) (stageMap M j) _
      (fun s => s.comm) s

-- A cycle with a chosen primitive in the target lifts to the boundary of a cell.
private theorem lift_primitive (a : A.Obj) (n : ℤ)
    (z : ((resolution M).complex a).X (n+1))
    (hz : ((resolution M).complex a).d (n+1) (n+1+1) z = 0)
    (x : (M.complex a).X n)
    (hx : (M.complex a).d n (n+1) x = ((augmentation M).app a).f (n+1) z) :
    ∃ y : ((resolution M).complex a).X n,
      ((resolution M).complex a).d n (n+1) y = z ∧ ((augmentation M).app a).f n y = x := by
  obtain ⟨j, t, rfl⟩ := inclusion_exhaustive M a (n+1) z
  have hcomm := CategoryTheory.congr_fun (((inclusion M j).app a).comm (n+1) (n+1+1)) t
  simp only [ModuleCat.comp_apply] at hcomm
  rw [hcomm] at hz
  have h0 : ((inclusion M j).app a).f (n+1+1) 0 = 0 :=
    map_zero (((inclusion M j).app a).f (n+1+1)).hom
  rw [← h0] at hz
  have hp := congrArg (fun (f : stage M j ⟶ M) => (f.app a).f (n+1) t)
    (inclusion_augmentation M j)
  exact stage_cell_lift M j a n t (inclusion_injective M j a _ hz) x (hx.trans hp)

private theorem augmentation_surjective : DegreewiseSurjective (augmentation M) := by
  intro a n x
  have hc : (M.complex a).d (n+1) (n+1+1) ((M.complex a).d n (n+1) x) =
      ((augmentation M).app a).f (n+1+1) 0 := by
    rw [square_zero, map_zero]
  obtain ⟨z, hz, hp⟩ := lift_primitive M a (n+1) 0 (map_zero _) _ hc
  obtain ⟨y, _, hy⟩ := lift_primitive M a n z hz x hp.symm
  exact ⟨y, hy⟩

private theorem augmentation_quasiIso : IsQuasiIso (augmentation M) := by
  apply (quasiIso_iff_cone_acyclic (augmentation M)).2
  intro a i
  let f := augmentation M
  let K := (cone f).complex a
  change K.ExactAt i
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, n+1 = i := ⟨i-1, by omega⟩
  rw [K.exactAt_iff' (i := n) (j := n+1) (k := n+1+1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro p hp
  change ShiftCone.coneDiff f a (n+1) (n+1+1) p = 0 at hp
  rw [ShiftCone.coneDiff_succ] at hp
  have hz : ((resolution M).complex a).d (n+1+1) (n+1+1+1) p.2 = 0 :=
    neg_eq_zero.mp (congrArg Prod.snd hp)
  have hx : (M.complex a).d (n+1) (n+1+1) (-p.1) =
      (f.app a).f (n+1+1) p.2 := by
    rw [map_neg]
    exact neg_eq_of_add_eq_zero_right (congrArg Prod.fst hp)
  -- The two components of the cone cycle prescribe the boundary and image of a cell.
  obtain ⟨e, he, hpe⟩ := lift_primitive M a (n+1) p.2 hz (-p.1) hx
  refine ⟨(0, -e), ?_⟩
  change ShiftCone.coneDiff f a n (n+1) (0, -e) = p
  rw [ShiftCone.coneDiff_succ]
  apply Prod.ext
  · change (M.complex a).d n (n+1) 0 + (f.app a).f (n+1) (-e) = p.1
    rw [map_zero, zero_add, map_neg, hpe, neg_neg]
  · change -((resolution M).complex a).d (n+1) (n+1+1) (-e) = p.2
    rw [map_neg, neg_neg, he]

end Resolution

/-- The countable cell filtration gives a resolution over the given dg category
when the coefficient universe contains the object type. -/
theorem unboundedSemiFreeResolutionInUniverse : SemiFreeResolution.NativeResolution.{u,v,w} := by
  intro k _ A M
  let F := presentation M
  obtain ⟨E, hE, _⟩ := DG.CellReindex.fromSmall.{u,max v w,w} F
  exact ⟨resolution M, augmentation M, ⟨CellReindex.indexedPresentation F E hE⟩,
    augmentation_surjective M,
    augmentation_quasiIso M⟩

private theorem liftPrimitiveOfQuasiIso {P N : RightDGModule A} {p : P ⟶ N}
    (hs : DegreewiseSurjective p) (hq : IsQuasiIso p) (a : A.Obj) (n : ℤ)
    (z : (P.complex a).X (n + 1)) (hz : (P.complex a).d (n + 1) (n + 1 + 1) z = 0)
    (x : (N.complex a).X n) (hx : (N.complex a).d n (n + 1) x = (p.app a).f (n + 1) z) :
    ∃ y : (P.complex a).X n,
      (P.complex a).d n (n + 1) y = z ∧ (p.app a).f n y = x := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, m + 1 = n := ⟨n - 1, by omega⟩
  let K := (cone p).complex a
  have hK : K.ExactAt (m + 1) := (quasiIso_iff_cone_acyclic p).1 hq a (m + 1)
  rw [K.exactAt_iff' (i := m) (j := m + 1) (k := m + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hK
  have hc : K.d (m + 1) (m + 1 + 1) (-x, z) = 0 := by
    change ShiftCone.coneDiff p a (m + 1) (m + 1 + 1) (-x, z) = 0
    rw [ShiftCone.coneDiff_succ]
    apply Prod.ext
    · change (N.complex a).d (m + 1) (m + 1 + 1) (-x) + (p.app a).f (m + 1 + 1) z = 0
      rw [map_neg, hx, neg_add_cancel]
    · change -((P.complex a).d (m + 1 + 1) (m + 1 + 1 + 1) z) = 0
      rw [hz, neg_zero]
  obtain ⟨b, hb⟩ := hK (-x, z) hc
  change ShiftCone.coneDiff p a m (m + 1) b = (-x, z) at hb
  rw [ShiftCone.coneDiff_succ] at hb
  -- A primitive in the cone gives a preimage of the cycle. Correct its
  -- image by the differential of a preimage of the other component.
  have hb₁ : (N.complex a).d m (m + 1) b.1 + (p.app a).f (m + 1) b.2 = -x :=
    congrArg Prod.fst hb
  have hb₂ : -((P.complex a).d (m + 1) (m + 1 + 1) b.2) = z :=
    congrArg Prod.snd hb
  obtain ⟨t, ht⟩ := hs a m b.1
  refine ⟨-b.2 - (P.complex a).d m (m + 1) t, ?_, ?_⟩
  · rw [map_sub, map_neg, square_zero, sub_zero, hb₂]
  · have ht' := CategoryTheory.congr_fun ((p.app a).comm m (m + 1)) t
    simp only [ModuleCat.comp_apply, ht] at ht'
    rw [map_sub, map_neg, ← ht']
    calc
      _ = -((N.complex a).d m (m + 1) b.1 + (p.app a).f (m + 1) b.2) := by abel
      _ = x := by rw [hb₁, neg_neg]

/-- Every original module has a semi-free resolution after enlarging coefficients
over the same objects. The augmentation computes the cohomology of the original module. -/
theorem unboundedSemiFreeResolution : SemiFreeResolution.UnboundedSemiFreeResolution.{u,v,w} := by
  intro k _ A M
  let N := CoefficientLift.liftModule.{u,v,w,w} M
  obtain ⟨P, p, hP, hs, hq⟩ :=
    unboundedSemiFreeResolutionInUniverse.{u,v,w} k (CoefficientLift.liftCategory.{u,v,w,w} A) N
  have ev := DG.CoefficientLift.evaluation.{u,v,w,w} p
  refine ⟨P, p, hP, hs, hq, fun a n => (ev.surjective a n).2 (hs a n),
    fun a n => ev.differential a n (n + 1), fun a b => ev.action (a := a) (b := b), ?_, ?_⟩
  · intro a n y hy
    have he : (N.complex a).d n (n + 1) (ULift.up y) = (p.app a).f (n + 1) 0 := by
      rw [map_zero]
      exact ULift.ext hy
    obtain ⟨x, hx, hp⟩ := liftPrimitiveOfQuasiIso hs hq a n 0 (map_zero _) (ULift.up y) he
    exact ⟨x, hx, congrArg ULift.down hp⟩
  · intro a n x hx
    generalize hm : n - 1 = m
    obtain rfl : m + 1 = n := by omega
    rintro ⟨y, hy⟩
    have he : (N.complex a).d m (m + 1) (ULift.up y) = (p.app a).f (m + 1) x :=
      ULift.ext hy
    obtain ⟨z, hz, _⟩ := liftPrimitiveOfQuasiIso hs hq a m x hx (ULift.up y) he
    exact ⟨z, hz⟩

end
end DerivedFormalization.RightDGModule
