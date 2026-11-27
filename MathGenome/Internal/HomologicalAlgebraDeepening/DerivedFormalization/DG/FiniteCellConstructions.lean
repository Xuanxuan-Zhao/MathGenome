import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.FiniteCellConstructions
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFree
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Yoneda
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CellLift
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CoefficientLiftComparison
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Basic.Finite.Sum
import Batteries.Tactic.OpenPrivate

universe u v w j t

namespace DerivedFormalization.RightDGModule

variable {k : Type u} [CommRing k]

noncomputable abbrev pretr (A : DGCategoryModel.{u,v,w} k) :=
  Specs.DerivedFormalization.DG.FiniteCellConstructions.pretr A

noncomputable abbrev pretrInclusion (A : DGCategoryModel.{u,v,w} k) :=
  Specs.DerivedFormalization.DG.FiniteCellConstructions.pretrInclusion A


open CategoryTheory HomologicalComplex
open Specs.DerivedFormalization.DG
open FiniteCellConstructions (FiniteIndex finiteSum zeroModule writtenSet writtenStage
  WrittenStep WrittenObject WrittenCode evalWrittenCode writtenModule pretrRepresentable)
open SemiFree (Presentation finiteCell attach inclusion)

noncomputable section

variable {A : DGCategoryModel.{u,v,w} k} {M N : RightDGModule A}

private theorem strict_ext {f g : M ⟶ N}
    (h : ∀ a i (x : (M.complex a).X i), (f.app a).f i x = (g.app a).f i x) : f = g := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  exact LinearMap.ext (h a i)

private def mapOfComponents (g : ∀ a i, (M.complex a).X i →ₗ[k] (N.complex a).X i)
    (hd : ∀ a i x, (N.complex a).d i (i+1) (g a i x) = g a (i+1) ((M.complex a).d i (i+1) x))
    (ha : ∀ a b i j n (h : i+j = n) x f,
      g a n (M.act i j n h x f) = N.act i j n h (g b i x) f) : M ⟶ N where
  app a := CochainComplex.ofHom (fun i => ModuleCat.ofHom (g a i)) (by
    intro i
    apply ModuleCat.hom_ext
    exact LinearMap.ext (hd a i))
  comm_act := ha _ _

private theorem strict_d (f : M ⟶ N) (a : A.Obj) (i : ℤ) (x : (M.complex a).X i) :
    (N.complex a).d i (i+1) ((f.app a).f i x) = (f.app a).f (i+1) ((M.complex a).d i (i+1) x) :=
  CategoryTheory.congr_fun ((f.app a).comm i (i+1)) x

private def strictIso (f : M ⟶ N)
    (hf : ∀ a i, Function.Bijective ((f.app a).f i)) : M ≅ N := by
  let E (a : A.Obj) (i : ℤ) := LinearEquiv.ofBijective ((f.app a).f i).hom (hf a i)
  let g (a : A.Obj) (i : ℤ) := (E a i).symm.toLinearMap
  have hg (a : A.Obj) (i : ℤ) (x : (N.complex a).X i) : (f.app a).f i (g a i x) = x :=
    (E a i).apply_symm_apply x
  refine ⟨f, mapOfComponents g ?_ ?_, ?_, ?_⟩
  · intro a i x
    apply (hf a (i+1)).1
    rw [← strict_d, hg, hg]
  · intro a b i j n h x f'
    apply (hf a n).1
    rw [hg, f.comm_act, hg]
  · apply strict_ext
    intro a i x
    exact (E a i).symm_apply_apply x
  · apply strict_ext
    exact hg

private theorem iso_hom_bijective (e : M ≅ N) (a : A.Obj) (i : ℤ) :
    Function.Bijective ((e.hom.app a).f i) := by
  let E := (RightDGModuleModel.degree a i).mapIso e
  exact E.toLinearEquiv.bijective

theorem finiteCell_of_iso (e : M ≅ N) : finiteCell M → finiteCell N := by
  rintro ⟨F, hf⟩
  refine ⟨{ F with
    into := fun j => F.into j ≫ e.hom
    compatible := fun j => by simpa only [Category.assoc] using congrArg (fun g => g ≫ e.hom) (F.compatible j)
    injective := fun j a i => (iso_hom_bijective e a i).1.comp (F.injective j a i)
    exhaustive := ?_ }, hf⟩
  intro a i x
  obtain ⟨y, rfl⟩ := (iso_hom_bijective e a i).2 x
  obtain ⟨j, z, hz⟩ := F.exhaustive a i y
  exact ⟨j, z, congrArg ((e.hom.app a).f i) hz⟩

private theorem zeroModule_element (a : A.Obj) (i : ℤ) (x : ((zeroModule A).complex a).X i) :
    x = 0 := by
  apply DFinsupp.ext
  exact fun s => Fin.elim0 s.down

private def emptyFamily (P : RightDGModule A) : CellFamily P (FiniteIndex.{v} 0) where
  object s := Fin.elim0 s.down
  degree s := Fin.elim0 s.down
  boundary s := Fin.elim0 s.down
  closed s := Fin.elim0 s.down

private def emptyAttachment (P : RightDGModule A) :
    P ≅ attach (emptyFamily P) :=
  strictIso (inclusion (emptyFamily P)) fun a i => by
    constructor
    · intro x y h
      exact congrArg Prod.fst h
    · intro ⟨x, y⟩
      refine ⟨x, Prod.ext rfl ?_⟩
      apply DFinsupp.ext
      exact fun s => Fin.elim0 s.down

private theorem writtenModule_injective (A : DGCategoryModel.{u,v,w} k) :
    Function.Injective (writtenModule A) := by
  intro x y
  induction x using Quotient.ind with
  | _ x =>
    induction y using Quotient.ind with
    | _ y =>
      intro h
      exact Quotient.sound (s := Setoid.ker (evalWrittenCode A)) h

private theorem writtenModule_range (A : DGCategoryModel.{u,v,w} k) :
    Set.range (writtenModule A) = writtenSet A := by
  ext M
  constructor
  · rintro ⟨x, rfl⟩
    induction x using Quotient.ind with
    | _ x => exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨Quotient.mk _ x, rfl⟩

private theorem writtenZero (A : DGCategoryModel.{u,v,w} k) : zeroModule A ∈ writtenSet A :=
  ⟨⟨0, Sum.inr ()⟩, rfl⟩

private theorem writtenRepresentable (a : A.Obj) : representable a ∈ writtenSet A :=
  ⟨⟨0, Sum.inl ⟨a⟩⟩, rfl⟩

private theorem writtenShift (h : M ∈ writtenSet A) (s : ℤ) : shift M s ∈ writtenSet A := by
  obtain ⟨⟨j, x⟩, rfl⟩ := h
  exact ⟨⟨j+1, WrittenStep.shift x s⟩, rfl⟩

private theorem writtenStage_mono {j l : ℕ} (hj : j ≤ l) (x : (writtenStage A j).1) :
    ∃ y : (writtenStage A l).1, (writtenStage A l).2 y = (writtenStage A j).2 x := by
  induction hj with
  | refl => exact ⟨x, rfl⟩
  | step _ ih =>
    obtain ⟨y, hy⟩ := ih
    exact ⟨WrittenStep.previous y, hy⟩

private theorem writtenSum {n : ℕ} (F : Fin n → RightDGModule A)
    (h : ∀ i, F i ∈ writtenSet A) : finiteSum F ∈ writtenSet A := by
  classical
  choose c hc using h
  let j := Finset.univ.sup fun i => (c i).1
  have H (i : Fin n) : ∃ y : (writtenStage A j).1, (writtenStage A j).2 y = F i := by
    obtain ⟨y, hy⟩ := writtenStage_mono (A := A)
      (Finset.le_sup (f := fun i => (c i).1) (Finset.mem_univ i)) (c i).2
    exact ⟨y, hy.trans (hc i)⟩
  choose y hy using H
  refine ⟨⟨j+1, WrittenStep.sum n y⟩, ?_⟩
  change finiteSum ((writtenStage A j).2 ∘ y) = finiteSum F
  rw [show (writtenStage A j).2 ∘ y = F from funext hy]

private theorem cone_of_eq {M' N' : RightDGModule A} (hm : M' = M) (hn : N' = N)
    (f : M ⟶ N) : cone (eqToHom hm ≫ f ≫ eqToHom hn.symm) = cone f := by
  subst M' N'
  simp

private theorem writtenCone (hM : M ∈ writtenSet A) (hN : N ∈ writtenSet A)
    (f : M ⟶ N) : cone f ∈ writtenSet A := by
  obtain ⟨⟨j, x⟩, rfl⟩ := hM
  obtain ⟨⟨l, y⟩, rfl⟩ := hN
  obtain ⟨x', hx⟩ := writtenStage_mono (A := A) (le_max_left j l) x
  obtain ⟨y', hy⟩ := writtenStage_mono (A := A) (le_max_right j l) y
  let g : (writtenStage A (max j l)).2 x' ⟶ (writtenStage A (max j l)).2 y' :=
    eqToHom hx ≫ f ≫ eqToHom hy.symm
  refine ⟨⟨max j l + 1, WrittenStep.cone x' y' g⟩, ?_⟩
  exact cone_of_eq hx hy f

private def writtenYoneda (A : DGCategoryModel.{u,v,w} k) :
    DGFunctorModel (Yoneda.liftCategory A) (pretr A) where
  obj := pretrRepresentable A
  map := (yoneda A).map
  map_id := (yoneda A).map_id
  map_comp := (yoneda A).map_comp

open private yonedaIso_laws from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Yoneda

theorem yonedaFactorization : FiniteCellConstructions.YonedaFactorization.{u,v,w} := by
  intro k _ A
  exact ⟨yonedaIso (A := A), yonedaIso_laws (A := A), writtenYoneda A, rfl, fun _ _ => HEq.rfl,
    fun a b => yoneda_map_isIso (A := A) a b⟩

private def strictSumReindex {I : Type j} {J : Type v} (e : I ≃ J)
    {F : I → RightDGModule A} {S : RightDGModule A} (D : IndexedSemiFree.StrictSum F S) :
    S ≅ directSum (F ∘ e.symm) := by
  classical
  let E (a : A.Obj) (i : ℤ) :
      (S.complex a).X i ≃ₗ[k] ((directSum (F ∘ e.symm)).complex a).X i :=
    (D.coordinates a i).trans (DirectSum.lequivCongrLeft k e)
  let g := mapOfComponents (fun a i => (E a i).toLinearMap)
    (fun a i x => by
      apply DFinsupp.ext
      intro s
      change (((directSum (F ∘ e.symm)).complex a).d i (i+1) (E a i x)) s =
        E a (i+1) ((S.complex a).d i (i+1) x) s
      rw [SemiFree.directSum_d (F ∘ e.symm)]
      simp only [E, LinearEquiv.trans_apply, DirectSum.lequivCongrLeft_apply, Function.comp_apply]
      exact (D.coordinate_d a i x (e.symm s)).symm)
    (fun a b i j n h x f => by
      apply DFinsupp.ext
      intro s
      change E a n (S.act i j n h x f) s =
        SemiFree.sumAct (F ∘ e.symm) i j n h (E b i x) f s
      simp only [E, LinearEquiv.trans_apply, DirectSum.lequivCongrLeft_apply,
        SemiFree.sumAct_apply, Function.comp_apply]
      exact D.coordinate_act i j n h x f (e.symm s))
  exact strictIso g (fun a i => (E a i).bijective)

private def sumReindex {I J : Type v} (e : I ≃ J) (F : I → RightDGModule A) :
    directSum F ≅ directSum (F ∘ e.symm) :=
  strictSumReindex e (DG.IndexedSums.nativeSum F)

private theorem exists_written_finite_sum {I : Type v} [Finite I] (F : I → RightDGModule A)
    (h : ∀ i, F i ∈ writtenSet A) :
    ∃ S ∈ writtenSet A, Nonempty (S ≅ directSum F) := by
  classical
  let _ := Fintype.ofFinite I
  let e := Fintype.equivFin I
  let e' : I ≃ FiniteIndex.{v} (Fintype.card I) := e.trans Equiv.ulift.symm
  let G := F ∘ e.symm
  exact ⟨finiteSum G, writtenSum G (fun i => h (e.symm i)), ⟨(sumReindex e' F).symm⟩⟩

theorem writtenFiniteSum : FiniteCellConstructions.WrittenFiniteSum.{u,v,w} := by
  intro k _ A I _ F
  obtain ⟨S, hS, e⟩ := exists_written_finite_sum (writtenModule A ∘ F) (fun i => by
    rw [← writtenModule_range]
    exact ⟨F i, rfl⟩)
  rw [← writtenModule_range] at hS
  obtain ⟨X, rfl⟩ := hS
  exact ⟨X, e⟩


section Filtrations

private theorem inclusion_injective {I : Type v} (C : CellFamily M I) (a : A.Obj) (i : ℤ) :
    Function.Injective (((inclusion C).app a).f i) :=
  fun _ _ h => congrArg Prod.fst h

private theorem inclusion_surjective {I : Type v} [IsEmpty I] (C : CellFamily M I)
    (a : A.Obj) (i : ℤ) : Function.Surjective (((inclusion C).app a).f i) := by
  intro ⟨x, y⟩
  refine ⟨x, Prod.ext rfl ?_⟩
  apply DFinsupp.ext
  exact isEmptyElim

private theorem presentation_into_step (F : Presentation M) (a : A.Obj) (i : ℤ) (j : ℕ)
    (x : ((F.stage j).complex a).X i) :
    ((F.into (j+1)).app a).f i (((F.successor j).hom.app a).f i
      (((inclusion (F.family j)).app a).f i x)) = ((F.into j).app a).f i x :=
  congrArg (fun f : F.stage j ⟶ M => (f.app a).f i x) (F.compatible j)

private theorem exists_terminalStage (F : Presentation M) (hf : Finite (Σ j, F.index j)) :
    ∃ b, ∀ a i, Function.Bijective ((F.into b).app a |>.f i) := by
  classical
  let _ := Fintype.ofFinite (Σ j, F.index j)
  let b := Finset.univ.sup fun c : Σ j, F.index j => c.1 + 1
  have hempty (j : ℕ) (hb : b ≤ j) : IsEmpty (F.index j) := by
    refine ⟨fun x => ?_⟩
    have h : j + 1 ≤ b := Finset.le_sup (f := fun c : Σ j, F.index j => c.1 + 1)
      (Finset.mem_univ (⟨j,x⟩ : Σ j, F.index j))
    omega
  refine ⟨b, fun a i => ⟨F.injective b a i, ?_⟩⟩
  let R (j : ℕ) : Set ((M.complex a).X i) := Set.range ((F.into j).app a |>.f i)
  have hmono : Monotone R := monotone_nat_of_le_succ (fun j => by
    rintro y ⟨x, rfl⟩
    exact ⟨((F.successor j).hom.app a).f i (((inclusion (F.family j)).app a).f i x),
      presentation_into_step F a i j x⟩)
  have hstable (j : ℕ) (hj : b ≤ j) : R j ⊆ R b := by
    induction hj with
    | refl => exact fun _ hx => hx
    | @step j hj ih =>
      rintro y ⟨x, rfl⟩
      obtain ⟨z, rfl⟩ := (iso_hom_bijective (F.successor j) a i).2 x
      let _ := hempty j hj
      obtain ⟨x, rfl⟩ := inclusion_surjective (F.family j) a i z
      exact ih ⟨x, (presentation_into_step F a i j x).symm⟩
  intro x
  obtain ⟨j, y, hy⟩ := F.exhaustive a i x
  rcases le_total j b with hj | hj
  · exact hmono hj ⟨y, hy⟩
  · exact hstable j hj ⟨y, hy⟩

/-- A finite succession of free cell attachments, allowing a strict change
of presentation at each step. -/
private inductive AttachmentChain : RightDGModule A → RightDGModule A → Type (max u (v+1) w)
  | nil (P) : AttachmentChain P P
  | change {P Q R} (e : P ≅ Q) (tail : AttachmentChain Q R) : AttachmentChain P R
  | step {P Q R} {I : Type v} (C : CellFamily P I) (hI : Finite I)
      (e : attach C ≅ Q) (tail : AttachmentChain Q R) : AttachmentChain P R

private def AttachmentChain.trans {P Q R : RightDGModule A}
    (c : AttachmentChain P Q) (d : AttachmentChain Q R) : AttachmentChain P R :=
  match c with
  | .nil _ => d
  | .change e tail => .change e (tail.trans d)
  | .step C hI e tail => .step C hI e (tail.trans d)

private theorem presentation_chain (F : Presentation M) (hf : Finite (Σ j, F.index j))
    (j d : ℕ) : Nonempty (AttachmentChain (F.stage j) (F.stage (j+d))) := by
  induction d generalizing j with
  | zero => exact ⟨.nil _⟩
  | succ d ih =>
    have hI : Finite (F.index j) := Finite.of_injective (fun x => (⟨j,x⟩ : Σ j, F.index j))
      (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)
    obtain ⟨tail⟩ := ih (j+1)
    rw [show j + (d+1) = j+1+d by omega]
    exact ⟨.step (F.family j) hI (F.successor j) tail⟩

private def zeroIso (P : RightDGModule A) (h : ∀ a i (x : (P.complex a).X i), x = 0) :
    zeroModule A ≅ P :=
  strictIso 0 (by
    intro a i
    constructor
    · intro x y _
      rw [zeroModule_element a i x, zeroModule_element a i y]
    · intro y
      exact ⟨0, (h a i y).symm⟩)

private theorem finiteCell_chain (h : finiteCell M) :
    Nonempty (AttachmentChain (zeroModule A) M) := by
  obtain ⟨F, hF⟩ := h
  obtain ⟨b, hb⟩ := exists_terminalStage F hF
  obtain ⟨T⟩ := presentation_chain F hF 0 b
  rw [Nat.zero_add] at T
  exact ⟨.change (zeroIso _ F.bottom) (T.trans (.change (strictIso (F.into b) hb) (.nil M)))⟩

end Filtrations


section FiltrationAssembly

private structure BasedFiltration (P Q : RightDGModule A) where
  stage : ℕ → RightDGModule A
  base : P ≅ stage 0
  index : ℕ → Type v
  family (j : ℕ) : CellFamily (stage j) (index j)
  successor (j : ℕ) : attach (family j) ≅ stage (j+1)
  into (j : ℕ) : stage j ⟶ Q
  compatible (j : ℕ) : inclusion (family j) ≫ (successor j).hom ≫ into (j+1) = into j
  injective (j : ℕ) (a : A.Obj) (i : ℤ) : Function.Injective ((into j).app a |>.f i)
  exhaustive (a : A.Obj) (i : ℤ) (x : (Q.complex a).X i) :
    ∃ j y, ((into j).app a).f i y = x
  finite : Finite (Σ j, index j)

private def BasedFiltration.constant (P : RightDGModule A) : BasedFiltration P P where
  stage _ := P
  base := Iso.refl _
  index _ := FiniteIndex.{v} 0
  family _ := emptyFamily P
  successor _ := (emptyAttachment P).symm
  into _ := 𝟙 _
  compatible _ := by
    rw [Category.comp_id]
    exact (emptyAttachment P).hom_inv_id
  injective _ _ _ := fun _ _ h => h
  exhaustive _ _ x := ⟨0, x, rfl⟩
  finite := by
    let _ : IsEmpty (Σ _ : ℕ, FiniteIndex.{v} 0) := ⟨fun s => Fin.elim0 s.2.down⟩
    infer_instance

private def BasedFiltration.prepend {P Q R : RightDGModule A} {I : Type v}
    (C : CellFamily P I) (hI : Finite I) (e : attach C ≅ Q) (F : BasedFiltration Q R) :
    BasedFiltration P R where
  stage
    | 0 => P
    | j+1 => F.stage j
  base := Iso.refl P
  index
    | 0 => I
    | j+1 => F.index j
  family
    | 0 => C
    | j+1 => F.family j
  successor
    | 0 => e.trans F.base
    | j+1 => F.successor j
  into
    | 0 => inclusion C ≫ (e.trans F.base).hom ≫ F.into 0
    | j+1 => F.into j
  compatible
    | 0 => rfl
    | j+1 => F.compatible j
  injective
    | 0 => fun a i =>
      (F.injective 0 a i).comp ((iso_hom_bijective (e.trans F.base) a i).1.comp
        (inclusion_injective C a i))
    | j+1 => F.injective j
  exhaustive a i x := by
    obtain ⟨j, y, hy⟩ := F.exhaustive a i x
    exact ⟨j+1, y, hy⟩
  finite := by
    let _ := F.finite
    let E := (Equiv.sigmaNatSucc fun
      | 0 => I
      | j+1 => F.index j).symm
    exact Finite.of_equiv (I ⊕ (Σ j, F.index j)) E

private def AttachmentChain.filtration {P Q : RightDGModule A}
    (T : AttachmentChain P Q) : BasedFiltration P Q :=
  match T with
  | .nil P => .constant P
  | .change e T => { T.filtration with base := e.trans T.filtration.base }
  | .step C hI e T => T.filtration.prepend C hI e

private theorem AttachmentChain.finiteCell (T : AttachmentChain (zeroModule A) M) :
    finiteCell M := by
  let F := T.filtration
  refine ⟨⟨F.stage, ?_, F.index, F.family, F.successor, F.into, F.compatible,
    F.injective, F.exhaustive⟩, F.finite⟩
  intro a i x
  obtain ⟨y, rfl⟩ := (iso_hom_bijective F.base a i).2 x
  rw [zeroModule_element a i y, map_zero]

theorem finiteCellZero : FiniteCellConstructions.FiniteCellZero.{u,v,w} := by
  intro k _ A
  exact (AttachmentChain.nil (zeroModule A)).finiteCell

private theorem finiteCell_attach {I : Type v} [Finite I] (C : CellFamily M I)
    (hM : finiteCell M) : finiteCell (attach C) := by
  obtain ⟨T⟩ := finiteCell_chain hM
  exact (T.trans (.step C inferInstance (Iso.refl _) (.nil _))).finiteCell

private theorem finiteCell_induction (p : RightDGModule A → Prop)
    (zero : p (zeroModule A)) (iso : ∀ {P Q : RightDGModule A}, (P ≅ Q) → p P → p Q)
    (step : ∀ {P : RightDGModule A} {I : Type v} [Finite I] (C : CellFamily P I), p P → p (attach C))
    (h : finiteCell M) : p M := by
  obtain ⟨T⟩ := finiteCell_chain h
  have H {X Y : RightDGModule A} (T : AttachmentChain X Y) : p X → p Y := by
    induction T with
    | nil _ => exact id
    | change e _ ih => exact fun h => ih (iso e h)
    | step C hI e _ ih => exact fun h => ih (iso e (step C h))
  exact H T zero

end FiltrationAssembly

section CellMaps

private def degreeIso (K : ModuleCochain.{u,v} k) {p q : ℤ} (h : p = q) :
    K.X p ≃ₗ[k] K.X q :=
  (K.XIsoOfEq h).toLinearEquiv

@[simp] private theorem degreeIso_rfl (K : ModuleCochain.{u,v} k) (p : ℤ)
    (x : K.X p) : degreeIso K (rfl : p = p) x = x := rfl

private theorem degreeIso_d (K : ModuleCochain.{u,v} k) {p q p' q' : ℤ}
    (e : p = q) (e' : p' = q') (x : K.X p) :
    degreeIso K e' (K.d p p' x) = K.d q q' (degreeIso K e x) := by
  subst q q'
  rfl

private theorem degreeIso_sign (K : ModuleCochain.{u,v} k) {p q : ℤ}
    (e : p = q) (c : ℤˣ) (x : K.X p) :
    degreeIso K e (c • x) = c • degreeIso K e x := by
  simp only [Units.smul_def, map_zsmul]

private theorem degreeIso_act (P : RightDGModule A) {a b : A.Obj} {i i' j j' n n' : ℤ}
    (ei : i = i') (ej : j = j') (en : n = n') (h : i+j = n) (h' : i'+j' = n')
    (x : (P.complex b).X i) (f : (A.hom a b).X j) :
    degreeIso (P.complex a) en (P.act i j n h x f) =
      P.act i' j' n' h' (degreeIso (P.complex b) ei x) (degreeIso (A.hom a b) ej f) := by
  subst i' j' n'
  rfl

private theorem degreeIso_gen (a : A.Obj) {p q : ℤ} (hp : 0 = p) (hq : 0 = q)
    (e : p = q) :
    degreeIso (A.hom a a) e (degreeIso (A.hom a a) hp (A.id a)) =
      degreeIso (A.hom a a) hq (A.id a) := by
  subst p q
  rfl

private theorem act_assoc_degrees (P : RightDGModule A) {a b c : A.Obj}
    {r i j p q n : ℤ} (hp : r+i = p) (hq : i+j = q) (hn : p+j = n)
    (z : (P.complex c).X r) (x : (A.hom b c).X i) (f : (A.hom a b).X j) :
    P.act r q n (by omega) z (A.comp i j q hq x f) =
      P.act p j n hn (P.act r i p hp z x) f := by
  subst p q n
  exact (P.act_assoc r i j z x f).symm

private theorem boundaryMap_d (P : RightDGModule A) {a b : A.Obj} (r p q q' : ℤ)
    (hp : r+q = p) (hq : q+1 = q')
    (z : (P.complex a).X r) (hz : (P.complex a).d r (r+1) z = 0)
    (x : (A.hom b a).X q) :
    (P.complex b).d p (p+1) (P.act r q p hp z x) =
      P.act r q' (p+1) (by omega) z (((-r).negOnePow • (A.hom b a).d q q') x) := by
  subst q'
  rw [P.leibniz, hz]
  simp only [map_zero, LinearMap.zero_apply, zero_add, ModuleCat.hom_smul,
    LinearMap.smul_apply, Int.negOnePow_neg, Units.smul_def, map_zsmul]

private def boundaryMap (P : RightDGModule A) (a : A.Obj) (r : ℤ)
    (z : (P.complex a).X r) (hz : (P.complex a).d r (r+1) z = 0) :
    freeCell a r ⟶ P :=
  mapOfComponents (fun b i => P.act r (i + -r) i (by omega) z) (by
    intro b i x
    exact boundaryMap_d P r i (i + -r) (i+1 + -r) (by omega) (by omega) z hz x) (by
    intro b c i j n h x f
    exact act_assoc_degrees P (by omega) (by omega) h z x f)

end CellMaps


section CellReindexing

variable {I : Type v}
variable (O : I → A.Obj) (d e : I → ℤ) (s : ℤ) (he : ∀ t, e t = d t - s)

private abbrev cellModules (O : I → A.Obj) (d : I → ℤ) (t : I) : RightDGModule A :=
  freeCell (O t) (d t)

private def reindexCell (a : A.Obj) (i : ℤ) (t : I) :
    ((cellModules O e t).complex a).X i ≃ₗ[k] ((cellModules O d t).complex a).X (i+s) :=
  degreeIso (A.hom a (O t)) (by have := he t; omega)

private def reindexCells (a : A.Obj) (i : ℤ) :
    SemiFree.SumTerm (cellModules O e) a i ≃ₗ[k] SemiFree.SumTerm (cellModules O d) a (i+s) :=
  DirectSum.congrLinearEquiv (reindexCell O d e s he a i)

@[simp] private theorem reindexCells_apply (a : A.Obj) (i : ℤ)
    (x : SemiFree.SumTerm (cellModules O e) a i) (t : I) :
    reindexCells O d e s he a i x t = reindexCell O d e s he a i t (x t) := rfl

private theorem reindexCells_single (a : A.Obj) (i : ℤ) (t : I)
    (x : ((cellModules O e t).complex a).X i) :
    reindexCells O d e s he a i (SemiFree.summand (cellModules O e) a i t x) =
      SemiFree.summand (cellModules O d) a (i+s) t (reindexCell O d e s he a i t x) := by
  classical
  exact DirectSum.lmap_lof (fun t => (reindexCell O d e s he a i t).toLinearMap) t x

private theorem directSum_d_at (F : I → RightDGModule A) (a : A.Obj)
    (i j : ℤ) (h : i+1 = j) (x : SemiFree.SumTerm F a i) (t : I) :
    ((directSum F).complex a).d i j x t = ((F t).complex a).d i j (x t) := by
  subst j
  exact SemiFree.directSum_d F a i x t

private theorem reindexCells_d (a : A.Obj) (i : ℤ)
    (x : SemiFree.SumTerm (cellModules O e) a i) :
    reindexCells O d e s he a (i+1) (((directSum (cellModules O e)).complex a).d i (i+1) x) =
      s.negOnePow • (((directSum (cellModules O d)).complex a).d (i+s) (i+1+s)
        (reindexCells O d e s he a i x)) := by
  apply DFinsupp.ext
  intro t
  rw [reindexCells_apply, SemiFree.directSum_d]
  change reindexCell O d e s he a (i+1) t (_) =
    s.negOnePow • ((((directSum (cellModules O d)).complex a).d (i+s) (i+1+s)
      (reindexCells O d e s he a i x)) t)
  rw [directSum_d_at _ a _ _ (by omega), reindexCells_apply]
  change degreeIso (A.hom a (O t)) _ (((-e t).negOnePow •
      (A.hom a (O t)).d (i + -e t) (i+1 + -e t)) (x t)) =
    s.negOnePow • (((-d t).negOnePow • (A.hom a (O t)).d (i+s + -d t)
      (i+1+s + -d t)) (degreeIso (A.hom a (O t)) _ (x t)))
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply, degreeIso_sign, smul_smul]
  rw [degreeIso_d _ (show i + -e t = i+s + -d t by have := he t; omega) _,
    ← Int.negOnePow_add]
  congr 1
  exact congrArg Int.negOnePow (by have := he t; omega)

private theorem reindexCells_act {a b : A.Obj} (i j n : ℤ) (h : i+j = n)
    (x : SemiFree.SumTerm (cellModules O e) b i) (f : (A.hom a b).X j) :
    reindexCells O d e s he a n (SemiFree.sumAct (cellModules O e) i j n h x f) =
      SemiFree.sumAct (cellModules O d) (i+s) j (n+s) (by omega)
        (reindexCells O d e s he b i x) f := by
  apply DFinsupp.ext
  intro t
  simp only [reindexCells_apply, SemiFree.sumAct_apply]
  exact degreeIso_act (representable (O t)) _ rfl _ _ _ (x t) f

end CellReindexing


section AttachmentCone

variable {I : Type v} (C : CellFamily M I)

private abbrev previousCells (t : I) : RightDGModule A :=
  freeCell (C.object t) (C.degree t+1)

private def attachmentConeMap : directSum (previousCells C) ⟶ M :=
  sumDesc _ (fun s => boundaryMap M (C.object s) (C.degree s+1) (C.boundary s) (C.closed s))

private def attachmentConeCoefficients (a : A.Obj) (i : ℤ) :
    SemiFree.SumTerm (SemiFree.cells C) a i ≃ₗ[k] SemiFree.SumTerm (previousCells C) a (i+1) :=
  reindexCells C.object (fun s => C.degree s+1) C.degree 1 (fun _ => by omega) a i

private theorem attachmentConeCoefficients_d (a : A.Obj) (i : ℤ)
    (x : SemiFree.SumTerm (SemiFree.cells C) a i) :
    attachmentConeCoefficients C a (i+1)
      (((SemiFree.cellSum C).complex a).d i (i+1) x) =
      -(((directSum (previousCells C)).complex a).d (i+1) (i+1+1)
        (attachmentConeCoefficients C a i x)) := by
  have h := reindexCells_d C.object (fun s => C.degree s+1) C.degree 1 (fun _ => by omega) a i x
  rw [Int.negOnePow_one, Units.neg_smul, one_smul] at h
  exact h

private theorem sumDesc_summand {I : Type v} (F : I → RightDGModule A) (g : ∀ s, F s ⟶ M)
    (a : A.Obj) (i : ℤ) (s : I) (x : ((F s).complex a).X i) :
    ((sumDesc F g).app a).f i (SemiFree.summand F a i s x) = ((g s).app a).f i x :=
  congrArg (fun f : F s ⟶ M => (f.app a).f i x) (sumInclusion_desc F g s)

private theorem attachmentConeMap_apply (a : A.Obj) (i : ℤ)
    (x : SemiFree.SumTerm (SemiFree.cells C) a i) :
    ((attachmentConeMap C).app a).f (i+1) (attachmentConeCoefficients C a i x) =
      SemiFree.attachingMap C a i x := by
  induction x using SemiFree.sum_induction (SemiFree.cells C) with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single s x =>
    rw [SemiFree.attachingMap_summand]
    change ((attachmentConeMap C).app a).f (i+1)
      (reindexCells C.object (fun s => C.degree s+1) C.degree 1 _
        a i (SemiFree.summand (SemiFree.cells C) a i s x)) = _
    rw [reindexCells_single]
    change ((sumDesc (previousCells C) _).app a).f (i+1)
      (SemiFree.summand (previousCells C) a (i+1) s _) = _
    rw [sumDesc_summand]
    exact (degreeIso_act M (a := a) (b := C.object s) rfl
      (show i + -C.degree s = i+1 + -(C.degree s+1) by omega) rfl
      (by omega) (by omega) (C.boundary s) x).symm

private def attachmentConeIso : attach C ≅ cone (attachmentConeMap C) := by
  let E (a : A.Obj) (i : ℤ) :
      ((attach C).complex a).X i ≃ₗ[k] ((cone (attachmentConeMap C)).complex a).X i :=
    (LinearEquiv.refl k ((M.complex a).X i)).prodCongr (attachmentConeCoefficients C a i)
  let g := mapOfComponents (fun a i => (E a i).toLinearMap)
    (fun a i x => by
      change ShiftCone.coneDiff _ a i (i+1) (x.1, attachmentConeCoefficients C a i x.2) =
        E a (i+1) ((SemiFree.attachComplex C a).d i (i+1) x)
      rw [ShiftCone.coneDiff_succ, SemiFree.attachComplex_d, attachmentConeMap_apply]
      exact Prod.ext rfl (attachmentConeCoefficients_d C a i x.2).symm)
    (fun a b i j n h x f => by
      apply Prod.ext
      · rfl
      · exact reindexCells_act C.object (fun s => C.degree s+1) C.degree 1
          (fun _ => by omega) i j n h x.2 f)
  exact strictIso g (fun a i => (E a i).bijective)

end AttachmentCone


section TriangularExtensions

variable {B T : RightDGModule A} {I : Type v} (O : I → A.Obj) (D : I → ℤ)

private abbrev ExtensionTerm (B : RightDGModule A) (O : I → A.Obj) (D : I → ℤ)
    (a : A.Obj) (i : ℤ) :=
  (B.complex a).X i × SemiFree.SumTerm (cellModules O D) a i


/-- Recognize a cell attachment in a graded splitting whose matrix differential
has the preceding module and the free cells on the diagonal. -/
private theorem attachment_of_matrix
    (g : ∀ a i, SemiFree.SumTerm (cellModules O D) a i →ₗ[k] (B.complex a).X (i+1))
    (θ : ∀ a i, ExtensionTerm B O D a i ≃ₗ[k] (T.complex a).X i)
    (ha : ∀ a b i j n (h : i+j = n) (p : ExtensionTerm B O D b i) f,
      T.act i j n h (θ b i p) f =
      θ a n (B.act i j n h p.1 f, SemiFree.sumAct (cellModules O D) i j n h p.2 f))
    (hd : ∀ a i (p : ExtensionTerm B O D a i),
      (T.complex a).d i (i+1) (θ a i p) =
      θ a (i+1) ((B.complex a).d i (i+1) p.1 + g a i p.2,
        ((directSum (cellModules O D)).complex a).d i (i+1) p.2)) :
    ∃ C : CellFamily B I, Nonempty (attach C ≅ T) := by
  let F := cellModules O D
  have hg (a b : A.Obj) (i j n : ℤ) (h : i+j = n)
      (x : SemiFree.SumTerm F b i) (f : (A.hom a b).X j) :
      g a n (SemiFree.sumAct F i j n h x f) =
        B.act (i+1) j (n+1) (by omega) (g b i x) f := by
    have H := T.leibniz i j n h (θ b i (0,x)) f
    rw [ha, hd, hd, ha, ha] at H
    simp only [map_zero, LinearMap.zero_apply, zero_add] at H
    rw [Units.smul_def, ← map_zsmul, ← map_add] at H
    have hfirst := congrArg Prod.fst ((θ a (n+1)).injective H)
    simpa only [Prod.fst_add, Prod.smul_fst, zsmul_zero, add_zero] using hfirst
  let gen (s : I) := SemiFree.summand F (O s) (D s) s (cellGenerator (O s) (D s))
  have hgen (s : I) : ((directSum F).complex (O s)).d (D s) (D s+1) (gen s) = 0 := by
    change ((directSum F).complex (O s)).d (D s) (D s+1) (SemiFree.summand F _ _ s _) = 0
    rw [SemiFree.directSum_d_summand, show ((F s).complex (O s)).d (D s) (D s+1)
      (cellGenerator (O s) (D s)) = 0 from cellGenerator_d _ _, map_zero]
  let C : CellFamily B I :=
    { object := O
      degree := D
      boundary := fun s => g (O s) (D s) (gen s)
      closed := by
        intro s
        have hh := CategoryTheory.congr_fun
          (HomologicalComplex.d_comp_d (T.complex (O s)) (D s) (D s+1) (D s+1+1))
          (θ (O s) (D s) (0, gen s))
        change (T.complex (O s)).d _ _
          ((T.complex (O s)).d _ _ (θ (O s) (D s) (0, gen s))) = 0 at hh
        rw [hd, hd, hgen]
          at hh
        simp only [map_zero, zero_add, add_zero] at hh
        exact congrArg Prod.fst ((θ (O s) (D s+1+1)).injective
          (hh.trans (map_zero (θ (O s) (D s+1+1))).symm)) }
  have hg' (a : A.Obj) (i : ℤ) (x : SemiFree.SumTerm F a i) :
      g a i x = SemiFree.attachingMap C a i x := by
    induction x using SemiFree.sum_induction F with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single s x =>
      have gen_act (j q : ℤ) (h : D s+j = q) (y : (A.hom a (O s)).X j) :
          (F s).act (D s) j q h (cellGenerator (O s) (D s)) y =
          degreeIso (A.hom a (O s)) (show j = q + -D s by omega) y := by
        subst q
        exact cellGenerator_mul (O s) (D s) a j y
      have hact : SemiFree.sumAct F (D s) (i + -D s) i (by omega) (gen s) x =
          SemiFree.summand F a i s x := by
        change SemiFree.sumAct F _ _ _ _ (SemiFree.summand F _ _ s _) x = _
        rw [SemiFree.sumAct_summand, gen_act, degreeIso_rfl]
      rw [SemiFree.attachingMap_summand, ← hact, hg]
  let f : attach C ⟶ T := mapOfComponents (fun a i => (θ a i).toLinearMap)
    (fun a i p => by
      change (T.complex a).d i (i+1) (θ a i p) = θ a (i+1) ((SemiFree.attachComplex C a).d i (i+1) p)
      rw [hd, SemiFree.attachComplex_d, ← hg'])
    (fun a b i j n h p f => (ha a b i j n h p f).symm)
  exact ⟨C, ⟨strictIso f (fun a i => (θ a i).bijective)⟩⟩

end TriangularExtensions


section ConeComparison

variable {M' N' : RightDGModule A}

private def coneMapOfSquare (f : M ⟶ N) (g : M' ⟶ N')
    (p : M ⟶ M') (q : N ⟶ N') (h : p ≫ g = f ≫ q) : cone f ⟶ cone g :=
  mapOfComponents (fun a i => ((q.app a).f i).hom.prodMap ((p.app a).f (i+1)).hom)
    (fun a i x => by
      change ShiftCone.coneDiff g a i (i+1) (((q.app a).f i x.1), (p.app a).f (i+1) x.2) =
        LinearMap.prodMap ((q.app a).f (i+1)).hom ((p.app a).f (i+1+1)).hom
          (ShiftCone.coneDiff f a i (i+1) x)
      rw [ShiftCone.coneDiff_succ, ShiftCone.coneDiff_succ]
      apply Prod.ext
      · change (N'.complex a).d i (i+1) ((q.app a).f i x.1) +
          (g.app a).f (i+1) ((p.app a).f (i+1) x.2) =
          (q.app a).f (i+1) ((N.complex a).d i (i+1) x.1 + (f.app a).f (i+1) x.2)
        rw [map_add, strict_d]
        exact congrArg (_ + ·) (congrArg (fun t : M ⟶ N' => (t.app a).f (i+1) x.2) h)
      · change -(M'.complex a).d (i+1) (i+1+1) ((p.app a).f (i+1) x.2) =
          (p.app a).f (i+1+1) (-(M.complex a).d (i+1) (i+1+1) x.2)
        rw [strict_d, map_neg])
    (fun a b i j n h x z => by
      exact Prod.ext (q.comm_act i j n h x.1 z)
        (p.comm_act (i+1) j (n+1) (by omega) x.2 z))

private def coneIsoOfSquare (f : M ⟶ N) (g : M' ⟶ N')
    (p : M ≅ M') (q : N ≅ N') (h : p.hom ≫ g = f ≫ q.hom) : cone f ≅ cone g :=
  strictIso (coneMapOfSquare f g p.hom q.hom h) fun a i =>
    (iso_hom_bijective q a i).prodMap (iso_hom_bijective p a (i+1))

private def sumEvaluation {I : Type v} (F : I → RightDGModule A) (t : I) (a : A.Obj) (i : ℤ) :
    SemiFree.SumTerm F a i →ₗ[k] ((F t).complex a).X i where
  toFun x := x t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem sumEvaluation_summand {I : Type v} (F : I → RightDGModule A) (t : I)
    (a : A.Obj) (i : ℤ) (x : ((F t).complex a).X i) :
    sumEvaluation F t a i (SemiFree.summand F a i t x) = x := by
  classical
  exact DFinsupp.single_eq_same

private def singletonSumIso {I : Type v} [Subsingleton I] (F : I → RightDGModule A) (t : I) :
    directSum F ≅ F t :=
  strictIso
    (mapOfComponents (sumEvaluation F t)
      (fun a i x => (SemiFree.directSum_d F a i x t).symm)
      (fun _ _ _ _ _ _ _ _ => rfl))
    (fun a i => ⟨fun x y h => DFinsupp.ext fun s => by
      obtain rfl : t = s := Subsingleton.elim _ _
      exact h, fun x => ⟨SemiFree.summand F a i t x, sumEvaluation_summand F t a i x⟩⟩)

theorem singletonAttachmentCone : FiniteCellConstructions.SingletonAttachmentCone.{u,v,w} := by
  intro k _ A P a n z hz
  let C := FiniteCellConstructions.singletonCell P a n z hz
  let t : FiniteIndex.{v} 1 := ⟨0⟩
  let f := boundaryMap P a (n+1) z hz
  let U := singletonSumIso (previousCells C) t
  have h : U.hom ≫ f = attachmentConeMap C ≫ 𝟙 P := by
    rw [Category.comp_id]
    apply sum_hom_ext (previousCells C)
    intro s
    obtain rfl : t = s := Subsingleton.elim _ _
    change sumInclusion (previousCells C) t ≫ U.hom ≫ f =
      sumInclusion (previousCells C) t ≫ sumDesc (previousCells C) _
    rw [sumInclusion_desc]
    apply strict_ext
    intro b i x
    change (f.app b).f i (sumEvaluation (previousCells C) t b i
      (SemiFree.summand (previousCells C) b i t x)) = (f.app b).f i x
    rw [sumEvaluation_summand]
  let e := (attachmentConeIso C).trans (coneIsoOfSquare _ f U (Iso.refl P) h)
  refine ⟨f, fun _ _ _ => rfl, e, ?_, ?_⟩
  · apply strict_ext
    intro b j x
    change (x, (attachmentConeCoefficients C b j 0) t) = (x, 0)
    rw [map_zero]
    rfl
  · change ((e.hom.app a).f n (attachedGenerator C t)) = (0, cellGenerator a (n+1))
    change (0, (reindexCells C.object (fun s => C.degree s+1) C.degree 1 _ a n
      (SemiFree.summand (SemiFree.cells C) a n t (cellGenerator a n))) t) =
      (0, cellGenerator a (n+1))
    have hR := reindexCells_single C.object (fun s => C.degree s+1) C.degree 1
      (fun _ => by omega) a n t (cellGenerator a n)
    have heval := congrArg (fun y : SemiFree.SumTerm (previousCells C) a (n+1) => y t) hR
    change _ = sumEvaluation (previousCells C) t a (n+1)
      (SemiFree.summand (previousCells C) a (n+1) t _) at heval
    rw [sumEvaluation_summand] at heval
    exact congrArg (fun y : ((freeCell a (n+1)).complex a).X (n+1) =>
      ((0 : (P.complex a).X n), y)) (heval.trans (degreeIso_gen a _ _ _))

end ConeComparison

section ShiftClosure

private def shiftIso (s : ℤ) (e : M ≅ N) : shift M s ≅ shift N s :=
  strictIso (ShiftCone.shiftMap s e.hom) fun a i => iso_hom_bijective e a (i+s)

private theorem shift_attach {I : Type v} (C : CellFamily M I) (s : ℤ) :
    ∃ C' : CellFamily (shift M s) I, Nonempty (attach C' ≅ shift (attach C) s) := by
  let D (t : I) := C.degree t - s
  let F := cellModules C.object D
  let E := reindexCells C.object C.degree D s (fun _ => rfl)
  let θ (a : A.Obj) (i : ℤ) :
      ExtensionTerm (shift M s) C.object D a i ≃ₗ[k] ((shift (attach C) s).complex a).X i :=
    (LinearEquiv.refl k ((M.complex a).X (i+s))).prodCongr (E a i)
  let g (a : A.Obj) (i : ℤ) :
      SemiFree.SumTerm F a i →ₗ[k] ((shift M s).complex a).X (i+1) :=
    (s.negOnePow : ℤ) •
      (((degreeIso (M.complex a) (show i+s+1 = (i+1)+s by omega)).toLinearMap.comp
        (SemiFree.attachingMap C a (i+s))).comp (E a i).toLinearMap)
  apply attachment_of_matrix C.object D g θ
  · intro a b i j n h p f
    apply Prod.ext
    · rfl
    · exact (reindexCells_act C.object C.degree D s (fun _ => rfl) i j n h p.2 f).symm
  · intro a i p
    change (s.negOnePow • (SemiFree.attachComplex C a).d (i+s) (i+1+s))
      (p.1, E a i p.2) =
      ( (s.negOnePow • (M.complex a).d (i+s) (i+1+s)) p.1 +
          (show (M.complex a).X (i+1+s) from g a i p.2),
        E a (i+1) (((directSum F).complex a).d i (i+1) p.2))
    have matrix (j : ℤ) (hj : i+s+1 = j) :
        (SemiFree.attachComplex C a).d (i+s) j (p.1, E a i p.2) =
          ((M.complex a).d (i+s) j p.1 +
            degreeIso (M.complex a) hj (SemiFree.attachingMap C a (i+s) (E a i p.2)),
           (SemiFree.cellSum C |>.complex a).d (i+s) j (E a i p.2)) := by
      subst j
      exact SemiFree.attachComplex_d C a (i+s) (p.1, E a i p.2)
    simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
    rw [matrix _ (by omega), Prod.smul_mk]
    apply Prod.ext
    · change s.negOnePow • (_ + _) = s.negOnePow • _ +
          (show (M.complex a).X (i+1+s) from g a i p.2)
      rw [smul_add]
      rfl
    · exact (reindexCells_d C.object C.degree D s (fun _ => rfl) a i p.2).symm

theorem finiteCellShift : FiniteCellConstructions.FiniteCellShift.{u,v,w} := by
  intro k _ A M s hM
  refine finiteCell_induction (fun M => finiteCell (shift M s)) ?_ ?_ ?_ hM
  · exact finiteCell_of_iso (zeroIso (shift (zeroModule A) s) fun a i x =>
      zeroModule_element a (i+s) x) (finiteCellZero A)
  · exact fun e => finiteCell_of_iso (shiftIso s e)
  · intro P I _ C hP
    obtain ⟨C', ⟨e⟩⟩ := shift_attach C s
    exact finiteCell_of_iso e (finiteCell_attach C' hP)

end ShiftClosure


section ConeClosure

private theorem cone_attach {I : Type v} (C : CellFamily M I) (f : attach C ⟶ N) :
    ∃ C' : CellFamily (cone (inclusion C ≫ f)) I, Nonempty (attach C' ≅ cone f) := by
  let D (t : I) := C.degree t - 1
  let F := cellModules C.object D
  let E := reindexCells C.object C.degree D 1 (fun _ => rfl)
  let U := cone (inclusion C ≫ f)
  let θ (a : A.Obj) (i : ℤ) :
      ExtensionTerm U C.object D a i ≃ₗ[k] ((cone f).complex a).X i :=
    (LinearEquiv.prodAssoc k ((N.complex a).X i) ((M.complex a).X (i+1))
      (SemiFree.SumTerm F a i)).trans
      ((LinearEquiv.refl k _).prodCongr ((LinearEquiv.refl k _).prodCongr (E a i)))
  let g (a : A.Obj) (i : ℤ) :
      SemiFree.SumTerm F a i →ₗ[k] (U.complex a).X (i+1) :=
    (((f.app a).f (i+1)).hom.comp ((LinearMap.inr k _ _).comp (E a i).toLinearMap)).prod
      (-(SemiFree.attachingMap C a (i+1)).comp (E a i).toLinearMap)
  apply attachment_of_matrix C.object D g θ
  · intro a b i j n h p x
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · exact (reindexCells_act C.object C.degree D 1 (fun _ => rfl) i j n h p.2 x).symm
  · intro a i p
    change ShiftCone.coneDiff f a i (i+1) (p.1.1, (p.1.2, E a i p.2)) =
      θ a (i+1) (ShiftCone.coneDiff (inclusion C ≫ f) a i (i+1) p.1 + g a i p.2,
        (((directSum F).complex a).d i (i+1) p.2))
    rw [ShiftCone.coneDiff_succ, ShiftCone.coneDiff_succ]
    apply Prod.ext
    · change (N.complex a).d i (i+1) p.1.1 + (f.app a).f (i+1) (p.1.2, E a i p.2) =
        (N.complex a).d i (i+1) p.1.1 + (f.app a).f (i+1) (p.1.2, 0) +
          (f.app a).f (i+1) (0, E a i p.2)
      rw [add_assoc, ← map_add]
      simp only [Prod.mk_add_mk, add_zero, zero_add]
    · change -((SemiFree.attachComplex C a).d (i+1) (i+1+1) (p.1.2, E a i p.2)) =
        (-(M.complex a).d (i+1) (i+1+1) p.1.2 +
          -SemiFree.attachingMap C a (i+1) (E a i p.2),
         E a (i+1) (((directSum F).complex a).d i (i+1) p.2))
      rw [SemiFree.attachComplex_d]
      apply Prod.ext
      · exact neg_add _ _
      · have h := reindexCells_d C.object C.degree D 1 (fun _ => rfl) a i p.2
        rw [Int.negOnePow_one, Units.neg_smul, one_smul] at h
        exact h.symm

theorem finiteCellCone : FiniteCellConstructions.FiniteCellCone.{u,v,w} := by
  intro k _ A P Q f hP hQ
  refine finiteCell_induction (fun P => ∀ f : P ⟶ Q, finiteCell (cone f)) ?_ ?_ ?_ hP f
  · intro g
    have e : Q ≅ cone g := strictIso (ShiftCone.coneInclusion g) fun a i => by
      constructor
      · intro x y h
        exact congrArg Prod.fst h
      · intro x
        exact ⟨x.1, Prod.ext rfl (zeroModule_element a (i+1) x.2).symm⟩
    exact finiteCell_of_iso e hQ
  · intro P P' e hp g
    have h : e.hom ≫ g = (e.hom ≫ g) ≫ (Iso.refl Q).hom := by simp
    exact finiteCell_of_iso (coneIsoOfSquare (e.hom ≫ g) g e (Iso.refl Q) h) (hp (e.hom ≫ g))
  · intro P I _ C hp g
    obtain ⟨C', ⟨e⟩⟩ := cone_attach C g
    exact finiteCell_of_iso e (finiteCell_attach C' (hp (inclusion C ≫ g)))

end ConeClosure


section Representables

theorem finiteCellRepresentable : FiniteCellConstructions.FiniteCellRepresentable.{u,v,w} := by
  intro k _ A a
  let I := FiniteIndex.{v} 1
  let t : I := ⟨0⟩
  let O : I → A.Obj := fun _ => a
  let D : I → ℤ := fun _ => 0
  let F := cellModules O D
  let B := zeroModule A
  let U := singletonSumIso F t
  let θ (b : A.Obj) (i : ℤ) :
      ExtensionTerm B O D b i ≃ₗ[k] ((representable a).complex b).X i :=
    (LinearEquiv.ofBijective (LinearMap.snd k ((B.complex b).X i) (SemiFree.SumTerm F b i))
      (by
        constructor
        · intro x y h
          exact Prod.ext ((zeroModule_element b i x.1).trans (zeroModule_element b i y.1).symm) h
        · intro y
          exact ⟨(0,y), rfl⟩)).trans
      (((RightDGModuleModel.degree b i).mapIso U).toLinearEquiv.trans
        (degreeIso (A.hom b a) (show i + -(0 : ℤ) = i by simp)))
  have ha : ∀ b c i j n (h : i+j = n) (p : ExtensionTerm B O D c i) f,
      (representable a).act i j n h (θ c i p) f =
      θ b n (B.act i j n h p.1 f, SemiFree.sumAct F i j n h p.2 f) := by
    intro b c i j n h p f
    change A.comp i j n h (degreeIso (A.hom c a) _ (p.2 t)) f =
      degreeIso (A.hom b a) _ ((SemiFree.sumAct F i j n h p.2 f) t)
    rw [SemiFree.sumAct_apply]
    exact (degreeIso_act (representable a) (show i + -(0 : ℤ) = i by simp) rfl
      (show n + -(0 : ℤ) = n by simp) _ h (p.2 t) f).symm
  have hd : ∀ b i (p : ExtensionTerm B O D b i),
      ((representable a).complex b).d i (i+1) (θ b i p) =
      θ b (i+1) ((B.complex b).d i (i+1) p.1 + 0,
        ((directSum F).complex b).d i (i+1) p.2) := by
    intro b i p
    change (A.hom b a).d i (i+1) (degreeIso (A.hom b a) _ (p.2 t)) =
      degreeIso (A.hom b a) _ ((((directSum F).complex b).d i (i+1) p.2) t)
    rw [SemiFree.directSum_d]
    change _ = degreeIso (A.hom b a) _
      ((((0 : ℤ).negOnePow • (A.hom b a).d (i + -(0 : ℤ)) (i+1 + -(0 : ℤ)))) (p.2 t))
    rw [Int.negOnePow_zero, one_smul]
    exact (degreeIso_d (A.hom b a) (show i + -(0 : ℤ) = i by simp)
      (show i+1 + -(0 : ℤ) = i+1 by simp) (p.2 t)).symm
  obtain ⟨C, ⟨e⟩⟩ := attachment_of_matrix O D (fun _ _ => 0) θ ha hd
  exact finiteCell_of_iso e (finiteCell_attach C (finiteCellZero A))

end Representables



section FiniteSums

variable {I : Type v} [Fintype I] (F : Option I → RightDGModule A)

private abbrev sumTail : RightDGModule A := directSum (F ∘ some)

private def sumTailProjection (a : A.Obj) (i : ℤ) :
    SemiFree.SumTerm F a i →ₗ[k] ((sumTail F).complex a).X i := by
  let E : SemiFree.SumTerm (F ∘ some) a i ≃ₗ[k] ((t : I) → ((F (some t)).complex a).X i) :=
    DFinsupp.linearEquivFunOnFintype
  let restrict : SemiFree.SumTerm F a i →ₗ[k] ((t : I) → ((F (some t)).complex a).X i) :=
    { toFun := fun x t => x (some t)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact E.symm.toLinearMap.comp restrict

@[simp] private theorem sumTailProjection_apply (a : A.Obj) (i : ℤ)
    (x : SemiFree.SumTerm F a i) (t : I) : sumTailProjection F a i x t = x (some t) := by
  let E : SemiFree.SumTerm (F ∘ some) a i ≃ₗ[k] ((t : I) → ((F (some t)).complex a).X i) :=
    DFinsupp.linearEquivFunOnFintype
  change (E.symm (fun t => x (some t))) t = x (some t)
  exact congrFun (E.apply_symm_apply (fun t => x (some t))) t

private def sumOptionCoefficients (a : A.Obj) (i : ℤ) :
    SemiFree.SumTerm F a i ≃ₗ[k] ((F none).complex a).X i × ((sumTail F).complex a).X i :=
  LinearEquiv.ofBijective ((sumEvaluation F none a i).prod (sumTailProjection F a i)) (by
    constructor
    · intro x y h
      apply DFinsupp.ext
      intro s
      cases s with
      | none => exact congrArg Prod.fst h
      | some t =>
        have ht := congrArg (fun z : ((F none).complex a).X i × ((sumTail F).complex a).X i =>
          z.2 t) h
        change sumTailProjection F a i x t = sumTailProjection F a i y t at ht
        exact (sumTailProjection_apply F a i x t).symm.trans
          (ht.trans (sumTailProjection_apply F a i y t))
    · intro ⟨x,y⟩
      let z : (t : Option I) → ((F t).complex a).X i := fun
        | none => x
        | some t => y t
      let E : SemiFree.SumTerm F a i ≃ₗ[k] ((t : Option I) → ((F t).complex a).X i) :=
        DFinsupp.linearEquivFunOnFintype
      let u := E.symm z
      have hu (t : Option I) : u t = z t := congrFun (E.apply_symm_apply z) t
      refine ⟨u, Prod.ext (hu none) ?_⟩
      apply DFinsupp.ext
      intro t
      change sumTailProjection F a i u t = y t
      rw [sumTailProjection_apply]
      exact hu (some t))

private def sumOptionConeIso :
    directSum F ≅ cone (0 : shift (sumTail F) (-1) ⟶ F none) := by
  let e (i : ℤ) : i = i+1 + (-1) := by omega
  let E (a : A.Obj) (i : ℤ) := degreeIso ((sumTail F).complex a) (e i)
  let θ (a : A.Obj) (i : ℤ) :
      ((directSum F).complex a).X i ≃ₗ[k]
        ((cone (0 : shift (sumTail F) (-1) ⟶ F none)).complex a).X i :=
    (sumOptionCoefficients F a i).trans ((LinearEquiv.refl k _).prodCongr (E a i))
  let f : directSum F ⟶ cone (0 : shift (sumTail F) (-1) ⟶ F none) :=
    mapOfComponents (fun a i => (θ a i).toLinearMap) (fun a i x => by
      change ShiftCone.coneDiff (0 : shift (sumTail F) (-1) ⟶ F none) a i (i+1)
        (x none, E a i (sumTailProjection F a i x)) =
        ((((directSum F).complex a).d i (i+1) x) none,
          E a (i+1) (sumTailProjection F a (i+1) (((directSum F).complex a).d i (i+1) x)))
      rw [ShiftCone.coneDiff_succ]
      apply Prod.ext
      · change ((F none).complex a).d i (i+1) (x none) + 0 =
          (((directSum F).complex a).d i (i+1) x) none
        rw [add_zero, SemiFree.directSum_d]
      · change -(((-1 : ℤ).negOnePow • ((sumTail F).complex a).d (i+1 + -1) (i+1+1 + -1))
            (E a i (sumTailProjection F a i x))) =
          E a (i+1) (sumTailProjection F a (i+1) (((directSum F).complex a).d i (i+1) x))
        simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul]
        change -(-(((sumTail F).complex a).d (i+1 + -1) (i+1+1 + -1)
            (E a i (sumTailProjection F a i x)))) = _
        rw [neg_neg]
        refine (degreeIso_d ((sumTail F).complex a) (e i) (e (i+1)) _).symm.trans ?_
        apply congrArg (E a (i+1))
        apply DFinsupp.ext
        intro t
        change (((directSum (F ∘ some)).complex a).d i (i+1) (sumTailProjection F a i x)) t =
          sumTailProjection F a (i+1) (((directSum F).complex a).d i (i+1) x) t
        rw [SemiFree.directSum_d (F ∘ some), sumTailProjection_apply,
          sumTailProjection_apply, SemiFree.directSum_d F]
        rfl) (fun a b i j n h x z => by
        apply Prod.ext
        · rfl
        · change E a n (sumTailProjection F a n (SemiFree.sumAct F i j n h x z)) =
            (sumTail F).act (i+1 + -1) j (n+1 + -1) (by omega)
              (E b i (sumTailProjection F b i x)) z
          refine Eq.trans ?_ (degreeIso_act (sumTail F) (e i) rfl (e n) h (by omega) _ z)
          apply congrArg (E a n)
          apply DFinsupp.ext
          intro t
          change sumTailProjection F a n (SemiFree.sumAct F i j n h x z) t =
            SemiFree.sumAct (F ∘ some) i j n h (sumTailProjection F b i x) z t
          rw [sumTailProjection_apply, SemiFree.sumAct_apply, SemiFree.sumAct_apply,
            sumTailProjection_apply]
          rfl)
  exact strictIso f (fun a i => (θ a i).bijective)

theorem finiteCellSum : FiniteCellConstructions.FiniteCellSum.{u,v,w} := by
  intro k _ A I _ F hF
  refine Finite.induction_empty_option
    (P := fun I : Type v => ∀ F : I → RightDGModule A, (∀ i, finiteCell (F i)) →
      finiteCell (directSum F)) ?_ ?_ ?_ I F hF
  · intro J K e hJ G hG
    let eG := sumReindex e (G ∘ e)
    have hEq : (G ∘ e) ∘ e.symm = G := funext fun t => congrArg G (e.apply_symm_apply t)
    rw [← hEq]
    exact finiteCell_of_iso eG (hJ (G ∘ e) fun j => hG (e j))
  · intro G _
    exact finiteCell_of_iso (zeroIso (directSum G) fun a i x =>
      DFinsupp.ext fun s => PEmpty.elim s) (finiteCellZero A)
  · intro J _ ih G hG
    exact finiteCell_of_iso (sumOptionConeIso G).symm (finiteCellCone 0
      (finiteCellShift (-1) (ih (G ∘ some) fun j => hG (some j))) (hG none))

end FiniteSums

section WrittenHull

private theorem finiteCell_writtenCode (A : DGCategoryModel.{u,v,w} k) (c : WrittenCode A) :
    finiteCell (evalWrittenCode A c) := by
  obtain ⟨j, x⟩ := c
  change finiteCell ((writtenStage A j).2 x)
  induction j with
  | zero =>
    change ULift.{v} A.Obj ⊕ Unit at x
    cases x with
    | inl a => exact finiteCellRepresentable a.down
    | inr _ => exact finiteCellZero A
  | succ j ih =>
    change WrittenStep A (writtenStage A j).2 at x
    cases x with
    | previous i => exact ih i
    | shift i s => exact finiteCellShift s (ih i)
    | sum n F =>
      exact finiteCellSum ((writtenStage A j).2 ∘ F ∘ ULift.down) (fun i => ih (F i.down))
    | cone i j f => exact finiteCellCone f (ih i) (ih j)

private theorem exists_written_rep (h : finiteCell M) :
    ∃ N ∈ writtenSet A, Nonempty (N ≅ M) := by
  refine finiteCell_induction (fun M => ∃ N ∈ writtenSet A, Nonempty (N ≅ M)) ?_ ?_ ?_ h
  · exact ⟨zeroModule A, writtenZero A, ⟨Iso.refl _⟩⟩
  · rintro P Q e ⟨R, hR, ⟨e'⟩⟩
    exact ⟨R, hR, ⟨e'.trans e⟩⟩
  · rintro P I _ C ⟨Q, hQ, ⟨eQ⟩⟩
    obtain ⟨U, hU, ⟨eU⟩⟩ := exists_written_finite_sum (previousCells C)
      (fun t => writtenShift (writtenRepresentable (C.object t)) _)
    let f := attachmentConeMap C
    let g := eU.hom ≫ f ≫ eQ.inv
    have hcomm : eU.hom ≫ f = g ≫ eQ.hom := by simp [g]
    exact ⟨cone g, writtenCone hU hQ g,
      ⟨(coneIsoOfSquare g f eU eQ hcomm).trans (attachmentConeIso C).symm⟩⟩

theorem writtenObjects : FiniteCellConstructions.WrittenObjects.{u,v,w} := by
  intro k _ A
  refine ⟨writtenModule_injective A, writtenModule_range A, fun _ => rfl, writtenZero A,
    fun h s => writtenShift h s, writtenSum, fun hP hQ f => writtenCone hP hQ f, ?_, ?_⟩
  · intro X
    induction X using Quotient.ind with
    | _ c => exact finiteCell_writtenCode A c
  · intro M hM
    obtain ⟨N, hN, hNM⟩ := exists_written_rep hM
    rw [← writtenModule_range] at hN
    obtain ⟨X, rfl⟩ := hN
    exact ⟨X, hNM⟩

end WrittenHull

theorem canonicalFiniteCells : FiniteCellConstructions.CanonicalFiniteCells.{u,v,w,j} := by
  intro k _ A
  have h (M : RightDGModule A) := DG.CellReindex.finiteCellComparison M
  have hW := writtenObjects A
  refine
    { concrete := h
      zero := (h _).mpr (finiteCellZero A)
      representable := fun a => (h _).mpr (finiteCellRepresentable a)
      shift := fun s hM => (h _).mpr (finiteCellShift s ((h _).mp hM))
      sum := ?_
      cone := fun f hP hQ => (h _).mpr (finiteCellCone f ((h _).mp hP) ((h _).mp hQ))
      finiteCell := fun X => (h _).mpr (hW.finiteCell X)
      represents := fun M hM => hW.represents M ((h _).mp hM) }
  intro I _ F S D hF
  classical
  let _ := Fintype.ofFinite I
  let e : I ≃ FiniteIndex.{v} (Fintype.card I) :=
    (Fintype.equivFin I).trans Equiv.ulift.symm
  apply (h S).mpr
  exact finiteCell_of_iso (strictSumReindex e D).symm
    (finiteCellSum (F ∘ e.symm) (fun s => (h _).mp (hF (e.symm s))))

section LiftedHull

open FiniteCellConstructions (sourcePretr liftedPretr liftedWrittenModule LiftedHullComparison)
open DG.CoefficientLift (liftFunctor gradedEquiv gradedEquiv_apply_down gradedEquiv_comm_d
  gradedEquiv_strict gradedEquiv_comp liftFullyFaithful representableComparison)

private def liftedHomIso (X Y : WrittenObject A) :
    (sourcePretr.{u,v,w,t} A).hom X Y ≅ (liftedPretr.{u,v,w,t} A).hom X Y :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r => (ULift.moduleEquiv.trans
      (gradedEquiv.{u,v,w,t} (writtenModule A X) (writtenModule A Y) r)).toModuleIso)
    (fun r q _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact (gradedEquiv_comm_d.{u,v,w,t} r q f.down).symm)

/-- The morphism complexes of the written hull transport by degreewise conjugation. -/
noncomputable def liftedHullComparison (A : DGCategoryModel.{u,v,w} k) :
    LiftedHullComparison.{u,v,w,t} A where
  homIso := liftedHomIso
  component _ _ r f a i q h x := gradedEquiv_apply_down.{u,v,w,t} r f a i q h (ULift.up x)
  identity X := by
    let M := writtenModule A X
    exact (gradedEquiv_strict.{u,v,w,t} (𝟙 M)).trans
      (congrArg HomComplex.ofStrict ((liftFunctor.{u,v,w,t} A).map_id M))
  composition i j n h f g := gradedEquiv_comp.{u,v,w,t} i j n h f.down g.down
  strictMap f := gradedEquiv_strict.{u,v,w,t} f

theorem liftedHull : FiniteCellConstructions.LiftedHull.{u,v,w,t} := by
  intro k _ A
  let F := liftFunctor.{u,v,w,t} A
  have hW := canonicalFiniteCells.{u,v,w,v} A
  refine ⟨⟨liftedHullComparison A⟩, representableComparison.{u,v,w,t} A, ?_, ?_⟩
  · intro L
    constructor
    · intro hL
      obtain ⟨M, hM, ⟨e⟩⟩ := (DG.CellLift.finiteCellTransport.{u,v,w,t} L).mp hL
      obtain ⟨X, ⟨i⟩⟩ := hW.represents M hM
      exact ⟨X, ⟨(F.mapIso i).trans e⟩⟩
    · rintro ⟨X, ⟨e⟩⟩
      exact (DG.CellLift.finiteCellTransport.{u,v,w,t} L).mpr
        ⟨writtenModule A X, hW.finiteCell X, ⟨e⟩⟩
  · intro X Y
    exact ⟨fun ⟨e⟩ => ⟨F.mapIso e⟩, fun ⟨e⟩ => ⟨(liftFullyFaithful.{u,v,w,t} A).preimageIso e⟩⟩

end LiftedHull

end
end DerivedFormalization.RightDGModule
