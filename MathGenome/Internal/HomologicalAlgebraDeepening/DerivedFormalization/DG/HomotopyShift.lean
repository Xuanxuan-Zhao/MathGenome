import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ShiftCone
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.HomotopyShift
import Mathlib.CategoryTheory.Shift.Induced

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject

universe u v w

namespace DerivedFormalization.RightDGModule

open Specs.DerivedFormalization.DG.Basic (classOf h0Hom)

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}
variable {M N : RightDGModule A}

noncomputable section

set_option maxHeartbeats 800000

instance homotopyPreadditive : Preadditive (K A) :=
  inferInstanceAs (Preadditive (DGCategory.H0 (dgCategory A)))

-- Stating the object map directly avoids unfolding the quotient construction in type checking.
private abbrev homotopyQuotient (A : DGCategory.{u,v,w} k) : RightDGModule A ⥤ K A where
  obj M := M
  map f := homotopyClass f
  map_id := (toHomotopyCategory A).map_id
  map_comp := (toHomotopyCategory A).map_comp

private theorem strict_ext {f g : M ⟶ N}
    (h : ∀ a i (x : (M.complex a).X i), (f.app a).f i x = (g.app a).f i x) : f = g := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro i
  exact ModuleCat.hom_ext (LinearMap.ext (h a i))

theorem toHomotopyCategory_map_surjective {M N : K A} (g : M ⟶ N) :
    ∃ f : RightDGModuleHomModel M N, (homotopyQuotient A).map f = g := by
  change h0Hom (homComplex M N) at g
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ g
  exact ⟨strictMap z, congrArg classOf (strictCycle_strictMap z)⟩

@[simp] private theorem class_zero (M N : RightDGModule A) :
    (homotopyQuotient A).map (0 : M ⟶ N) = 0 := by
  change classOf (strictCycle (0 : M ⟶ N)) = classOf (0 : _)
  congr 1
  apply Subtype.ext
  exact Subtype.ext (funext fun a => CochainComplex.HomComplex.Cochain.ofHom_zero (M.complex a) (N.complex a))

instance toHomotopyCategoryPreservesZeroMorphisms : (toHomotopyCategory A).PreservesZeroMorphisms where
  map_zero := class_zero

instance homotopyHasZeroObject : HasZeroObject (K A) := by
  let Z := (⊤_ (RightDGModule A))
  refine ⟨(homotopyQuotient A).obj Z, (IsZero.iff_id_eq_zero _).2 ?_⟩
  have h : (𝟙 Z : Z ⟶ Z) = 0 := terminalIsTerminal.hom_ext _ _
  rw [← (homotopyQuotient A).map_id, h, class_zero]

/-- The strict signed shift. -/
abbrev strictShift (s : ℤ) : RightDGModule A ⥤ RightDGModule A where
  obj M := shift M s
  map f := shiftMap s f
  map_id _ := strict_ext (fun _ _ _ => rfl)
  map_comp _ _ := strict_ext (fun _ _ _ => rfl)

abbrev homotopyShift (s : ℤ) : K A ⥤ K A where
  obj M := shift M s
  map f := Specs.DerivedFormalization.DG.Basic.h0Map (shiftDGFunctor A s) f
  map_id := (DGFunctor.H0 (shiftDGFunctor A s)).map_id
  map_comp := (DGFunctor.H0 (shiftDGFunctor A s)).map_comp

private instance (s : ℤ) : (homotopyShift (A := A) s).Additive :=
  inferInstanceAs (DGFunctor.H0 (shiftDGFunctor A s)).Additive

@[simp] theorem homotopyShift_map (s : ℤ) (f : M ⟶ N) :
    (homotopyShift (A := A) s).map ((homotopyQuotient A).map f) =
      (homotopyQuotient A).map (shiftMap s f) := by
  change Specs.DerivedFormalization.DG.Basic.h0Map (shiftDGFunctor A s) (classOf (strictCycle f)) = _
  rw [DGFunctor.h0Map_mk]
  exact congrArg classOf (Subtype.ext (shiftDGFunctor_map_strict s f))

private theorem transport_act (M : RightDGModule A) {a b : A.Obj}
    {i i' j n n' : ℤ} (hi : i = i') (hn : n = n')
    (h : i+j = n) (h' : i'+j = n') (x : (M.complex b).X i) (z : (A.hom a b).X j) :
    (eqToHom (congrArg (M.complex a).X hn)) (M.act i j n h x z) =
      M.act i' j n' h' (eqToHom (congrArg (M.complex b).X hi) x) z := by
  subst i' n'
  rfl

private def strictShiftZero : strictShift (A := A) 0 ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M =>
    { hom :=
        { app := fun a => (CochainComplex.shiftFunctorZero' (ModuleCat k) 0 rfl).hom.app (M.complex a)
          comm_act := by
            intro a b i j n h x z
            exact transport_act M (show i+0 = i by omega) (show n+0 = n by omega) _ _ x z }
      inv :=
        { app := fun a => (CochainComplex.shiftFunctorZero' (ModuleCat k) 0 rfl).inv.app (M.complex a)
          comm_act := by
            intro a b i j n h x z
            exact transport_act M (show i = i+0 by omega) (show n = n+0 by omega) _ _ x z }
      hom_inv_id := RightDGModuleModel.hom_ext fun a => Iso.hom_inv_id _
      inv_hom_id := RightDGModuleModel.hom_ext fun a => Iso.inv_hom_id _ })
    (fun f => RightDGModuleModel.hom_ext fun a =>
      (CochainComplex.shiftFunctorZero' (ModuleCat k) 0 rfl).hom.naturality (f.app a))

private def strictShiftAdd (s t : ℤ) :
    strictShift (A := A) (s+t) ≅ strictShift s ⋙ strictShift t :=
  NatIso.ofComponents (fun M =>
    { hom :=
        { app := fun a => (CochainComplex.shiftFunctorAdd' (ModuleCat k) s t _ rfl).hom.app (M.complex a)
          comm_act := by
            intro a b i j n h x z
            exact transport_act M (show i+(s+t) = i+t+s by omega)
              (show n+(s+t) = n+t+s by omega) _ _ x z }
      inv :=
        { app := fun a => (CochainComplex.shiftFunctorAdd' (ModuleCat k) s t _ rfl).inv.app (M.complex a)
          comm_act := by
            intro a b i j n h x z
            exact transport_act M (show i+t+s = i+(s+t) by omega)
              (show n+t+s = n+(s+t) by omega) _ _ x z }
      hom_inv_id := RightDGModuleModel.hom_ext fun a => Iso.hom_inv_id _
      inv_hom_id := RightDGModuleModel.hom_ext fun a => Iso.inv_hom_id _ })
    (fun f => RightDGModuleModel.hom_ext fun a =>
      (CochainComplex.shiftFunctorAdd' (ModuleCat k) s t _ rfl).hom.naturality (f.app a))

private def strictShiftCore : ShiftMkCore (RightDGModule A) ℤ where
  F := strictShift
  zero := strictShiftZero
  add := strictShiftAdd
  assoc_hom_app s t r M := by
    apply RightDGModuleModel.hom_ext
    intro a
    simp only [RightDGModuleModel.comp_app]
    rw [show (eqToHom (by rw [add_assoc]) :
      (strictShift (A := A) ((s+t)+r)).obj M ⟶ (strictShift (s+(t+r))).obj M).app a =
        eqToHom (by simp only [add_assoc]) from eqToHom_map (eval a) _]
    have h := shiftFunctorAdd_assoc_hom_app s t r (M.complex a)
    rw [shiftFunctorAdd'] at h
    change
      (shiftFunctorAdd (ModuleCochain.{u,v} k) (s+t) r).hom.app (M.complex a) ≫
        (CategoryTheory.shiftFunctor (ModuleCochain.{u,v} k) r).map
          ((shiftFunctorAdd (ModuleCochain.{u,v} k) s t).hom.app (M.complex a)) =
        _ ≫ (shiftFunctorAdd (ModuleCochain.{u,v} k) s (t+r)).hom.app (M.complex a) ≫
          (shiftFunctorAdd (ModuleCochain.{u,v} k) t r).hom.app
            ((CategoryTheory.shiftFunctor (ModuleCochain.{u,v} k) s).obj (M.complex a))
    simpa only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
      Category.assoc] using h
  zero_add_hom_app s M := by
    apply RightDGModuleModel.hom_ext
    intro a
    simp only [RightDGModuleModel.comp_app]
    rw [show (eqToHom (by rw [zero_add]) :
      (strictShift (A := A) (0+s)).obj M ⟶ (strictShift s).obj M).app a =
        eqToHom (by simp only [zero_add]) from eqToHom_map (eval a) _]
    exact shiftFunctorAdd_zero_add_hom_app s (M.complex a)
  add_zero_hom_app s M := by
    apply RightDGModuleModel.hom_ext
    intro a
    simp only [RightDGModuleModel.comp_app]
    rw [show (eqToHom (by rw [add_zero]) :
      (strictShift (A := A) (s+0)).obj M ⟶ (strictShift s).obj M).app a =
        eqToHom (by simp only [add_zero]) from eqToHom_map (eval a) _]
    exact shiftFunctorAdd_add_zero_hom_app s (M.complex a)

@[reducible] instance strictHasShift : HasShift (RightDGModule A) ℤ where
  shift := Discrete.functor (strictShift (A := A))
  shiftMonoidal := (hasShiftMk _ _ (strictShiftCore (A := A))).shiftMonoidal

private instance quotientWhiskerFull :
    ((CategoryTheory.Functor.whiskeringLeft (RightDGModule A) (K A) (K A)).obj
      (homotopyQuotient A)).Full where
  map_surjective {F G} τ := by
    let σ : F ⟶ G :=
      { app := fun X => τ.app (X : RightDGModule A)
        naturality := by
          intro X Y g
          obtain ⟨f, rfl⟩ := toHomotopyCategory_map_surjective g
          exact τ.naturality f }
    exact ⟨σ, NatTrans.ext rfl⟩

private instance quotientWhiskerFaithful :
    ((CategoryTheory.Functor.whiskeringLeft (RightDGModule A) (K A) (K A)).obj
      (homotopyQuotient A)).Faithful where
  map_injective h := by
    apply NatTrans.ext
    funext X
    exact congrArg (fun τ => τ.app (X : RightDGModule A)) h

@[reducible] private def quotientShiftIso (s : ℤ) :
    homotopyQuotient A ⋙ homotopyShift (A := A) s ≅
      CategoryTheory.shiftFunctor (RightDGModule A) s ⋙ homotopyQuotient A :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M N f
    change (homotopyShift (A := A) s).map ((homotopyQuotient A).map f) ≫ 𝟙 _ =
      𝟙 _ ≫ (homotopyQuotient A).map (shiftMap s f)
    rw [Category.comp_id, Category.id_comp, homotopyShift_map])

/-- The coherent `ℤ`-action on the homotopy category. -/
@[reducible] instance homotopyHasShift : HasShift (K A) ℤ where
  shift := Discrete.functor (homotopyShift (A := A))
  shiftMonoidal := (HasShift.induced (homotopyQuotient A) ℤ (homotopyShift (A := A))
    (quotientShiftIso (A := A))).shiftMonoidal

instance homotopyShiftAdditive (s : ℤ) : (CategoryTheory.shiftFunctor (K A) s).Additive :=
  inferInstanceAs (homotopyShift (A := A) s).Additive

theorem homotopyShiftFunctor_eq (s : ℤ) :
    CategoryTheory.shiftFunctor (K A) s = homotopyShift (A := A) s := rfl

private instance quotientCommShift : (homotopyQuotient A).CommShift ℤ :=
  CategoryTheory.Functor.CommShift.ofInduced (homotopyQuotient A) ℤ
    (homotopyShift (A := A)) (quotientShiftIso (A := A))

/-- The existing quotient functor commutes coherently with the chosen shifts. -/
instance toHomotopyCategoryCommShift : (toHomotopyCategory A).CommShift ℤ :=
  quotientCommShift

/-- Cancellation of shifts by `s` and then by `-s` on strict modules. -/
def cancelShift (M : RightDGModule A) (s : ℤ) : shift (shift M s) (-s) ≅ M :=
  (shiftFunctorCompIsoId (RightDGModule A) s (-s) (add_neg_cancel s)).app M

/-- Cancellation of shifts by `-s` and then by `s` on strict modules. -/
def cancelShift' (M : RightDGModule A) (s : ℤ) : shift (shift M (-s)) s ≅ M :=
  (shiftFunctorCompIsoId (RightDGModule A) (-s) s (neg_add_cancel s)).app M

/-- Cancellation of shifts by `s` and then by `-s` in the homotopy category. -/
def homotopyCancelShift (M : K A) (s : ℤ) :
    @Iso (K A) _ (shift (shift M s) (-s)) M :=
  (shiftFunctorCompIsoId (K A) s (-s) (add_neg_cancel s)).app M

/-- Cancellation of shifts by `-s` and then by `s` in the homotopy category. -/
def homotopyCancelShift' (M : K A) (s : ℤ) :
    @Iso (K A) _ (shift (shift M (-s)) s) M :=
  (shiftFunctorCompIsoId (K A) (-s) s (neg_add_cancel s)).app M

private theorem map_cancelShift_hom {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ]
    (e : ∀ (n : ℤ) (X : C), F.obj (X⟦n⟧) = (F.obj X)⟦n⟧)
    (eh : ∀ n X, (F.commShiftIso (n : ℤ)).hom.app X = eqToHom (e n X))
    (X : C) (a b : ℤ) (h : a + b = 0) :
    F.map ((shiftFunctorCompIsoId C a b h).hom.app X) =
      eqToHom ((e b (X⟦a⟧)).trans (congrArg (shiftFunctor D b).obj (e a X))) ≫
        (shiftFunctorCompIsoId D a b h).hom.app (F.obj X) := by
  rw [CategoryTheory.Functor.map_shiftFunctorCompIsoId_hom_app, eh, eh, eqToHom_map,
    eqToHom_trans_assoc]

private abbrev quotientCommShiftIso (n : ℤ) :
    CategoryTheory.shiftFunctor (RightDGModule A) n ⋙ homotopyQuotient A ≅
      homotopyQuotient A ⋙ CategoryTheory.shiftFunctor (K A) n :=
  @CategoryTheory.Functor.commShiftIso (RightDGModule A) (K A)
    RightDGModuleModel.category (instCategoryK A) (homotopyQuotient A)
    ℤ _ strictHasShift homotopyHasShift quotientCommShift n

private theorem quotientShiftObjEq (n : ℤ) (X : RightDGModule A) :
    (homotopyQuotient A).obj ((CategoryTheory.shiftFunctor (RightDGModule A) n).obj X) =
      (CategoryTheory.shiftFunctor (K A) n).obj ((homotopyQuotient A).obj X) := rfl

-- Fix the quotient's object map before invoking the generic compatibility formulas.
set_option maxHeartbeats 500000 in
private theorem quotientCommShift_hom (n : ℤ) (X : RightDGModule A) :
    @Eq (@Quiver.Hom (K A) (instCategoryK A).toCategoryStruct.toQuiver
      ((CategoryTheory.shiftFunctor (RightDGModule A) n ⋙ homotopyQuotient A).obj X)
      ((homotopyQuotient A ⋙ CategoryTheory.shiftFunctor (K A) n).obj X))
      ((quotientCommShiftIso (A := A) n).hom.app X)
      (eqToHom (quotientShiftObjEq n X)) := rfl

set_option maxHeartbeats 80000 in
theorem quotient_shiftFunctorCompIsoId_hom (M : RightDGModule A) (n m : ℤ)
    (h : n + m = 0) :
    (homotopyQuotient A).map ((shiftFunctorCompIsoId (RightDGModule A) n m h).hom.app M) =
      (shiftFunctorCompIsoId (K A) n m h).hom.app ((homotopyQuotient A).obj M) := by
  have e := @map_cancelShift_hom (RightDGModule A) (K A)
    RightDGModuleModel.category (instCategoryK A) (strictHasShift (A := A)) (homotopyHasShift (A := A))
    (homotopyQuotient A) (quotientCommShift (A := A)) (@quotientShiftObjEq k _ A)
    (@quotientCommShift_hom k _ A) M n m h
  exact e.trans (Category.id_comp _)

theorem quotient_shiftFunctorCompIsoId_inv (M : RightDGModule A) (n m : ℤ)
    (h : n + m = 0) :
    (homotopyQuotient A).map ((shiftFunctorCompIsoId (RightDGModule A) n m h).inv.app M) =
      (shiftFunctorCompIsoId (K A) n m h).inv.app ((homotopyQuotient A).obj M) := by
  have e : (homotopyQuotient A).mapIso ((shiftFunctorCompIsoId (RightDGModule A) n m h).app M) =
      (shiftFunctorCompIsoId (K A) n m h).app ((homotopyQuotient A).obj M) :=
    Iso.ext (quotient_shiftFunctorCompIsoId_hom M n m h)
  exact congrArg Iso.inv e

/-- Evaluation of a strict shift cancellation gives ordinary cochain cancellation. -/
theorem shiftFunctorCompIsoId_hom_app (M : RightDGModule A) (n m : ℤ)
    (h : n + m = 0) (a : A.Obj) :
    ((shiftFunctorCompIsoId (RightDGModule A) n m h).hom.app M).app a =
      (shiftFunctorCompIsoId (ModuleCochain.{u,v} k) n m h).hom.app (M.complex a) := by
  simp only [shiftFunctorCompIsoId, shiftFunctorAdd', Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, NatTrans.comp_app, eqToIso.inv, eqToHom_app, RightDGModuleModel.comp_app]
  rw [show (eqToHom (congrArg (fun t : ℤ => shift M t) h) :
      shift M (n+m) ⟶ shift M 0).app a =
        eqToHom (congrArg (fun t : ℤ => (shift M t).complex a) h) from eqToHom_map (eval a) _]
  rfl

/-- Evaluation of the inverse strict cancellation gives its ordinary cochain counterpart. -/
theorem shiftFunctorCompIsoId_inv_app (M : RightDGModule A) (n m : ℤ)
    (h : n + m = 0) (a : A.Obj) :
    ((shiftFunctorCompIsoId (RightDGModule A) n m h).inv.app M).app a =
      (shiftFunctorCompIsoId (ModuleCochain.{u,v} k) n m h).inv.app (M.complex a) := by
  simp only [shiftFunctorCompIsoId, shiftFunctorAdd', Iso.trans_hom, Iso.trans_inv,
    Iso.symm_inv, NatTrans.comp_app, eqToIso.hom, eqToHom_app, RightDGModuleModel.comp_app]
  rw [show (eqToHom (congrArg (fun t : ℤ => shift M t) h.symm) :
      shift M 0 ⟶ shift M (n+m)).app a =
        eqToHom (congrArg (fun t : ℤ => (shift M t).complex a) h.symm) from eqToHom_map (eval a) _]
  rfl

private theorem map_heq_of_eq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F = G) {X Y : C} (f : X ⟶ Y) : HEq (F.map f) (G.map f) := by
  subst G
  rfl

/-- Both shift actions are compatible with the right-linear homotopy quotient. -/
theorem homotopyShiftCoherence :
    Specs.DerivedFormalization.DG.HomotopyShift.ShiftCoherence.{u,v,w} := by
  intro k _ A
  refine ⟨instCategoryK A, rfl, homotopyPreadditive (A := A),
    homotopyHasZeroObject (A := A), strictHasShift (A := A), homotopyHasShift (A := A), ?_⟩
  refine ⟨fun _ _ => HEq.rfl, fun _ _ => rfl, fun _ _ => HEq.rfl,
    fun _ _ => rfl, homotopyShiftAdditive (A := A), ?_, ?_⟩
  · intro X n m h a
    exact ⟨heq_of_eq (shiftFunctorCompIsoId_hom_app X n m h a),
      heq_of_eq (shiftFunctorCompIsoId_inv_app X n m h a)⟩
  · refine ⟨toHomotopyCategory A, fun _ => rfl, fun _ => HEq.rfl, ?_,
      toHomotopyCategoryPreservesZeroMorphisms (A := A), ?_, ?_⟩
    · intro X Y g
      exact toHomotopyCategory_map_surjective g
    · intro X Y n f
      have q := map_heq_of_eq (@homotopyShiftFunctor_eq k _ A n)
        ((homotopyQuotient A).map f)
      exact q.trans (heq_of_eq (@homotopyShift_map k _ A X Y n f))
    · intro X n m h
      exact ⟨heq_of_eq (@quotient_shiftFunctorCompIsoId_hom k _ A X n m h),
        heq_of_eq (@quotient_shiftFunctorCompIsoId_inv k _ A X n m h)⟩

end

end DerivedFormalization.RightDGModule
