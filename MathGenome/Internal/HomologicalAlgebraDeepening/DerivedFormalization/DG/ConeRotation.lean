import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ConeMaps
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.ConeRotation

import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.HomotopyShift
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex

universe u v w z

namespace DerivedFormalization.RightDGModule

open Specs.DerivedFormalization.DG.Basic (classOf)
open Specs.DerivedFormalization.DG.HomComplex (HomotopyEquation homotopyCategory)
open Specs.DerivedFormalization.DG.ConeRotation (coneTriangle inverseConeArrow
  quotientShiftObj strictShiftCompObj)

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}
variable {M N : RightDGModule A}

noncomputable section

private def strictNeg (f : M ⟶ N) : M ⟶ N where
  app a := -f.app a
  comm_act := by
    intro a b i j n h x z
    change -(f.app a).f n (M.act i j n h x z) = N.act i j n h (-(f.app b).f i x) z
    rw [f.comm_act, map_neg, LinearMap.neg_apply]

@[simp] private theorem shift_d_one (M : RightDGModule A) (a : A.Obj) (i : ℤ)
    (x : (M.complex a).X (i+1)) :
    ((shift M 1).complex a).d i (i+1) x = -(M.complex a).d (i+1) (i+1+1) x := by
  change ((1 : ℤ).negOnePow • (M.complex a).d (i+1) (i+1+1)) x = _
  simp [Int.negOnePow_one, Units.neg_smul, ModuleCat.hom_neg, LinearMap.neg_apply]

private theorem identityConeContractible (M : RightDGModule A) :
    ∃ H : GradedHom (cone (𝟙 M)) (cone (𝟙 M)) (-1),
      HomotopyEquation (𝟙 (cone (𝟙 M))) (0 : cone (𝟙 M) ⟶ cone (𝟙 M)) H := by
  let H := homotopyOfComponents (M := cone (𝟙 M)) (N := cone (𝟙 M))
    (fun _ _ => (0 : _ →ₗ[k] _).prod (LinearMap.fst _ _ _))
    (by
      intro a b i j n e p z
      change (0, M.act (i+1) j (n+1) (by omega) p.1 z) = (cone (𝟙 M)).act i j n e (0, p.1) z
      rw [cone_act]
      simp only [map_zero, LinearMap.zero_apply])
  refine ⟨H, ?_⟩
  apply homotopyEquationOfSucc
  intro a i p
  change p - (0 : ((cone (𝟙 M)).complex a).X (i+1)) =
    ((cone (𝟙 M)).complex a).d i (i+1) (0,p.1) +
      (0, (((cone (𝟙 M)).complex a).d (i+1) (i+1+1) p).1)
  rw [cone_d (𝟙 M) a i, cone_d (𝟙 M) a (i+1)]
  change p - (0 : ((cone (𝟙 M)).complex a).X (i+1)) =
    (((M.complex a).d i (i+1) 0 + p.1), -(M.complex a).d (i+1) (i+1+1) p.1) +
      (0, (M.complex a).d (i+1) (i+1+1) p.1 + p.2)
  simp only [sub_zero, map_zero, zero_add, Prod.add_def, add_zero]
  exact Prod.ext rfl (by abel)

section Rotation

variable (f : M ⟶ N)

private theorem rotationCone_d (a : A.Obj) (i : ℤ)
    (p : ((cone (coneInclusion f)).complex a).X i) :
    ((cone (coneInclusion f)).complex a).d i (i+1) p =
      (((N.complex a).d i (i+1) p.1.1 + (f.app a).f (i+1) p.1.2 + p.2,
        -(M.complex a).d (i+1) (i+1+1) p.1.2), -(N.complex a).d (i+1) (i+1+1) p.2) := by
  rw [cone_d (coneInclusion f), cone_d f, coneInclusion_f f]
  exact Prod.ext (Prod.ext rfl (add_zero _)) rfl

private def rotationReadout : cone (coneInclusion f) ⟶ shift M 1 :=
  strictOfComponents
    (fun _ _ => -(LinearMap.snd _ _ _ ∘ₗ LinearMap.fst _ _ _))
    (by
      intro a i p
      change ((shift M 1).complex a).d i (i+1) (-p.1.2) =
        -(((cone (coneInclusion f)).complex a).d i (i+1) p).1.2
      rw [shift_d_one, rotationCone_d f, map_neg])
    (by
      intro a b i j n e p z
      change -((cone (coneInclusion f)).act i j n e p z).1.2 =
        M.act (i+1) j (n+1) (by omega) (-p.1.2) z
      rw [cone_act, cone_act, map_neg, LinearMap.neg_apply])

private def rotationSection : shift M 1 ⟶ cone (coneInclusion f) :=
  strictOfComponents
    (fun a i => ((0 : (M.complex a).X (i+1) →ₗ[k] (N.complex a).X i).prod (-LinearMap.id)).prod
      ((f.app a).f (i+1)).hom)
    (by
      intro a i x
      change ((cone (coneInclusion f)).complex a).d i (i+1) ((0,-x), (f.app a).f (i+1) x) =
        ((0, -(((shift M 1).complex a).d i (i+1) x)),
          (f.app a).f (i+1+1) (((shift M 1).complex a).d i (i+1) x))
      rw [shift_d_one, rotationCone_d f]
      simp only [map_zero, map_neg, neg_neg, zero_add, neg_add_cancel, strict_d])
    (by
      intro a b i j n e x z
      change ((0,-(M.act (i+1) j (n+1) (by omega) x z)),
        (f.app a).f (n+1) (M.act (i+1) j (n+1) (by omega) x z)) =
        (cone (coneInclusion f)).act i j n e ((0,-x),(f.app b).f (i+1) x) z
      rw [cone_act, cone_act, f.comm_act]
      simp only [map_zero, map_neg, LinearMap.neg_apply, LinearMap.zero_apply])

private def rotationHomotopy : GradedHom (cone (coneInclusion f)) (cone (coneInclusion f)) (-1) :=
  homotopyOfComponents (fun _ _ => (0 : _ →ₗ[k] _).prod
    (-(LinearMap.fst _ _ _ ∘ₗ LinearMap.fst _ _ _))) (by
    intro a b i j n e p z
    change ((0,0), -((cone (coneInclusion f)).act (i+1) j (n+1) _ p z).1.1) =
      (cone (coneInclusion f)).act i j n e ((0,0),-p.1.1) z
    rw [cone_act (coneInclusion f), cone_act f, cone_act (coneInclusion f), cone_act f]
    simp only [map_zero, map_neg, LinearMap.neg_apply, LinearMap.zero_apply])

private def rotationSquareHomotopy : GradedHom (cone f) (cone (coneInclusion f)) (-1) :=
  homotopyOfComponents (fun _ _ => (0 : _ →ₗ[k] _).prod (-LinearMap.fst _ _ _)) (by
    intro a b i j n e p z
    change ((0,0), -((cone f).act (i+1) j (n+1) _ p z).1) =
      (cone (coneInclusion f)).act i j n e ((0,0),-p.1) z
    rw [cone_act, cone_act, cone_act]
    simp only [map_zero, map_neg, LinearMap.neg_apply, LinearMap.zero_apply])

private theorem rotation_id_left :
    rotationSection f ≫ rotationReadout f = 𝟙 (shift M 1) := by
  apply strict_ext
  intro a i x
  change -(-x) = x
  exact neg_neg _

private theorem rotation_id_right :
    HomotopyEquation (rotationReadout f ≫ rotationSection f)
      (𝟙 (cone (coneInclusion f))) (rotationHomotopy f) := by
  apply homotopyEquationOfSucc
  intro a i p
  change (((0, -(-p.1.2)), (f.app a).f (i+1+1) (-p.1.2)) - p) =
    ((cone (coneInclusion f)).complex a).d i (i+1) ((0,0),-p.1.1) +
      ((0,0), -(((cone (coneInclusion f)).complex a).d (i+1) (i+1+1) p).1.1)
  rw [rotationCone_d f, rotationCone_d f]
  simp only [Prod.sub_def, Prod.add_def,
    map_zero, map_neg, neg_neg, zero_add, add_zero, zero_sub, sub_self]
  apply Prod.ext <;> dsimp only <;> abel

private theorem rotation_comm₂ :
    HomotopyEquation (strictNeg (coneProjection f) ≫ rotationSection f)
      (coneInclusion (coneInclusion f)) (rotationSquareHomotopy f) := by
  apply homotopyEquationOfSucc
  intro a i p
  change (((0, -(-p.2)), (f.app a).f (i+1+1) (-p.2)) - (p,0)) =
    ((cone (coneInclusion f)).complex a).d i (i+1) ((0,0),-p.1) +
      ((0,0), -(((cone f).complex a).d (i+1) (i+1+1) p).1)
  rw [rotationCone_d f, cone_d f]
  simp only [Prod.sub_def, Prod.add_def,
    map_zero, map_neg, neg_neg, zero_add, add_zero, zero_sub, sub_self, sub_zero]
  apply Prod.ext <;> dsimp only <;> abel

private theorem rotation_comm₃ :
    rotationSection f ≫ coneProjection (coneInclusion f) = shiftMap 1 f := by
  apply strict_ext
  intro a i x
  rfl

end Rotation

namespace InverseRotation

variable (f : M ⟶ N) (g : shift (cone f) (-1) ⟶ M)
variable (I : shift (shift (cone f) (-1)) 1 ≅ cone f)
variable (hg : shiftMap 1 g = I.hom ≫ coneProjection f)

include hg in
private theorem inverseArrow_component (a : A.Obj) (i : ℤ)
    (x : ((shift (cone f) (-1)).complex a).X (i+1)) :
    (g.app a).f (i+1) x = ((I.hom.app a).f i x).2 := by
  exact CategoryTheory.congr_fun
    (congrArg (fun h : shift (shift (cone f) (-1)) 1 ⟶ shift M 1 => (h.app a).f i)
      hg) x

include hg in
private theorem inverseCone_diff (a : A.Obj) (i : ℤ)
    (p : ((cone g).complex a).X i) :
    (((cone g).complex a).d i (i+1) p).1 =
      (M.complex a).d i (i+1) p.1 + ((I.hom.app a).f i p.2).2 ∧
    (I.hom.app a).f (i+1) (((cone g).complex a).d i (i+1) p).2 =
      ((cone f).complex a).d i (i+1) ((I.hom.app a).f i p.2) := by
  rw [cone_d, inverseArrow_component f g I hg]
  refine ⟨rfl, ?_⟩
  rw [← shift_d_one]
  exact (strict_d I.hom a i p.2).symm

private theorem innerIso_hom_inv (a : A.Obj) (i : ℤ) (p : ((cone f).complex a).X i) :
    (I.hom.app a).f i ((I.inv.app a).f i p) = p := by
  exact CategoryTheory.congr_fun (congrArg (fun h : cone f ⟶ cone f => (h.app a).f i)
    I.inv_hom_id) p

private theorem innerIso_inv_hom (a : A.Obj) (i : ℤ)
    (p : ((shift (cone f) (-1)).complex a).X (i+1)) :
    (I.inv.app a).f i ((I.hom.app a).f i p) = p := by
  exact CategoryTheory.congr_fun
    (congrArg (fun h : shift (shift (cone f) (-1)) 1 ⟶ shift (shift (cone f) (-1)) 1 =>
      (h.app a).f i) I.hom_inv_id) p

include hg in
private def inverseReadout : cone g ⟶ N :=
  strictOfComponents (fun a i =>
    ((f.app a).f i).hom ∘ₗ LinearMap.fst _ _ _ -
      LinearMap.fst _ _ _ ∘ₗ ((I.hom.app a).f i).hom ∘ₗ LinearMap.snd _ _ _)
    (by
      intro a i p
      let u := (I.hom.app a).f i p.2
      change (N.complex a).d i (i+1) ((f.app a).f i p.1 - u.1) =
        (f.app a).f (i+1) (((cone g).complex a).d i (i+1) p).1 -
          ((I.hom.app a).f (i+1) (((cone g).complex a).d i (i+1) p).2).1
      rw [(inverseCone_diff f g I hg a i p).1, (inverseCone_diff f g I hg a i p).2, cone_d, map_sub, strict_d, map_add]
      dsimp only [u]
      abel)
    (by
      intro a b i j n e p z
      change (f.app a).f n ((cone g).act i j n e p z).1 -
        ((I.hom.app a).f n ((cone g).act i j n e p z).2).1 =
        N.act i j n e ((f.app b).f i p.1 - ((I.hom.app b).f i p.2).1) z
      rw [cone_act, f.comm_act]
      have h := I.hom.comm_act i j n e p.2 z
      change (N.act i j n e ((f.app b).f i p.1)) z -
        ((I.hom.app a).f n
          ((shift (shift (cone f) (-1)) 1).act i j n e p.2 z)).1 = _
      rw [h, cone_act, map_sub, LinearMap.sub_apply])

private theorem innerIso_injective (a : A.Obj) (i : ℤ) :
    Function.Injective (fun p : ((shift (cone f) (-1)).complex a).X (i+1) =>
      (I.hom.app a).f i p) := by
  intro x y e
  exact (innerIso_inv_hom f I a i x).symm.trans
    ((congrArg (fun z => (I.inv.app a).f i z) e).trans (innerIso_inv_hom f I a i y))

include hg in
private def inverseSection : N ⟶ cone g :=
  strictOfComponents
    (fun a i => (0 : _ →ₗ[k] _).prod (((I.inv.app a).f i).hom ∘ₗ
      LinearMap.inl _ _ _ ∘ₗ (-LinearMap.id)))
    (by
      intro a i y
      let p : ((cone g).complex a).X i :=
        (0, (I.inv.app a).f i (-y,0))
      change ((cone g).complex a).d i (i+1) p =
        (0, (I.inv.app a).f (i+1) (-(N.complex a).d i (i+1) y, 0))
      apply Prod.ext
      · rw [(inverseCone_diff f g I hg a i p).1]
        dsimp only [p]
        rw [innerIso_hom_inv, map_zero, add_zero]
      · apply innerIso_injective f I a (i+1)
        change (I.hom.app a).f (i+1) (((cone g).complex a).d i (i+1) p).2 =
          (I.hom.app a).f (i+1) ((I.inv.app a).f (i+1) (-(N.complex a).d i (i+1) y, 0))
        rw [(inverseCone_diff f g I hg a i p).2, innerIso_hom_inv]
        dsimp only [p]
        rw [innerIso_hom_inv, cone_d]
        simp only [map_zero, map_neg, add_zero, neg_zero])
    (by
      intro a b i j n e x z
      change (0, (I.inv.app a).f n (-(N.act i j n e x z),0)) =
        (cone g).act i j n e (0, (I.inv.app b).f i (-x,0)) z
      rw [cone_act]
      apply Prod.ext
      · change 0 = M.act i j n e 0 z
        simp only [map_zero, LinearMap.zero_apply]
      · change (I.inv.app a).f n (-(N.act i j n e x z),0) =
          (shift (shift (cone f) (-1)) 1).act i j n e ((I.inv.app b).f i (-x,0)) z
        rw [← I.inv.comm_act, cone_act]
        simp only [map_zero, LinearMap.zero_apply, map_neg, LinearMap.neg_apply])

private def inverseHomotopy :
    GradedHom (cone g) (cone g) (-1) :=
  homotopyOfComponents
    (fun a i => (0 : _ →ₗ[k] _).prod
      (((I.inv.app a).f i).hom ∘ₗ LinearMap.inr _ _ _ ∘ₗ
        (-(LinearMap.fst _ _ _))))
    (by
      intro a b i j n e p z
      change (0, (I.inv.app a).f n (0, -((cone g).act (i+1) j (n+1) _ p z).1)) =
        (cone g).act i j n e (0, (I.inv.app b).f i (0,-p.1)) z
      rw [cone_act g, cone_act g]
      apply Prod.ext
      · change 0 = M.act i j n e 0 z
        simp only [map_zero, LinearMap.zero_apply]
      · change (I.inv.app a).f n (0,-(M.act (i+1) j (n+1) _ p.1 z)) =
          (shift (shift (cone f) (-1)) 1).act i j n e ((I.inv.app b).f i (0,-p.1)) z
        rw [← I.inv.comm_act, cone_act]
        simp only [map_zero, map_neg, LinearMap.zero_apply, LinearMap.neg_apply])

private theorem inverse_id_left : inverseSection f g I hg ≫ inverseReadout f g I hg = 𝟙 N := by
  apply strict_ext
  intro a i y
  change (f.app a).f i 0 - ((I.hom.app a).f i ((I.inv.app a).f i (-y,0))).1 = y
  rw [innerIso_hom_inv, map_zero]
  exact zero_sub (-y) |>.trans (neg_neg y)

private theorem inverse_id_right :
    HomotopyEquation (inverseReadout f g I hg ≫ inverseSection f g I hg)
      (𝟙 (cone g)) (inverseHomotopy f g I) := by
  apply homotopyEquationOfSucc
  intro a i p
  let T : ((shift (cone f) (-1)).complex a).X (i+1+1) ⟶ ((cone f).complex a).X (i+1) :=
    (I.hom.app a).f (i+1)
  let S : ((cone f).complex a).X (i+1) ⟶ ((shift (cone f) (-1)).complex a).X (i+1+1) :=
    (I.inv.app a).f (i+1)
  let F := ((f.app a).f (i+1))
  let p₀ : ((cone g).complex a).X i :=
    (0, (I.inv.app a).f i (0,-p.1))
  let dp := ((cone g).complex a).d (i+1) (i+1+1) p
  let d₀ := ((cone g).complex a).d i (i+1) p₀
  let q : ((cone g).complex a).X (i+1) := (0, S (-(F p.1 - (T p.2).1),0))
  let h : ((cone g).complex a).X (i+1) := (0, S (0, -dp.1))
  change q - p = d₀ + h
  apply Prod.ext
  · change 0 - p.1 = d₀.1 + 0
    rw [zero_sub]
    rw [(inverseCone_diff f g I hg a i p₀).1]
    dsimp only [p₀]
    rw [innerIso_hom_inv, map_zero, zero_add, add_zero]
  · apply innerIso_injective f I a (i+1)
    change T (S (-(F p.1 - (T p.2).1),0) - p.2) = T (d₀.2 + S (0,-dp.1))
    rw [map_sub, map_add]
    dsimp only [T, S, F, d₀, dp]
    rw [innerIso_hom_inv, innerIso_hom_inv]
    rw [(inverseCone_diff f g I hg a i p₀).2, (inverseCone_diff f g I hg a (i+1) p).1]
    dsimp only [p₀]
    rw [innerIso_hom_inv, cone_d]
    simp only [Prod.add_def, Prod.sub_def, map_zero, map_neg, zero_add, zero_sub, neg_neg]
    apply Prod.ext <;> dsimp only <;> abel

private theorem inverse_inclusion : coneInclusion g ≫ inverseReadout f g I hg = f := by
  apply strict_ext
  intro a i x
  change (f.app a).f i x - ((I.hom.app a).f i 0).1 = (f.app a).f i x
  rw [map_zero]
  exact sub_zero _

private theorem inverse_projection :
    inverseSection f g I hg ≫ strictNeg (coneProjection (g)) =
      coneInclusion f ≫ I.inv := by
  apply strict_ext
  intro a i y
  change -(I.inv.app a).f i (-y,0) = (I.inv.app a).f i (y,0)
  rw [show ((-y, 0) : ((cone f).complex a).X i) = -(y,0) from by
    change (-y,0) = (-y,-(0 : (M.complex a).X (i+1)))
    rw [neg_zero], map_neg, neg_neg]

end InverseRotation

section Transport

open CategoryTheory.Category

private theorem squareOfHEq {C : Type*} [Category C] {X Y X' Y' : C}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (hx : X = X') (hy : Y = Y') (h : HEq f g) :
    f ≫ eqToHom hy = eqToHom hx ≫ g := by
  cases hx
  cases hy
  simpa only [eqToHom_refl, comp_id, id_comp] using eq_of_heq h

private theorem shiftMapSquare [HasShift (RightDGModule A) ℤ]
    (hS : ∀ (X : RightDGModule A) (n : ℤ),
      (shiftFunctor (RightDGModule A) n).obj X = shift X n)
    (hmap : ∀ {X Y : RightDGModule A} (n : ℤ) (a : X ⟶ Y),
      HEq ((shiftFunctor (RightDGModule A) n).map a) (shiftMap n a))
    (n : ℤ) (f : M ⟶ N) :
    (shiftFunctor (RightDGModule A) n).map f ≫ eqToHom (hS N n) =
      eqToHom (hS M n) ≫ shiftMap n f :=
  squareOfHEq (hS M n) (hS N n) (hmap n f)

private def strictCancellation [HasShift (RightDGModule A) ℤ]
    (hS : ∀ (X : RightDGModule A) (n : ℤ),
      (shiftFunctor (RightDGModule A) n).obj X = shift X n)
    (n m : ℤ) (h : n + m = 0) (X : RightDGModule A) : shift (shift X n) m ≅ X :=
  (eqToIso (strictShiftCompObj hS X n m).symm).trans
    ((shiftFunctorCompIsoId (RightDGModule A) n m h).app X)

private theorem map_inverse_arrow {C : Type*} [Category C] [HasShift C ℤ]
    {X Z : C} (p : Z ⟶ (shiftFunctor C (1 : ℤ)).obj X) :
    (shiftFunctor C (1 : ℤ)).map
        ((shiftFunctor C (-1 : ℤ)).map p ≫
          (shiftFunctorCompIsoId C 1 (-1) (add_neg_cancel (1 : ℤ))).hom.app X) =
      (shiftFunctorCompIsoId C (-1) 1 (neg_add_cancel (1 : ℤ))).hom.app Z ≫ p := by
  rw [CategoryTheory.Functor.map_comp, shift_shiftFunctorCompIsoId_add_neg_cancel_hom_app]
  exact (shiftFunctorCompIsoId C (-1) 1 (neg_add_cancel (1 : ℤ))).hom.naturality p

private theorem strict_inverseArrow_shift [HasShift (RightDGModule A) ℤ]
    (hS : ∀ (X : RightDGModule A) (n : ℤ),
      (shiftFunctor (RightDGModule A) n).obj X = shift X n)
    (hmap : ∀ {X Y : RightDGModule A} (n : ℤ) (a : X ⟶ Y),
      HEq ((shiftFunctor (RightDGModule A) n).map a) (shiftMap n a))
    (f : M ⟶ N) :
    shiftMap 1 (inverseConeArrow hS f) =
      (strictCancellation hS (-1) 1 (by decide) (cone f)).hom ≫ coneProjection f := by
  let U := shiftFunctor (RightDGModule A) (1 : ℤ)
  let V := shiftFunctor (RightDGModule A) (-1 : ℤ)
  let p := coneProjection f
  let unit := (shiftFunctorCompIsoId (RightDGModule A) 1 (-1) (by decide)).hom.app M
  let counit := (shiftFunctorCompIsoId (RightDGModule A) (-1) 1 (by decide)).hom.app (cone f)
  let p' : cone f ⟶ U.obj M := p ≫ eqToHom (hS M 1).symm
  have hp : V.map p' =
      eqToHom (hS (cone f) (-1)) ≫ shiftMap (-1) p ≫
        eqToHom (strictShiftCompObj hS M 1 (-1)).symm := by
    have t := shiftMapSquare hS hmap (-1) p
    change V.map p ≫ eqToHom (hS (shift M 1) (-1)) =
      eqToHom (hS (cone f) (-1)) ≫ shiftMap (-1) p at t
    have h := (comp_eqToHom_iff (hS (shift M 1) (-1)) _ _).mp t
    change V.map (p ≫ eqToHom (hS M 1).symm) = _
    simp only [CategoryTheory.Functor.map_comp, h, eqToHom_map, assoc, eqToHom_trans]
  have hg : eqToHom (hS (cone f) (-1)).symm ≫ (V.map p' ≫ unit) =
      inverseConeArrow hS f := by
    change _ = (shiftMap (-1) p ≫ eqToHom (strictShiftCompObj hS M 1 (-1)).symm) ≫ unit
    simp only [hp, assoc, eqToHom_trans_assoc, eqToHom_refl, id_comp]
  have t := shiftMapSquare hS hmap 1 (inverseConeArrow hS f)
  change U.map (inverseConeArrow hS f) ≫ eqToHom (hS M 1) =
    eqToHom (hS (shift (cone f) (-1)) 1) ≫ shiftMap 1 (inverseConeArrow hS f) at t
  refine ((eqToHom_comp_iff _ _ _).mp t.symm).trans ?_
  rw [← hg]
  change eqToHom (hS (shift (cone f) (-1)) 1).symm ≫
    U.map (eqToHom (hS (cone f) (-1)).symm ≫ (V.map p' ≫ unit)) ≫
      eqToHom (hS M 1) = _
  have h := map_inverse_arrow p'
  change U.map (V.map p' ≫ unit) = counit ≫ p' at h
  rw [CategoryTheory.Functor.map_comp, h]
  change _ = (eqToHom (strictShiftCompObj hS (cone f) (-1) 1).symm ≫ counit) ≫ p
  simp only [eqToHom_map, p', assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, comp_id]

end Transport

section Quotient

open CategoryTheory.Category

variable [Category.{max v w} (homotopyCategory A)] [Preadditive (homotopyCategory A)]
variable (Q : RightDGModule A ⥤ homotopyCategory A)
variable (hclass : ∀ {X Y : RightDGModule A} (f : X ⟶ Y), HEq (Q.map f) (homotopyClass f))

include hclass in
omit [Preadditive (homotopyCategory A)] in
private theorem quotient_map_homotopy {f g : M ⟶ N} (h : GradedHom M N (-1))
    (H : HomotopyEquation f g h) : Q.map f = Q.map g :=
  eq_of_heq ((hclass f).trans
    ((heq_of_eq ((homotopyCriterion f g).mpr ⟨h, H⟩)).trans (hclass g).symm))

private theorem negHEq {B D : Type z} (b : AddCommGroup B) (d : AddCommGroup D)
    {x : B} {y : D} (hg : HEq b d) (hx : HEq x y) :
    HEq (@Neg.neg B (by letI := b; infer_instance) x)
      (@Neg.neg D (by letI := d; infer_instance) y) := by
  cases type_eq_of_heq hx
  cases eq_of_heq hg
  cases eq_of_heq hx
  rfl

omit [Category.{max v w} (homotopyCategory A)] [Preadditive (homotopyCategory A)] in
private theorem homotopyClass_neg (f : M ⟶ N) :
    homotopyClass (strictNeg f) = -homotopyClass f := by
  change classOf (strictCycle (strictNeg f)) = -classOf (strictCycle f)
  rw [← Submodule.Quotient.mk_neg]
  congr 1
  apply Subtype.ext
  apply GradedHom.ext
  intro a i j e
  obtain rfl : i = j := by omega
  rfl

include hclass in
private theorem quotient_map_neg
    (hobj : ∀ X, Q.obj X = X)
    (hgroup : ∀ X Y : homotopyCategory A, HEq (Preadditive.homGroup X Y)
      (inferInstance : AddCommGroup (Specs.DerivedFormalization.DG.Basic.h0Hom (homComplex X Y))))
    (f : M ⟶ N) : Q.map (strictNeg f) = -Q.map f := by
  let hcarrier (X Y : homotopyCategory A) := (inferInstance :
    AddCommGroup (Specs.DerivedFormalization.DG.Basic.h0Hom (homComplex X Y)))
  have hxy : HEq (hcarrier (Q.obj M) (Q.obj N)) (hcarrier M N) := by
    have eX := hobj M
    have eY := hobj N
    generalize Q.obj M = X at eX ⊢
    generalize Q.obj N = Y at eY ⊢
    subst X Y
    rfl
  have hg := (hgroup (Q.obj M) (Q.obj N)).trans hxy
  exact eq_of_heq ((hclass (strictNeg f)).trans
    ((heq_of_eq (homotopyClass_neg f)).trans (negHEq _ _ hg (hclass f)).symm))

private def quotientHomotopyIso {r : N ⟶ M} {s : M ⟶ N}
    (L : s ≫ r = 𝟙 M) (R : Q.map (r ≫ s) = Q.map (𝟙 N)) :
    Q.obj M ≅ Q.obj N where
  hom := Q.map s
  inv := Q.map r
  hom_inv_id := by rw [← Q.map_comp, L, Q.map_id]
  inv_hom_id := by rw [← Q.map_comp, R, Q.map_id]

variable [HasShift (homotopyCategory A) ℤ]
variable (hQT : ∀ (X : RightDGModule A) (n : ℤ),
  (shiftFunctor (homotopyCategory A) n).obj (Q.obj X) = Q.obj (shift X n))
variable (hQmap : ∀ {X Y : RightDGModule A} (n : ℤ) (a : X ⟶ Y),
  HEq ((shiftFunctor (homotopyCategory A) n).map (Q.map a)) (Q.map (shiftMap n a)))

include hQmap in
omit [Preadditive (homotopyCategory A)] in
private theorem quotientShiftSquare (n : ℤ) (f : M ⟶ N) :
    (shiftFunctor (homotopyCategory A) n).map (Q.map f) ≫ eqToHom (hQT N n) =
      eqToHom (hQT M n) ≫ Q.map (shiftMap n f) :=
  squareOfHEq (hQT M n) (hQT N n) (hQmap n f)

include hclass hQmap in
private theorem forwardRotation
    (hneg : ∀ {X Y : RightDGModule A} (a : X ⟶ Y), Q.map (strictNeg a) = -Q.map a)
    (f : M ⟶ N) :
    ∃ e : (coneTriangle Q hQT f).rotate ≅ coneTriangle Q hQT (coneInclusion f),
      e.hom.hom₁ = 𝟙 _ ∧ e.hom.hom₂ = 𝟙 _ ∧
      e.hom.hom₃ = eqToHom (hQT M 1) ≫ Q.map (rotationSection f) ∧
      e.inv.hom₃ = Q.map (rotationReadout f) ≫ eqToHom (hQT M 1).symm := by
  let e := quotientHomotopyIso Q (rotation_id_left f)
    (quotient_map_homotopy Q hclass (rotationHomotopy f) (rotation_id_right f))
  let i := (eqToIso (hQT M 1)).trans e
  have comm₂ : (-(Q.map (coneProjection f)) ≫ eqToHom (hQT M 1).symm) ≫ i.hom =
      Q.map (coneInclusion (coneInclusion f)) := by
    have hs : (-(Q.map (coneProjection f))) ≫ Q.map (rotationSection f) =
        Q.map (coneInclusion (coneInclusion f)) := by
      rw [← hneg, ← Q.map_comp]
      exact quotient_map_homotopy Q hclass (rotationSquareHomotopy f) (rotation_comm₂ f)
    rw [← Preadditive.neg_comp]
    simpa only [i, e, Iso.trans_hom, eqToIso.hom, quotientHomotopyIso, assoc,
      eqToHom_trans_assoc, eqToHom_refl, id_comp] using hs
  have comm₃ : -((shiftFunctor (homotopyCategory A) (1 : ℤ)).map (Q.map f)) =
      i.hom ≫ (-(Q.map (coneProjection (coneInclusion f))) ≫ eqToHom (hQT N 1).symm) := by
    rw [Preadditive.comp_neg]
    apply congrArg Neg.neg
    have t := (comp_eqToHom_iff (hQT N 1) _ _).mp (quotientShiftSquare Q hQT hQmap 1 f)
    have hs : Q.map (rotationSection f) ≫ Q.map (coneProjection (coneInclusion f)) =
        Q.map (shiftMap 1 f) := by
      rw [← Q.map_comp, rotation_comm₃]
    change _ = (eqToHom (hQT M 1) ≫ Q.map (rotationSection f)) ≫
      Q.map (coneProjection (coneInclusion f)) ≫ eqToHom (hQT N 1).symm
    rw [t, assoc, assoc, ← assoc (Q.map (rotationSection f)), hs]
  let comparison := Triangle.isoMk (coneTriangle Q hQT f).rotate (coneTriangle Q hQT (coneInclusion f))
    (Iso.refl (Q.obj N)) (Iso.refl (Q.obj (cone f))) i
    (show Q.map (coneInclusion f) ≫ 𝟙 _ = 𝟙 _ ≫ Q.map (coneInclusion f) by
      rw [comp_id, id_comp])
    (by
      change (-(Q.map (coneProjection f) ≫ eqToHom (hQT M 1).symm)) ≫ i.hom =
        𝟙 _ ≫ Q.map (coneInclusion (coneInclusion f))
      rw [id_comp]
      exact comm₂)
    (by
      change (-((shiftFunctor (homotopyCategory A) (1 : ℤ)).map (Q.map f))) ≫
        (shiftFunctor (homotopyCategory A) (1 : ℤ)).map (𝟙 (Q.obj N)) =
        i.hom ≫ (-(Q.map (coneProjection (coneInclusion f))) ≫ eqToHom (hQT N 1).symm)
      rw [CategoryTheory.Functor.map_id, comp_id]
      exact comm₃)
  exact ⟨comparison, rfl, rfl, rfl, rfl⟩

section Inverse

variable [HasShift (RightDGModule A) ℤ]
variable (hS : ∀ (X : RightDGModule A) (n : ℤ),
  (shiftFunctor (RightDGModule A) n).obj X = shift X n)
variable (hmap : ∀ {X Y : RightDGModule A} (n : ℤ) (a : X ⟶ Y),
  HEq ((shiftFunctor (RightDGModule A) n).map a) (shiftMap n a))
variable (hcancel : ∀ (X : RightDGModule A) (n m : ℤ) (h : n + m = 0),
  HEq (Q.map ((shiftFunctorCompIsoId (RightDGModule A) n m h).hom.app X))
    ((shiftFunctorCompIsoId (homotopyCategory A) n m h).hom.app (Q.obj X)) ∧
  HEq (Q.map ((shiftFunctorCompIsoId (RightDGModule A) n m h).inv.app X))
    ((shiftFunctorCompIsoId (homotopyCategory A) n m h).inv.app (Q.obj X)))

local notation "K₀" => homotopyCategory A
local notation "D₀" => RightDGModule A

include hcancel in
omit [Preadditive (homotopyCategory A)] in
private theorem quotient_cancel_hom (X : RightDGModule A) :
    Q.map (strictCancellation hS 1 (-1) (by decide) X).hom =
      eqToHom (hQT (shift X 1) (-1)).symm ≫
        (shiftFunctor K₀ (-1 : ℤ)).map (eqToHom (hQT X 1).symm) ≫
        (shiftFunctorCompIsoId K₀ 1 (-1) (by decide)).hom.app (Q.obj X) := by
  apply eq_of_heq
  have h := (hcancel X 1 (-1) (by decide)).1
  change Q.map (eqToHom (strictShiftCompObj hS X 1 (-1)).symm ≫
    (shiftFunctorCompIsoId D₀ 1 (-1) (by decide)).hom.app X) ≍ _
  simpa only [Q.map_comp, eqToHom_map, eqToHom_comp_heq_iff, heq_eqToHom_comp_iff, assoc]
    using h

include hcancel in
omit [Preadditive (homotopyCategory A)] in
private theorem quotient_cancel_inv (X : RightDGModule A) :
    Q.map (strictCancellation hS (-1) 1 (by decide) X).inv =
      (shiftFunctorCompIsoId K₀ (-1) 1 (by decide)).inv.app (Q.obj X) ≫
        (shiftFunctor K₀ (1 : ℤ)).map (eqToHom (hQT X (-1))) ≫
        eqToHom (hQT (shift X (-1)) 1) := by
  apply eq_of_heq
  have h := (hcancel X (-1) 1 (by decide)).2
  change Q.map ((shiftFunctorCompIsoId D₀ (-1) 1 (by decide)).inv.app X ≫
    eqToHom (strictShiftCompObj hS X (-1) 1)) ≍ _
  simpa only [Q.map_comp, eqToHom_map, eqToHom_trans, comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
    using h

variable [hAdd : ∀ n : ℤ, CategoryTheory.Functor.Additive (shiftFunctor (homotopyCategory A) n)]

include hQmap hcancel in
private theorem inverseRotation_first (f : M ⟶ N) :
    (coneTriangle Q hQT f).invRotate.mor₁ =
      eqToHom (hQT (cone f) (-1)) ≫ Q.map (inverseConeArrow hS f) := by
  let V := shiftFunctor K₀ (-1 : ℤ)
  let c := (shiftFunctorCompIsoId K₀ 1 (-1) (by decide)).hom.app (Q.obj M)
  change -(V.map (-(Q.map (coneProjection f) ≫ eqToHom (hQT M 1).symm)) ≫ c) = _
  rw [CategoryTheory.Functor.map_neg, Preadditive.neg_comp, neg_neg, V.map_comp]
  have h := (comp_eqToHom_iff (hQT (shift M 1) (-1)) _ _).mp
    (quotientShiftSquare Q hQT hQmap (-1) (coneProjection f))
  change V.map (Q.map (coneProjection f)) = _ at h
  rw [h]
  change _ = eqToHom (hQT (cone f) (-1)) ≫
    Q.map (shiftMap (-1) (coneProjection f) ≫ (strictCancellation hS 1 (-1) (by decide) M).hom)
  rw [Q.map_comp, quotient_cancel_hom Q hQT hS hcancel]
  simp only [V, c, assoc]

include hclass hmap hQmap hcancel in
private theorem inverseRotation
    (hneg : ∀ {X Y : RightDGModule A} (a : X ⟶ Y), Q.map (strictNeg a) = -Q.map a)
    (f : M ⟶ N) :
    ∃ e : (coneTriangle Q hQT f).invRotate ≅ coneTriangle Q hQT (inverseConeArrow hS f),
      e.hom.hom₁ = eqToHom (hQT (cone f) (-1)) ∧ e.hom.hom₂ = 𝟙 _ := by
  let g := inverseConeArrow hS f
  let I := strictCancellation hS (-1) 1 (by decide) (cone f)
  have hg : shiftMap 1 g = I.hom ≫ coneProjection f := strict_inverseArrow_shift hS hmap f
  let s := InverseRotation.inverseSection f g I hg
  let r := InverseRotation.inverseReadout f g I hg
  let e := quotientHomotopyIso Q (InverseRotation.inverse_id_left f g I hg)
    (quotient_map_homotopy Q hclass (InverseRotation.inverseHomotopy f g I)
      (InverseRotation.inverse_id_right f g I hg))
  let i := eqToIso (hQT (cone f) (-1))
  have comm₁ : (coneTriangle Q hQT f).invRotate.mor₁ ≫ (𝟙 (Q.obj M)) = i.hom ≫ Q.map g := by
    exact (comp_id _).trans (inverseRotation_first Q hQT hQmap hS hcancel f)
  have comm₂ : Q.map f ≫ Q.map s = (𝟙 (Q.obj M)) ≫ Q.map (coneInclusion g) := by
    have h₁ : Q.map (coneInclusion g) ≫ Q.map r = Q.map f := by
      rw [← Q.map_comp]
      exact congrArg (fun t => Q.map t) (InverseRotation.inverse_inclusion f g I hg)
    have h₂ : Q.map r ≫ Q.map s = 𝟙 (Q.obj (cone g)) := e.inv_hom_id
    rw [← h₁, assoc, h₂, comp_id, id_comp]
  have comm₃ : (coneTriangle Q hQT f).invRotate.mor₃ ≫
      (shiftFunctor K₀ (1 : ℤ)).map i.hom = Q.map s ≫ (coneTriangle Q hQT g).mor₃ := by
    let c := (shiftFunctorCompIsoId K₀ (-1) 1 (by decide)).inv.app (Q.obj (cone f))
    let U := shiftFunctor K₀ (1 : ℤ)
    let he := hQT (shift (cone f) (-1)) 1
    have h₁ : (c ≫ U.map i.hom) ≫ eqToHom he = Q.map I.inv := by
      rw [assoc]
      exact (quotient_cancel_inv Q hQT hS hcancel (cone f)).symm
    have h₂ := (comp_eqToHom_iff he _ _).mp h₁
    have h₃ : Q.map (coneInclusion f) ≫ Q.map I.inv =
        Q.map s ≫ Q.map (strictNeg (coneProjection g)) := by
      rw [← Q.map_comp, ← Q.map_comp]
      exact congrArg (fun a => Q.map a) (InverseRotation.inverse_projection f g I hg).symm
    change (Q.map (coneInclusion f) ≫ c) ≫ U.map i.hom =
      Q.map s ≫ (-(Q.map (coneProjection g) ≫ eqToHom he.symm))
    rw [assoc, h₂, ← Preadditive.neg_comp, ← hneg, ← assoc, h₃, assoc]
  let comparison := Triangle.isoMk (coneTriangle Q hQT f).invRotate
    (coneTriangle Q hQT g) i (Iso.refl (Q.obj M)) e comm₁ comm₂ comm₃
  exact ⟨comparison, rfl, rfl⟩

end Inverse

end Quotient

/-- The signed cone triangles rotate on the fixed right-linear homotopy category,
given its coherent shift and quotient structures. -/
theorem coneRotation_conditional
    (coherence : Specs.DerivedFormalization.DG.HomotopyShift.ShiftCoherence.{u,v,w}) :
    Specs.DerivedFormalization.DG.ConeRotation.Rotations.{u,v,w} := by
  intro k hk A
  let _ := hk
  obtain ⟨C, hC, P, Z, S, T, hP, hS, hmap, hT, hAdd, hStrictCancel,
    Q, hQ, hClass, hSurj, hZero, hQmap, hCancel⟩ := coherence A
  let _ := C
  let _ := P
  let _ := S
  let _ := T
  let _ := hAdd
  let _ := hZero
  let hQT := quotientShiftObj Q hQ hT
  have hNeg {X Y : RightDGModule A} (a : X ⟶ Y) : Q.map (strictNeg a) = -Q.map a :=
    quotient_map_neg Q hClass hQ hP a
  refine ⟨C, hC, P, Z, S, T, hP, hS, hT, hmap, hAdd, hStrictCancel,
    Q, hQ, hClass, hSurj, hZero, hQmap, hCancel, ?_, ?_, ?_⟩
  · intro M N f
    exact ⟨rotationSection f, rotationReadout f, rotationHomotopy f, rotation_id_left f,
      rotation_id_right f, forwardRotation Q hClass hQT hQmap hNeg f⟩
  · intro M N f
    exact inverseRotation Q hClass hQT hQmap hS hmap hCancel hNeg f
  · intro M
    obtain ⟨H, hH⟩ := identityConeContractible M
    refine ⟨H, hH, (IsZero.iff_id_eq_zero _).mpr ?_⟩
    have e := quotient_map_homotopy Q hClass H hH
    rw [Q.map_id, Q.map_zero] at e
    exact e

end

end DerivedFormalization.RightDGModule

universe v8_closure_8bb1bd682ee68829_u0 v8_closure_8bb1bd682ee68829_u1 v8_closure_8bb1bd682ee68829_u2
theorem _root_.«DerivedFormalization».«RightDGModule».«coneRotation» : _root_.«Specs».«DerivedFormalization».«DG».«ConeRotation».«Rotations».{v8_closure_8bb1bd682ee68829_u0, v8_closure_8bb1bd682ee68829_u1, v8_closure_8bb1bd682ee68829_u2} :=
  @_root_.«DerivedFormalization».«RightDGModule».«coneRotation_conditional».{v8_closure_8bb1bd682ee68829_u0, v8_closure_8bb1bd682ee68829_u1, v8_closure_8bb1bd682ee68829_u2} (@_root_.«DerivedFormalization».«RightDGModule».«homotopyShiftCoherence».{v8_closure_8bb1bd682ee68829_u0, v8_closure_8bb1bd682ee68829_u1, v8_closure_8bb1bd682ee68829_u2})
