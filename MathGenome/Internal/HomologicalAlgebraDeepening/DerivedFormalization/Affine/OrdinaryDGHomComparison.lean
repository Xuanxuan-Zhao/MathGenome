import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.OrdinaryDGHomComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.DerivedHom
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedHomModels
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurAlgebras
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.PerfectHomBaseChange

/-! Ordinary and dg Hom comparisons at the common coefficient bound. -/

namespace DerivedFormalization.Affine.OrdinaryDGHomComparison

open CategoryTheory Opposite CochainComplex.HomComplex
open scoped TensorProduct
open Specs.DerivedFormalization.Affine.OrdinaryDGHomComparison
open Specs.DerivedFormalization.Cochains (compValue derivedValue homotopyValue qValue qhValue
  quotientValue)
open Specs.DerivedFormalization.CochainModels (internalHomValue internalHomMapValue
  isKProjectiveValue)
open Specs.DerivedFormalization.DG.HomComplex (gradedHom component homotopyClass)
open Specs.DerivedFormalization.Affine.Tensor (act)
open Specs.DerivedFormalization.Affine.DerivedHom (HomActions HomActionLaws)

noncomputable section

universe u v t
set_option autoImplicit false
set_option linter.checkUnivs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] [CharZero k]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

local instance : CommRing (transported.{u,v,t} k R).toCommDGAlgebra.DegreeZero :=
  CommDGAlgebra.instCommRingDegreeZero _
local instance : Algebra k (transported.{u,v,t} k R).toCommDGAlgebra.DegreeZero :=
  CommDGAlgebra.instAlgebraDegreeZero _

private theorem stalk_zero (j : ℤ) (hj : j ≠ 0) (z : (transported.{u,v,t} k R).complex.X j) :
    z = 0 := by
  apply ULift.ext
  exact (ModuleCat.subsingleton_of_isZero (HomologicalComplex.isZero_single_obj_X
    (.up ℤ) 0 (ModuleCat.of k R) j hj)).elim z.down 0

private theorem graded_ext {M N : (transported.{u,v,t} k R).Module} {n : ℤ} {f g : gradedHom M N n}
    (h : ∀ i j (e : i + n = j) (x : (M.complex ()).X i),
      component f () i j e x = component g () i j e x) : f = g := by
  apply Subtype.ext
  funext a
  cases a
  apply Cochain.ext
  intro i j e
  exact ModuleCat.hom_ext (LinearMap.ext (h i j e))

variable (E : StrictComparison.{u,v,t} k R)

private def termsEquiv (X : compValue.{max v t} R) (i : ℤ) :
    ((restrictComplex.{u,v,t} k R).obj X).X i ≃ₗ[k] ((E.strict.functor.obj X).complex ()).X i :=
  letI : IsIso ((E.terms X).hom.f i) :=
    (inferInstance : IsIso (((HomologicalComplex.eval _ _ i).mapIso (E.terms X)).hom))
  LinearEquiv.ofBijective ((E.terms X).hom.f i).hom
    (ConcreteCategory.bijective_of_isIso ((E.terms X).hom.f i))

private lemma terms_natural_apply {X Y : compValue.{max v t} R} (f : X ⟶ Y) (i : ℤ) (x : X.X i) :
    (E.terms Y).hom.f i (f.f i x) = ((E.strict.functor.map f).app ()).f i ((E.terms X).hom.f i x) :=
  ConcreteCategory.congr_hom (HomologicalComplex.congr_hom (E.terms_natural f) i) x

private def conjugateFamily {X Y : compValue.{max v t} R} {n : ℤ} (f : Cochain X Y n) :
    Cochain ((E.strict.functor.obj X).complex ()) ((E.strict.functor.obj Y).complex ()) n :=
  ((Cochain.ofHom (E.terms X).inv).comp
    (f.map (ModuleCat.restrictScalars.{max v t} (algebraMap k R))) (zero_add n)).comp
      (Cochain.ofHom (E.terms Y).hom) (add_zero n)

private theorem conjugateFamily_apply {X Y : compValue.{max v t} R} {n : ℤ} (f : Cochain X Y n)
    (i j : ℤ) (e : i + n = j) (x : X.X i) :
    (conjugateFamily E f).v i j e ((E.terms X).hom.f i x) =
      (E.terms Y).hom.f j (f.v i j e x) := by
  simp only [conjugateFamily, Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.map_v, ModuleCat.comp_apply]
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (E.terms X).hom_inv_id i) x
  change (E.terms X).inv.f i ((E.terms X).hom.f i x) = x at h
  rw [h]
  rfl

private def conjugate {X Y : compValue.{max v t} R} {n : ℤ} (f : Cochain X Y n) :
    gradedHom (E.strict.functor.obj X) (E.strict.functor.obj Y) n :=
  ⟨fun a => by cases a; exact conjugateFamily E f, by
    rintro ⟨⟩ ⟨⟩ i j l ir lr h hi hl x z
    obtain ⟨x, rfl⟩ := (termsEquiv E X i).surjective x
    change (conjugateFamily E f).v l lr hl
        (act (E.strict.functor.obj X) i j l h ((E.terms X).hom.f i x) z) =
      act (E.strict.functor.obj Y) ir j lr _
        ((conjugateFamily E f).v i ir hi ((E.terms X).hom.f i x)) z
    by_cases hj : j = 0
    · subst j
      obtain rfl : l = i := by omega
      obtain rfl : lr = ir := by omega
      obtain ⟨a, rfl⟩ := E.scalar.surjective z
      rw [E.action, conjugateFamily_apply, conjugateFamily_apply, E.action]
      congr 1
      exact (f.v _ _ _).hom.map_smul a (show X.X _ from x)
    · rw [stalk_zero j hj z]
      simp only [map_zero]⟩

private theorem conjugate_apply {X Y : compValue.{max v t} R} {n : ℤ} (f : Cochain X Y n)
    (i j : ℤ) (e : i + n = j) (x : X.X i) :
    component (conjugate E f) () i j e ((E.terms X).hom.f i x) =
      (E.terms Y).hom.f j (f.v i j e x) :=
  conjugateFamily_apply E f i j e x

private def unConjugate {X Y : compValue.{max v t} R} {n : ℤ}
    (f : gradedHom (E.strict.functor.obj X) (E.strict.functor.obj Y) n) : Cochain X Y n :=
  Cochain.mk fun i j e =>
    ModuleCat.ofHom
      { toFun := fun x => (E.terms Y).inv.f j (component f () i j e ((E.terms X).hom.f i x))
        map_add' := fun x y => by simp only [map_add]
        map_smul' := fun a x => by
          have h := f.property (a := ()) (b := ()) i 0 i j j (add_zero i) e e
            ((E.terms X).hom.f i x) (E.scalar a)
          change component f () i j e
            (act (E.strict.functor.obj X) i 0 i _ ((E.terms X).hom.f i x) (E.scalar a)) =
            act (E.strict.functor.obj Y) j 0 j _
              (component f () i j e ((E.terms X).hom.f i x)) (E.scalar a) at h
          obtain ⟨y, hy⟩ := (termsEquiv E Y j).surjective
            (component f () i j e ((E.terms X).hom.f i x))
          change (E.terms Y).hom.f j y = _ at hy
          rw [← hy, E.action, E.action] at h
          simp only [RingHom.id_apply]
          rw [← hy, h]
          have inv (z : Y.X j) : (E.terms Y).inv.f j ((E.terms Y).hom.f j z) = z :=
            ConcreteCategory.congr_hom (HomologicalComplex.congr_hom (E.terms Y).hom_inv_id j) z
          rw [inv, inv] }

private theorem unConjugate_apply {X Y : compValue.{max v t} R} {n : ℤ}
    (f : gradedHom (E.strict.functor.obj X) (E.strict.functor.obj Y) n)
    (i j : ℤ) (e : i + n = j) (x : X.X i) :
    (E.terms Y).hom.f j ((unConjugate E f).v i j e x) =
      component f () i j e ((E.terms X).hom.f i x) := by
  rw [unConjugate, Cochain.mk_v]
  exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom (E.terms Y).inv_hom_id j) _

private theorem conjugate_bijective (X Y : compValue.{max v t} R) (n : ℤ) :
    Function.Bijective (conjugate E (X := X) (Y := Y) (n := n)) := by
  constructor
  · intro f g h
    apply Cochain.ext
    intro i j e
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply (termsEquiv E Y j).injective
    change (E.terms Y).hom.f j (f.v i j e x) = (E.terms Y).hom.f j (g.v i j e x)
    rw [← conjugate_apply, ← conjugate_apply, h]
  · intro f
    refine ⟨unConjugate E f, graded_ext (fun i j e x => ?_)⟩
    obtain ⟨x, rfl⟩ := (termsEquiv E X i).surjective x
    exact (conjugate_apply E _ i j e x).trans (unConjugate_apply E f i j e x)

private def conjugateLinear (X Y : compValue.{max v t} R) (n : ℤ) :
    ((restrictComplex.{u,v,t} k R).obj (internalHomValue X Y)).X n →ₗ[k]
      gradedHom (E.strict.functor.obj X) (E.strict.functor.obj Y) n where
  toFun := conjugate E
  map_add' f g := by
    apply graded_ext
    intro i j e x
    obtain ⟨x, rfl⟩ := (termsEquiv E X i).surjective x
    change component (conjugate E (f + g)) () i j e ((E.terms X).hom.f i x) =
      ((conjugate E f).val () + (conjugate E g).val ()).v i j e ((E.terms X).hom.f i x)
    rw [conjugate_apply, Cochain.add_v, Cochain.add_v]
    simp only [ModuleCat.hom_add, LinearMap.add_apply, map_add]
    exact congrArg₂ (· + ·) (conjugate_apply E f i j e x).symm
      (conjugate_apply E g i j e x).symm
  map_smul' c f := by
    apply graded_ext
    intro i j e x
    obtain ⟨x, rfl⟩ := (termsEquiv E X i).surjective x
    change component (conjugate E (algebraMap k R c • (show Cochain X Y n from f))) () i j e ((E.terms X).hom.f i x) =
      (c • (conjugate E f).val ()).v i j e ((E.terms X).hom.f i x)
    rw [conjugate_apply, Cochain.smul_v, Cochain.smul_v]
    simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
    change (E.terms Y).hom.f j (c • (show ((restrictComplex.{u,v,t} k R).obj Y).X j
        from f.v i j e x)) = c • component (conjugate E f) () i j e ((E.terms X).hom.f i x)
    rw [map_smul, conjugate_apply]

private theorem conjugate_differential (X Y : compValue.{max v t} R) (n : ℤ) (f : Cochain X Y n) :
    conjugate E (δ n (n + 1) f) =
      ((DerivedHom.internalHom (E.strict.functor.obj X) (E.strict.functor.obj Y)).complex ()).d
        n (n + 1) (conjugate E f) := by
  apply Subtype.ext
  funext a
  cases a
  change conjugateFamily E (δ n (n + 1) f) = δ n (n + 1) (conjugateFamily E f)
  simp only [conjugateFamily, δ_comp_ofHom, δ_ofHom_comp, δ_map]

private theorem cochain_smul_apply {X Y : compValue.{max v t} R} {n : ℤ}
    (a : R) (f : Cochain X Y n) (i j : ℤ) (e : i + n = j) (x : X.X i) :
    (a • f).v i j e x = a • f.v i j e x := by
  rw [Cochain.smul_v]
  rfl

private def homDegreeEquiv (X Y : compValue.{max v t} R) (n : ℤ) :
    ((E.strict.functor.obj (internalHomValue X Y)).complex ()).X n ≃ₗ[k]
      gradedHom (E.strict.functor.obj X) (E.strict.functor.obj Y) n :=
  (termsEquiv E (internalHomValue X Y) n).symm.trans
    (LinearEquiv.ofBijective (conjugateLinear E X Y n) (conjugate_bijective E X Y n))

private theorem homDegreeEquiv_apply (X Y : compValue.{max v t} R) (n : ℤ)
    (f : Cochain X Y n) :
    homDegreeEquiv E X Y n ((E.terms (internalHomValue X Y)).hom.f n f) = conjugate E f := by
  change (conjugateLinear E X Y n)
      ((termsEquiv E (internalHomValue X Y) n).symm
        (termsEquiv E (internalHomValue X Y) n f)) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

private theorem conjugate_action (X Y : compValue.{max v t} R) (n : ℤ) (f : Cochain X Y n)
    (a : R) :
    conjugate E (a • f) =
      act (DerivedHom.internalHom (E.strict.functor.obj X) (E.strict.functor.obj Y))
        n 0 n (add_zero n) (conjugate E f) (E.scalar a) := by
  apply graded_ext
  intro i j e x
  obtain ⟨y, hy⟩ := (termsEquiv E X i).surjective x
  change (E.terms X).hom.f i y = x at hy
  rw [← hy, conjugate_apply, cochain_smul_apply]
  have h := DerivedHom.scalarFormula (E.strict.functor.obj X) (E.strict.functor.obj Y)
    n 0 n (add_zero n) (conjugate E f) (E.scalar a) i j j e e ((E.terms X).hom.f i y)
  simp only [mul_zero, Int.negOnePow_zero, one_smul] at h
  rw [h, conjugate_apply, E.action]

private def strictHomIso (X Y : compValue.{max v t} R) :
    E.strict.functor.obj (internalHomValue X Y) ≅
      DerivedHom.internalHom (E.strict.functor.obj X) (E.strict.functor.obj Y) :=
  DG.CoefficientLift.isoOfComponents
    (fun a n => by cases a; exact homDegreeEquiv E X Y n)
    (by
      rintro ⟨⟩ n z
      obtain ⟨f, rfl⟩ := (termsEquiv E (internalHomValue X Y) n).surjective z
      change homDegreeEquiv E X Y (n+1)
          (((E.strict.functor.obj (internalHomValue X Y)).complex ()).d n (n+1)
            ((E.terms (internalHomValue X Y)).hom.f n f)) =
        ((DerivedHom.internalHom (E.strict.functor.obj X) (E.strict.functor.obj Y)).complex ()).d
          n (n+1) (homDegreeEquiv E X Y n ((E.terms (internalHomValue X Y)).hom.f n f))
      have h := ConcreteCategory.congr_hom ((E.terms (internalHomValue X Y)).hom.comm n (n+1)).symm f
      change (E.terms (internalHomValue X Y)).hom.f (n+1) (δ n (n+1) f) =
        ((E.strict.functor.obj (internalHomValue X Y)).complex ()).d n (n+1)
          ((E.terms (internalHomValue X Y)).hom.f n f) at h
      rw [← h, homDegreeEquiv_apply, homDegreeEquiv_apply, conjugate_differential])
    (by
      rintro ⟨⟩ ⟨⟩ i j n e z a
      obtain ⟨f, rfl⟩ := (termsEquiv E (internalHomValue X Y) i).surjective z
      change homDegreeEquiv E X Y n
          (act (E.strict.functor.obj (internalHomValue X Y)) i j n e
            ((E.terms (internalHomValue X Y)).hom.f i f) a) =
        act (DerivedHom.internalHom (E.strict.functor.obj X) (E.strict.functor.obj Y))
          i j n e (homDegreeEquiv E X Y i ((E.terms (internalHomValue X Y)).hom.f i f)) a
      by_cases h : j = 0
      · subst j
        obtain rfl : n = i := by omega
        obtain ⟨r, rfl⟩ := E.scalar.surjective a
        rw [E.action, homDegreeEquiv_apply, homDegreeEquiv_apply, conjugate_action]
      · rw [stalk_zero.{u,v,t} (k := k) (R := R) j h a]
        simp only [map_zero])

private theorem strictHomIso_apply (X Y : compValue.{max v t} R) (n : ℤ)
    (f : Cochain X Y n) :
    ((strictHomIso E X Y).hom.app ()).f n ((E.terms (internalHomValue X Y)).hom.f n f) =
      conjugate E f :=
  homDegreeEquiv_apply E X Y n f

theorem strictHomComparison : StrictHomComparison.{u,v,t} := by
  intro k _ _ R _ _ E
  refine ⟨⟨strictHomIso E, ?_, ?_⟩⟩
  · intro X Y n i j e f x
    rw [strictHomIso_apply, conjugate_apply]
  · intro S hS X X' Y Y' f g
    apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := (termsEquiv E (internalHomValue X Y) n).surjective z
    change ((strictHomIso E X' Y').hom.app ()).f n
        (((E.strict.functor.map (internalHomMapValue f g)).app ()).f n
          ((E.terms (internalHomValue X Y)).hom.f n z)) =
      ((S.post (E.strict.functor.obj X') (E.strict.functor.map g)).app ()).f n
        (((S.pre (E.strict.functor.obj Y) (E.strict.functor.map f)).app ()).f n
          (((strictHomIso E X Y).hom.app ()).f n ((E.terms (internalHomValue X Y)).hom.f n z)))
    rw [← terms_natural_apply, strictHomIso_apply, strictHomIso_apply]
    apply graded_ext
    intro i j e x
    obtain ⟨y, hy⟩ := (termsEquiv E X' i).surjective x
    change (E.terms X').hom.f i y = x at hy
    rw [← hy, conjugate_apply, hS.post, hS.pre, ← terms_natural_apply, conjugate_apply,
      ← terms_natural_apply]
    exact congrArg ((E.terms Y').hom.f j ·) (DerivedFormalization.internalHomMap_apply (hi := e) f g z y)

section ScalarChange

open Specs.DerivedFormalization.Affine.Tensor (restrict restrictFunctor)
open Specs.DerivedFormalization.Descent.PerfectHomBaseChange
  (extend extendCochain comparison extendComp changeHomCoefficients scalarExtension)
open DerivedFormalization.Descent (homBaseChange_apply changeHomCoefficients_apply
  changeCoefficients_apply homBaseChange_isIso homBaseChange_changeCoefficients)

variable {E : StrictComparison.{u,v,t} k R} {F : StrictComparison.{u,v,t} k S}
variable {X : compValue.{max v t} R} {Y : compValue.{max v t} S}

private theorem transportedMap_scalar (φ : R →ₐ[k] S) (r : R) :
    (transportedMap.{u,v,t} φ).chainMap.f 0 (E.scalar r) = F.scalar (φ r) := by
  rw [E.scalar_apply, F.scalar_apply]
  rfl

/-- The terms of a map semilinear over the given map of ordinary algebras. -/
private structure SemilinearCochainMap (φ : R →ₐ[k] S)
    (X : compValue.{max v t} R) (Y : compValue.{max v t} S) where
  apply (i : ℤ) : X.X i → Y.X i
  add (i : ℤ) (x y : X.X i) : apply i (x + y) = apply i x + apply i y
  smul (i : ℤ) (r : R) (x : X.X i) : apply i (r • x) = φ r • apply i x
  comm (i : ℤ) (x : X.X i) :
    apply (i+1) (X.d i (i+1) x) = Y.d i (i+1) (apply i x)

variable {φ : R →ₐ[k] S}

private def SemilinearCochainMap.restrictTerms (m : SemilinearCochainMap φ X Y) (i : ℤ) :
    ((restrictComplex.{u,v,t} k R).obj X).X i →ₗ[k]
      ((restrictComplex.{u,v,t} k S).obj Y).X i where
  toFun := m.apply i
  map_add' := m.add i
  map_smul' c x := by
    change m.apply i (algebraMap k R c • (show X.X i from x)) =
      algebraMap k S c • m.apply i x
    rw [m.smul, φ.commutes]

private def SemilinearCochainMap.toDG (m : SemilinearCochainMap φ X Y) :
    E.strict.functor.obj X ⟶
      restrict (transportedMap.{u,v,t} φ :
        (transported.{u,v,t} k R).toCommDGAlgebra ⟶ (transported.{u,v,t} k S).toCommDGAlgebra)
        (F.strict.functor.obj Y) := by
  let l : (restrictComplex.{u,v,t} k R).obj X ⟶ (restrictComplex.{u,v,t} k S).obj Y :=
    CochainComplex.ofHom (fun i => ModuleCat.ofHom
      (X := ((restrictComplex.{u,v,t} k R).obj X).X i)
      (Y := ((restrictComplex.{u,v,t} k S).obj Y).X i) (m.restrictTerms i)) (fun i => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact (m.comm i x).symm)
  refine ⟨fun a => by cases a; exact (E.terms X).inv ≫ l ≫ (F.terms Y).hom, ?_⟩
  rintro ⟨⟩ ⟨⟩ i j n h z a
  have point (l' : ℤ) (x : X.X l') :
      ((E.terms X).inv ≫ l ≫ (F.terms Y).hom).f l' ((E.terms X).hom.f l' x) =
        (F.terms Y).hom.f l' (m.apply l' x) := by
    have e := ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom (E.terms X).hom_inv_id l') x
    change (E.terms X).inv.f l' ((E.terms X).hom.f l' x) = x at e
    change (F.terms Y).hom.f l' (m.apply l' ((E.terms X).inv.f l' ((E.terms X).hom.f l' x))) = _
    rw [e]
  by_cases hj : j = 0
  · subst j
    obtain rfl : i = n := by omega
    obtain ⟨r, rfl⟩ := E.scalar.surjective a
    obtain ⟨x, hx⟩ := (termsEquiv E X i).surjective z
    change (E.terms X).hom.f i x = z at hx
    change ((E.terms X).inv ≫ l ≫ (F.terms Y).hom).f i
        (act (E.strict.functor.obj X) i 0 i _ z (E.scalar r)) =
      act (F.strict.functor.obj Y) i 0 i _
        (((E.terms X).inv ≫ l ≫ (F.terms Y).hom).f i z)
        ((transportedMap.{u,v,t} φ).chainMap.f 0 (E.scalar r))
    rw [← hx, E.action, point, point, transportedMap_scalar, F.action, m.smul]
  · rw [stalk_zero.{u,v,t} (k := k) (R := R) j hj a]
    simp only [map_zero]

private theorem SemilinearCochainMap.toDG_apply (m : SemilinearCochainMap φ X Y)
    (i : ℤ) (x : X.X i) :
    ((m.toDG (E := E) (F := F)).app ()).f i ((E.terms X).hom.f i x) =
      (F.terms Y).hom.f i (m.apply i x) := by
  change (F.terms Y).hom.f i (m.apply i ((E.terms X).inv.f i ((E.terms X).hom.f i x))) = _
  have e := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom (E.terms X).hom_inv_id i) x
  change (E.terms X).inv.f i ((E.terms X).hom.f i x) = x at e
  rw [e]

private def transferHom (I : StrictHom E) (J : StrictHom F)
    (P X : compValue.{max v t} R) (P' X' : compValue.{max v t} S)
    (m : SemilinearCochainMap φ (internalHomValue P X) (internalHomValue P' X')) :
    DerivedHom.internalHom (E.strict.functor.obj P) (E.strict.functor.obj X) ⟶
      restrict (transportedMap.{u,v,t} φ :
        (transported.{u,v,t} k R).toCommDGAlgebra ⟶ (transported.{u,v,t} k S).toCommDGAlgebra)
        (DerivedHom.internalHom (F.strict.functor.obj P') (F.strict.functor.obj X')) :=
  (I.iso P X).inv ≫ m.toDG ≫ (restrictFunctor (transportedMap.{u,v,t} φ :
    (transported.{u,v,t} k R).toCommDGAlgebra ⟶
      (transported.{u,v,t} k S).toCommDGAlgebra)).map (J.iso P' X').hom

private theorem transferHom_apply (I : StrictHom E) (J : StrictHom F)
    (P X : compValue.{max v t} R) (P' X' : compValue.{max v t} S)
    (m : SemilinearCochainMap φ (internalHomValue P X) (internalHomValue P' X'))
    (n : ℤ) (z : Cochain P X n) :
    ((transferHom I J P X P' X' m).app ()).f n ((I.chain P X).f n z) =
      (J.chain P' X').f n (m.apply n z) := by
  have cancel := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (congrArg (fun f => RightDGModuleHomModel.app f ()) (I.iso P X).hom_inv_id) n)
      ((E.terms (internalHomValue P X)).hom.f n z)
  change (((I.iso P X).inv.app ()).f n)
      ((((I.iso P X).hom.app ()).f n) ((E.terms (internalHomValue P X)).hom.f n z)) =
    (E.terms (internalHomValue P X)).hom.f n z at cancel
  change (((J.iso P' X').hom.app ()).f n)
      (((m.toDG (E := E) (F := F)).app ()).f n
        ((((I.iso P X).inv.app ()).f n)
          ((((I.iso P X).hom.app ()).f n) ((E.terms (internalHomValue P X)).hom.f n z)))) = _
  rw [cancel, m.toDG_apply]
  rfl

private def augmentOrdinary (P X : compValue.{max v t} R) [Algebra R S] [IsScalarTower k R S] :
    SemilinearCochainMap (IsScalarTower.toAlgHom k R S) (internalHomValue P X)
      (internalHomValue ((extend R S).obj P) ((extend R S).obj X)) where
  apply n := extendCochain S n
  add n := map_add (extendCochain S n)
  smul n r z := by
    letI : Module R (Cochain ((extend R S).obj P) ((extend R S).obj X) n) :=
      Module.restrictScalars R S _
    exact (extendCochain S n).map_smul r z
  comm n z := (δ_map n (n+1) z (scalarExtension R S)).symm

private theorem extendCochain_tmul (S : Type v) [CommRing S] [Algebra R S]
    (P X : compValue.{max v t} R) (n i j : ℤ) (h : i+n=j) (z : Cochain P X n)
    (s : S) (x : P.X i) :
    (extendCochain S n z).v i j h (s ⊗ₜ[R] x) = s ⊗ₜ[R] z.v i j h x :=
  rfl

private def changeHomOrdinary {B T : Type v} [CommRing B] [CommRing T]
    [Algebra k B] [Algebra k T] [Algebra B R] [Algebra B T]
    [IsScalarTower k B R] [IsScalarTower k B T]
    (φ : R →ₐ[B] T) (P X : compValue.{max v t} B) :
    SemilinearCochainMap (φ.restrictScalars k)
      (internalHomValue ((extend B R).obj P) ((extend B R).obj X))
      (internalHomValue ((extend B T).obj P) ((extend B T).obj X)) := by
  letI : Algebra R T := φ.toRingHom.toAlgebra
  letI : IsScalarTower B R T := IsScalarTower.of_algHom φ
  let M := changeHomCoefficients B R T P X
  refine ⟨fun n => M.f n, ?_, ?_, ?_⟩
  · intro n x y
    exact LinearMap.map_add (M.f n).hom x y
  · intro n r z
    let U := internalHomValue ((extend B R).obj P) ((extend B R).obj X)
    let L := comparison T ((extend B R).obj P) ((extend B R).obj X) ≫
      internalHomMapValue (extendComp B R T P).inv (extendComp B R T X).hom
    change L.f n ((1 : T) ⊗ₜ[R] (r • (show U.X n from z))) =
      φ r • L.f n ((1 : T) ⊗ₜ[R] (show U.X n from z))
    rw [← TensorProduct.smul_tmul, ← map_smul]
    congr 1
  · intro n x
    let U := internalHomValue ((extend B R).obj P) ((extend B R).obj X)
    let x' : ((Specs.DerivedFormalization.Descent.PerfectHomBaseChange.restrict B R).obj U).X n := x
    have h := ConcreteCategory.congr_hom (M.comm n (n+1)) x'
    exact h.symm

set_option maxHeartbeats 750000 in
private theorem homBaseChange_coface_apply {B T : Type v} [CommRing B] [CommRing T]
    [Algebra B R] [Algebra B T] (φ : R →ₐ[B] T) (P X : compValue.{max v t} B) (n : ℤ)
    (z : ((extend B R).obj (internalHomValue P X)).X n) :
    letI : Algebra R T := φ.toRingHom.toAlgebra
    letI : IsScalarTower B R T := IsScalarTower.of_algHom φ
    (changeHomCoefficients B R T P X).f n ((comparison R P X).f n z) =
      (comparison T P X).f n
        ((Specs.DerivedFormalization.Descent.PerfectHomBaseChange.changeCoefficients B R T
          (internalHomValue P X)).f n z) := by
  letI : Algebra R T := φ.toRingHom.toAlgebra
  letI : IsScalarTower B R T := IsScalarTower.of_algHom φ
  let U := ((extend B R).obj (internalHomValue P X))
  let z' : ((Specs.DerivedFormalization.Descent.PerfectHomBaseChange.restrict B R).obj U).X n := z
  have e := HomologicalComplex.congr_hom
    (homBaseChange_changeCoefficients.{v,v,max v t} B R T φ P X) n
  exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e) z').symm

end ScalarChange

section Amitsur

open Specs.DerivedFormalization.Descent.PerfectHomBaseChange
  (extend extendCochain comparison extendComp changeHomCoefficients scalarExtension)
open DerivedFormalization.Descent (homBaseChange_apply changeHomCoefficients_apply
  changeCoefficients_apply homBaseChange_isIso homBaseChange_changeCoefficients)

variable {A B C : Type v} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra k A] [Algebra k B] [Algebra k C] [Algebra A B] [Algebra A C]
variable [IsScalarTower k A B] [IsScalarTower k A C]

local notation "Bₚ" => ColumnRing A B C
local notation "extCol" => column (A := A) (C := C)
local notation "coeff" => columnCochainMap (A := A) (C := C)
local notation "homCoeff" => columnHomMap (A := A) (C := C)
local notation "rings" => columnMap (A := A) (C := C)

private theorem columnCochainMap_tmul {p q : ℕ} (f : Fin (p+1) → Fin (q+1))
    (X : compValue.{max v t} B) (n : ℤ) (s : Bₚ p) (x : X.X n) :
    (coeff X f).f n (s ⊗ₜ[B] x) = rings f s ⊗ₜ[B] x :=
  changeCoefficients_apply B (Bₚ p) (Bₚ q) (rings f) X n s x

private theorem columnHomMap_eval {p q : ℕ} (f : Fin (p+1) → Fin (q+1))
    (P X : compValue.{max v t} B) (n i j : ℤ) (h : i+n=j)
    (z : Cochain (extCol P p) (extCol X p) n) (x : (extCol P p).X i) :
    ((homCoeff P X f).f n z).v i j h ((coeff P f).f i x) =
      (coeff X f).f j (z.v i j h x) :=
  changeHomCoefficients_apply B (Bₚ p) (Bₚ q) (rings f) P X n i j h z x

private abbrev changeOrdinary {p q : ℕ} (f : Fin (p+1) → Fin (q+1))
    (P X : compValue.{max v t} B) :=
  changeHomOrdinary.{u,v,t} (k := k) (rings f : Bₚ p →ₐ[B] Bₚ q) P X

private theorem columnMap_id (p : ℕ) :
    rings (id : Fin (p+1) → Fin (p+1)) = AlgHom.id B (Bₚ p) := by
  unfold columnMap
  have h : (AmitsurAlgebrasSpec.map (id : Fin (p+1) → Fin (p+1)) :
      AmitsurAlgebrasSpec.degree A C p →ₐ[A] _) = AlgHom.id A _ :=
    Descent.AmitsurAlgebras.map_id (A := A) (B := C) (p+1)
  rw [h, Algebra.TensorProduct.map_id]

private theorem columnMap_comp {p q r : ℕ} (f : Fin (p+1) → Fin (q+1))
    (g : Fin (q+1) → Fin (r+1)) : (rings (g ∘ f) : Bₚ p →ₐ[B] Bₚ r) = (rings g).comp (rings f : Bₚ p →ₐ[B] Bₚ q) := by
  unfold columnMap
  have h : (AmitsurAlgebrasSpec.map (g ∘ f) : AmitsurAlgebrasSpec.degree A C p →ₐ[A] _) =
      (AmitsurAlgebrasSpec.map g).comp
        (AmitsurAlgebrasSpec.map f : AmitsurAlgebrasSpec.degree A C p →ₐ[A] _) :=
    Descent.AmitsurAlgebras.map_comp (A := A) (B := C) f g
  rw [h, Algebra.TensorProduct.map_id_comp]

private theorem columnCochainMap_id (X : compValue.{max v t} B) (p : ℕ)
    (n : ℤ) (z : (extCol X p).X n) :
    (coeff X (id : Fin (p+1) → Fin (p+1))).f n z = z := by
  induction z using TensorProduct.inductionOn with
  | tmul s x => rw [columnCochainMap_tmul, columnMap_id]; rfl
  | add x y hx hy => rw [map_add, hx, hy]

private theorem columnCochainMap_comp {p q r : ℕ} (f : Fin (p+1) → Fin (q+1))
    (g : Fin (q+1) → Fin (r+1)) (X : compValue.{max v t} B)
    (n : ℤ) (z : (extCol X p).X n) :
    (coeff X (g ∘ f)).f n z = (coeff X g).f n ((coeff X f).f n z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s x => simp only [columnCochainMap_tmul, columnMap_comp, AlgHom.comp_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem cochain_column_ext {p : ℕ} {P X : compValue.{max v t} B} {n : ℤ}
    {f g : Cochain (extCol P p) (extCol X p) n}
    (h : ∀ i j (e : i+n=j) (x : P.X i),
      f.v i j e ((1 : Bₚ p) ⊗ₜ[B] x) = g.v i j e ((1 : Bₚ p) ⊗ₜ[B] x)) : f = g := by
  apply Cochain.ext
  intro i j e
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
      rw [show (s ⊗ₜ[B] x : (extCol P p).X i) = s • ((1 : Bₚ p) ⊗ₜ[B] x) by
        rw [TensorProduct.smul_tmul']; simp]
      rw [map_smul, map_smul, h i j e x]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem columnHomMap_id (P X : compValue.{max v t} B) (p : ℕ)
    (n : ℤ) (z : Cochain (extCol P p) (extCol X p) n) :
    (homCoeff P X (id : Fin (p+1) → Fin (p+1))).f n z = z := by
  apply cochain_column_ext
  intro i j h x
  have eq := columnHomMap_eval (id : Fin (p+1) → Fin (p+1)) P X n i j h
    z ((1 : Bₚ p) ⊗ₜ[B] x)
  simpa only [columnCochainMap_id] using eq

private theorem columnHomMap_comp {p q r : ℕ} (f : Fin (p+1) → Fin (q+1))
    (g : Fin (q+1) → Fin (r+1)) (P X : compValue.{max v t} B)
    (n : ℤ) (z : Cochain (extCol P p) (extCol X p) n) :
    (homCoeff P X (g ∘ f)).f n z = (homCoeff P X g).f n ((homCoeff P X f).f n z) := by
  apply cochain_column_ext
  intro i j h x
  let w : (extCol P p).X i := (1 : Bₚ p) ⊗ₜ[B] x
  have hw : (coeff P (g ∘ f)).f i w = (1 : Bₚ r) ⊗ₜ[B] x := by
    simp only [w, columnCochainMap_tmul, map_one]
  rw [← hw, columnHomMap_eval, columnCochainMap_comp f g P,
    columnHomMap_eval, columnHomMap_eval, columnCochainMap_comp f g X]


private theorem columnHomMap_augment {p q : ℕ} (f : Fin (p+1) → Fin (q+1))
    (P X : compValue.{max v t} B) (n : ℤ) (z : Cochain P X n) :
    (homCoeff P X f).f n (extendCochain (Bₚ p) n z) = extendCochain (Bₚ q) n z := by
  apply cochain_column_ext
  intro i j h x
  let w : (extCol P p).X i := (1 : Bₚ p) ⊗ₜ[B] x
  have hw : (coeff P f).f i w = (1 : Bₚ q) ⊗ₜ[B] x := by
    simp only [w, columnCochainMap_tmul, map_one]
  rw [← hw, columnHomMap_eval, hw]
  change (coeff X f).f j ((extendCochain (Bₚ p) n z).v i j h
      ((1 : Bₚ p) ⊗ₜ[B] x)) = (extendCochain (Bₚ q) n z).v i j h ((1 : Bₚ q) ⊗ₜ[B] x)
  rw [extendCochain_tmul, columnCochainMap_tmul, map_one, extendCochain_tmul]

private theorem homChain_surjective {E : StrictComparison.{u,v,t} k R} (I : StrictHom E)
    (P X : compValue.{max v t} R) (n : ℤ) :
    Function.Surjective ((I.chain P X).f n) := by
  let e := (HomologicalComplex.eval _ _ n).mapIso (E.terms (internalHomValue P X))
  have hs : Function.Surjective e.hom := (ConcreteCategory.bijective_of_isIso e.hom).2
  intro z
  let z' := ((I.iso P X).inv.app ()).f n z
  obtain ⟨w, hw⟩ := hs z'
  refine ⟨w, ?_⟩
  change ((I.iso P X).hom.app ()).f n (e.hom w) = z
  rw [hw]
  exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (congrArg (fun f => RightDGModuleHomModel.app f ()) (I.iso P X).inv_hom_id) n) z

private def columnBaseChangeIso
    (F : ∀ p, StrictComparison.{u,v,t} k (Bₚ p)) (J : ∀ p, StrictHom (F p))
    (P X : compValue.{max v t} B) (hP : BoundedFiniteProjective P) (p : ℕ) :
    (F p).strict.functor.obj (extCol (internalHomValue P X) p) ≅ dgHomColumn F p P X := by
  letI := homBaseChange_isIso.{v,v,max v t} B (Bₚ p) P X hP.1 hP.2.1 hP.2.2
  exact (F p).strict.functor.mapIso (asIso (comparison (Bₚ p) P X)) ≪≫
    (J p).iso (extCol P p) (extCol X p)

private theorem columnBaseChangeIso_apply
    (F : ∀ p, StrictComparison.{u,v,t} k (Bₚ p)) (J : ∀ p, StrictHom (F p))
    (P X : compValue.{max v t} B) (hP : BoundedFiniteProjective P) (p : ℕ)
    (n : ℤ) (z : (extCol (internalHomValue P X) p).X n) :
    ((columnBaseChangeIso F J P X hP p).hom.app ()).f n
        (((F p).terms (extCol (internalHomValue P X) p)).hom.f n z) =
      ((J p).chain (extCol P p) (extCol X p)).f n ((comparison (Bₚ p) P X).f n z) := by
  change (((J p).iso (extCol P p) (extCol X p)).hom.app ()).f n
      ((((F p).strict.functor.map (comparison (Bₚ p) P X)).app ()).f n
        (((F p).terms (extCol (internalHomValue P X) p)).hom.f n z)) = _
  rw [← terms_natural_apply]
  rfl

set_option maxHeartbeats 1600000 in
private theorem compatibleHomColumns (E : StrictComparison.{u,v,t} k B) (I : StrictHom E)
    (F : ∀ p, StrictComparison.{u,v,t} k (Bₚ p)) (J : ∀ p, StrictHom (F p)) :
    Nonempty (HomColumns E I F J) := by
  let a (p : ℕ) (P X : compValue.{max v t} B) :=
    transferHom I (J p) P X (extCol P p) (extCol X p) (augmentOrdinary P X)
  let m {p q : ℕ} (f : Fin (p+1) → Fin (q+1)) (P X : compValue.{max v t} B) :=
    transferHom (J p) (J q) (extCol P p) (extCol X p) (extCol P q) (extCol X q)
      (changeOrdinary f P X)
  have ha (p : ℕ) (P X : compValue.{max v t} B) (n : ℤ) (z : Cochain P X n) :
      ((a p P X).app ()).f n ((I.chain P X).f n z) =
        ((J p).chain (extCol P p) (extCol X p)).f n (extendCochain (Bₚ p) n z) :=
    transferHom_apply I (J p) P X _ _ (augmentOrdinary P X) n z
  have hm {p q : ℕ} (f : Fin (p+1) → Fin (q+1)) (P X : compValue.{max v t} B)
      (n : ℤ) (z : Cochain (extCol P p) (extCol X p) n) :
      ((m f P X).app ()).f n (((J p).chain (extCol P p) (extCol X p)).f n z) =
        ((J q).chain (extCol P q) (extCol X q)).f n ((homCoeff P X f).f n z) :=
    transferHom_apply (J p) (J q) _ _ _ _ (changeOrdinary f P X) n z
  refine ⟨{ augmentation := a
            augmentation_ordinary := ha
            map := fun f => m f
            map_ordinary := hm
            baseChangeIso := columnBaseChangeIso F J
            baseChange_hom := fun _ _ _ _ => rfl
            augmentation_evaluation := ?_
            map_evaluation := ?_
            map_id := ?_
            map_comp := ?_
            augmentation_comp := ?_
            baseChange_evaluation := ?_
            baseChange_coface := ?_ }⟩
  · intro p P X n i j h z s x
    rw [ha]
    exact ((J p).evaluation (extCol P p) (extCol X p) n i j h _
      (s ⊗ₜ[B] x)).trans (congrArg (((F p).terms (extCol X p)).hom.f j ·)
        (extendCochain_tmul (Bₚ p) P X n i j h z s x))
  · intro p q f P X n i j h z x
    rw [hm]
    exact ((J q).evaluation (extCol P q) (extCol X q) n i j h _
      ((coeff P f).f i x)).trans (congrArg (((F q).terms (extCol X q)).hom.f j ·)
        (columnHomMap_eval f P X n i j h z x))
  · intro p P X
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := homChain_surjective (J p) (extCol P p) (extCol X p) n z
    change ((m id P X).app ()).f n (((J p).chain (extCol P p) (extCol X p)).f n z) = _
    rw [hm, columnHomMap_id]
    rfl
  · intro p q r f g P X
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := homChain_surjective (J p) (extCol P p) (extCol X p) n z
    change ((m (g ∘ f) P X).app ()).f n (((J p).chain (extCol P p) (extCol X p)).f n z) =
      ((m g P X).app ()).f n
        (((m f P X).app ()).f n (((J p).chain (extCol P p) (extCol X p)).f n z))
    rw [hm, hm, hm, columnHomMap_comp]
  · intro p q f P X
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := homChain_surjective I P X n z
    change ((m f P X).app ()).f n (((a p P X).app ()).f n ((I.chain P X).f n z)) =
      ((a q P X).app ()).f n ((I.chain P X).f n z)
    rw [ha, hm, ha, columnHomMap_augment]
  · intro P X hP p n i j h s s' z x
    rw [columnBaseChangeIso_apply F J]
    exact ((J p).evaluation (extCol P p) (extCol X p) n i j h _
      (s' ⊗ₜ[B] x)).trans (congrArg (((F p).terms (extCol X p)).hom.f j ·)
        (homBaseChange_apply B (Bₚ p) P X n i j h s s' z x))
  · intro p q f P X hP n z
    rw [columnBaseChangeIso_apply F J, hm, columnBaseChangeIso_apply F J]
    exact congrArg (((J q).chain (extCol P q) (extCol X q)).f n ·)
      (homBaseChange_coface_apply (rings f : Bₚ p →ₐ[B] Bₚ q) P X n z)

theorem amitsurHomComparison : AmitsurHomComparison.{u,v,t} := by
  intro k _ _ A B C _ _ _ _ _ _ _ _ _ _ E I F J
  exact compatibleHomColumns E I F J

end Amitsur

section LocalizationHelpers

attribute [local instance] HasDerivedCategory.standard

open Specs.DerivedFormalization.DerivedHomModels (Models Representative rHomValue modelMap)
open Specs.DerivedFormalization.Cochains (quotientValue qhValue)

private def conjugateFunctor {A B : Type*} [Category* A] [Category* B]
    (K : A ⥤ B) (obj : A → B) (a : ∀ X, K.obj X ≅ obj X) : A ⥤ B where
  obj := obj
  map f := (a _).inv ≫ K.map f ≫ (a _).hom
  map_id X := by simp
  map_comp f g := by simp

private def conjugateFunctorIso {A B : Type*} [Category* A] [Category* B]
    (K : A ⥤ B) (obj : A → B) (a : ∀ X, K.obj X ≅ obj X) :
    K ≅ conjugateFunctor K obj a :=
  NatIso.ofComponents a (by intro X Y f; simp [conjugateFunctor])

private def ordinaryProjectives (R : Type v) [CommRing R] :
    ObjectProperty (homotopyValue.{max v t} R) :=
  fun X => isKProjectiveValue X.as

private abbrev projectiveQuotient (R : Type v) [CommRing R] :
    (ordinaryProjectives.{v,t} R).FullSubcategory ⥤ derivedValue.{max v t} R :=
  (ordinaryProjectives.{v,t} R).ι ⋙ qhValue R

private theorem projectiveQuotient_isEquivalence (O : Models.{v,max v t} R) :
    (projectiveQuotient.{v,t} R).IsEquivalence := by
  let U := projectiveQuotient.{v,t} R
  have h (X Y : (ordinaryProjectives.{v,t} R).FullSubcategory) :
      Function.Bijective (U.map : (X ⟶ Y) → _) := by
    letI : CochainComplex.IsKProjective X.obj.as := X.property
    exact (CochainComplex.IsKProjective.Qh_map_bijective X.obj.as Y.obj).comp
      ((ordinaryProjectives.{v,t} R).fullyFaithfulι.homEquiv.bijective)
  letI : U.Full := ⟨fun hx => (h _ _).2 hx⟩
  letI : U.Faithful := ⟨fun he => (h _ _).1 he⟩
  letI : U.EssSurj := ⟨fun X => ⟨⟨(O.projective X).obj, O.isProjective X⟩,
    ⟨(O.projective X).iso⟩⟩⟩
  exact { }

private abbrev ordinaryLocalizedInputs (R : Type v) [CommRing R] :=
  (projectiveQuotient.{v,t} R).op.prod (qhValue.{max v t} R)

private def homotopyRepresentative (X : homotopyValue.{max v t} R) :
    Representative ((qhValue R).obj X) :=
  ⟨X, Iso.refl _⟩

private def ordinaryFactorization (O : Models.{v,max v t} R) :
    ((ordinaryProjectives.{v,t} R).ι.op.prod (𝟭 _)) ⋙ O.hom.functor ≅
      ordinaryLocalizedInputs.{v,t} R ⋙ rHomValue O :=
  NatIso.ofComponents (fun Z => by
    let X := homotopyRepresentative Z.1.unop.obj
    let Y := homotopyRepresentative Z.2
    letI := DerivedFormalization.DerivedHomModels.modelMap_isIso O X Y (Or.inl Z.1.unop.property)
    exact asIso (modelMap O X Y)) (by
      intro Z Z' f
      let X := homotopyRepresentative Z.1.unop.obj
      let X' := homotopyRepresentative Z'.1.unop.obj
      let Y := homotopyRepresentative Z.2
      let Y' := homotopyRepresentative Z'.2
      let a := (ordinaryProjectives.{v,t} R).ι.map f.1.unop
      let b := f.2
      have ha : X'.Over X ((qhValue R).map a) a := by
        simp [X, X', homotopyRepresentative, Representative.Over]
      have hb : Y.Over Y' ((qhValue R).map b) b := by
        simp [Y, Y', homotopyRepresentative, Representative.Over]
      exact DerivedFormalization.DerivedHomModels.modelMap_natural O X X' Y Y' _ _ a b ha hb)

private def unwhiskerLocalizationIso {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (L : A ⥤ B) (W : MorphismProperty A) [L.IsLocalization W] {F G : B ⥤ C}
    (α : L ⋙ F ≅ L ⋙ G) : F ≅ G :=
  (Localization.fullyFaithfulWhiskeringLeft L W C).preimageIso α

private theorem unwhiskerLocalizationIso_app {A B C : Type*} [Category* A] [Category* B]
    [Category* C] (L : A ⥤ B) (W : MorphismProperty A) [L.IsLocalization W]
    {F G : B ⥤ C} (α : L ⋙ F ≅ L ⋙ G) (X : A) :
    (unwhiskerLocalizationIso L W α).hom.app (L.obj X) = α.hom.app X :=
  congr_app ((Localization.fullyFaithfulWhiskeringLeft L W C).map_preimage α.hom) X

end LocalizationHelpers

section DerivedComparison

attribute [local instance] HasDerivedCategory.standard

open Specs.DerivedFormalization.Affine.CotangentComplex (oneObject)
open Specs.DerivedFormalization.DG.Derived (HomotopyCategoryLaws)
open Specs.DerivedFormalization.DG.DerivedKProjective
  (derivedCategoryInstance restrictedLocalization kProjectiveObjects)
open Specs.DerivedFormalization.DG.KProjective (isKProjective)
open Specs.DerivedFormalization.DerivedHomModels (Models Representative rHomValue modelMap)
open Specs.DerivedFormalization.Affine.DerivedHom (Kp)

variable {E : StrictComparison.{u,v,t} k R} (I : StrictHom E)
variable (h : HomotopyCategoryLaws (oneObject (transported.{u,v,t} k R)))

variable [hh : Fact (HomotopyCategoryLaws (oneObject (transported.{u,v,t} k R)))]

local instance : Category (dgHomotopy.{u,v,t} k R) :=
  Specs.DerivedFormalization.DG.Derived.homotopyCategory _ hh.out
local instance : Category (dgDerived.{u,v,t} k R h) := derivedCategoryInstance _ h

variable (K : homotopyValue.{max v t} R ⥤ dgHomotopy.{u,v,t} k R)
variable (a : ∀ X : compValue.{max v t} R, K.obj ((quotientValue R).obj X) ≅
  (E.strict.functor.obj X : dgHomotopy.{u,v,t} k R))

private def strictHomotopyFunctor : homotopyValue.{max v t} R ⥤ dgHomotopy.{u,v,t} k R :=
  conjugateFunctor K (fun V => E.strict.functor.obj V.as) (fun V => a V.as)

private def strictHomotopyFunctorIso : K ≅ strictHomotopyFunctor K a :=
  conjugateFunctorIso K _ (fun V => a V.as)

variable (ha : ∀ {X Y : compValue.{max v t} R} (f : X ⟶ Y),
  K.map ((quotientValue R).map f) ≫ (a Y).hom =
    (a X).hom ≫ homotopyClass (E.strict.functor.map f))

include ha in
private theorem strictHomotopyFunctor_map {X Y : compValue.{max v t} R} (f : X ⟶ Y) :
    (strictHomotopyFunctor K a).map ((quotientValue R).map f) =
      homotopyClass (E.strict.functor.map f) := by
  change (a X).inv ≫ K.map ((quotientValue R).map f) ≫ (a Y).hom = _
  rw [ha f, Iso.inv_hom_id_assoc]

variable (D : derivedValue.{max v t} R ⥤ dgDerived.{u,v,t} k R h)

private abbrev quotientStrictIso (τ : qhValue R ⋙ D ≅ K ⋙ (Specs.DerivedFormalization.DG.AmbientDerived.quotient.{u,v,0,t} (oneObject (ordinary k R)) h)) :
    qhValue R ⋙ D ≅ strictHomotopyFunctor K a ⋙ (Specs.DerivedFormalization.DG.AmbientDerived.quotient.{u,v,0,t} (oneObject (ordinary k R)) h) :=
  τ ≪≫ Functor.isoWhiskerRight (strictHomotopyFunctorIso K a) (Specs.DerivedFormalization.DG.AmbientDerived.quotient.{u,v,0,t} (oneObject (ordinary k R)) h)

variable (O : Models.{v,max v t} R)
variable (S : HomActions (transported.{u,v,t} k R).toCommDGAlgebra)
variable (H : (dgHomotopy.{u,v,t} k R)ᵒᵖ × dgHomotopy.{u,v,t} k R ⥤ dgHomotopy.{u,v,t} k R)
variable (hS : HomActionLaws (transported.{u,v,t} k R).toCommDGAlgebra S)
variable (objH : ∀ (X Y : (transported.{u,v,t} k R).Module),
  H.obj (op X, Y) = DerivedHom.internalHom X Y)
variable (mapH : ∀ {X X' Y Y' : (transported.{u,v,t} k R).Module}
    (f : X' ⟶ X) (g : Y ⟶ Y'),
    let f₀ : @Quiver.Hom (dgHomotopy.{u,v,t} k R)
      (Specs.DerivedFormalization.DG.Derived.homotopyCategory _ h).toQuiver X' X :=
      homotopyClass f
    let g₀ : @Quiver.Hom (dgHomotopy.{u,v,t} k R)
      (Specs.DerivedFormalization.DG.Derived.homotopyCategory _ h).toQuiver Y Y' :=
      homotopyClass g
    HEq (H.map (Prod.mkHom f₀.op g₀)) (homotopyClass (S.pre Y f ≫ S.post X' g)))

include I ha hS objH mapH in
set_option maxHeartbeats 1000000 in
private def strictHomotopyHomIso
    (ρ : qhValue R ⋙ D ≅ strictHomotopyFunctor K a ⋙ (Specs.DerivedFormalization.DG.AmbientDerived.quotient.{u,v,0,t} (oneObject (ordinary k R)) h)) :
    O.hom.functor ⋙ D ≅
      (strictHomotopyFunctor K a).op.prod (strictHomotopyFunctor K a) ⋙ H ⋙ (Specs.DerivedFormalization.DG.AmbientDerived.quotient.{u,v,0,t} (oneObject (ordinary k R)) h) := by
  let U := strictHomotopyFunctor K a
  let Q : dgHomotopy.{u,v,t} k R ⥤ dgDerived.{u,v,t} k R h :=
    Specs.DerivedFormalization.DG.AmbientDerived.quotient.{u,v,0,t} (oneObject (ordinary k R)) h
  let L : (transported.{u,v,t} k R).Module ⥤ dgHomotopy.{u,v,t} k R :=
    RightDGModule.toHomotopyCategory (oneObject (transported.{u,v,t} k R))
  let obj (X Y : homotopyValue.{max v t} R) := eqToIso (objH (U.obj X) (U.obj Y))
  let β (X Y : homotopyValue.{max v t} R) :=
    D.mapIso (eqToIso (O.hom.obj_eq X Y)) ≪≫
      ρ.app ((quotientValue R).obj (internalHomValue X.as Y.as)) ≪≫
      Q.mapIso (L.mapIso (I.iso X.as Y.as)) ≪≫ (Q.mapIso (obj X Y)).symm
  refine NatIso.ofComponents (fun Z => β Z.1.unop Z.2) ?_
  rintro ⟨⟨X⟩, Y⟩ ⟨⟨X'⟩, Y'⟩ f
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨X', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨Y, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  obtain ⟨Y', rfl⟩ := HomotopyCategory.quotient_obj_surjective Y'
  let q := quotientValue.{max v t} R
  letI : q.Full := inferInstanceAs (HomotopyCategory.quotient _ _).Full
  obtain ⟨f₁, hf₁⟩ := q.map_surjective f.1.unop
  obtain ⟨f₂, hf₂⟩ := q.map_surjective f.2
  have hf : f = Prod.mkHom (q.map f₁).op (q.map f₂) :=
    Prod.ext (congrArg Quiver.Hom.op hf₁).symm hf₂.symm
  subst f
  have hmap : H.map (Prod.mkHom (U.map (q.map f₁)).op (U.map (q.map f₂))) =
      (obj (q.obj X) (q.obj Y)).hom ≫
        L.map (S.pre (E.strict.functor.obj Y) (E.strict.functor.map f₁) ≫
          S.post (E.strict.functor.obj X') (E.strict.functor.map f₂)) ≫
        (obj (q.obj X') (q.obj Y')).inv := by
    rw [strictHomotopyFunctor_map K a ha, strictHomotopyFunctor_map K a ha]
    exact (conj_eqToHom_iff_heq _ _ (objH _ _) (objH _ _)).2
      (mapH (E.strict.functor.map f₁) (E.strict.functor.map f₂))
  have hr := ρ.hom.naturality (q.map (internalHomMapValue f₁ f₂))
  have hn := congrArg (fun f => Q.map (L.map f)) (I.naturality S hS f₁ f₂)
  change D.map (O.hom.functor.map (Prod.mkHom (q.map f₁).op (q.map f₂))) ≫
      (β (q.obj X') (q.obj Y')).hom =
      (β (q.obj X) (q.obj Y)).hom ≫
        Q.map (H.map (Prod.mkHom (U.map (q.map f₁)).op (U.map (q.map f₂))))
  rw [O.hom.map_eq f₁ f₂, hmap]
  simp only [β, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc, eqToIso.hom, Iso.app_hom] at ⊢ hn
  rw [← D.map_comp_assoc (eqToHom (O.hom.obj_eq (q.obj X') (q.obj Y')).symm)
    (eqToHom (O.hom.obj_eq (q.obj X') (q.obj Y'))), eqToHom_trans, eqToHom_refl,
    D.map_id, Category.id_comp]
  rw [← Q.map_comp_assoc (obj (q.obj X) (q.obj Y)).inv (obj (q.obj X) (q.obj Y)).hom,
    Iso.inv_hom_id, Q.map_id, Category.id_comp]
  change D.map ((qValue R).map (internalHomMapValue f₁ f₂)) ≫
    ρ.hom.app (q.obj (internalHomValue X' Y')) =
    ρ.hom.app (q.obj (internalHomValue X Y)) ≫
      Q.map (U.map (q.map (internalHomMapValue f₁ f₂))) at hr
  have hu : U.map (q.map (internalHomMapValue f₁ f₂)) =
      L.map (E.strict.functor.map (internalHomMapValue f₁ f₂)) :=
    strictHomotopyFunctor_map K a ha _
  change D.map (eqToHom (O.hom.obj_eq (q.obj X) (q.obj Y))) ≫
      D.map ((qValue R).map (internalHomMapValue f₁ f₂)) ≫
        ρ.hom.app (q.obj (internalHomValue X' Y')) ≫
        Q.map (L.map (I.iso X' Y').hom) ≫ Q.map (obj (q.obj X') (q.obj Y')).inv =
    D.map (eqToHom (O.hom.obj_eq (q.obj X) (q.obj Y))) ≫
      ρ.hom.app (q.obj (internalHomValue X Y)) ≫ Q.map (L.map (I.iso X Y).hom) ≫
      Q.map (L.map (S.pre (E.strict.functor.obj Y) (E.strict.functor.map f₁))) ≫
      Q.map (L.map (S.post (E.strict.functor.obj X') (E.strict.functor.map f₂))) ≫
      Q.map (obj (q.obj X') (q.obj Y')).inv
  rw [reassoc_of% hr, hu, reassoc_of% hn]

set_option maxHeartbeats 1600000 in
theorem localizedHomComparison : LocalizedHomComparison.{u,v,t} := by
  intro k _ _ R _ _ E I h
  dsimp only
  let G := oneObject (transported.{u,v,t} k R)
  letI : Fact (HomotopyCategoryLaws G) := ⟨h⟩
  letI := Specs.DerivedFormalization.DG.Derived.homotopyCategory G h
  letI := derivedCategoryInstance G h
  intro K D a τ ha projective O S H F hS objH mapH σ
  let Q := Specs.DerivedFormalization.DG.AmbientDerived.quotient.{u,v,0,t} (oneObject (ordinary k R)) h
  let Qp := restrictedLocalization G h
  let U := strictHomotopyFunctor K.functor a
  let j := (ordinaryProjectives.{v,t} R).ι
  let V := (kProjectiveObjects G).lift (j ⋙ U) (fun X => projective X.obj.as X.property)
  let ρ := quotientStrictIso h K.functor a D.functor τ
  let L := ordinaryLocalizedInputs.{v,t} R
  let W₁ := MorphismProperty.isomorphisms ((ordinaryProjectives.{v,t} R).FullSubcategory)ᵒᵖ
  let W₂ := HomotopyCategory.quasiIso (ModuleCat.{max v t} R) (.up ℤ)
  let W := W₁.prod W₂
  letI : (projectiveQuotient.{v,t} R).IsEquivalence := projectiveQuotient_isEquivalence O
  letI : (projectiveQuotient.{v,t} R).op.IsLocalization W₁ :=
    Functor.IsLocalization.of_isEquivalence _ _ le_rfl
  letI : (qhValue.{max v t} R).IsLocalization W₂ :=
    (inferInstance : (DerivedCategory.Qh (C := ModuleCat.{max v t} R)).IsLocalization
      (HomotopyCategory.quasiIso (ModuleCat.{max v t} R) (.up ℤ)))
  letI : L.IsLocalization W :=
    Functor.IsLocalization.prod _ W₁ _ W₂
  let input : L ⋙ D.functor.op.prod D.functor ≅
      (V.op.prod U) ⋙ Qp.op.prod Q := NatIso.ofComponents
    (fun Z => ((ρ.app Z.1.unop.obj).symm.op).prod (ρ.app Z.2))
    (by
      intro Z Z' f
      exact Prod.ext
        (congrArg Quiver.Hom.op ((ρ.inv.naturality (j.map f.1.unop)).symm))
        (ρ.hom.naturality f.2))
  let dgFactor : L ⋙ (D.functor.op.prod D.functor ⋙ F) ≅
      (j.op.prod (𝟭 _)) ⋙ U.op.prod U ⋙ H ⋙ Q :=
    Functor.isoWhiskerRight input F ≪≫ Functor.isoWhiskerLeft (V.op.prod U) σ
  let C := strictHomotopyHomIso (I := I) (h := h) (K := K.functor) (a := a)
    (ha := ha) (D := D.functor) (O := O) (S := S) (H := H) (hS := hS)
    (objH := objH) (mapH := mapH) ρ
  let localizedModels : L ⋙ (rHomValue O ⋙ D.functor) ≅
      L ⋙ (D.functor.op.prod D.functor ⋙ F) :=
    (Functor.isoWhiskerRight (ordinaryFactorization O) D.functor).symm ≪≫
      Functor.isoWhiskerLeft (j.op.prod (𝟭 _)) C ≪≫ dgFactor.symm
  refine ⟨unwhiskerLocalizationIso L W localizedModels, ?_⟩
  intro X Y hX
  let Z : ((ordinaryProjectives.{v,t} R).FullSubcategory)ᵒᵖ × homotopyValue.{max v t} R :=
    (op ⟨(quotientValue R).obj X, hX⟩, (quotientValue R).obj Y)
  change _ ≫ (unwhiskerLocalizationIso L W localizedModels).hom.app (L.obj Z) ≫ _ = _
  rw [unwhiskerLocalizationIso_app L W localizedModels Z]
  -- Evaluate both model factorizations on these representatives.
  let P₁ := D.functor.mapIso ((ordinaryFactorization O).app Z)
  let O₁ := D.functor.mapIso (eqToIso (O.hom.obj_eq ((quotientValue R).obj X)
    ((quotientValue R).obj Y)))
  let T₁ := F.mapIso (input.app Z)
  let D₁ := σ.app ((V.op.prod U).obj Z)
  let R₁ := Q.mapIso (eqToIso (objH (E.strict.functor.obj X) (E.strict.functor.obj Y)))
  let r := (ρ.app ((quotientValue R).obj (internalHomValue X Y))).hom
  let i := Q.map (homotopyClass (I.iso X Y).hom)
  rw [D.functor.map_comp]
  change (O₁.inv ≫ P₁.hom) ≫
      (P₁.inv ≫ (O₁.hom ≫ r ≫ i ≫ R₁.inv) ≫ (D₁.inv ≫ T₁.inv)) ≫
      T₁.hom ≫ D₁.hom ≫ R₁.hom = r ≫ i
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]

end DerivedComparison

end

end DerivedFormalization.Affine.OrdinaryDGHomComparison
