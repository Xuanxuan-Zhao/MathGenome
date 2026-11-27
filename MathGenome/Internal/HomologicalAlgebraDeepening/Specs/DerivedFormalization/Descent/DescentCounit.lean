import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.StrictModuleData
import Mathlib.RingTheory.Flat.Equalizer

/-! The invariant module and the flat descent counit. -/

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace DescentCounitSpec

open StrictModuleDataSpec TensorProduct

universe u v w

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]


/-- The vector (1\otimes x) in the pullback at position (i). -/
def generator {n : ℕ} (i : Fin n) {N : ModuleCat.{max u v w} B} (x : N) :
    (atPosition A B i).obj N :=
  (1 : Power A B n) ⊗ₜ[B, (factor A B i).toRingHom] x

theorem generator_add {n : ℕ} (i : Fin n) {N : ModuleCat.{max u v w} B} (x y : N) :
    generator (A := A) i (x + y) = generator i x + generator i y := by
  exact tmul_add _ _ _

theorem generator_zero {n : ℕ} (i : Fin n) (N : ModuleCat.{max u v w} B) :
    generator (A := A) i (0 : N) = 0 := by
  exact tmul_zero _ _

theorem generator_smul {n : ℕ} (i : Fin n) {N : ModuleCat.{max u v w} B} (b : B) (x : N) :
    generator (A := A) i (b • x) = factor A B i b • generator i x := by
  let D := (ModuleCat.restrictScalars (factor A B i).toRingHom).obj
    (ModuleCat.of (Power A B n) (Power A B n))
  change (show D from (1 : Power A B n)) ⊗ₜ[B] (b • x) = _
  rw [tmul_smul, smul_tmul']
  change (factor A B i b * 1) ⊗ₜ[B, (factor A B i).toRingHom] x = _
  exact rfl

/-- The A-submodule of invariant elements in a strict descent datum. -/
def invariants (X : Datum.{u, v, w} A B) : Submodule A (restrict A B X.module) where
  carrier := {x | X.theta.hom (generator.{u,v,w} (N := X.module) (0 : Fin 2) x) =
    generator.{u,v,w} (N := X.module) (1 : Fin 2) x}
  zero_mem' := by
    change X.theta.hom (generator.{u,v,w} (0 : Fin 2) (0 : X.module)) =
      generator.{u,v,w} (1 : Fin 2) (0 : X.module)
    simp [generator_zero]
  add_mem' {x y} hx hy := by
    change X.theta.hom (generator.{u,v,w} (N := X.module) (0 : Fin 2) (x + y)) =
      generator.{u,v,w} (N := X.module) (1 : Fin 2) (x + y)
    rw [generator_add.{u,v,w} (N := X.module) 0 x y,
      generator_add.{u,v,w} (N := X.module) 1 x y, map_add]
    exact congrArg₂ (· + ·) hx hy
  smul_mem' a x hx := by
    change X.theta.hom (generator.{u,v,w} (N := X.module) (0 : Fin 2) (algebraMap A B a • x)) =
      generator.{u,v,w} (N := X.module) (1 : Fin 2) (algebraMap A B a • x)
    rw [generator_smul.{u,v,w} (N := X.module) 0,
      generator_smul.{u,v,w} (N := X.module) 1, map_smul, AlgHom.commutes, AlgHom.commutes]
    exact congrArg ((algebraMap A (Power A B 2) a) • ·) hx

attribute [local instance] StrictModuleDataSpec.category

/-- Restrict a strict map to invariant elements. -/
def invariantsMap {X Y : Datum.{u, v, w} A B} (f : X ⟶ Y) :
    invariants X →ₗ[A] invariants Y :=
  ((ModuleCat.restrictScalars (algebraMap A B)).map f.hom).hom.restrict fun x hx ↦ by
    change Y.theta.hom (generator.{u,v,w} (0 : Fin 2) (f.hom x)) =
      generator.{u,v,w} (1 : Fin 2) (f.hom x)
    have h := congrArg (fun k ↦ k (generator.{u,v,w} (N := X.module) (0 : Fin 2) x)) f.comm
    change Y.theta.hom (generator.{u,v,w} (0 : Fin 2) (f.hom x)) =
      (atPosition A B (1 : Fin 2)).map f.hom (X.theta.hom (generator.{u,v,w} (N := X.module) (0 : Fin 2) x)) at h
    change X.theta.hom (generator.{u,v,w} (N := X.module) (0 : Fin 2) x) =
      generator.{u,v,w} (N := X.module) (1 : Fin 2) x at hx
    rw [h, hx]
    rfl

/-- The descended module, functorially in strict maps. -/
def descend : Datum.{u, v, w} A B ⥤ ModuleCat.{max u v w} A where
  obj X := ModuleCat.of A (invariants X)
  map f := ModuleCat.ofHom (invariantsMap f)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The two positions of a base-changed A-module identify with extension directly to the
ordered tensor algebra. -/
def baseChangePosition {n : ℕ} (i : Fin n) :
    ModuleCat.extendScalars.{u,max u v,max u v w} (algebraMap A (Power A B n)) ≅
    ModuleCat.extendScalars.{u,v,max u v w} (algebraMap A B) ⋙ atPosition.{u, v, w} A B i :=
  extendCongr (by ext a; exact ((factor A B i).commutes a).symm) ≪≫ extendComp _ _

/-- The canonical position comparison for (B\otimes_A M). -/
def baseChangeTheta (M : ModuleCat.{max u v w} A) : Theta A B ((ModuleCat.extendScalars.{u,v,max u v w} (algebraMap A B)).obj M) :=
  (baseChangePosition (0 : Fin 2)).symm.app M ≪≫ (baseChangePosition (1 : Fin 2)).app M

/-- The canonical multiplication map (B\otimes_A M \longrightarrow N) on the invariant
submodule (M) of a strict datum (N). -/
def counitMap (X : Datum.{u, v, w} A B) :
    (ModuleCat.extendScalars.{u,v,max u v w} (algebraMap A B)).obj ((descend (A := A) (B := B)).obj X) ⟶ X.module :=
  ((ModuleCat.extendRestrictScalarsAdj.{max u v w,u,v} (algebraMap A B)).homEquiv _ _).symm
    (ModuleCat.ofHom (Y := restrict A B X.module) (invariants X).subtype)

/-- The tensor-position comparison sends `(b ⊗ m) ⊗ c` to `b ⊗ (c ⊗ m)`. -/
def BaseChangeThetaTmul : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (M : ModuleCat.{max u v w} A) (b c : B) (x : M),
    (baseChangeTheta.{u,v,w} M).hom
      (factor A B (1 : Fin 2) c ⊗ₜ[B, (factor A B (0 : Fin 2)).toRingHom]
        (show (ModuleCat.extendScalars (algebraMap A B)).obj M from b ⊗ₜ[A, algebraMap A B] x)) =
    factor A B (0 : Fin 2) b ⊗ₜ[B, (factor A B (1 : Fin 2)).toRingHom]
      (show (ModuleCat.extendScalars (algebraMap A B)).obj M from c ⊗ₜ[A, algebraMap A B] x)

/-- The specified counit acts by scalar multiplication on every pure tensor. -/
def CounitMapTmul : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (X : Datum.{u,v,w} A B) (b : B) (x : invariants X),
    counitMap X (b ⊗ₜ[A, algebraMap A B] (show (descend (A := A) (B := B)).obj X from x)) =
      b • (show X.module from x.val)

def IsIsoCounit : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B],
    ∀ X : Datum.{u, v, w} A B, IsIso (counitMap X)

def CounitCompatible : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    ∀ X : Datum.{u, v, w} A B,
    (atPosition A B (0 : Fin 2)).map (counitMap X) ≫ X.theta.hom =
      (baseChangeTheta ((descend (A := A) (B := B)).obj X)).hom ≫
        (atPosition A B (1 : Fin 2)).map (counitMap X)

def CounitNatural : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    ∀ {X Y : Datum.{u, v, w} A B} (f : X ⟶ Y),
      (ModuleCat.extendScalars.{u,v,max u v w} (algebraMap A B)).map (descend.map f) ≫ counitMap Y =
        counitMap X ≫ f.hom

set_option linter.checkUnivs false in
private def declarationType {T : Sort*} (_ : T) := T

set_option linter.checkUnivs false in
def InvariantsType := declarationType (@invariants.{u, v, w})
set_option linter.checkUnivs false in
def DescendType := declarationType (@descend.{u, v, w})
set_option linter.checkUnivs false in
def BaseChangeThetaType := declarationType (@baseChangeTheta.{u, v, w})
set_option linter.checkUnivs false in
def CounitMapType := declarationType (@counitMap.{u, v, w})

end

end DescentCounitSpec
