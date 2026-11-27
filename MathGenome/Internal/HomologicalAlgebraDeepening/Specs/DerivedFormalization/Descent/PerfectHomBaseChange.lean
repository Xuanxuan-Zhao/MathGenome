import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainModels
import Mathlib.LinearAlgebra.TensorProduct.Lift
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Finiteness.Projective

open CategoryTheory CochainComplex CochainComplex.HomComplex
open scoped TensorProduct

set_option linter.checkUnivs false

universe u v w
namespace Specs.DerivedFormalization.Descent.PerfectHomBaseChange

variable (A : Type u) (S : Type v) [CommRing A] [CommRing S] [Algebra A S]

abbrev Complex (R : Type u) [CommRing R] :=
  Specs.DerivedFormalization.Cochains.compValue.{w} R

abbrev HomComplex {R : Type u} [CommRing R] (P X : Complex.{u,w} R) :=
  Specs.DerivedFormalization.CochainModels.internalHomValue P X

/-- Ordinary extension of scalars, with the extending ring on the left. -/
def scalarExtension : ModuleCat.{w} A ⥤ ModuleCat.{max v w} S where
  obj M := ModuleCat.of S (S ⊗[A] M)
  map f := ModuleCat.ofHom (f.hom.baseChange S)
  map_id _ := ModuleCat.hom_ext (LinearMap.baseChange_id (A := S))
  map_comp _ _ := ModuleCat.hom_ext (LinearMap.baseChange_comp (A := S) _ _)

instance scalarExtension_additive : (scalarExtension.{u,v,w} A S).Additive where
  map_add := fun {_ _} f g => ModuleCat.hom_ext (LinearMap.baseChange_add (A := S) f.hom g.hom)

abbrev extend := (scalarExtension.{u,v,w} A S).mapHomologicalComplex (ComplexShape.up ℤ)

@[simp] theorem extend_map_tmul {X Y : Complex.{u,w} A} (f : X ⟶ Y)
    (i : ℤ) (s : S) (x : X.X i) :
    ((extend A S).map f).f i (s ⊗ₜ[A] x) = s ⊗ₜ[A] f.f i x :=
  rfl

variable {A} {P X : Complex.{u,w} A}

local instance cochainModule (n : ℤ) :
    Module A (Cochain ((extend A S).obj P) ((extend A S).obj X) n) :=
  Module.restrictScalars A S _

local instance cochainTower (n : ℤ) :
    IsScalarTower A S (Cochain ((extend A S).obj P) ((extend A S).obj X) n) :=
  IsScalarTower.restrictScalars A S _

/-- Extend a homogeneous family of maps before taking its `S`-linear span. -/
def extendCochain (n : ℤ) :
    Cochain P X n →ₗ[A] Cochain ((extend A S).obj P) ((extend A S).obj X) n where
  toFun f := f.map (scalarExtension A S)
  map_add' f g := f.map_add g _
  map_smul' r f := by
    change (r • f).map (scalarExtension A S) =
      algebraMap A S r • f.map (scalarExtension A S)
    apply Cochain.ext
    intro i j hij
    simp only [Cochain.map_v, Cochain.smul_v]
    apply ModuleCat.hom_ext
    change (r • (f.v i j hij).hom).baseChange S = algebraMap A S r • (f.v i j hij).hom.baseChange S
    exact (LinearMap.baseChange_smul (A := S) r _).trans (algebraMap_smul S r _).symm

/-- The ordinary base change map on signed internal Hom complexes. -/
def comparison (P X : Complex.{u,w} A) :
    (extend A S).obj (HomComplex P X) ⟶
      HomComplex ((extend A S).obj P) ((extend A S).obj X) where
  f n := ModuleCat.ofHom ((extendCochain S n).liftBaseChange S)
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply (LinearMap.liftBaseChangeEquiv S
      (M := Cochain P X n)
      (N := Cochain ((extend A S).obj P) ((extend A S).obj X) m)).symm.injective
    apply LinearMap.ext
    intro f
    change δ n m (((extendCochain S n).liftBaseChange S) (1 ⊗ₜ[A] f)) =
      ((extendCochain S m).liftBaseChange S) (1 ⊗ₜ[A] δ n m f)
    simp only [LinearMap.liftBaseChange_one_tmul]
    exact δ_map _ _ _ _

def comparisonType :=
  ∀ (A : Type u) (S : Type v) [CommRing A] [CommRing S] [Algebra A S]
    (P X : Complex.{u,w} A),
    (extend A S).obj (HomComplex P X) ⟶
      HomComplex ((extend A S).obj P) ((extend A S).obj X)

abbrev comparisonValue (A : Type u) (S : Type v) [CommRing A] [CommRing S] [Algebra A S]
    (P X : Complex.{u,w} A) := comparison S P X

def comparison_applyType : Prop :=
  ∀ (A : Type u) (S : Type v) [CommRing A] [CommRing S] [Algebra A S]
    (P X : Complex.{u,w} A) (n i j : ℤ) (hij : i + n = j)
    (s t : S) (f : Cochain P X n) (p : P.X i),
    ((comparison S P X).f n (s ⊗ₜ[A] f)).v i j hij (t ⊗ₜ[A] p) =
      (s * t) ⊗ₜ[A] f.v i j hij p

def comparison_isIsoType : Prop :=
  ∀ (A : Type u) (S : Type v) [CommRing A] [CommRing S] [Algebra A S]
    (P X : Complex.{u,w} A),
    (∃ L U : ℤ, ∀ i : ℤ, (i < L ∨ U < i) → Subsingleton (P.X i)) →
    (∀ i : ℤ, Module.Finite A (P.X i)) →
    (∀ i : ℤ, Module.Projective A (P.X i)) →
    IsIso (comparison S P X)

def comparison_naturalType : Prop :=
  ∀ (A : Type u) (S : Type v) [CommRing A] [CommRing S] [Algebra A S]
    {P P' X X' : Complex.{u,w} A} (g : P' ⟶ P) (h : X ⟶ X'),
    (extend A S).map (Specs.DerivedFormalization.CochainModels.internalHomMapValue g h) ≫
        comparison S P' X' =
      comparison S P X ≫ Specs.DerivedFormalization.CochainModels.internalHomMapValue
        ((extend A S).map g) ((extend A S).map h)

section Unit

variable (A : Type u) [CommRing A]

/-- The unit identification for ordinary scalar extension. -/
def extendId (X : Complex.{u,max u w} A) : (extend A A).obj X ≅ X :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (TensorProduct.lid A (X.X i)).toModuleIso) <| by
      intro i j _
      apply ModuleCat.hom_ext
      apply TensorProduct.AlgebraTensorModule.ext
      intro a x
      change X.d i j (a • x) = a • X.d i j x
      exact (X.d i j).hom.map_smul a x

@[simp] theorem extendId_hom_tmul (X : Complex.{u,max u w} A)
    (i : ℤ) (a : A) (x : X.X i) :
    (extendId A X).hom.f i (a ⊗ₜ[A] x) = a • x :=
  rfl

@[simp] theorem extendId_inv_apply (X : Complex.{u,max u w} A) (i : ℤ) (x : X.X i) :
    (extendId A X).inv.f i x = 1 ⊗ₜ[A] x :=
  rfl

def comparison_unitType : Prop :=
  ∀ (A : Type u) [CommRing A] (P X : Complex.{u,max u w} A),
    comparison A P X ≫
        Specs.DerivedFormalization.CochainModels.internalHomMapValue
          (extendId A P).inv (extendId A X).hom =
      (extendId A (HomComplex P X)).hom

end Unit

section Tower

variable (A : Type u) (S T : Type v) [CommRing A] [CommRing S] [CommRing T]
  [Algebra A S] [Algebra A T] [Algebra S T] [IsScalarTower A S T]

/-- The iterated scalar extension is identified with the direct extension by
\(t \otimes (s \otimes x) \mapsto (s \cdot t) \otimes x\). -/
def extendComp (X : Complex.{u,w} A) :
    (extend S T).obj ((extend A S).obj X) ≅ (extend A T).obj X :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (TensorProduct.AlgebraTensorModule.cancelBaseChange A S T T (X.X i)).toModuleIso)
    (by
      intro i j _
      apply ModuleCat.hom_ext
      let e (k : ℤ) := TensorProduct.AlgebraTensorModule.cancelBaseChange A S T T (X.X k)
      let d := (X.d i j).hom
      change (d.baseChange T).comp (e i).toLinearMap =
        (e j).toLinearMap.comp ((d.baseChange S).baseChange T)
      rw [LinearMap.baseChange_baseChange]
      apply TensorProduct.AlgebraTensorModule.ext
      intro t z
      simp [e, LinearMap.comp_apply])

@[simp] theorem extendComp_hom_tmul (X : Complex.{u,w} A) (i : ℤ) (t : T) (s : S)
    (x : X.X i) :
    (extendComp A S T X).hom.f i (t ⊗ₜ[S] (s ⊗ₜ[A] x)) = (s • t) ⊗ₜ[A] x :=
  rfl

@[simp] theorem extendComp_inv_tmul (X : Complex.{u,w} A) (i : ℤ) (t : T) (x : X.X i) :
    (extendComp A S T X).inv.f i (t ⊗ₜ[A] x) = t ⊗ₜ[S] (1 ⊗ₜ[A] x) :=
  rfl

def comparison_towerType : Prop :=
  ∀ (A : Type u) (S T : Type v) [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] [Algebra S T] [IsScalarTower A S T]
    (P X : Complex.{u,w} A),
    (extend S T).map (comparison S P X) ≫
        comparison T ((extend A S).obj P) ((extend A S).obj X) ≫
        Specs.DerivedFormalization.CochainModels.internalHomMapValue
          (extendComp A S T P).inv (extendComp A S T X).hom =
      (extendComp A S T (HomComplex P X)).hom ≫ comparison T P X

/-- Restrict a cochain complex along the structure map of an algebra. -/
noncomputable abbrev restrict (R : Type u) (V : Type v) [CommRing R] [CommRing V] [Algebra R V] :=
  (ModuleCat.restrictScalars.{max v w} (algebraMap R V)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The unit of scalar extension from `S` to `T`, viewed over `A`. -/
noncomputable def extensionUnit (Y : Complex.{v,max v w} S) :
    (restrict A S).obj Y ⟶ (restrict A T).obj ((extend S T).obj Y) where
  f i := ModuleCat.ofHom (X := ((restrict A S).obj Y).X i)
    (Y := ((restrict A T).obj ((extend S T).obj Y)).X i)
    { toFun := fun y => (1 : T) ⊗ₜ[S] y
      map_add' := fun y z => TensorProduct.tmul_add _ _ _
      map_smul' := fun a y => by
        let z : Y.X i := y
        change (1 : T) ⊗ₜ[S] (algebraMap A S a • z) =
          algebraMap A T a • ((1 : T) ⊗ₜ[S] z)
        rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', IsScalarTower.algebraMap_apply A S T]
        simp [Algebra.smul_def] }
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    rfl

/-- On a base-extended complex, change the coefficient of each tensor along `S → T`. -/
noncomputable def changeCoefficients (X : Complex.{u,w} A) :
    (restrict A S).obj ((extend A S).obj X) ⟶ (restrict A T).obj ((extend A T).obj X) :=
  extensionUnit A S T ((extend A S).obj X) ≫
    (restrict A T).map (extendComp A S T X).hom

/-- On an internal Hom complex, extend each homogeneous map and transport its
source and target along the iterated-extension identifications. -/
noncomputable def changeHomCoefficients (P X : Complex.{u,w} A) :
    (restrict A S).obj (HomComplex ((extend A S).obj P) ((extend A S).obj X)) ⟶
      (restrict A T).obj (HomComplex ((extend A T).obj P) ((extend A T).obj X)) :=
  extensionUnit A S T (HomComplex ((extend A S).obj P) ((extend A S).obj X)) ≫
    (restrict A T).map (comparison T ((extend A S).obj P) ((extend A S).obj X) ≫
      Specs.DerivedFormalization.CochainModels.internalHomMapValue
        (extendComp A S T P).inv (extendComp A S T X).hom)

def changeCoefficients_applyType : Prop :=
  ∀ (A : Type u) (S T : Type v) [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] (φ : S →ₐ[A] T)
    (X : Complex.{u,w} A) (i : ℤ) (s : S) (x : X.X i),
    letI : Algebra S T := φ.toRingHom.toAlgebra
    letI : IsScalarTower A S T := IsScalarTower.of_algHom φ
    (changeCoefficients A S T X).f i (s ⊗ₜ[A] x) = φ s ⊗ₜ[A] x

def changeHomCoefficients_applyType : Prop :=
  ∀ (A : Type u) (S T : Type v) [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] (φ : S →ₐ[A] T)
    (P X : Complex.{u,w} A) (n i j : ℤ) (hij : i + n = j)
    (f : Cochain ((extend A S).obj P) ((extend A S).obj X) n)
    (z : ((extend A S).obj P).X i),
    letI : Algebra S T := φ.toRingHom.toAlgebra
    letI : IsScalarTower A S T := IsScalarTower.of_algHom φ
    let g : Cochain ((extend A T).obj P) ((extend A T).obj X) n :=
      (changeHomCoefficients A S T P X).f n f
    g.v i j hij ((changeCoefficients A S T P).f i z) =
      (changeCoefficients A S T X).f j (f.v i j hij z)

def comparison_changeCoefficientsType : Prop :=
  ∀ (A : Type u) (S T : Type v) [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] (φ : S →ₐ[A] T) (P X : Complex.{u,w} A),
    letI : Algebra S T := φ.toRingHom.toAlgebra
    letI : IsScalarTower A S T := IsScalarTower.of_algHom φ
    changeCoefficients A S T (HomComplex P X) ≫ (restrict A T).map (comparison T P X) =
      (restrict A S).map (comparison S P X) ≫ changeHomCoefficients A S T P X

end Tower

end Specs.DerivedFormalization.Descent.PerfectHomBaseChange
