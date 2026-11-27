import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.PerfectHomBaseChange
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.UnboundedAmitsurDescent
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedHomModels
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! Perfect-coefficient mapping descent using ordinary signed Hom models. -/

namespace Specs.DerivedFormalization.Descent.PerfectMappingDescent

open CategoryTheory Opposite
open Cochains (compValue derivedValue qValue)
open CochainModels (internalHomValue internalHomMapValue)
open CochainCoefficientLift (lift liftD)
open DerivedHomModels (Models rHomValue)
open PerfectHomBaseChange (extend restrict changeHomCoefficients comparison)
open AmitsurAlgebrasSpec (degree coface)
open AmitsurTotalComplexSpec (rowIndex)
open scoped BigOperators TensorProduct

universe u v w t a
set_option linter.checkUnivs false

noncomputable section

variable (A : Type u) [CommRing A]

/-- The full subcategory of bounded complexes of finite projectives. -/
def perfect : ObjectProperty (compValue.{w} A) := fun P =>
  (∃ L U : ℤ, ∀ i : ℤ, (i < L ∨ U < i) → Subsingleton (P.X i)) ∧
    (∀ i : ℤ, Module.Finite A (P.X i)) ∧ (∀ i : ℤ, Module.Projective A (P.X i))

abbrev Inputs := (perfect.{u,w} A).FullSubcategoryᵒᵖ × compValue.{t} A

variable (B : Type v) [CommRing B] [Algebra A B]

abbrev firstLift :
    (perfect.{u,w} A).FullSubcategory ⥤ compValue.{max u v w t} A :=
  (perfect A).ι ⋙ lift.{max u v t,w} A

abbrev secondLift : compValue.{t} A ⥤ compValue.{max u v w t} A :=
  lift.{max u v w,t} A

variable (I : Inputs.{u,w,t} A)

abbrev P : compValue.{max u v w t} A := (firstLift.{u,v,w,t} A).obj I.1.unop
abbrev X : compValue.{max u v w t} A := (secondLift.{u,v,w,t} A).obj I.2

abbrev globalHom : compValue.{max u v w t} A :=
  internalHomValue (P.{u,v,w,t} A I) (X.{u,v,w,t} A I)

abbrev localP (p : ℕ) :=
  (extend A (degree A B p)).obj (P.{u,v,w,t} A I)

abbrev localX (p : ℕ) :=
  (extend A (degree A B p)).obj (X.{u,v,w,t} A I)

abbrev localHom (p : ℕ) := internalHomValue (localP A B I p) (localX A B I p)

abbrev column (p : ℕ) : compValue.{max u v w t} A :=
  (restrict.{u,max u v,max w t} A (degree A B p)).obj (localHom A B I p)

/-- A coface extends each homogeneous map, using the iterated-extension
identifications for its source and target. -/
def localCoface {p : ℕ} (i : Fin (p + 2)) : column A B I p ⟶ column A B I (p + 1) :=
  let φ := coface (A := A) (B := B) i
  letI : Algebra (degree A B p) (degree A B (p + 1)) := φ.toRingHom.toAlgebra
  letI : IsScalarTower A (degree A B p) (degree A B (p + 1)) := IsScalarTower.of_algHom φ
  changeHomCoefficients A (degree A B p) (degree A B (p + 1))
    (P.{u,v,w,t} A I) (X.{u,v,w,t} A I)

/-- Use products of the actual restricted Hom terms on every diagonal. -/
abbrev totalTerm (n : ℤ) : ModuleCat.{max u v w t} A :=
  ModuleCat.of A (∀ p : ℕ, (column A B I p).X (rowIndex n p))

def diagonalHorizontal (n : ℤ) (p : ℕ) :
    (column A B I p).X (rowIndex n p) ⟶ (column A B I (p + 1)).X (rowIndex (n + 1) (p + 1)) :=
  (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (localCoface A B I i).f (rowIndex n p)) ≫
    eqToHom (congrArg ((column A B I (p + 1)).X) (by
      change rowIndex n p = (n + 1) - (p + 1 : ℕ)
      rw [AmitsurTotalComplexSpec.rowIndex_eq]
      omega : rowIndex n p = rowIndex (n + 1) (p + 1)))

/-- The alternating horizontal differential plus the column-signed vertical one. -/
def totalStep (n : ℤ) : totalTerm A B I n ⟶ totalTerm A B I (n + 1) :=
  ModuleCat.ofHom (LinearMap.pi fun p => match p with
    | 0 => ((column A B I 0).d n (n + 1)).hom.comp (LinearMap.proj 0)
    | p + 1 =>
      (diagonalHorizontal A B I n p).hom.comp (LinearMap.proj p) +
        (-1 : ℤ) ^ (p + 1) •
          (((column A B I (p + 1)).d (rowIndex n (p + 1)) (rowIndex (n + 1) (p + 1))).hom.comp
            (LinearMap.proj (p + 1))))

abbrev localTotal (sq : ∀ n, totalStep A B I n ≫ totalStep A B I (n + 1) = 0) :
    compValue.{max u v w t} A :=
  CochainComplex.of (totalTerm A B I) (totalStep A B I) sq

variable {A I} {J : Inputs.{u,w,t} A}

def globalMap (f : I ⟶ J) : globalHom.{u,v,w,t} A I ⟶ globalHom.{u,v,w,t} A J :=
  internalHomMapValue ((firstLift.{u,v,w,t} A).map f.1.unop)
    ((secondLift.{u,v,w,t} A).map f.2)

def localMap (f : I ⟶ J) (p : ℕ) : localHom A B I p ⟶ localHom A B J p :=
  internalHomMapValue ((extend A (degree A B p)).map ((firstLift.{u,v,w,t} A).map f.1.unop))
    ((extend A (degree A B p)).map ((secondLift.{u,v,w,t} A).map f.2))

def totalComponent (f : I ⟶ J) (n : ℤ) : totalTerm A B I n ⟶ totalTerm A B J n :=
  ModuleCat.ofHom (LinearMap.pi fun p =>
    (((restrict.{u,max u v,max w t} A (degree A B p)).map (localMap B f p)).f (rowIndex n p)).hom.comp
      (LinearMap.proj p))

variable (A) (I)

/-- The derived input functor uses the localization of each original complex
followed by its same-ring coefficient lift. -/
def derivedInputs :
    Inputs.{u,w,t} A ⥤ (derivedValue.{max u v w t} A)ᵒᵖ × derivedValue.{max u v w t} A :=
  (((perfect A).ι ⋙ qValue.{w} A ⋙ liftD.{max u v t,w} A).op).prod
    (qValue.{t} A ⋙ liftD.{max u v w,t} A)

def localDerivedInputs (p : ℕ) :
    Inputs.{u,w,t} A ⥤
      (derivedValue.{max u v w t} (degree A B p))ᵒᵖ ×
        derivedValue.{max u v w t} (degree A B p) :=
  (((firstLift.{u,v,w,t} A ⋙ extend A (degree A B p)) ⋙ qValue (degree A B p)).op).prod
    ((secondLift.{u,v,w,t} A ⋙ extend A (degree A B p)) ⋙ qValue (degree A B p))

/-- A natural comparison in the original ring's derived category and natural
models for every local derived Hom. The comparison on the strict models uses
the Amitsur unit in column zero and vanishes in positive columns. -/
def descentType : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B]
    (M : Models.{u,max u v w t} A)
    (N : ∀ p : ℕ, Models.{max u v,max u v w t} (degree A B p)),
    ∃ (sq : ∀ (I : Inputs.{u,w,t} A) (n : ℤ),
          totalStep A B I n ≫ totalStep A B I (n + 1) = 0)
      (F : Inputs.{u,w,t} A ⥤ compValue.{max u v w t} A)
      (eF : ∀ I, F.obj I = localTotal A B I (sq I))
      (L : ∀ p : ℕ, Inputs.{u,w,t} A ⥤ compValue.{max u v w t} (degree A B p))
      (eL : ∀ p I, (L p).obj I = localHom A B I p)
      (G : Inputs.{u,w,t} A ⥤ compValue.{max u v w t} A)
      (eG : ∀ I, G.obj I = globalHom.{u,v,w,t} A I)
      (α : G ⟶ F)
      (g : G ⋙ qValue A ≅ derivedInputs.{u,v,w,t} A ⋙ rHomValue M)
      (_l : ∀ p, L p ⋙ qValue (degree A B p) ≅ localDerivedInputs A B p ⋙ rHomValue (N p))
      (e : derivedInputs.{u,v,w,t} A ⋙ rHomValue M ≅ F ⋙ qValue A),
      (∀ {I J} (f : I ⟶ J),
        G.map f = eqToHom (eG I) ≫ globalMap.{u,v,w,t} f ≫ eqToHom (eG J).symm) ∧
      (∀ p {I J} (f : I ⟶ J),
        (L p).map f = eqToHom (eL p I) ≫ localMap B f p ≫ eqToHom (eL p J).symm) ∧
      (∀ {I J} (f : I ⟶ J) (n : ℤ),
        (eqToHom (eF I).symm ≫ F.map f ≫ eqToHom (eF J)).f n = totalComponent B f n) ∧
      (∀ I (n : ℤ) (z : (globalHom.{u,v,w,t} A I).X n),
        let x := (eqToHom (eG I).symm ≫ α.app I ≫ eqToHom (eF I)).f n z
        x 0 = (comparison (degree A B 0) (P.{u,v,w,t} A I) (X.{u,v,w,t} A I)).f n
          (1 ⊗ₜ[A] z) ∧ ∀ p : ℕ, x (p + 1) = 0) ∧
      (∀ I, e.hom.app I = (g.app I).inv ≫ (qValue A).map (α.app I))

end

end Specs.DerivedFormalization.Descent.PerfectMappingDescent
