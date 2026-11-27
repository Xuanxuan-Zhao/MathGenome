import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CotangentAmitsurModels
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.SquareZeroHomotopy
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.PerfectMappingDescent

open CategoryTheory
open scoped TensorProduct

namespace Specs.DerivedFormalization.Affine.TangentDescent

noncomputable section

universe u v w s t j
set_option linter.checkUnivs false
attribute [local instance] HasDerivedCategory.standard

open Cochains (compValue derivedValue qValue)
open CochainModels (internalHomValue internalHomMapValue)
open CotangentAmitsurModels (BP baseMap columnMap FiniteProjective)
open AmitsurAlgebrasSpec
open Descent.PerfectHomBaseChange (extend restrict changeCoefficients changeHomCoefficients extendCochain)
open CochainComplex.HomComplex (Cochain)

section Powers

variable (A : Type u) (B : Type v) (C : Type w)
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

abbrev BaseChange := B ⊗[A] C

/-- The first base-change ring at the level of all original rings. -/
abbrev coverRing := ULift.{max u j} (BaseChange A B C)
abbrev powerRing (p : ℕ) := degree B (coverRing.{u,v,w,j} A B C) p

variable {A B C}

abbrev onColumn {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1))
    (P X : compValue.{max u v w s t j} B) :=
  let φ : BP A B C p →ₐ[B] BP A B C q := columnMap f
  letI : Algebra (BP A B C p) (BP A B C q) := φ.toRingHom.toAlgebra
  letI : IsScalarTower B (BP A B C p) (BP A B C q) := IsScalarTower.of_algHom φ
  changeHomCoefficients.{v,max u v w,max u v w s t j} B (BP A B C p) (BP A B C q) P X

abbrev onPower {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1))
    (P X : compValue.{max u v w s t j} B) :=
  let φ : powerRing.{u,v,w,j} A B C p →ₐ[B] powerRing.{u,v,w,j} A B C q := map f
  letI : Algebra (powerRing.{u,v,w,j} A B C p) (powerRing.{u,v,w,j} A B C q) := φ.toRingHom.toAlgebra
  letI : IsScalarTower B (powerRing.{u,v,w,j} A B C p) (powerRing.{u,v,w,j} A B C q) := IsScalarTower.of_algHom φ
  changeHomCoefficients.{v,max u v w j,max u v w s t j} B (powerRing.{u,v,w,j} A B C p) (powerRing.{u,v,w,j} A B C q) P X

abbrev onExtension {p q : ℕ} (f : Fin (p+1) → Fin (q+1))
    (X : compValue.{max u v w s t j} B) :=
  let φ : BP A B C p →ₐ[B] BP A B C q := columnMap f
  letI : Algebra (BP A B C p) (BP A B C q) := φ.toRingHom.toAlgebra
  letI : IsScalarTower B (BP A B C p) (BP A B C q) := IsScalarTower.of_algHom φ
  changeCoefficients.{v,max u v w,max u v w s t j} B (BP A B C p) (BP A B C q) X

variable (A B C)

/-- The columns in the actual F08 product, identified with ordinary Hom
over the original tensor rings, including the cofaces and unit. -/
structure ColumnComparison where
  ring (p : ℕ) : BP A B C p ≃ₐ[B] powerRing.{u,v,w,j} A B C p
  ring_natural {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (z : BP A B C p) :
    ring q (columnMap (A := A) (B := B) (C := C) f z) = map f (ring p z)
  iso (p : ℕ) (P X : compValue.{max u v w s t j} B) (hP : FiniteProjective P) :
    (restrict.{v,max u v w,max u v w s t j} B (BP A B C p)).obj
        (internalHomValue ((extend.{v,max u v w,max u v w s t j} B (BP A B C p)).obj P) ((extend.{v,max u v w,max u v w s t j} B (BP A B C p)).obj X)) ≅
      (restrict.{v,max u v w j,max u v w s t j} B (powerRing.{u,v,w,j} A B C p)).obj
        (internalHomValue ((extend.{v,max u v w j,max u v w s t j} B (powerRing.{u,v,w,j} A B C p)).obj P) ((extend.{v,max u v w j,max u v w s t j} B (powerRing.{u,v,w,j} A B C p)).obj X))
  cofaces {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1))
      (P X : compValue.{max u v w s t j} B) (hP : FiniteProjective P) :
    onColumn.{u,v,w,s,t,j} (A := A) (C := C) f P X ≫ (iso q P X hP).hom =
      (iso p P X hP).hom ≫ onPower.{u,v,w,s,t,j} (A := A) (C := C) f P X
  unit (p : ℕ) (P X : compValue.{max u v w s t j} B) (hP : FiniteProjective P) (n : ℤ) (z : Cochain P X n) :
    (iso p P X hP).hom.f n (extendCochain (BP A B C p) n z) =
      extendCochain (powerRing.{u,v,w,j} A B C p) n z

def ColumnComparisonType : Prop :=
  ∀ (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Module.FaithfullyFlat A C],
    Nonempty (ColumnComparison.{u,v,w,s,t,j} A B C)

end Powers

section OriginalProduct

open Descent.PerfectMappingDescent (Inputs P X localTotal)
open AmitsurTotalComplexSpec (rowIndex)
open scoped BigOperators

variable (A : Type u) (B : Type v) (C : Type w)
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
variable (I : Inputs.{v,s,t} B)


/-- The column over the actual tensor ring (Bₚ), restricted to (B). -/
abbrev originalColumn (p : ℕ) : compValue.{max u v w s t j} B :=
  let G := extend.{v,max u v w,max u v w s t j} B (BP A B C p)
  (restrict.{v,max u v w,max u v w s t j} B (BP A B C p)).obj
    (internalHomValue (G.obj (P.{v,max u v w j,s,t} B I)) (G.obj (X.{v,max u v w j,s,t} B I)))

abbrev originalTotalTerm (n : ℤ) : ModuleCat.{max u v w s t j} B :=
  ModuleCat.of B (∀ p : ℕ, (originalColumn.{u,v,w,s,t,j} A B C I p).X (rowIndex n p))

theorem diagonalIndex (n : ℤ) (p : ℕ) :
    rowIndex n p = rowIndex (n + 1) (p + 1) := by
  rw [AmitsurTotalComplexSpec.rowIndex_eq, AmitsurTotalComplexSpec.rowIndex_eq]
  omega

def originalHorizontal (n : ℤ) (p : ℕ) :
    (originalColumn.{u,v,w,s,t,j} A B C I p).X (rowIndex n p) ⟶
      (originalColumn.{u,v,w,s,t,j} A B C I (p + 1)).X (rowIndex (n + 1) (p + 1)) :=
  (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
    (onColumn.{u,v,w,s,t,j} (A := A) (C := C) i.succAbove (P.{v,max u v w j,s,t} B I) (X.{v,max u v w j,s,t} B I)).f (rowIndex n p)) ≫
    eqToHom (congrArg (originalColumn.{u,v,w,s,t,j} A B C I (p + 1)).X (diagonalIndex n p))

/-- The product differential on the original columns, with the alternating
cofaces and the vertical sign depending on the column. -/
def originalTotalStep (n : ℤ) :
    originalTotalTerm.{u,v,w,s,t,j} A B C I n ⟶ originalTotalTerm.{u,v,w,s,t,j} A B C I (n + 1) :=
  ModuleCat.ofHom (LinearMap.pi fun p => match p with
    | 0 =>
      ((originalColumn.{u,v,w,s,t,j} A B C I 0).d n (n + 1)).hom.comp (LinearMap.proj 0)
    | p + 1 =>
      (originalHorizontal.{u,v,w,s,t,j} A B C I n p).hom.comp (LinearMap.proj p) +
        (-1 : ℤ) ^ (p + 1) •
          (((originalColumn.{u,v,w,s,t,j} A B C I (p + 1)).d
            (rowIndex n (p + 1)) (rowIndex (n + 1) (p + 1))).hom.comp (LinearMap.proj (p + 1))))

abbrev originalTotal
    (sq : ∀ n, originalTotalStep.{u,v,w,s,t,j} A B C I n ≫
      originalTotalStep.{u,v,w,s,t,j} A B C I (n + 1) = 0) :
    compValue.{max u v w s t j} B :=
  CochainComplex.of (originalTotalTerm.{u,v,w,s,t,j} A B C I)
    (originalTotalStep.{u,v,w,s,t,j} A B C I) sq

/-- Identify the whole product, coordinatewise, with the F08 totalization. -/
structure ProductComparison
    (E : ColumnComparison.{u,v,w,s,t,j} A B C) (hP : FiniteProjective (P.{v,max u v w j,s,t} B I))
    (sq : ∀ n, Descent.PerfectMappingDescent.totalStep B (coverRing.{u,v,w,j} A B C) I n ≫
        Descent.PerfectMappingDescent.totalStep B (coverRing.{u,v,w,j} A B C) I (n + 1) = 0) where
  sqOriginal (n : ℤ) :
    originalTotalStep.{u,v,w,s,t,j} A B C I n ≫ originalTotalStep.{u,v,w,s,t,j} A B C I (n + 1) = 0
  iso : originalTotal.{u,v,w,s,t,j} A B C I sqOriginal ≅ localTotal B (coverRing.{u,v,w,j} A B C) I sq
  coordinates (n : ℤ) (x : originalTotalTerm.{u,v,w,s,t,j} A B C I n) (p : ℕ) :
    iso.hom.f n x p = (E.iso p (P.{v,max u v w j,s,t} B I) (X.{v,max u v w j,s,t} B I) hP).hom.f (rowIndex n p) (x p)

end OriginalProduct

section Descent
open Opposite
open Descent.PerfectMappingDescent
open DerivedHomModels (Models rHomValue)
open Descent.PerfectHomBaseChange (comparison)

variable {B : Type v} [CommRing B]

abbrev homInTarget {K : Type*} [Category K] (P : compValue.{t} B) (V : K ⥤ compValue.{t} B) (J : (compValue.{t} B)ᵒᵖ × compValue.{t} B ⥤ compValue.{t} B) :=
  ((Functor.const K).obj (op P)).prod' V ⋙ J

abbrev derivedHomInTarget {K : Type*} [Category K] (L : derivedValue.{t} B)
    (V : K ⥤ compValue.{t} B) (H : Models.{v,t} B) :=
  ((Functor.const K).obj (op L)).prod' (V ⋙ qValue B) ⋙ rHomValue H

variable (A : Type u) (B : Type v) (C : Type w)
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

abbrev input (P₀ : (perfect.{v,s} B).FullSubcategory) :
    compValue.{t} B ⥤ Inputs.{v,s,t} B :=
  ((Functor.const _).obj (op P₀)).prod' (𝟭 _)

abbrev perfectLift (_A : Type u) (B : Type v) [CommRing B] (_C : Type w) (P₀ : (perfect.{v,s} B).FullSubcategory) :=
  (firstLift.{v,max u v w j,s,t} B).obj P₀

abbrev targetLift (_A : Type u) (B : Type v) [CommRing B] (_C : Type w) : compValue.{t} B ⥤ compValue.{max u v w s t j} B :=
  secondLift.{v,max u v w j,s,t} B

abbrev localTarget (p : ℕ) :=
  targetLift.{u,v,w,s,t,j} A B C ⋙ extend.{v,max u v w,max u v w s t j} B (BP A B C p)

/-- The descent comparison uses a specified derived identification with a
cotangent representative; its scalar extensions are induced by one strict map. -/
structure DescentData [Module.FaithfullyFlat A C]
    (P₀ : (perfect.{v,s} B).FullSubcategory)
    (L : compValue.{max u v w s t j} B)
    (α : (qValue B).obj (perfectLift.{u,v,w,s,t,j} A B C P₀) ≅ (qValue B).obj L)
    (H : Models.{v,max u v w s t j} B)
    (Hₚ : ∀ p : ℕ, Models.{max u v w,max u v w s t j} (BP A B C p)) where
  c : perfectLift.{u,v,w,s,t,j} A B C P₀ ⟶ L
  columns : ColumnComparison.{u,v,w,s,t,j} A B C
  perfect : FiniteProjective (perfectLift.{u,v,w,s,t,j} A B C P₀)
  sq (X : compValue.{t} B) (n : ℤ) :
    let S := coverRing.{u,v,w,j} A B C
    let I := (input.{v,s,t} B P₀).obj X
    totalStep B S I n ≫ totalStep B S I (n+1) = 0
  product (X : compValue.{t} B) :
    ProductComparison.{u,v,w,s,t,j} A B C ((input.{v,s,t} B P₀).obj X) columns perfect (sq X)
  total : compValue.{t} B ⥤ compValue.{max u v w s t j} B
  global : compValue.{t} B ⥤ compValue.{max u v w s t j} B
  total_obj (X : compValue.{t} B) :
    total.obj X = localTotal B (coverRing.{u,v,w,j} A B C) ((input.{v,s,t} B P₀).obj X) (sq X)
  global_obj (X : compValue.{t} B) :
    global.obj X = internalHomValue (perfectLift.{u,v,w,s,t,j} A B C P₀)
      ((targetLift.{u,v,w,s,t,j} A B C).obj X)
  augmentation : global ⟶ total
  global_model : global ⋙ qValue B ≅
    derivedHomInTarget ((qValue B).obj L) (targetLift.{u,v,w,s,t,j} A B C) H
  descent : derivedHomInTarget ((qValue B).obj L) (targetLift.{u,v,w,s,t,j} A B C) H ≅
    total ⋙ qValue B
  localHom (p : ℕ) : compValue.{t} B ⥤ compValue.{max u v w s t j} (BP A B C p)
  representative : QuasiIso c
  represents : (qValue B).map c = α.hom
  augmentation_quasiIso (X : compValue.{t} B) : QuasiIso (augmentation.app X)
  descent_hom (X : compValue.{t} B) :
    descent.hom.app X = (global_model.app X).inv ≫ (qValue B).map (augmentation.app X)
  total_map {X Y : compValue.{t} B} (f : X ⟶ Y) (n : ℤ) :
    (eqToHom (total_obj X).symm ≫ total.map f ≫ eqToHom (total_obj Y)).f n =
      totalComponent (coverRing.{u,v,w,j} A B C) ((input.{v,s,t} B P₀).map f) n
  localRepresentative (p : ℕ) :
    QuasiIso ((extend.{v,max u v w,max u v w s t j} B (BP A B C p)).map c)
  localRepresentative_cofaces {p q : ℕ} (f : Fin (p+1) → Fin (q+1)) :
    let P := perfectLift.{u,v,w,s,t,j} A B C P₀
    let Cₚ (r : ℕ) := (restrict.{v,max u v w,max u v w s t j} B (BP A B C r)).map
      ((extend.{v,max u v w,max u v w s t j} B (BP A B C r)).map c)
    Cₚ p ≫ onExtension.{u,v,w,s,t,j} (A := A) (C := C) f L =
      onExtension.{u,v,w,s,t,j} (A := A) (C := C) f P ≫ Cₚ q
  local_model (p : ℕ) : localHom p ⋙ qValue (BP A B C p) ≅
    derivedHomInTarget
      ((qValue (BP A B C p)).obj ((extend.{v,max u v w,max u v w s t j} B (BP A B C p)).obj L))
      (localTarget.{u,v,w,s,t,j} A B C p) (Hₚ p)
  local_obj (p : ℕ) (X : compValue.{t} B) :
    (localHom p).obj X = internalHomValue
      ((extend.{v,max u v w,max u v w s t j} B (BP A B C p)).obj
        (perfectLift.{u,v,w,s,t,j} A B C P₀))
      ((localTarget.{u,v,w,s,t,j} A B C p).obj X)
  augmentation_coordinates (X : compValue.{t} B) (n : ℤ)
      (z : (internalHomValue (perfectLift.{u,v,w,s,t,j} A B C P₀)
        ((targetLift.{u,v,w,s,t,j} A B C).obj X)).X n) :
    let x := (eqToHom (global_obj X).symm ≫ augmentation.app X ≫ eqToHom (total_obj X)).f n z
    x 0 = (columns.iso 0 _ _ perfect).hom.f n (extendCochain (BP A B C 0) n z) ∧
      ∀ p : ℕ, x (p+1) = 0

namespace DescentData

variable {A B C}
variable [Module.FaithfullyFlat A C]
variable {P₀ : (Descent.PerfectMappingDescent.perfect.{v,s} B).FullSubcategory}
  {L : compValue.{max u v w s t j} B}
  {α : (qValue B).obj (perfectLift.{u,v,w,s,t,j} A B C P₀) ≅ (qValue B).obj L}
  {H : Models.{v,max u v w s t j} B}
  {Hₚ : ∀ p, Models.{max u v w,max u v w s t j} (BP A B C p)}
  (Z : DescentData.{u,v,w,s,t,j} A B C P₀ L α H Hₚ)

/-- The coordinatewise comparison with the F08 product over the cover powers. -/
def productIso (X : compValue.{t} B) :
    originalTotal.{u,v,w,s,t,j} A B C ((input.{v,s,t} B P₀).obj X) (Z.product X).sqOriginal ≅
      Z.total.obj X :=
  (Z.product X).iso ≪≫ eqToIso (Z.total_obj X).symm

/-- View F08's natural totalization on the product of the original columns. -/
def originalTotalFunctor : compValue.{t} B ⥤ compValue.{max u v w s t j} B where
  obj X := originalTotal.{u,v,w,s,t,j} A B C ((input.{v,s,t} B P₀).obj X) (Z.product X).sqOriginal
  map {X Y} f := (Z.productIso X).hom ≫ Z.total.map f ≫ (Z.productIso Y).inv
  map_id X := by simp
  map_comp f g := by simp

/-- The comparison of totalizations is natural in the target complex. -/
def originalTotalComparison : Z.originalTotalFunctor ≅ Z.total :=
  NatIso.ofComponents Z.productIso (by intro X Y f; simp [originalTotalFunctor])

/-- The augmentation into the product of the original columns. -/
def originalAugmentation : Z.global ⟶ Z.originalTotalFunctor :=
  Z.augmentation ≫ Z.originalTotalComparison.inv

/-- The descent isomorphism with the signed product of the original Hom columns. -/
def originalDescent :
    derivedHomInTarget ((qValue B).obj L) (targetLift.{u,v,w,s,t,j} A B C) H ≅
      Z.originalTotalFunctor ⋙ qValue B :=
  Z.descent ≪≫ Functor.isoWhiskerRight Z.originalTotalComparison.symm (qValue B)

/-- The original augmentation is unit insertion in column zero on the signed product. -/
def OriginalAugmentationFormula : Prop :=
  ∀ (X : compValue.{t} B) (n : ℤ)
    (z : (internalHomValue (perfectLift.{u,v,w,s,t,j} A B C P₀)
      ((targetLift.{u,v,w,s,t,j} A B C).obj X)).X n),
    let x := (eqToHom (Z.global_obj X).symm ≫ Z.originalAugmentation.app X).f n z
    x 0 = extendCochain (BP A B C 0) n z ∧ ∀ p : ℕ, x (p + 1) = 0

end DescentData

def PerfectCotangentDescent : Prop :=
  ∀ (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Module.FaithfullyFlat A C]
    (P₀ : (perfect.{v,s} B).FullSubcategory)
    (L : compValue.{max u v w s t j} B)
    (α : (qValue B).obj (perfectLift.{u,v,w,s,t,j} A B C P₀) ≅ (qValue B).obj L)
    (H : Models.{v,max u v w s t j} B)
    (Hₚ : ∀ p : ℕ, Models.{max u v w,max u v w s t j} (BP A B C p)),
    Nonempty (DescentData.{u,v,w,s,t,j} A B C P₀ L α H Hₚ)

end Descent
section SquareZero
open _root_.DerivedFormalization (ModuleCochain)
open _root_.DerivedFormalization.Affine (NonpositiveCDGA)

open CotangentAmitsurModels (RingBridge transported ordinaryRestriction)
open CotangentComplex (Model)
open Tensor (ModuleTensor regular)
open SquareZeroMaps (Extension IsNonpositive Maps CycleComparison PathTarget)
open PolynomialPath (ModulePathModel)
open SquareZeroHomotopy (PolynomiallyHomotopic cohomologyClass)
open DG.HomComplex (homComplex)
open Descent.PerfectHomBaseChange (restrict)

universe k₀ r z

/-- A strict cohomology calculation for the actual square-zero extension
and polynomial homotopy relation. -/
def SquareZeroClasses {k : Type k₀} [Field k] [CharZero k]
    {A B : NonpositiveCDGA.{k₀,z} k} {b : A ⟶ B} (M : Model b)
    (T : ModuleTensor.{k₀,z} k) (X : B.Module) (H : ModuleCochain.{k₀,z} k) : Prop :=
  ∃ (S : Extension X) (W : ModulePathModel X) (U : Extension W.obj)
    (Y : PathTarget S W U) (D₀ : CycleComparison M T S)
    (a : ∀ i : ℤ, (homComplex (M.module T) X).homology i ≅ H.homology i)
    (q : Quot (PolynomiallyHomotopic (R := M) Y) ≃ H.homology 0),
    ∀ f : Maps M S.projection S.zeroSection,
      q (Quot.mk _ f) = (a 0).hom (cohomologyClass (D₀.equiv f))

/-- Compute the square-zero classes and every tangent cohomology group on the
same ordinary Hom column, using the map from the perfect representative. -/
def SquareZeroCohomology : Prop :=
  ∀ {k : Type k₀} [Field k] [CharZero k]
    {R : Type r} [CommRing R] [Algebra k R] (E : RingBridge.{k₀,r,z} k R)
    {A : NonpositiveCDGA.{k₀,max r z} k}
    {b : A ⟶ transported.{k₀,r,z} k R} (M : Model b)
    (T : ModuleTensor.{k₀,max r z} k)
    (_ : T.Formulas (M.augmentation : _ ⟶ (transported.{k₀,r,z} k R).toCommDGAlgebra)
      (regular _))
    (_ : ∀ N : (transported.{k₀,r,z} k R).Module, T.Formulas (𝟙 _) N)
    (P L X : compValue.{max r z} R)
    (_e : E.strict.functor.obj L ≅ M.module T)
    (c : P ⟶ L) (_ : QuasiIso c) (_ : P.IsKProjective)
    (_ : ∀ i : ℤ, 0 < i → Subsingleton (X.X i)),
    let Xdg := E.strict.functor.obj X
    let H := (ordinaryRestriction.{k₀,r,z} k R).obj (internalHomValue P X)
    SquareZeroClasses M T Xdg H

end SquareZero

section Affine

open Opposite
open Descent.PerfectMappingDescent (perfect)
open DerivedHomModels (Models)
open CotangentAmitsurModels
  (BP CP RingBridge CompatibleColumns OriginalRingDiagramComparison transported
    liftedBaseMap originalBaseMap changeRepresentative)
open CotangentComplex (Model oneObject)
open Tensor (ModuleTensor)
open Descent.PerfectHomBaseChange (changeCoefficients)

universe k₀ r

/-- The common representative of the cotangent complex and its scalar
extensions are taken in the original rings and compared to one resolved
diagram. -/
def CotangentDiagramConclusion
    (k : Type k₀) [Field k] [CharZero k]
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Algebra k A] [Algebra k B] [IsScalarTower k A B]
    {A' B' C' : Type r}
    [CommRing A'] [CommRing B'] [CommRing C']
    [Algebra k A'] [Algebra k B'] [Algebra A' B'] [Algebra A' C'] [IsScalarTower k A' B']
    [Module.FaithfullyFlat A C]
    (e : B ≃ₐ[k] B') (eₚ : ∀ p, BP A B C p ≃ₐ[k] BP A' B' C' p)
    (O : OriginalRingDiagramComparison.{v,r,max u v w,max k₀ s t} e.toRingEquiv (fun p => (eₚ p).toRingEquiv)
      (fun f => columnMap (A := A) (B := B) (C := C) f)
      (fun f => columnMap (A := A') (B := B') (C := C') f))
    (T : ModuleTensor.{k₀,max k₀ u v w r s t} k)
    (M : Model (liftedBaseMap.{k₀,r,max k₀ u v w s t} (k := k) (A := A') (B := B')))
    (E : RingBridge.{k₀,r,max k₀ u v w s t} k B')
    (F : ∀ p, RingBridge.{k₀,r,max k₀ u v w s t} k (BP A' B' C' p))
    (D : CompatibleColumns T M E F) : Prop :=
    let b := transported.{k₀,r,max k₀ u v w s t} k B'
    ∀ (h : DG.Derived.HomotopyCategoryLaws (oneObject b)),
    letI := DG.Derived.homotopyCategory (oneObject b) h
    letI := DG.DerivedKProjective.derivedCategoryInstance (oneObject b) h
    let Q := DG.Derived.quotient (oneObject b) h
    ∃ (L : compValue.{max k₀ u v w r s t} B)
      (a : (changeRepresentative.{v,r,max k₀ u v w r s t} e.toRingEquiv).obj L ≅ D.L)
      (I : derivedValue.{max k₀ u v w r s t} B ≌
        CotangentAmitsurModels.transportDerived.{k₀,r,max k₀ u v w s t} k B' h)
      (_l : I.functor.obj ((qValue B).obj L) ≅ Q.obj (M.module T))
      (lₚ : ∀ p,
        let X := (changeRepresentative.{max u v w,r,max k₀ u v w r s t} (eₚ p).toRingEquiv).obj
          ((extend.{v,max u v w,max k₀ u v w r s t} B (BP A B C p)).obj L)
        (F p).strict.functor.obj X ≅ (D.column p).model.module T),
      (∀ p, (lₚ p).hom = (F p).strict.functor.map
        ((O.extendIso p).hom.app L ≫ (extend B' (BP A' B' C' p)).map a.hom) ≫
        (D.identification p).hom) ∧
      ∀ (P₀ : (perfect.{v,s} B).FullSubcategory)
        (α : (qValue B).obj (perfectLift.{u,v,w,s,t,max k₀ r} A B C P₀) ≅ (qValue B).obj L)
        (H : Models.{v,max k₀ u v w r s t} B)
        (Hₚ : ∀ p, Models.{max u v w,max k₀ u v w r s t} (BP A B C p)),
        ∃ Z : DescentData.{u,v,w,s,t,max k₀ r} A B C P₀ L α H Hₚ,
          Z.OriginalAugmentationFormula ∧
          ∀ (X : compValue.{t} B) (_ : ∀ i : ℤ, i ≠ 0 → Subsingleton (X.X i)),
            let V := (targetLift.{u,v,w,s,t,max k₀ r} A B C).obj X
            let Xdg := E.strict.functor.obj
              ((changeRepresentative.{v,r,max k₀ u v w r s t} e.toRingEquiv).obj V)
            SquareZeroClasses M T Xdg
              ((CotangentAmitsurModels.ordinaryRestriction.{k₀,v,max k₀ u v w r s t} k B).obj
                (Z.originalTotalFunctor.obj X)) ∧
            ∀ p,
              let Xₚ := (localTarget.{u,v,w,s,t,max k₀ r} A B C p).obj X
              let Xdgₚ := (F p).strict.functor.obj
                ((changeRepresentative.{max u v w,r,max k₀ u v w r s t} (eₚ p).toRingEquiv).obj Xₚ)
              SquareZeroClasses (D.column p).model T Xdgₚ
                ((CotangentAmitsurModels.ordinaryRestriction.{k₀,max u v w,max k₀ u v w r s t}
                  k (BP A B C p)).obj ((Z.localHom p).obj X))

def CotangentDiagramDescent : Prop :=
  ∀ (k : Type k₀) [Field k] [CharZero k]
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Algebra k A] [Algebra k B] [IsScalarTower k A B]
    {A' B' C' : Type r}
    [CommRing A'] [CommRing B'] [CommRing C']
    [Algebra k A'] [Algebra k B'] [Algebra A' B'] [Algebra A' C'] [IsScalarTower k A' B']
    [Module.FaithfullyFlat A C]
    (e : B ≃ₐ[k] B') (eₚ : ∀ p, BP A B C p ≃ₐ[k] BP A' B' C' p)
    (O : OriginalRingDiagramComparison.{v,r,max u v w,max k₀ s t} e.toRingEquiv (fun p => (eₚ p).toRingEquiv)
      (fun f => columnMap (A := A) (B := B) (C := C) f)
      (fun f => columnMap (A := A') (B := B') (C := C') f))
    (T : ModuleTensor.{k₀,max k₀ u v w r s t} k)
    (M : Model (liftedBaseMap.{k₀,r,max k₀ u v w s t} (k := k) (A := A') (B := B')))
    (E : RingBridge.{k₀,r,max k₀ u v w s t} k B')
    (F : ∀ p, RingBridge.{k₀,r,max k₀ u v w s t} k (BP A' B' C' p))
    (D : CompatibleColumns T M E F)
    (_ : ∀ {U V : _root_.DerivedFormalization.Affine.CommDGAlgebra.{k₀,max k₀ u v w r s t} k}
      (f : U ⟶ V) (X : V.Module), T.Formulas f X),
    CotangentDiagramConclusion.{u,v,w,s,t,k₀,r} k A B C e eₚ O T M E F D


/-- Faithfully flat locality over the original rings, with independent levels
for the rings and the two original complexes. -/
def FaithfullyFlatTangentDescent : Prop :=
  ∀ (k : Type k₀) [Field k] [CharZero k]
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    [IsScalarTower k A B] [IsScalarTower k A C] [Module.FaithfullyFlat A C],
    ∃ (A' B' C' : CommAlgCat.{max k₀ u v w} k)
      (eA : A ≃ₐ[k] A') (eB : B ≃ₐ[k] B') (eC : C ≃ₐ[k] C')
      (f : A' →ₐ[k] B') (g : A' →ₐ[k] C'),
      (∀ a : A, f (eA a) = eB (algebraMap A B a)) ∧
      (∀ a : A, g (eA a) = eC (algebraMap A C a)) ∧
      letI : Algebra A' B' := f.toRingHom.toAlgebra
      letI : Algebra A' C' := g.toRingHom.toAlgebra
      letI : IsScalarTower k A' B' := IsScalarTower.of_algHom f
      letI : IsScalarTower k A' C' := IsScalarTower.of_algHom g
      Module.FaithfullyFlat A' C' ∧
      ∃ (eCP : ∀ p, CP A C p ≃ₐ[k] CP A' C' p)
        (eBP : ∀ p, BP A B C p ≃ₐ[k] BP A' B' C' p),
        (∀ (p : ℕ) (i : Fin (p+1)) (c : C),
          eCP p (factor A C i c) = factor A' C' i (eC c)) ∧
        (∀ (p : ℕ) (b : B) (z : CP A C p), eBP p (b ⊗ₜ[A] z) = eB b ⊗ₜ[A'] eCP p z) ∧
        (∀ (p : ℕ) (b : B), eBP p (baseMap p b) = baseMap p (eB b)) ∧
        (∀ {p q : ℕ} (d : Fin (p+1) → Fin (q+1)) (z : BP A B C p),
          eBP q (columnMap (A := A) (B := B) (C := C) d z) =
            columnMap (A := A') (B := B') (C := C') d (eBP p z)) ∧
        ∃ (O : OriginalRingDiagramComparison.{v,max k₀ u v w,max u v w,max k₀ s t}
              eB.toRingEquiv (fun p => (eBP p).toRingEquiv)
              (fun f => columnMap (A := A) (B := B) (C := C) f)
              (fun f => columnMap (A := A') (B := B') (C := C') f))
          (T : ModuleTensor.{k₀,max k₀ u v w s t} k)
          (M : Model (liftedBaseMap.{k₀,max k₀ u v w,max k₀ u v w s t}
            (k := k) (A := A') (B := B')))
          (E : RingBridge.{k₀,max k₀ u v w,max k₀ u v w s t} k B')
          (F : ∀ p, RingBridge.{k₀,max k₀ u v w,max k₀ u v w s t} k (BP A' B' C' p))
          (D : CompatibleColumns T M E F),
          (∀ h, E.Localizes h) ∧ (∀ p h, (F p).Localizes h) ∧
          Nonempty (CotangentAmitsurModels.CompatibleHomColumns (A := A') (C := C') E F) ∧
          D.CoherentExtensions ∧
          CotangentDiagramConclusion.{u,v,w,s,t,k₀,max k₀ u v w} k A B C
            eB eBP O T M E F D

end Affine

end
end Specs.DerivedFormalization.Affine.TangentDescent
