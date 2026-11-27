import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.TowerExactSequence
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.Projective
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.CategoryTheory.Whiskering

namespace Specs.DerivedFormalization.SequentialHomotopyLimits

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open HomologicalComplex
open Specs.DerivedFormalization.Cochains (compValue cohomologyValue qValue)
open Specs.DerivedFormalization.TowerExactSequence

universe u v

noncomputable section

abbrev Towers (C : Type*) [Category* C] := ℕᵒᵖ ⥤ C

variable {R : Type u} [Ring R]

abbrev productMap {X Y : Towers (compValue.{v} R)} (f : X ⟶ Y) :
    towerProduct X ⟶ towerProduct Y :=
  Limits.Pi.map (fun n : ℕ ↦ f.app (op n))

theorem difference_natural {X Y : Towers (compValue.{v} R)} (f : X ⟶ Y) :
    differenceValue X ≫ productMap f = productMap f ≫ differenceValue Y := by
  apply Pi.hom_ext
  intro n
  simp only [differenceValue, Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
    Category.comp_id, Category.assoc, Limits.Pi.map_π, Limits.Pi.map_π_assoc,
    shiftValue, Pi.map'_comp_π, Pi.map'_comp_π_assoc]
  rw [f.naturality]

/-- The strict tower model given by the shifted cone of the product difference. -/
def holimValue : Towers (compValue.{v} R) ⥤ compValue.{v} R where
  obj X := CochainComplex.mappingCocone (differenceValue X)
  map {X Y} f := (CochainComplex.mappingCone.map _ _ (productMap f) (productMap f)
    (difference_natural f))⟦(-1 : ℤ)⟧'
  map_id X := by
    have h : productMap (𝟙 X) = 𝟙 _ := by
      apply Pi.hom_ext
      intro n
      simp
    change (shiftFunctor (compValue R) (-1 : ℤ)).map
      (CochainComplex.mappingCone.map _ _ _ _ (difference_natural (𝟙 X))) = 𝟙 _
    rw [show CochainComplex.mappingCone.map _ _ _ _ (difference_natural (𝟙 X)) = 𝟙 _ by
      simp [h, CochainComplex.mappingCone.map_id]]
    exact (shiftFunctor (compValue R) (-1 : ℤ)).map_id _
  map_comp {X Y Z} f g := by
    have h : productMap (f ≫ g) = productMap f ≫ productMap g := by
      apply Pi.hom_ext
      intro n
      simp
    let G := shiftFunctor (compValue R) (-1 : ℤ)
    change G.map (CochainComplex.mappingCone.map _ _ _ _ (difference_natural (f ≫ g))) =
      G.map (CochainComplex.mappingCone.map _ _ _ _ (difference_natural f)) ≫
      G.map (CochainComplex.mappingCone.map _ _ _ _ (difference_natural g))
    rw [← G.map_comp]
    apply congrArg G.map
    rw [← CochainComplex.mappingCone.map_comp]
    congr

set_option linter.checkUnivs false in
def holimType := ∀ {R : Type u} [Ring R], Towers (compValue.{v} R) ⥤ compValue.{v} R

/-- The inclusion of compatible families into the shifted cone with zero target coordinate. -/
def comparisonValue (X : Towers (compValue.{v} R)) : limit X ⟶ holimValue.obj X :=
  CochainComplex.mappingCocone.lift (differenceValue X) (inclusionValue X) 0 (by
    have h : inclusionValue X ≫ differenceValue X = 0 := (shortComplexValue X).zero
    simp [h])

set_option linter.checkUnivs false in
def comparisonType :=
  ∀ {R : Type u} [Ring R] (X : Towers (compValue.{v} R)), limit X ⟶ holimValue.obj X

def stagewiseQuasiIso {X Y : Towers (compValue.{v} R)} (f : X ⟶ Y) : Prop :=
  ∀ n : ℕ, QuasiIso (f.app (op n))

def surjectiveTransitions (X : Towers (compValue.{v} R)) : Prop :=
  ∀ (n : ℕ) (i : ℤ), Function.Surjective ((transition X n).f i)

def holimInvarianceType : Prop :=
  ∀ {R : Type u} [Ring R] {X Y : Towers (compValue.{v} R)} (f : X ⟶ Y),
    stagewiseQuasiIso f → QuasiIso (holimValue.map f)

def comparisonQuasiIsoType : Prop :=
  ∀ {R : Type u} [Ring R] (X : Towers (compValue.{v} R)),
    surjectiveTransitions X → QuasiIso (comparisonValue X)

def comparisonNaturalityType : Prop :=
  ∀ {R : Type u} [Ring R] {X Y : Towers (compValue.{v} R)} (f : X ⟶ Y),
    limMap f ≫ comparisonValue Y = comparisonValue X ≫ holimValue.map f

open DerivedFormalization.Model.Complexes in
open DerivedFormalization.Specs.ComplexProjective
  DerivedFormalization.Specs.ComplexGenerators in
abbrev ProjectiveFactorization (R : Type u) [Ring R] :=
  MorphismProperty.FunctorialFactorizationData
    (cofibrationsValue R ⊓ quasiIso (ModuleCat R) (ComplexShape.up ℤ))
    (degreewiseSurjectiveValue R)

/-- The replacement is obtained by successive functorial projective factorizations.
The isomorphisms identify its stages with the chosen factorization objects. -/
def replacementFor (F : ProjectiveFactorization R) : Prop :=
    ∃ (Y : Towers (compValue.{u} R) ⥤ Towers (compValue.{u} R)) (j : 𝟭 _ ⟶ Y),
      (∀ X, stagewiseQuasiIso (j.app X) ∧ surjectiveTransitions (Y.obj X)) ∧
      (∀ X, ∃ e : (Y.obj X).obj (op 0) ≅ X.obj (op 0),
        (j.app X).app (op 0) ≫ e.hom = 𝟙 _) ∧
      (∀ (X) (n : ℕ),
        let a := Arrow.mk (transition X n ≫ (j.app X).app (op n))
        ∃ e : (Y.obj X).obj (op (n + 1)) ≅ F.Z.obj a,
          (j.app X).app (op (n + 1)) ≫ e.hom = F.i.app a ∧
          transition (Y.obj X) n = e.hom ≫ F.p.app a) ∧
      (∀ {X Z} (f : X ⟶ Z), stagewiseQuasiIso f → QuasiIso (limMap (Y.map f))) ∧
      (∀ X, QuasiIso (comparisonValue (Y.obj X)) ∧ QuasiIso (holimValue.map (j.app X))) ∧
      Nonempty ((Y ⋙ lim) ⋙ qValue.{u} R ≅ holimValue ⋙ qValue.{u} R)

def replacementType : Prop :=
  ∀ (R : Type u) [Ring R] (F : ProjectiveFactorization R), replacementFor F

def projectiveReplacementType : Prop :=
  ∀ (R : Type u) [Ring R], ∃ F : ProjectiveFactorization R, replacementFor F

/-- An explicit degreewise surjective replacement inside the original category,
with the ring and module universes independent. Its limit computes the same
localized functor as the shifted cone. -/
def contractibleReplacementType : Prop :=
  ∀ (R : Type u) [Ring R],
    ∃ (Y : Towers (compValue.{v} R) ⥤ Towers (compValue.{v} R)) (j : 𝟭 _ ⟶ Y),
      (∀ X, stagewiseQuasiIso (j.app X) ∧ surjectiveTransitions (Y.obj X)) ∧
      (∀ X, ∃ e : (Y.obj X).obj (op 0) ≅ X.obj (op 0),
        (j.app X).app (op 0) ≫ e.hom = 𝟙 _) ∧
      (∀ (X) (n : ℕ),
        let Z := (Y.obj X).obj (op n)
        let a := transition X n ≫ (j.app X).app (op n)
        let φ : Z ⟶ Z := -𝟙 Z
        ∃ e : (Y.obj X).obj (op (n + 1)) ≅ X.obj (op (n + 1)) ⊞ CochainComplex.mappingCocone φ,
          (j.app X).app (op (n + 1)) ≫ e.hom = biprod.inl ∧
            transition (Y.obj X) n = e.hom ≫ biprod.desc a (CochainComplex.mappingCocone.fst φ)) ∧
      (∀ {X Z} (f : X ⟶ Z), stagewiseQuasiIso f → QuasiIso (limMap (Y.map f))) ∧
      ∃ e : (Y ⋙ lim) ⋙ qValue.{v} R ≅ holimValue ⋙ qValue.{v} R,
        ∀ X, e.hom.app X ≫ (qValue.{v} R).map (holimValue.map (j.app X)) =
          (qValue.{v} R).map (comparisonValue (Y.obj X))

abbrev moduleProduct (M : Towers (ModuleCat.{v} R)) := ∏ᶜ (fun n : ℕ ↦ M.obj (op n))

/-- The successor difference on a tower of modules. -/
def moduleDifference (M : Towers (ModuleCat.{v} R)) : moduleProduct M ⟶ moduleProduct M :=
  𝟙 _ - Pi.map' (fun n : ℕ ↦ n + 1) (fun n ↦ M.map (homOfLE (Nat.le_add_right n 1)).op)

abbrev moduleInclusion (M : Towers (ModuleCat.{v} R)) : limit M ⟶ moduleProduct M :=
  Pi.lift (fun n : ℕ ↦ limit.π M (op n))

abbrev moduleProductMap {M N : Towers (ModuleCat.{v} R)} (f : M ⟶ N) :
    moduleProduct M ⟶ moduleProduct N :=
  Limits.Pi.map (fun n : ℕ ↦ f.app (op n))

theorem moduleDifference_natural {M N : Towers (ModuleCat.{v} R)} (f : M ⟶ N) :
    moduleDifference M ≫ moduleProductMap f = moduleProductMap f ≫ moduleDifference N := by
  apply Pi.hom_ext
  intro n
  simp only [moduleDifference, Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
    Category.comp_id, Category.assoc, Limits.Pi.map_π, Limits.Pi.map_π_assoc,
    Pi.map'_comp_π, Pi.map'_comp_π_assoc]
  rw [f.naturality]

/-- For sequential module towers, the first derived limit is the difference cokernel. -/
abbrev limOne (M : Towers (ModuleCat.{v} R)) := cokernel (moduleDifference M)

abbrev limOneMap {M N : Towers (ModuleCat.{v} R)} (f : M ⟶ N) : limOne M ⟶ limOne N :=
  cokernel.map _ _ (moduleProductMap f) (moduleProductMap f) (moduleDifference_natural f)

abbrev cohomologyTower (X : Towers (compValue.{v} R)) (q : ℤ) :=
  X ⋙ cohomologyValue R q

abbrev cohomologyTowerMap {X Y : Towers (compValue.{v} R)} (f : X ⟶ Y) (q : ℤ) :=
  Functor.whiskerRight f (cohomologyValue R q)

abbrev productComparison (X : Towers (compValue.{v} R)) (q : ℤ) :
    (cohomologyValue R q).obj (towerProduct X) ⟶ moduleProduct (cohomologyTower X q) :=
  piComparison (cohomologyValue R q) (fun n : ℕ ↦ X.obj (op n))

/-- The shifted cone triangle, taken in the homotopy category. -/
def holimTriangle (X : Towers (compValue.{v} R)) :=
  (HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).mapTriangle.obj
    (CochainComplex.mappingCocone.triangle (differenceValue X))

/-- The connecting map in the cohomology sequence of the shifted cone triangle. -/
def coneConnecting (X : Towers (compValue.{v} R)) (q : ℤ) :
    (towerProduct X).homology (q - 1) ⟶ (holimValue.obj X).homology q :=
  (HomotopyCategory.homologyFunctorFactors _ _ (q - 1)).inv.app _ ≫
    Functor.homologySequenceδ
      (HomotopyCategory.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) 0) (holimTriangle X) (q - 1) q (sub_add_cancel q 1) ≫
    (HomotopyCategory.homologyFunctorFactors _ _ q).hom.app _

abbrev coneProjection (X : Towers (compValue.{v} R)) (q : ℤ) :
    (holimValue.obj X).homology q ⟶ (towerProduct X).homology q :=
  homologyMap (CochainComplex.mappingCocone.fst (differenceValue X)) q

/-- The Milnor short exact sequence, with both maps induced by the shifted cone
sequence under the canonical cohomology product comparisons. -/
def milnorSequenceType : Prop :=
  ∀ (R : Type u) [Ring R] (q : ℤ),
    ∃ (i : ∀ (X : Towers (compValue.{v} R)),
        limOne (cohomologyTower X (q - 1)) ⟶ (holimValue.obj X).homology q)
      (p : ∀ (X : Towers (compValue.{v} R)),
        (holimValue.obj X).homology q ⟶ limit (cohomologyTower X q))
      (w : ∀ X, i X ≫ p X = 0),
      (∀ X, (ShortComplex.mk (i X) (p X) (w X)).ShortExact ∧
        productComparison X (q - 1) ≫ cokernel.π _ ≫ i X = coneConnecting X q ∧
        p X ≫ moduleInclusion _ = coneProjection X q ≫ productComparison X q) ∧
      (∀ {X Y} (a : X ⟶ Y),
        limOneMap (cohomologyTowerMap a (q - 1)) ≫ i Y = i X ≫ homologyMap (holimValue.map a) q ∧
        homologyMap (holimValue.map a) q ≫ p Y = p X ≫ limMap (cohomologyTowerMap a q))

end

end Specs.DerivedFormalization.SequentialHomotopyLimits
