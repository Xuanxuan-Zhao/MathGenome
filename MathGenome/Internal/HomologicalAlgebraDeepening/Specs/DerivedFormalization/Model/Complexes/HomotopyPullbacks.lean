import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.Projective
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomotopicalAlgebra
open CochainComplex CochainComplex.HomComplex

universe u

namespace DerivedFormalization.Specs.ComplexHomotopyPullbacks

open Model.Complexes

variable {A : Type u} [Ring A] {T X Y Z : Cochains A}

/-- The shifted cone of the difference of the two legs. -/
noncomputable def modelValue (f : X ⟶ Z) (g : Y ⟶ Z) : Cochains A :=
  mappingCocone (biprod.desc f (-g))

/-- The strict square map on shifted cones. -/
noncomputable def coconeMapValue {S W : Cochains A} (h : T ⟶ Z) (k : S ⟶ W)
    (a : T ⟶ S) (c : Z ⟶ W) (w : h ≫ c = a ≫ k) :
    mappingCocone h ⟶ mappingCocone k :=
  (mappingCone.map h k a c w)⟦(-1 : ℤ)⟧'

open WalkingCospan WalkingCospan.Hom in
/-- The cone model on the category of strict cospan diagrams. -/
noncomputable def functorValue (A : Type u) [Ring A] :
    (WalkingCospan ⥤ Cochains A) ⥤ Cochains A where
  obj D := modelValue (D.map inl) (D.map inr)
  map {D E} a := coconeMapValue _ _ (biprod.map (a.app left) (a.app right)) (a.app one) (by
    apply biprod.hom_ext'
    · simp [a.naturality inl]
    · simp [Preadditive.comp_neg, Preadditive.neg_comp, a.naturality inr])
  map_id D := by
    have h : biprod.map (𝟙 (D.obj left)) (𝟙 (D.obj right)) = 𝟙 _ := by
      apply biprod.hom_ext <;> simp
    simp [coconeMapValue, h, mappingCone.map_id, modelValue, mappingCocone]
  map_comp a b := by
    have h : biprod.map (a.app left ≫ b.app left) (a.app right ≫ b.app right) =
        biprod.map (a.app left) (a.app right) ≫ biprod.map (b.app left) (b.app right) := by
      apply biprod.hom_ext <;> simp
    simp only [NatTrans.comp_app, coconeMapValue, modelValue, mappingCocone]
    rw [← Functor.map_comp, ← mappingCone.map_comp]
    simp only [h]

/-- The auxiliary contractible complex with differential (da, a - db). -/
noncomputable def contractibleValue (Z : Cochains A) : Cochains A :=
  mappingCocone (-𝟙 Z)

/-- The replacement projection (x,a,b) ↦ f(x)+a. -/
noncomputable def replacementValue (f : X ⟶ Z) : X ⊞ contractibleValue Z ⟶ Z :=
  biprod.desc f (mappingCocone.fst (-𝟙 Z))

/-- Send a strict pullback point to the shifted cone with last coordinate zero. -/
noncomputable def comparisonValue (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullback f g ⟶ modelValue f g :=
  mappingCocone.lift (biprod.desc f (-g)) (biprod.lift (pullback.fst f g) (pullback.snd f g)) 0 (by
    rw [biprod.lift_desc, Preadditive.comp_neg, ← sub_eq_add_neg, sub_eq_zero.mpr (pullback.condition (f := f) (g := g))]
    simp)

def modelType :=
  ∀ {A : Type u} [Ring A] {X Y Z : Cochains A}, (X ⟶ Z) → (Y ⟶ Z) → Cochains A

def functorType :=
  ∀ (A : Type u) [Ring A], (WalkingCospan ⥤ Cochains A) ⥤ Cochains A

def contractibleType := ∀ {A : Type u} [Ring A], Cochains A → Cochains A

def replacementMapType :=
  ∀ {A : Type u} [Ring A] {X Z : Cochains A},
    (X ⟶ Z) → (X ⊞ contractibleValue Z ⟶ Z)

def comparisonMapType :=
  ∀ {A : Type u} [Ring A] {X Y Z : Cochains A} (f : X ⟶ Z) (g : Y ⟶ Z),
    pullback f g ⟶ modelValue f g

/-- The cocone coordinates give the differential (dt, -h(t)-dz).
The first coordinate is the cochain map mappingCocone.fst. -/
def coconeDifferentialType : Prop :=
  ∀ (A : Type u) [Ring A] {T Z : Cochains A} (h : T ⟶ Z) (n : ℤ),
    (mappingCocone h).d n (n + 1) ≫ (mappingCocone.snd h).v (n + 1) n (by omega) =
      -((mappingCocone.fst h).f n ≫ h.f n) -
        (mappingCocone.snd h).v n (n - 1) (by omega) ≫ Z.d (n - 1) n

def contractibilityType : Prop :=
  ∀ (A : Type u) [Ring A] (Z : Cochains A),
    Nonempty (Homotopy (𝟙 (contractibleValue Z)) 0)

def replacementType : Prop :=
  ∀ (A : Type u) [Ring A] {X Z : Cochains A} (f : X ⟶ Z),
    biprod.inl ≫ replacementValue f = f ∧
      QuasiIso (biprod.inl : X ⟶ X ⊞ contractibleValue Z) ∧
      ComplexGenerators.degreewiseSurjectiveValue A (replacementValue f)

/-- The strict pullback of the replacement has coordinates (x,y,b), with its
auxiliary first coordinate forced to be g(y)-f(x). -/
def replacementPullbackType : Prop :=
  ∀ (A : Type u) [Ring A] {X Y Z : Cochains A} (f : X ⟶ Z) (g : Y ⟶ Z),
    ∃ e : pullback (replacementValue f) g ≅ modelValue f g,
      e.hom ≫ mappingCocone.fst (biprod.desc f (-g)) =
        biprod.lift (pullback.fst (replacementValue f) g ≫ biprod.fst) (pullback.snd (replacementValue f) g) ∧
      (Cochain.ofHom (pullback.fst (replacementValue f) g ≫ biprod.snd)).comp
          (mappingCocone.snd (-𝟙 Z)) (zero_add (-1)) =
        (Cochain.ofHom e.hom).comp (mappingCocone.snd (biprod.desc f (-g))) (zero_add (-1))

def invarianceType : Prop :=
  ∀ (A : Type u) [Ring A] {D E : WalkingCospan ⥤ Cochains A} (a : D ⟶ E),
    (∀ j, QuasiIso (a.app j)) → QuasiIso ((functorValue A).map a)

def kernelComparisonType : Prop :=
  ∀ (A : Type u) [Ring A] {T Z : Cochains A} (h : T ⟶ Z),
    ComplexGenerators.degreewiseSurjectiveValue A h →
      QuasiIso (mappingCocone.lift h (kernel.ι h) 0 (by simp))

def strictComparisonType : Prop :=
  ∀ (A : Type u) [Ring A] (M : ProjectiveModel A),
    letI := M.model
    ∀ {X Y Z : Cochains A} (f : X ⟶ Z) (g : Y ⟶ Z),
      (Fibration f ∨ Fibration g) → QuasiIso (comparisonValue f g)

end DerivedFormalization.Specs.ComplexHomotopyPullbacks
