import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! HA-K02, notes/002/advanced-homological-algebra.tex, proposition and proof
at lines 1240–1266. Additivity is expressed by Preadditive and binary biproducts.
The library orders the summands X[n+1], Y[n]; degreeIso gives the source order.
projectionToShift is the positive projection, opposite to the library triangle's third map.
Homotopy (f ≫ b) (a ≫ f') means bf-f'a = d s + s d.
-/
set_option linter.checkUnivs false
set_option linter.unusedVariables false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe v u
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace Specs.AdvancedHomologicalAlgebra.MappingCones
variable {A : Type u} [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
noncomputable abbrev coneComplex {X Y : CochainComplex A ℤ} (f : X ⟶ Y) := mappingCone f
noncomputable abbrev targetInclusion {X Y : CochainComplex A ℤ} (f : X ⟶ Y) := mappingCone.inr f
noncomputable abbrev projectionToShift {X Y : CochainComplex A ℤ} (f : X ⟶ Y) :=
  -(mappingCone.triangle f).mor₃
noncomputable abbrev targetProjection {X Y : CochainComplex A ℤ} (f : X ⟶ Y) (n : ℤ) :=
  (mappingCone.snd f).v n n (add_zero n)
noncomputable abbrev shiftProjection {X Y : CochainComplex A ℤ} (f : X ⟶ Y) (n : ℤ) :=
  (mappingCone.fst f).1.v n (n+1) rfl
noncomputable abbrev shiftInclusion {X Y : CochainComplex A ℤ} (f : X ⟶ Y) (n : ℤ) :=
  (mappingCone.inl f).v (n+1) n (by omega)
noncomputable def degreeBiproductIso {X Y : CochainComplex A ℤ} (f : X ⟶ Y) (n : ℤ) :
    (coneComplex f).X n ≅ Y.X n ⊞ X.X (n+1) where
  hom := biprod.lift (targetProjection f n) (shiftProjection f n)
  inv := biprod.desc ((targetInclusion f).f n) (shiftInclusion f n)
  hom_inv_id := by
    simp only [biprod.lift_desc]
    simpa only [add_comm] using mappingCone.id_X f n (n+1) rfl
  inv_hom_id := by
    ext <;> simp [targetProjection, shiftProjection, targetInclusion, shiftInclusion]
noncomputable abbrev chosenConeMap {X Y X' Y' : CochainComplex A ℤ}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {a : X ⟶ X'} {b : Y ⟶ Y'}
    (h : Homotopy (f ≫ b) (a ≫ f')) := mappingCone.mapOfHomotopy h
noncomputable abbrev strictConeMap {X Y X' Y' : CochainComplex A ℤ}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (w : f ≫ b = a ≫ f') := mappingCone.map f f' a b w
end Specs.AdvancedHomologicalAlgebra.MappingCones

namespace Specs.AdvancedHomologicalAlgebra.MappingCones

def coneType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A], ∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y), CochainComplex A ℤ

noncomputable def coneValue : coneType :=
  fun _ _ _ _ _ _ f => coneComplex f

def degreeIsoType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A], ∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y), ∀ n : ℤ, (coneComplex f).X n ≅ Y.X n ⊞ X.X (n+1)

noncomputable def degreeIsoValue : degreeIsoType :=
  fun _ _ _ _ _ _ f n => degreeBiproductIso f n

def inclusionType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A], ∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y), Y ⟶ coneComplex f

noncomputable def inclusionValue : inclusionType :=
  fun _ _ _ _ _ _ f => targetInclusion f

def projectionType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A], ∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y), coneComplex f ⟶ X⟦(1 : ℤ)⟧

noncomputable def projectionValue : projectionType :=
  fun _ _ _ _ _ _ f => projectionToShift f

def degree_coordinatesType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A], ∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y), ∀ n : ℤ, (degreeBiproductIso f n).hom ≫ biprod.fst = targetProjection f n ∧ (degreeBiproductIso f n).hom ≫ biprod.snd = shiftProjection f n

def differentialType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A], ∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y), ∀ n : ℤ, (coneComplex f).d n (n+1) ≫ targetProjection f (n+1) = targetProjection f n ≫ Y.d n (n+1) + shiftProjection f n ≫ f.f (n+1) ∧ (coneComplex f).d n (n+1) ≫ shiftProjection f (n+1) = -(shiftProjection f n ≫ X.d (n+1) (n+1+1))

def inclusion_componentsType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A], ∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y), ∀ n : ℤ, (targetInclusion f).f n ≫ targetProjection f n = 𝟙 _ ∧ (targetInclusion f).f n ≫ shiftProjection f n = 0

def projection_componentsType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A], ∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y), ∀ n : ℤ, (projectionToShift f).f n = shiftProjection f n

def coneMapType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A], ∀ (X Y X' Y' : CochainComplex A ℤ) (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : Homotopy (f ≫ b) (a ≫ f')), coneComplex f ⟶ coneComplex f'

noncomputable def coneMapValue : coneMapType :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ h => chosenConeMap h

def coneMap_formulaType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A], ∀ (X Y X' Y' : CochainComplex A ℤ) (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : Homotopy (f ≫ b) (a ≫ f')), ∀ n : ℤ, (chosenConeMap h).f n = targetProjection f n ≫ b.f n ≫ (targetInclusion f').f n + shiftProjection f n ≫ (h.hom (n+1) n ≫ (targetInclusion f').f n + a.f (n+1) ≫ shiftInclusion f' n)

def coneMap_inclusionType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A], ∀ (X Y X' Y' : CochainComplex A ℤ) (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : Homotopy (f ≫ b) (a ≫ f')), targetInclusion f ≫ chosenConeMap h = b ≫ targetInclusion f'

def coneMap_projectionType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A], ∀ (X Y X' Y' : CochainComplex A ℤ) (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : Homotopy (f ≫ b) (a ≫ f')), chosenConeMap h ≫ projectionToShift f' = projectionToShift f ≫ a⟦(1 : ℤ)⟧'

def strictMapType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A], ∀ (X Y X' Y' : CochainComplex A ℤ) (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (w : f ≫ b = a ≫ f'), coneComplex f ⟶ coneComplex f'

noncomputable def strictMapValue : strictMapType :=
  fun _ _ _ _ _ _ _ _ f f' a b w => strictConeMap f f' a b w

def strictMap_zeroHomotopyType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A], ∀ (X Y X' Y' : CochainComplex A ℤ) (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (w : f ≫ b = a ≫ f'), strictConeMap f f' a b w = chosenConeMap (Homotopy.ofEq w)

def strictMap_idType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A], ∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y), strictConeMap f f (𝟙 X) (𝟙 Y) (by simp) = 𝟙 (coneComplex f)

def strictMap_compType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A], ∀ (X Y X' Y' X'' Y'' : CochainComplex A ℤ) (f : X ⟶ Y) (f' : X' ⟶ Y') (f'' : X'' ⟶ Y'') (a : X ⟶ X') (b : Y ⟶ Y') (a' : X' ⟶ X'') (b' : Y' ⟶ Y'') (w : f ≫ b = a ≫ f') (w' : f' ≫ b' = a' ≫ f''), strictConeMap f f'' (a ≫ a') (b ≫ b') (by rw [← Category.assoc, w, Category.assoc, w', ← Category.assoc]) = strictConeMap f f' a b w ≫ strictConeMap f' f'' a' b' w'


def inclusion_matrixType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A], ∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y), ∀ n : ℤ, (targetInclusion f).f n ≫ (degreeBiproductIso f n).hom = biprod.inl

def projection_matrixType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A], ∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y), ∀ n : ℤ, (degreeBiproductIso f n).inv ≫ (projectionToShift f).f n = biprod.snd

def differential_matrixType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A], ∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y), ∀ n : ℤ, (degreeBiproductIso f n).inv ≫ (coneComplex f).d n (n+1) ≫ (degreeBiproductIso f (n+1)).hom = biprod.lift (biprod.fst ≫ Y.d n (n+1) + biprod.snd ≫ f.f (n+1)) (-(biprod.snd ≫ X.d (n+1) (n+1+1)))

def coneMap_matrixType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A], ∀ (X Y X' Y' : CochainComplex A ℤ) (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : Homotopy (f ≫ b) (a ≫ f')), ∀ n : ℤ, (degreeBiproductIso f n).inv ≫ (chosenConeMap h).f n ≫ (degreeBiproductIso f' n).hom = biprod.lift (biprod.fst ≫ b.f n + biprod.snd ≫ h.hom (n+1) n) (biprod.snd ≫ a.f (n+1))

end Specs.AdvancedHomologicalAlgebra.MappingCones
