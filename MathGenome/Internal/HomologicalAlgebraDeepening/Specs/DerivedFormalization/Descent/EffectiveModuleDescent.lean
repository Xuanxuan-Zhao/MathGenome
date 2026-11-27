import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.DescentCounit
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! Effective descent for modules along a faithfully flat algebra. -/

open CategoryTheory
open scoped ChangeOfRings

namespace EffectiveModuleDescentSpec

universe u v w

noncomputable section

open StrictModuleDataSpec
open DescentCounitSpec (baseChangePosition baseChangeTheta descend counitMap)

attribute [local instance] StrictModuleDataSpec.category

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

/-- Scalar extension along the given map of commutative rings. -/
abbrev extend : ModuleCat.{max u v w} A ⥤ ModuleCat.{max u v w} B :=
  ModuleCat.extendScalars (algebraMap A B)

/-- The diagonal and triple identities for the canonical tensor-position isomorphisms. -/
structure Coherence : Prop where
  normalized (M : ModuleCat.{max u v w} A) :
    (diagonalTheta (baseChangeTheta.{u, v, w} (B := B) M)).hom =
      𝟙 ((extend.{u, v, w} A B).obj M)
  cocycle (M : ModuleCat.{max u v w} A) :
    (alongTheta (pair 2) (baseChangeTheta.{u, v, w} (B := B) M)).hom ≫
        (alongTheta (pair 0) (baseChangeTheta.{u, v, w} (B := B) M)).hom =
      (alongTheta (pair 1) (baseChangeTheta.{u, v, w} (B := B) M)).hom

private theorem baseChange_naturality {M N : ModuleCat.{max u v w} A} (f : M ⟶ N) :
    (atPosition.{u, v, w} A B (0 : Fin 2)).map ((extend A B).map f) ≫
        (baseChangeTheta.{u, v, w} (B := B) N).hom =
      (baseChangeTheta.{u, v, w} (B := B) M).hom ≫
        (atPosition.{u, v, w} A B (1 : Fin 2)).map ((extend A B).map f) := by
  let p₀ := baseChangePosition.{u, v, w} (A := A) (B := B) (0 : Fin 2)
  let p₁ := baseChangePosition.{u, v, w} (A := A) (B := B) (1 : Fin 2)
  change _ ≫ (p₀.inv.app N ≫ p₁.hom.app N) =
    (p₀.inv.app M ≫ p₁.hom.app M) ≫ _
  rw [← Category.assoc]
  change (((extend A B) ⋙ atPosition.{u, v, w} A B (0 : Fin 2)).map f ≫ p₀.inv.app N) ≫
    p₁.hom.app N = _
  rw [p₀.inv.naturality, Category.assoc, p₁.hom.naturality, Category.assoc]
  rfl

/-- Send M to B ⊗[A] M with the canonical tensor-position comparison.
Scalar extension on maps is the underlying map of strict data. -/
def baseChange (h : Coherence.{u, v, w} A B) :
    ModuleCat.{max u v w} A ⥤ Datum.{u, v, w} A B where
  obj M := ⟨(extend A B).obj M, baseChangeTheta (B := B) M, h.normalized M, h.cocycle M⟩
  map f := ⟨(extend A B).map f, baseChange_naturality A B f⟩
  map_id _ := Hom.ext ((extend A B).map_id _)
  map_comp f g := Hom.ext ((extend A B).map_comp f g)

/-- The equivalence with its canonical comparison maps. The inverse is the functor
of invariants, acting by restriction on morphisms. -/
structure EffectiveEquivalence where
  coherence : Coherence.{u, v, w} A B
  unitIso : 𝟭 (ModuleCat.{max u v w} A) ≅ baseChange A B coherence ⋙ descend
  counitIso : descend ⋙ baseChange A B coherence ≅ 𝟭 (Datum.{u, v, w} A B)
  unit_apply (M : ModuleCat.{max u v w} A) (m : M) :
    ((unitIso.hom.app M m).val : (extend A B).obj M) = (1 : B) ⊗ₜ[A, algebraMap A B] m
  counit_hom (X : Datum.{u, v, w} A B) :
    (counitIso.hom.app X).hom = counitMap X
  triangle (M : ModuleCat.{max u v w} A) :
    (baseChange A B coherence).map (unitIso.hom.app M) ≫
      counitIso.hom.app ((baseChange A B coherence).obj M) =
        𝟙 ((baseChange A B coherence).obj M)

/-- The categorical equivalence with the specified forward and inverse functors. -/
def EffectiveEquivalence.toEquivalence (e : EffectiveEquivalence.{u, v, w} A B) :
    ModuleCat.{max u v w} A ≌ Datum.{u, v, w} A B :=
  ⟨baseChange A B e.coherence, descend, e.unitIso, e.counitIso, e.triangle⟩

/-- The canonical tensor-position comparisons define strict descent data for any algebra. -/
def BaseChangeCoherence : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    Coherence.{u, v, w} A B

/-- Faithfully flat scalar extension is an equivalence onto strict module descent data. -/
def Effective : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B], Nonempty (EffectiveEquivalence.{u, v, w} A B)

end

end EffectiveModuleDescentSpec
