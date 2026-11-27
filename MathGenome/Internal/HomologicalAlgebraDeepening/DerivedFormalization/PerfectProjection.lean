import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.PerfectProjection
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedHomComparisonMaps
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.PerfectDuals
import Mathlib.CategoryTheory.Yoneda

/-! Projection through a perfect factor. -/

namespace DerivedFormalization.PerfectProjection

open CategoryTheory MonoidalCategory

universe u a

attribute [local instance] HasDerivedCategory.standard

noncomputable section

set_option linter.style.haveILetI false

/-- The projection comparison for the right adjoint of tensoring on the right,
tested on maps from an arbitrary object using the exact pairing on the left. -/
private theorem comparison_isIso_of_pairing {C : Type*} [Category C] [MonoidalCategory C]
    {P D X : C} [ExactPairing P D] {G : C ⥤ C}
    (adj : (Functor.curryObj (MonoidalCategory.tensor C)).flip.obj X ⊣ G) (Y : C) :
    IsIso ((adj.homEquiv (P ⊗ G.obj Y) (P ⊗ Y))
      ((α_ P (G.obj Y) X).hom ≫ P ◁ adj.counit.app Y)) := by
  let B := G.obj Y
  let ev : B ⊗ X ⟶ Y := adj.counit.app Y
  let k : (P ⊗ B) ⊗ X ⟶ P ⊗ Y := (α_ P B X).hom ≫ P ◁ ev
  apply isIso_of_yoneda_map_bijective
  intro Z
  let e : (Z ⟶ P ⊗ B) ≃ (Z ⟶ G.obj (P ⊗ Y)) :=
    (tensorLeftHomEquiv Z P D B).symm.trans <|
      (adj.homEquiv (D ⊗ Z) Y).symm.trans <|
      ((α_ D Z X).homFromEquiv (Z := Y)).trans <|
      (tensorLeftHomEquiv (Z ⊗ X) P D Y).trans (adj.homEquiv Z (P ⊗ Y))
  change Function.Bijective (fun f : Z ⟶ P ⊗ B => f ≫ adj.homEquiv (P ⊗ B) (P ⊗ Y) k)
  suffices h : (fun f : Z ⟶ P ⊗ B => f ≫ adj.homEquiv (P ⊗ B) (P ⊗ Y) k) = e by
    rw [h]
    exact e.bijective
  funext f
  let g : D ⊗ Z ⟶ B := (tensorLeftHomEquiv Z P D B).symm f
  change f ≫ adj.homEquiv (P ⊗ B) (P ⊗ Y) k =
    adj.homEquiv Z (P ⊗ Y)
      (tensorLeftHomEquiv (Z ⊗ X) P D Y ((α_ D Z X).inv ≫ (adj.homEquiv (D ⊗ Z) Y).symm g))
  rw [← adj.homEquiv_naturality_left]
  apply congrArg (adj.homEquiv Z (P ⊗ Y))
  rw [adj.homEquiv_counit]
  change (f ⊗ₘ 𝟙 X) ≫ ((α_ P B X).hom ≫ P ◁ ev) =
    tensorLeftHomEquiv (Z ⊗ X) P D Y ((α_ D Z X).inv ≫ (g ⊗ₘ 𝟙 X) ≫ ev)
  rw [← Category.assoc, ← Category.assoc, tensorLeftHomEquiv_naturality]
  apply congrArg (fun m => m ≫ P ◁ ev)
  apply (tensorLeftHomEquiv (Z ⊗ X) P D (B ⊗ X)).symm.injective
  rw [Equiv.symm_apply_apply]
  exact tensorLeftHomEquiv_tensor (Y' := D) f (𝟙 X)

/-- For any perfect complex and arbitrary derived inputs, the canonical
tensor-evaluation comparison is a natural isomorphism. -/
theorem perfectProjection : Specs.DerivedFormalization.PerfectProjection.ProjectionIsomorphism.{u,a} := by
  refine ⟨DerivedHomComparisonMaps.projectionComparison_natural, ?_⟩
  intro R _ A _ e M T H c P X Y hP
  letI := T.monoidal
  have hDual := PerfectDuals.perfectDuality T H c
  obtain ⟨pairing, _, _, _⟩ := (hDual.2 P hP).2.2.1
  letI := pairing
  have h := comparison_isIso_of_pairing (P := P) (D := Specs.DerivedFormalization.PerfectDuals.dualValue T H P)
    (X := X) (c.adjunction X) Y
  rw [c.adjunction_homEquiv, ← DerivedHomComparisonMaps.evaluation_eq_counit c X Y] at h
  unfold Specs.DerivedFormalization.DerivedHomComparisonMaps.projectionComparisonValue
  rw [id_tensorHom]
  exact h

end

end DerivedFormalization.PerfectProjection
