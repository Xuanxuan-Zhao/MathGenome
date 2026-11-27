import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedHomComparisonMaps

/-! The tensor-evaluation comparison and the scalar-extension comparison. -/

namespace DerivedFormalization.DerivedHomComparisonMaps

open CategoryTheory Category MonoidalCategory Opposite
open Specs.DerivedFormalization.DerivedHomComparisonMaps
open Specs.DerivedFormalization.Cochains (derivedValue)
open Specs.DerivedFormalization.CochainTensorTransport (AdequateModel)
open Specs.DerivedFormalization.DerivedHomAdjunction (Closed tensorRight)
open Specs.DerivedFormalization.DerivedHomModels (Models rHomValue)

universe u w a

attribute [local instance] HasDerivedCategory.standard

noncomputable section

set_option linter.style.haveILetI false

/-- The evaluation counit for derived Hom. -/
abbrev evaluation : EvaluationType := @evaluationValue

/-- The mate of associativity followed by tensoring the evaluation counit. -/
abbrev projectionComparison : ProjectionComparisonType := @projectionComparisonValue

/-- The mate of derived evaluation transported along scalar extension. -/
abbrev baseChange : BaseChangeType := @baseChangeValue

section Naturality

variable {R : Type u} [CommRing R] {A : Type a} [CommRing A] {e : R ≃+* A}
  {M : AdequateModel e} {T : Specs.DerivedFormalization.DerivedTensor.Model M}
  {H : Models.{u,a} R} (c : Closed T H)

private theorem transpose_precomp {Z Z' X Y : derivedValue.{a} R}
    (z : Z' ⟶ Z) :
    letI := T.monoidal
    ∀ (k : Z ⊗ X ⟶ Y), c.equiv Z' X Y ((z ⊗ₘ 𝟙 X) ≫ k) = z ≫ c.equiv Z X Y k := by
  letI := T.monoidal
  intro k
  have h := c.natural z (𝟙 X) (𝟙 Y) k
  change c.equiv Z' X Y ((z ⊗ₘ 𝟙 X) ≫ k ≫ 𝟙 Y) =
    z ≫ c.equiv Z X Y k ≫ (rHomValue H).map (𝟙 _) at h
  rw [(rHomValue H).map_id, comp_id, comp_id] at h
  exact h

private theorem transpose_prepost {Z X X' Y Y' : derivedValue.{a} R}
    (x : X' ⟶ X) (y : Y ⟶ Y') :
    letI := T.monoidal
    ∀ (k : Z ⊗ X ⟶ Y), c.equiv Z X' Y' ((𝟙 Z ⊗ₘ x) ≫ k ≫ y) =
      c.equiv Z X Y k ≫ (rHomValue H).map (Prod.mkHom x.op y) := by
  letI := T.monoidal
  intro k
  have h := c.natural (𝟙 Z) x y k
  change c.equiv Z X' Y' ((𝟙 Z ⊗ₘ x) ≫ k ≫ y) =
    𝟙 Z ≫ c.equiv Z X Y k ≫ (rHomValue H).map (Prod.mkHom x.op y) at h
  simpa only [id_comp] using h

private theorem mates_commute {Z Z' X X' Y Y' : derivedValue.{a} R}
    (z : Z ⟶ Z') (x : X' ⟶ X) (y : Y ⟶ Y') :
    letI := T.monoidal
    ∀ (k : Z ⊗ X ⟶ Y) (k' : Z' ⊗ X' ⟶ Y'),
      (z ⊗ₘ 𝟙 X') ≫ k' = (𝟙 Z ⊗ₘ x) ≫ k ≫ y →
      z ≫ c.equiv Z' X' Y' k' = c.equiv Z X Y k ≫ (rHomValue H).map (Prod.mkHom x.op y) := by
  letI := T.monoidal
  intro k k' h
  rw [← transpose_precomp c z k', h, transpose_prepost c x y k]

/-- Evaluation is the counit of the fixed-source adjunction. -/
theorem evaluation_eq_counit (X Y : derivedValue.{a} R) :
    evaluation c X Y = (c.adjunction X).counit.app Y := by
  have h := (c.adjunction X).homEquiv_counit ((rHomValue H).obj (op X, Y)) Y (𝟙 _)
  rw [c.adjunction_homEquiv, (tensorRight T X).map_id, id_comp] at h
  exact h

/-- Compatibility of evaluation with precomposition in its source and
postcomposition in its target. -/
theorem evaluation_natural {X X' Y Y' : derivedValue.{a} R}
    (x : X' ⟶ X) (y : Y ⟶ Y') :
    letI := T.monoidal
    ((rHomValue H).map (Prod.mkHom x.op y) ⊗ₘ 𝟙 X') ≫ evaluation c X' Y' =
      (𝟙 ((rHomValue H).obj (op X, Y)) ⊗ₘ x) ≫ evaluation c X Y ≫ y := by
  letI := T.monoidal
  apply (c.equiv ((rHomValue H).obj (op X, Y)) X' Y').injective
  rw [transpose_precomp c, transpose_prepost c]
  simp only [evaluation, evaluationValue, LinearEquiv.apply_symm_apply, comp_id, id_comp]

end Naturality

theorem projectionComparison_natural : ProjectionNaturality := by
  intro R _ A _ e M T H c P P' X X' Y Y' p x y
  letI := T.monoidal
  dsimp only [projectionComparisonValue]
  apply mates_commute c
  simp only [assoc, associator_naturality_assoc, tensorHom_comp_tensorHom, comp_id, id_comp]
  rw [evaluation_natural c]
  rw [← id_tensorHom_id P ((rHomValue H).obj (op X, Y))]
  simp only [associator_naturality_assoc, tensorHom_comp_tensorHom, id_comp]

theorem baseChange_natural : BaseChangeNaturality := by
  intro R S _ _ A B _ _ e d MR MS TR TS HR HS f F L cR cS m X X' Y Y' x y
  letI := TR.monoidal
  letI := TS.monoidal
  letI := TR.symmetric
  letI := TS.symmetric
  letI := m.braided
  dsimp only [baseChangeValue]
  apply mates_commute cS
  let E := L.derived
  let K := rHomValue HR
  change
    (E.map (K.map (Prod.mkHom x.op y)) ⊗ₘ 𝟙 _) ≫
      Functor.LaxMonoidal.μ E _ _ ≫ E.map (evaluation cR X' Y') =
    (𝟙 _ ⊗ₘ E.map x) ≫
      (Functor.LaxMonoidal.μ E _ _ ≫ E.map (evaluation cR X Y)) ≫ E.map y
  simp only [assoc]
  rw [← E.map_id X', Functor.LaxMonoidal.μ_natural_assoc, ← E.map_comp]
  rw [← E.map_id (K.obj (op X, Y)), Functor.LaxMonoidal.μ_natural_assoc,
    ← E.map_comp, ← E.map_comp]
  rw [evaluation_natural cR]

end

end DerivedFormalization.DerivedHomComparisonMaps
