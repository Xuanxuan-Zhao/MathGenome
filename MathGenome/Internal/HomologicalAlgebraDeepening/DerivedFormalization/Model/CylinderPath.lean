import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.CylinderPath

namespace DerivedFormalization.Model

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra Specs.ModelCylinderPath

abbrev Cylinder : cylinderType.{v, u} := cylinderValue

abbrev PathObject : pathObjectType.{v, u} := pathObjectValue

abbrev Cylinder.IsGood : goodCylinderType.{v, u} := goodCylinderValue

abbrev PathObject.IsGood : goodPathObjectType.{v, u} := goodPathObjectValue

section

variable {C : Type u} [Category.{v} C] [ModelCategory C]

theorem cylinderFold {A : C} (P : Cylinder A) : P.val.i ≫ P.val.π = codiag A := by
  apply coprod.hom_ext <;> simp

theorem pathObjectDiagonal {B : C} (P : PathObject B) : P.val.ι ≫ P.val.p = diag B := by
  apply prod.hom_ext <;> simp

theorem cylinderEndpoints {A : C} [IsCofibrant A] (P : Cylinder A) :
    trivialCofibrations C P.val.i₀ ∧ trivialCofibrations C P.val.i₁ := by
  let _ : P.val.IsGood := P.property
  exact ⟨mem_trivialCofibrations _, mem_trivialCofibrations _⟩

theorem pathObjectEvaluations {B : C} [IsFibrant B] (P : PathObject B) :
    trivialFibrations C P.val.p₀ ∧ trivialFibrations C P.val.p₁ := by
  let _ : P.val.IsGood := P.property
  exact ⟨mem_trivialFibrations _, mem_trivialFibrations _⟩

end

theorem functorialGoodCylinder : functorialGoodCylinderType.{v, u} := by
  intro C _ _
  let D : C ⥤ C :=
    { obj A := A ⨿ A
      map f := coprod.map f f
      map_id _ := coprod.map_id_id
      map_comp f g := (coprod.map_map f f g g).symm }
  let inl : 𝟭 C ⟶ D :=
    { app _ := coprod.inl
      naturality _ _ f := (coprod.inl_map f f).symm }
  let inr : 𝟭 C ⟶ D :=
    { app _ := coprod.inr
      naturality _ _ f := (coprod.inr_map f f).symm }
  let fold : D ⟶ 𝟭 C :=
    { app A := codiag A
      naturality _ _ f := coprod.map_codiag f }
  let factor := functorialFactorizationData (cofibrations C) (trivialFibrations C)
  let h := (factor.functorCategory C).factorizationData fold
  refine ⟨h.Z, inl ≫ h.i, inr ≫ h.i, h.p, fun A => ?_⟩
  have fac : h.i.app A ≫ h.p.app A = codiag A := congr_app h.fac A
  change (coprod.inl ≫ h.i.app A) ≫ h.p.app A = 𝟙 A ∧
    (coprod.inr ≫ h.i.app A) ≫ h.p.app A = 𝟙 A ∧
    cofibrations C (coprod.desc (coprod.inl ≫ h.i.app A) (coprod.inr ≫ h.i.app A)) ∧
    trivialFibrations C (h.p.app A)
  refine ⟨by simp [Category.assoc, fac], by simp [Category.assoc, fac], ?_, h.hp A⟩
  simpa only [← coprod.desc_comp, coprod.desc_inl_inr, Category.id_comp] using h.hi A

theorem functorialGoodPathObject : functorialGoodPathObjectType.{v, u} := by
  intro C _ _
  let D : C ⥤ C :=
    { obj B := B ⨯ B
      map f := prod.map f f
      map_id _ := prod.map_id_id
      map_comp f g := (prod.map_map f f g g).symm }
  let fst : D ⟶ 𝟭 C :=
    { app _ := prod.fst
      naturality _ _ f := prod.map_fst f f }
  let snd : D ⟶ 𝟭 C :=
    { app _ := prod.snd
      naturality _ _ f := prod.map_snd f f }
  let diagonal : 𝟭 C ⟶ D :=
    { app B := diag B
      naturality _ _ f := (prod.diag_map f).symm }
  let factor := functorialFactorizationData (trivialCofibrations C) (fibrations C)
  let h := (factor.functorCategory C).factorizationData diagonal
  refine ⟨h.Z, h.i, h.p ≫ fst, h.p ≫ snd, fun B => ?_⟩
  have fac : h.i.app B ≫ h.p.app B = diag B := congr_app h.fac B
  change h.i.app B ≫ h.p.app B ≫ prod.fst = 𝟙 B ∧
    h.i.app B ≫ h.p.app B ≫ prod.snd = 𝟙 B ∧
    trivialCofibrations C (h.i.app B) ∧
    fibrations C (prod.lift (h.p.app B ≫ prod.fst) (h.p.app B ≫ prod.snd))
  refine ⟨by simp [← Category.assoc, fac], by simp [← Category.assoc, fac], h.hi B, ?_⟩
  rw [← prod.comp_lift, prod.lift_fst_snd]
  change fibrations C (h.p.app B ≫ 𝟙 (D.obj B))
  rw [Category.comp_id]
  exact h.hp B

end DerivedFormalization.Model
