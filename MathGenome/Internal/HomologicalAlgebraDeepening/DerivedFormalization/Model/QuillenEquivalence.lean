import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.DerivedAdjunction
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

open CategoryTheory HomotopicalAlgebra

universe v₁ v₂ u₁ u₂

namespace DerivedFormalization.Model

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [FunctorialModelCategory C] [FunctorialModelCategory D]
  {L : C ⥤ D} {U : D ⥤ C} {adj : L ⊣ U}
  {c : Replacement C} {d : Replacement D}

set_option backward.isDefEq.respectTransparency false in
/-- Transporting an ordinary map to the derived adjunction commutes with
taking its adjoint, in the respective comparison coordinates. -/
private theorem localized_homEquiv (a : DerivedAdjunctionData adj c d)
    {X : C} {Y : D} (f : L.obj X ⟶ Y) :
    a.adjunction.homEquiv (c.localization.obj X) (d.localization.obj Y)
        ((a.leftComparison.hom.app X ≫ d.localization.map (L.map (c.p.app X))) ≫
          d.localization.map f) =
      c.localization.map (adj.homEquiv X Y f) ≫
        (c.localization.map (U.map (d.i.app Y)) ≫ a.rightComparison.inv.app Y) := by
  let p : c.Q.obj X ⟶ X := c.p.app X
  let i : Y ⟶ d.R.obj Y := d.i.app Y
  let k := (a.leftComparison.hom.app X ≫ d.localization.map (L.map p)) ≫
    d.localization.map f
  have hk : k ≫ d.localization.map i =
      a.leftComparison.hom.app X ≫ d.localization.map (L.map p ≫ f ≫ i) := by
    simp only [k, Functor.map_comp, Category.assoc]
  have he := a.homEquiv_representative X Y (L.map p ≫ f ≫ i) k hk
  change c.localization.map p ≫ a.adjunction.homEquiv _ _ k ≫
      a.rightComparison.hom.app Y =
    c.localization.map (adj.homEquiv _ _ (L.map p ≫ f ≫ i)) at he
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
    c.localization.map_comp, c.localization.map_comp] at he
  have : IsIso (c.localization.map p) :=
    (c.weakEquivalence_iff_isIso p).2 (c.trivialFibration X).2
  have he' := (cancel_epi (c.localization.map p)).1 he
  apply (cancel_mono (a.rightComparison.hom.app Y)).1
  change a.adjunction.homEquiv _ _ k ≫ a.rightComparison.hom.app Y = _
  simp only [Category.assoc, Iso.inv_hom_id_app]
  change _ = c.localization.map (adj.homEquiv X Y f) ≫
    c.localization.map (U.map i) ≫ 𝟙 (c.localization.obj (U.obj (d.R.obj Y)))
  rw [Category.comp_id]
  exact he'

/-- Quillen equivalences are detected on ordinary adjoint maps between
a cofibrant source and a fibrant target. -/
theorem DerivedAdjunctionData.isEquivalence_iff (h : IsQuillen adj)
    (a : DerivedAdjunctionData adj c d) :
    a.left.IsEquivalence ↔
      ∀ (X : C) (Y : D) [IsCofibrant X] [IsFibrant Y] (f : L.obj X ⟶ Y),
        weakEquivalences D f ↔ weakEquivalences C (adj.homEquiv X Y f) := by
  constructor
  · intro he X Y _ _ f
    have : a.left.IsEquivalence := he
    have : a.right.IsEquivalence := a.adjunction.isEquivalence_right_of_isEquivalence_left
    let α := a.leftComparison.hom.app X ≫ d.localization.map (L.map (c.p.app X))
    let β := c.localization.map (U.map (d.i.app Y)) ≫ a.rightComparison.inv.app Y
    have : IsIso α := a.isIso_leftComparison_cofibrant h X
    have : IsIso β := a.isIso_rightComparison_fibrant h Y
    let k := α ≫ d.localization.map f
    have hk : IsIso k ↔ IsIso (a.adjunction.homEquiv _ _ k) := by
      rw [a.adjunction.homEquiv_unit]
      refine ⟨fun _ => inferInstance, fun hk => ?_⟩
      have : IsIso (a.right.map k) := (isIso_comp_left_iff _ _).1 hk
      exact isIso_of_reflects_iso k a.right
    have hf := localized_homEquiv a f
    change a.adjunction.homEquiv _ _ k = c.localization.map (adj.homEquiv X Y f) ≫ β at hf
    rw [← d.weakEquivalence_iff_isIso, ← c.weakEquivalence_iff_isIso,
      ← isIso_comp_left_iff α, ← isIso_comp_right_iff _ β, ← hf]
    exact hk
  · intro hw
    have unitIso (X : C) [IsCofibrant X] :
        IsIso (a.adjunction.unit.app (c.localization.obj X)) := by
      have := d.fibrant (L.obj X)
      let f : L.obj X ⟶ d.R.obj (L.obj X) := d.i.app (L.obj X)
      have hf := (hw X (d.R.obj (L.obj X)) f).1 (d.trivialCofibration (L.obj X)).2
      have := a.isIso_leftComparison_cofibrant h X
      have he := (c.weakEquivalence_iff_isIso _).2 hf
      rw [← a.unit_cofibrant X] at he
      exact (isIso_comp_right_iff _ _).1 he
    have counitIso (Y : D) [IsFibrant Y] :
        IsIso (a.adjunction.counit.app (d.localization.obj Y)) := by
      have := c.cofibrant (U.obj Y)
      let g : c.Q.obj (U.obj Y) ⟶ U.obj Y := c.p.app (U.obj Y)
      let f := (adj.homEquiv (c.Q.obj (U.obj Y)) Y).symm g
      have hf : weakEquivalences D f := (hw (c.Q.obj (U.obj Y)) Y f).2 (by
        simpa only [f, Equiv.apply_symm_apply] using (c.trivialFibration (U.obj Y)).2)
      have := a.isIso_rightComparison_fibrant h Y
      have := (d.weakEquivalence_iff_isIso f).2 hf
      have he : IsIso (a.leftComparison.hom.app (U.obj Y) ≫ d.localization.map f) :=
        inferInstance
      change IsIso (a.leftComparison.hom.app (U.obj Y) ≫ d.localization.map
        ((adj.homEquiv (c.Q.obj (U.obj Y)) Y).symm (c.p.app (U.obj Y)))) at he
      rw [← a.counit_fibrant Y] at he
      exact (isIso_comp_left_iff _ _).1 he
    have := c.isLocalization
    have := d.isLocalization
    have := Localization.essSurj c.localization (weakEquivalences C)
    have := Localization.essSurj d.localization (weakEquivalences D)
    have (A : HomotopyCategory C) : IsIso (a.adjunction.unit.app A) := by
      let X := c.localization.objPreimage A
      let p : c.Q.obj X ⟶ X := c.p.app X
      have := c.cofibrant X
      have := (c.weakEquivalence_iff_isIso p).2 (c.trivialFibration X).2
      let e := asIso (c.localization.map p) ≪≫ c.localization.objObjPreimageIso A
      exact (NatTrans.isIso_app_iff_of_iso a.adjunction.unit e).1 (unitIso (c.Q.obj X))
    have (B : HomotopyCategory D) : IsIso (a.adjunction.counit.app B) := by
      let Y := d.localization.objPreimage B
      let i : Y ⟶ d.R.obj Y := d.i.app Y
      have := d.fibrant Y
      have := (d.weakEquivalence_iff_isIso i).2 (d.trivialCofibration Y).2
      let e := (asIso (d.localization.map i)).symm ≪≫ d.localization.objObjPreimageIso B
      exact (NatTrans.isIso_app_iff_of_iso a.adjunction.counit e).1 (counitIso (d.R.obj Y))
    exact a.adjunction.toEquivalence.isEquivalence_functor

end DerivedFormalization.Model
