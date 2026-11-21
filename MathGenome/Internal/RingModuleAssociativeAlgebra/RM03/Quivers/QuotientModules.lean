import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.QuotientModules

open CategoryTheory

namespace RM03.Quivers.QuotientModules

universe u v

variable {A : Type u} [Ring A] (I : Ideal A) [I.IsTwoSided]

@[simp]
theorem descendObj_mk_smul (M : (annihilated.{u, v} I).FullSubcategory)
    (a : A) (m : M.obj) :
    Ideal.Quotient.mk I a • (show descendObj I M from m) = (a • m : M.obj) :=
  rfl

theorem linearityAfterRestriction : Specs.LinearityAfterRestriction.{u, v} := by
  intro A _ I _ M N f
  constructor
  · intro h a m
    exact h (Ideal.Quotient.mk I a) m
  · intro h q m
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact h a m

/-- Restriction along the quotient projection, with codomain the full subcategory of
modules annihilated by the ideal. -/
noncomputable def restrict : ModuleCat.{v} (A ⧸ I) ⥤ (annihilated.{u, v} I).FullSubcategory :=
  (annihilated I).lift (ModuleCat.restrictScalars (Ideal.Quotient.mk I)) (by
    intro M m a
    change Ideal.Quotient.mk I (a : A) • (show M from m) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr a.property, zero_smul])

/-- Descend the action on objects and retain the original function on each morphism. -/
def descend : (annihilated.{u, v} I).FullSubcategory ⥤ ModuleCat.{v} (A ⧸ I) where
  obj := descendObj I
  map {M N} f := ModuleCat.ofHom (X := descendObj I M) (Y := descendObj I N)
    { toFun := f.hom
      map_add' := f.hom.hom.map_add
      map_smul' := by
        intro q m
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
        exact f.hom.hom.map_smul a m }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The canonical equivalence given by restriction and descent along the quotient projection. -/
noncomputable def equivalence :
    ModuleCat.{v} (A ⧸ I) ≌ (annihilated.{u, v} I).FullSubcategory where
  functor := restrict I
  inverse := descend I
  unitIso := NatIso.ofComponents (fun M => by
    let e : M ≃ₗ[A ⧸ I] (restrict I ⋙ descend I).obj M :=
      { toAddEquiv := AddEquiv.refl M
        map_smul' := by
          intro q m
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
          rfl }
    exact e.toModuleIso) (fun _ => rfl)
  counitIso := NatIso.ofComponents (fun M => (annihilated I).isoMk (by
    let e : ((descend I ⋙ restrict I).obj M).obj ≃ₗ[A] M.obj :=
      { toAddEquiv := AddEquiv.refl M.obj
        map_smul' := fun _ _ => rfl }
    exact e.toModuleIso)) (fun _ => rfl)
  functor_unitIso_comp _ := rfl

theorem quotientEquivalence : Specs.QuotientEquivalence.{u, v} := by
  intro A _ I _
  exact ⟨equivalence I, rfl, rfl, fun _ => rfl, rfl⟩

end RM03.Quivers.QuotientModules
