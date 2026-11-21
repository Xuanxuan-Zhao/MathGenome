import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.FreeChainDual
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open P202Specs.FreeChainDual

universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace P202.FreeChainDual

/-- Duality identifies bounded-below projective chain complexes with
bounded-below injective cochain complexes in the opposite category. -/
private theorem opposite_isKInjective {R : Type u} [Ring R]
    (C : ChainComplex (ModuleCat.{v} R) ℤ)
    [∀ n, Module.Free R (C.X n)] (hC : BoundedBelow C) :
    CochainComplex.IsKInjective C.op := by
  obtain ⟨b, hb⟩ := hC
  have : CochainComplex.IsStrictlyGE C.op b := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact (hb n hn).op
  have (n : ℤ) : Injective (C.op.X n) := by
    change Injective (op (C.X n))
    infer_instance
  exact CochainComplex.isKInjective_of_injective C.op b

theorem homotopy_equivalence : HomotopyEquivalenceType.{u,v} := by
  intro R _ C D _ _ hC hD f _
  have := opposite_isKInjective C hC
  have := opposite_isKInjective D hD
  let fo : D.op ⟶ C.op := (opFunctor (ModuleCat.{v} R) (.down ℤ)).map f.op
  have : QuasiIso fo := inferInstance
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff fo).mp inferInstance
  let g : D ⟶ C := (unopFunctor (ModuleCat.{v} R) (.up ℤ)).map e.inv.op
  have hC' : Homotopy (f ≫ g) (𝟙 C) := by
    convert e.homotopyInvHomId.unop using 1 <;> (try simp [fo, g, he, opFunctor, unopFunctor]) <;> rfl
  have hD' : Homotopy (g ≫ f) (𝟙 D) := by
    convert e.homotopyHomInvId.unop using 1 <;> (try simp [fo, g, he, opFunctor, unopFunctor]) <;> rfl
  exact ⟨⟨f, g, hC', hD'⟩, rfl⟩

/-- Contravariant algebraic Hom preserves both chain homotopies. -/
theorem dual_cohomology_iso : DualCohomologyType.{u,v} := by
  intro R _ C D _ _ hC hD f _ A n
  obtain ⟨e, he⟩ := homotopy_equivalence C D hC hD f
  let F := preadditiveYoneda.obj A
  let eo : HomotopyEquiv D.op C.op :=
    { hom := (opFunctor (ModuleCat.{v} R) (.down ℤ)).map e.hom.op
      inv := (opFunctor (ModuleCat.{v} R) (.down ℤ)).map e.inv.op
      homotopyHomInvId := by simpa using e.homotopyInvHomId.op
      homotopyInvHomId := by simpa using e.homotopyHomInvId.op }
  let ed := F.mapHomotopyEquiv eo
  have : QuasiIso (dualMap f A) := by
    convert ed.quasiIso_hom using 1 <;> (try simp [ed, eo, F, dualMap, he]) <;> rfl
  infer_instance

end P202.FreeChainDual
