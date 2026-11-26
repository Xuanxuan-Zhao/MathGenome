import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RealFormsConjugations
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SolvableRadical
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Complex.Basic

universe u

namespace LinearAlgebraicGroups.Specs.RealPolarFixedPoints

open LieAlgebrasAndRepresentations.RealForms
open _root_.Specs.LieAlgebrasAndRepresentations.SolvableRadical (IsSemisimple_value)

/-- The automorphism group law is composition of Lie equivalences. -/
@[instance_reducible] def automorphismGroup {L : Type u} [LieRing L] [LieAlgebra ℂ L] :
    Group (L ≃ₗ⁅ℂ⁆ L) where
  one := 1
  mul g h := h.trans g
  inv := LieEquiv.symm
  mul_assoc _ _ _ := LieEquiv.ext fun _ => rfl
  one_mul _ := LieEquiv.ext fun _ => rfl
  mul_one _ := LieEquiv.ext fun _ => rfl
  inv_mul_cancel g := LieEquiv.ext g.symm_apply_apply

/-- The topology on complex Lie automorphisms induced by their matrix entries. -/
@[instance_reducible] noncomputable def automorphismTopology {L : Type u} [LieRing L] [LieAlgebra ℂ L] {n : ℕ}
    (b : Module.Basis (Fin n) ℂ L) : TopologicalSpace (L ≃ₗ⁅ℂ⁆ L) :=
  TopologicalSpace.induced (fun (g : L ≃ₗ⁅ℂ⁆ L) (i j : Fin n) =>
    b.repr (g (b j)) i) inferInstance

/-- Connected complex centralizers of all square-one automorphisms imply
connectedness of the automorphisms fixed by any real conjugation. -/
def connectedFixedPointsType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (σ : Conjugation L) (n : ℕ) (b : Module.Basis (Fin n) ℂ L),
    letI := automorphismGroup (L := L)
    letI := automorphismTopology b
    IsSemisimple_value ℂ L →
    (∀ a : L ≃ₗ⁅ℂ⁆ L, a * a = 1 →
      ConnectedSpace {g : L ≃ₗ⁅ℂ⁆ L // Commute g a}) →
    ConnectedSpace {g : L ≃ₗ⁅ℂ⁆ L // Intertwines σ σ g}

end LinearAlgebraicGroups.Specs.RealPolarFixedPoints
