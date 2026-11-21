import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Basic.Complex.Basic

/-!
Lemma 7.3 of the Lie algebra volume. The Cartan acts on both the stable
subspace and the quotient. We use the ordinary simultaneous eigenspaces
from the opening of Chapter 7, indexed by the entire complex Cartan dual.
-/

namespace Specs.LieAlgebrasAndRepresentations.WeightSubmodules

universe u v

local notation "weight[" M ", " μ "]" => LieSubmodule.toSubmodule (LieModule.weightSpace M (μ : _ → ℂ))

/-- The intersections with the ambient weight spaces form an internal direct sum in the
stable subspace. The weight spaces of the quotient likewise form an internal direct sum,
and each is canonically identified with the corresponding quotient of a weight space. -/
def weight_submodules_type : Prop := by
  classical
  exact
    ∀ {H : Type u} [LieRing H] [LieAlgebra ℂ H] [IsLieAbelian H]
      {V : Type v} [AddCommGroup V] [Module ℂ V] [LieRingModule H V] [LieModule ℂ H V]
      (W : LieSubmodule ℂ H V),
      DirectSum.IsInternal (fun μ : Module.Dual ℂ H => weight[V, μ]) →
      DirectSum.IsInternal
        (fun μ : Module.Dual ℂ H => (weight[V, μ]).comap W.toSubmodule.subtype) ∧
      DirectSum.IsInternal (fun μ : Module.Dual ℂ H => weight[(V ⧸ W), μ]) ∧
      ∀ μ : Module.Dual ℂ H,
        ∃ e : (weight[V, μ] ⧸ W.toSubmodule.comap (weight[V, μ]).subtype) ≃ₗ[ℂ]
                weight[(V ⧸ W), μ],
          ∀ x : weight[V, μ],
            (e (Submodule.Quotient.mk x) : V ⧸ W) = LieSubmodule.Quotient.mk' W (x : V)

end Specs.LieAlgebrasAndRepresentations.WeightSubmodules
