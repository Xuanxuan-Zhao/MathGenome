import MathGenome.Internal.Specs.D05.M07.Annihilator
import MathGenome.Internal.Specs.D05.M07.Biddual

/-!
Independent specifications for K05.07.double_annihilator, paper.tex:1075–1081.

All duals are algebraic linear maps over the given field. The preannihilator
uses the same span-of-a-set convention as K05.07.annihilator. In the bidual
identity the subspace of V is transported by the canonical evaluation map;
subspaces in different ambient spaces are never equated directly. Finite
dimension is assumed only of V, and includes the zero space.
-/

namespace Specs.D05.M07.DoubleAnnihilator

/-- The preannihilator in V of the annihilator of U is exactly U. -/
def double_annihilator : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (U : Submodule K V),
    (Submodule.span K (U.dualAnnihilator : Set (Module.Dual K V))).dualCoannihilator = U

/-- The evaluation map carries membership in U to double annihilation in V**. -/
def evaluation_mem_iff : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (U : Submodule K V) (v : V),
    Module.Dual.eval K V v ∈ U.dualAnnihilator.dualAnnihilator ↔ v ∈ U

/-- The annihilator in V** equals the image of U under canonical evaluation. -/
def bidual_annihilator : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (U : Submodule K V),
    U.dualAnnihilator.dualAnnihilator = U.map (Module.Dual.eval K V)

end Specs.D05.M07.DoubleAnnihilator
