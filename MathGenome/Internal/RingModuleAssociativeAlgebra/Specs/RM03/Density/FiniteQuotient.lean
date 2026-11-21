import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Density.Action
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Topology.Constructions

universe u v

namespace RM03.Specs.Density

-- The ring and module universes are independent.
set_option linter.checkUnivs false in
def finiteTopologyType :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M],
    TopologicalSpace (RightEndValue R M)

/-- The right-linear endomorphisms carry the subspace topology from the product
of discrete copies of the underlying module. -/
def finiteTopologyValue : finiteTopologyType :=
  fun R M _ _ _ ↦
    letI : TopologicalSpace M := ⊥
    TopologicalSpace.induced (fun T : RightEndValue R M ↦ (T : M → M)) inferInstance

def finiteTopology_nhds_basisType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    (T : RightEndValue R M),
    letI : TopologicalSpace (RightEndValue R M) := finiteTopologyValue R M
    (nhds T).HasBasis Set.Finite (fun S : Set M ↦ {F | ∀ m ∈ S, F m = T m})

def action_agrees_on_finiteType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] (T : RightEndValue R M) (S : Set M), S.Finite →
    ∃ r : R, ∀ m ∈ S, actionValue R M r m = T m

def action_denseType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [IsSimpleModule R M],
    letI : TopologicalSpace (RightEndValue R M) := finiteTopologyValue R M
    Dense (Set.range (actionValue R M))

-- Finite generation for the evaluation action of End_R(M) on the left
-- is finite-dimensionality over its opposite division ring on the right.
def action_surjective_of_finiteType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] [Module.Finite (Module.End R M) M],
    Function.Surjective (actionValue R M)

def quotient_action_isomorphismType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] [Module.Finite (Module.End R M) M],
    ∃ e : (R ⧸ Module.annihilator R M) ≃+* RightEndValue R M,
      ∀ r : R, e (Ideal.Quotient.mk (Module.annihilator R M) r) = actionValue R M r

end RM03.Specs.Density
