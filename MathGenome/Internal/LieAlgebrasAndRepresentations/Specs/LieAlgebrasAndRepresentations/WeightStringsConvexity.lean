import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.HighestWeightClassification
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Sl2SimpleModules
import Mathlib.Analysis.Convex.Hull

/-! LA-G07, source lines 3375–3411. The convex hull uses real coefficients
in the complex Cartan dual, and the Weyl group acts by ordinary reflections. -/

noncomputable section
universe u v
open scoped Classical

namespace Specs.LieAlgebrasAndRepresentations.WeightStringsConvexity

open _root_.LieAlgebrasAndRepresentations.RepresentationJordan (weightSpace)
open RootDecomposition RootForm SolvableRadical MaximalTori
open Module FiniteModuleWeights Sl2Model Sl2SimpleModules
open VermaModules VermaWeightsUniversal SimpleHighestWeightQuotient
open HighestWeightData IntegrableHighestWeightQuotient
open SerreRelations (simple)
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The subspace spanned by the weight spaces in one integral root coset. -/
def cosetSpace {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (H : LieSubalgebra ℂ L)
    (μ α : Module.Dual ℂ H) : Submodule ℂ V :=
  ⨆ j : ℤ, weightSpace ρ H (μ + j • α)

/-- The summands are standard rank-one modules for the actual root triple.
Their bases exhibit the full Cartan weights and their reversal under reflection. -/
def root_coset_strings_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    IsSemisimple_value ℂ L →
    ∀ (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (H : LieSubalgebra ℂ L),
    IsMaximalToral_value H →
    ∀ (μ α : Module.Dual ℂ H), α ∈ rootSet_value H →
    ∃ e f : L, e ∈ rootSpace_value H α ∧ f ∈ rootSpace_value H (-α) ∧
      ⁅e, f⁆ = (coroot_value H α : L) ∧
    let K := cosetSpace ρ H μ α
    iSupIndep (fun j : ℤ => weightSpace ρ H (μ + j • α)) ∧
    ∃ σ : Model ℂ →ₗ⁅ℂ⁆ Module.End ℂ K,
      (∀ x : K, (σ (E ℂ) x : V) = ρ e x ∧
        (σ (F ℂ) x : V) = ρ f x ∧
        (σ (Sl2Model.H ℂ) x : V) = ρ (coroot_value H α : L) x) ∧
      letI := LieRingModule.compLieHom K σ
      letI := LieModule.compLieHom K σ
      ∃ S : Set (LieSubmodule ℂ (Model ℂ) K), S.Finite ∧
        DirectSum.IsInternal (fun W : S => W.val.toSubmodule) ∧
        ∀ W ∈ S, ∃ (n : ℕ) (b : Basis (Fin (n + 1)) ℂ W) (k : ℤ),
          IsStandardBasis b ∧ LieModule.IsIrreducible ℂ (Model ℂ) W ∧
          (∀ j : Fin (n + 1), ((b j : K) : V) ∈
            weightSpace ρ H (μ + (k - (j.val : ℤ)) • α)) ∧
          ∀ j : Fin (n + 1),
            weightReflection H α (μ + (k - (j.val : ℤ)) • α) =
              μ + (k - ((j.rev).val : ℤ)) • α

def multiplicities_type : Prop := multiplicities_weyl_invariant_type.{u,v}

def saturation_type : Prop := saturated_weights_type.{u,v}

/-- Every occurring weight of the canonical simple quotient of dominant
integral highest weight lies in the root-lattice coset and Weyl polytope. -/
def highest_weight_convex_bound_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ),
    IsWeightCharacter H φ lam χ → IsDominant H φ lam →
    letI := inducedLieRingModule H φ χ
    letI := inducedLieModule H φ χ
    ∀ μ : Module.Dual ℂ H, weightSpace_value (simpleQuotient_value H φ χ) H μ ≠ ⊥ →
      μ - lam ∈ integralRootLattice_value (fun i : simple H φ => i.val) ∧
      μ ∈ convexHull ℝ (Set.range fun w : weightWeylGroup H => w.val lam)

end Specs.LieAlgebrasAndRepresentations.WeightStringsConvexity
