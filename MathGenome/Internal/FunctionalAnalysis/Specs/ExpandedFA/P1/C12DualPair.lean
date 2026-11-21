import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.RCLike.Basic

/-!
Independent specifications for Definition `fa2:p1:c12:dual-pair`, paper.tex 2240–2254.
`B y x` is bilinear over the original scalar field, including over ℂ.
The native weak space is `WeakBilin B.flip`. No topology or norm on X or Y
is assumed. These constructions and basis formulas also work for nonseparating
pairings, so in particular for all the separating pairings of the manuscript.
A finite set of tests is equivalent to a finite list (repetitions have no effect);
the empty finite set gives the whole space. The scalar norm means |·| on ℝ
and modulus on ℂ. Topology order is Lean's reverse order on open sets.
-/

namespace ExpandedFA.P1.C12DualPairSpec

universe u v w
open scoped Topology
noncomputable section

def DualPairEquivType :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜), X ≃ₗ[𝕜] WeakBilin B.flip

def DualPairEquivValue : DualPairEquivType :=
  fun 𝕜 X _ _ _ _ _ _ _ => LinearEquiv.refl 𝕜 X

def DualPairTopologyType :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (_B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜), TopologicalSpace X

def DualPairTopologyValue : DualPairTopologyType :=
  fun 𝕜 X Y _ _ _ _ _ B => TopologicalSpace.induced
    (DualPairEquivValue 𝕜 X Y B) (WeakBilin.instTopologicalSpace B.flip)

def PairNeighborhoodType :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (_B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜), X → Finset Y → ℝ → Set X

def PairNeighborhoodValue : PairNeighborhoodType :=
  fun _ X _ _ _ _ _ _ B x₀ s ε => {x : X | ∀ y ∈ s, ‖B y (x - x₀)‖ < ε}

def EquivIdentity : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜) (x : X), (DualPairEquivValue 𝕜 X Y B x : X) = x

def Initial : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜),
    DualPairTopologyValue 𝕜 X Y B =
      ⨅ y : Y, TopologicalSpace.induced (fun x : X => B y x) inferInstance

def Coarsest : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜) (t : TopologicalSpace X),
    (∀ y : Y, @Continuous X 𝕜 t inferInstance (fun x => B y x)) ↔
      t ≤ DualPairTopologyValue 𝕜 X Y B

def NeighborhoodBasis : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜) (x₀ : X),
    (@nhds X (DualPairTopologyValue 𝕜 X Y B) x₀).HasBasis
      (fun p : Finset Y × ℝ => 0 < p.2)
      (fun p => PairNeighborhoodValue 𝕜 X Y B x₀ p.1 p.2)

def OpenCharacterization : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜) (U : Set X),
    @IsOpen X (DualPairTopologyValue 𝕜 X Y B) U ↔
      ∀ x₀ ∈ U, ∃ (s : Finset Y) (ε : ℝ), 0 < ε ∧
        PairNeighborhoodValue 𝕜 X Y B x₀ s ε ⊆ U

def EmptyNeighborhood : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜) (x₀ : X) (ε : ℝ),
    PairNeighborhoodValue 𝕜 X Y B x₀ ∅ ε = Set.univ

/-- Positive finite-test neighborhoods form a basis of open sets; equivalently,
the topology consists of their arbitrary unions. -/
def OpenBasis : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜),
    @TopologicalSpace.IsTopologicalBasis X (DualPairTopologyValue 𝕜 X Y B)
      {U | ∃ (x₀ : X) (s : Finset Y) (ε : ℝ), 0 < ε ∧
        U = PairNeighborhoodValue 𝕜 X Y B x₀ s ε}

/-- The norm-continuous dual is fixed before changing the topology on E. -/
def EvaluationCompatibility : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E) =
      ⨅ f : E →L[𝕜] 𝕜, TopologicalSpace.induced (fun x : E => f x) inferInstance

/-- The same identity equivalence has exactly the native WeakSpace topology. -/
def WeakSpaceCompatibility : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E) =
      TopologicalSpace.induced (toWeakSpace 𝕜 E) (instTopologicalSpaceWeakSpace 𝕜 E)

end
end ExpandedFA.P1.C12DualPairSpec
