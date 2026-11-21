import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Dual

/-!
Independent specification for Definition fa2:p1:c12:weak-star (paper.tex 2290–2306).
All duals below use the original norm topology before any topology is changed.
The native WeakDual and the weak topology of the normed dual are different
constructions. Lean orders topologies in reverse order of their open sets.
No completeness or nontriviality of E is assumed.
-/

namespace ExpandedFA.P1.C12WeakStar.Spec

universe u v w
open scoped Topology
noncomputable section

/-- Keep the original normed dual fixed, then equip its carrier with the
initial topology of evaluation at vectors of E. -/
def WeakStarTopologyType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E], TopologicalSpace (E →L[𝕜] 𝕜)

def WeakStarTopologyValue : WeakStarTopologyType :=
  fun 𝕜 E _ _ _ => C12DualPairSpec.DualPairTopologyValue 𝕜 (E →L[𝕜] 𝕜) E
    (topDualPairing 𝕜 E).flip

/-- The weak topology of the normed dual tests against its full norm bidual. -/
def DualWeakTopologyType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E], TopologicalSpace (E →L[𝕜] 𝕜)

def DualWeakTopologyValue : DualWeakTopologyType :=
  fun 𝕜 E _ _ _ => C12DualPairSpec.DualPairTopologyValue 𝕜 (E →L[𝕜] 𝕜)
    ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) (topDualPairing 𝕜 (E →L[𝕜] 𝕜))

def NeighborhoodType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    (E →L[𝕜] 𝕜) → Finset E → ℝ → Set (E →L[𝕜] 𝕜)

def NeighborhoodValue : NeighborhoodType :=
  fun 𝕜 E _ _ _ f₀ s ε => {f : E →L[𝕜] 𝕜 | ∀ x ∈ s, ‖(f - f₀) x‖ < ε}

def PairingCompatibility : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C12DualPairSpec.DualPairTopologyValue 𝕜 (E →L[𝕜] 𝕜) E
      (topDualPairing 𝕜 E).flip =
      WeakStarTopologyValue 𝕜 E

def NativeCompatibility : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    WeakStarTopologyValue 𝕜 E =
      TopologicalSpace.induced
        (StrongDual.toWeakDual : (E →L[𝕜] 𝕜) ≃ₗ[𝕜] WeakDual 𝕜 E)
        (instTopologicalSpaceWeakDual 𝕜 E)

def Initial : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    WeakStarTopologyValue 𝕜 E =
      ⨅ x : E, TopologicalSpace.induced (fun f : E →L[𝕜] 𝕜 => f x) inferInstance

def Coarsest : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (t : TopologicalSpace (E →L[𝕜] 𝕜)),
    (∀ x : E, @Continuous (E →L[𝕜] 𝕜) 𝕜 t inferInstance (fun f => f x)) ↔
      t ≤ WeakStarTopologyValue 𝕜 E

def NeighborhoodBasis : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (f₀ : E →L[𝕜] 𝕜),
    (@nhds (E →L[𝕜] 𝕜)
      (WeakStarTopologyValue 𝕜 E) f₀).HasBasis
      (fun p : Finset E × ℝ => 0 < p.2)
      (fun p => NeighborhoodValue 𝕜 E f₀ p.1 p.2)

def OpenCharacterization : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (U : Set (E →L[𝕜] 𝕜)),
    @IsOpen (E →L[𝕜] 𝕜)
      (WeakStarTopologyValue 𝕜 E) U ↔
      ∀ f₀ ∈ U, ∃ (s : Finset E) (ε : ℝ), 0 < ε ∧
        NeighborhoodValue 𝕜 E f₀ s ε ⊆ U

def OpenBasis : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    @TopologicalSpace.IsTopologicalBasis (E →L[𝕜] 𝕜)
      (WeakStarTopologyValue 𝕜 E)
      {U | ∃ (f₀ : E →L[𝕜] 𝕜) (s : Finset E) (ε : ℝ), 0 < ε ∧
        U = NeighborhoodValue 𝕜 E f₀ s ε}

def EmptyNeighborhood : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (f₀ : E →L[𝕜] 𝕜) (ε : ℝ),
    NeighborhoodValue 𝕜 E f₀ ∅ ε = Set.univ

/-- The tests here range over the continuous bidual, with the normed dual as domain. -/
def DualWeakInitial : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    DualWeakTopologyValue 𝕜 E =
      ⨅ Φ : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜, TopologicalSpace.induced Φ inferInstance

/-- This is the displayed inclusion chain, written in Lean's reversed order. -/
def TopologyInclusions : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    (inferInstance : TopologicalSpace (E →L[𝕜] 𝕜)) ≤
      DualWeakTopologyValue 𝕜 E ∧
    DualWeakTopologyValue 𝕜 E ≤
      WeakStarTopologyValue 𝕜 E

/-- Explicit inclusion of open sets avoids ambiguity about the topology order. -/
def OpenInclusions : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (U : Set (E →L[𝕜] 𝕜)),
    (@IsOpen _ (WeakStarTopologyValue 𝕜 E) U →
      @IsOpen _ (DualWeakTopologyValue 𝕜 E) U) ∧
    (@IsOpen _ (DualWeakTopologyValue 𝕜 E) U →
      IsOpen U)

/-- A specified predual consists of a normed E and an explicit dual identification.
The identification is retained as data, not merely an existence proposition.
We allow any scalar-linear identification; norm-isometric identifications in
particular supply this data without additional assumptions on E or F. -/
def PredualIdentificationType :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F], Type (max u v w)

def PredualIdentificationValue : PredualIdentificationType :=
  fun 𝕜 E F _ _ _ _ _ => (E →L[𝕜] 𝕜) ≃ₗ[𝕜] F

def PredualPairingType :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F],
    PredualIdentificationValue 𝕜 E F → E →ₗ[𝕜] F →ₗ[𝕜] 𝕜

def PredualPairingValue : PredualPairingType :=
  fun 𝕜 E _ _ _ _ _ _ I => (topDualPairing 𝕜 E).flip.compl₂ I.symm.toLinearMap

def PredualTopologyType :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F],
    PredualIdentificationValue 𝕜 E F → TopologicalSpace F

def PredualTopologyValue : PredualTopologyType :=
  fun 𝕜 E F _ _ _ _ _ I => C12DualPairSpec.DualPairTopologyValue 𝕜 F E
    (PredualPairingValue 𝕜 E F I)

def PredualEvaluation : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F]
    (I : PredualIdentificationValue 𝕜 E F) (x : E) (f : F),
    PredualPairingValue 𝕜 E F I x f = I.symm f x

def PredualInitial : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F]
    (I : PredualIdentificationValue 𝕜 E F),
    PredualTopologyValue 𝕜 E F I =
      ⨅ x : E, TopologicalSpace.induced (fun f : F => I.symm f x) inferInstance

/-- The specified identification transports the canonical weak-star topology. -/
def PredualTransport : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F]
    (I : PredualIdentificationValue 𝕜 E F),
    PredualTopologyValue 𝕜 E F I = TopologicalSpace.induced I.symm
      (WeakStarTopologyValue 𝕜 E)

end
end ExpandedFA.P1.C12WeakStar.Spec
