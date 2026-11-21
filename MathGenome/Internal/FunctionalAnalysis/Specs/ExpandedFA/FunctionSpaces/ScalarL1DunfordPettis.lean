import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.WeakL1UniformIntegrability
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar

/-!
Independent statements for `fa2:p4:dunford-pettis-l1`, paper.tex:16982–17019.
The ambient scalar field is real or complex. The two uniform integral
conditions are stated in epsilon form, so empty sets of functions are included.
Compactness refers to the closure in the weak topology of the original
normed L¹ space. The auxiliary closure statement uses the scalar-linear,
unconjugated integration embedding into (L∞)′.
-/
open MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace ExpandedFA.FunctionSpaces.ScalarL1DunfordPettisSpec

open WeakL1UniformIntegrabilitySpec

abbrev weakTopology {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) : TopologicalSpace (Lp 𝕜 1 μ) :=
  ExpandedFA.P1.C12DualPairSpec.DualPairTopologyValue 𝕜 (Lp 𝕜 1 μ)
    (Lp 𝕜 1 μ →L[𝕜] 𝕜) (topDualPairing 𝕜 (Lp 𝕜 1 μ))

def RelativelyWeaklyCompact {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) (A : Set (Lp 𝕜 1 μ)) : Prop :=
  @IsCompact _ (weakTopology μ) (@closure _ (weakTopology μ) A)

def UniformIntegralControls {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) (A : Set (Lp 𝕜 1 μ)) : Prop :=
  Controls μ (fun f : A => (f.val : X → 𝕜))

def BoundedAndUniformlyIntegrable {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) (A : Set (Lp 𝕜 1 μ)) : Prop :=
  Bornology.IsBounded A ∧ UniformIntegralControls μ A

/-- Full scalar Dunford–Pettis criterion, including both integral conditions. -/
def DunfordPettis : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ] (A : Set (Lp 𝕜 1 μ)),
    RelativelyWeaklyCompact μ A ↔ BoundedAndUniformlyIntegrable μ A

def Necessity : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ] (A : Set (Lp 𝕜 1 μ)),
    RelativelyWeaklyCompact μ A → BoundedAndUniformlyIntegrable μ A

def Sufficiency : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ] (A : Set (Lp 𝕜 1 μ)),
    BoundedAndUniformlyIntegrable μ A → RelativelyWeaklyCompact μ A

/-- f ↦ (h ↦ ∫ h*f), the shared upstream scalar-linear pairing. -/
abbrev integrationEmbedding {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) :=
  ScalarLpIntegralPairingSpec.IntegralPairingValue (𝕜 := 𝕜) μ ∞ 1

/-- Indicator of a measurable set as an ordinary L∞ class; no finite-mass
assumption on the set is needed. -/
def unitIndicator {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (E : Set X) (hE : MeasurableSet E) : Lp 𝕜 ∞ μ :=
  (memLp_top_of_bound
    (aestronglyMeasurable_const.indicator hE) 1
    (Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ E <;> simp [hx]))).toLp (E.indicator fun _ => (1 : 𝕜))

/-- Sequential order continuity on measurable indicators. -/
def IndicatorOrderContinuous {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X)
    (L : Lp 𝕜 ∞ μ →L[𝕜] 𝕜) : Prop :=
  ∀ (E : ℕ → Set X) (hE : ∀ n, MeasurableSet (E n)), Antitone E →
    μ (⋂ n, E n) = 0 →
    Filter.Tendsto (fun n => L (unitIndicator μ (E n) (hE n))) Filter.atTop
      (nhds 0)

/-- The weak-star closure consists of actual ordinary L¹ densities. -/
def WeakStarClosureDensities : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ] (A : Set (Lp 𝕜 1 μ)),
    BoundedAndUniformlyIntegrable μ A →
    ∀ L ∈ @closure _
      (ExpandedFA.P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (Lp 𝕜 ∞ μ))
      (integrationEmbedding μ '' A),
      ∃ g : Lp 𝕜 1 μ, ∀ h : Lp 𝕜 ∞ μ, L h = ∫ x, h x * g x ∂μ

end ExpandedFA.FunctionSpaces.ScalarL1DunfordPettisSpec
