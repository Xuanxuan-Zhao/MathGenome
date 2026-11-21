import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CompactSpectral.SingularApproximation
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Trace class uses the canonical one-based ordered singular sequence.
No separability or nonzero-dimensional hypothesis is imposed. -/
noncomputable section
universe u v w z
namespace ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec
variable {𝕜 : Type u} [RCLike 𝕜]
  {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
  [CompleteSpace H] [CompleteSpace K]

abbrev singularSequence (T : H →L[𝕜] K) (n : ℕ) : ℝ :=
  CompactSpectral.SingularApproximation.Spec.SingularValueValue T (n + 1)

def IsTraceClassValue (T : H →L[𝕜] K) : Prop :=
  Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap ∧
    Summable (singularSequence T)

def TraceNormValue (T : H →L[𝕜] K) : ℝ := ∑' n, singularSequence T n

def RankOneValue (u : K) (v : H) : H →L[𝕜] K :=
  (innerSL 𝕜 v).smulRight u

def chosenBasisIndex : Set H := Classical.choose (exists_hilbertBasis 𝕜 H)

def chosenBasis : HilbertBasis (chosenBasisIndex (𝕜 := 𝕜) (H := H)) 𝕜 H :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis 𝕜 H))

def TraceValue (T : H →L[𝕜] H) : 𝕜 :=
  ∑' i, inner 𝕜 (chosenBasis (𝕜 := 𝕜) (H := H) i)
    (T (chosenBasis (𝕜 := 𝕜) (H := H) i))

def IsTraceClassType := ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
  [CompleteSpace H] [CompleteSpace K], (H →L[𝕜] K) → Prop

def TraceNormType := ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
  [CompleteSpace H] [CompleteSpace K], (H →L[𝕜] K) → ℝ

def RankOneType := ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K], K → H → (H →L[𝕜] K)

def TraceType := ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H], (H →L[𝕜] H) → 𝕜

/-- Absolute convergence and equality to a single trace for every Hilbert basis,
including bases with uncountable index sets. -/
def DiagonalTrace : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (T : H →L[𝕜] H),
    IsTraceClassValue T → ∀ (ι : Type z) (b : HilbertBasis ι 𝕜 H),
    Summable (fun i => ‖inner 𝕜 (b i) (T (b i))‖) ∧
    HasSum (fun i => inner 𝕜 (b i) (T (b i))) (TraceValue T)

/-- A bridge to every positive singular system, with no padding directions added
in either ambient space. -/
def SingularSystemSum : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    IsTraceClassValue T →
    ∀ S : CompactSpectral.SingularExpansion.Spec.SingularSystem 𝕜 H K T,
      Summable S.sigma ∧ ∑' j, S.sigma j = TraceNormValue T

def TraceBound : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (T : H →L[𝕜] H),
    IsTraceClassValue T → ‖TraceValue T‖ ≤ TraceNormValue T

def RankOneApplication : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K] (u : K) (v x : H),
    RankOneValue (𝕜 := 𝕜) u v x = inner 𝕜 v x • u

def RankOneTrace : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (u v : H),
    TraceValue (RankOneValue (𝕜 := 𝕜) u v) = inner 𝕜 v u

end ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec
