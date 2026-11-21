import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.TraceClassDefinitions

/-! Trace-normed ideal, including the zero and nonseparable Hilbert spaces.
Completeness is expressed by the Cauchy criterion for the trace-norm distance. -/
noncomputable section
universe u v w v₀ w₀
namespace ExpandedFA.TraceIdeals.TraceNormIdeal.Spec
open TraceClassDefinitions.Spec
open scoped Topology

/-- All norm axioms on the original trace-class operators, with closure under
addition and scalar multiplication. -/
def NormedIdealAxioms : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K],
  IsTraceClassValue (0 : H →L[𝕜] K) ∧ TraceNormValue (0 : H →L[𝕜] K) = 0 ∧
  (∀ T : H →L[𝕜] K, IsTraceClassValue T →
    0 ≤ TraceNormValue T ∧ (TraceNormValue T = 0 ↔ T = 0) ∧ ‖T‖ ≤ TraceNormValue T) ∧
  (∀ (S T : H →L[𝕜] K), IsTraceClassValue S → IsTraceClassValue T →
    IsTraceClassValue (S + T) ∧ TraceNormValue (S + T) ≤ TraceNormValue S + TraceNormValue T) ∧
  (∀ (c : 𝕜) (T : H →L[𝕜] K), IsTraceClassValue T →
    IsTraceClassValue (c • T) ∧ TraceNormValue (c • T) = ‖c‖ * TraceNormValue T)

def TraceNormComplete : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K],
  ∀ T : ℕ → H →L[𝕜] K, (∀ n, IsTraceClassValue (T n)) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      TraceNormValue (T m - T n) < ε) →
    ∃ L : H →L[𝕜] K, IsTraceClassValue L ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, TraceNormValue (T n - L) < ε

def FiniteRankDense : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K],
  ∀ T : H →L[𝕜] K, IsTraceClassValue T → ∀ ε : ℝ, 0 < ε →
    ∃ F : H →L[𝕜] K, FiniteDimensional 𝕜 F.range ∧ IsTraceClassValue F ∧
      IsTraceClassValue (T - F) ∧ TraceNormValue (T - F) < ε

/-- This optional characterization also gives the lower semicontinuity needed
for completeness. The bound applies to arbitrary finite orthonormal pairs. -/
def FiniteFamilyCharacterization : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K],
  ∀ T : H →L[𝕜] K,
    Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ C : ℝ, 0 ≤ C →
      ((IsTraceClassValue T ∧ TraceNormValue T ≤ C) ↔
        ∀ (n : ℕ) (a : Fin n → K) (b : Fin n → H),
          Orthonormal 𝕜 a → Orthonormal 𝕜 b →
          ∑ i, ‖inner 𝕜 (a i) (T (b i))‖ ≤ C)

/-- Every bounded finite-rank operator belongs to the ideal. -/
def FiniteRankTraceClass : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K],
    ∀ F : H →L[𝕜] K, FiniteDimensional 𝕜 F.range → IsTraceClassValue F

/-- Both external factors have arbitrary compatible Hilbert source/target. -/
def TwoSidedIdeal : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    (H₀ : Type v₀) (K₀ : Type w₀)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [NormedAddCommGroup H₀] [NormedAddCommGroup K₀]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [InnerProductSpace 𝕜 H₀] [InnerProductSpace 𝕜 K₀]
    [CompleteSpace H] [CompleteSpace K] [CompleteSpace H₀] [CompleteSpace K₀]
    (T : H →L[𝕜] K) (A : K →L[𝕜] K₀) (B : H₀ →L[𝕜] H),
    IsTraceClassValue T → IsTraceClassValue (A.comp (T.comp B)) ∧
      TraceNormValue (A.comp (T.comp B)) ≤ ‖A‖ * TraceNormValue T * ‖B‖

end ExpandedFA.TraceIdeals.TraceNormIdeal.Spec
