import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.LumerPhillips
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Monotone.Definitions

/-! Linear maximal monotone operators, paper.tex, fa2:p3:linear-monotone.
The original subspace domain is retained. The complex monotone graph is read
on the underlying real Hilbert space, with real part of the pairing. -/
noncomputable section
open Filter Topology Set
namespace ExpandedFA.Semigroups.LinearMaximalMonotoneSpec

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- I + rL on precisely D(L). -/
def plusMap (L : Unbounded.Operator 𝕜 H H) (r : ℝ) : L.domain →ₗ[𝕜] H :=
  L.domain.subtype + algebraMap ℝ 𝕜 r • L.toFun

/-- Two-point monotonicity, using the real pairing also for complex H. -/
def Monotone (L : Unbounded.Operator 𝕜 H H) : Prop :=
  ∀ x y : L.domain, 0 ≤ RCLike.re (inner 𝕜 (L x - L y) ((x : H) - y))

/-- Restrict scalar linearity, without changing either domain or values. -/
def realOperator (L : Unbounded.Operator 𝕜 H H) :
    letI := NormedSpace.restrictScalars ℝ 𝕜 H
    Unbounded.Operator ℝ H H := by
  letI := NormedSpace.restrictScalars ℝ 𝕜 H
  exact ⟨L.domain.restrictScalars ℝ, L.toFun.restrictScalars ℝ⟩

set_option linter.checkUnivs false

def MonotonicityBridge : Prop := ∀ {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (L : Unbounded.Operator 𝕜 H H),
  letI := NormedSpace.restrictScalars ℝ 𝕜 H
  letI := InnerProductSpace.rclikeToReal 𝕜 H
  Monotone L ↔ ExpandedFA.Monotone.Spec.MonotoneValue H
    (ExpandedFA.Monotone.Spec.HilbertGraphValue H ((realOperator L).graph : Set (H × H)))

/-- Full original conclusion, including both inverse laws, bounded Yosida
operators, norm and strong approximation, and density in the graph norm.
The maps at nonpositive parameters are immaterial to the right-hand limits. -/
def LinearMaximalMonotone : Prop := ∀ {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (L : Unbounded.Operator 𝕜 H H),
  Monotone L → Function.Surjective (plusMap L 1) →
  L.IsClosed ∧ Dense (L.domain : Set H) ∧
  (∀ r : ℝ, 0 < r → Function.Surjective (plusMap L r)) ∧
  (∃ J K : ℝ → H →L[𝕜] H,
    (∀ (r : ℝ) (hr : 0 < r),
      ∃ hm : ∀ x, J r x ∈ L.domain,
      (∀ x, (J r x : H) + algebraMap ℝ 𝕜 r • L ⟨J r x, hm x⟩ = x) ∧
      (∀ x : L.domain, J r (plusMap L r x) = (x : H)) ∧
      ‖J r‖ ≤ 1 ∧
      (∀ x, K r x = L ⟨J r x, hm x⟩) ∧
      (∀ x : L.domain, ‖K r x‖ ≤ ‖L x‖)) ∧
    (∀ x : H, Tendsto (fun r => J r x) (𝓝[>] (0 : ℝ)) (𝓝 x)) ∧
    (∀ x : L.domain, Tendsto (fun r => K r x) (𝓝[>] (0 : ℝ)) (𝓝 (L x)))) ∧
  (∀ (x : L.domain) (ε : ℝ), 0 < ε → ∃ y : L.domain,
    L y ∈ L.domain ∧ ‖(y : H) - x‖ + ‖L y - L x‖ < ε) ∧
  (∃ T : C0Semigroup 𝕜 H, C0SemigroupSpec.generatorValue T = -L ∧
    LumerPhillipsSpec.Contractive T)

end ExpandedFA.Semigroups.LinearMaximalMonotoneSpec
