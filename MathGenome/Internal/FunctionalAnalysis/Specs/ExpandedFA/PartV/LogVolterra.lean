import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.WeakVolterraResolvent

/-! The separate logarithmic clause of `fa2:p5:weak-volterra`.
The iterates below use log itself, not a power-kernel surrogate. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace ExpandedFA.PartV.LogVolterra.Spec
open ExpandedFA.PartV.FractionalIntegrals.Spec
open ExpandedFA.PartV.WeakVolterraBounds.Spec

def logKernel {𝕜 : Type} [RCLike 𝕜] {T : ℝ}
    (k : C(triangle T, 𝕜)) (t s : ℝ) : 𝕜 :=
  Real.log (t-s) • amplitudeValue k t s

def logIntegrand {𝕜 : Type} [RCLike 𝕜] {T : ℝ}
    (k : C(triangle T, 𝕜)) (f : ℝ → 𝕜) (t s : ℝ) : 𝕜 :=
  logKernel k t s * f s

def logValue {𝕜 : Type} [RCLike 𝕜] {T : ℝ}
    (k : C(triangle T, 𝕜)) (f : ℝ → 𝕜) (t : ℝ) : 𝕜 :=
  ∫ s in Ioc 0 t, logIntegrand k f t s

/-- Index n is the kernel of V^(n+1). -/
def logIterate {𝕜 : Type} [RCLike 𝕜] {T : ℝ}
    (k : C(triangle T, 𝕜)) : ℕ → ℝ → ℝ → 𝕜
  | 0, t, s => logKernel k t s
  | n+1, t, s => ∫ v in Ioc s t, logKernel k t v * logIterate k n v s

/-- A single kernel used by every realization and every majorant exponent. -/
def resolventKernel {𝕜 : Type} [RCLike 𝕜] {T : ℝ}
    (k : C(triangle T, 𝕜)) (ζ : 𝕜) (t s : ℝ) : 𝕜 :=
  ∑' n : ℕ, ζ^(n+1) * logIterate k n t s

def ZeroTime : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] {T : ℝ}
    (k : C(triangle T, 𝕜)) (f : ℝ → 𝕜), logValue k f 0 = 0

def ContinuousTheorem : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ) (hT : 0 ≤ T) (k : C(triangle T, 𝕜)),
    ∃ V : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜),
      (∀ f (t : Icc (0 : ℝ) T),
        IntegrableOn (logIntegrand k (continuousExtension hT f) t) (Ioc 0 (t : ℝ)) ∧
        V f t = logValue k (continuousExtension hT f) t) ∧
      IsCompactOperator V ∧ ResolventProperties V ∧ ∀ ζ : 𝕜,
      ∃ R : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜),
        (1-ζ • V)*R = 1 ∧ R*(1-ζ • V) = 1 ∧ ∀ f (t : Icc (0 : ℝ) T),
          IntegrableOn (fun s => resolventKernel k ζ t s * continuousExtension hT f s)
            (Ioc 0 (t : ℝ)) ∧
          R f t = f t + ∫ s in Ioc 0 (t : ℝ),
            resolventKernel k ζ t s * continuousExtension hT f s

def LpTheorem : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ), 0 ≤ T → ∀ k : C(triangle T, 𝕜),
    ∀ p : ℝ≥0∞, ∀ [Fact (1 ≤ p)],
    ∃ V : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T),
      (∀ (f : ℝ → 𝕜) (hf : MemLp f p (intervalMeasure T)),
        (∀ᵐ t ∂intervalMeasure T, IntegrableOn (logIntegrand k f t) (Ioc 0 t)) ∧
        (V (hf.toLp f) : ℝ → 𝕜) =ᵐ[intervalMeasure T] logValue k f) ∧
      IsCompactOperator V ∧ ResolventProperties V ∧ ∀ ζ : 𝕜,
      ∃ R : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T),
        (1-ζ • V)*R = 1 ∧ R*(1-ζ • V) = 1 ∧
        ∀ (f : ℝ → 𝕜) (hf : MemLp f p (intervalMeasure T)),
          (∀ᵐ t ∂intervalMeasure T,
            IntegrableOn (fun s => resolventKernel k ζ t s * f s) (Ioc 0 t)) ∧
          (R (hf.toLp f) : ℝ → 𝕜) =ᵐ[intervalMeasure T]
            fun t => f t + ∫ s in Ioc 0 t, resolventKernel k ζ t s * f s

/-- Uniform in s and t near the diagonal. The same kernel has the explicit
first logarithmic term for every 0 < ε < 1/2. This is stronger than just a
power bound on the entire kernel. -/
def LeadingTerm : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ), 0 ≤ T → ∀ (k : C(triangle T, 𝕜)) (ζ : 𝕜),
    (∀ (t s : ℝ), 0 ≤ s → s < t → t ≤ T →
      Summable (fun n : ℕ => ζ^(n+1) * logIterate k n t s)) ∧
    ∀ ε : ℝ, 0 < ε → ε < 1/2 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (t s : ℝ), 0 ≤ s → s < t → t ≤ T → t-s ≤ 1 →
        ‖resolventKernel k ζ t s - ζ * logKernel k t s‖ ≤ C * (t-s)^(1-2*ε)

end ExpandedFA.PartV.LogVolterra.Spec
