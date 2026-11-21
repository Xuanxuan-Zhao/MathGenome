import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.WeakVolterraBounds
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Independent obligations for the power-kernel resolvent and constant datum
in `fa2:p5:weak-volterra`. Index n below denotes the kernel of V^(n+1).
No kernel identity or regularity certificate is assumed in the final statements.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace ExpandedFA.PartV.WeakVolterraResolvent.Spec
open ExpandedFA.PartV.FractionalIntegrals.Spec
open ExpandedFA.PartV.WeakVolterraBounds.Spec

/-- Successive triangular convolution of the actual unnormalized kernel. -/
def iteratedKernel {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (α : ℝ)
    (k : C(triangle T, 𝕜)) : ℕ → ℝ → ℝ → 𝕜
  | 0, t, s => (t-s) ^ (α-1) • amplitudeValue k t s
  | n+1, t, s => ∫ v in Ioc s t,
      (t-v) ^ (α-1) • (amplitudeValue k t v * iteratedKernel α k n v s)

/-- The normalized extension on the diagonal is k for the first iterate and
zero for all subsequent iterates. Its continuity is a theorem, not a definition. -/
def normalizedAmplitude {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (α : ℝ)
    (k : C(triangle T, 𝕜)) (n : ℕ) (z : triangle T) : 𝕜 :=
  match n with
  | 0 => k z
  | n+1 => if z.val.2 < z.val.1 then
      (z.val.1-z.val.2) ^ (1-α) • iteratedKernel α k (n+1) z.val.1 z.val.2 else 0

def kernelBound (α M : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  M ^ (n+1) * Real.Gamma α ^ (n+1) * r ^ (((n+1 : ℕ) : ℝ)*α-1) /
    Real.Gamma (((n+1 : ℕ) : ℝ)*α)

def amplitudeBound (α T M : ℝ) (n : ℕ) : ℝ :=
  M ^ (n+1) * Real.Gamma α ^ (n+1) * T ^ ((n : ℝ)*α) /
    Real.Gamma (((n+1 : ℕ) : ℝ)*α)

def KernelRegularity : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ), 0 < α → 0 ≤ T → ∀ (k : C(triangle T, 𝕜))
    (M : ℝ), 0 ≤ M → (∀ z, ‖k z‖ ≤ M) →
    (∀ n, Continuous (normalizedAmplitude α k n)) ∧
    (∀ n z, ‖normalizedAmplitude α k n z‖ ≤ amplitudeBound α T M n) ∧
    (∀ n (t s : ℝ), 0 ≤ s → s < t → t ≤ T →
      ‖iteratedKernel α k n t s‖ ≤ kernelBound α M n (t-s)) ∧
    (∀ n (t s : ℝ), 0 ≤ s → s < t → t ≤ T →
      IntegrableOn (fun v => (t-v) ^ (α-1) •
        (amplitudeValue k t v * iteratedKernel α k n v s)) (Ioc s t))

/-- A single kernel q for every function-space realization. -/
def KernelSeries {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (α : ℝ)
    (k : C(triangle T, 𝕜)) (ζ : 𝕜) (q : C(triangle T, 𝕜)) : Prop :=
  (∀ z, HasSum (fun n : ℕ => ζ^(n+1) * normalizedAmplitude α k n z) (q z)) ∧
  TendstoUniformly
    (fun N z => ∑ n ∈ Finset.range N, ζ^(n+1) * normalizedAmplitude α k n z)
    q atTop ∧
  (∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T),
    q ⟨(t,t), ht.1, le_rfl, ht.2⟩ = ζ * k ⟨(t,t), ht.1, le_rfl, ht.2⟩) ∧
  (∀ (t s : ℝ) (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T),
    HasSum (fun n : ℕ => ζ^(n+1) * iteratedKernel α k n t s)
      ((t-s) ^ (α-1) • q ⟨(t,s), hs, hst.le, ht⟩))

def ContinuousRealizes {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (hT : 0 ≤ T)
    (α : ℝ) (k : C(triangle T, 𝕜))
    (V : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜)) : Prop :=
  ∀ f t, V f t = weakValue α k (continuousExtension hT f) t

def LpRealizes {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (α : ℝ)
    (k : C(triangle T, 𝕜)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (V : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T)) : Prop :=
  ∀ (f : ℝ → 𝕜) (hf : MemLp f p (intervalMeasure T)),
    (V (hf.toLp f) : ℝ → 𝕜) =ᵐ[intervalMeasure T] weakValue α k f

/-- Powers are represented by the recursively specified iterated kernels. -/
def IterateRepresentation : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ), 0 < α → ∀ hT : 0 ≤ T, ∀ k : C(triangle T, 𝕜),
    (∀ V, ContinuousRealizes hT α k V → ∀ n f (t : Icc (0 : ℝ) T),
      IntegrableOn (fun s => iteratedKernel α k n t s * continuousExtension hT f s)
        (Ioc 0 (t : ℝ)) ∧
      (V^(n+1)) f t = ∫ s in Ioc 0 (t : ℝ),
        iteratedKernel α k n t s * continuousExtension hT f s) ∧
    (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] V, LpRealizes α k p V →
      ∀ n (f : ℝ → 𝕜) (hf : MemLp f p (intervalMeasure T)),
        (∀ᵐ t ∂intervalMeasure T,
          IntegrableOn (fun s => iteratedKernel α k n t s * f s) (Ioc 0 t)) ∧
        ((V^(n+1)) (hf.toLp f) : ℝ → 𝕜) =ᵐ[intervalMeasure T]
          fun t => ∫ s in Ioc 0 t, iteratedKernel α k n t s * f s)

/-- The common resolvent is both a two-sided inverse and the displayed
integral, pointwise on C and for every representative a.e. on Lp. -/
def ResolventRepresentation : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ), 0 < α → ∀ hT : 0 ≤ T,
    ∀ (k : C(triangle T, 𝕜)) (M : ℝ), 0 ≤ M → (∀ z, ‖k z‖ ≤ M) →
    ∀ ζ : 𝕜, ∃ q : C(triangle T, 𝕜), KernelSeries α k ζ q ∧
    (∀ V, ContinuousRealizes hT α k V →
      ∃ R : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜),
        (1-ζ • V)*R = 1 ∧ R*(1-ζ • V) = 1 ∧ ∀ f (t : Icc (0 : ℝ) T),
        IntegrableOn (weakIntegrand α q (continuousExtension hT f) t) (Ioc 0 (t : ℝ)) ∧
        R f t = f t + weakValue α q (continuousExtension hT f) t) ∧
    (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] V, LpRealizes α k p V →
      ∃ R : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T),
        (1-ζ • V)*R = 1 ∧ R*(1-ζ • V) = 1 ∧
        ∀ (f : ℝ → 𝕜) (hf : MemLp f p (intervalMeasure T)),
          (∀ᵐ t ∂intervalMeasure T, IntegrableOn (weakIntegrand α q f t) (Ioc 0 t)) ∧
          (R (hf.toLp f) : ℝ → 𝕜) =ᵐ[intervalMeasure T]
            fun t => f t + weakValue α q f t)

/-- The n=0 power is one also when t=0. -/
def mittagTerm {𝕜 : Type} [RCLike 𝕜] (α : ℝ) (ζ : 𝕜) (n : ℕ) (t : ℝ) : 𝕜 :=
  (t ^ ((n : ℝ)*α) / Real.Gamma ((n : ℝ)*α+1)) • ζ^n

def MittagLeffler : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ), 0 < α → ∀ hT : 0 ≤ T, ∀ ζ : 𝕜,
    ∃ u : C(Icc (0 : ℝ) T, 𝕜),
      (∀ t : Icc (0 : ℝ) T, HasSum (fun n => mittagTerm α ζ n t) (u t)) ∧
      TendstoUniformly (fun N (t : Icc (0 : ℝ) T) => ∑ n ∈ Finset.range N, mittagTerm α ζ n t) u atTop ∧
      (∀ t, u t = 1 + ζ * fractionalValue α (continuousExtension hT u) t) ∧
      (∀ v : C(Icc (0 : ℝ) T, 𝕜),
        (∀ t, v t = 1 + ζ * fractionalValue α (continuousExtension hT v) t) → v = u) ∧
      (∀ t : Icc (0 : ℝ) T, (t : ℝ) = 0 → u t = 1)

end ExpandedFA.PartV.WeakVolterraResolvent.Spec
