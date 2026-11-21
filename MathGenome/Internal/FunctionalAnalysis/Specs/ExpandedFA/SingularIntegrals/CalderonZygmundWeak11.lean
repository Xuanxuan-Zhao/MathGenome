import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.StandardConvolutionOperator
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.CalderonZygmundDecomposition
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Independent full endpoint obligation for `fa2:p4:calderon-zygmund`.
The only operator assumptions are those in the upstream standard-kernel setting.
In particular neither a weak bound nor a nonsmooth kernel formula is assumed.
All dimensions and both scalar fields are retained. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace ExpandedFA.SingularIntegrals.CZWeak
open StandardConvolution

abbrev L1 (𝕜 : Type) [RCLike 𝕜] (d : ℕ) := Lp 𝕜 1 (volume : Measure (Space d))
abbrev MeasurableClasses (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :=
  Space d →ₘ[(volume : Measure (Space d))] 𝕜

/-- Center of the actual upstream half-open dyadic cube. -/
def cubeCenter {d : ℕ} (q : CZ.DyadicCube d) : Space d :=
  WithLp.toLp 2 (fun i => CZ.side q * ((q.2 i : ℝ) + 1 / 2))

/-- A positive radius dominating the half diagonal, also in dimension zero. -/
def cubeRadius {d : ℕ} (q : CZ.DyadicCube d) : ℝ :=
  Real.sqrt (d + 1) * CZ.side q

/-- Fixed dimension-dependent coordinate dilation of the bad cube. -/
def enlargedCube {d : ℕ} (q : CZ.DyadicCube d) : Set (Space d) :=
  {x | ∀ i, |x i - cubeCenter q i| ≤ 2 * cubeRadius q}

/-- Weak (1,1) on the original L¹ ∩ L² domain, with a single finite constant. -/
def WeakOneOnCore {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (T : StandardConvolutionOperator 𝕜 d) (C : ℝ) : Prop :=
  ∀ (f : Space d → 𝕜), Integrable f → ∀ h2 : MemLp f 2,
    ∀ t : ℝ, 0 < t →
      volume {x | t < ‖T.operator (h2.toLp f) x‖} ≤
        ENNReal.ofReal (C / t) * eLpNorm f 1 volume

/-- Measurable outputs are a.e. classes, so uniqueness has its usual meaning.
The weak estimate is required on every L¹ input, with no support restriction. -/
def IsCompatibleExtension {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (T : StandardConvolutionOperator 𝕜 d)
    (S : L1 𝕜 d →ₗ[𝕜] MeasurableClasses 𝕜 d) : Prop :=
  (∀ (f : Space d → 𝕜) (h1 : MemLp f 1) (h2 : MemLp f 2),
    (S (h1.toLp f) : Space d → 𝕜) =ᵐ[volume]
      (T.operator (h2.toLp f) : Space d → 𝕜)) ∧
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : L1 𝕜 d) (t : ℝ), 0 < t →
    volume {x | t < ‖S f x‖} ≤ ENNReal.ofReal (C / t) * ENNReal.ofReal ‖f‖

end ExpandedFA.SingularIntegrals.CZWeak

namespace Specs.ExpandedFA.SingularIntegrals.CalderonZygmundWeak11
open _root_.ExpandedFA.SingularIntegrals
open StandardConvolution CZWeak

/-- Integrated cancellation, uniform in the size and location of the cube and
in its zero-mean L¹ ∩ L² input. Integrability is explicit. -/
def IntegratedCancellation : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (T : StandardConvolutionOperator 𝕜 d),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : CZ.DyadicCube d) (b : Space d → 𝕜),
      Integrable b → ∀ h2 : MemLp b 2,
        SupportedAE b (CZ.cube q) → (∫ x, b x) = 0 →
          IntegrableOn (fun x => ‖T.operator (h2.toLp b) x‖) (enlargedCube q)ᶜ ∧
          (∫ x in (enlargedCube q)ᶜ, ‖T.operator (h2.toLp b) x‖) ≤
            C * ∫ x, ‖b x‖

def WeakCore : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (T : StandardConvolutionOperator 𝕜 d),
    ∃ C : ℝ, 0 ≤ C ∧ WeakOneOnCore T C

def UniqueExtension : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (T : StandardConvolutionOperator 𝕜 d),
    ∃! S : L1 𝕜 d →ₗ[𝕜] MeasurableClasses 𝕜 d, IsCompatibleExtension T S

/-- Uniqueness is separated from existence for incremental verification. -/
def ExtensionUniqueness : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (T : StandardConvolutionOperator 𝕜 d)
    (S S' : L1 𝕜 d →ₗ[𝕜] MeasurableClasses 𝕜 d),
      IsCompatibleExtension T S → IsCompatibleExtension T S' → S = S'

/-- The pointwise smoothness estimate needed to integrate cancellation. -/
def KernelDifference : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (k : StandardKernel 𝕜 d)
    (a h : Space d), a ≠ 0 → ‖h‖ ≤ ‖a‖ / 2 →
      ‖k.function (a - h) - k.function a‖ ≤
        ((d : ℝ) * k.constant * 2 ^ (d + 1)) * ‖h‖ / ‖a‖ ^ (d + 1)

end Specs.ExpandedFA.SingularIntegrals.CalderonZygmundWeak11
