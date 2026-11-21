import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.AtomicHardySpace
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.CalderonZygmundWeak11

/-! The CZ endpoint clause of `fa2:p4:hardy-atomic`, including the agreement
with the weak (1,1) extension in its proof. Both scalar fields and every
Euclidean dimension are included. The explicit constant is allowed to be
nonoptimal and depends only on dimension and the kernel/L² bounds. -/
noncomputable section
open MeasureTheory

namespace ExpandedFA.Hardy.HardyCZEndpointSpec
open SingularIntegrals StandardConvolution CZWeak AtomicHardySpaceSpec

abbrev Atoms (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :=
  AtomValue (𝕜 := 𝕜) (volume : Measure (Space d))
abbrev Hardy (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :=
  HardyValue (𝕜 := 𝕜) (volume : Measure (Space d))

def endpointConstant {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (T : StandardConvolutionOperator 𝕜 d) : ℝ :=
  (2 : ℝ) ^ d + ‖T.operator‖ ^ 2 +
    (((d : ℝ) * T.kernel.constant * 2 ^ (d + 1)) *
      ((d : ℝ) * volume.real (Metric.ball (0 : Space d) 1)) / 2)

/-- The L² realization of each original L∞ atom has an integrable image,
uniformly over all radii and centers. -/
def AtomEstimate : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (T : StandardConvolutionOperator 𝕜 d)
    (a : Atoms 𝕜 d),
    ∃ h2 : MemLp (a.val : Space d → 𝕜) 2,
      Integrable (T.operator (h2.toLp a.val) : Space d → 𝕜) ∧
      (∫ x, ‖T.operator (h2.toLp a.val) x‖) ≤ endpointConstant T

/-- A bounded scalar-linear map on the actual quotient-norm Hardy space.
Its output agrees with every compatible weak extension on every Hardy input,
so in particular with the previously constructed unique extension. -/
def Endpoint : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (T : StandardConvolutionOperator 𝕜 d),
    ∃ E : Hardy 𝕜 d →L[𝕜] CZWeak.L1 𝕜 d,
      ‖E‖ ≤ endpointConstant T ∧
      ∀ S : CZWeak.L1 𝕜 d →ₗ[𝕜] MeasurableClasses 𝕜 d,
        IsCompatibleExtension T S → ∀ h : Hardy 𝕜 d,
          (E h : Space d → 𝕜) =ᵐ[volume]
            (S (EmbeddingValue volume h) : Space d → 𝕜)

end ExpandedFA.Hardy.HardyCZEndpointSpec
