import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.ReproducingKernels
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
The integral-range clause of `fa2:p5:rkhs`, paper.tex:23138–23160.
The measure is arbitrary and the point set has no topology. Scalar L² uses
ordinary a.e. equality. The output consists of actual scalar functions.
The algebraic range subtype itself receives the transported Hilbert norm;
its formula below is the infimum of preimage norms.
No ambient output norm or closed-range assumption occurs.
-/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace ExpandedFA.PartV.ReproducingKernelRange.Spec
universe u v
variable {𝕜 : Type} {Z : Type u} {X : Type v} [RCLike 𝕜] [MeasurableSpace Z]

/-- The domain evaluation vector is the ordinary L² class of the conjugate row. -/
def sectionVector (μ : Measure Z) (k : X → Z → 𝕜)
    (hk : ∀ x, MemLp (k x) 2 μ) (x : X) : Lp 𝕜 2 μ :=
  (hk x).star.toLp (star (k x))

/-- Scalar-linear integral map, expressed using the L² inner product.
`IntegralRange` includes its equality to the original integral on every input. -/
def integralMap (μ : Measure Z) (k : X → Z → 𝕜)
    (hk : ∀ x, MemLp (k x) 2 μ) : Lp 𝕜 2 μ →ₗ[𝕜] (X → 𝕜) :=
  LinearMap.pi fun x => (innerSL 𝕜 (sectionVector μ k hk x)).toLinearMap

/-- The displayed minimum-preimage norm, on actual range functions. -/
def preimageNorm (μ : Measure Z) (k : X → Z → 𝕜)
    (hk : ∀ x, MemLp (k x) 2 μ) (f : X → 𝕜) : ℝ :=
  sInf {r | ∃ u : Lp 𝕜 2 μ, integralMap μ k hk u = f ∧ ‖u‖ = r}

/-- The actual range subtype receives a complete Hilbert structure. Its
function realization is precisely subtype inclusion. `J` identifies it
isometrically with the closed orthogonal complement of the kernel. -/
def IntegralRange : Prop :=
  ∀ (𝕜 : Type) (Z : Type u) (X : Type v) [RCLike 𝕜] [MeasurableSpace Z]
    (μ : Measure Z) (k : X → Z → 𝕜) (hk : ∀ x, MemLp (k x) 2 μ),
    let A := integralMap μ k hk
    IsClosed (A.ker : Set (Lp 𝕜 2 μ)) ∧
    (∀ (u : Lp 𝕜 2 μ) x,
      Integrable (fun z => k x z * u z) μ ∧
      A u x = ∫ z, k x z * u z ∂μ ∧
      ‖A u x‖ ≤ ‖sectionVector μ k hk x‖ * ‖u‖) ∧
    ∃ (ng : NormedAddCommGroup A.range),
      letI : UniformSpace A.range := ng.toMetricSpace.toUniformSpace
      letI : TopologicalSpace A.range := ng.toMetricSpace.toUniformSpace.toTopologicalSpace
      ∃ (_ : InnerProductSpace 𝕜 A.range) (_ : CompleteSpace A.range)
      (F : ReproducingKernels.Spec.FunctionSpace 𝕜 X A.range)
      (J : A.range ≃ₗᵢ[𝕜] A.ker.orthogonal),
      (∀ f, F.functions f = f.val) ∧
      (∀ f : A.range,
        A (J f) = f.val ∧
        ‖f‖ = preimageNorm μ k hk f.val ∧
        (∀ u, A u = f.val → ‖f‖ ≤ ‖u‖ ∧
          (‖u‖ = ‖f‖ ↔ u = (J f : Lp 𝕜 2 μ))) ∧
        (∀ u, (A u = f.val ∧ u ∈ A.ker.orthogonal) ↔
          u = (J f : Lp 𝕜 2 μ))) ∧
      ∃ κ : X → A.range,
        (∀ x, (J (κ x) : Lp 𝕜 2 μ) = sectionVector μ k hk x) ∧
        ReproducingKernels.Spec.Reproduces F κ ∧
        (∀ x y, F.functions (κ y) x = ∫ z, k x z * conj (k y z) ∂μ) ∧
        (∀ x y, ⟪κ x, κ y⟫_𝕜 = ∫ z, k x z * conj (k y z) ∂μ)

end ExpandedFA.PartV.ReproducingKernelRange.Spec
