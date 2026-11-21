import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinLocalFiberKernels

/-! The measurable global kernel of paper.tex:21274–21294, before the
operator action is used to obtain the distribution equation. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace ExpandedFA.PartIV.KreinKernelPatching
open KreinSpectralKernel

/-- The fields of `KernelData` independent of the distribution equation.
All fields concern this same representative, with all real radii retained. -/
structure PatchedKernel {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {p : Bool} {F : ℝ → ℝ}
    (G : KreinSymmetricOperator.Spec.GramData p F H)
    {S : Unbounded.Operator ℂ H H} (M : RealSpectralModel S) where
  h : ℝ → ℝ → FiberSpace
  measurable : AEStronglyMeasurable (Function.uncurry h) (M.μ.prod volume)
  local_square : ∀ R : ℝ, 0 < R →
    MemLp (Function.uncurry h) 2 (M.μ.prod (intervalMeasure R))
  fiber_properties : ∀ᵐ ξ ∂M.μ,
    (∀ n : ℕ, MemLp (h ξ) 2 (intervalMeasure (n + 1))) ∧
    (∀ᵐ t ∂volume, h ξ t ∈ coordinateFiber (M.multiplicity ξ)) ∧
    (∀ᵐ t ∂volume, h ξ (-t) = KreinSymmetricOperator.Spec.paritySign p • h ξ t)
  represents : ∀ R : ℝ, 0 < R → ∀ f : Lp ℂ 2 (intervalMeasure R),
    (M.U (∫ t, f t • G.vectors t ∂intervalMeasure R) : ℝ → FiberSpace) =ᵐ[M.μ]
      fun ξ => ∫ t, f t • h ξ t ∂intervalMeasure R
  energy : ∀ R : ℝ, 0 < R →
    (∫⁻ ξ, ∫⁻ t, ‖h ξ t‖ₑ ^ 2 ∂intervalMeasure R ∂M.μ) =
      ENNReal.ofReal (∫ t, ‖G.vectors t‖ ^ 2 ∂intervalMeasure R)

namespace Spec

def KernelPatching : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] {p : Bool} {F : ℝ → ℝ}
    (G : KreinSymmetricOperator.Spec.GramData p F H)
    (S : Unbounded.Operator ℂ H H) (M : RealSpectralModel S),
    Nonempty (PatchedKernel G M)
end Spec
end ExpandedFA.PartIV.KreinKernelPatching
