import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Asplund.SimultaneousRenorming
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Asplund.OrderLimit
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Complex.Basic

/-! Complex version of `fa2:p1:asplund-complex` (paper.tex:7060–7078).
All duals consist of scalar-linear continuous functionals. Equivalence is to
one reference norm, so these are the duals of every norm under consideration.
No completeness or nontriviality is assumed. -/
noncomputable section
namespace ExpandedFA.Asplund.ComplexRenorming

open SimultaneousRenorming

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The underlying real structure, always obtained by restriction. -/
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E

/-- Complex norm axioms and equivalence to the common reference topology. -/
def EquivalentComplexNorm (p : E → ℝ) : Prop :=
  P1.C01Norm.NormAxioms ℂ p ∧
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x, a * ‖x‖ ≤ p x ∧ p x ≤ b * ‖x‖

/-- The complex continuous dual norm, with the actual complex modulus. -/
def complexDualNorm (p : E → ℝ) (f : E →L[ℂ] ℂ) : ℝ :=
  sSup ((fun x => ‖f x‖) '' {x : E | p x ≤ 1})

/-- Canonical restriction by taking real parts; its inverse is the complex
extension. The isometry here uses the reference norm. -/
def realDualEquiv : (E →L[ℂ] ℂ) ≃ₗᵢ[ℝ] (E →L[ℝ] ℝ) :=
  (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ) (F := E)).symm

/-- Invariance under every scalar of modulus one. -/
def PhaseInvariant (q : E → ℝ) : Prop :=
  ∀ (z : ℂ), ‖z‖ = 1 → ∀ x, q (z • x) = q x

namespace Spec

def RealDualIdentification : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E],
    (∀ (f : E →L[ℂ] ℂ) x, realDualEquiv f x = (f x).re) ∧
    (∀ (u : E →L[ℝ] ℝ) x,
      realDualEquiv.symm u x = (u x : ℂ) - Complex.I * (u (Complex.I • x) : ℂ))

def DualNormIdentification : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : E → ℝ), EquivalentComplexNorm p → ∀ f : E →L[ℂ] ℂ,
    complexDualNorm p f = NormSquareConjugate.dualNorm p (realDualEquiv f)

/-- A bound for either scalar-linear dual characterizes continuity in the
common topology, for every equivalent norm, including the constructed one. -/
def CommonDualTopology : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : E → ℝ), EquivalentComplexNorm p →
    (∀ f : E →ₗ[ℝ] ℝ, Continuous f ↔
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M * p x) ∧
    (∀ f : E →ₗ[ℂ] ℂ, Continuous f ↔
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M * p x)

/-- Phase symmetry passes through both operations at every stage and into
the actual common-limit function. -/
def IterationPhaseInvariance : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (φ ψ : E → ℝ), PhaseInvariant φ → PhaseInvariant ψ →
    (∀ n, PhaseInvariant (Iteration.Spec.phiValue E φ ψ n) ∧
      PhaseInvariant (Iteration.Spec.psiValue E φ ψ n)) ∧
    PhaseInvariant (OrderLimit.Spec.thetaValue E φ ψ)

/-- The real norm obtained from the invariant quadratic limit is complex
homogeneous; the remaining norm axioms keep their original meaning. -/
def LimitComplexNorm : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (φ ψ p : E → ℝ), PhaseInvariant φ → PhaseInvariant ψ →
    P1.C01Norm.NormAxioms ℝ p →
    (∀ x, p x ^ 2 / 2 = OrderLimit.Spec.thetaValue E φ ψ x) →
    P1.C01Norm.NormAxioms ℂ p

def SimultaneousComplexRenorming : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p₁ p₂ : E → ℝ), EquivalentComplexNorm p₁ → EquivalentComplexNorm p₂ →
    SphereStrictConvex p₁ → SphereStrictConvex (complexDualNorm p₂) →
    ∃ p : E → ℝ, EquivalentComplexNorm p ∧ SphereStrictConvex p ∧
      SphereStrictConvex (complexDualNorm p)

end Spec
end ExpandedFA.Asplund.ComplexRenorming
