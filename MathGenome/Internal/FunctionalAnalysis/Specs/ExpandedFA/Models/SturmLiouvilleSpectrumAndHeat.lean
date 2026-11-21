import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.SturmLiouvillePeriodic
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.C0SemigroupAndGenerator
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! Spectral and heat conclusions of `fa2:p3:sturm-liouville`.
The operators are the actual maximal form realizations on the upstream L²
space, with either of the two upstream boundary conditions. A finite negative
part is permitted. Divergence is expressed invariantly by finiteness of every
lower spectral section, counting basis vectors and hence multiplicities. -/
noncomputable section
open Filter Topology
open scoped NNReal
namespace ExpandedFA.Models.SturmLiouvilleSpectrumAndHeat
open Unbounded Semigroups SturmLiouvilleDirichlet

/-- The eigenspace in the actual operator domain, including the zero vector. -/
def eigenspace {𝕜 H : Type} [RCLike 𝕜] [NormedAddCommGroup H]
    [NormedSpace 𝕜 H] (A : Operator 𝕜 H H) (z : 𝕜) : Submodule 𝕜 A.domain :=
  LinearMap.ker (A.toFun - z • A.domain.subtype)

/-- Either of the two boundary conditions, on the original coefficient data. -/
def IsRealization {𝕜 : Type} [RCLike 𝕜] {a b : ℝ}
    (c : Coefficients a b) (A : Operator 𝕜 (L2 𝕜 a b) (L2 𝕜 a b)) : Prop :=
  FormRealization c A ∨ SturmLiouvillePeriodic.FormRealization c A

/-- Complete orthonormal spectral data. No positivity of L is assumed.
`finite_below` implies λ tends to +∞ along the cofinite filter and in
particular that the entire nonpositive part is finite dimensional. -/
structure SpectralResolution {𝕜 H : Type} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : Operator 𝕜 H H) where
  Index : Type
  countable : Countable Index
  basis : HilbertBasis Index 𝕜 H
  eigenvalue : Index → ℝ
  mem_domain : ∀ i, basis i ∈ A.domain
  action : ∀ i, A ⟨basis i, mem_domain i⟩ = (eigenvalue i : 𝕜) • basis i
  lower_bound : ∃ γ : ℝ, ∀ i, γ ≤ eigenvalue i
  finite_below : ∀ R : ℝ, {i | eigenvalue i ≤ R}.Finite
  eigenvalues_real : ∀ (z : 𝕜) (u : A.domain), (u : H) ≠ 0 →
    A u = z • (u : H) → ∃ r : ℝ, z = (r : 𝕜)
  finite_multiplicity : ∀ z : 𝕜, FiniteDimensional 𝕜 (eigenspace A z)

namespace Spec

def Spectrum : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ)
    (c : Coefficients a b) (A : Operator 𝕜 (L2 𝕜 a b) (L2 𝕜 a b)),
    IsRealization c A → Nonempty (SpectralResolution A)

/-- exp(−tL) is specified by its action on a complete eigenbasis and by its
full infinitesimal generator, so the assertion refers to the actual heat
semigroup of L. Compactness includes every positive real time. -/
def Heat : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ)
    (c : Coefficients a b) (A : Operator 𝕜 (L2 𝕜 a b) (L2 𝕜 a b)),
    IsRealization c A → ∃ (D : SpectralResolution A) (T : C0Semigroup 𝕜 (L2 𝕜 a b)),
      C0SemigroupSpec.generatorValue T = -A ∧
      (∀ (t : ℝ≥0) i, T.operators t (D.basis i) =
        (Real.exp (-(t : ℝ) * D.eigenvalue i) : 𝕜) • D.basis i) ∧
      ∀ t : ℝ≥0, 0 < t → IsCompactOperator (T.operators t)

end Spec
end ExpandedFA.Models.SturmLiouvilleSpectrumAndHeat
