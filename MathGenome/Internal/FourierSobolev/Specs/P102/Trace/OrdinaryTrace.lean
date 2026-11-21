import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.OrdinaryTraceMap
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.ZeroExtension

/-!
The ordinary trace theorem, paper.tex:2595–2608 and 2617–2691.
All spaces, the Lipschitz hypothesis, and the physical Hausdorff boundary
measure are the shared objects from `OrdinaryTraceMap`. In particular m=0
means physical dimension one; neither connectedness nor nonemptiness is
required. The exponent is finite and at least one.

These are unconditional original propositions. They contain no provisional
upstream certificates. The bulk extension clause is the restriction property
of the extension already allocated to `Sobolev.LipschitzExtension`; the
stronger fixed reflection formula and simultaneous exponent estimates remain
in that upstream specification.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal Topology

namespace P102.Trace.Ordinary
open P102.U4 P102.U4.GraphPieces P102.Sobolev.Geometry
open P102.Sobolev.Extension

/-- Membership of the zero extension as a function in the whole-space W¹ᵖ.
No derivative identity and no vanishing trace is part of this definition. -/
def HasZeroExtension {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space (m + 1))} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 Ω 1 p) : Prop :=
  ∃ w : Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p,
    sobolevUnderlying w = lpZeroExtension Ω p (sobolevUnderlying u)

namespace Expected

/-- Equality with the actual norm closure of ambient smooth tests supported
compactly inside Ω, for every representative of the canonical trace map. -/
def Kernel : Prop :=
  ∀ (m : ℕ) (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1))),
    IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)) →
    ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
    ∀ T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p, IsTrace T →
      T.ker = sobolevZeroSubmodule 𝕜 Ω 1 p

/-- The two-sided zero-extension criterion for the same trace, without
assuming in advance any formula for weak derivatives of the extension. -/
def ZeroExtensionCriterion : Prop :=
  ∀ (m : ℕ) (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1))),
    IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)) →
    ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
    ∀ T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p, IsTrace T →
    ∀ u : Sobolev 𝕜 Ω 1 p, T u = 0 ↔ HasZeroExtension u

/-- Surjectivity at p=1 with one domain-dependent preimage bound. No
linearity or continuity of the selection of preimages is asserted. This
also includes arbitrary endpoint data on a finite union of intervals. -/
def EndpointSurjectivity : Prop :=
  ∀ (m : ℕ) (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1))),
    IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)) →
    ∀ (𝕜 : Type) [RCLike 𝕜],
    ∃ C : ℝ, 0 ≤ C ∧
      (∃ T : Sobolev 𝕜 Ω 1 1 →L[𝕜] BoundaryLp 𝕜 Ω 1, IsTrace T) ∧
      ∀ T : Sobolev 𝕜 Ω 1 1 →L[𝕜] BoundaryLp 𝕜 Ω 1, IsTrace T →
      ∀ g : BoundaryLp 𝕜 Ω 1,
        ∃ u : Sobolev 𝕜 Ω 1 1, T u = g ∧ ‖u‖ ≤ C * ‖g‖

/-- The bounded linear bulk extension recalled in the ordinary theorem.
The common compact essential support is independent of the input. -/
def BulkExtension : Prop :=
  ∀ (m : ℕ) (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1))),
    IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)) →
    ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
    ∃ (K : Compacts (Space (m + 1)))
      (E : Sobolev 𝕜 Ω 1 p →L[𝕜] Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p),
      (∀ u, sobolevUnderlying (E u) =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))]
        sobolevUnderlying u) ∧
      (∀ u, ∀ᵐ x ∂volume, x ∉ (K : Set (Space (m + 1))) →
        sobolevUnderlying (E u) x = 0)

/-- The complete ordinary trace theorem. Existence retains boundedness,
smooth compatibility and canonicity. The endpoint clause uses the same
trace and exactly H⁰ counting measure, with AC representatives on all
component intervals. -/
def OrdinaryTrace : Prop :=
  TraceExists ∧ Kernel ∧ ZeroExtensionCriterion ∧ EndpointSurjectivity ∧
    EndpointIdentification ∧ BulkExtension

end Expected
end P102.Trace.Ordinary
