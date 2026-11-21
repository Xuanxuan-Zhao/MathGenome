import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.C1DomainExtension
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.OneDimensionalSobolev
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Independent scope of the trace clauses of paper.tex:17902–17940.
Poincaré is a separate allocated obligation. Scalars include ℝ and ℂ.
Boundary Lp is realized on the ambient space with surface measure supported
on the frontier, so its elements carry exactly boundary a.e. data. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal

namespace ExpandedFA.Sobolev.Trace
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open C1Extension OneDimensional

/-- Normalized Euclidean (d-1)-dimensional Hausdorff measure on the frontier.
`Domain d` has the coordinate sup norm, so Hausdorff measure is first formed
in the Euclidean norm and pulled back by the coordinate identification.
The volume of the radius-1/2 ball supplies the standard Hausdorff normalization.
In dimension zero the frontier of an open set is empty. -/
def surfaceMeasure {d : ℕ} (Ω : Opens (Domain d)) : Measure (Domain d) :=
  volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d - 1))) (1 / 2)) •
    (Measure.comap (WithLp.toLp 2 : Domain d → EuclideanSpace ℝ (Fin d))
      (Measure.hausdorffMeasure (d - 1 : ℕ))).restrict
        (frontier (Ω : Set (Domain d)))

abbrev BoundaryLp (𝕜 : Type) [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  Lp 𝕜 p (surfaceMeasure Ω)

/-- Agreement with actual ambient smooth restrictions. There is no assumed
trace certificate, bound, or boundary theorem in this predicate. -/
def IsTrace {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) : Prop :=
  ∀ (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜),
    ContDiff ℝ (⊤ : ℕ∞) f →
    u.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f →
    T u =ᵐ[surfaceMeasure Ω] f

/-- Zero extension concerns the function itself; the existence of global weak
derivatives is the conclusion, and is not built into the extension formula. -/
def HasSobolevZeroExtension {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : SpaceValue 𝕜 d Ω 1 p) : Prop :=
  ∃ v : SpaceValue 𝕜 d ⊤ 1 p,
    v.val (zeroIndex d 1) =ᵐ[volume]
      (Ω : Set (Domain d)).indicator (u.val (zeroIndex d 1))

/-- Endpoint order is left, then right. -/
def endpoint (a b : ℝ) (i : Fin 2) : ℝ := if i = 0 then a else b

end ExpandedFA.Sobolev.Trace

namespace Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.Sobolev
open _root_.ExpandedFA.Sobolev.Trace _root_.ExpandedFA.Sobolev.C1Extension
open _root_.ExpandedFA.Sobolev.OneDimensional WeakDerivativeSpaces

/-- The unique bounded scalar-linear extension of smooth restriction. -/
def TraceExists : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
    IsC1Domain Ω → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∃! T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p, IsTrace T

def TraceKernel : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
    IsC1Domain Ω → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
    T.ker = ZeroSpaceValue 𝕜 d Ω 1 p hp

def ZeroExtensionCriterion : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
    IsC1Domain Ω → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
    ∀ u, T u = 0 ↔ HasSobolevZeroExtension u

/-- A bounded endpoint operator on the very same accepted W1p graph. Its
values are those of every continuous primitive representative on [a,b].
The stronger infinity case is also useful and valid here. -/
def IntervalEndpointOperator : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (a b : ℝ), a < b → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∃! T : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p →L[𝕜] (Fin 2 → 𝕜),
      ∀ (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p) (f : ℝ → 𝕜),
        PrimitiveRepresentative u f → ∀ i, T u i = f (endpoint a b i)

/-- The interval endpoint operator realized in the same boundary Lp space
as the general trace, with existence and uniqueness. -/
def IntervalBoundaryOperator : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (a b : ℝ), a < b → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∃! T : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p →L[𝕜]
      BoundaryLp 𝕜 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) p, IsTrace T

/-- Compatibility of the general boundary trace with the same endpoint
values, rather than merely a second unrelated operator. -/
def IntervalIdentification : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (a b : ℝ), a < b → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ (T : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p →L[𝕜]
      BoundaryLp 𝕜 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) p), IsTrace T →
    ∀ (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p) (f : ℝ → 𝕜),
      PrimitiveRepresentative u f →
      T u =ᵐ[surfaceMeasure (lineDomain ⟨Ioo a b, isOpen_Ioo⟩)] (fun z => f (z 0))

/-- The original closure-defined kernel, including its reverse inclusion,
specialized to each nondegenerate bounded interval. -/
def IntervalKernel : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (a b : ℝ), a < b → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p →L[𝕜]
      BoundaryLp 𝕜 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) p), IsTrace T →
    T.ker = ZeroSpaceValue 𝕜 1 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) 1 p hp

/-- The original zero-extension criterion specialized to a nondegenerate
bounded interval, for the actual boundary trace. -/
def IntervalZeroExtensionCriterion : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (a b : ℝ), a < b → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ (T : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p →L[𝕜]
      BoundaryLp 𝕜 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) p), IsTrace T →
    ∀ u, T u = 0 ↔ HasSobolevZeroExtension u

/-- The closure definition forces both continuous endpoint values to vanish. -/
def IntervalZeroSpaceEndpoints : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (a b : ℝ), a < b → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p),
    u ∈ ZeroSpaceValue 𝕜 1 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) 1 p hp →
    ∀ f : ℝ → 𝕜, PrimitiveRepresentative u f → f a = 0 ∧ f b = 0

/-- Density proves uniqueness from smooth agreement. -/
def TraceUniqueness : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)), IsC1Domain Ω →
    IsCompact (frontier (Ω : Set (Domain d))) →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ (T S : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p),
      IsTrace T → IsTrace S → T = S

/-- The easy kernel inclusion uses only boundedness and smooth agreement. -/
def KernelContainsZeroSpace : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
    ZeroSpaceValue 𝕜 d Ω 1 p hp ≤ T.ker

/-- On arbitrary open sets, zero extension preserves the full jet of W₀
and is isometric. No regular boundary is assumed for this direction. -/
def ZeroExtensionOfZeroSpace : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : SpaceValue 𝕜 d Ω m p), u ∈ ZeroSpaceValue 𝕜 d Ω m p hp →
    ∃ v : SpaceValue 𝕜 d ⊤ m p,
      (∀ α, v.val α =ᵐ[volume] (Ω : Set (Domain d)).indicator (u.val α)) ∧
      ‖v‖ = ‖u‖

/-- The geometric approximation characterization uses the original closure
of compact interior smooth functions, independently of a chosen trace map. -/
def ZeroSpaceExtensionCriterion : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
    IsC1Domain Ω → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : SpaceValue 𝕜 d Ω 1 p),
    HasSobolevZeroExtension u ↔ u ∈ ZeroSpaceValue 𝕜 d Ω 1 p hp

end Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel
