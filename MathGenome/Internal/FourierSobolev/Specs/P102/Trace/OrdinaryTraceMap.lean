import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.LipschitzExtension
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
Independent statements for the ordinary trace map in paper.tex:2595–2608,
2617–2629,2671–2691. The kernel, zero-extension criterion, and surjectivity
are allocated to `OrdinaryTrace`; none is assumed here. The geometric
hypothesis is the shared bounded Lipschitz **open set**, including empty
and disconnected sets. No C¹ boundary hypothesis is imposed.

The physical ambient space has dimension m+1, including m=0. The isometry
`e` only expresses the shared graph-coordinate geometric hypothesis.
Boundary data are ambient Lp classes for the Euclidean-normalized Hausdorff
measure restricted to the frontier, hence are exactly boundary a.e. data.
The propositions below are unconditional original types. Conditional proof
premises belong exclusively to the implementation helpers.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal ContDiff Topology

namespace P102.Trace.Ordinary
open P102.U4 P102.U4.GraphPieces P102.Sobolev.Geometry
open P102.Sobolev.Extension

/-- Euclidean-normalized H^m on the physical boundary in dimension m+1. -/
def boundaryMeasure {m : ℕ} (Ω : Opens (Space (m + 1))) :
    Measure (Space (m + 1)) :=
  (μHE[m] : Measure (Space (m + 1))).restrict (frontier (Ω : Set (Space (m + 1))))

abbrev BoundaryLp {m : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (Ω : Opens (Space (m + 1))) (p : ℝ≥0∞) := Lp 𝕜 p (boundaryMeasure Ω)

/-- Agreement with all globally smooth restrictions, not only compact tests.
The a.e. representative hypothesis is on Ω; the conclusion is on its boundary. -/
def IsTrace {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space (m + 1))}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) : Prop :=
  ∀ (u : Sobolev 𝕜 Ω 1 p) (f : Space (m + 1) → 𝕜),
    ContDiff ℝ ∞ f →
    sobolevUnderlying u =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] f →
    (T u : Space (m + 1) → 𝕜) =ᵐ[boundaryMeasure Ω] f

/-- The ordinary physical coordinate on the one-dimensional ambient space. -/
def linePoint (t : ℝ) : Space 1 := WithLp.toLp 2 (fun _ => t)

/-- A representative on all finitely many closed component intervals. Values
in the gaps are irrelevant. AC is required through each endpoint, and its
classical derivative agrees with the prescribed weak derivative a.e. -/
def IsEndpointRepresentative {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space 1)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {n : ℕ} (a b : Fin n → ℝ)
    (u : Sobolev 𝕜 Ω 1 p) (f : ℝ → 𝕜) : Prop :=
  (∀ᵐ t ∂volume.restrict (linePoint ⁻¹' (Ω : Set (Space 1))),
    sobolevUnderlying u (linePoint t) = f t) ∧
  (∀ i, AbsolutelyContinuousOnInterval f (a i) (b i)) ∧
  ∀ᵐ t ∂volume.restrict (linePoint ⁻¹' (Ω : Set (Space 1))),
    HasDerivAt f (firstWeakDerivative u 0 (linePoint t)) t

namespace Expected

/-- Existence, the full W¹ᵖ norm estimate, and canonicity. Uniqueness among
all bounded maps agreeing on smooth restrictions implies independence of
any chart or partition used in the construction. -/
def TraceExists : Prop :=
  ∀ (m : ℕ) (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1))),
    IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)) →
    ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
    ∃ C : ℝ, 0 ≤ C ∧
    ∃ T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p,
      IsTrace T ∧ (∀ u, ‖T u‖ ≤ C * ‖u‖) ∧
      ∀ S : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p, IsTrace S → S = T

def TraceUniqueness : Prop :=
  ∀ (m : ℕ) (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1))),
    IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)) →
    ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
    ∀ T S : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p,
      IsTrace T → IsTrace S → T = S

/-- A smooth ambient cutoff acts in the bulk, and its boundary action is
pointwise multiplication on boundary a.e. classes. Every Sobolev class
representing the bulk product has the asserted trace; it is not necessary
to fix an implementation of Sobolev multiplication in this interface. -/
def CutoffCompatibility : Prop :=
  ∀ (m : ℕ) (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1))),
    IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)) →
    ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
    ∀ T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p, IsTrace T →
    ∀ χ : Space (m + 1) → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
    ∀ u : Sobolev 𝕜 Ω 1 p,
      (∃ v : Sobolev 𝕜 Ω 1 p,
        sobolevUnderlying v =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))]
          (fun x => χ x • sobolevUnderlying u x)) ∧
      ∀ v : Sobolev 𝕜 Ω 1 p,
        sobolevUnderlying v =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))]
          (fun x => χ x • sobolevUnderlying u x) →
        (T v : Space (m + 1) → 𝕜) =ᵐ[boundaryMeasure Ω] (fun x => χ x • T u x)

/-- Dimension one: finitely many disjoint component intervals with distinct
endpoints, counting boundary measure, AC representatives on their closures,
and evaluation of the *same* trace at every endpoint. Pointwise values of
the Lp class are meaningful here because each endpoint is an atom of mass one.
The norm estimate uses the full Sobolev norm and one constant for all inputs. -/
def EndpointIdentification : Prop :=
  ∀ (e : Ambient 0 ≃ₗᵢ[ℝ] Space 1) (Ω : Opens (Space 1)),
    IsLipschitzOpen (geometricOpen e Ω : Set (Ambient 0)) →
    ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
    ∀ T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p, IsTrace T →
      boundaryMeasure Ω = Measure.count.restrict (frontier (Ω : Set (Space 1))) ∧
      ∃ (n : ℕ) (a b : Fin n → ℝ),
        (∀ i, a i < b i) ∧ Function.Injective (Sum.elim a b) ∧
        Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) ∧
        (Ω : Set (Space 1)) = ⋃ i, linePoint '' Ioo (a i) (b i) ∧
        frontier (Ω : Set (Space 1)) = ⋃ i, {linePoint (a i), linePoint (b i)} ∧
        (∃ C : ℝ, 0 ≤ C ∧ ∀ u, ‖T u‖ ≤ C * ‖u‖) ∧
        (∀ u : Sobolev 𝕜 Ω 1 p, ∃ f : ℝ → 𝕜, IsEndpointRepresentative a b u f) ∧
        ∀ (u : Sobolev 𝕜 Ω 1 p) (f : ℝ → 𝕜),
          IsEndpointRepresentative a b u f → ∀ i,
            T u (linePoint (a i)) = f (a i) ∧ T u (linePoint (b i)) = f (b i)

end Expected
end P102.Trace.Ordinary
