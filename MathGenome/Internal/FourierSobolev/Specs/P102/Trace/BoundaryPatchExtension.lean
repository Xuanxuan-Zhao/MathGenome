import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.GraphFractionalTransport

/-! The supported-patch reverse estimate in paper.tex:2586–2591.
The support is any fixed compact subset of the full physical chart. -/
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal
namespace P102.Trace.BoundaryPatchExtension
open P102.U4 P102.U4.GraphPieces P102.Sobolev.Geometry
open MeasuredFractional

def surfaceMeasure {m : ℕ} (Ω : Set (Ambient m)) : Measure (Ambient m) :=
  (μHE[m] : Measure (Ambient m)).restrict (frontier Ω)

def patch {m : ℕ} {Ω : Set (Ambient m)} (C : BoundaryChart Ω) : Set (Ambient m) :=
  GraphFractionalTransport.graphMap C.frame C.graphFunction '' ball C.center C.radius

/-- Pullback on the full base ball, extended by zero to the whole tangent space. -/
def pullback {m : ℕ} {Ω : Set (Ambient m)} (C : BoundaryChart Ω)
    {E : Type*} [Zero E] (q : Ambient m → E) : Space m → E :=
  (ball C.center C.radius).indicator (q ∘ GraphFractionalTransport.graphMap C.frame C.graphFunction)

namespace Expected

def FiniteSurfaceMeasure : Prop :=
  ∀ (m : ℕ) (Ω : Set (Ambient m)), IsLipschitzOpen Ω →
    surfaceMeasure Ω univ < ∞

/-- The constant is chosen before the field and the a.e. representative.
Both norms are global: the surface measure is on the entire boundary and the
base measure is unrestricted Lebesgue measure on the whole tangent space. -/
def PatchExtension : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (Ω : Set (Ambient m)), IsLipschitzOpen Ω →
    ∀ (C : BoundaryChart Ω) (K : Set (Ambient m)), IsCompact K →
    K ⊆ chartImage C.frame C.graphFunction C.center C.radius C.height →
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ (p : ℝ≥0∞), 1 ≤ p → p < ∞ →
    ∃ A : ℝ≥0, 0 < A ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (q : Ambient m → 𝕜),
      MemLp q p (surfaceMeasure Ω) →
      (∀ᵐ x ∂surfaceMeasure Ω, x ∉ K → q x = 0) →
      MemLp (pullback C q) p volume ∧
      metricNorm m (surfaceMeasure Ω) s p q ≤
        (A : ℝ≥0∞) * metricNorm m volume s p (pullback C q)

end Expected
end P102.Trace.BoundaryPatchExtension
