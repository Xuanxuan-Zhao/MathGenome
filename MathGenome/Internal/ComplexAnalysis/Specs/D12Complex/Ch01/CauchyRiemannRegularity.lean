import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.RealComplexDifferential

/-!
Independent statements for the regular sufficiency part of d12:01-03.
The hypotheses assert existence of the actual one-variable derivatives of
both coordinate slices, and continuity of those partials on the open set.
They do not assume real total differentiability or continuity of a complex
derivative. Empty and disconnected open sets are included.
-/
namespace Specs.D12Complex.Ch01.CauchyRiemannRegularity
open _root_.D12Complex

def realDifferentiableAt_of_continuousPartials_type : Prop :=
  ∀ (Ω : Set ℂ) (u : ℂ → ℝ), IsOpen Ω →
    (∀ a ∈ Ω, DifferentiableAt ℝ (fun t : ℝ => u (a + (t : ℂ))) 0) →
    (∀ a ∈ Ω, DifferentiableAt ℝ (fun t : ℝ => u (a + (t : ℂ) * Complex.I)) 0) →
    ContinuousOn (partialX u) Ω → ContinuousOn (partialY u) Ω →
    ∀ a ∈ Ω, DifferentiableAt ℝ u a

/-- Necessity has no continuity-of-partials hypothesis. -/
def cauchyRiemann_of_holomorphicOn_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), HolomorphicOn Ω f →
    ∀ a ∈ Ω,
      partialX (fun z => (f z).re) a = partialY (fun z => (f z).im) a ∧
      partialY (fun z => (f z).re) a = -partialX (fun z => (f z).im) a

def holomorphicOn_iff_CR_of_continuousPartials_type : Prop :=
  ∀ (Ω : Set ℂ) (u v : ℂ → ℝ), IsOpen Ω →
    (∀ a ∈ Ω, DifferentiableAt ℝ (fun t : ℝ => u (a + (t : ℂ))) 0) →
    (∀ a ∈ Ω, DifferentiableAt ℝ (fun t : ℝ => u (a + (t : ℂ) * Complex.I)) 0) →
    (∀ a ∈ Ω, DifferentiableAt ℝ (fun t : ℝ => v (a + (t : ℂ))) 0) →
    (∀ a ∈ Ω, DifferentiableAt ℝ (fun t : ℝ => v (a + (t : ℂ) * Complex.I)) 0) →
    ContinuousOn (partialX u) Ω → ContinuousOn (partialY u) Ω →
    ContinuousOn (partialX v) Ω → ContinuousOn (partialY v) Ω →
    (HolomorphicOn Ω (fun z => (u z : ℂ) + Complex.I * (v z : ℂ)) ↔
      ∀ a ∈ Ω, partialX u a = partialY v a ∧ partialY u a = -partialX v a)

end Specs.D12Complex.Ch01.CauchyRiemannRegularity
