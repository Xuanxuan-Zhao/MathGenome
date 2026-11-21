import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Foundation

/-! Dini part of Theorem 1.6, paper.tex:305–338. All integrals are Lebesgue
integrals on the open positive interval. Norm integrability expresses finiteness
of the source's nonnegative weighted integral. Values on null sets do not affect
this hypothesis or the Fourier sums. No one-sided limit is assumed in `symmetricStatement`. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Real

namespace P102.Periodic.Expected.Dini

/-- Displacement corresponding to an angular coordinate, for every period. -/
def offset (T v : ℝ) : Circle T := ((T * v / (2 * Real.pi) : ℝ) : Circle T)

def residual (T : ℝ) (f : Circle T → ℂ) (x : Circle T) (L : ℂ) (v : ℝ) : ℂ :=
  f (x + offset T v) + f (x - offset T v) - 2 * L

def symmetricStatement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f : Circle T → ℂ), Integrable f (haar T) →
    ∀ (x : Circle T) (L : ℂ) (δ : ℝ), 0 < δ →
      IntegrableOn (fun v => ‖residual T f x L v‖ / v) (Ioo 0 δ) →
      Tendsto (fun N : ℕ => partialSum T N f x) atTop (𝓝 L)

def separateStatement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f : Circle T → ℂ), Integrable f (haar T) →
    ∀ (x : Circle T) (aPlus aMinus : ℂ) (δPlus δMinus : ℝ),
      0 < δPlus → 0 < δMinus →
      IntegrableOn (fun v => ‖f (x + offset T v) - aPlus‖ / v) (Ioo 0 δPlus) →
      IntegrableOn (fun v => ‖f (x - offset T v) - aMinus‖ / v) (Ioo 0 δMinus) →
      Tendsto (fun N : ℕ => partialSum T N f x) atTop (𝓝 ((aPlus + aMinus) / 2))

def midpointStatement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f : Circle T → ℂ), Integrable f (haar T) →
    ∀ (x : Circle T) (L aPlus aMinus : ℂ) (δ : ℝ), 0 < δ →
      IntegrableOn (fun v => ‖residual T f x L v‖ / v) (Ioo 0 δ) →
      Tendsto (fun v => f (x + offset T v)) (𝓝[>] 0) (𝓝 aPlus) →
      Tendsto (fun v => f (x - offset T v)) (𝓝[>] 0) (𝓝 aMinus) →
      (aPlus + aMinus) / 2 = L

def symmetricL1Statement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f : L1 T) (x : Circle T) (L : ℂ) (δ : ℝ), 0 < δ →
    IntegrableOn (fun v => ‖residual T f x L v‖ / v) (Ioo 0 δ) →
    Tendsto (fun N : ℕ => partialSum T N f x) atTop (𝓝 L)

end P102.Periodic.Expected.Dini
