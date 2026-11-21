import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Foundation

/-! Independent full statement types for Theorem 1.3 and Corollary 2.3.
The means and polynomials here are the canonical upstream objects. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Real ENNReal ComplexConjugate
namespace P102.Periodic.Expected.FejerRecovery

def cesaroStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)] (N : ℕ)
    (f : Circle T → ℂ) (x : Circle T),
  fejerMean T N f x = (N + 1 : ℂ)⁻¹ *
    ∑ j ∈ Finset.range (N + 1), partialSum T j f x

def kernelAverageStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)] (N : ℕ) (x : Circle T),
  fejerKernel T N x = (N + 1 : ℂ)⁻¹ *
    ∑ j ∈ Finset.range (N + 1), dirichletKernel T j x

def kernelSquareStatement : Prop := ∀ (N : ℕ) (v : ℝ),
  fejerKernel (2 * Real.pi) N (v : Circle (2 * Real.pi)) =
    ((1 / (N + 1 : ℝ) * ‖∑ j ∈ Finset.range (N + 1),
      Complex.exp (Complex.I * (j : ℂ) * v)‖ ^ 2 : ℝ) : ℂ)

def kernelExpansionStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)] (N : ℕ) (x : Circle T),
  fejerKernel T N x = ∑ k ∈ frequencies N,
    ((1 - (k.natAbs : ℝ) / (N + 1 : ℝ) : ℝ) : ℂ) * mode T k x

def kernelAngularExpansionStatement : Prop := ∀ (N : ℕ) (v : ℝ),
  fejerKernel (2 * Real.pi) N (v : Circle (2 * Real.pi)) =
    ∑ k ∈ frequencies N, ((1 - (k.natAbs : ℝ) / (N + 1 : ℝ) : ℝ) : ℂ) *
      Complex.exp (Complex.I * k * v)

def kernelPositiveStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)] (N : ℕ) (x : Circle T),
  (fejerKernel T N x).im = 0 ∧ 0 ≤ (fejerKernel T N x).re

def kernelMassStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)] (N : ℕ),
  (∫ x, fejerKernel T N x ∂haar T) = 1

def kernelDegreeStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)] (N : ℕ),
  ∃ K : C(Circle T, ℂ), K ∈ complexTrigDegree T N ∧ ∀ x, K x = fejerKernel T N x

def outsideBoundStatement : Prop := ∀ (δ : ℝ), 0 < δ → δ < Real.pi →
  ∀ (N : ℕ) (v : ℝ), δ ≤ |v| → |v| ≤ Real.pi →
  (fejerKernel (2 * Real.pi) N (v : Circle (2 * Real.pi))).re ≤
    1 / ((N + 1 : ℝ) * Real.sin (δ / 2) ^ 2)

def concentrationStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)] (U : Set (Circle T)),
  U ∈ 𝓝 (0 : Circle T) →
  Tendsto (fun N : ℕ => ∫ x in Uᶜ, (fejerKernel T N x).re ∂haar T) atTop (𝓝 0)

def convolutionStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)] (f : Circle T → ℂ),
  Integrable f (haar T) → ∀ (N : ℕ) (x : Circle T),
    ConvolutionExistsAt T f (fejerKernel T N) x ∧
    fejerMean T N f x = convolution T f (fejerKernel T N) x

def meanDegreeStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)] (N : ℕ) (f : Circle T → ℂ),
  ∃ P : C(Circle T, ℂ), P ∈ complexTrigDegree T N ∧ ∀ x, P x = fejerMean T N f x

def uniformComplexStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)] (f : C(Circle T, ℂ)),
  TendstoUniformly (fun N => fejerMean T N f) f atTop

def uniformRealStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)] (f : C(Circle T, ℝ)),
  (∀ N x, (fejerMean T N (fun y => (f y : ℂ)) x).im = 0) ∧
  TendstoUniformly (fun N x => (fejerMean T N (fun y => (f y : ℂ)) x).re) f atTop

def contractionComplexStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)]
  (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ → ∀ (f : Circle T → ℂ), MemLp f p (haar T) →
  ∀ N, MemLp (fejerMean T N f) p (haar T) ∧
    eLpNorm (fejerMean T N f) p (haar T) ≤ eLpNorm f p (haar T)

def contractionRealStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)]
  (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ → ∀ (f : Circle T → ℝ), MemLp f p (haar T) →
  ∀ N, MemLp (fun x => (fejerMean T N (fun y => (f y : ℂ)) x).re) p (haar T) ∧
    eLpNorm (fun x => (fejerMean T N (fun y => (f y : ℂ)) x).re) p (haar T) ≤
      eLpNorm f p (haar T)

def lpComplexStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)]
  (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ → ∀ (f : Circle T → ℂ), MemLp f p (haar T) →
  Tendsto (fun N => eLpNorm (fun x => fejerMean T N f x - f x) p (haar T)) atTop (𝓝 0)

def lpRealStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)]
  (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ → ∀ (f : Circle T → ℝ), MemLp f p (haar T) →
  Tendsto (fun N => eLpNorm
    (fun x => (fejerMean T N (fun y => (f y : ℂ)) x).re - f x) p (haar T)) atTop (𝓝 0)

def uniformDensityComplexStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)]
  (f : C(Circle T, ℂ)) (ε : ℝ), 0 < ε →
  ∃ P ∈ complexTrigPolynomials T, ‖P - f‖ < ε

def uniformDensityRealStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)]
  (f : C(Circle T, ℝ)) (ε : ℝ), 0 < ε →
  ∃ P ∈ realTrigPolynomials T, ‖P - f‖ < ε

def lpDensityComplexStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)]
  (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ → ∀ (f : Circle T → ℂ), MemLp f p (haar T) →
  ∀ (ε : ℝ), 0 < ε → ∃ P ∈ complexTrigPolynomials T,
    eLpNorm (fun x => P x - f x) p (haar T) < ENNReal.ofReal ε

def lpDensityRealStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)]
  (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ → ∀ (f : Circle T → ℝ), MemLp f p (haar T) →
  ∀ (ε : ℝ), 0 < ε → ∃ P ∈ realTrigPolynomials T,
    eLpNorm (fun x => P x - f x) p (haar T) < ENNReal.ofReal ε

def sineCosineRepresentationStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)]
  (P : C(Circle T, ℝ)), P ∈ realTrigPolynomials T →
  ∃ (N : ℕ) (a b : ℤ → ℝ), ∀ t : ℝ,
    P (t : Circle T) = ∑ k ∈ frequencies N,
      (a k * Real.cos (2 * Real.pi * k * t / T) +
       b k * Real.sin (2 * Real.pi * k * t / T))

/-- Explicit real sine/cosine witnesses, with the original period. -/
def sineCosineDensityStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)]
  (f : C(Circle T, ℝ)) (ε : ℝ), 0 < ε →
  ∃ (N : ℕ) (a b : ℤ → ℝ), ∀ t : ℝ,
    |(∑ k ∈ frequencies N, (a k * Real.cos (2 * Real.pi * k * t / T) +
      b k * Real.sin (2 * Real.pi * k * t / T))) - f (t : Circle T)| < ε

end P102.Periodic.Expected.FejerRecovery
