import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Foundation

/-! Theorem 1.4 (paper.tex:230–260). All L² spaces use probability Haar.
The paper's first-variable-linear coefficient is Mathlib `inner mode f`. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology Real ENNReal ComplexConjugate
namespace P102.Periodic.FourierHilbert

abbrev L2C (T : ℝ) [Fact (0 < T)] := Lp ℂ 2 (Expected.haar T)
abbrev L2R (T : ℝ) [Fact (0 < T)] := Lp ℝ 2 (Expected.haar T)

/-- One constant, followed by one cosine and one sine for every positive frequency.
`false` selects cosine and `true` selects sine. -/
abbrev RealIndex := Option (ℕ × Bool)

def realWave (T : ℝ) : RealIndex → C(Expected.Circle T, ℝ)
  | none => 1
  | some (n, false) => ⟨fun x => Real.sqrt 2 * (Expected.mode T (n + 1) x).re,
      continuous_const.mul (Complex.continuous_re.comp (Expected.mode T (n + 1)).continuous)⟩
  | some (n, true) => ⟨fun x => Real.sqrt 2 * (Expected.mode T (n + 1) x).im,
      continuous_const.mul (Complex.continuous_im.comp (Expected.mode T (n + 1)).continuous)⟩

def realVector (T : ℝ) [Fact (0 < T)] (i : RealIndex) : L2R T :=
  ContinuousMap.toLp 2 (Expected.haar T) ℝ (realWave T i)

/-- Exact coefficient correspondence, including the minus sign for sine. -/
def realCoeff (T : ℝ) [Fact (0 < T)] (f : L2R T) : RealIndex → ℝ
  | none => (Expected.coefficient T (fun x => (f x : ℂ)) 0).re
  | some (n, false) => Real.sqrt 2 * (Expected.coefficient T (fun x => (f x : ℂ)) (n + 1)).re
  | some (n, true) => -Real.sqrt 2 * (Expected.coefficient T (fun x => (f x : ℂ)) (n + 1)).im

namespace Specs

def ComplexBasis : Prop := ∀ (T : ℝ) [Fact (0 < T)],
  ∃ b : HilbertBasis ℤ ℂ (L2C T),
    (∀ k, b k = fourierLp 2 k) ∧
    (∀ (f : L2C T) k, b.repr f k = Expected.coefficient T f k)

def IntervalCoefficient : Prop := ∀ (T : ℝ) [Fact (0 < T)]
    (f : L2C T) (k : ℤ) (a : ℝ),
  Expected.coefficient T f k = (1 / T : ℝ) • ∫ t in a..a + T,
    f (t : Expected.Circle T) * Complex.exp (-(2 * Real.pi * Complex.I * k * t / T))

def ComplexExpansion : Prop := ∀ (T : ℝ) [Fact (0 < T)] (f : L2C T),
  HasSum (fun k => Expected.coefficient T f k • fourierLp 2 k) f ∧
  HasSum (fun k => ‖Expected.coefficient T f k‖ ^ 2) (‖f‖ ^ 2)

/-- The finite vector is explicitly tied to the shared pointwise S_N, up to a.e. equality. -/
def PartialSumConvergence : Prop := ∀ (T : ℝ) [Fact (0 < T)] (f : L2C T),
  (∀ N : ℕ, (∑ k ∈ Expected.frequencies N,
      Expected.coefficient T f k • fourierLp 2 k : L2C T) =ᵐ[Expected.haar T]
        Expected.partialSum T N f) ∧
  Tendsto (fun N : ℕ => ∑ k ∈ Expected.frequencies N,
    Expected.coefficient T f k • fourierLp 2 k) atTop (𝓝 f)

def RealSymmetry : Prop := ∀ (T : ℝ) [Fact (0 < T)] (f : L2R T) (k : ℤ),
  Expected.coefficient T (fun x => (f x : ℂ)) (-k) =
    conj (Expected.coefficient T (fun x => (f x : ℂ)) k)

def RealWaveFormula : Prop := ∀ (T : ℝ) [Fact (0 < T)],
  (∀ x, realWave T none x = 1) ∧
  (∀ (n : ℕ) (t : ℝ),
    realWave T (some (n, false)) (t : Expected.Circle T) =
      Real.sqrt 2 * Real.cos (2 * Real.pi * (n + 1) * t / T) ∧
    realWave T (some (n, true)) (t : Expected.Circle T) =
      Real.sqrt 2 * Real.sin (2 * Real.pi * (n + 1) * t / T))

/-- This supplies the normalized real Hilbert basis, its coefficient correspondence,
reconstruction and Parseval. `HasSum` is the net over all finite subsets. -/
def RealBasis : Prop := ∀ (T : ℝ) [Fact (0 < T)],
  ∃ b : HilbertBasis RealIndex ℝ (L2R T),
    (∀ i, b i = realVector T i) ∧
    (∀ (f : L2R T) i, b.repr f i = realCoeff T f i) ∧
    (∀ f : L2R T, HasSum (fun i => realCoeff T f i • realVector T i) f) ∧
    (∀ f : L2R T, HasSum (fun i => (realCoeff T f i) ^ 2) (‖f‖ ^ 2))

end Specs
end P102.Periodic.FourierHilbert
