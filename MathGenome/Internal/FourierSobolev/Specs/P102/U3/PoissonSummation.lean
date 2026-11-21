import MathGenome.Internal.FourierSobolev.Specs.P102.U3.SchwartzFourier
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Independent statement of paper.tex:1136–1147 (p102:U3-01).
The index type is the ordinary integer lattice, with unconditional finite-subset
partial sums. The factor (T^d)⁻¹ is T^{-d}; no positive-dimensional premise is used. -/
noncomputable section
open scoped FourierTransform

namespace P102.U3.PoissonSummation
open P102.Specs.U3

/-- Standard coordinate inclusion of ℤ^d in Euclidean ℝ^d. -/
def latticePoint {d : ℕ} (k : Fin d → ℤ) : Euclidean d :=
  WithLp.toLp 2 (fun i => (k i : ℝ))

/-- A term of the spatial periodization at spacing T. -/
def spatialTerm {d : ℕ} (T : ℝ) (φ : Test d) (k : Fin d → ℤ)
    (x : Euclidean d) : ℂ := φ (x + T • latticePoint k)

/-- A term of the dual-lattice Fourier series; the pairing is the Euclidean dot product. -/
def fourierTerm {d : ℕ} (T : ℝ) (φ : Test d) (m : Fin d → ℤ)
    (x : Euclidean d) : ℂ :=
  fourierValue d φ (T⁻¹ • latticePoint m) *
    Complex.exp (((2 * Real.pi * inner ℝ (latticePoint m) x / T : ℝ) : ℂ) * Complex.I)

end P102.U3.PoissonSummation

namespace P102.Specs.U3.PoissonSummation
open P102.U3.PoissonSummation

/-- Absolute convergence at every point, local uniform convergence on both sides,
global uniform convergence on the Fourier side, and the cubical Poisson identity.
This includes d=0, where both index and Euclidean spaces are singletons of mass one. -/
def poissonSummation_type : Prop :=
  ∀ (d : ℕ) (φ : Test d) (T : ℝ), 0 < T →
    (∀ x : Euclidean d, Summable (fun k : Fin d → ℤ => ‖spatialTerm T φ k x‖)) ∧
    (∀ x : Euclidean d, Summable (fun m : Fin d → ℤ => ‖fourierTerm T φ m x‖)) ∧
    TendstoLocallyUniformly
      (fun s : Finset (Fin d → ℤ) => fun x => ∑ k ∈ s, spatialTerm T φ k x)
      (fun x => ∑' k : Fin d → ℤ, spatialTerm T φ k x) Filter.atTop ∧
    TendstoLocallyUniformly
      (fun s : Finset (Fin d → ℤ) => fun x => ∑ m ∈ s, fourierTerm T φ m x)
      (fun x => ∑' m : Fin d → ℤ, fourierTerm T φ m x) Filter.atTop ∧
    TendstoUniformly
      (fun s : Finset (Fin d → ℤ) => fun x => ∑ m ∈ s, fourierTerm T φ m x)
      (fun x => ∑' m : Fin d → ℤ, fourierTerm T φ m x) Filter.atTop ∧
    (∀ x : Euclidean d,
      (∑' k : Fin d → ℤ, spatialTerm T φ k x) =
        ((T ^ d)⁻¹ : ℝ) • (∑' m : Fin d → ℤ, fourierTerm T φ m x))

end P102.Specs.U3.PoissonSummation
