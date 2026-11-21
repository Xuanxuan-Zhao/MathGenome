import MathGenome.Internal.FourierSobolev.Specs.P102.U3.SchwartzFourier
import MathGenome.Internal.FourierSobolev.Specs.P102.U3.Plancherel
import MathGenome.Internal.FourierSobolev.Specs.P102.U3.FourierConvolution
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Independent specification of the dyadic-kernel stage of paper.tex:1206–1231.
Ordered coordinate derivatives represent all multi-indices, including order zero.
All measures are standard Euclidean volume. No assumption on the value m(0) is made.
The cutoff is chosen before, and independently of, the symbol and its bound. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff

namespace P102.U3.Mihlin
open P102.Specs.U3 (Euclidean)

/-- The least integer strictly greater than d/2. -/
def order (d : ℕ) : ℕ := d / 2 + 1

/-- Real dyadic scale, also for negative integer indices. -/
def scale (j : ℤ) : ℝ := (2 : ℝ) ^ j

/-- Smooth real radial cutoff. The range condition is available for the chosen cutoff. -/
def IsCutoff {d : ℕ} (χ : Euclidean d → ℝ) : Prop :=
  ContDiff ℝ ∞ χ ∧
  (∀ x y, ‖x‖ = ‖y‖ → χ x = χ y) ∧
  (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
  (∀ x, ‖x‖ ≤ 1 → χ x = 1) ∧
  (∀ x, 2 ≤ ‖x‖ → χ x = 0)

def annulus {d : ℕ} (χ : Euclidean d → ℝ) (ξ : Euclidean d) : ℝ :=
  χ ξ - χ ((2 : ℝ) • ξ)

def block {d : ℕ} (χ : Euclidean d → ℝ) (j : ℤ) (ξ : Euclidean d) : ℝ :=
  annulus χ (scale (-j) • ξ)

/-- A locally finite partition with an absolute uniform overlap bound. -/
def IsPartition {d : ℕ} (χ : Euclidean d → ℝ) : Prop :=
  (∀ ξ, annulus χ ξ ≠ 0 → (1 / 2 : ℝ) < ‖ξ‖ ∧ ‖ξ‖ < 2) ∧
  (∀ ξ, ξ ≠ 0 → HasSum (fun j : ℤ => block χ j ξ) 1) ∧
  (∀ ξ, (Function.support (fun j : ℤ => block χ j ξ)).Finite) ∧
  (∃ B : ℕ, ∀ (ξ : Euclidean d) (J : Finset ℤ),
    (J.filter (fun j => block χ j ξ ≠ 0)).card ≤ B)

/-- The source's C^N off-origin symbol and coordinate derivative hypothesis.
In particular, n=0 is the bound |m(ξ)|≤A off zero. -/
def SymbolBound {d : ℕ} (m : Euclidean d → ℂ) (A : ℝ) : Prop :=
  ContDiffOn ℝ (order d) m ({0}ᶜ : Set (Euclidean d)) ∧
  ∀ (n : ℕ), n ≤ order d → ∀ (β : Fin n → Fin d) (ξ : Euclidean d), ξ ≠ 0 →
    ‖iteratedFDeriv ℝ n m ξ (P102.U3.coordinateVector ∘ β)‖ ≤
      A * ‖ξ‖ ^ (-(n : ℤ))

def annularSymbol {d : ℕ} (χ : Euclidean d → ℝ) (m : Euclidean d → ℂ)
    (j : ℤ) (ξ : Euclidean d) : ℂ :=
  m (scale j • ξ) * (annulus χ ξ : ℂ)

/-- The positive-sign integral transform, rather than a Schwartz assumption. -/
def inverseKernel {d : ℕ} (χ : Euclidean d → ℝ) (m : Euclidean d → ℂ)
    (j : ℤ) : Euclidean d → ℂ := 𝓕⁻ (annularSymbol χ m j)

/-- Coordinate gradient with its Euclidean norm. -/
def gradient {d : ℕ} (f : Euclidean d → ℂ) (x : Euclidean d) :
    EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 (fun k => fderiv ℝ f x (P102.U3.coordinateVector k))

def dilatedKernel {d : ℕ} (χ : Euclidean d → ℝ) (m : Euclidean d → ℂ)
    (j : ℤ) (x : Euclidean d) : ℂ :=
  (scale j ^ d : ℝ) • inverseKernel χ m j (scale j • x)

def finiteKernel {d : ℕ} (χ : Euclidean d → ℝ) (m : Euclidean d → ℂ)
    (J : Finset ℤ) (x : Euclidean d) : ℂ := ∑ j ∈ J, dilatedKernel χ m j x

def finiteSymbol {d : ℕ} (χ : Euclidean d → ℝ) (m : Euclidean d → ℂ)
    (J : Finset ℤ) (ξ : Euclidean d) : ℂ :=
  m ξ * ((∑ j ∈ J, block χ j ξ : ℝ) : ℂ)

/-- MemLp clauses prevent the totalized real norm from hiding infinite norms. -/
def KernelEstimates {d : ℕ} (χ : Euclidean d → ℝ) (m : Euclidean d → ℂ)
    (A C : ℝ) : Prop :=
  ∀ j : ℤ,
    let L := inverseKernel χ m j
    let wL := fun x => ((1 + ‖x‖) ^ order d : ℝ) • L x
    let wgL := fun x => ((1 + ‖x‖) ^ order d : ℝ) • gradient L x
    ContDiff ℝ ∞ L ∧
    MemLp wL 2 ∧ MemLp wgL 2 ∧
    (eLpNorm wL 2 volume).toReal + (eLpNorm wgL 2 volume).toReal ≤ C * A ∧
    Integrable L ∧ Integrable (gradient L) ∧
    (∫ x, ‖L x‖) + (∫ x, ‖gradient L x‖) ≤ C * A ∧
    ∀ R : ℝ, 1 ≤ R →
      (∫ x in {x | R < ‖x‖}, ‖L x‖) ≤
        C * A * R ^ (-((order d : ℝ) - (d : ℝ) / 2))

/-- The L² operator is specified by its actual a.e. multiplier and convolution
representatives, for every L² input. The Fourier transform here is canonical L²
Plancherel. The Hörmander constant is uniform over all finite sets of scales. -/
def FiniteSumEstimates {d : ℕ} (χ : Euclidean d → ℝ) (m : Euclidean d → ℂ)
    (A C : ℝ) : Prop :=
  ∀ J : Finset ℤ,
    let K := finiteKernel χ m J
    Integrable K ∧
    (∀ ξ, 𝓕 K ξ = finiteSymbol χ m J ξ) ∧
    (∃ T : Lp (α := Euclidean d) ℂ 2 volume →L[ℂ]
        Lp (α := Euclidean d) ℂ 2 volume,
      ‖T‖ ≤ C * A ∧ ∀ f : Lp (α := Euclidean d) ℂ 2 volume,
        ((𝓕 (T f) : Lp (α := Euclidean d) ℂ 2 volume) : Euclidean d → ℂ)
          =ᵐ[volume] (fun ξ => finiteSymbol χ m J ξ * (𝓕 f : Lp (α := Euclidean d) ℂ 2 volume) ξ) ∧
        (∀ᵐ x, Integrable (fun y => K (x - y) * f y)) ∧
        (T f : Euclidean d → ℂ) =ᵐ[volume]
          (fun x => ∫ y, K (x - y) * f y)) ∧
    (∀ h : Euclidean d, h ≠ 0 →
      IntegrableOn (fun x => ‖K (x - h) - K x‖) {x | 2 * ‖h‖ < ‖x‖} ∧
      (∫ x in {x | 2 * ‖h‖ < ‖x‖}, ‖K (x - h) - K x‖) ≤ C * A)

end P102.U3.Mihlin

namespace P102.Specs.U3.MihlinDyadicKernels
open P102.U3.Mihlin

def theoremType : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ (χ : Euclidean d → ℝ) (C : ℝ),
    0 < C ∧ IsCutoff χ ∧ IsPartition χ ∧
    ∀ (m : Euclidean d → ℂ) (A : ℝ), SymbolBound m A →
      KernelEstimates χ m A C ∧ FiniteSumEstimates χ m A C

/-- Subtarget retained for partial cutoff construction. -/
def cutoffExistenceType : Prop := ∀ d : ℕ, ∃ χ : Euclidean d → ℝ, IsCutoff χ

def cutoffPartitionType : Prop :=
  ∀ d : ℕ, ∃ χ : Euclidean d → ℝ, IsCutoff χ ∧ IsPartition χ

def annularSymbolPropertiesType : Prop :=
  ∀ (d : ℕ) (χ : Euclidean d → ℝ), IsCutoff χ →
    ∀ (m : Euclidean d → ℂ) (A : ℝ), SymbolBound m A → ∀ j : ℤ,
      ContDiff ℝ (order d) (annularSymbol χ m j) ∧
      HasCompactSupport (annularSymbol χ m j) ∧ Integrable (annularSymbol χ m j) ∧
      ContDiff ℝ ∞ (inverseKernel χ m j)

def finiteSymbolBoundType : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ χ : Euclidean d → ℝ, IsCutoff χ →
    ∀ (m : Euclidean d → ℂ) (A : ℝ), SymbolBound m A →
      ∀ (J : Finset ℤ) (ξ : Euclidean d), ‖finiteSymbol χ m J ξ‖ ≤ 2 * A

end P102.Specs.U3.MihlinDyadicKernels
