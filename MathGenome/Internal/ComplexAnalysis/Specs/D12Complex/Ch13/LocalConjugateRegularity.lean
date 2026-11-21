import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.HarmonicFoundation
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.TaylorSmoothness
import Mathlib.Analysis.Analytic.Basic

/-! Independent statements for the local and regularity conclusions of
paper.tex:2539–2548, d12:13-02. No connectedness or simple connectivity
is required. Harmonicity retains the original C² differential definition. -/
noncomputable section
open Complex Set Metric
open scoped ContDiff

namespace D12Complex

/-- A conjugate of u is a real v for which u + i v is holomorphic. -/
def HarmonicConjugateOn (U : Set ℂ) (u v : ℂ → ℝ) : Prop :=
  HolomorphicOn U (fun z => (u z : ℂ) + I * (v z : ℂ))

end D12Complex

namespace Specs.D12Complex.Ch13.LocalConjugateRegularity
open _root_.D12Complex

def HarmonicConjugateOn_type := Set ℂ → (ℂ → ℝ) → (ℂ → ℝ) → Prop
def HarmonicConjugateOn_value : HarmonicConjugateOn_type :=
  fun U u v => HolomorphicOn U (fun z => (u z : ℂ) + I * (v z : ℂ))

def conjugate_harmonic_type : Prop :=
  ∀ (U : Set ℂ) (u v : ℂ → ℝ), HarmonicConjugateOn U u v →
    HarmonicOn U u ∧ HarmonicOn U v

def conjugate_partials_type : Prop :=
  ∀ (U : Set ℂ) (u v : ℂ → ℝ), HarmonicConjugateOn U u v →
    ∀ z ∈ U, partialX v z = -partialY u z ∧ partialY v z = partialX u z

/-- The neighborhood can be chosen to be a disk, inside the original open set. -/
def local_conjugate_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ), HarmonicOn U u → ∀ a ∈ U,
    ∃ r : ℝ, 0 < r ∧ ball a r ⊆ U ∧ ∃ v : ℂ → ℝ,
      HarmonicOn (ball a r) v ∧ HarmonicConjugateOn (ball a r) u v

def harmonic_real_analytic_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ), HarmonicOn U u → AnalyticOnNhd ℝ u U

def harmonic_smooth_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ), HarmonicOn U u → ContDiffOn ℝ ∞ u U

/-- A local real analytic expansion is explicitly realized as the real part
of a convergent holomorphic Taylor series. Both sums have their actual values;
the coefficients are the canonical complex Taylor coefficients. -/
def harmonic_real_taylor_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ), HarmonicOn U u → ∀ a ∈ U,
    ∃ r : ℝ, 0 < r ∧ ball a r ⊆ U ∧ ∃ F : ℂ → ℂ,
      HolomorphicOn (ball a r) F ∧
      EqOn (fun z => (F z).re) u (ball a r) ∧
      ∀ z ∈ ball a r,
        HasSum (fun n => Taylor.coefficients F a n * (z - a)^n) (F z) ∧
        HasSum (fun n => (Taylor.coefficients F a n * (z - a)^n).re) (u z)

end Specs.D12Complex.Ch13.LocalConjugateRegularity
