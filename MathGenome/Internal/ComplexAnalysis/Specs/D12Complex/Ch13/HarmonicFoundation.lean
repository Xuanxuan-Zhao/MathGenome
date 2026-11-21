import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.RealComplexDifferential
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-! The differential definition in paper.tex:2531–2537. All functions are total;
regularity and equations are imposed only on the indicated open set. The
coordinate derivatives are the actual real slice derivatives defined in Ch01. -/
noncomputable section

namespace D12Complex

/-- The coordinate Laplacian of a real function on the complex plane. -/
def coordinateLaplacian (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  partialX (partialX u) z + partialY (partialY u) z

/-- Real harmonicity: C² and zero coordinate Laplacian on an open set. -/
def HarmonicOn (U : Set ℂ) (u : ℂ → ℝ) : Prop :=
  IsOpen U ∧ ContDiffOn ℝ 2 u U ∧ ∀ z ∈ U, coordinateLaplacian u z = 0

end D12Complex

namespace Specs.D12Complex.Ch13.HarmonicFoundation
open _root_.D12Complex InnerProductSpace Laplacian

def coordinateLaplacian_type := (ℂ → ℝ) → ℂ → ℝ
def coordinateLaplacian_value : coordinateLaplacian_type :=
  fun u z => partialX (partialX u) z + partialY (partialY u) z

def HarmonicOn_type := Set ℂ → (ℂ → ℝ) → Prop
def HarmonicOn_value : HarmonicOn_type :=
  fun U u => IsOpen U ∧ ContDiffOn ℝ 2 u U ∧
    ∀ z ∈ U, coordinateLaplacian u z = 0

def coordinateLaplacian_eq_laplacian_type : Prop :=
  ∀ (u : ℂ → ℝ) (z : ℂ), ContDiffAt ℝ 2 u z →
    coordinateLaplacian u z = Δ u z

def harmonicOn_iff_harmonicOnNhd_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ), IsOpen U →
    (HarmonicOn U u ↔ HarmonicOnNhd u U)

def holomorphic_harmonic_re_type : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℂ), HolomorphicOn U f →
    HarmonicOn U (fun z => (f z).re)

def holomorphic_harmonic_im_type : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℂ), HolomorphicOn U f →
    HarmonicOn U (fun z => (f z).im)

/-- The chain rule is stated for every C² real function, including nonharmonic
ones. In particular no injectivity or nonzero derivative is assumed. -/
def coordinateLaplacian_comp_holomorphic_type : Prop :=
  ∀ (U V : Set ℂ) (u : ℂ → ℝ) (F : ℂ → ℂ),
    IsOpen U → ContDiffOn ℝ 2 u U → HolomorphicOn V F →
    Set.MapsTo F V U → ∀ z ∈ V,
    coordinateLaplacian (u ∘ F) z =
      ‖deriv F z‖ ^ 2 * coordinateLaplacian u (F z)

def harmonicOn_comp_holomorphic_type : Prop :=
  ∀ (U V : Set ℂ) (u : ℂ → ℝ) (F : ℂ → ℂ),
    HarmonicOn U u → HolomorphicOn V F → Set.MapsTo F V U →
    HarmonicOn V (u ∘ F)

end Specs.D12Complex.Ch13.HarmonicFoundation
