import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Dini
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-! Independent specification of the full Dini / Dirichlet--Jordan theorem,
paper.tex:305–330. The BV alternative is local and allows arbitrary null
modifications of each one-sided representative. It includes complex functions.
Neither BV hypothesis contains a Dini integrability assumption. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Real

namespace P102.Periodic.Expected.DirichletJordan
open Dini (offset residual)

/-- A one-sided function has a BV representative with the prescribed right limit.
The equality uses Lebesgue measure in the angular variable. -/
def BVSide (φ : ℝ → ℂ) (a : ℂ) (δ : ℝ) : Prop :=
  ∃ g : ℝ → ℂ, BoundedVariationOn g (Ioo 0 δ) ∧
    φ =ᵐ[volume.restrict (Ioo 0 δ)] g ∧ Tendsto g (𝓝[>] 0) (𝓝 a)

/-- The componentwise form permits different representatives for the real and
imaginary components, and therefore explicitly includes separate real/imaginary
BV applicability. -/
def ComponentBVSide (φ : ℝ → ℂ) (a : ℂ) (δ : ℝ) : Prop :=
  ∃ u v : ℝ → ℝ, BoundedVariationOn u (Ioo 0 δ) ∧
    BoundedVariationOn v (Ioo 0 δ) ∧
    (fun t => (φ t).re) =ᵐ[volume.restrict (Ioo 0 δ)] u ∧
    (fun t => (φ t).im) =ᵐ[volume.restrict (Ioo 0 δ)] v ∧
    Tendsto u (𝓝[>] 0) (𝓝 a.re) ∧ Tendsto v (𝓝[>] 0) (𝓝 a.im)

def componentBridgeStatement : Prop :=
  ∀ (φ : ℝ → ℂ) (a : ℂ) (δ : ℝ), ComponentBVSide φ a δ → BVSide φ a δ

def jordanStatement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f : Circle T → ℂ), Integrable f (haar T) →
    ∀ (x : Circle T) (aPlus aMinus : ℂ) (δ : ℝ), 0 < δ →
      BVSide (fun v => f (x + offset T v)) aPlus δ →
      BVSide (fun v => f (x - offset T v)) aMinus δ →
      Tendsto (fun N : ℕ => partialSum T N f x) atTop (𝓝 ((aPlus + aMinus) / 2))

def componentsStatement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f : Circle T → ℂ), Integrable f (haar T) →
    ∀ (x : Circle T) (aPlus aMinus : ℂ) (δ : ℝ), 0 < δ →
      ComponentBVSide (fun v => f (x + offset T v)) aPlus δ →
      ComponentBVSide (fun v => f (x - offset T v)) aMinus δ →
      Tendsto (fun N : ℕ => partialSum T N f x) atTop (𝓝 ((aPlus + aMinus) / 2))

def jordanL1Statement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f : L1 T) (x : Circle T)
    (aPlus aMinus : ℂ) (δ : ℝ), 0 < δ →
      BVSide (fun v => f (x + offset T v)) aPlus δ →
      BVSide (fun v => f (x - offset T v)) aMinus δ →
      Tendsto (fun N : ℕ => partialSum T N f x) atTop (𝓝 ((aPlus + aMinus) / 2))

/-- The two sufficient conditions are alternatives, with exactly the same
ordinary symmetric Fourier partial sums in both conclusions. -/
def alternativesStatement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f : Circle T → ℂ), Integrable f (haar T) →
    ∀ (x : Circle T) (L : ℂ),
      ((∃ δ : ℝ, 0 < δ ∧
        IntegrableOn (fun v => ‖residual T f x L v‖ / v) (Ioo 0 δ)) ∨
       (∃ (aPlus aMinus : ℂ) (δ : ℝ), 0 < δ ∧
         BVSide (fun v => f (x + offset T v)) aPlus δ ∧
         BVSide (fun v => f (x - offset T v)) aMinus δ ∧
         L = (aPlus + aMinus) / 2)) →
      Tendsto (fun N : ℕ => partialSum T N f x) atTop (𝓝 L)

/-- The separate Dini corollary and the midpoint identification are retained
as part of the complete source theorem, reusing the upstream interfaces. -/
def symmetricDiniStatement : Prop := Dini.symmetricStatement

def separateDiniStatement : Prop := Dini.separateStatement

def midpointStatement : Prop := Dini.midpointStatement

end P102.Periodic.Expected.DirichletJordan
