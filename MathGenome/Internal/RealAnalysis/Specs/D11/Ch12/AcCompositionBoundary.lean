import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.BvDefinition
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Independent specification for the example at paper.tex:4247–4268.
The real cube root is defined on both signs, rather than using real rpow
on negative arguments. The cube identity is an explicit bridge.
All AC and variation assertions use the shared classical definitions. -/

noncomputable section
open Set
open scoped NNReal ENNReal

namespace Specs.D11.Ch12.AcCompositionBoundary

abbrev scalarFunctionType := ℝ → ℝ

def cubeRoot (t : ℝ) : ℝ :=
  if 0 ≤ t then t ^ (1 / 3 : ℝ) else -((-t) ^ (1 / 3 : ℝ))

def oscillation (x : ℝ) : ℝ :=
  if x = 0 then 0 else x ^ 2 * Real.cos (Real.pi / (2 * x))

def oscillationDerivative (x : ℝ) : ℝ :=
  if x = 0 then 0 else
    2 * x * Real.cos (Real.pi / (2 * x)) +
      (Real.pi / 2) * Real.sin (Real.pi / (2 * x))

def cubeRoot_cube : Prop := ∀ t : ℝ, cubeRoot t ^ 3 = t

def cubeRoot_ac : Prop :=
  Specs.D11.Ch12.absolutelyContinuousOnIntervalValue cubeRoot (-1) 1

def oscillation_derivative : Prop :=
  ∀ x : ℝ, HasDerivAt oscillation (oscillationDerivative x) x

def oscillation_derivative_bound : Prop :=
  ∀ x ∈ Icc (-1 : ℝ) 1, |oscillationDerivative x| ≤ 2 + Real.pi / 2

def oscillation_lipschitz : Prop :=
  ∃ L : ℝ≥0, LipschitzOnWith L oscillation (Icc (-1 : ℝ) 1)

def oscillation_ac : Prop :=
  Specs.D11.Ch12.absolutelyContinuousOnIntervalValue oscillation (-1) 1

/-- The inner function actually has values in the outer function's interval. -/
def oscillation_mapsTo : Prop := MapsTo oscillation (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1)

/-- The displayed alternating values, indexed from n = 1. -/
def composition_values : Prop :=
  ∀ n : ℕ, 0 < n →
    cubeRoot (oscillation (1 / (2 * (n : ℝ)))) =
      (-1 : ℝ) ^ n * (2 * (n : ℝ)) ^ (-(2 / 3 : ℝ))

def composition_variation : Prop :=
  Specs.D11.Ch12.variation_value (cubeRoot ∘ oscillation) (-1) 1 = ⊤

def composition_not_bv : Prop :=
  ¬ Specs.D11.Ch12.BV_value (cubeRoot ∘ oscillation) (-1) 1

/-- Only Lipschitz control on the actual range is required. The scalar fields
may independently be real or complex. Ambient presentations impose no
condition on the values of the outer map away from that range. -/
def lipschitz_outer_comp : Prop :=
  ∀ {𝕂 𝕃 : Type*} [RCLike 𝕂] [RCLike 𝕃]
    {a b : ℝ} {g : ℝ → 𝕂} (H : 𝕂 → 𝕃) {L : ℝ≥0}, a < b →
    LipschitzOnWith L H (g '' Icc a b) →
    Specs.D11.Ch12.absolutelyContinuousOnIntervalValue g a b →
    Specs.D11.Ch12.absolutelyContinuousOnIntervalValue (H ∘ g) a b

/-- An outer map whose domain is only a subset of the scalar field is
evaluated on the inner map's range. Zero outside that domain merely supplies
an ambient presentation; those values are never tested on the interval. -/
def rangeComposition {𝕂 𝕃 : Type*} [RCLike 𝕂] [RCLike 𝕃]
    (g : ℝ → 𝕂) (s : Set 𝕂) (H : s → 𝕃) (x : ℝ) : 𝕃 := by
  classical
  exact if hx : g x ∈ s then H ⟨g x, hx⟩ else 0

def lipschitz_outer_subtype_comp : Prop :=
  ∀ {𝕂 𝕃 : Type*} [RCLike 𝕂] [RCLike 𝕃]
    {a b : ℝ} {g : ℝ → 𝕂} {s : Set 𝕂} (H : s → 𝕃) {L : ℝ≥0}, a < b →
    MapsTo g (Icc a b) s → LipschitzWith L H →
    Specs.D11.Ch12.absolutelyContinuousOnIntervalValue g a b →
    Specs.D11.Ch12.absolutelyContinuousOnIntervalValue (rangeComposition g s H) a b

end Specs.D11.Ch12.AcCompositionBoundary
