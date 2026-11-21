import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-! Poincaré on the original full-norm closure of compactly supported tests.
The gradient uses the Euclidean norm on the scalar coordinate vector.
No boundary regularity is imposed. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal

namespace ExpandedFA.Sobolev
open ExpandedFA.Distributions

def coordinateIndex {d : ℕ} (i : Fin d) : DerivativeIndex d 1 :=
  ⟨fun j => if j = i then 1 else 0, by
    simp only [apply_ite, Fin.val_one, Fin.val_zero]
    simp⟩

/-- The actual vector of weak first partial derivatives, with its Euclidean norm. -/
def gradientFunction {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue 𝕜 d Ω 1 p)
    (x : Domain d) : PiLp 2 (fun _ : Fin d => 𝕜) :=
  WithLp.toLp 2 (fun i => u.val (coordinateIndex i) x)

/-- Lp norm of the Euclidean gradient, on the same restricted measure as u. -/
def gradientLpNorm {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue 𝕜 d Ω 1 p) : ℝ :=
  (eLpNorm (gradientFunction u) p (volume.restrict (Ω : Set (Domain d)))).toReal

end ExpandedFA.Sobolev

namespace Specs.ExpandedFA.Sobolev.PoincareInequality
open _root_.ExpandedFA.Sobolev _root_.ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- The stronger directional estimate on any open set in a coordinate strip. -/
def CoordinateStrip : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)) (i : Fin d) (a b : ℝ), a < b →
  (∀ x ∈ Ω, a < x i ∧ x i < b) →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : ZeroSpaceValue 𝕜 d Ω 1 p hp),
    ‖u.val.val (zeroIndex d 1)‖ ≤ (b - a) * ‖u.val.val (coordinateIndex i)‖

/-- In particular the original gradient inequality holds whenever one existing
coordinate projection is bounded, even if Ω is unbounded in other directions. -/
def BoundedProjection : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)) (i : Fin d),
  Bornology.IsBounded ((fun x : Domain d => x i) '' (Ω : Set (Domain d))) →
  ∃ C : ℝ, 0 < C ∧
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (u : ZeroSpaceValue 𝕜 d Ω 1 p hp),
    ‖u.val.val (zeroIndex d 1)‖ ≤ C * gradientLpNorm u.val

/-- Arbitrary bounded open sets, including the empty set in every dimension. -/
def BoundedDomain : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
  (0 < d ∨ (Ω : Set (Domain d)) = ∅) →
  ∃ C : ℝ, 0 < C ∧
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (u : ZeroSpaceValue 𝕜 d Ω 1 p hp),
    ‖u.val.val (zeroIndex d 1)‖ ≤ C * gradientLpNorm u.val

/-- The degenerate empty-domain case has no positive-dimension premise. -/
def EmptyDomain : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)), (Ω : Set (Domain d)) = ∅ →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : ZeroSpaceValue 𝕜 d Ω 1 p hp),
    ‖u.val.val (zeroIndex d 1)‖ = 0

end Specs.ExpandedFA.Sobolev.PoincareInequality
