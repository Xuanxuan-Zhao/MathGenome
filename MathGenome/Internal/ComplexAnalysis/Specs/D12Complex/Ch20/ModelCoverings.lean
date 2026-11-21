import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.CoveringPaths
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! The models and full obligations of paper.tex:3405–3446.
Sheets are actual images of the displayed holomorphic inverse branches.
The finite sheet family is indexed by `Fin n`; its members are nonempty,
pairwise disjoint and exhaust the preimage, so the sheet number is exactly n.
The counterexample uses the affine parametrization t = ε(s-1) of [-ε,0]. -/

noncomputable section

namespace D12Complex.Ch20.ModelCoverings

abbrev PuncturedPlane := {z : ℂ // z ≠ 0}

def expProjection (z : ℂ) : PuncturedPlane := ⟨Complex.exp z, Complex.exp_ne_zero z⟩
def restrictedExp (z : PuncturedPlane) : PuncturedPlane := expProjection z

def powerProjection (n : ℕ) (z : PuncturedPlane) : PuncturedPlane :=
  ⟨(z : ℂ) ^ n, pow_ne_zero n z.property⟩

def period : ℂ := 2 * Real.pi * Complex.I

def expBranch (L : ℂ → ℂ) (k : ℤ) (z : ℂ) : ℂ := L z + k * period

def powerBranch (L : ℂ → ℂ) (n : ℕ) (k : Fin n) (z : ℂ) : ℂ :=
  Complex.exp ((L z + (k.val : ℂ) * period) / n)

def intervalParameter (ε : ℝ) (s : unitInterval) : ℂ := (ε * ((s : ℝ) - 1) : ℝ)

def terminalPath (ε : ℝ) (s : unitInterval) : PuncturedPlane :=
  expProjection (intervalParameter ε s)

end D12Complex.Ch20.ModelCoverings

namespace Specs.D12Complex.Ch20.ModelCoverings

open _root_.D12Complex _root_.D12Complex.Ch20 _root_.D12Complex.Ch20.ModelCoverings

/-- Surjectivity, topological covering and weak holomorphy of the exponential. -/
def exponential_covering : Prop :=
  Function.Surjective expProjection ∧ IsCovering expProjection ∧
    HolomorphicOn Set.univ Complex.exp

/-- Each nonzero point admits a zero-free disk and all integer inverse sheets. -/
def exponential_sheets : Prop :=
  ∀ b : ℂ, b ≠ 0 → ∃ (r : ℝ) (L : ℂ → ℂ),
    0 < r ∧ (∀ z ∈ Metric.ball b r, z ≠ 0) ∧
    HolomorphicOn (Metric.ball b r) L ∧
    (∀ z ∈ Metric.ball b r, Complex.exp (L z) = z) ∧
    Pairwise (fun j k : ℤ => Disjoint
      (expBranch L j '' Metric.ball b r) (expBranch L k '' Metric.ball b r)) ∧
    (⋃ k : ℤ, expBranch L k '' Metric.ball b r) = Complex.exp ⁻¹' Metric.ball b r ∧
    ∀ k : ℤ, BiholomorphicPair (expBranch L k '' Metric.ball b r)
      (Metric.ball b r) Complex.exp (expBranch L k)

/-- Positive powers on the punctured plane are surjective holomorphic coverings. -/
def power_covering : Prop :=
  ∀ n : ℕ, 0 < n → Function.Surjective (powerProjection n) ∧
    IsCovering (powerProjection n) ∧
    HolomorphicOn {z : ℂ | z ≠ 0} (fun z => z ^ n)

/-- The cardinality of every fiber is exactly the positive exponent. -/
def power_fiber_card : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ b : PuncturedPlane,
    Nat.card {z : PuncturedPlane // powerProjection n z = b} = n

/-- Exactly n nonempty inverse sheets, with the formulas specified in the paper. -/
def power_sheets : Prop :=
  ∀ (b : ℂ) (n : ℕ), b ≠ 0 → 0 < n → ∃ (r : ℝ) (L : ℂ → ℂ),
    0 < r ∧ (∀ z ∈ Metric.ball b r, z ≠ 0) ∧
    HolomorphicOn (Metric.ball b r) L ∧
    (∀ z ∈ Metric.ball b r, Complex.exp (L z) = z) ∧
    (∀ k : Fin n, (powerBranch L n k '' Metric.ball b r).Nonempty) ∧
    Pairwise (fun j k : Fin n => Disjoint
      (powerBranch L n j '' Metric.ball b r) (powerBranch L n k '' Metric.ball b r)) ∧
    (⋃ k : Fin n, powerBranch L n k '' Metric.ball b r) =
      (fun z : ℂ => z ^ n) ⁻¹' Metric.ball b r ∧
    ∀ k : Fin n, BiholomorphicPair (powerBranch L n k '' Metric.ball b r)
      (Metric.ball b r) (fun z => z ^ n) (powerBranch L n k)

/-- The restricted exponential remains onto and locally biholomorphic. -/
def restricted_exponential_local : Prop :=
  Function.Surjective restrictedExp ∧
    HolomorphicOn {z : ℂ | z ≠ 0} Complex.exp ∧
    ∀ a : ℂ, a ≠ 0 → ∃ (U V : Set ℂ) (L : ℂ → ℂ),
      a ∈ U ∧ Complex.exp a ∈ V ∧
      U ⊆ {z | z ≠ 0} ∧ V ⊆ {z | z ≠ 0} ∧ BiholomorphicPair U V Complex.exp L

/-- Every positive ε gives a continuous path on the whole closed interval
whose lift from -ε cannot remain in the punctured source at the final endpoint. -/
def restricted_exponential_no_lift : Prop :=
  ∀ ε : ℝ, 0 < ε → Continuous (terminalPath ε) ∧
    ¬ ∃ Γ : unitInterval → PuncturedPlane,
      Continuous Γ ∧ (Γ 0 : ℂ) = -(ε : ℂ) ∧ restrictedExp ∘ Γ = terminalPath ε

/-- A surjective local biholomorphism which fails the covering property. -/
def restricted_exponential_not_covering : Prop := ¬ IsCovering restrictedExp

end Specs.D12Complex.Ch20.ModelCoverings
