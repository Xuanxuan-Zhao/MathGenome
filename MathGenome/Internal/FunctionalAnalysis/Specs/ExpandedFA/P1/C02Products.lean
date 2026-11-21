import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Norm
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Banach
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Operator.Basic

/-!
Independent statements for `fa2:p1:c02:products`, paper.tex lines 464–474.
A finite dependent family includes `Fin n` with the manuscript's coordinate
`j+1` represented by `j : Fin n`. No factor is assumed complete or nonzero.
`PiLp p E` is a copy of the full Cartesian product, with coordinatewise module
operations and its actual p-norm metric. The infinity formula uses a finite
supremum in the nonnegative reals, whose empty value is zero.
-/

noncomputable section
open scoped ENNReal NNReal
universe u v w

namespace ExpandedFA.P1.C02Products.Spec

/-- The displayed power-sum formula on the original Cartesian product. -/
def ProductPNormType :=
  ∀ {ι : Type u} [Fintype ι] (E : ι → Type v) [∀ i, NormedAddCommGroup (E i)],
    ℝ → (∀ i, E i) → ℝ

def ProductPNormValue : ProductPNormType.{u,v} :=
  fun E _ p x => (∑ i, ‖x i‖ ^ p) ^ (1 / p)

/-- Finite maximum with the explicit empty-family convention. -/
def ProductMaxNormType :=
  ∀ {ι : Type u} [Fintype ι] (E : ι → Type v) [∀ i, NormedAddCommGroup (E i)],
    (∀ i, E i) → ℝ

def ProductMaxNormValue : ProductMaxNormType.{u,v} :=
  fun E _ x => ((Finset.univ.sup (fun i => ‖x i‖₊) : ℝ≥0) : ℝ)

/-- These formulas are the norms of the canonical normed product spaces. -/
def NormFormulas : Prop :=
  ∀ {ι : Type u} [Fintype ι] (E : ι → Type v) [∀ i, NormedAddCommGroup (E i)]
    (p : ℝ) (hp : 1 ≤ p) (x : ∀ i, E i),
    ‖WithLp.toLp (ENNReal.ofReal p) x‖ = ProductPNormValue E p x ∧
    ‖WithLp.toLp ∞ x‖ = ProductMaxNormValue E x

/-- Definiteness, homogeneity, nonnegativity and Minkowski on the full product. -/
def FormulaNormAxioms : Prop :=
  ∀ (𝕜 : Type w) [RCLike 𝕜] {ι : Type u} [Fintype ι]
    (E : ι → Type v) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    (p : ℝ), 1 ≤ p →
    ExpandedFA.P1.C01Norm.NormAxioms 𝕜 (ProductPNormValue E p) ∧
    ExpandedFA.P1.C01Norm.NormAxioms 𝕜 (ProductMaxNormValue E)

/-- Identification with the product topology and with every other allowed norm.
The maps preserve every coordinate, rather than being unspecified homeomorphisms. -/
def SameTopology : Prop :=
  ∀ {ι : Type u} [Fintype ι] (E : ι → Type v) [∀ i, NormedAddCommGroup (E i)]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)],
    IsHomeomorph (WithLp.ofLp : PiLp p E → ∀ i, E i) ∧
    IsHomeomorph (fun x : PiLp p E => WithLp.toLp q (WithLp.ofLp x))

/-- The precise dimension-dependent estimates, including cardinality zero. -/
def NormComparison : Prop :=
  ∀ {ι : Type u} [Fintype ι] (E : ι → Type v) [∀ i, NormedAddCommGroup (E i)]
    (p : ℝ), 1 ≤ p → ∀ x : ∀ i, E i,
    ProductMaxNormValue E x ≤ ProductPNormValue E p x ∧
    ProductPNormValue E p x ≤
      (Fintype.card ι : ℝ) ^ (1 / p) * ProductMaxNormValue E x

/-- Bounded linear projections and zero-filled inclusions for every p, including
infinity. Their coordinates are specified, and both operator norms are ≤ 1. -/
def CoordinateMaps : Prop :=
  ∀ (𝕜 : Type w) [RCLike 𝕜] {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E : ι → Type v) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : ι),
    ∃ P : PiLp p E →L[𝕜] E i,
      (∀ x, P x = x i) ∧ ‖P‖ ≤ 1 ∧
      ∃ I : E i →L[𝕜] PiLp p E,
        (∀ a, WithLp.ofLp (I a) = Pi.single i a) ∧ ‖I‖ ≤ 1

/-- Banach completeness in the displayed p-norm is equivalent to completeness
of every factor, with no completeness assumed on either side. -/
def BanachIff : Prop :=
  ∀ {ι : Type u} [Fintype ι] (E : ι → Type v) [∀ i, NormedAddCommGroup (E i)]
    (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ExpandedFA.P1.C01Banach.Spec.IsBanachSpaceValue (PiLp p E) ↔
      ∀ i, ExpandedFA.P1.C01Banach.Spec.IsBanachSpaceValue (E i)

/-- The empty Cartesian product is the zero space, its maximum and all allowed
p-norms are zero, and its Banach assertion has a vacuous right-hand side. -/
def EmptyProduct : Prop :=
  ∀ {ι : Type u} [Fintype ι] [IsEmpty ι] (E : ι → Type v)
    [∀ i, NormedAddCommGroup (E i)] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    (∀ x : PiLp p E, x = 0 ∧ ‖x‖ = 0) ∧
    (∀ x : ∀ i, E i, ProductMaxNormValue E x = 0) ∧
    ExpandedFA.P1.C01Banach.Spec.IsBanachSpaceValue (PiLp p E) ∧
    (∀ i, ExpandedFA.P1.C01Banach.Spec.IsBanachSpaceValue (E i))

end ExpandedFA.P1.C02Products.Spec
