import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.BanachSumDefinitions

/-! Full proposition types for Arbitrary Banach sums, paper.tex:6234–6269.
The carriers, norms, truncations and coordinate maps are the accepted native
ones. Exponents range over all real p ≥ 1, with ∞ treated separately.
The index type may be empty; no summand is required to be nonzero. -/

open scoped ENNReal Classical
noncomputable section
universe u v w
namespace ExpandedFA.Supplements.BanachSums.Spec
open ExpandedFA.Supplements.BanachSumDefinitions.Spec

/-- Completeness in the displayed finite-power-sum norm. -/
def CompletePowerSum : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, CompleteSpace (E i)] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    p ≠ ∞ → CompleteSpace (Space E p)

/-- Completeness in the supremum norm, including the empty product. -/
def CompleteBoundedProduct : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, CompleteSpace (E i)], CompleteSpace (BoundedProduct E)

/-- The exact finite-level-set c₀ condition defines a closed subspace. -/
def ClosedC0 : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
    {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
    IsClosed (c0Submodule (𝕜 := 𝕜) E : Set (BoundedProduct E))

def CompleteC0 : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, CompleteSpace (E i)]
    {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
    CompleteSpace (C0Space (𝕜 := 𝕜) E)

/-- Operator norm at most one states contractivity for all four maps.
The exponent may be ∞, so the first pair covers the bounded product too. -/
def ContractiveCoordinates : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
    {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : I),
    ‖coordinate (𝕜 := 𝕜) E p i‖ ≤ 1 ∧
    ‖inclusion (𝕜 := 𝕜) E p i‖ ≤ 1 ∧
    ‖c0Coordinate (𝕜 := 𝕜) E i‖ ≤ 1 ∧
    ‖c0Inclusion (𝕜 := 𝕜) E i‖ ≤ 1

/-- Finite truncations converge along the directed set of finite subsets. -/
def PowerTruncationsConverge : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ x : Space E p,
    Filter.Tendsto (fun A : Finset I => truncate E p A (fun i => x i))
      Filter.atTop (nhds x)

def DensePowerFiniteSupport : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → Dense (finiteSupport E p)

/-- Uniform finite truncation approximation in c₀. -/
def C0TruncationApproximation : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
    {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)]
    (x : C0Space (𝕜 := 𝕜) E) (ε : ℝ), 0 < ε →
    ∃ A : Finset I, ‖x - c0Truncate E A (fun i => x.val i)‖ < ε

def DenseC0FiniteSupport : Prop :=
  ∀ {I : Type u} (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
    {𝕜 : Type w} [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)],
    Dense {x : C0Space (𝕜 := 𝕜) E | Set.Finite {i | x.val i ≠ 0}}

/-- The constant scalar family is separated from every finite-support vector.
This applies over both ℝ and ℂ and every infinite index set. -/
def BoundedConstantObstruction : Prop :=
  ∀ (I : Type u) [Infinite I] (𝕜 : Type w) [RCLike 𝕜],
    ∃ c : BoundedProduct (fun _ : I => 𝕜),
      (∀ i, c i = 1) ∧ ‖c‖ = 1 ∧
      ∀ y ∈ finiteSupport (fun _ : I => 𝕜) ∞, 1 ≤ dist c y

def NotDenseBoundedFiniteSupport : Prop :=
  ∀ (I : Type u) [Infinite I] (𝕜 : Type w) [RCLike 𝕜],
    ¬ Dense (finiteSupport (fun _ : I => 𝕜) ∞)

end ExpandedFA.Supplements.BanachSums.Spec
