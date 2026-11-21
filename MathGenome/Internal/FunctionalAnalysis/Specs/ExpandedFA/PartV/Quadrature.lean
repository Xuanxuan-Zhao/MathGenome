import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Weierstrass

noncomputable section
namespace ExpandedFA.PartV.Quadrature.Spec
open Set MeasureTheory Filter
open scoped Topology ZeroAtInfty
open ExpandedFA.FunctionSpaces.ScalarRieszMarkovSpec
universe u

/-- Tests use the uniform norm and the scalar-linear (not conjugate-linear) dual. -/
def DenseTestCriterion : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (𝕜 : Type) [RCLike 𝕜]
    (μ : ℕ → VectorMeasure K 𝕜) (hμ : ∀ n, FiniteScalarRadon (μ n))
    (D : Submodule 𝕜 C(K, 𝕜)) (hD : Dense (D : Set C(K, 𝕜)))
    (L : C(K, 𝕜) →L[𝕜] 𝕜),
    (∀ f : C(K, 𝕜), Tendsto (fun n => scalarIntegral (μ n) f) atTop (𝓝 (L f))) ↔
    ((∃ M : ℝ, 0 ≤ M ∧ ∀ n, (μ n).variation.real univ ≤ M) ∧
      ∀ f ∈ D, Tendsto (fun n => scalarIntegral (μ n) f) atTop (𝓝 (L f)))

/-- The unqualified convergence assertion, including construction of its bounded limit. -/
def ConvergenceCriterion : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (𝕜 : Type) [RCLike 𝕜]
    (μ : ℕ → VectorMeasure K 𝕜), (∀ n, FiniteScalarRadon (μ n)) →
    ∀ (D : Submodule 𝕜 C(K, 𝕜)) (_hD : Dense (D : Set C(K, 𝕜))),
    (∀ f : C(K, 𝕜), ∃ a : 𝕜, Tendsto (fun n => scalarIntegral (μ n) f) atTop (𝓝 a)) ↔
    ((∃ M : ℝ, 0 ≤ M ∧ ∀ n, (μ n).variation.real univ ≤ M) ∧
      ∃ L : C(K, 𝕜) →L[𝕜] 𝕜, ∀ f ∈ D,
        Tendsto (fun n => scalarIntegral (μ n) f) atTop (𝓝 (L f)))

/-- Uniform modulus, with zero inserted so that it also covers the empty space. -/
def modulus {K 𝕜 : Type*} [MetricSpace K] [RCLike 𝕜] [CompactSpace K]
    (f : C(K, 𝕜)) (r : ℝ) : ℝ :=
  sSup (insert 0 {d : ℝ | ∃ x y : K, dist x y ≤ r ∧ d = dist (f x) (f y)})

/-- A finite measurable quantizer gives exactly the weighted atomic measure
on its fibers. A tagged partition is represented by its constant tag on each
cell; tags in their cells make the fibers precisely those cells. -/
def QuadratureWeights : Prop :=
  ∀ (K : Type u) [MetricSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (𝕜 : Type) [RCLike 𝕜]
    (μ : VectorMeasure K 𝕜) (q : SimpleFunc K K),
    μ.map q = ∑ y ∈ q.range, VectorMeasure.dirac y (μ (q ⁻¹' {y}))

def QuadratureEstimate : Prop :=
  ∀ (K : Type u) [MetricSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (𝕜 : Type) [RCLike 𝕜]
    (μ : VectorMeasure K 𝕜), FiniteScalarRadon μ →
    ∀ (q : SimpleFunc K K) (r : ℝ), (∀ x, dist (q x) x ≤ r) →
    ∀ f : C(K, 𝕜),
      ‖scalarIntegral (μ.map q) f - scalarIntegral μ f‖ ≤
        μ.variation.real univ * modulus f r

def QuadratureConvergence : Prop :=
  ∀ (K : Type u) [MetricSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (𝕜 : Type) [RCLike 𝕜]
    (μ : VectorMeasure K 𝕜), FiniteScalarRadon μ →
    ∀ (q : ℕ → SimpleFunc K K) (r : ℕ → ℝ),
      (∀ n x, dist (q n x) x ≤ r n) → Tendsto r atTop (𝓝 0) →
      (∀ n, FiniteScalarRadon (μ.map (q n))) ∧
      ∀ f : C(K, 𝕜), Tendsto (fun n => scalarIntegral (μ.map (q n)) f) atTop
        (𝓝 (scalarIntegral μ f))

/-- A finite measurable partition is encoded by its cell-index map. The
fiber at i is Aᵢ; the tag condition says that its chosen node belongs to Aᵢ.
There is no nonempty-space assumption, and the empty partition is allowed. -/
structure TaggedPartition (K : Type u) [MeasurableSpace K] where
  size : ℕ
  index : SimpleFunc K (Fin size)
  tag : Fin size → K
  tag_index : ∀ i, index (tag i) = i

def TaggedPartition.cell {K : Type u} [MeasurableSpace K]
    (p : TaggedPartition K) (i : Fin p.size) : Set K := p.index ⁻¹' {i}

def TaggedPartition.quantizer {K : Type u} [MeasurableSpace K]
    (p : TaggedPartition K) : SimpleFunc K K := p.index.map p.tag

def TaggedPartition.measure {K : Type u} [MeasurableSpace K]
    (p : TaggedPartition K) {𝕜 : Type*} [RCLike 𝕜] (μ : VectorMeasure K 𝕜) :
    VectorMeasure K 𝕜 := ∑ i, VectorMeasure.dirac (p.tag i) (μ (p.cell i))

/-- The literal partition rule, with mesh bounding each cell's diameter. -/
def TaggedQuadrature : Prop :=
  ∀ (K : Type u) [MetricSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (𝕜 : Type) [RCLike 𝕜]
    (μ : VectorMeasure K 𝕜), FiniteScalarRadon μ →
    ∀ (p : ℕ → TaggedPartition K) (r : ℕ → ℝ),
      (∀ n i, ∀ x ∈ (p n).cell i, ∀ y ∈ (p n).cell i, dist x y ≤ r n) →
      Tendsto r atTop (𝓝 0) →
      (∀ n, FiniteScalarRadon ((p n).measure μ)) ∧
      (∀ n (f : C(K, 𝕜)),
        ‖scalarIntegral ((p n).measure μ) f - scalarIntegral μ f‖ ≤
          μ.variation.real univ * modulus f (r n)) ∧
      ∀ f : C(K, 𝕜), Tendsto (fun n => scalarIntegral ((p n).measure μ) f) atTop
        (𝓝 (scalarIntegral μ f))

/-- The nodes of the explicit example. Lean's inverse is zero at zero;
all substantive counterexample identities concern n ≥ 1. -/
def inverseSquareNode (n : ℕ) : Set.Icc (0 : ℝ) 1 := by
  refine ⟨(n : ℝ)⁻¹ ^ 2, sq_nonneg _, ?_⟩
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hi : (n : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hn'
    nlinarith [inv_nonneg.mpr ((show (0 : ℝ) ≤ n from Nat.cast_nonneg n))]

def counterexampleMeasure (n : ℕ) : VectorMeasure (Set.Icc (0 : ℝ) 1) ℝ :=
  VectorMeasure.dirac (inverseSquareNode n) (n : ℝ) -
    VectorMeasure.dirac ⟨0, le_rfl, zero_le_one⟩ (n : ℝ)

def sqrtTest : C(Set.Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun x => Real.sqrt x, Real.continuous_sqrt.comp continuous_subtype_val⟩

def DenseTestsCounterexample : Prop :=
  (∀ n, FiniteScalarRadon (counterexampleMeasure n)) ∧
  Dense (polynomialFunctions (Set.Icc (0 : ℝ) 1) :
    Set C(Set.Icc (0 : ℝ) 1, ℝ)) ∧
  (∀ p : Polynomial ℝ, Tendsto
    (fun n => scalarIntegral (counterexampleMeasure n) (p.toContinuousMapOn _))
    atTop (𝓝 0)) ∧
  (∀ n, 1 ≤ n → scalarIntegral (counterexampleMeasure n) sqrtTest = 1) ∧
  (∀ n, (counterexampleMeasure n).variation.real univ = 2 * (n : ℝ)) ∧
  (¬ ∃ M : ℝ, ∀ n, (counterexampleMeasure n).variation.real univ ≤ M) ∧
  ¬ (∀ f : C(Set.Icc (0 : ℝ) 1, ℝ),
    Tendsto (fun n => scalarIntegral (counterexampleMeasure n) f) atTop (𝓝 0))

end ExpandedFA.PartV.Quadrature.Spec
