import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15Basis
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Nat.Log
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
Independent interface for the Haar clauses of `fa2:p1:schauder-haar`,
paper.tex:4380–4420. The domain is the actual closed unit interval with its
Lebesgue probability measure. Half-open dyadic cells omit only its null right
endpoint. We use unnormalised Haar functions (values +1 and -1), with the
constant function at index 0. Index 2^l+k is the kth subdivision at level l.
All exponent quantifiers include p = 1 and exclude only p = infinity.
-/
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators unitInterval
universe u
namespace ExpandedFA.P1.HaarBasis.Spec

/-- Half-open dyadic cells in the closed unit interval. -/
def dyadicCell (l k : ℕ) : Set I :=
  Subtype.val ⁻¹' Set.Ico ((k : ℝ) / 2 ^ l) (((k : ℝ) + 1) / 2 ^ l)

lemma measurableSet_dyadicCell (l k : ℕ) : MeasurableSet (dyadicCell l k) :=
  measurableSet_Ico.preimage measurable_subtype_coe

/-- Level and position of a positive index; the values at zero are unused. -/
def haarLevel (n : ℕ) : ℕ := n.log2
def haarPosition (n : ℕ) : ℕ := n - 2 ^ haarLevel n

def leftCell (n : ℕ) : Set I :=
  dyadicCell (haarLevel n + 1) (2 * haarPosition n)
def rightCell (n : ℕ) : Set I :=
  dyadicCell (haarLevel n + 1) (2 * haarPosition n + 1)

/-- Constant first, then left-to-right subdivisions at each successive level. -/
def haarFunction (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) (x : I) : 𝕜 :=
  if n = 0 then 1 else
    (leftCell n).indicator (fun _ => 1) x - (rightCell n).indicator (fun _ => 1) x

/-- These are elements of the actual a.e. quotient, not merely representatives. -/
def haarLp (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    Lp 𝕜 p (volume : Measure I) :=
  if n = 0 then Lp.const p volume 1 else
    indicatorConstLp (s := leftCell n) p (measurableSet_dyadicCell _ _) (measure_ne_top _ _) 1 -
      indicatorConstLp (s := rightCell n) p (measurableSet_dyadicCell _ _) (measure_ne_top _ _) 1

/-- The usual Fourier-Haar coefficient; Haar functions are real-valued,
so no conjugation is needed, also over the complex field. -/
def haarCoefficient {𝕜 : Type u} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp 𝕜 p (volume : Measure I)) (n : ℕ) : 𝕜 :=
  (if n = 0 then 1 else (2 : 𝕜) ^ haarLevel n) *
    ∫ x : I, f x * haarFunction 𝕜 n x

def haarPartialSum {𝕜 : Type u} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (N : ℕ) (f : Lp 𝕜 p (volume : Measure I)) : Lp 𝕜 p (volume : Measure I) :=
  C15Basis.Spec.orderedPartialSum (haarLp 𝕜 p) (haarCoefficient f) N

/-- The finite sigma algebra after the first N Haar functions. Each new
positive index splits exactly one old cell. This includes partial levels. -/
def prefixSigma (N : ℕ) : MeasurableSpace I :=
  MeasurableSpace.generateFrom {s | ∃ i, 0 < i ∧ i < N ∧
    (s = leftCell i ∨ s = rightCell i)}

/-- P₀ is zero; positive prefixes are finite-partition conditional expectations.
The equality with the explicit Haar partial sums is a separate obligation. -/
def prefixExpectation {𝕜 : Type u} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (N : ℕ) (f : Lp 𝕜 p (volume : Measure I)) : Lp 𝕜 p (volume : Measure I) :=
  if N = 0 then 0 else
    ((Lp.memLp f).condExp (m := prefixSigma N) Fact.out).toLp
      (volume[⇑f | prefixSigma N])

/-- A concrete endpoint test family of L¹ norm one. -/
def endpointSpike (𝕜 : Type u) [RCLike 𝕜] (N : ℕ) : Lp 𝕜 1 (volume : Measure I) :=
  indicatorConstLp (s := dyadicCell N 0) 1 (measurableSet_dyadicCell N 0)
    (measure_ne_top _ _) ((2 : 𝕜) ^ N)

/-- The alternating sign transform of its leftmost-branch Haar expansion. -/
def endpointTransform (𝕜 : Type u) [RCLike 𝕜] (N : ℕ) : Lp 𝕜 1 (volume : Measure I) :=
  haarLp 𝕜 1 0 + ∑ k ∈ Finset.range N,
    (((-1 : 𝕜) ^ (k + 1)) * (2 : 𝕜) ^ k) • haarLp 𝕜 1 (2 ^ k)

def HaarRepresentatives : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ),
    ⇑(haarLp 𝕜 p n) =ᵐ[volume] haarFunction 𝕜 n

def PrefixExpectationContraction : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (N : ℕ) (f : Lp 𝕜 p (volume : Measure I)), ‖prefixExpectation N f‖ ≤ ‖f‖

def HaarNonzero : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (_hp : p ≠ ∞) (n : ℕ),
    haarLp 𝕜 p n ≠ 0

def HaarPrefixExpectation : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (_hp : p ≠ ∞)
    (N : ℕ) (f : Lp 𝕜 p (volume : Measure I)),
    haarPartialSum N f = prefixExpectation N f

def HaarContractions : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (_hp : p ≠ ∞)
    (N : ℕ) (f : Lp 𝕜 p (volume : Measure I)), ‖haarPartialSum N f‖ ≤ ‖f‖

def HaarConvergence : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (_hp : p ≠ ∞)
    (f : Lp 𝕜 p (volume : Measure I)),
    Tendsto (fun N => haarPartialSum N f) atTop (𝓝 f)

def HaarBasis : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (_hp : p ≠ ∞),
    C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) (haarLp 𝕜 p)

/-- The natural-order expansion of some L¹ function fails to converge as the
net of all finite subsums. Thus conditionality has its series meaning, not just
an unboundedness assertion about some unrelated operators. -/
def HaarConditional : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ f : Lp 𝕜 1 (volume : Measure I),
      ¬ Summable (fun n => haarCoefficient f n • haarLp 𝕜 1 n)

/-- Quantitative finite witnesses from the source proof, useful for the endpoint. -/
def EndpointWitnesses : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (N : ℕ),
    ‖endpointSpike 𝕜 N‖ = 1 ∧
      ((N : ℝ) - 1) / 3 ≤ ‖endpointTransform 𝕜 N‖

end ExpandedFA.P1.HaarBasis.Spec

namespace ExpandedFA.P1.HaarBasis.Spec.Expected
open ExpandedFA.P1.HaarBasis.Spec

def haarFunctionType : Type _ := ∀ (𝕜 : Type u) [RCLike 𝕜], ℕ → I → 𝕜
def haarFunctionValue : haarFunctionType := @haarFunction

def haarLpType : Type _ := ∀ (𝕜 : Type u) [RCLike 𝕜]
  (p : ℝ≥0∞) [Fact (1 ≤ p)], ℕ → Lp 𝕜 p (volume : Measure I)
def haarLpValue : haarLpType := @haarLp

def haarCoefficientType : Type _ := ∀ {𝕜 : Type u} [RCLike 𝕜]
  {p : ℝ≥0∞} [Fact (1 ≤ p)], Lp 𝕜 p (volume : Measure I) → ℕ → 𝕜
def haarCoefficientValue : haarCoefficientType := @haarCoefficient

def haarPartialSumType : Type _ := ∀ {𝕜 : Type u} [RCLike 𝕜]
  {p : ℝ≥0∞} [Fact (1 ≤ p)], ℕ → Lp 𝕜 p (volume : Measure I) → Lp 𝕜 p (volume : Measure I)
def haarPartialSumValue : haarPartialSumType := @haarPartialSum

def prefixSigmaType : Type := ℕ → MeasurableSpace I
def prefixSigmaValue : prefixSigmaType := prefixSigma

def prefixExpectationType : Type _ := ∀ {𝕜 : Type u} [RCLike 𝕜]
  {p : ℝ≥0∞} [Fact (1 ≤ p)], ℕ → Lp 𝕜 p (volume : Measure I) → Lp 𝕜 p (volume : Measure I)
def prefixExpectationValue : prefixExpectationType := @prefixExpectation

def EndpointSpikeNorm : Prop := ∀ (𝕜 : Type u) [RCLike 𝕜] (N : ℕ), ‖endpointSpike 𝕜 N‖ = 1

def EndpointSpikeExpansion : Prop := ∀ (𝕜 : Type u) [RCLike 𝕜] (N : ℕ),
  endpointSpike 𝕜 N = haarLp 𝕜 1 0 +
    ∑ k ∈ Finset.range N, ((2 : 𝕜) ^ k) • haarLp 𝕜 1 (2 ^ k)

def HaarIntegral : Prop := ∀ (𝕜 : Type u) [RCLike 𝕜] (n : ℕ),
  (∫ x : I, haarFunction 𝕜 n x) = if n = 0 then 1 else 0

/-- Continuity is proved for the explicit integral coefficients. -/
def HaarCoefficientContinuity : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ),
    Continuous (fun f : Lp 𝕜 p (volume : Measure I) => haarCoefficient f n)

def HaarBiorthogonality : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (i j : ℕ),
    haarCoefficient (haarLp 𝕜 p j) i = if i = j then 1 else 0

def HaarExpansionUniqueness : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {f : Lp 𝕜 p (volume : Measure I)} {a : ℕ → 𝕜},
    Tendsto (C15Basis.Spec.orderedPartialSum (haarLp 𝕜 p) a) atTop (𝓝 f) →
      a = haarCoefficient f

def EndpointTransformNormLower : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (N : ℕ), (N : ℝ) / 3 ≤ ‖endpointTransform 𝕜 N‖

end ExpandedFA.P1.HaarBasis.Spec.Expected
