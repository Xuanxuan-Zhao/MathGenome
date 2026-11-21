import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.ENat.Lattice
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Monotone

/-!
Independent specification of paper.tex, Definition d13:18:hausdorff-definition.
The Hausdorff quantities use diameter powers with coefficient exactly one.
They are defined directly, without substituting a normalized library measure.
The exponent in the source is positive. Values at other real exponents are
only a total extension and are not used to specify the source definition.
Empty countable covers are represented by a sequence of empty sets; for
positive exponents each such term is zero. The infimum of no admissible
cover is infinity, and divergent sums and unbounded suprema are infinity.
-/

open Set Filter Metric
open scoped ENNReal Topology

noncomputable section
universe u
namespace Specs.D13Unified.Ch18.HausdorffDefinitions

/-- Type of the unnormalized content, with real exponent and real mesh. -/
def hausdorffContent_type :=
  ∀ {X : Type u}, [MetricSpace X] → ℝ → ℝ → Set X → ℝ≥0∞

/-- All countable covers are permitted; their members need not be measurable. -/
def hausdorffContent_value : hausdorffContent_type :=
  fun {X} _ s δ E =>
    ⨅ (U : ℕ → Set X) (_ : E ⊆ ⋃ i, U i)
      (_ : ∀ i, ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, (ediam (U i)) ^ s

def hausdorffMeasure_type :=
  ∀ {X : Type u}, [MetricSpace X] → ℝ → Set X → ℝ≥0∞

/-- The increasing limit as the positive real mesh decreases to zero.
Its equality with that limit is an implementation obligation below. -/
def hausdorffMeasure_value : hausdorffMeasure_type :=
  fun {_} _ s E => ⨆ (δ : ℝ) (_ : 0 < δ), hausdorffContent_value s δ E

def hausdorffDimension_type :=
  ∀ {X : Type u}, [MetricSpace X] → Set X → ℝ≥0∞

/-- Infimum over positive real exponents, taken in `[0,∞]`.
In particular an empty exponent set has infimum infinity. -/
def hausdorffDimension_value : hausdorffDimension_type :=
  fun {_} _ E => ⨅ (s : ℝ) (_ : 0 < s) (_ : hausdorffMeasure_value s E = 0),
    ENNReal.ofReal s

def intervalCover_type := Set ℝ → ℝ → ℕ → Prop

/-- A finite cover by closed intervals of length at most `ε`.
For positive `ε`, closing arbitrary bounded intervals preserves their lengths
and the covering property, so closed intervals give the same least count.
Zero intervals are allowed: `n = 0` covers exactly the empty set. -/
def intervalCover_value : intervalCover_type := fun E ε n =>
  ∃ a b : Fin n → ℝ,
    (∀ i, a i ≤ b i ∧ b i - a i ≤ ε) ∧ E ⊆ ⋃ i, Icc (a i) (b i)

def intervalCoveringNumber_type := Set ℝ → ℝ → ℕ∞

/-- Infimum of the natural numbers of intervals in a cover; infinity if no
finite cover exists. Compactness and positive mesh ensure a finite minimum. -/
def intervalCoveringNumber_value : intervalCoveringNumber_type := fun E ε =>
  ⨅ (n : ℕ) (_ : intervalCover_value E ε n), (n : ℕ∞)

def boxCountingRatio_type := Set ℝ → ℝ → ℝ

/-- For nonempty compact sets and positive mesh the covering number is a
positive finite natural number, so `toNat` is exact. The empty set has ratio
zero by explicit convention (avoiding an interpretation of `log 0`). -/
def boxCountingRatio_value : boxCountingRatio_type := fun E ε =>
  if E = ∅ then 0 else
    Real.log ((intervalCoveringNumber_value E ε).toNat : ℝ) / Real.log (1 / ε)

def hasBoxDimension_type := Set ℝ → ℝ → Prop

/-- The right-hand limit through all positive real meshes, when it exists.
The empty-set convention is dimension zero. -/
def hasBoxDimension_value : hasBoxDimension_type := fun E d =>
  IsCompact E ∧ Tendsto (boxCountingRatio_value E) (𝓝[>] (0 : ℝ)) (𝓝 d)

def boxDimension_type := Set ℝ → Option ℝ

/-- `none` when a compact-set box dimension is not defined, `some d` when it
is. Uniqueness and the precise characterization are obligations below. -/
def boxDimension_value : boxDimension_type := by
  classical
  exact fun E => if h : ∃ d, hasBoxDimension_value E d then some (Classical.choose h) else none

/-- Full type of the mesh-limit bridge, with the source's positive exponent. -/
def hausdorffMeasure_limit_type : Prop :=
  ∀ {X : Type u} [MetricSpace X] (s : ℝ), 0 < s → ∀ E : Set X,
    Tendsto (fun δ => hausdorffContent_value s δ E)
      (𝓝[>] (0 : ℝ)) (𝓝 (hausdorffMeasure_value s E))

/-- The covering infimum is attained and is the least possible count. -/
def intervalCoveringNumber_minimum_type : Prop :=
  ∀ (E : Set ℝ), IsCompact E → ∀ ε : ℝ, 0 < ε →
    ∃ n : ℕ, intervalCoveringNumber_value E ε = (n : ℕ∞) ∧
      intervalCover_value E ε n ∧
      ∀ m : ℕ, intervalCover_value E ε m → n ≤ m

/-- On the domain where logarithms are used, the count is positive and finite. -/
def intervalCoveringNumber_positive_type : Prop :=
  ∀ (E : Set ℝ), IsCompact E → E.Nonempty → ∀ ε : ℝ, 0 < ε →
    0 < intervalCoveringNumber_value E ε ∧ intervalCoveringNumber_value E ε < ⊤

/-- Closing intervals does not change the least count: on the real line even
arbitrary sets of the allowed diameter can be replaced by closed intervals. -/
def intervalCover_iff_diameterCover_type : Prop :=
  ∀ (E : Set ℝ) (ε : ℝ), 0 ≤ ε → ∀ n : ℕ,
    intervalCover_value E ε n ↔
      ∃ U : Fin n → Set ℝ, (∀ i, ediam (U i) ≤ ENNReal.ofReal ε) ∧
        E ⊆ ⋃ i, U i

/-- Exact partial-value semantics, rather than an arbitrarily chosen limit. -/
def boxDimension_some_iff_type : Prop :=
  ∀ (E : Set ℝ) (d : ℝ), boxDimension_value E = some d ↔ hasBoxDimension_value E d

end Specs.D13Unified.Ch18.HausdorffDefinitions
