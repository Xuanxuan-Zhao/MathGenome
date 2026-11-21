import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BasisNormCompleteness
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15CoordinateContinuity
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15Unconditional
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
Independent statements for all clauses of
`fa2:p1:basis-renorming`, paper.tex 4202–4212.

The norm is exactly the shared real supremum of the original partial-sum
norms. `CompleteSupremumNorm` spells out finiteness, the norm axioms,
domination of the original norm, and completeness for the original vector
operations. The positive upper comparison below gives equivalence, and the
last assertion is monotonicity (contractivity of every truncation).

Natural indices start at zero. Finite lists, including length zero, use the
shared finite partial sums, which stabilize at the identity after their last
index. No infinite sequence padded by zero vectors is used.

The multiplier norm is specified below by its exact supremum and complete
norm axioms; the real coordinate lattice and coordinate algebra use exactly
the original vector operations.
-/

open Filter Topology
noncomputable section
universe u v
namespace ExpandedFA.P1.BasisRenorming.Spec

open C15Basis.Spec BasisNormCompleteness.Spec

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The complete equivalent norm is the displayed supremum, and each of the
original truncations is contractive for that very norm. -/
def MonotoneNorm (P : ℕ → E → E) : Prop :=
  CompleteSupremumNorm (𝕜 := 𝕜) P ∧
  (∃ K : ℝ, 0 < K ∧ ∀ x, partialSumSupNorm P x ≤ K * ‖x‖) ∧
  ∀ N x, partialSumSupNorm P (P N x) ≤ partialSumSupNorm P x

def RawMonotoneRenorming : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e),
    MonotoneNorm (𝕜 := 𝕜) (rawPartialSum h)

def FiniteMonotoneRenorming : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {d : ℕ} {e : Fin d → E} (h : IsRawFiniteBasis (𝕜 := 𝕜) e),
    MonotoneNorm (𝕜 := 𝕜) (finitePartialSum h)

/-- In the zero space the displayed norm has value zero, as it must, while
the positive equivalence constant in `MonotoneNorm` remains harmless. -/
def EmptyMonotoneNorm : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (h : IsRawFiniteBasis (𝕜 := 𝕜) (emptyFamily (E := E))) (x : E),
    partialSumSupNorm (finitePartialSum h) x = 0

/-- A helper for the last clause: once a multiplication with the correct
coordinates has been constructed, a normalized infinite Schauder basis
precludes even a left identity. The final algebra theorem applies this helper
to its actual constructed multiplication. -/
def NormalizedCoordinateProductNoIdentity : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e),
    (∀ n, ‖e n‖ = 1) →
    ∀ m : E → E → E,
      (∀ x y n, rawCoordinates h (m x y) n =
        rawCoordinates h x n * rawCoordinates h y n) →
      ¬ ∃ u : E, ∀ x, m u x = x


/-- The source's multiplier is the sum with its actual original coordinates. -/
def coordinateMultiplier {ι : Type*} (e : ι → E) (a : E → ι → 𝕜)
    (c : ι → 𝕜) (x : E) : E := ∑' i, (c i * a x i) • e i

/-- Closed scalar unit ball, with arbitrary (also finite or empty) indices. -/
def UnitWeights (ι 𝕜 : Type*) [RCLike 𝕜] := {c : ι → 𝕜 // ∀ i, ‖c i‖ ≤ 1}

/-- The displayed supremum over ALL unit bounded scalar sequences. -/
def multiplierSupNorm {ι : Type*} (e : ι → E) (a : E → ι → 𝕜) (x : E) : ℝ :=
  ⨆ c : UnitWeights ι 𝕜, ‖coordinateMultiplier e a c.val x‖

/-- A complete norm on the original vector space, with explicit equivalence. -/
structure CompleteEquivalentNorm (n : E → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ n x
  eq_zero : ∀ x, n x = 0 ↔ x = 0
  add_le : ∀ x y, n (x + y) ≤ n x + n y
  smul : ∀ (c : 𝕜) x, n (c • x) = ‖c‖ * n x
  dominates : ∀ x, ‖x‖ ≤ n x
  upper : ∃ K : ℝ, 0 < K ∧ ∀ x, n x ≤ K * ‖x‖
  complete : ∀ (s : ℕ → E),
    (∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ k ≥ J, n (s j - s k) < ε) →
    ∃ x : E, ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, n (s j - x) < ε

/-- Includes existence of every bounded multiplier, its exact coordinates and
its quantitative norm bound. Taking R=1 gives the requested contractivity. -/
structure MultiplierRenorming {ι : Type*} (e : ι → E) (a : E → ι → 𝕜) : Prop where
  bounded : ∀ x, ∃ M : ℝ, ∀ c : UnitWeights ι 𝕜,
    ‖coordinateMultiplier e a c.val x‖ ≤ M
  norm : CompleteEquivalentNorm (𝕜 := 𝕜) (multiplierSupNorm e a)
  multiplier : ∀ (c : ι → 𝕜) (R : ℝ), 0 ≤ R → (∀ i, ‖c i‖ ≤ R) → ∀ x,
    HasSum (fun i => (c i * a x i) • e i) (coordinateMultiplier e a c x) ∧
    (∀ i, a (coordinateMultiplier e a c x) i = c i * a x i) ∧
    multiplierSupNorm e a (coordinateMultiplier e a c x) ≤ R * multiplierSupNorm e a x

def RawMultiplierRenorming : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e),
    C15Unconditional.Spec.IsUnconditionalSchauderBasisValue 𝕜 E e →
    MultiplierRenorming e (rawCoordinates h)

def FiniteMultiplierRenorming : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {d : ℕ} {e : Fin d → E} (h : IsRawFiniteBasis (𝕜 := 𝕜) e),
    MultiplierRenorming e (finiteCoordinates h)


/-- A genuine vector lattice on E, with exactly the coordinate order. The
last field is the lattice-norm inequality, using scalar absolute values. -/
def RealCoordinateLattice {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : ι → E) (a : E → ι → ℝ) : Prop :=
  ∃ l : Lattice E,
    (∀ x y, l.le x y ↔ ∀ i, a x i ≤ a y i) ∧
    (∀ x y z, l.le x y → l.le (x + z) (y + z)) ∧
    (∀ (t : ℝ), 0 ≤ t → ∀ x y, l.le x y → l.le (t • x) (t • y)) ∧
    (∀ x y, (∀ i, |a x i| ≤ |a y i|) →
      multiplierSupNorm e a x ≤ multiplierSupNorm e a y)

/-- All algebra laws on the original vector operations, together with the
coordinate formula and submultiplicativity for the displayed multiplier norm.
Completeness is supplied separately by `MultiplierRenorming.norm`. No unit is
included: the algebra can have no unit in infinite dimension. -/
def CoordinateAlgebra {ι : Type*} (e : ι → E) (a : E → ι → 𝕜)
    (m : E → E → E) : Prop :=
  (∀ x y i, a (m x y) i = a x i * a y i) ∧
  (∀ x y z, m (m x y) z = m x (m y z)) ∧
  (∀ x y, m x y = m y x) ∧
  (∀ x y z, m x (y + z) = m x y + m x z) ∧
  (∀ x y z, m (x + y) z = m x z + m y z) ∧
  (∀ (t : 𝕜) x y, m (t • x) y = t • m x y) ∧
  (∀ (t : 𝕜) x y, m x (t • y) = t • m x y) ∧
  (∀ x y, multiplierSupNorm e a (m x y) ≤
    multiplierSupNorm e a x * multiplierSupNorm e a y)

def RawRealCoordinateLattice : Prop :=
  ∀ {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := ℝ) e),
    C15Unconditional.Spec.IsUnconditionalSchauderBasisValue ℝ E e →
    RealCoordinateLattice e (rawCoordinates h)

def FiniteRealCoordinateLattice : Prop :=
  ∀ {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {d : ℕ} {e : Fin d → E} (h : IsRawFiniteBasis (𝕜 := ℝ) e),
    RealCoordinateLattice e (finiteCoordinates h)

def RawNormalizedCoordinateAlgebra : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e),
    C15Unconditional.Spec.IsUnconditionalSchauderBasisValue 𝕜 E e →
    (∀ i, ‖e i‖ = 1) →
    ∃ m : E → E → E, CoordinateAlgebra e (rawCoordinates h) m ∧
      ¬ ∃ u : E, ∀ x, m u x = x

def FiniteNormalizedCoordinateAlgebra : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {d : ℕ} {e : Fin d → E} (h : IsRawFiniteBasis (𝕜 := 𝕜) e),
    (∀ i, ‖e i‖ = 1) →
    ∃ m : E → E → E, CoordinateAlgebra e (finiteCoordinates h) m

end ExpandedFA.P1.BasisRenorming.Spec
