import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
Independent interface for paper.tex, fa2:p4:cz-decomposition, with the local
positive-dimension correction in notes/001/AUTHORIZED_SOURCE_ERRATA.txt.
The scalar field is either real or complex. The cubes are concrete half-open
coordinate cubes, and series convergence is in the usual a.e. quotient Lp.
There are no assumed decomposition certificates or theorem axioms here.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ExpandedFA.SingularIntegrals.CZ

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Level `k` and lattice corner `m` encode `2^k (m + [0,1)^d)`.
Using a subtype of this countable type permits empty and finite selections
without repeated or empty padding cubes. -/
abbrev DyadicCube (d : ℕ) := ℤ × (Fin d → ℤ)

def side {d : ℕ} (q : DyadicCube d) : ℝ := (2 : ℝ) ^ q.1

def cube {d : ℕ} (q : DyadicCube d) : Set (Point d) :=
  {x | ∀ i, side q * (q.2 i : ℝ) ≤ x i ∧ x i < side q * ((q.2 i : ℝ) + 1)}

def parent {d : ℕ} (q : DyadicCube d) : DyadicCube d :=
  (q.1 + 1, fun i => q.2 i / 2)

def cubeAverage {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (q : DyadicCube d) : 𝕜 :=
  ⨍ x in cube q, f x

/-- The bad piece has an actual representative vanishing outside its cube. -/
def badPiece {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (q : DyadicCube d) : Point d → 𝕜 :=
  (cube q).indicator (fun x => f x - cubeAverage f q)

def badRegion {d : ℕ} (Q : Set (DyadicCube d)) : Set (Point d) :=
  ⋃ q : Q, cube q.1

/-- Canonical pointwise good representative. On a disjoint cube family the
sum at any point has at most one nonzero term, including at cube boundaries. -/
def goodPart {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (Q : Set (DyadicCube d)) : Point d → 𝕜 :=
  fun x => f x - ∑' q : Q, badPiece f q.1 x

/-- The output of maximal-cube selection. These are properties to prove from
integrability and differentiation, not extra hypotheses on the main theorem.
Geometric facts are included so that the analytical assembly is independent
of the proof of dyadic nesting. -/
structure Selection {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (t : ℝ) (Q : Set (DyadicCube d)) : Prop where
  measurable : ∀ q ∈ Q, MeasurableSet (cube q)
  positive : ∀ q ∈ Q, 0 < volume (cube q)
  finite : ∀ q ∈ Q, volume (cube q) < ∞
  disjoint : Q.PairwiseDisjoint cube
  lower : ∀ q ∈ Q, t * volume.real (cube q) < ∫ x in cube q, ‖f x‖
  upper : ∀ q ∈ Q, (∫ x in cube q, ‖f x‖) ≤
    (2 : ℝ) ^ d * t * volume.real (cube q)
  outside : ∀ᵐ x ∂volume, x ∉ badRegion Q → ‖f x‖ ≤ t

/-- Series in the complete Lp space; its sum is the class of `f - g`.
In particular this means `f = g + ∑ b` in Lp, not just pointwise convergence. -/
def BadSeries {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f g : Point d → 𝕜) (Q : Set (DyadicCube d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : Prop :=
  ∃ _hg : MemLp g p volume,
    ∃ hb : ∀ q : Q, MemLp (badPiece f q.1) p volume,
      ∃ hsum : MemLp (f - g) p volume,
        HasSum (fun q : Q => (hb q).toLp (badPiece f q.1)) (hsum.toLp (f - g))

/-- All estimates and both convergence assertions of the source lemma.
The exact averaging formulas give useful compatibility for downstream kernels. -/
structure Decomposition {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (t : ℝ) (Q : Set (DyadicCube d))
    (g : Point d → 𝕜) : Prop where
  disjoint : Q.PairwiseDisjoint cube
  good_outside : ∀ x, x ∉ badRegion Q → g x = f x
  good_inside : ∀ q ∈ Q, ∀ x ∈ cube q, g x = cubeAverage f q
  measure_bound : (∑' q : Q, volume (cube q.1)) ≤
    eLpNorm f 1 volume / ENNReal.ofReal t
  good_integrable : Integrable g volume
  good_infinity : eLpNorm g ∞ volume ≤ ENNReal.ofReal ((2 : ℝ) ^ d * t)
  good_one : eLpNorm g 1 volume ≤ eLpNorm f 1 volume
  bad_integrable : ∀ q : Q, Integrable (badPiece f q.1) volume
  bad_mean : ∀ q : Q, (∫ x, badPiece f q.1 x) = 0
  bad_support : ∀ q : Q, Function.support (badPiece f q.1) ⊆ cube q.1
  bad_one_bound : (∑' q : Q, eLpNorm (badPiece f q.1) 1 volume) ≤
    2 * eLpNorm f 1 volume
  series_one : BadSeries f g Q 1
  series_two : MemLp f 2 volume → BadSeries f g Q 2

end ExpandedFA.SingularIntegrals.CZ

namespace ExpandedFA.SingularIntegrals.CalderonZygmundDecompositionSpec
open CZ

/-- The complete corrected source obligation, for both scalar fields. -/
def DecompositionTheorem : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ {𝕜 : Type} [RCLike 𝕜]
    (f : Point d → 𝕜), Integrable f volume → ∀ (t : ℝ), 0 < t →
      ∃ (Q : Set (DyadicCube d)) (g : Point d → 𝕜), Decomposition f t Q g

/-- Geometry needed for dyadic maximal selection. -/
def CubeGeometry : Prop :=
  ∀ (d : ℕ) (q : DyadicCube d),
    MeasurableSet (cube q) ∧ 0 < volume (cube q) ∧
      volume (cube q) = ENNReal.ofReal (side q ^ d) ∧
      cube q ⊆ cube (parent q) ∧
      volume (cube (parent q)) = 2 ^ d * volume (cube q)

/-- Selection must establish its own averages and the a.e. exterior bound. -/
def MaximalSelection : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ {𝕜 : Type} [RCLike 𝕜]
    (f : Point d → 𝕜), Integrable f volume → ∀ (t : ℝ), 0 < t →
      ∃ Q : Set (DyadicCube d), Selection f t Q

/-- Analysis on an already selected disjoint family. This is a helper target,
not a replacement of the unconditional decomposition theorem. -/
def AssembleSelection : Prop :=
  ∀ (d : ℕ) {𝕜 : Type} [RCLike 𝕜]
    (f : Point d → 𝕜), Integrable f volume → ∀ (t : ℝ), 0 < t →
      ∀ Q : Set (DyadicCube d), Selection f t Q →
        ∃ g : Point d → 𝕜, Decomposition f t Q g

/-- Cube nesting and the actual coordinate grid cover, without any dimension
restriction. These are auxiliary geometry, not an assumed differentiation law. -/
def CubeGrid : Prop :=
  (∀ (d : ℕ) (q r : DyadicCube d),
    cube q ⊆ cube r ∨ cube r ⊆ cube q ∨ Disjoint (cube q) (cube r)) ∧
  (∀ (d : ℕ) (k : ℤ) (x : Point d), ∃ q : DyadicCube d, q.1 = k ∧ x ∈ cube q)

/-- The two summation bounds after selection. -/
def SelectionBounds : Prop :=
  ∀ (d : ℕ) {𝕜 : Type} [RCLike 𝕜]
    (f : Point d → 𝕜), Integrable f volume → ∀ (t : ℝ), 0 < t →
      ∀ Q : Set (DyadicCube d), Selection f t Q →
        ((∑' q : Q, volume (cube q.1)) ≤ eLpNorm f 1 volume / ENNReal.ofReal t) ∧
        ((∑' q : Q, eLpNorm (badPiece f q.1) 1 volume) ≤ 2 * eLpNorm f 1 volume)

/-- The canonical good representative has the correct values and a.e. bound.
Its integrability and convergence remain separate analytical obligations. -/
def PointwiseGood : Prop :=
  ∀ (d : ℕ) {𝕜 : Type} [RCLike 𝕜] (f : Point d → 𝕜)
    (t : ℝ), 0 < t → ∀ Q : Set (DyadicCube d), Selection f t Q →
      (∀ x, x ∉ badRegion Q → goodPart f Q x = f x) ∧
      (∀ q ∈ Q, ∀ x ∈ cube q, goodPart f Q x = cubeAverage f q) ∧
      (∀ᵐ x ∂volume, ‖goodPart f Q x‖ ≤ 2 ^ d * t)

/-- A logical assembly lemma records the proof architecture, while the full
unconditional theorem remains the separate required target above. -/
def AssemblyReduction : Prop := MaximalSelection → AssembleSelection → DecompositionTheorem

/-- A useful independently checkable part of the eventual analytical assembly. -/
def SingleBadPiece : Prop :=
  ∀ (d : ℕ) {𝕜 : Type} [RCLike 𝕜] (f : Point d → 𝕜),
    Integrable f volume → ∀ q : DyadicCube d,
      Integrable (badPiece f q) volume ∧
      (∫ x, badPiece f q x) = 0 ∧
      Function.support (badPiece f q) ⊆ cube q ∧
      ((∫ x, ‖badPiece f q x‖) ≤ 2 * ∫ x in cube q, ‖f x‖) ∧
      (MemLp f 2 volume → MemLp (badPiece f q) 2 volume)

end ExpandedFA.SingularIntegrals.CalderonZygmundDecompositionSpec
