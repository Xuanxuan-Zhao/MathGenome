import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyMaximalInterfaces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyWhitney
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecificLimits.Basic

/-! Independent level-set interfaces for the localization stage in
`fa2:p4:hardy-grand-atomic`, paper.tex:20281--20376. This chapter has d ≥ 1.
The grand maximal function is the accepted Euclidean one. Cubes use the
accepted supremum-norm coordinates; `coordinates` is the actual coordinate
identification, not a new maximal function. -/
noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal Topology

namespace ExpandedFA.PartIV.HardyLevel
open ExpandedFA.Fourier ExpandedFA.Distributions
open HardyMaximalSpec HardyWhitney

/-- The level threshold, for every integer k. -/
def threshold (k : ℤ) : ℝ := (2 : ℝ) ^ k

def level {X : Type*} (G : X → ℝ≥0∞) (k : ℤ) : Set X :=
  {x | ENNReal.ofReal (threshold k) < G x}

def coordinates {d : ℕ} (x : Euclidean d) : Domain d := WithLp.ofLp x

def cubeRegion {d : ℕ} (Q : DyadicCube d) (C : ℝ) : Set (Euclidean d) :=
  coordinates ⁻¹' Q.dilate C

/-- The actual level set, viewed in the coordinates used by Whitney. -/
def coordinateLevel {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (N : ℕ)
    (f : Euclidean d → 𝕜) (k : ℤ) : Set (Domain d) :=
  WithLp.toLp 2 ⁻¹' level (grand N f) k

/-- Real partition weights transported to Euclidean coordinates. -/
def weight {d : ℕ} {Ω : Opens (Domain d)} (W : Partition Ω)
    (Q : W.cubes) (x : Euclidean d) : ℝ := W.weight Q (coordinates x)

/-- The actual Whitney averages; the later existence statement proves the
nonzero-denominator and integrability facts, rather than assuming them. -/
def average {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    (f : Euclidean d → 𝕜) (W : Partition Ω) (Q : W.cubes) : 𝕜 :=
  (∫ x, weight W Q x)⁻¹ • ∫ x, weight W Q x • f x

def bad {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    (f : Euclidean d → 𝕜) (W : Partition Ω) (Q : W.cubes)
    (x : Euclidean d) : 𝕜 := weight W Q x • (f x - average f W Q)

/-- `f` minus the L¹-summable bad functions is the eventual good function.
This pointwise expression is required to agree a.e. with that L¹ sum. -/
def good {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    (f : Euclidean d → 𝕜) (W : Partition Ω) (x : Euclidean d) : 𝕜 :=
  f x - ∑' Q : W.cubes, bad f W Q x

/-- Cancellation correction between consecutive (fine and coarse) levels. -/
def correction {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω Ω' : Opens (Domain d)} (f : Euclidean d → 𝕜)
    (W : Partition Ω) (W' : Partition Ω') (Q : W.cubes) (R : W'.cubes) : 𝕜 :=
  (∫ x, weight W' R x)⁻¹ • ∫ x, weight W Q x • bad f W' R x

def piece {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω Ω' : Opens (Domain d)} (f : Euclidean d → 𝕜)
    (W : Partition Ω) (W' : Partition Ω') (Q : W.cubes)
    (x : Euclidean d) : 𝕜 :=
  bad f W Q x - ∑' R : W'.cubes,
    (weight W Q x • bad f W' R x - weight W' R x • correction f W W' Q R)

end ExpandedFA.PartIV.HardyLevel

namespace Specs.ExpandedFA.PartIV.HardyLevelDecomposition
open _root_.ExpandedFA.PartIV.HardyLevel
open _root_.ExpandedFA.Fourier _root_.ExpandedFA.Distributions
open _root_.ExpandedFA.PartIV.HardyMaximalSpec
open _root_.ExpandedFA.PartIV.HardyWhitney

def thresholdType := ℤ → ℝ
def thresholdValue : thresholdType := threshold

def dyadicLayerBoundType : Prop := ∀ {X : Type*} [MeasurableSpace X]
  (μ : Measure X) (G : X → ℝ≥0∞), Measurable G →
  (∑' k : ℤ, ENNReal.ofReal (threshold k) * μ (level G k)) ≤ 2 * ∫⁻ x, G x ∂μ

def levelMeasureFiniteType : Prop := ∀ {X : Type*} [MeasurableSpace X]
  (μ : Measure X) (G : X → ℝ≥0∞), Measurable G →
  (∫⁻ x, G x ∂μ) < ⊤ → ∀ k : ℤ, μ (level G k) < ⊤

def grandLevelOpenType : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
  (N : ℕ) (f : Euclidean d → 𝕜), Integrable f → ∀ k : ℤ,
  IsOpen (level (grand N f) k)

def coordinateLevelsType : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
  (N : ℕ) (f : Euclidean d → 𝕜), Integrable f →
  (∫⁻ x, grand N f x) < ⊤ → ∀ k : ℤ,
  IsOpen (coordinateLevel N f k) ∧ volume (coordinateLevel N f k) < ⊤ ∧
  coordinateLevel N f (k + 1) ⊆ coordinateLevel N f k

def cubeVolumeType : Prop := ∀ {d : ℕ} (Q : DyadicCube d),
  volume (cubeRegion Q 1) = volume Q.carrier

def emptyGoodType : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
  {Ω : Opens (Domain d)} (f : Euclidean d → 𝕜) (W : Partition Ω),
  W.cubes = ∅ → good f W = f

/-- The geometric and coefficient part of the parent conclusion, with
simultaneous constants and the actual grand-maximal levels. -/
def levelPartitionsType : Prop := ∀ d : ℕ, 0 < d →
  ∃ (c C : ℝ) (A : ℕ → ℝ) (M : ℕ),
    0 < c ∧ 1 ≤ C ∧ (∀ j, 0 < A j) ∧ 0 < M ∧
    ∀ {𝕜 : Type} [RCLike 𝕜] (N : ℕ) (f : Euclidean d → 𝕜),
      Integrable f → (∫⁻ x, grand N f x) < ⊤ →
      ∃ (Ω : ℤ → Opens (Domain d)) (W : ∀ k, Partition (Ω k)),
        (∀ k, (Ω k : Set (Domain d)) = coordinateLevel N f k) ∧
        (∀ k, PartitionEstimates c C A M (W k)) ∧
        (∀ k, NestedEstimates C M (W k) (W (k + 1))) ∧
        (∀ k, (Ω k : Set (Domain d)) = ∅ → (W k).cubes = ∅) ∧
        (∑' k : ℤ, ∑' Q : (W k).cubes,
          ENNReal.ofReal (C * threshold k) * volume (cubeRegion Q.val 1)) ≤
            2 * ENNReal.ofReal C * ∫⁻ x, grand N f x

/-- Full parent obligation. Opens may be empty, in which case their cube
families must be empty and `good = f`. Constants are independent of f,k,Q.
The L¹ identities refer to genuine integrable functions, not formal sums. -/
def levelDecompositionType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d N : ℕ),
  0 < d → AdmissibleOrder d N →
  ∃ (c C : ℝ) (A : ℕ → ℝ) (M : ℕ),
    0 < c ∧ 1 ≤ C ∧ (∀ j, 0 < A j) ∧ 0 < M ∧
    ∀ f : Euclidean d → 𝕜, Integrable f →
    (∫⁻ x, grand N f x) < ⊤ →
    ∃ (Ω : ℤ → Opens (Domain d)) (W : ∀ k, Partition (Ω k)),
      (∀ k, (Ω k : Set (Domain d)) = coordinateLevel N f k) ∧
      (∀ k, PartitionEstimates c C A M (W k)) ∧
      (∀ k, NestedEstimates C M (W k) (W (k + 1))) ∧
      (∀ k, (Ω k : Set (Domain d)) = ∅ → (W k).cubes = ∅) ∧
      (∀ k, Integrable (good f (W k))) ∧
      (∀ k, ∀ᵐ x, ‖good f (W k) x‖ ≤ C * threshold k) ∧
      Tendsto (fun k : ℤ => ∫ x, ‖good f (W k) x - f x‖) atTop (𝓝 0) ∧
      (∀ φ : Schwartz 𝕜 d,
        Tendsto (fun k : ℤ => ∫ x, φ x * good f (W k) x) atBot (𝓝 0)) ∧
      (∀ (k : ℤ) (Q : (W k).cubes),
        Integrable (piece f (W k) (W (k + 1)) Q) ∧
        (∫ x, piece f (W k) (W (k + 1)) Q x) = 0 ∧
        (∀ᵐ x, x ∉ cubeRegion Q.val C → piece f (W k) (W (k + 1)) Q x = 0) ∧
        (∀ᵐ x, ‖piece f (W k) (W (k + 1)) Q x‖ ≤ C * threshold k)) ∧
      (∀ k,
        (∑' Q : (W k).cubes, ∫⁻ x,
          ENNReal.ofReal ‖piece f (W k) (W (k + 1)) Q x‖) < ⊤ ∧
        (∀ᵐ x, (∑' Q : (W k).cubes, piece f (W k) (W (k + 1)) Q x) =
          good f (W (k + 1)) x - good f (W k) x)) ∧
      (∑' k : ℤ, ∑' Q : (W k).cubes,
        ENNReal.ofReal (C * threshold k) * volume (cubeRegion Q.val 1)) ≤
          2 * ENNReal.ofReal C * ∫⁻ x, grand N f x

end Specs.ExpandedFA.PartIV.HardyLevelDecomposition
