import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.AveragesMaximalDefinition
import Mathlib.Topology.MetricSpace.Isometry

/-! Independent statements of paper.tex:4437–4453. The function and its
Lebesgue point use the upstream completed-measure interfaces. Families are
indexed by an arbitrary filter, including sequences. Cubes are arbitrary
Euclidean isometric images, with `s` their full side length. -/
set_option maxHeartbeats 2000000
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
universe u

namespace D11.Ch13.RegularShrinking
open D11.Ch03
local instance (n : ℕ) [NeZero n] : MeasurableSpace (Point n) :=
  Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value n

/-- The normalized scalar integral on a measurable finite positive-volume set.
The theorems below establish integrability and the denominator conditions. -/
def setMean {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
    (f : Point n → 𝕜) (E : Set (Point n)) : 𝕜 :=
  ((Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n) E).toReal⁻¹ •
    ∫ y in E, f y ∂(Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n)

/-- A closed Euclidean cube of full side length `s`. The isometry includes
both its position and its orientation. -/
def closedCube {n : ℕ} (e : Point n ≃ᵢ Point n) (s : ℝ) : Set (Point n) :=
  e '' {y | ∀ j, |y j| ≤ s / 2}
/-- The corresponding open cube. Sets between this and the closed cube
include all choices of faces and endpoints. -/
def openCube {n : ℕ} (e : Point n ≃ᵢ Point n) (s : ℝ) : Set (Point n) :=
  e '' {y | ∀ j, |y j| < s / 2}
end D11.Ch13.RegularShrinking

namespace Specs.D11.Ch13.RegularShrinking
open _root_.D11.Ch03 _root_.D11.Ch13.RegularShrinking
open Specs.D11.Ch13.AveragesMaximalDefinition
local instance (n : ℕ) [NeZero n] : MeasurableSpace (Point n) :=
  Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value n

/-- All hypotheses are those of the source, including a uniform positive
volume fraction and balls containing the chosen point. -/
def regular_shrinking : Prop :=
  ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Point n → 𝕜) (hf : locallyIntegrable_value f) (x : Point n),
    lebesguePoint_value f hf x →
    ∀ {ι : Type u} (l : Filter ι) (E : ι → Set (Point n))
      (z : ι → Point n) (r : ι → ℝ) (c : ℝ),
    0 < c → (∀ i, MeasurableSet (E i)) →
    (∀ i, E i ⊆ Metric.ball (z i) (r i)) →
    (∀ i, x ∈ Metric.ball (z i) (r i)) →
    Tendsto r l (𝓝 0) →
    (∀ i, ENNReal.ofReal c *
      (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n) (Metric.ball (z i) (r i)) ≤
      (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n) (E i)) →
    (∀ i, 0 < (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n) (E i) ∧
      (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n) (E i) < ∞ ∧
      IntegrableOn f (E i) (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n)) ∧
    Tendsto (fun i => setMean (fun y => ‖f y - f x‖) (E i)) l (𝓝 0) ∧
    Tendsto (fun i => setMean f (E i)) l (𝓝 (f x))

/-- Cubes containing x may vary in orientation and position at every index. -/
def cubes_shrinking : Prop :=
  ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Point n → 𝕜) (hf : locallyIntegrable_value f) (x : Point n),
    lebesguePoint_value f hf x →
    ∀ {ι : Type u} (l : Filter ι) (e : ι → Point n ≃ᵢ Point n) (s : ι → ℝ),
    (∀ i, 0 < s i) → (∀ i, x ∈ closedCube (e i) (s i)) →
    Tendsto s l (𝓝 0) →
    (∀ i, MeasurableSet (closedCube (e i) (s i)) ∧
      0 < (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n) (closedCube (e i) (s i)) ∧
      (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n) (closedCube (e i) (s i)) < ∞ ∧
      IntegrableOn f (closedCube (e i) (s i))
        (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n)) ∧
    Tendsto (fun i => setMean (fun y => ‖f y - f x‖) (closedCube (e i) (s i))) l (𝓝 0) ∧
    Tendsto (fun i => setMean f (closedCube (e i) (s i))) l (𝓝 (f x))
/-- The same conclusion for every measurable choice of the cube's boundary,
including open, closed and half-open cubes. -/
def cube_families_shrinking : Prop :=
  ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Point n → 𝕜) (hf : locallyIntegrable_value f) (x : Point n),
    lebesguePoint_value f hf x →
    ∀ {ι : Type u} (l : Filter ι) (Q : ι → Set (Point n))
      (e : ι → Point n ≃ᵢ Point n) (s : ι → ℝ),
    (∀ i, 0 < s i) → (∀ i, MeasurableSet (Q i)) →
    (∀ i, openCube (e i) (s i) ⊆ Q i) →
    (∀ i, Q i ⊆ closedCube (e i) (s i)) →
    (∀ i, x ∈ Q i) → Tendsto s l (𝓝 0) →
    (∀ i, 0 < (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n) (Q i) ∧
      (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n) (Q i) < ∞ ∧
      IntegrableOn f (Q i) (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n)) ∧
    Tendsto (fun i => setMean (fun y => ‖f y - f x‖) (Q i)) l (𝓝 0) ∧
    Tendsto (fun i => setMean f (Q i)) l (𝓝 (f x))
end Specs.D11.Ch13.RegularShrinking
