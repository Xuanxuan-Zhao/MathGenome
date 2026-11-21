import MathGenome.Internal.FourierSobolev.Specs.P102.U4.Rademacher
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Count

/-!
Independent statements for paper.tex:1538–1546,1578–1635.
The ambient product has its L² norm. Thus neither graph lengths nor Hausdorff
measure use the max norm on an ordinary product. `AmbientCoordinates` below
records the required isometric bridge to the shared coordinate model.
Integrals and inequalities take values in ENNReal, including infinite area.
-/
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace P102.U4.GraphPieces

abbrev Ambient (m : ℕ) := WithLp 2 (Space m × ℝ)

def graph {m : ℕ} (γ : Space m → ℝ) (x : Space m) : Ambient m :=
  WithLp.toLp 2 (x, γ x)

def affineGraph {m : ℕ} (a : Space m) : Space m →ₗ[ℝ] Ambient m :=
  (WithLp.linearEquiv 2 ℝ (Space m × ℝ)).symm.toLinearMap.comp
    (LinearMap.id.prod (innerSL ℝ a).toLinearMap)

def jacobian {m : ℕ} (a : Space m) : ℝ := Real.sqrt (1 + ‖a‖ ^ 2)

def rationalVector {m : ℕ} (q : Fin m → ℚ) : Space m :=
  WithLp.toLp 2 (fun i => (q i : ℝ))

/-- Borel a.e. representative of the classical gradient; no condition outside U. -/
def GradientRepresentative {m : ℕ} (U : Opens (Space m)) (γ : Space m → ℝ)
    (a : Space m → Space m) : Prop :=
  Measurable a ∧
    ∀ᵐ x ∂volume.restrict (U : Set (Space m)), HasFDerivAt γ (innerSL ℝ (a x)) x

/-- The purely geometric part of the countable partition. -/
def AffinePartition {m : ℕ} (U : Opens (Space m)) (γ : Space m → ℝ)
    (a : Space m → Space m) (ε : ℝ) (E : ℕ → Set (Space m))
    (q : ℕ → Fin m → ℚ) : Prop :=
  (∀ n, MeasurableSet (E n)) ∧
  (∀ n, E n ⊆ (U : Set (Space m))) ∧
  Pairwise (fun i j => Disjoint (E i) (E j)) ∧
  volume ((U : Set (Space m)) \ ⋃ n, E n) = 0 ∧
  (∀ n x, x ∈ E n → ‖a x - rationalVector (q n)‖ < ε / 2) ∧
  (∀ n x, x ∈ E n → ∀ y, y ∈ E n →
    |γ y - γ x - inner ℝ (rationalVector (q n)) (y - x)| ≤ ε * ‖y - x‖)

namespace Expected

def AmbientCoordinates : Prop :=
  ∀ m : ℕ, Nonempty (Ambient m ≃ₗᵢ[ℝ] Space (m + 1))

def Normalization : Prop :=
  (∀ (m n : ℕ) (i : Space m → Space n), Isometry i →
    ∀ S : Set (Space m), (μHE[m] : Measure (Space n)) (i '' S) = volume S) ∧
  (∀ n : ℕ, (μHE[0] : Measure (Ambient n)) = Measure.count)

def AffineJacobian : Prop :=
  ∀ (m : ℕ) (a : Space m) (S : Set (Space m)),
    (μHE[m] : Measure (Ambient m)) (affineGraph a '' S) =
      ENNReal.ofReal (jacobian a) * volume S

def ImageMeasurability : Prop :=
  ∀ (m : ℕ) (U : Opens (Space m)) (γ : Space m → ℝ),
    ContinuousOn γ U → ∀ S : Set (Space m), MeasurableSet S → S ⊆ U →
      MeasurableSet (graph γ '' S)

def GradientExistence : Prop :=
  ∀ (m : ℕ) (_hm : 0 < m) (U : Opens (Space m)) (γ : Space m → ℝ)
    (L : ℝ≥0), LipschitzOnWith L γ U →
      ∃ a : Space m → Space m, GradientRepresentative U γ a

def LipschitzDistortion : Prop :=
  ∀ (m : ℕ) (K : ℝ≥0) (f : Ambient m → Ambient m) (S : Set (Ambient m)),
    LipschitzOnWith K f S →
      (μHE[m] : Measure (Ambient m)) (f '' S) ≤
        (K : ℝ≥0∞) ^ m * (μHE[m] : Measure (Ambient m)) S

def Partition : Prop :=
  ∀ (m : ℕ) (_hm : 0 < m) (U : Opens (Space m)) (γ : Space m → ℝ)
    (L : ℝ≥0), LipschitzOnWith L γ U →
    ∀ a : Space m → Space m, GradientRepresentative U γ a →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ (E : ℕ → Set (Space m)) (q : ℕ → Fin m → ℚ), AffinePartition U γ a ε E q

/-- The quantitative estimate on any individual piece, with a real affine slope.
No differentiability assumption is needed once the two error estimates hold. -/
def PieceEstimate : Prop :=
  ∀ (m : ℕ) (γ : Space m → ℝ) (a : Space m → Space m) (b : Space m)
    (ε : ℝ), 0 < ε → ε < 1 / 2 → Measurable a →
    ∀ E : Set (Space m),
      (∀ x ∈ E, ‖a x - b‖ < ε / 2) →
      (∀ x ∈ E, ∀ y ∈ E,
        |γ y - γ x - inner ℝ b (y - x)| ≤ ε * ‖y - x‖) →
      ∀ S : Set (Space m), MeasurableSet S → S ⊆ E →
        ENNReal.ofReal ((1 - ε) ^ (m + 1)) *
            (∫⁻ x in S, ENNReal.ofReal (jacobian (a x))) ≤
          (μHE[m] : Measure (Ambient m)) (graph γ '' S) ∧
        (μHE[m] : Measure (Ambient m)) (graph γ '' S) ≤
          ENNReal.ofReal ((1 + ε) ^ (m + 1)) *
            (∫⁻ x in S, ENNReal.ofReal (jacobian (a x)))

/-- Full countable-piece conclusion, including Borel images and infinite integrals. -/
def Theorem : Prop :=
  ∀ (m : ℕ) (_hm : 0 < m) (U : Opens (Space m)) (γ : Space m → ℝ)
    (L : ℝ≥0), LipschitzOnWith L γ U →
    ∀ a : Space m → Space m, GradientRepresentative U γ a →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ (E : ℕ → Set (Space m)) (q : ℕ → Fin m → ℚ),
        AffinePartition U γ a ε E q ∧
        ∀ n (S : Set (Space m)), MeasurableSet S → S ⊆ E n →
          MeasurableSet (graph γ '' S) ∧
          ENNReal.ofReal ((1 - ε) ^ (m + 1)) *
              (∫⁻ x in S, ENNReal.ofReal (jacobian (a x))) ≤
            (μHE[m] : Measure (Ambient m)) (graph γ '' S) ∧
          (μHE[m] : Measure (Ambient m)) (graph γ '' S) ≤
            ENNReal.ofReal ((1 + ε) ^ (m + 1)) *
              (∫⁻ x in S, ENNReal.ofReal (jacobian (a x)))

end Expected
end P102.U4.GraphPieces
