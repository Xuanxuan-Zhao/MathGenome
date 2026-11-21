import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.CaratheodoryIntegrands
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Topology.Instances.EReal.Lemmas

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace VariationalNotes.Sobolev.AffineEnvelopeSpecs

/-- The coefficients of an actual countable affine envelope.  The exceptional
set in the representation is common to all states, fibers, and indices.
Measurability is requested for a.e. measurable state substitutions, so this
interface does not impose completeness on the underlying measure space. -/
def CountableAffineEnvelope {S : Type*} [MeasurableSpace S] (μ : Measure S)
    {m k : ℕ} {d : Fin k → ℕ}
    (G : S → EuclideanSpace ℝ (Fin m) →
      (∀ i, EuclideanSpace ℝ (Fin (d i))) → ℝ)
    (c : ℕ → S → EuclideanSpace ℝ (Fin m) → ℝ)
    (b : ℕ → (i : Fin k) → S → EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin (d i))) : Prop :=
  (∀ j x, Continuous (c j x)) ∧
  (∀ j i x, Continuous (b j i x)) ∧
  (∀ j (s : S → EuclideanSpace ℝ (Fin m)), AEMeasurable s μ →
    AEMeasurable (fun x ↦ c j x (s x)) μ) ∧
  (∀ j i (s : S → EuclideanSpace ℝ (Fin m)), AEMeasurable s μ →
    AEMeasurable (fun x ↦ b j i x (s x)) μ) ∧
  (∀ᵐ x ∂μ, ∀ s y,
    (∀ j, c j x s + ∑ i, inner ℝ (b j i x s) (y i) ≤ G x s y) ∧
    IsLUB ({0} ∪ Set.range (fun j ↦ c j x s +
      ∑ i, inner ℝ (b j i x s) (y i))) (G x s y))

universe u

/-- Countable-affine-envelope lower semicontinuity, with a.e. state convergence
and independent weakly converging mixed-exponent fibers.  All dimensions may
vanish; energies are the canonical signed extended integrals and may be infinite. -/
def AffineEnvelopeLowerLimit : Prop :=
  ∀ (S : Type u) [MeasurableSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    (m k : ℕ) (d : Fin k → ℕ) (r : Fin k → ℝ≥0∞)
    (hr : ∀ i, 1 < r i) (_hrtop : ∀ i, r i < ∞),
    letI : ∀ i, Fact (1 ≤ r i) := fun i ↦ ⟨(hr i).le⟩
    ∀ (G : S → EuclideanSpace ℝ (Fin m) →
        (∀ i, EuclideanSpace ℝ (Fin (d i))) → ℝ)
      (c : ℕ → S → EuclideanSpace ℝ (Fin m) → ℝ)
      (b : ℕ → (i : Fin k) → S → EuclideanSpace ℝ (Fin m) →
        EuclideanSpace ℝ (Fin (d i)))
      (sₙ : ℕ → S → EuclideanSpace ℝ (Fin m))
      (s : S → EuclideanSpace ℝ (Fin m))
      (zₙ : (i : Fin k) → ℕ → Lp (EuclideanSpace ℝ (Fin (d i))) (r i) μ)
      (z : (i : Fin k) → Lp (EuclideanSpace ℝ (Fin (d i))) (r i) μ),
      CaratheodorySpecs.MixedCaratheodory μ G →
      (∀ᵐ x ∂μ, ∀ a y, 0 ≤ G x a y) →
      CountableAffineEnvelope μ G c b →
      (∀ n, AEMeasurable (sₙ n) μ) → AEMeasurable s μ →
      (∀ᵐ x ∂μ, Tendsto (fun n ↦ sₙ n x) atTop (𝓝 (s x))) →
      (∀ i, Tendsto (fun n ↦ toWeakSpace ℝ _ (zₙ i n)) atTop
        (𝓝 (toWeakSpace ℝ _ (z i)))) →
      CaratheodorySpecs.extendedIntegral μ (fun x ↦ G x (s x) (fun i ↦ z i x)) ≤
        liminf (fun n ↦ CaratheodorySpecs.extendedIntegral μ
          (fun x ↦ G x (sₙ n x) (fun i ↦ zₙ i n x))) atTop

end VariationalNotes.Sobolev.AffineEnvelopeSpecs
