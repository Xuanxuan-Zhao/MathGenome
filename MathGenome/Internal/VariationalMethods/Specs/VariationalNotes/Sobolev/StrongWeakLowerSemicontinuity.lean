import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.CaratheodoryIntegrands
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Topology.Order.LiminfLimsup

/-! Independent statements for `paper.tex`, Theorem `thm:strong-weak-integral`
(lines 3768–3880). The measure space need not be complete or countably generated.
The norm in the growth bound is the Euclidean norm. Each independent fiber has
its own exponent; convexity is in the whole product of fibers. The extended
integral is the previously specified signed Lebesgue integral, retaining `⊤`.
No convexity in the state, upper growth, or finite-energy hypothesis is imposed.
All dimensions, including the number of fibers, may be zero. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
universe u
namespace VariationalNotes.Sobolev.StrongWeakSpecs

/-- The lower bound guarantees a finite negative part at every admissible field.
This statement needs no convexity or convergence hypothesis. -/
def mixed_energy_negativePartIntegrable : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    {m k : ℕ} {d : Fin k → ℕ} {q : ℝ≥0∞} {r : Fin k → ℝ≥0∞}
    (F : S → EuclideanSpace ℝ (Fin m) →
      (∀ i, EuclideanSpace ℝ (Fin (d i))) → ℝ),
    CaratheodorySpecs.MixedCaratheodory μ F →
    ∀ (a : S → ℝ), Integrable a μ → ∀ C : ℝ, 0 ≤ C →
    (∀ᵐ x ∂μ, ∀ s z, -a x - C * ‖s‖ ^ q.toReal ≤ F x s z) →
    ∀ (s : Lp (EuclideanSpace ℝ (Fin m)) q μ)
      (z : ∀ i, Lp (EuclideanSpace ℝ (Fin (d i))) (r i) μ),
      CaratheodorySpecs.NegativePartIntegrable μ
        (fun x => F x (s x) (fun i => z i x))

/-- Full mixed-exponent strong–weak lower semicontinuity, independently stated.
`toWeakSpace` equips each `Lp` with the topology of its entire continuous dual,
so the convergence assumption is weak convergence in the function space. -/
def strong_weak_lowerSemicontinuity : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    {m k : ℕ} {d : Fin k → ℕ}
    (q : ℝ≥0∞) (r : Fin k → ℝ≥0∞)
    (hq : 1 ≤ q) (_hq_top : q ≠ ∞)
    (hr : ∀ i, 1 < r i) (_hr_top : ∀ i, r i ≠ ∞),
    letI : Fact (1 ≤ q) := ⟨hq⟩
    letI : ∀ i, Fact (1 ≤ r i) := fun i => ⟨(hr i).le⟩
    ∀ (F : S → EuclideanSpace ℝ (Fin m) →
        (∀ i, EuclideanSpace ℝ (Fin (d i))) → ℝ),
      CaratheodorySpecs.MixedCaratheodory μ F →
      (∀ᵐ x ∂μ, ∀ s, ConvexOn ℝ univ (F x s)) →
      ∀ (a : S → ℝ), Integrable a μ → ∀ C : ℝ, 0 ≤ C →
      (∀ᵐ x ∂μ, ∀ s z, -a x - C * ‖s‖ ^ q.toReal ≤ F x s z) →
      ∀ (sₙ : ℕ → Lp (EuclideanSpace ℝ (Fin m)) q μ)
        (s : Lp (EuclideanSpace ℝ (Fin m)) q μ)
        (zₙ : ℕ → ∀ i, Lp (EuclideanSpace ℝ (Fin (d i))) (r i) μ)
        (z : ∀ i, Lp (EuclideanSpace ℝ (Fin (d i))) (r i) μ),
        Tendsto sₙ atTop (𝓝 s) →
        (∀ i, Tendsto (fun n => toWeakSpace ℝ _ (zₙ n i)) atTop
          (𝓝 (toWeakSpace ℝ _ (z i)))) →
        CaratheodorySpecs.extendedIntegral μ (fun x => F x (s x) (fun i => z i x)) ≤
          liminf (fun n => CaratheodorySpecs.extendedIntegral μ
            (fun x => F x (sₙ n x) (fun i => zₙ n i x))) atTop

end VariationalNotes.Sobolev.StrongWeakSpecs
