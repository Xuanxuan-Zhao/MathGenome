import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.FirstBorelCantelli
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! First Borel–Cantelli, with the source's explicit positive-index tail event.
The underlying sigma algebra need not be complete. -/

open MeasureTheory Filter
open scoped ENNReal

namespace ProbabilityFoundations.Ch02

universe u

/-- The event that infinitely many of the events `A n` occur. -/
def infinitelyOftenEvent {Ω : Type u} (A : ℕ → Set Ω) : Set Ω :=
  ⋂ m : ℕ, ⋂ (_ : 1 ≤ m), ⋃ n ≥ m, A n

theorem measurable_infinitelyOftenEvent {Ω : Type u} [MeasurableSpace Ω]
    (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n)) :
    MeasurableSet (infinitelyOftenEvent A) :=
  MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
    MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => hA n

/-- Restricting the tail starting indices to positive naturals leaves the limsup
unchanged, including for a sequence indexed by all of `ℕ`. -/
theorem infinitelyOftenEvent_eq_limsup {Ω : Type u} (A : ℕ → Set Ω) :
    infinitelyOftenEvent A = limsup A atTop := by
  ext ω
  simp only [infinitelyOftenEvent, limsup_eq_iInf_iSup_of_nat,
    Set.iInf_eq_iInter, Set.iSup_eq_iUnion, Set.mem_iInter, Set.mem_iUnion]
  constructor
  · intro h m
    obtain ⟨n, hn, hω⟩ := h (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
    exact ⟨n, (Nat.le_succ m).trans hn, hω⟩
  · intro h m _
    exact h m

theorem not_mem_infinitelyOftenEvent_iff {Ω : Type u} (A : ℕ → Set Ω) (ω : Ω) :
    ω ∉ infinitelyOftenEvent A ↔ {n : ℕ | ω ∈ A n}.Finite := by
  rw [infinitelyOftenEvent_eq_limsup, ← Nat.cofinite_eq_atTop]
  simp [mem_limsup_iff_frequently_mem, Filter.Frequently]

/-- The equivalence does not itself need measurability or a probability measure. -/
theorem infinitelyOften_null_iff_ae_finite {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (A : ℕ → Set Ω) :
    P (infinitelyOftenEvent A) = 0 ↔ ∀ᵐ ω ∂P, {n : ℕ | ω ∈ A n}.Finite := by
  rw [measure_eq_zero_iff_ae_notMem]
  simp only [not_mem_infinitelyOftenEvent_iff]

/-- First Borel–Cantelli: summable event probabilities give a null limsup event.
There is no independence hypothesis. -/
theorem first_borel_cantelli {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (_hA : ∀ n, MeasurableSet (A n)) (hsum : (∑' n, P (A n)) < ∞) :
    P (infinitelyOftenEvent A) = 0 := by
  rw [infinitelyOftenEvent_eq_limsup]
  exact measure_limsup_atTop_eq_zero hsum.ne

/-- Almost surely only finitely many events in a summable sequence occur. -/
theorem ae_finite_occurrences {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (hA : ∀ n, MeasurableSet (A n)) (hsum : (∑' n, P (A n)) < ∞) :
    ∀ᵐ ω ∂P, {n : ℕ | ω ∈ A n}.Finite :=
  (infinitelyOften_null_iff_ae_finite P A).mp (first_borel_cantelli P A hA hsum)

end ProbabilityFoundations.Ch02
