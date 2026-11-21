import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.Stationarity

open MeasureTheory
open scoped ENNReal MeasureTheory
universe u v
namespace P207.Markov
noncomputable section

/-- The states charged by the stationary probability. -/
abbrev StationarySupport {S : Type u} (π : ProbabilityLaw S) := {i : S // 0 < π i}

private theorem support_tsum {S : Type u} (π : ProbabilityLaw S) :
    ∑' i : StationarySupport π, π i.val = 1 := by
  calc
    ∑' i : StationarySupport π, π i.val = ∑' i, π i :=
      tsum_subtype_eq_of_support_subset (s := {i | 0 < π i}) (fun _ hi =>
        pos_iff_ne_zero.mpr hi)
    _ = 1 := π.tsum_coe

/-- Restriction to the positive support loses no probability mass. -/
def supportLaw {S : Type u} (π : ProbabilityLaw S) : ProbabilityLaw (StationarySupport π) :=
  ⟨fun i => π i.val, ENNReal.summable.hasSum_iff.mpr (support_tsum π)⟩

private theorem incoming_support_tsum {S : Type u} (P : StochasticMatrix S)
    (π : ProbabilityLaw S) (hπ : IsStationary P π) (i : S) :
    ∑' j : StationarySupport π, π j.val * P j.val i = π i := by
  calc
    ∑' j : StationarySupport π, π j.val * P j.val i = ∑' j, π j * P j i :=
      tsum_subtype_eq_of_support_subset (s := {j | 0 < π j}) (f := fun j => π j * P j i) (fun j hj =>
        show 0 < π j from pos_iff_ne_zero.mpr (fun hz : π j = 0 => hj (by simp [hz])))
    _ = π i := (PMF.bind_apply π P i).symm.trans
      (congrArg (fun ν : PMF S => ν i) hπ)

/-- The reversed transition is defined only on the positive support. -/
def reverseKernel {S : Type u} (P : StochasticMatrix S) (π : ProbabilityLaw S)
    (hπ : IsStationary P π) : StochasticMatrix (StationarySupport π) := fun i =>
  ⟨fun j => π j.val * P j.val i.val / π i.val, ENNReal.summable.hasSum_iff.mpr (by
    simp only [div_eq_mul_inv, ENNReal.tsum_mul_right,
      incoming_support_tsum P π hπ i.val]
    exact ENNReal.div_self (ne_of_gt i.property) (π.apply_ne_top i.val))⟩

namespace TimeReversalSpec

def supportLawType := {S : Type u} → (π : ProbabilityLaw S) →
  ProbabilityLaw (StationarySupport π)
def supportLawValue : supportLawType.{u} := @supportLaw

def reverseKernelType := {S : Type u} → (P : StochasticMatrix S) →
  (π : ProbabilityLaw S) → IsStationary P π → StochasticMatrix (StationarySupport π)
def reverseKernelValue : reverseKernelType.{u} := @reverseKernel

def support_closed : Prop := ∀ {S : Type u} (P : StochasticMatrix S)
  (π : ProbabilityLaw S), IsStationary P π →
  ∀ i j, 0 < π i → π j = 0 → P i j = 0

def stationarySupport_isClosed : Prop := ∀ {S : Type u} (P : StochasticMatrix S)
  (π : ProbabilityLaw S), IsStationary P π → IsClosed P {i | 0 < π i}

def supportLaw_apply : Prop := ∀ {S : Type u} (π : ProbabilityLaw S)
  (i : StationarySupport π), supportLaw π i = π i.val

def supportLaw_map : Prop := ∀ {S : Type u} (π : ProbabilityLaw S),
  (supportLaw π).map Subtype.val = π

def reverseKernel_apply : Prop := ∀ {S : Type u} (P : StochasticMatrix S)
  (π : ProbabilityLaw S) (hπ : IsStationary P π) (i j : StationarySupport π),
  reverseKernel P π hπ i j = π j.val * P j.val i.val / π i.val

def reverseKernel_row_sum : Prop := ∀ {S : Type u} (P : StochasticMatrix S)
  (π : ProbabilityLaw S) (hπ : IsStationary P π) (i : StationarySupport π),
  ∑' j, reverseKernel P π hπ i j = 1

def reverseKernel_stationary : Prop := ∀ {S : Type u} (P : StochasticMatrix S)
  (π : ProbabilityLaw S) (hπ : IsStationary P π),
  IsStationary (reverseKernel P π hπ) (supportLaw π)

/-- Equality as measures on words in the original state space. This includes
words containing zero-mass states and blocks starting at every time `r`. -/
def reversed_segment_law : Prop := ∀ {S : Type u} [Countable S] [MeasurableSpace S]
  [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (π : ProbabilityLaw S)
  (hπ : IsStationary P π) (n r : ℕ),
  (pathLaw P π).map (fun ω (a : Fin (n + 1)) => ω (r + (n - a.val))) =
  (pathLaw (reverseKernel P π hπ) (supportLaw π)).map
    (fun ω (a : Fin (n + 1)) => (ω a.val).val)

/-- The same conclusion for any chain with the given transition and initial law. -/
def chain_reversed_segment_law : Prop := ∀ {S : Type u} [Countable S] [Nonempty S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω]
  (P : StochasticMatrix S) (π : ProbabilityLaw S) (X : ℕ → Ω → S)
  (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ],
  IsMarkovChain P π X ℱ μ → ∀ (hπ : IsStationary P π) (n r : ℕ),
  μ.map (fun ω (a : Fin (n + 1)) => X (r + (n - a.val)) ω) =
  (pathLaw (reverseKernel P π hπ) (supportLaw π)).map
    (fun ω (a : Fin (n + 1)) => (ω a.val).val)

def reversible_iff_detailedBalance : Prop := ∀ {S : Type u} [Countable S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  (P : StochasticMatrix S) (π : ProbabilityLaw S),
  IsReversible P π ↔ DetailedBalance P π

end TimeReversalSpec
end
end P207.Markov
