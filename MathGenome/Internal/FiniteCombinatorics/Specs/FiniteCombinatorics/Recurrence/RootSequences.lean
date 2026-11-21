import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.GeneratingSeries
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.LinearMap.End

/-! Independent contracts for the root sequences in p204:W16.
The inverse below is the formal power-series inverse; the denominator has
constant coefficient one. No restriction on the characteristic is imposed. -/
noncomputable section
universe u
namespace Specs.FiniteCombinatorics.Recurrence

def rootSequenceType : Type (u + 1) :=
  ∀ {K : Type u} [Field K], K → ℕ → (ℕ → K)

def rootSequenceValue : rootSequenceType :=
  fun {K} [_] lam j n => PowerSeries.coeff n
    ((PowerSeries.X : PowerSeries K) ^ j *
      ((1 - PowerSeries.C lam * PowerSeries.X) ^ (j + 1))⁻¹)

def leftShiftType : Type (u + 1) :=
  ∀ {K : Type u} [Field K], Module.End K (ℕ → K)

def leftShiftValue : leftShiftType :=
  fun {_} [_] => {
    toFun := fun a n => a (n + 1)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

def root_coefficients : Prop :=
  ∀ {K : Type u} [Field K] (lam : K) (j n : ℕ),
    rootSequenceValue lam j n =
      if j ≤ n then (Nat.choose n j : K) * lam ^ (n - j) else 0

def zero_root_spike : Prop :=
  ∀ {K : Type u} [Field K] (j n : ℕ),
    rootSequenceValue (0 : K) j n = if n = j then 1 else 0

def shift_root_zero : Prop :=
  ∀ {K : Type u} [Field K] (lam : K),
    (leftShiftValue (K := K) - lam • (LinearMap.id : Module.End K (ℕ → K))) (rootSequenceValue lam 0) = 0

def shift_root_succ : Prop :=
  ∀ {K : Type u} [Field K] (lam : K) (j : ℕ),
    (leftShiftValue (K := K) - lam • (LinearMap.id : Module.End K (ℕ → K))) (rootSequenceValue lam (j + 1)) =
      rootSequenceValue lam j

def root_annihilation : Prop :=
  ∀ {K : Type u} [Field K] (lam : K) (j : ℕ),
    ((leftShiftValue (K := K) - lam • (LinearMap.id : Module.End K (ℕ → K))) ^ (j + 1)) (rootSequenceValue lam j) = 0

end Specs.FiniteCombinatorics.Recurrence
