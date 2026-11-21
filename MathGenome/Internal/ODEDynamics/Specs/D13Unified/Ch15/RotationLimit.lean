import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.CircleLift
import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber

/-!
Independent specification for the limit and lift-change clauses of
`paper.tex`, Theorem `d13:15:rotation-number`, including the iterate/translation
formula used there before rational periodicity is proved.
-/
namespace Specs.D13Unified.Ch15.RotationLimit

open Filter
open scoped Topology
open CircleLift

noncomputable section

/-- Forget only invertibility and strictness to use the library's degree-one maps. -/
def toDegreeOneLift (L : IncreasingLift) : CircleDeg1Lift where
  toFun := L
  monotone' := L.strictMono'.monotone
  map_add_one' := L.map_add_one'

def toDegreeOneLiftType := IncreasingLift → CircleDeg1Lift

/-- The real rotation number of a lift, prior to passing to its class modulo integers. -/
def rotationNumber (L : IncreasingLift) : ℝ := (toDegreeOneLift L).translationNumber

def rotationNumberType := IncreasingLift → ℝ

/-- Integer change of lift, with its actual translated real homeomorphism. -/
def shiftLift (L : IncreasingLift) (k : ℤ) : IncreasingLift where
  toHomeomorph := L.toHomeomorph.trans (Homeomorph.addRight (k : ℝ))
  strictMono' := L.strictMono'.add_const (k : ℝ)
  map_add_one' := fun x => by
    change L (x + 1) + (k : ℝ) = (L x + (k : ℝ)) + 1
    rw [L.map_add_one']
    ac_rfl

def shiftLiftType := IncreasingLift → ℤ → IncreasingLift

/-- Natural iterates, including the identity lift at time zero. -/
def iterateLift (L : IncreasingLift) : ℕ → IncreasingLift
  | 0 =>
    { toHomeomorph := Homeomorph.refl ℝ
      strictMono' := strictMono_id
      map_add_one' := fun _ => rfl }
  | n + 1 =>
    { toHomeomorph := (iterateLift L n).toHomeomorph.trans L.toHomeomorph
      strictMono' := L.strictMono'.comp (iterateLift L n).strictMono'
      map_add_one' := fun x => by
        change L (iterateLift L n (x + 1)) = L (iterateLift L n x) + 1
        rw [(iterateLift L n).map_add_one', L.map_add_one'] }

def iterateLiftType := IncreasingLift → ℕ → IncreasingLift

def rotationNumber_tendstoStatement : Prop :=
  ∀ (L : IncreasingLift) (x : ℝ),
    Tendsto (fun n : ℕ => ((L : ℝ → ℝ)^[n] x - x) / (n : ℝ))
      atTop (𝓝 (rotationNumber L))

def exists_unique_rotationNumberStatement : Prop :=
  ∀ L : IncreasingLift, ∃! ρ : ℝ, ∀ x : ℝ,
    Tendsto (fun n : ℕ => ((L : ℝ → ℝ)^[n] x - x) / (n : ℝ)) atTop (𝓝 ρ)

def shiftLift_applyStatement : Prop :=
  ∀ (L : IncreasingLift) (k : ℤ) (x : ℝ), shiftLift L k x = L x + (k : ℝ)

def iterateLift_applyStatement : Prop :=
  ∀ (L : IncreasingLift) (q : ℕ) (x : ℝ), iterateLift L q x = (L : ℝ → ℝ)^[q] x

def shiftLift_iterateStatement : Prop :=
  ∀ (L : IncreasingLift) (k : ℤ) (n : ℕ) (x : ℝ),
    (shiftLift L k : ℝ → ℝ)^[n] x = (L : ℝ → ℝ)^[n] x + (n : ℝ) * (k : ℝ)

def rotationNumber_shiftStatement : Prop :=
  ∀ (L : IncreasingLift) (k : ℤ),
    rotationNumber (shiftLift L k) = rotationNumber L + (k : ℝ)

def rotationNumber_iterateStatement : Prop :=
  ∀ (L : IncreasingLift) (q : ℕ),
    rotationNumber (iterateLift L q) = (q : ℝ) * rotationNumber L

def iterate_sub_int_identityStatement : Prop :=
  ∀ (L : IncreasingLift) (q : ℕ) (p : ℤ) (n : ℕ) (x : ℝ),
    (shiftLift (iterateLift L q) (-p) : ℝ → ℝ)^[n] x =
      (L : ℝ → ℝ)^[q * n] x - (n : ℝ) * (p : ℝ)

def rotationNumber_iterate_sub_intStatement : Prop :=
  ∀ (L : IncreasingLift) (q : ℕ) (p : ℤ), 0 < q →
    rotationNumber (shiftLift (iterateLift L q) (-p)) =
      (q : ℝ) * rotationNumber L - (p : ℝ)

end
end Specs.D13Unified.Ch15.RotationLimit
