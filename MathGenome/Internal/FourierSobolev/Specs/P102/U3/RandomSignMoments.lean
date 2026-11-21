import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm

/-! The finite uniform sign cube. The average below is probability counting
measure on all `2 ^ card J` sign choices, including the singleton cube for an
empty index type. -/
namespace P102.U3.RandomSigns
open scoped BigOperators

abbrev Cube (J : Type*) := J → Bool

def sign (b : Bool) : ℝ := if b then 1 else -1

noncomputable def signedSum {J : Type*} [Fintype J] (a : J → ℂ) (ω : Cube J) : ℂ :=
  ∑ j, (sign (ω j) : ℂ) * a j

noncomputable def energy {J : Type*} [Fintype J] (a : J → ℂ) : ℝ :=
  ∑ j, ‖a j‖ ^ 2

noncomputable def moment {J : Type*} [Fintype J] (a : J → ℂ) (q : ℝ) : ℝ := by
  classical
  exact 𝔼 ω : Cube J, ‖signedSum a ω‖ ^ q

end P102.U3.RandomSigns

namespace Specs.P102.U3
open P102.U3.RandomSigns

/-- The full two-sided random-sign moment estimate, with constants chosen
before the finite index type and coefficients. A finite subset is represented
by its subtype; no nonemptiness assumption is imposed. -/
def RandomSignMoments : Prop :=
  ∀ q : ℝ, 0 < q → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
    ∀ (J : Type) [Fintype J] (a : J → ℂ),
      c * (energy a) ^ (q / 2) ≤ moment a q ∧
      moment a q ≤ C * (energy a) ^ (q / 2)

end Specs.P102.U3
