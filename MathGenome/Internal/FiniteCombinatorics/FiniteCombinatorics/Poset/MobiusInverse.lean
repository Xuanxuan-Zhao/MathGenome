import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Poset.IncidenceAlgebra
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Poset.MobiusInverse

/-! The Möbius inverse on arbitrary finite posets, realizing the inverse,
recurrence, uniqueness and coefficient specialization in `paper.tex`, p204:W08. -/

noncomputable section
open Classical
open scoped FiniteCombinatorics.Poset

namespace FiniteCombinatorics.Poset.IncidenceFunction

variable (R P : Type*) [CommRing R] [PartialOrder P] [Fintype P]

/-- The recursively defined Möbius incidence function. -/
def mobius : IncidenceFunction R P := IncidenceAlgebra.mu R

theorem mobius_inverse :
    zeta R P * mobius R P = delta R P ∧
    mobius R P * zeta R P = delta R P := by
  exact ⟨IncidenceAlgebra.zeta_mul_mu, IncidenceAlgebra.mu_mul_zeta R P⟩

@[simp] theorem mobius_self (x : P) : mobius R P x x = 1 :=
  IncidenceAlgebra.mu_self x

theorem mobius_recurrence (x z : P) (h : x < z) :
    mobius R P x z = -∑ y ∈ Finset.Ico x z, mobius R P x y :=
  IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne h.ne

/-- The recursion forces a right convolution inverse of zeta. -/
theorem mul_zeta_of_recursion (f : IncidenceFunction R P)
    (hd : ∀ x : P, f x x = 1)
    (hr : ∀ x z : P, x < z → f x z = -∑ y ∈ Finset.Ico x z, f x y) :
    f * zeta R P = delta R P := by
  apply IncidenceAlgebra.ext
  intro x z hxz
  rw [convolution_apply]
  have hs : (∑ y ∈ Finset.Icc x z, f x y * zeta R P y z) =
      ∑ y ∈ Finset.Icc x z, f x y := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [zeta_apply, ite_eq_left (Finset.mem_Icc.mp hy).2, mul_one]
  rw [hs, delta_apply]
  by_cases he : x = z
  · subst z
    simp [hd]
  · rw [ite_eq_right he, Finset.Icc_eq_cons_Ico hxz, Finset.sum_cons,
      hr x z (lt_of_le_of_ne hxz he)]
    exact neg_add_cancel _

theorem mobius_unique (f : IncidenceFunction R P)
    (hd : ∀ x : P, f x x = 1)
    (hr : ∀ x z : P, x < z → f x z = -∑ y ∈ Finset.Ico x z, f x y) :
    f = mobius R P := by
  have hf := mul_zeta_of_recursion R P f hd hr
  calc
    f = f * delta R P := (mul_one f).symm
    _ = f * (zeta R P * mobius R P) := by rw [(mobius_inverse R P).1]
    _ = (f * zeta R P) * mobius R P := (mul_assoc _ _ _).symm
    _ = mobius R P := by rw [hf]; exact one_mul _

/-- The universal integer Möbius values specialize through the integer cast. -/
theorem mobius_intCast (x z : P) :
    (mobius ℤ P x z : R) = mobius R P x z := by
  let f : IncidenceFunction R P :=
    { toFun := fun x z => (mobius ℤ P x z : R)
      eq_zero_of_not_le' := by
        intro x z h
        rw [IncidenceAlgebra.apply_eq_zero_of_not_le h, Int.cast_zero] }
  have hd : ∀ x : P, f x x = 1 := by
    intro x
    change (mobius ℤ P x x : R) = 1
    rw [mobius_self, Int.cast_one]
  have hr : ∀ x z : P, x < z → f x z = -∑ y ∈ Finset.Ico x z, f x y := by
    intro x z h
    change (mobius ℤ P x z : R) = -∑ y ∈ Finset.Ico x z, (mobius ℤ P x y : R)
    rw [mobius_recurrence ℤ P x z h, Int.cast_neg, Int.cast_sum]
  exact congrArg (fun g : IncidenceFunction R P => g x z) (mobius_unique R P f hd hr)

end FiniteCombinatorics.Poset.IncidenceFunction
