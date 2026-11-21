import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Poset.MobiusInverse
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Poset.MobiusInversion

/-! Möbius inversion in both directions on arbitrary finite partial orders.
We use the zero extension of incidence functions to write convolution as an
unrestricted finite sum, then let the incidence algebra act on functions. -/

noncomputable section
open Classical
open scoped FiniteCombinatorics.Poset

namespace FiniteCombinatorics.Poset.IncidenceFunction

variable {R P : Type*} [CommRing R] [PartialOrder P] [Fintype P]

/-- Zero extension allows convolution to be summed over the entire finite poset. -/
theorem convolution_univ (a b : IncidenceFunction R P) (x z : P) :
    (a * b) x z = ∑ y, a x y * b y z := by
  rw [convolution_apply]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro y _ hy
  have hn : ¬ (x ≤ y ∧ y ≤ z) := by simpa only [Finset.mem_Icc] using hy
  by_cases hxy : x ≤ y
  · rw [IncidenceAlgebra.apply_eq_zero_of_not_le (fun hyz => hn ⟨hxy, hyz⟩) b,
      mul_zero]
  · rw [IncidenceAlgebra.apply_eq_zero_of_not_le hxy a, zero_mul]

/-- The action summing toward larger elements. -/
def lowerAction (a : IncidenceFunction R P) (f : P → R) (x : P) : R :=
  ∑ y, a y x * f y

/-- The action summing toward smaller elements. -/
def upperAction (a : IncidenceFunction R P) (f : P → R) (x : P) : R :=
  ∑ y, a x y * f y

lemma lowerAction_mul (a b : IncidenceFunction R P) (f : P → R) :
    lowerAction (a * b) f = lowerAction b (lowerAction a f) := by
  funext x
  simp only [lowerAction, convolution_univ, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro y _
  rw [mul_assoc, mul_left_comm (a y z)]

lemma upperAction_mul (a b : IncidenceFunction R P) (f : P → R) :
    upperAction (a * b) f = upperAction a (upperAction b f) := by
  funext x
  simp only [upperAction, convolution_univ, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro y _
  exact mul_assoc _ _ _

@[simp] lemma lowerAction_delta (f : P → R) : lowerAction (delta R P) f = f := by
  funext x
  simp [lowerAction, delta_apply, ite_mul]

@[simp] lemma upperAction_delta (f : P → R) : upperAction (delta R P) f = f := by
  funext x
  simp [upperAction, delta_apply, ite_mul]

lemma lowerAction_eq_sum (a : IncidenceFunction R P) (f : P → R) (x : P) :
    lowerAction a f x = ∑ y ∈ Finset.univ.filter (fun y => y ≤ x), a y x * f y := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro y _ hy
  have hn : ¬ y ≤ x := by simpa using hy
  rw [IncidenceAlgebra.apply_eq_zero_of_not_le hn a, zero_mul]

lemma upperAction_eq_sum (a : IncidenceFunction R P) (f : P → R) (x : P) :
    upperAction a f x = ∑ y ∈ Finset.univ.filter (fun y => x ≤ y), a x y * f y := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro y _ hy
  have hn : ¬ x ≤ y := by simpa using hy
  rw [IncidenceAlgebra.apply_eq_zero_of_not_le hn a, zero_mul]

lemma lowerAction_zeta (f : P → R) (x : P) :
    lowerAction (zeta R P) f x = ∑ y ∈ Finset.univ.filter (fun y => y ≤ x), f y := by
  rw [lowerAction_eq_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [zeta_apply, ite_eq_left (Finset.mem_filter.mp hy).2, one_mul]

lemma upperAction_zeta (f : P → R) (x : P) :
    upperAction (zeta R P) f x = ∑ y ∈ Finset.univ.filter (fun y => x ≤ y), f y := by
  rw [upperAction_eq_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [zeta_apply, ite_eq_left (Finset.mem_filter.mp hy).2, one_mul]

variable (R P)

/-- The lower-sum equivalence of `paper.tex`, p204:W08. -/
theorem mobius_inversion_lower (f g : P → R) :
    (∀ x, g x = ∑ y ∈ Finset.univ.filter (fun y => y ≤ x), f y) ↔
    (∀ x, f x = ∑ y ∈ Finset.univ.filter (fun y => y ≤ x), mobius R P y x * g y) := by
  have hzμ (v : P → R) :
      lowerAction (mobius R P) (lowerAction (zeta R P) v) = v := by
    rw [← lowerAction_mul, (mobius_inverse R P).1, lowerAction_delta]
  have hμz (v : P → R) :
      lowerAction (zeta R P) (lowerAction (mobius R P) v) = v := by
    rw [← lowerAction_mul, (mobius_inverse R P).2, lowerAction_delta]
  constructor
  · intro h x
    have hg : g = lowerAction (zeta R P) f :=
      funext fun y => (h y).trans (lowerAction_zeta f y).symm
    calc
      f x = lowerAction (mobius R P) (lowerAction (zeta R P) f) x :=
        congrFun (hzμ f).symm x
      _ = lowerAction (mobius R P) g x := by rw [← hg]
      _ = _ := lowerAction_eq_sum _ _ _
  · intro h x
    have hf : f = lowerAction (mobius R P) g :=
      funext fun y => (h y).trans (lowerAction_eq_sum _ _ y).symm
    calc
      g x = lowerAction (zeta R P) (lowerAction (mobius R P) g) x :=
        congrFun (hμz g).symm x
      _ = lowerAction (zeta R P) f x := by rw [← hf]
      _ = _ := lowerAction_zeta _ _

/-- The upper-sum equivalence of `paper.tex`, p204:W08. -/
theorem mobius_inversion_upper (f g : P → R) :
    (∀ x, g x = ∑ y ∈ Finset.univ.filter (fun y => x ≤ y), f y) ↔
    (∀ x, f x = ∑ y ∈ Finset.univ.filter (fun y => x ≤ y), mobius R P x y * g y) := by
  have hμz (v : P → R) :
      upperAction (mobius R P) (upperAction (zeta R P) v) = v := by
    rw [← upperAction_mul, (mobius_inverse R P).2, upperAction_delta]
  have hzμ (v : P → R) :
      upperAction (zeta R P) (upperAction (mobius R P) v) = v := by
    rw [← upperAction_mul, (mobius_inverse R P).1, upperAction_delta]
  constructor
  · intro h x
    have hg : g = upperAction (zeta R P) f :=
      funext fun y => (h y).trans (upperAction_zeta f y).symm
    calc
      f x = upperAction (mobius R P) (upperAction (zeta R P) f) x :=
        congrFun (hμz f).symm x
      _ = upperAction (mobius R P) g x := by rw [← hg]
      _ = _ := upperAction_eq_sum _ _ _
  · intro h x
    have hf : f = upperAction (mobius R P) g :=
      funext fun y => (h y).trans (upperAction_eq_sum _ _ y).symm
    calc
      g x = upperAction (zeta R P) (upperAction (mobius R P) g) x :=
        congrFun (hzμ g).symm x
      _ = upperAction (zeta R P) f x := by rw [← hf]
      _ = _ := upperAction_zeta _ _

end FiniteCombinatorics.Poset.IncidenceFunction
