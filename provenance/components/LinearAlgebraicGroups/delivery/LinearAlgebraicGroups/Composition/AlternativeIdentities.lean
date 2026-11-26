import Mathlib.Algebra.Ring.Associator
import Mathlib.RingTheory.TensorProduct.Basic

open scoped TensorProduct

namespace LinearAlgebraicGroups.Composition

universe u v w

/-- An algebra is alternative when both adjacent repeated-entry associators vanish. -/
def IsAlternative (A : Type u) [NonUnitalNonAssocRing A] : Prop :=
  ∀ x y : A, associator x x y = 0 ∧ associator y x x = 0

variable {A : Type u} [NonUnitalNonAssocRing A]

private theorem associator_add_left (x x' y z : A) :
    associator (x + x') y z = associator x y z + associator x' y z := by
  simp only [associator_apply, add_mul]
  abel

private theorem associator_add_middle (x y y' z : A) :
    associator x (y + y') z = associator x y z + associator x y' z := by
  simp only [associator_apply, add_mul, mul_add]
  abel

private theorem associator_add_right (x y z z' : A) :
    associator x y (z + z') = associator x y z + associator x y z' := by
  simp only [associator_apply, mul_add]
  abel

namespace IsAlternative

theorem associator_swap_left (h : IsAlternative A) (x y z : A) :
    associator x y z = -associator y x z := by
  have hz := (h (x + y) z).1
  rw [associator_add_left, associator_add_middle, associator_add_middle,
    (h x z).1, (h y z).1, zero_add, add_zero] at hz
  exact eq_neg_of_add_eq_zero_left hz

theorem associator_swap_right (h : IsAlternative A) (x y z : A) :
    associator x y z = -associator x z y := by
  have hx := (h (y + z) x).2
  rw [associator_add_middle, associator_add_right, associator_add_right,
    (h y x).2, (h z x).2, zero_add, add_zero] at hx
  exact eq_neg_of_add_eq_zero_left hx

theorem associator_flexible (h : IsAlternative A) (x y : A) :
    associator x y x = 0 := by
  rw [h.associator_swap_left, (h x y).2, neg_zero]

theorem flexible (h : IsAlternative A) (x y : A) :
    (x * y) * x = x * (y * x) :=
  sub_eq_zero.mp (h.associator_flexible x y)

end IsAlternative

theorem isAlternative_iff :
    IsAlternative A ↔ ∀ x y z : A, x = y ∨ y = z ∨ x = z → associator x y z = 0 := by
  constructor
  · intro h x y z heq
    rcases heq with rfl | rfl | rfl
    · exact (h x z).1
    · exact (h y x).2
    · exact h.associator_flexible x y
  · intro h x y
    exact ⟨h x x y (Or.inl rfl), h y x x (Or.inr (Or.inl rfl))⟩

namespace IsAlternative

theorem moufang_left (h : IsAlternative A) (x a y : A) :
    ((x * a) * x) * y = x * (a * (x * y)) := by
  have hleft (b : A) : x * (x * b) = (x * x) * b :=
    (sub_eq_zero.mp (h x b).1).symm
  have hs : associator (x * x) a y + associator (x * x) y a = 0 := by
    rw [h.associator_swap_right (x * x) a y, neg_add_cancel]
  have ht : associator x a y + associator x y a = 0 := by
    rw [h.associator_swap_right x a y, neg_add_cancel]
  apply sub_eq_zero.mp
  calc
    _ = associator (x * a) x y + associator x a (x * y) := by
      simp only [associator_apply]
      abel
    _ = -(associator x (x * a) y + associator x (x * y) a) := by
      rw [h.associator_swap_left (x * a) x y, h.associator_swap_right x a (x * y), neg_add]
    _ = -(associator (x * x) a y + associator (x * x) y a) +
        x * (associator x a y + associator x y a) := by
      simp only [associator_apply, mul_add, mul_sub, hleft]
      abel
    _ = 0 := by rw [hs, ht, mul_zero, neg_zero, add_zero]

theorem opposite (h : IsAlternative A) : IsAlternative Aᵐᵒᵖ := by
  intro x y
  simp [associator_op, (h (MulOpposite.unop x) (MulOpposite.unop y)).1,
    (h (MulOpposite.unop x) (MulOpposite.unop y)).2]

theorem moufang_right (h : IsAlternative A) (x a y : A) :
    y * ((x * a) * x) = ((y * x) * a) * x := by
  have hop := congrArg MulOpposite.unop
    (h.opposite.moufang_left (MulOpposite.op x) (MulOpposite.op a) (MulOpposite.op y))
  simp only [MulOpposite.unop_mul, MulOpposite.unop_op] at hop
  exact (congrArg (y * ·) (h.flexible x a)).trans hop

theorem moufang_middle (h : IsAlternative A) (x a y : A) :
    (x * y) * (a * x) = (x * (y * a)) * x := by
  have hassoc : -associator x (a * x) y = x * associator a x y := by
    rw [associator_apply, neg_sub, ← h.flexible x a, h.moufang_left x a y,
      associator_apply, mul_sub]
  apply sub_eq_zero.mp
  calc
    _ = associator x y (a * x) - x * associator y a x := by
      rw [h.flexible x (y * a)]
      simp only [associator_apply, mul_sub]
      abel
    _ = x * associator a x y - x * associator y a x := by
      rw [h.associator_swap_right x y (a * x), hassoc]
    _ = 0 := by
      rw [h.associator_swap_right a x y, h.associator_swap_left a y x, neg_neg, sub_self]

end IsAlternative

section ScalarExtension

variable {R : Type v} {S : Type w}
  [CommRing R] [CommRing S] [Algebra R S]
  [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

private theorem associator_tmul (s t u : S) (a b c : A) :
    associator (s ⊗ₜ[R] a) (t ⊗ₜ[R] b) (u ⊗ₜ[R] c) =
      (s * t * u) ⊗ₜ[R] associator a b c := by
  simp only [associator_apply, Algebra.TensorProduct.tmul_mul_tmul,
    mul_assoc s t u, TensorProduct.tmul_sub]

private theorem tensor_associator_swaps (h : IsAlternative A) (x y z : S ⊗[R] A) :
    associator x y z = -associator y x z ∧ associator x y z = -associator x z y := by
  induction x with
  | add x x' hx hx' =>
    constructor
    · simp only [associator_add_left, associator_add_middle, hx.1, hx'.1, neg_add]
    · simp only [associator_add_left, hx.2, hx'.2, neg_add]
  | tmul s a =>
    induction y with
    | add y y' hy hy' =>
      constructor
      · simp only [associator_add_middle, associator_add_left, hy.1, hy'.1, neg_add]
      · simp only [associator_add_middle, associator_add_right, hy.2, hy'.2, neg_add]
    | tmul t b =>
      induction z with
      | add z z' hz hz' =>
        constructor
        · simp only [associator_add_right, hz.1, hz'.1, neg_add]
        · simp only [associator_add_right, associator_add_middle, hz.2, hz'.2, neg_add]
      | tmul u c =>
        simp only [associator_tmul]
        constructor
        · rw [h.associator_swap_left a b c, TensorProduct.tmul_neg, mul_comm s t]
        · rw [h.associator_swap_right a b c, TensorProduct.tmul_neg, mul_right_comm s t u]

/-- The tensor product with a commutative scalar extension inherits alternativity. -/
theorem IsAlternative.scalar_extension (h : IsAlternative A) : IsAlternative (S ⊗[R] A) := by
  intro x y
  induction x with
  | tmul s a =>
    induction y with
    | tmul t b =>
      simp only [associator_tmul, (h a b).1, (h a b).2, TensorProduct.tmul_zero, and_self]
    | add y y' hy hy' =>
      simp only [associator_add_right, associator_add_left, hy.1, hy.2, hy'.1, hy'.2,
        add_zero, and_self]
  | add x x' hx hx' =>
    have hs := tensor_associator_swaps h x x' y
    have ht := tensor_associator_swaps h y x x'
    constructor
    · calc
        _ = (associator x x y + associator x' x' y) +
            (associator x x' y + associator x' x y) := by
          simp only [associator_add_left, associator_add_middle]
          abel
        _ = 0 := by rw [hx.1, hx'.1, hs.1, neg_add_cancel, add_zero, add_zero]
    · calc
        _ = (associator y x x + associator y x' x') +
            (associator y x x' + associator y x' x) := by
          simp only [associator_add_middle, associator_add_right]
          abel
        _ = 0 := by rw [hx.2, hx'.2, ht.2, neg_add_cancel, add_zero, add_zero]

end ScalarExtension

end LinearAlgebraicGroups.Composition
