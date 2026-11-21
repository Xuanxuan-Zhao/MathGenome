import MathGenome.Internal.Specs.D07.Ch10.PidNotEuclideanQuadraticIntegerNorm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! Unique integer coordinates, the positive multiplicative integer norm,
and the complete unit group of the complex ring of discriminant -19. -/
noncomputable section
namespace D07.Ch10.PidNotEuclideanQuadraticIntegerNorm

lemma sqrt19_sq : (Real.sqrt 19) ^ 2 = 19 := Real.sq_sqrt (by norm_num)
lemma sqrt19_pos : 0 < Real.sqrt 19 := Real.sqrt_pos.2 (by norm_num)

@[simp] lemma omega_re : omega.re = 1 / 2 := by
  norm_num [omega, sqrtMinus19, Complex.div_re, Complex.normSq_apply]
@[simp] lemma omega_im : omega.im = Real.sqrt 19 / 2 := by
  norm_num [omega, sqrtMinus19, Complex.div_im, Complex.normSq_apply]

@[simp] lemma expression_re (a b : ℤ) :
    (expression a b).re = (a : ℝ) + (b : ℝ) / 2 := by
  simp [expression, Complex.mul_re, div_eq_mul_inv]
@[simp] lemma expression_im (a b : ℤ) :
    (expression a b).im = (b : ℝ) * Real.sqrt 19 / 2 := by
  simp [expression, Complex.mul_im, mul_div_assoc]

theorem squareRootPresentation : Specs.SquareRootPresentation := by
  refine ⟨?_, sqrt19_pos, rfl⟩
  apply Complex.ext <;> simp [sqrtMinus19, pow_two, Complex.mul_re, Complex.mul_im]

theorem quadraticRelation : Specs.QuadraticRelation := by
  apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im]
  · nlinarith [sqrt19_sq]
  · ring

lemma expression_mul (a b c d : ℤ) :
    expression a b * expression c d =
      expression (a * c - 5 * b * d) (a * d + b * c + b * d) := by
  have hw : omega ^ 2 = omega - 5 := by
    have := quadraticRelation
    unfold Specs.QuadraticRelation at this
    linear_combination this
  simp only [expression, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  linear_combination (b : ℂ) * (d : ℂ) * hw

theorem coordinateMembership : Specs.CoordinateMembership := by
  intro z
  constructor
  · intro hz
    induction hz using Subring.closure_induction with
    | mem x hx =>
      have : x = omega := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨0, 1, by simp [expression]⟩
    | zero => exact ⟨0, 0, by simp [expression]⟩
    | one => exact ⟨1, 0, by simp [expression]⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨a, b, rfl⟩ := ihx
      obtain ⟨c, d, rfl⟩ := ihy
      exact ⟨a+c, b+d, by simp [expression]; ring⟩
    | neg x hx ih =>
      obtain ⟨a, b, rfl⟩ := ih
      exact ⟨-a, -b, by simp [expression]; ring⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨a, b, rfl⟩ := ihx
      obtain ⟨c, d, rfl⟩ := ihy
      exact ⟨_, _, expression_mul a b c d⟩
  · rintro ⟨a, b, rfl⟩
    exact integerRing.add_mem (intCast_mem integerRing a)
      (integerRing.mul_mem (intCast_mem integerRing b)
        (Subring.subset_closure (Set.mem_singleton omega)))

lemma expression_injective {a b c d : ℤ} (h : expression a b = expression c d) :
    a = c ∧ b = d := by
  have hi := congrArg Complex.im h
  simp only [expression_im] at hi
  have hbd : (b : ℝ) = (d : ℝ) := by nlinarith [sqrt19_pos]
  have hb : b = d := by exact_mod_cast hbd
  have hr := congrArg Complex.re h
  simp only [expression_re, hb] at hr
  have ha : (a : ℝ) = (c : ℝ) := by linarith
  exact ⟨by exact_mod_cast ha, hb⟩

theorem uniqueCoordinates : Specs.UniqueCoordinates := by
  intro z
  obtain ⟨a, b, h⟩ := (coordinateMembership (z : ℂ)).mp z.property
  refine ⟨(a,b), h, ?_⟩
  rintro ⟨c,d⟩ hcd
  obtain ⟨hac, hbd⟩ := expression_injective (hcd.symm.trans h)
  exact Prod.ext hac hbd

lemma normSq_expression (a b : ℤ) :
    Complex.normSq (expression a b) = ((a ^ 2 + a * b + 5 * b ^ 2 : ℤ) : ℝ) := by
  rw [Complex.normSq_apply, expression_re, expression_im]
  push_cast
  nlinarith [sqrt19_sq]

theorem normFormula : Specs.NormFormula := by
  intro z a b hz
  unfold norm
  rw [hz, normSq_expression, Int.floor_intCast]

lemma norm_cast (z : R) : (norm z : ℝ) = Complex.normSq (z : ℂ) := by
  obtain ⟨a,b,h⟩ := (coordinateMembership (z : ℂ)).mp z.property
  rw [normFormula z a b h, h, normSq_expression]

theorem normConjugate : Specs.NormConjugate := by
  intro z
  change (norm z : ℂ) = (z : ℂ) * (starRingEnd ℂ) (z : ℂ)
  rw [Complex.mul_conj]
  exact congrArg (fun x : ℝ => (x : ℂ)) (norm_cast z)

theorem completedSquare : Specs.CompletedSquare := by
  intro a b
  rw [normSq_expression]
  push_cast
  ring

theorem multiplicativeNorm : Specs.MultiplicativeNorm := by
  refine ⟨?_, ?_, ?_⟩
  · simp [norm]
  · simp [norm]
  · intro z w
    apply Int.cast_injective (α := ℝ)
    rw [Int.cast_mul, norm_cast, norm_cast, norm_cast]
    exact Complex.normSq_mul _ _

theorem positiveNorm : Specs.PositiveNorm := by
  have hp : ∀ z : R, z ≠ 0 → 0 < norm z := by
    intro z hz
    have hzc : (z : ℂ) ≠ 0 := by
      intro h
      apply hz
      exact Subtype.ext h
    exact_mod_cast (show (0 : ℝ) < (norm z : ℝ) by
      rw [norm_cast]; exact Complex.normSq_pos.mpr hzc)
  refine ⟨?_, ?_, hp⟩
  · intro z
    by_cases hz : z = 0
    · simp [hz, multiplicativeNorm.1]
    · exact (hp z hz).le
  · intro z
    constructor
    · intro hn
      by_contra hz
      have := hp z hz
      omega
    · rintro rfl
      exact multiplicativeNorm.1

theorem nonzeroSecondCoordinateBound : Specs.NonzeroSecondCoordinateBound := by
  intro z a b hz hb
  rw [normFormula z a b hz]
  have hb2 : 1 ≤ b ^ 2 := by
    have : b ≤ -1 ∨ 1 ≤ b := by omega
    rcases this with h | h <;> nlinarith [sq_nonneg b]
  have := sq_nonneg (2*a+b)
  nlinarith

theorem normOne : Specs.NormOne := by
  intro z
  constructor
  · intro hn
    obtain ⟨a,b,h⟩ := (coordinateMembership (z : ℂ)).mp z.property
    have hb : b = 0 := by
      by_contra hb
      have := nonzeroSecondCoordinateBound z a b h hb
      omega
    subst b
    have ha : a^2 = 1 := by simpa using (normFormula z a 0 h).symm.trans hn
    have ha' : a = 1 ∨ a = -1 := by
      rcases le_total a 0 with h | h
      · right; nlinarith
      · left; nlinarith
    rcases ha' with rfl | rfl
    · left; apply Subtype.ext; simpa [expression] using h
    · right; apply Subtype.ext; simpa [expression] using h
  · rintro (rfl | rfl)
    · exact multiplicativeNorm.2.1
    · simp [norm, Complex.normSq_apply]

theorem units : Specs.Units := by
  intro z
  constructor
  · rintro ⟨u, rfl⟩
    apply (normOne (u : R)).mp
    have hm := multiplicativeNorm.2.2 (u : R) (↑u⁻¹ : R)
    rw [Units.mul_inv] at hm
    rw [multiplicativeNorm.2.1] at hm
    have hp := positiveNorm.2.2 (u : R) (Units.ne_zero u)
    have hq := positiveNorm.2.2 (↑u⁻¹ : R) (Units.ne_zero _)
    nlinarith
  · rintro (rfl | rfl)
    · exact isUnit_one
    · exact isUnit_one.neg

end D07.Ch10.PidNotEuclideanQuadraticIntegerNorm
