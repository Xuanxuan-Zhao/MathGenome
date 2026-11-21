import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.ReversibleDirichletForm
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.TimeReversal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

open scoped BigOperators ENNReal
open MeasureTheory
universe u
namespace P207.Markov
noncomputable section

namespace ReversibleDirichletForm
abbrev WeightedSpace : ReversibleDirichletFormSpec.WeightedSpaceType.{u} :=
  @P207.Markov.WeightedSpace
abbrev weightedInner : ReversibleDirichletFormSpec.weightedInnerType.{u} :=
  @P207.Markov.WeightedSpace.weightedInner
abbrev transitionLinear : ReversibleDirichletFormSpec.transitionLinearType.{u} :=
  @P207.Markov.WeightedSpace.transitionLinear
abbrev transitionOperator : ReversibleDirichletFormSpec.transitionOperatorType.{u} :=
  @P207.Markov.WeightedSpace.transitionOperator
abbrev dirichletForm : ReversibleDirichletFormSpec.dirichletFormType.{u} :=
  @P207.Markov.WeightedSpace.dirichletForm
end ReversibleDirichletForm

namespace WeightedSpace

@[simp] theorem weighted_inner {S : Type u} [Fintype S] (π : ProbabilityLaw S)
    (hπ : ∀ i, 0 < π i) (f g : WeightedSpace π hπ) :
    inner ℝ f g = ∑ i, (π i).toReal * f i * g i := rfl

theorem weighted_norm_sq : ReversibleDirichletFormSpec.weighted_norm_sq.{u} := by
  intro S _ π hπ f
  rw [← real_inner_self_eq_norm_sq]
  rfl

@[simp] theorem transition_apply {S : Type u} [Fintype S] (π : ProbabilityLaw S)
    (hπ : ∀ i, 0 < π i) (P : StochasticMatrix S) (f : WeightedSpace π hπ) (i : S) :
    transitionOperator π hπ P f i = ∑ j, realMatrix P i j * f j := rfl

variable {S : Type u} [Fintype S] (π : ProbabilityLaw S) (hπ : ∀ i, 0 < π i)
  (P : StochasticMatrix S)

omit [Fintype S] in
/-- Detailed balance expressed in the real matrix, with no infinite masses. -/
theorem real_detailedBalance (h : DetailedBalance P π) (x y : S) :
    (π x).toReal * realMatrix P x y = (π y).toReal * realMatrix P y x := by
  simpa only [ENNReal.toReal_mul, realMatrix] using congrArg ENNReal.toReal (h x y)

/-- Exchanging the two ends of a reversible flow. -/
theorem flow_swap (h : DetailedBalance P π) (F : S → S → ℝ) :
    (∑ x, ∑ y, (π x).toReal * realMatrix P x y * F x y) =
      ∑ x, ∑ y, (π x).toReal * realMatrix P x y * F y x := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [real_detailedBalance π P h y x]

/-- Sum out a flow that depends only on its starting state. -/
theorem flow_row (f : S → ℝ) :
    (∑ x, ∑ y, (π x).toReal * realMatrix P x y * f x) =
      ∑ x, (π x).toReal * f x := by
  apply Finset.sum_congr rfl
  intro x hx
  calc
    (∑ y, (π x).toReal * realMatrix P x y * f x) =
        (π x).toReal * f x * ∑ y, realMatrix P x y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = _ := by rw [realMatrix_finite_rowsum, mul_one]

/-- Sum out the terminal state using reversibility (and hence stationarity). -/
theorem flow_column (h : DetailedBalance P π) (f : S → ℝ) :
    (∑ x, ∑ y, (π x).toReal * realMatrix P x y * f y) =
      ∑ x, (π x).toReal * f x := by
  rw [flow_swap π P h (fun _ y => f y)]
  exact flow_row π P f

/-- The pairing with the transition operator is the flow pairing. -/
theorem inner_transition (f g : WeightedSpace π hπ) :
    inner ℝ f (transitionOperator π hπ P g) =
      ∑ x, ∑ y, (π x).toReal * realMatrix P x y * (f x * g y) := by
  change (∑ x, (π x).toReal * f x * (∑ y, realMatrix P x y * g y)) = _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem transition_selfAdjoint (h : DetailedBalance P π) :
    IsSelfAdjoint (transitionOperator π hπ P) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro f g
  change inner ℝ (transitionOperator π hπ P f) g = inner ℝ f (transitionOperator π hπ P g)
  rw [real_inner_comm, inner_transition, inner_transition]
  rw [flow_swap π P h (fun x y => g x * f y)]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- Jensen's square inequality, proved directly by nonnegative variance. -/
theorem transition_sq_le (f : WeightedSpace π hπ) (x : S) :
    (transitionOperator π hπ P f x) ^ 2 ≤ ∑ y, realMatrix P x y * (f y) ^ 2 := by
  let a := transitionOperator π hπ P f x
  have hv : 0 ≤ ∑ y, realMatrix P x y * (f y - a) ^ 2 :=
    Finset.sum_nonneg fun y _ => mul_nonneg (realMatrix_nonneg P x y) (sq_nonneg _)
  have he : (∑ y, realMatrix P x y * (f y - a) ^ 2) =
      (∑ y, realMatrix P x y * (f y)^2) - 2 * a *
        (∑ y, realMatrix P x y * f y) + a^2 * (∑ y, realMatrix P x y) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  rw [realMatrix_finite_rowsum] at he
  have ha : (∑ y, realMatrix P x y * f y) = a := rfl
  rw [ha] at he
  dsimp only [a] at he hv
  nlinarith

theorem transition_norm_le (h : DetailedBalance P π) (f : WeightedSpace π hπ) :
    ‖transitionOperator π hπ P f‖ ≤ ‖f‖ := by
  have hs : ‖transitionOperator π hπ P f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [weighted_norm_sq, weighted_norm_sq]
    calc
      (∑ x, (π x).toReal * transitionOperator π hπ P f x * transitionOperator π hπ P f x) ≤
          ∑ x, (π x).toReal * ∑ y, realMatrix P x y * (f y)^2 := by
        apply Finset.sum_le_sum
        intro x hx
        simpa only [sq, mul_assoc] using
          mul_le_mul_of_nonneg_left (transition_sq_le π hπ P f x) ENNReal.toReal_nonneg
      _ = ∑ x, ∑ y, (π x).toReal * realMatrix P x y * (f y)^2 := by
        simp only [Finset.mul_sum, mul_assoc]
      _ = ∑ x, (π x).toReal * f x * f x := by
        rw [flow_column π P h]
        simp only [sq, mul_assoc]
  nlinarith [norm_nonneg f, norm_nonneg (transitionOperator π hπ P f)]

theorem transition_opNorm_le (h : DetailedBalance P π) :
    ‖transitionOperator π hπ P‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using transition_norm_le π hπ P h f

/-- The bilinear energy expansion for every pair of real functions. -/
theorem dirichlet_identity (h : DetailedBalance P π) (f g : WeightedSpace π hπ) :
    dirichletForm π hπ P f g = (1 / 2 : ℝ) *
      ∑ x, ∑ y, (π x).toReal * realMatrix P x y * (f x - f y) * (g x - g y) := by
  have hxx := flow_row π P (fun x => f x * g x)
  have hyy := flow_column π P h (fun x => f x * g x)
  have hxy := flow_swap π P h (fun x y => f x * g y)
  have he : (∑ x, ∑ y, (π x).toReal * realMatrix P x y * (f x - f y) * (g x - g y)) =
      (∑ x, ∑ y, (π x).toReal * realMatrix P x y * (f x * g x)) +
      (∑ x, ∑ y, (π x).toReal * realMatrix P x y * (f y * g y)) -
      (∑ x, ∑ y, (π x).toReal * realMatrix P x y * (f x * g y)) -
      (∑ x, ∑ y, (π x).toReal * realMatrix P x y * (f y * g x)) := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    ring
  rw [hxx, hyy, ← hxy] at he
  rw [dirichletForm, inner_sub_right, inner_transition, weighted_inner]
  simp only [mul_assoc] at he ⊢
  linarith

theorem dirichlet_nonneg (h : DetailedBalance P π) (f : WeightedSpace π hπ) :
    0 ≤ dirichletForm π hπ P f f := by
  rw [dirichlet_identity π hπ P h]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro x hx
  apply Finset.sum_nonneg
  intro y hy
  have hw : 0 ≤ (π x).toReal * realMatrix P x y :=
    mul_nonneg ENNReal.toReal_nonneg (realMatrix_nonneg P x y)
  simpa only [sq, mul_assoc] using mul_nonneg hw (sq_nonneg (f x - f y))

/-- A zero energy function is constant along every positive transition. -/
theorem equal_on_edge_of_dirichlet_zero (h : DetailedBalance P π)
    (f : WeightedSpace π hπ) (hf : dirichletForm π hπ P f f = 0)
    (x y : S) (hxy : 0 < P x y) : f x = f y := by
  let e : S → S → ℝ := fun x y =>
    (π x).toReal * realMatrix P x y * (f x - f y)^2
  have he : ∀ x y, 0 ≤ e x y := fun x y =>
    mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (realMatrix_nonneg P x y)) (sq_nonneg _)
  have hs : (∑ x, ∑ y, e x y) = 0 := by
    rw [dirichlet_identity π hπ P h] at hf
    have hz := (mul_eq_zero.mp hf).resolve_left (by norm_num : (1 / 2 : ℝ) ≠ 0)
    simpa only [e, sq, mul_assoc] using hz
  have hx := (Finset.sum_eq_zero_iff_of_nonneg
    (fun x (_ : x ∈ Finset.univ) => Finset.sum_nonneg (fun y _ => he x y))).mp hs x
      (Finset.mem_univ x)
  have hxy0 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun y (_ : y ∈ Finset.univ) => he x y)).mp hx y (Finset.mem_univ y)
  have hw : 0 < (π x).toReal * realMatrix P x y := mul_pos
    (ENNReal.toReal_pos (ne_of_gt (hπ x)) (π.apply_ne_top x))
    (ENNReal.toReal_pos (ne_of_gt hxy) ((P x).apply_ne_top y))
  have hz : (f x - f y)^2 = 0 := (mul_eq_zero.mp hxy0).resolve_left (ne_of_gt hw)
  nlinarith [sq_nonneg (f x - f y)]

/-- Equality along edges propagates through the canonical powers of the PMF kernel. -/
theorem equal_of_power_positive (f : WeightedSpace π hπ)
    (he : ∀ x y, 0 < P x y → f x = f y) :
    ∀ n x y, 0 < power P n x y → f x = f y := by
  intro n
  induction n with
  | zero =>
    intro x y hxy
    classical
    rw [power_zero, identity_apply] at hxy
    split_ifs at hxy with hy
    · exact congrArg f hy.symm
    · simp at hxy
  | succ n ih =>
    intro x y hxy
    rw [power_succ, comp_apply, tsum_fintype] at hxy
    obtain ⟨z, hz, hzpos⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun z (_ : z ∈ Finset.univ) => show (0 : ℝ≥0∞) ≤ power P n x z * P z y from bot_le)).mp hxy
    obtain ⟨h₁, h₂⟩ := ENNReal.mul_pos_iff.mp hzpos
    exact (ih x z h₁).trans (he z y h₂)

/-- Irreducibility eliminates every nonconstant vector in the nullspace. -/
theorem ker_iff_constant [Nonempty S] (h : DetailedBalance P π) (hi : Irreducible P)
    (f : WeightedSpace π hπ) :
    f ∈ LinearMap.ker (LinearMap.id - transitionLinear π hπ P) ↔
      ∃ c : ℝ, ∀ x, f x = c := by
  constructor
  · intro hf
    have hfix : transitionOperator π hπ P f = f := by
      have hz : f - transitionOperator π hπ P f = 0 := hf
      exact (sub_eq_zero.mp hz).symm
    have hz : dirichletForm π hπ P f f = 0 := by
      rw [dirichletForm, hfix, sub_self, inner_zero_right]
    let x₀ : S := Classical.choice inferInstance
    refine ⟨f x₀, fun x => ?_⟩
    obtain ⟨n, hn⟩ := (hi x x₀).1
    exact equal_of_power_positive π hπ P f
      (equal_on_edge_of_dirichlet_zero π hπ P h f hz) n x x₀ hn
  · rintro ⟨c, hc⟩
    change f - transitionLinear π hπ P f = 0
    apply sub_eq_zero.mpr
    funext x
    change f x = ∑ y, realMatrix P x y * f y
    simp only [hc, ← Finset.sum_mul, realMatrix_finite_rowsum, one_mul]

/-- The reversible Dirichlet-form theorem for every finite irreducible kernel. -/
theorem reversible_form : ReversibleDirichletFormSpec.reversible_form.{u} := by
  intro S _ _ _ _ P π hπ hi hr
  have hb : DetailedBalance P π := (reversible_iff_detailedBalance P π).mp hr
  exact ⟨transition_selfAdjoint π hπ P hb, transition_opNorm_le π hπ P hb,
    dirichlet_identity π hπ P hb, dirichlet_nonneg π hπ P hb,
    ker_iff_constant π hπ P hb hi⟩

end WeightedSpace
end
end P207.Markov
