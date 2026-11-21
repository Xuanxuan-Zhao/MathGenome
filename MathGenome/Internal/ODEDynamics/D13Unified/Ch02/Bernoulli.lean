import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch02.Bernoulli
import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.SolutionConcepts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open Set

namespace D13Unified
namespace Bernoulli

lemma forward_velocity (a b p x : ℝ) (hx : 0 < x) :
    (a * x + b * x ^ p) * (1 - p) * x ^ ((1 - p) - 1) =
      (1 - p) * a * x ^ (1 - p) + (1 - p) * b := by
  have h₁ : x * x ^ (-p) = x ^ (1 - p) := by
    rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one]
  have h₂ : x ^ p * x ^ (-p) = 1 := by
    rw [← Real.rpow_add hx, add_neg_cancel, Real.rpow_zero]
  rw [show (1 - p) - 1 = -p by ring]
  calc
    _ = (1 - p) * a * (x * x ^ (-p)) +
        (1 - p) * b * (x ^ p * x ^ (-p)) := by ring
    _ = _ := by rw [h₁, h₂, mul_one]

lemma inverse_velocity (a b p u : ℝ) (hp : p ≠ 1) (hu : 0 < u) :
    ((1 - p) * a * u + (1 - p) * b) * (1 / (1 - p)) *
        u ^ ((1 / (1 - p)) - 1) =
      a * u ^ (1 / (1 - p)) + b * (u ^ (1 / (1 - p))) ^ p := by
  have hq : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  have h₁ : u * u ^ ((1 / (1 - p)) - 1) = u ^ (1 / (1 - p)) := by
    rw [Real.rpow_sub_one hu.ne']
    field_simp
  have hexp : (1 / (1 - p)) * p = (1 / (1 - p)) - 1 := by
    field_simp
    ring
  have h₂ : (u ^ (1 / (1 - p))) ^ p = u ^ ((1 / (1 - p)) - 1) := by
    rw [← Real.rpow_mul hu.le, hexp]
  calc
    _ = a * (u * u ^ ((1 / (1 - p)) - 1)) +
        b * u ^ ((1 / (1 - p)) - 1) := by
      field_simp [hq]
    _ = _ := by rw [h₁, h₂]

lemma forward {a b : ℝ → ℝ} {p : ℝ} {I : TimeInterval} {x : ℝ → ℝ}
    (hx : PositiveBernoulliOn a b p I x) :
    PositiveBernoulliLinearOn a b p I (fun t => (x t) ^ (1 - p)) := by
  refine ⟨hx.1.rpow_const (fun t ht => Or.inl (hx.2.1 t ht).ne'),
    fun t ht => Real.rpow_pos_of_pos (hx.2.1 t ht) _, ?_⟩
  intro t ht
  simpa only [forward_velocity (a t) (b t) p (x t) (hx.2.1 t ht)] using
    (hx.2.2 t ht).rpow_const (p := 1 - p) (Or.inl (hx.2.1 t ht).ne')

lemma inverse {a b : ℝ → ℝ} {p : ℝ} {I : TimeInterval} {u : ℝ → ℝ}
    (hp : p ≠ 1) (hu : PositiveBernoulliLinearOn a b p I u) :
    PositiveBernoulliOn a b p I (fun t => (u t) ^ (1 / (1 - p))) := by
  refine ⟨hu.1.rpow_const (fun t ht => Or.inl (hu.2.1 t ht).ne'),
    fun t ht => Real.rpow_pos_of_pos (hu.2.1 t ht) _, ?_⟩
  intro t ht
  simpa only [inverse_velocity (a t) (b t) p (u t) hp (hu.2.1 t ht)] using
    (hu.2.2 t ht).rpow_const (p := 1 / (1 - p)) (Or.inl (hu.2.1 t ht).ne')

end Bernoulli

/-- Bernoulli's substitution and its inverse on the same positive interval. -/
theorem bernoulli_reduction : Specs.D13Unified.Ch02.Bernoulli.reductionExpected := by
  intro a b p I _ha _hb hp
  have hq : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  refine ⟨fun _ hx => Bernoulli.forward hx, fun _ hu => Bernoulli.inverse hp hu, ?_, ?_⟩
  · intro x hx t ht
    simpa only [one_div] using Real.rpow_rpow_inv (hx.2.1 t ht).le hq
  · intro u hu t ht
    simpa only [one_div] using Real.rpow_inv_rpow (hu.2.1 t ht).le hq

/-- No representative outside the interval is part of this bijection. -/
theorem bernoulli_solution_bijection :
    Specs.D13Unified.Ch02.Bernoulli.solutionBijectionExpected := by
  intro a b p I _ha _hb hp
  let forward : PositiveBernoulliSolutions a b p I →
      PositiveBernoulliLinearSolutions a b p I := fun v =>
    ⟨fun t => (v.val t) ^ (1 - p), by
      obtain ⟨x, hx, hv⟩ := v.property
      exact ⟨fun t => (x t) ^ (1 - p), Bernoulli.forward hx,
        fun t => congrArg (fun z : ℝ => z ^ (1 - p)) (hv t)⟩⟩
  let inverse : PositiveBernoulliLinearSolutions a b p I →
      PositiveBernoulliSolutions a b p I := fun v =>
    ⟨fun t => (v.val t) ^ (1 / (1 - p)), by
      obtain ⟨u, hu, hv⟩ := v.property
      exact ⟨fun t => (u t) ^ (1 / (1 - p)), Bernoulli.inverse hp hu,
        fun t => congrArg (fun z : ℝ => z ^ (1 / (1 - p))) (hv t)⟩⟩
  have hq : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  have hleft : Function.LeftInverse inverse forward := by
    intro v
    apply Subtype.ext
    funext t
    obtain ⟨x, hx, hv⟩ := v.property
    change ((v.val t) ^ (1 - p)) ^ (1 / (1 - p)) = v.val t
    rw [← hv t, one_div, Real.rpow_rpow_inv (hx.2.1 t t.property).le hq]
  have hright : Function.RightInverse inverse forward := by
    intro v
    apply Subtype.ext
    funext t
    obtain ⟨u, hu, hv⟩ := v.property
    change ((v.val t) ^ (1 / (1 - p))) ^ (1 - p) = v.val t
    rw [← hv t, one_div, Real.rpow_inv_rpow (hu.2.1 t t.property).le hq]
  exact ⟨⟨forward, inverse, hleft, hright⟩, fun _ _ => rfl, fun _ _ => rfl⟩

theorem bernoulli_solution_bridge :
    Specs.D13Unified.Ch02.Bernoulli.solutionBridgeExpected := by
  intro F a b p I x hgraph hfield
  constructor
  · rintro ⟨hc, hpos, hd⟩
    exact ⟨⟨hc, hgraph, fun t ht => by rw [hfield t ht]; exact hd t ht⟩, hpos⟩
  · rintro ⟨h, hpos⟩
    exact ⟨h.1, hpos, fun t ht => by rw [← hfield t ht]; exact h.2.2 t ht⟩

theorem bernoulli_linear_solution_bridge :
    Specs.D13Unified.Ch02.Bernoulli.linearSolutionBridgeExpected := by
  intro F a b p I u hgraph hfield
  constructor
  · rintro ⟨hc, hpos, hd⟩
    exact ⟨⟨hc, hgraph, fun t ht => by rw [hfield t ht]; exact hd t ht⟩, hpos⟩
  · rintro ⟨h, hpos⟩
    exact ⟨h.1, hpos, fun t ht => by rw [← hfield t ht]; exact h.2.2 t ht⟩

/-- Continuous coefficients give C¹ regularity, without any extra smoothness
assumption on the coefficients or on the unknown. -/
theorem bernoulli_classical_regularity :
    Specs.D13Unified.Ch02.Bernoulli.classicalRegularityExpected := by
  intro a b p I ha hb
  constructor
  · intro x hx
    rw [contDiffOn_one_iff_derivWithin I.isOpen.uniqueDiffOn]
    refine ⟨fun t ht => (hx.2.2 t ht).differentiableWithinAt, ?_⟩
    have hv : ContinuousOn (fun t => a t * x t + b t * (x t) ^ p) I.carrier :=
      (ha.mul hx.1).add (hb.mul (hx.1.rpow_const (fun t ht => Or.inl (hx.2.1 t ht).ne')))
    apply hv.congr
    intro t ht
    exact (hx.2.2 t ht).derivWithin (I.isOpen.uniqueDiffOn t ht)
  · intro u hu
    rw [contDiffOn_one_iff_derivWithin I.isOpen.uniqueDiffOn]
    refine ⟨fun t ht => (hu.2.2 t ht).differentiableWithinAt, ?_⟩
    have hv : ContinuousOn (fun t => (1 - p) * a t * u t + (1 - p) * b t) I.carrier :=
      ((continuousOn_const.mul ha).mul hu.1).add (continuousOn_const.mul hb)
    apply hv.congr
    intro t ht
    exact (hu.2.2 t ht).derivWithin (I.isOpen.uniqueDiffOn t ht)

theorem bernoulli_classical_solution_bridge :
    Specs.D13Unified.Ch02.Bernoulli.classicalSolutionBridgeExpected := by
  intro F a b p I x hgraph hfield
  exact (bernoulli_solution_bridge F a b p I.toTimeInterval x hgraph hfield).trans
    (and_congr (classical_iff_solutionOn F I x).symm Iff.rfl)

theorem bernoulli_linear_classical_solution_bridge :
    Specs.D13Unified.Ch02.Bernoulli.linearClassicalSolutionBridgeExpected := by
  intro F a b p I u hgraph hfield
  exact (bernoulli_linear_solution_bridge F a b p I.toTimeInterval u hgraph hfield).trans
    (and_congr (classical_iff_solutionOn F I u).symm Iff.rfl)

end D13Unified
