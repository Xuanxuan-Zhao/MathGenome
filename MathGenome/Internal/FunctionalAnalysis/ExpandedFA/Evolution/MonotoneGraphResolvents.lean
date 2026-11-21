import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.MonotoneGraphResolvents
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Monotone.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.RieszRepresentation
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Tactic.Linarith

/-! The resolvent and Yosida approximation of a possibly multivalued monotone
Hilbert graph. Surjectivity supplies the choices, while monotonicity proves
that the inverse relation has exactly one value. The estimates are derived
from x-y = (Jx-Jy) + t(Atx-Aty) and the original graph inequality.
Maximality is the canonical dual-graph maximality transported by real Riesz. -/
noncomputable section
namespace ExpandedFA.Evolution.MonotoneGraphResolvents
universe u

def ShiftOnto : Spec.ShiftOntoType.{u} := Spec.ShiftOntoValue

def resolvent : Spec.ResolventType.{u} := Spec.ResolventValue

def yosida : Spec.YosidaType.{u} := Spec.YosidaValue

theorem resolvent_preimage : Spec.ResolventPreimage.{u} := by
  intro H _ _ A t honto x
  exact (honto x).choose_spec

section Estimates
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The two useful scalar inequalities for a resolvent pair. -/
lemma pair_estimates {u v a b x y : H} {t : ℝ} (ht : 0 ≤ t)
    (hm : 0 ≤ inner ℝ (a - b) (u - v))
    (hx : x = u + t • a) (hy : y = v + t • b) :
    ‖u - v‖ ^ 2 ≤ inner ℝ (u - v) (x - y) ∧
      t * ‖a - b‖ ^ 2 ≤ inner ℝ (a - b) (x - y) := by
  have hd : x - y = (u - v) + t • (a - b) := by
    rw [hx, hy, smul_sub]
    abel
  rw [hd, inner_add_right, inner_add_right,
    real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  rw [real_inner_comm (a - b) (u - v)]
  exact ⟨le_add_of_nonneg_right (mul_nonneg ht hm), le_add_of_nonneg_left hm⟩

/-- Cancel a possible zero norm before using Cauchy--Schwarz. -/
lemma le_of_sq_le_mul {s t : ℝ} (ht : 0 ≤ t) (h : s ^ 2 ≤ s * t) : s ≤ t := by
  by_cases hzero : s = 0
  · simpa [hzero] using ht
  · nlinarith

end Estimates

theorem resolvent_singleValued : Spec.ResolventSingleValued.{u} := by
  intro H _ _ A hmono t ht x u v a b ha hb hx hy
  have hm := (ExpandedFA.Monotone.monotone_hilbertGraph_iff H A).mp hmono ha hb
  have he := (pair_estimates ht.le hm hx hy).1
  rw [sub_self, inner_zero_right] at he
  have hn : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem resolvent_characterization : Spec.ResolventCharacterization.{u} := by
  intro H _ _ A hmono t ht honto x u
  constructor
  · intro h
    obtain ⟨a, ha, hx⟩ := resolvent_preimage H A t honto x
    rw [h] at ha hx
    exact ⟨a, ha, hx⟩
  · rintro ⟨a, ha, hx⟩
    obtain ⟨b, hb, hy⟩ := resolvent_preimage H A t honto x
    exact resolvent_singleValued H A hmono t ht x _ u b a hb ha hy hx

private lemma yosida_eq_of_preimage {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (A : Set (H × H)) (t : ℝ) (ht : 0 < t)
    (honto : Spec.ShiftOntoValue H A t) (x a : H)
    (hx : x = resolvent H A t honto x + t • a) :
    yosida H A t honto x = a := by
  change t⁻¹ • (x - resolvent H A t honto x) = a
  have hdiff := congrArg (fun z : H => z - resolvent H A t honto x) hx
  simp only [add_sub_cancel_left] at hdiff
  rw [hdiff, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]

theorem yosida_graph : Spec.YosidaGraph.{u} := by
  intro H _ _ A t ht honto x
  obtain ⟨a, ha, hx⟩ := resolvent_preimage H A t honto x
  change (resolvent H A t honto x, yosida H A t honto x) ∈ A
  rw [yosida_eq_of_preimage A t ht honto x a hx]
  exact ha

theorem resolvent_identity : Spec.ResolventIdentity.{u} := by
  intro H _ _ A t ht honto x
  obtain ⟨a, _, hx⟩ := resolvent_preimage H A t honto x
  change x = resolvent H A t honto x + t • yosida H A t honto x
  rw [yosida_eq_of_preimage A t ht honto x a hx]
  exact hx

theorem resolvent_firm : Spec.ResolventFirm.{u} := by
  intro H _ _ A hmono t ht honto x y
  have hm := (ExpandedFA.Monotone.monotone_hilbertGraph_iff H A).mp hmono
    (yosida_graph H A t ht honto x) (yosida_graph H A t ht honto y)
  exact (pair_estimates ht.le hm
    (resolvent_identity H A t ht honto x) (resolvent_identity H A t ht honto y)).1

theorem resolvent_nonexpansive : Spec.ResolventNonexpansive.{u} := by
  intro H _ _ A hmono t ht honto
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_one, one_mul]
  apply le_of_sq_le_mul (norm_nonneg _)
  exact (resolvent_firm H A hmono t ht honto x y).trans (real_inner_le_norm _ _)

/-- A slightly stronger form of Yosida monotonicity, used for its sharp bound. -/
lemma yosida_cocoercive {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H))
    (hmono : ExpandedFA.Monotone.Monotone H (ExpandedFA.Monotone.hilbertGraph H A))
    (t : ℝ) (ht : 0 < t) (honto : ShiftOnto H A t) (x y : H) :
    t * ‖yosida H A t honto x - yosida H A t honto y‖ ^ 2 ≤
      inner ℝ (yosida H A t honto x - yosida H A t honto y) (x - y) := by
  have hm := (ExpandedFA.Monotone.monotone_hilbertGraph_iff H A).mp hmono
    (yosida_graph H A t ht honto x) (yosida_graph H A t ht honto y)
  exact (pair_estimates ht.le hm
    (resolvent_identity H A t ht honto x) (resolvent_identity H A t ht honto y)).2

theorem yosida_lipschitz : Spec.YosidaLipschitz.{u} := by
  intro H _ _ A hmono t ht honto
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  change ‖yosida H A t honto x - yosida H A t honto y‖ ≤ t⁻¹ * ‖x - y‖
  have he := (yosida_cocoercive A hmono t ht honto x y).trans (real_inner_le_norm _ _)
  by_cases hs : ‖yosida H A t honto x - yosida H A t honto y‖ = 0
  · rw [hs]
    exact mul_nonneg (inv_nonneg.mpr ht.le) (norm_nonneg _)
  · have hspos : 0 < ‖yosida H A t honto x - yosida H A t honto y‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hs)
    have hscaled : t * ‖yosida H A t honto x - yosida H A t honto y‖ ≤ ‖x - y‖ := by
      apply (mul_le_mul_iff_right₀ hspos).mp
      nlinarith only [he]
    calc
      _ ≤ ‖x - y‖ / t := (le_div_iff₀ ht).mpr (by nlinarith only [hscaled])
      _ = t⁻¹ * ‖x - y‖ := by rw [div_eq_mul_inv, mul_comm]

theorem yosida_monotone : Spec.YosidaMonotone.{u} := by
  intro H _ _ A hmono t ht honto
  apply (ExpandedFA.Monotone.monotone_hilbertGraph_iff H _).mpr
  intro x y a b ha hb
  change a = yosida H A t honto x at ha
  change b = yosida H A t honto y at hb
  subst a
  subst b
  exact (mul_nonneg ht.le (sq_nonneg _)).trans
    (yosida_cocoercive A hmono t ht honto x y)

theorem maximal_monotone : Spec.GraphMaximality.{u} := by
  intro H _ _ _ A hmono honto
  apply (ExpandedFA.Monotone.maximalMonotone_hilbertGraph_iff H A).mpr
  refine ⟨(ExpandedFA.Monotone.monotone_hilbertGraph_iff H A).mp hmono, ?_⟩
  intro u a hrelated
  obtain ⟨v, b, hvb, heq⟩ := honto 1 (by norm_num) (u + a)
  have hd : a - b = -(u - v) := by
    simp only [one_smul] at heq
    apply eq_neg_iff_add_eq_zero.mpr
    rw [← add_sub_add_comm]
    exact sub_eq_zero.mpr (by simpa [add_comm] using heq)
  have hm := hrelated v b hvb
  rw [hd, inner_neg_left, real_inner_self_eq_norm_sq] at hm
  have hn : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
  have huv : u = v := sub_eq_zero.mp (norm_eq_zero.mp hn)
  have hab : a = b := sub_eq_zero.mp (by simpa [huv] using hd)
  simpa [huv, hab] using hvb

end ExpandedFA.Evolution.MonotoneGraphResolvents
