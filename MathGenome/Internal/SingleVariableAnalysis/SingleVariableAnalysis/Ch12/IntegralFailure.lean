import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.IntegralFailure
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Linearity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Uniform
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The moving triangles of K03.12.integral_failure. The integral computation
below works directly with the upstream tagged-sum/Darboux equivalence. -/
noncomputable section
namespace SingleVariableAnalysis.IntegralFailure
open Set Riemann
open scoped BigOperators

/-- The source's piecewise affine triangle (used only for n ≥ 2 on [0,1]). -/
def movingTriangle (n : ℕ) (x : ℝ) : ℝ :=
  if x ≤ 1 / (n : ℝ) then (n : ℝ)^2 * x
  else if x ≤ 2 / (n : ℝ) then (n : ℝ) * (2 - (n : ℝ) * x) else 0

private theorem index_pos {n : ℕ} (hn : 2 ≤ n) : 0 < (n : ℝ) := by
  exact_mod_cast (show 0 < n by omega)

private theorem cuts {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ 1 / (n : ℝ) ∧ 1 / (n : ℝ) ≤ 2 / (n : ℝ) ∧ 2 / (n : ℝ) ≤ 1 := by
  have hp := index_pos hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact ⟨by positivity, div_le_div_of_nonneg_right (by norm_num) hp.le,
    (div_le_one hp).mpr hn'⟩

theorem triangle_continuous (n : ℕ) (hn : 2 ≤ n) :
    ContinuousOn (movingTriangle n) (Icc 0 1) := by
  have hp := index_pos hn
  have hz := ne_of_gt hp
  have inner : Continuous (fun x : ℝ =>
      if x ≤ 2 / (n : ℝ) then (n : ℝ) * (2 - (n : ℝ) * x) else 0) := by
    apply Continuous.if_le (by fun_prop) continuous_const continuous_id continuous_const
    intro x hx
    dsimp at hx
    rw [hx]
    field_simp [hz]
    ring
  apply Continuous.continuousOn
  apply Continuous.if_le (by fun_prop) inner continuous_id continuous_const
  intro x hx
  dsimp at hx
  rw [hx, ite_eq_left (cuts hn).2.1]
  field_simp [hz]
  ring

theorem zero_continuous :
    ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 1) := continuousOn_const

private theorem triangle_zero_at_zero (n : ℕ) : movingTriangle n 0 = 0 := by
  simp [movingTriangle]

private theorem triangle_zero_after {n : ℕ} {x : ℝ}
    (hx : 2 / (n : ℝ) < x) : movingTriangle n x = 0 := by
  have hcut : 1 / (n : ℝ) ≤ 2 / (n : ℝ) :=
    div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg n)
  unfold movingTriangle
  rw [ite_eq_right (not_le.mpr (hcut.trans_lt hx)), ite_eq_right (not_le.mpr hx)]

theorem triangle_pointwise :
    RealPointwiseConverges
      (fun n (x : Icc (0 : ℝ) 1) => movingTriangle (n+2) x) (fun _ => 0) := by
  intro x ε hε
  rcases eq_or_lt_of_le x.property.1 with hx | hx
  · refine ⟨0, fun n _ => ?_⟩
    simp only [← hx, triangle_zero_at_zero, sub_self, abs_zero]
    exact hε
  · obtain ⟨N, hN⟩ := exists_nat_gt (2 / (x : ℝ))
    refine ⟨N, fun n hn => ?_⟩
    have hp : 0 < ((n+2 : ℕ) : ℝ) := by positivity
    have hg : 2 / (x : ℝ) < ((n+2 : ℕ) : ℝ) := by
      have hh : (N : ℝ) ≤ n := by exact_mod_cast hn
      push_cast
      linarith
    have hc : 2 / ((n+2 : ℕ) : ℝ) < (x : ℝ) := by
      apply (div_lt_iff₀ hp).mpr
      have ht := (div_lt_iff₀ hx).mp hg
      nlinarith
    change |movingTriangle (n+2) x - 0| < ε
    rw [triangle_zero_after hc, sub_self, abs_zero]
    exact hε

theorem triangle_peak (n : ℕ) (hn : 2 ≤ n) :
    1 / (n : ℝ) ∈ Icc (0 : ℝ) 1 ∧ movingTriangle n (1 / (n : ℝ)) = n := by
  have hz := ne_of_gt (index_pos hn)
  refine ⟨⟨(cuts hn).1, (cuts hn).2.1.trans (cuts hn).2.2⟩, ?_⟩
  simp only [movingTriangle, le_refl, ite_true]
  field_simp [hz]

theorem triangle_not_uniform :
    ¬ RealUniformConverges
      (fun n (x : Icc (0 : ℝ) 1) => movingTriangle (n+2) x) (fun _ => 0) := by
  intro h
  obtain ⟨N, hN⟩ := h 1 zero_lt_one
  have hn : 2 ≤ N+2 := by omega
  have hpeak := triangle_peak (N+2) hn
  have hh := hN N le_rfl ⟨1 / ((N+2 : ℕ) : ℝ), hpeak.1⟩
  change |movingTriangle (N+2) (1 / ((N+2 : ℕ) : ℝ)) - 0| < 1 at hh
  rw [hpeak.2, sub_zero, abs_of_nonneg (Nat.cast_nonneg (N+2))] at hh
  have : (2 : ℝ) ≤ ((N+2 : ℕ) : ℝ) := by exact_mod_cast hn
  linarith

/-- The primitive increments of an affine function telescope. The error in
an arbitrary closed-cell tagging is bounded by |A| mesh(P) (b-a). -/
theorem affine_tagged_limit (A B a b : ℝ) (hab : a ≤ b) :
    FineTaggedLimit (fun x => A*x+B) a b (A*(b^2-a^2)/2+B*(b-a)) := by
  intro ε hε
  let C := (|A|+1)*(b-a+1)
  have hlen : 0 ≤ b-a := sub_nonneg.mpr hab
  have hC : 0 < C := mul_pos (by positivity) (by linarith)
  refine ⟨ε/C, div_pos hε hC, fun P ξ hP => ?_⟩
  let q : ℝ → ℝ := fun t => A*t^2/2+B*t
  have htel : (∑ i : Fin P.n, (q (P.point i.succ) - q (P.point i.castSucc))) =
      A*(b^2-a^2)/2+B*(b-a) := by
    calc
      _ = q b - q a := by
        simpa only [P.first, P.last] using
          (sum_cell_differences (fun i => q (P.point i)))
      _ = _ := by dsimp [q]; ring
  have herr : taggedSum P ξ (fun x => A*x+B) - (A*(b^2-a^2)/2+B*(b-a)) =
      ∑ i : Fin P.n, A * cellLength P i *
        ((ξ i : ℝ) - (P.point i.succ + P.point i.castSucc)/2) := by
    rw [← htel]
    change (∑ i : Fin P.n, cellLength P i * (A*(ξ i : ℝ)+B)) - _ = _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [cellLength, S.lengthValue, q]
    ring
  have hterm (i : Fin P.n) :
      |A * cellLength P i * ((ξ i : ℝ) -
        (P.point i.succ + P.point i.castSucc)/2)| ≤
          |A| * mesh P * cellLength P i := by
    have hd := (cell_positive P i).le
    have hd' : 0 ≤ P.point i.succ - P.point i.castSucc := hd
    have ht := (ξ i).property
    have hm : |(ξ i : ℝ) - (P.point i.succ + P.point i.castSucc)/2| ≤
        cellLength P i := by
      apply abs_le.mpr
      change -(P.point i.succ-P.point i.castSucc) ≤ _ ∧
        _ ≤ P.point i.succ-P.point i.castSucc
      constructor <;> linarith [ht.1, ht.2]
    rw [abs_mul, abs_mul, abs_of_nonneg hd]
    calc
      _ ≤ |A| * cellLength P i * cellLength P i :=
        mul_le_mul_of_nonneg_left hm (mul_nonneg (abs_nonneg _) hd)
      _ ≤ |A| * mesh P * cellLength P i :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (cellLength_le_mesh P i) (abs_nonneg _)) hd
  have hbound : |taggedSum P ξ (fun x => A*x+B) -
      (A*(b^2-a^2)/2+B*(b-a))| ≤ |A| * mesh P * (b-a) := by
    rw [herr]
    calc
      _ ≤ ∑ i : Fin P.n, |A * cellLength P i *
          ((ξ i : ℝ)-(P.point i.succ+P.point i.castSucc)/2)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin P.n, |A| * mesh P * cellLength P i :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ = |A| * mesh P * (b-a) := by rw [← Finset.mul_sum, sum_cellLength]
  have hsmall : C * mesh P < ε := by
    simpa only [mul_comm] using (lt_div_iff₀ hC).mp hP
  have hcoef : |A| * (b-a) ≤ C := by
    dsimp [C]
    nlinarith [abs_nonneg A]
  rw [Real.norm_eq_abs]
  apply hbound.trans_lt
  calc
    |A| * mesh P * (b-a) = (|A| * (b-a))*mesh P := by ring
    _ ≤ C * mesh P := mul_le_mul_of_nonneg_right hcoef (mesh_nonneg P)
    _ < ε := hsmall

/-- A function equal to an affine function on the interval has its Darboux
integral value, including degenerate intervals. -/
theorem affine_integral_on (f : ℝ → ℝ) (A B : ℝ) {a b : ℝ} (hab : a ≤ b)
    (heq : EqOn f (fun x => A*x+B) (Icc a b)) :
    ∃ h : RealIntegrable f a b, realIntegral f h = A*(b^2-a^2)/2+B*(b-a) := by
  have hc : ContinuousOn f (Icc a b) :=
    (show Continuous (fun x : ℝ => A*x+B) by fun_prop).continuousOn.congr heq
  have hb : BoundedOnInterval f a b :=
    ⟨(isCompact_Icc.image_of_continuousOn hc).bddBelow,
      (isCompact_Icc.image_of_continuousOn hc).bddAbove⟩
  apply (real_tagged_equivalence f hab hb _).mpr
  intro ε hε
  obtain ⟨δ, hδ, hlim⟩ := affine_tagged_limit A B a b hab ε hε
  refine ⟨δ, hδ, fun P ξ hP => ?_⟩
  have hs : taggedSum P ξ f = taggedSum P ξ (fun x => A*x+B) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [heq (cell_subset_interval P i (ξ i).property)]
  change ‖taggedSum P ξ f - (A*(b^2-a^2)/2+B*(b-a))‖ < ε
  rw [hs]
  exact hlim P ξ hP

/-- Splitting the proper Riemann integral at the two joins gives
one half on each sloping piece and zero on the remainder. -/
theorem triangle_integral (n : ℕ) (hn : 2 ≤ n) :
    ∃ h : RealIntegrable (movingTriangle n) 0 1,
      realIntegral (movingTriangle n) h = 1 := by
  have hp := index_pos hn
  have hz := ne_of_gt hp
  obtain ⟨hc0, hc12, hc2⟩ := cuts hn
  have hc02 : 0 ≤ 2 / (n : ℝ) := hc0.trans hc12
  have hcstrict : 1 / (n : ℝ) < 2 / (n : ℝ) :=
    div_lt_div_of_pos_right (by norm_num) hp
  have hleft : EqOn (movingTriangle n) (fun x => (n : ℝ)^2*x+0)
      (Icc 0 (1/(n : ℝ))) := by
    intro x hx
    dsimp [movingTriangle]
    rw [ite_eq_left hx.2]
    ring
  have hmiddle : EqOn (movingTriangle n) (fun x => -(n : ℝ)^2*x+2*(n : ℝ))
      (Icc (1/(n : ℝ)) (2/(n : ℝ))) := by
    intro x hx
    unfold movingTriangle
    by_cases hxc : x ≤ 1/(n : ℝ)
    · have he : x = 1/(n : ℝ) := le_antisymm hxc hx.1
      rw [ite_eq_left hxc, he]
      field_simp [hz]
      ring
    · rw [ite_eq_right hxc, ite_eq_left hx.2]
      ring
  have hright : EqOn (movingTriangle n) (fun x => (0 : ℝ)*x+0)
      (Icc (2/(n : ℝ)) 1) := by
    intro x hx
    unfold movingTriangle
    rw [ite_eq_right (not_le.mpr (hcstrict.trans_le hx.1))]
    by_cases hxc : x ≤ 2/(n : ℝ)
    · have he : x = 2/(n : ℝ) := le_antisymm hxc hx.1
      rw [ite_eq_left hxc, he]
      field_simp [hz]
      ring
    · rw [ite_eq_right hxc]
      ring
  obtain ⟨hl, hIl⟩ := affine_integral_on (movingTriangle n) ((n : ℝ)^2) 0 hc0 hleft
  obtain ⟨hm, hIm⟩ := affine_integral_on (movingTriangle n) (-(n : ℝ)^2)
    (2*(n : ℝ)) hc12 hmiddle
  obtain ⟨hr, hIr⟩ := affine_integral_on (movingTriangle n) 0 0 hc2 hright
  have hIl' : realIntegral (movingTriangle n) hl = 1/2 := by
    rw [hIl]
    field_simp [hz]
    ring
  have hIm' : realIntegral (movingTriangle n) hm = 1/2 := by
    rw [hIm]
    field_simp [hz]
    ring
  have hIr' : realIntegral (movingTriangle n) hr = 0 := by simpa using hIr
  have hb : BoundedOnInterval (movingTriangle n) 0 1 :=
    ⟨(isCompact_Icc.image_of_continuousOn (triangle_continuous n hn)).bddBelow,
      (isCompact_Icc.image_of_continuousOn (triangle_continuous n hn)).bddAbove⟩
  have hb02 := hb.mono (Icc_subset_Icc le_rfl hc2)
  have hs02 := real_split (movingTriangle n) hc0 hc12 hb02
  have h02 := hs02.1.mpr ⟨hl, hm⟩
  have hs := real_split (movingTriangle n) hc02 hc2 hb
  have h01 := hs.1.mpr ⟨h02, hr⟩
  refine ⟨h01, ?_⟩
  have hv01 : realIntegral (movingTriangle n) h01 =
      realIntegral (movingTriangle n) h02 + realIntegral (movingTriangle n) hr :=
    hs.2 h01 h02 hr
  have hv02 : realIntegral (movingTriangle n) h02 =
      realIntegral (movingTriangle n) hl + realIntegral (movingTriangle n) hm :=
    hs02.2 h02 hl hm
  rw [hv01, hv02, hIl', hIm', hIr']
  norm_num

theorem zero_integral : ∃ h : RealIntegrable (fun _ => 0) 0 1,
    realIntegral (fun _ => 0) h = 0 := real_zero_value (by norm_num)

end SingleVariableAnalysis.IntegralFailure
