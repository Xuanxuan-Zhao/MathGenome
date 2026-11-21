import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.BetaDefinition
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.SeveralEndpoints
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.Comparison
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.PTest
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Products

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SingleVariableAnalysis.SpecialIntegrals
open Set
open SingleVariableAnalysis.Riemann SingleVariableAnalysis.Riemann.Improper
open Specs.SingleVariableAnalysis.Ch18.BetaDefinition

abbrev betaIntegrand := integrandValue
abbrev beta := betaValue

/-- Continuous data have a proper Darboux integral. This derives the needed
local helper from continuous composition and a polynomial primitive. -/
theorem continuous_darboux_integrable {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) : RealIntegrable f a b := by
  have hi : RealIntegrable (fun x : ℝ => x) a b := by
    apply (PTest.integral_of_continuous_derivative (F := fun x : ℝ => x^2/2) hab continuousOn_id ?_).choose
    intro x _
    convert ((hasDerivAt_id x).pow 2).div_const 2 using 1 <;> simp
  exact real_composition hi hf (fun _ hx => hx)

theorem beta_integrand_positive : integrandPositive := by
  intro p q t ht ht1
  exact mul_pos (realPower_pos t ht (p-1)) (realPower_pos (1-t) (sub_pos.mpr ht1) (q-1))

theorem beta_integrand_continuous (p q : ℝ) : ContinuousOn (betaIntegrand p q) (Ioo 0 1) := by
  apply ContinuousOn.mul
  · exact (realPower_continuous_base (p-1)).mono (fun _ hx => hx.1)
  · exact (realPower_continuous_base (q-1)).comp (continuousOn_const.sub continuousOn_id)
      (fun _ hx => sub_pos.mpr hx.2)

theorem beta_local_integrability : localIntegrability := by
  intro p q u v hu huv hv
  apply continuous_darboux_integrable huv
  apply (beta_integrand_continuous p q).mono
  intro x hx
  exact ⟨(WithBot.coe_lt_coe.mp hu).trans_le hx.1,
    hx.2.trans_lt (WithTop.coe_lt_coe.mp hv)⟩

private def halfSplit : RegularPoint (0 : WithBot ℝ) (1 : WithTop ℝ) :=
  ⟨1/2, by norm_num, by norm_num⟩

private theorem left_regular (p q : ℝ) :
    LeftRegular .real (betaIntegrand p q) (0 : WithBot ℝ) (1/2) := by
  refine ⟨by norm_num, fun t => ?_⟩
  exact beta_local_integrability p q t.val (1/2) t.property.1 t.property.2.le (by norm_num)

/-- Reflection is a proper, decreasing C¹ substitution, applied before
passing to either singular endpoint. -/
theorem darboux_reflection {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : RealIntegrable f (1-b) (1-a))
    (hg : RealIntegrable (fun t => f (1-t)) a b) :
    realIntegral (fun t => f (1-t)) hg = realIntegral f hf := by
  have hba : 1-b ≤ 1-a := sub_le_sub_left hab 1
  have hfo : OrientedRealIntegrable f (1-a) (1-b) := by
    simpa only [Specs.SingleVariableAnalysis.Ch08.Oriented.realIntegrableValue,
      min_eq_right hba, max_eq_left hba] using hf
  have hc : C1OnInterval (fun t : ℝ => 1-t) (fun _ => -1) a b := by
    refine ⟨continuousOn_const, fun t _ => ?_⟩
    exact ((hasDerivAt_id t).const_sub 1).hasDerivWithinAt
  obtain ⟨hneg, hv⟩ := real_monotone_substitution (fun t : ℝ => 1-t) (fun _ => -1) f
    hab hc (Or.inr (fun _ _ _ _ h => sub_le_sub_left h 1)) hfo
  obtain ⟨hneg', hval⟩ := real_mul_value hg (-1)
  have hfor : OrientedRealIntegrable f (1-b) (1-a) := by
    simpa only [Specs.SingleVariableAnalysis.Ch08.Oriented.realIntegrableValue,
      min_eq_left hba, max_eq_right hba] using hf
  have hrev : orientedRealIntegral f hfo = -realIntegral f hf :=
    (oriented_real_symmetry f (1-a) (1-b) hfo hfor).trans
      (congrArg Neg.neg (oriented_real_agreement f hba hfor hf))
  have hv' : realIntegral _ hneg = -realIntegral f hf := hv.trans hrev
  have he : realIntegral _ hneg = realIntegral _ hneg' := rfl
  linarith

private theorem left_converges (p q : ℝ) (hp : 0 < p) :
    LeftConverges .real (betaIntegrand p q) (0 : WithBot ℝ) (1/2) := by
  let g : ℝ → ℝ := fun x => realPower x (p-1)
  have hg1 : LeftRegular .real g (0 : WithBot ℝ) 1 := by
    simpa only [g, show -(1-p) = p-1 by ring] using PTest.power_left_regular (1-p)
  have hgc1 : LeftConverges .real g (0 : WithBot ℝ) 1 := by
    have h := (PTest.power_zero_iff (1-p)).mpr (by linarith)
    change LeftConverges .real (fun x => realPower x (-(1-p))) (0 : WithBot ℝ) 1 at h
    simpa only [g, show -(1-p) = p-1 by ring] using h
  let r : LeftIndex (0 : WithBot ℝ) 1 := ⟨1/2, by norm_num, by norm_num⟩
  have hgc : LeftConverges .real g (0 : WithBot ℝ) (1/2) :=
    (left_finite_prefix g 0 1 hg1 r).mp hgc1
  have hg : LeftRegular .real g (0 : WithBot ℝ) (1/2) :=
    (Classical.choose_spec hgc).choose
  have hc : ContinuousOn (fun x : ℝ => realPower (1-x) (q-1)) (Icc 0 (1/2)) := by
    apply (realPower_continuous_base (q-1)).comp (continuousOn_const.sub continuousOn_id)
    intro x hx
    change 0 < 1-x
    linarith [hx.2]
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hc
  apply left_scaled_comparison (betaIntegrand p q) g 0 (1/2) (left_regular p q) hg
    (max M 0) (le_max_right _ _) _ hgc
  refine ⟨⟨1/4, by norm_num, by norm_num⟩, fun x hx => ?_⟩
  have hx0 : 0 < x.val := WithBot.coe_lt_coe.mp x.property.1
  have hx1 : x.val < 1 := by linarith [x.property.2]
  refine ⟨(beta_integrand_positive p q x.val hx0 hx1).le, ?_⟩
  change realPower x.val (p-1) * realPower (1-x.val) (q-1) ≤
    max M 0 * realPower x.val (p-1)
  rw [mul_comm (max M 0)]
  apply mul_le_mul_of_nonneg_left _ (realPower_pos x.val hx0 (p-1)).le
  exact (hM (mem_image_of_mem _ ⟨hx0.le, x.property.2.le⟩)).trans (le_max_left _ _)

@[simp] theorem beta_integrand_reflect (p q t : ℝ) :
    betaIntegrand p q (1-t) = betaIntegrand q p t := by
  dsimp [betaIntegrand, integrandValue]
  rw [show 1-(1-t) = t by ring, mul_comm]

private theorem right_regular (p q : ℝ) :
    RightRegular .real (betaIntegrand p q) (1/2) (1 : WithTop ℝ) := by
  refine ⟨by norm_num, fun t => ?_⟩
  exact beta_local_integrability p q (1/2) t.val (by norm_num) t.property.1.le t.property.2

private theorem reflect_left_limit (p q L : ℝ)
    (h : LeftHasIntegral .real (betaIntegrand q p) (0 : WithBot ℝ) (1/2) L) :
    RightHasIntegral .real (betaIntegrand p q) (1/2) (1 : WithTop ℝ) L := by
  obtain ⟨hl, hL⟩ := h
  let hr := right_regular p q
  refine ⟨hr, fun ε hε => ?_⟩
  obtain ⟨r, hcut⟩ := hL ε hε
  let s : RightIndex (1/2) (1 : WithTop ℝ) :=
    ⟨1-r.val, by linarith [r.property.2],
      WithTop.coe_lt_coe.mpr (by linarith [WithBot.coe_lt_coe.mp r.property.1])⟩
  refine ⟨s, fun t ht => ?_⟩
  let u : LeftIndex (0 : WithBot ℝ) (1/2) :=
    ⟨1-t.val, WithBot.coe_lt_coe.mpr (sub_pos.mpr (WithTop.coe_lt_coe.mp t.property.2)),
      by linarith [t.property.1]⟩
  have hv : RightTruncation .real (betaIntegrand p q) (1/2) 1 hr t =
      LeftTruncation .real (betaIntegrand q p) 0 (1/2) hl u := by
    have hfl : RealIntegrable (betaIntegrand q p) (1-t.val) (1-(1/2)) := by
      have hu : RealIntegrable (betaIntegrand q p) (1-t.val) (1/2) := hl.2 u
      convert hu using 1 <;> norm_num
    have hgt : RealIntegrable (betaIntegrand p q) (1/2) t.val := hr.2 t
    have he := darboux_reflection t.property.1.le hfl
      (by simpa only [beta_integrand_reflect] using hgt)
    change realIntegral (betaIntegrand p q) (hr.2 t) =
      realIntegral (betaIntegrand q p) (hl.2 u)
    have hhalf : (1 : ℝ) - 1/2 = 1/2 := by norm_num
    simpa only [beta_integrand_reflect, hhalf] using he
  change dist (RightTruncation .real (betaIntegrand p q) (1/2) 1 hr t : ℝ) L < ε
  rw [hv]
  apply hcut u
  change 1-r.val < t.val at ht
  change 1-t.val < r.val
  linarith

private theorem converges (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    Converges .real (betaIntegrand p q) (0 : WithBot ℝ) (1 : WithTop ℝ) := by
  obtain ⟨l, hl⟩ := left_converges p q hp
  obtain ⟨r, hr⟩ := left_converges q p hq
  exact ⟨l+r, beta_local_integrability p q, halfSplit, l, r, hl,
    reflect_left_limit p q r hr, rfl⟩

theorem beta_has_integral : betaHasIntegral := by
  intro p q hp hq
  have hc := converges p q hp hq
  change HasIntegral .real (betaIntegrand p q) 0 1 (beta p q)
  unfold beta betaValue
  rw [dite_eq_left hc]
  exact integral_hasValue .real (betaIntegrand p q) 0 1 hc

theorem beta_independent_endpoints : betaIndependentEndpoints := by
  intro p q hp hq c
  exact ((hasIntegral_at_every_split .real (betaIntegrand p q) 0 1 c (beta p q)).mp
    (beta_has_integral p q hp hq)).2

private theorem beta_integrand_norm (p q : ℝ) :
    (fun t => ‖betaIntegrand p q t‖) = betaIntegrand p q := by
  have hpower (x α : ℝ) : 0 < realPower x α := by
    change 0 < realSeriesExp (α * seriesLog x)
    have he : realSeriesExp (α * seriesLog x) = Real.exp (α * seriesLog x) :=
      expSeries_eq_realExp _
    rw [he]
    exact Real.exp_pos _
  funext t
  exact (Real.norm_eq_abs _).trans (abs_of_pos (mul_pos (hpower _ _) (hpower _ _)))

theorem beta_absolute_convergence : betaAbsoluteConvergence := by
  intro p q hp hq
  rw [beta_integrand_norm]
  exact beta_has_integral p q hp hq

private theorem left_truncation_le_limit (p q L : ℝ)
    (h : LeftHasIntegral .real (betaIntegrand p q) (0 : WithBot ℝ) (1/2) L)
    (t : LeftIndex (0 : WithBot ℝ) (1/2)) :
    (show ℝ from LeftTruncation .real (betaIntegrand p q) 0 (1/2) h.choose t) ≤ L := by
  let H : LeftIndex (0 : WithBot ℝ) (1/2) → ℝ :=
    LeftTruncation .real (betaIntegrand p q) 0 (1/2) h.choose
  by_contra hn
  have hd : 0 < H t - L := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨r, hr⟩ := h.choose_spec (H t-L) hd
  obtain ⟨u, hut, hur⟩ := left_earlier t r
  have hu : RealIntegrable (betaIntegrand p q) u.val (1/2) := h.choose.2 u
  have hi : RealIntegrable (betaIntegrand p q) u.val t.val :=
    hu.subinterval le_rfl hut.le t.property.2.le
  have hpos : 0 ≤ realIntegral _ hi := realIntegral_nonneg hi (by
    intro x hx
    apply (beta_integrand_positive p q x _ _).le
    · exact (WithBot.coe_lt_coe.mp u.property.1).trans_le hx.1
    · exact hx.2.trans_lt (by linarith [t.property.2]))
  have he := left_truncation_sub h.choose t u hut.le hi
  have hmono : H t ≤ H u := by change H u - H t = _ at he; linarith
  have hc := hr u hur
  change dist (H u) L < H t-L at hc
  rw [Real.dist_eq] at hc
  exact (not_lt_of_ge hmono) ((sub_lt_sub_iff_right L).mp (abs_lt.mp hc).2)

/-- A positive continuous function has strictly positive proper integral
on a nondegenerate compact interval. -/
theorem positive_darboux_integral {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn f (Icc a b))
    (hp : ∀ x ∈ Icc a b, 0 < f x) (hf : RealIntegrable f a b) :
    0 < realIntegral f hf := by
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le) hc
  obtain ⟨hm, hv⟩ := PTest.integral_of_continuous_derivative (f := fun _ => f x)
    (F := fun t => f x * t) hab.le continuousOn_const
    (fun t _ => by simpa using (hasDerivAt_id t).const_mul (f x))
  have he := realIntegral_mono _ _ hm hf (fun t ht => hmin ht)
  change realIntegral _ hm ≤ realIntegral _ hf at he
  rw [hv] at he
  have hpos : 0 < f x * b - f x * a := by
    rw [← mul_sub]
    exact mul_pos (hp x hx) (sub_pos.mpr hab)
  exact hpos.trans_le he

private theorem left_limit_positive (p q L : ℝ)
    (h : LeftHasIntegral .real (betaIntegrand p q) (0 : WithBot ℝ) (1/2) L) : 0 < L := by
  let t : LeftIndex (0 : WithBot ℝ) (1/2) := ⟨1/4, by norm_num, by norm_num⟩
  have hc : ContinuousOn (betaIntegrand p q) (Icc t.val (1/2)) :=
    (beta_integrand_continuous p q).mono (by
      intro x hx
      exact ⟨(by norm_num : (0 : ℝ) < t.val).trans_le hx.1,
        hx.2.trans_lt (by norm_num)⟩)
  have hpos := positive_darboux_integral (by norm_num : t.val < (1/2 : ℝ)) hc
    (fun x hx => beta_integrand_positive p q x
      ((by norm_num : (0 : ℝ) < t.val).trans_le hx.1)
      (hx.2.trans_lt (by norm_num))) (h.choose.2 t)
  exact hpos.trans_le (left_truncation_le_limit p q L h t)

theorem beta_positive : betaPositive := by
  intro p q hp hq
  obtain ⟨l, hl⟩ := left_converges p q hp
  obtain ⟨r, hr⟩ := left_converges q p hq
  have he := split_unique .real (betaIntegrand p q) 0 1 halfSplit (beta p q) (l+r)
    (beta_independent_endpoints p q hp hq halfSplit)
    ⟨l, r, hl, reflect_left_limit p q r hr, rfl⟩
  change 0 < beta p q
  rw [he]
  exact add_pos (left_limit_positive p q l hl) (left_limit_positive q p r hr)

theorem beta_symmetry : betaSymmetry := by
  intro p q hp hq
  obtain ⟨l, hl⟩ := left_converges p q hp
  obtain ⟨r, hr⟩ := left_converges q p hq
  have he := split_unique .real (betaIntegrand p q) 0 1 halfSplit (beta p q) (l+r)
    (beta_independent_endpoints p q hp hq halfSplit)
    ⟨l, r, hl, reflect_left_limit p q r hr, rfl⟩
  have he' := split_unique .real (betaIntegrand q p) 0 1 halfSplit (beta q p) (r+l)
    (beta_independent_endpoints q p hq hp halfSplit)
    ⟨r, l, hr, reflect_left_limit q p l hl, rfl⟩
  exact he.trans ((add_comm l r).trans he'.symm)

end SingleVariableAnalysis.SpecialIntegrals
