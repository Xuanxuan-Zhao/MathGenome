import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.ArcLength
import MathGenome.Internal.MultivariableAnalysis.D04.C09.PathsLength
import MathGenome.Internal.MultivariableAnalysis.D04.C02.ChainRule
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.FtcFirst
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Higher
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Order.Monotone.Union

noncomputable section
open Set
open scoped Topology BigOperators
namespace D04.C09
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C09.ArcLength.Model
open Specs.SingleVariableAnalysis.Ch09.FtcFirst
open SingleVariableAnalysis.Riemann

lemma accumulation_derivative {f s : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (hs : realAccumulationOn f s a b)
    (hc : ContinuousOn f (Icc a b)) :
    ∀ t ∈ Icc a b, HasDerivWithinAt s (f t) (Icc a b) t := by
  intro t ht
  exact (SingleVariableAnalysis.withinIncrementDerivative_iff_hasDerivWithinAt _ _ _ _).mp
    (real_ftc_first_within f s hf hs t ht (hc t ht))

lemma accumulation_initial {f s : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hs : realAccumulationOn f s a b) : s a = 0 := by
  obtain ⟨h, hh⟩ := hs a (left_mem_Icc.mpr hab)
  rw [hh]
  exact realIntegral_degenerate f a h

lemma positive_derivative_strictMono {f s : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn s (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt s (f t) (Icc a b) t)
    (hp : ∀ t ∈ Icc a b, 0 < f t) : StrictMonoOn s (Icc a b) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a b) hc
  · intro t ht
    exact (hd t (interior_subset ht)).mono interior_subset
  · intro t ht
    exact hp t (interior_subset ht)

/-- The scalar inverse theorem is applied on the closed interval, and thus
also supplies the available one-sided derivative at both endpoints. -/
lemma interval_inverse_C1 {f s : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn s (Icc a b)) (hm : StrictMonoOn s (Icc a b))
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt s (f t) (Icc a b) t)
    (hp : ∀ t ∈ Icc a b, f t ≠ 0) :
    ∃ r : ℝ → ℝ, IntervalInverse s r a b (s a) (s b) ∧
      ContinuousOn (fun u => (f (r u))⁻¹) (Icc (s a) (s b)) ∧
      ∀ u ∈ Icc (s a) (s b),
        HasDerivWithinAt r (f (r u))⁻¹ (Icc (s a) (s b)) u := by
  have himage : s '' Icc a b = Icc (s a) (s b) := hc.image_Icc_of_monotoneOn hab hm.monotoneOn
  have hI : SingleVariableAnalysis.RealInterval (Icc a b) := by
    intro x hx y hy z hxz hzy
    exact ⟨hx.1.trans hxz, hzy.trans hy.2⟩
  have hrelative : SingleVariableAnalysis.RelativeContinuous s (Icc a b) := by
    intro t ht
    exact (SingleVariableAnalysis.relativeContinuousAt_within_iff _ _ _).mpr (hc t ht)
  obtain ⟨hmap, hleft, hright, hcont⟩ :=
    SingleVariableAnalysis.intervalInverse_properties s (Icc a b) hI hrelative (Or.inl hm)
  let r := Function.invFunOn s (Icc a b)
  have hrmap : MapsTo r (Icc (s a) (s b)) (Icc a b) := by rwa [himage] at hmap
  have hrc : ContinuousOn r (Icc (s a) (s b)) := by
    rw [← himage]
    intro u hu
    exact (SingleVariableAnalysis.relativeContinuousAt_within_iff _ _ _).mp (hcont u hu)
  refine ⟨r, ⟨hrmap, hleft, ?_, hrc⟩, (hf.comp hrc hrmap).inv₀ (fun u hu => hp _ (hrmap hu)), ?_⟩
  · simpa only [himage] using hright
  · intro u hu
    have ht := hrmap hu
    have he : s (r u) = u := hright u (himage.symm ▸ hu)
    have h := SingleVariableAnalysis.intervalInverse_derivativeWithin s (Icc a b) (r u) (f (r u))
      hI hrelative (Or.inl hm) ht
      ((SingleVariableAnalysis.withinIncrementDerivative_iff_hasDerivWithinAt _ _ _ _).mpr (hd _ ht))
      (hp _ ht)
    rw [himage, he] at h
    simpa only [one_div] using
      (SingleVariableAnalysis.withinIncrementDerivative_iff_hasDerivWithinAt _ _ _ _).mp h

theorem arc_length_accumulation_exists :
    Specs.D04.C09.ArcLength.arc_length_accumulation_existsType := by
  intro n a b γ v hv
  exact real_accumulation_exists _ (C1Piece.speed_integrable γ.ordered hv)

theorem regular_arc_length : Specs.D04.C09.ArcLength.regular_arc_lengthType := by
  intro n a b γ v hab hv hnonzero s hs
  have hint := C1Piece.speed_integrable hab.le hv
  have hd := accumulation_derivative hint hs hv.1.norm
  have hc : ContinuousOn s (Icc a b) := fun t ht => (hd t ht).continuousWithinAt
  have hm := positive_derivative_strictMono hc hd (fun t ht => norm_pos_iff.mpr (hnonzero t ht))
  have ha := accumulation_initial hab.le hs
  have hl : 0 < s b := by
    rw [← ha]
    exact hm (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
  have himage : s '' Icc a b = Icc 0 (s b) := by
    rw [hc.image_Icc_of_monotoneOn hab.le hm.monotoneOn, ha]
  have hbij : BijOn s (Icc a b) (Icc 0 (s b)) :=
    ⟨fun t ht => himage ▸ mem_image_of_mem s ht, hm.injOn, fun u hu => himage.symm ▸ hu⟩
  have hlength : length γ a b = ENNReal.ofReal (s b) := by
    obtain ⟨P⟩ := partition_exists hab.le
    apply length_eq_of_mesh_limit γ hab.le P (s b)
    intro ε hε
    obtain ⟨δ, hδ, hclose⟩ := C1Piece.polygonalLength_mesh_limit hab.le hv hint ε hε
    refine ⟨δ, hδ, fun Q _ hQ => ?_⟩
    obtain ⟨hi, he⟩ := hs b (right_mem_Icc.mpr hab.le)
    change s b = realIntegral (fun t => ‖v t‖) hi at he
    rw [he]
    exact hclose Q hQ
  obtain ⟨r, hr, hrc, hrd⟩ := interval_inverse_C1 hab.le hc hm hv.1.norm hd
    (fun t ht => norm_ne_zero_iff.mpr (hnonzero t ht))
  rw [ha] at hr hrc hrd
  have hvc : ContinuousOn (fun u => ‖v (r u)‖⁻¹ • v (r u)) (Icc 0 (s b)) :=
    hrc.smul (hv.1.comp hr.2.2.2 hr.1)
  have hcomp : ∀ u ∈ Icc 0 (s b), HasDerivWithinAt (γ ∘ r)
      (‖v (r u)‖⁻¹ • v (r u)) (Icc 0 (s b)) u := by
    intro u hu
    exact (hv.2 _ (hr.1 hu)).scomp u (hrd u hu) hr.1
  refine ⟨ha, hl, hlength, hm, hbij, hc, hd, r, hr, hrc, hrd,
    γ.continuousOn.comp hr.2.2.2 hr.1, ⟨hvc, hcomp⟩, ?_⟩
  intro u hu
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hnonzero _ (hr.1 hu)))]

theorem arc_length_degenerate : Specs.D04.C09.ArcLength.arc_length_degenerateType := by
  intro n a γ
  exact length_degenerate γ a

/-- Extend an accumulation constantly to either side of its piece. -/
def clippedAccumulation (F : ℝ → ℝ) (a b t : ℝ) : ℝ := F (max a (min b t))

lemma clippedAccumulation_left {F : ℝ → ℝ} {a b t : ℝ} (ht : t ≤ a) :
    clippedAccumulation F a b t = F a := by
  simp only [clippedAccumulation, max_eq_left ((min_le_right b t).trans ht)]

lemma clippedAccumulation_right {F : ℝ → ℝ} {a b t : ℝ} (hab : a ≤ b) (ht : b ≤ t) :
    clippedAccumulation F a b t = F b := by
  simp only [clippedAccumulation, min_eq_left ht, max_eq_right hab]

lemma clippedAccumulation_mem {F : ℝ → ℝ} {a b t : ℝ} (ht : t ∈ Icc a b) :
    clippedAccumulation F a b t = F t := by
  simp only [clippedAccumulation, min_eq_right ht.2, max_eq_right ht.1]

lemma clippedAccumulation_continuous {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) : Continuous (clippedAccumulation F a b) := by
  exact hF.comp_continuous (continuous_const.max (continuous_const.min continuous_id))
    (fun t => ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩)

/-- Finite adjacent closed pieces suffice for strict monotonicity. -/
lemma strictMonoOn_partition {a b : ℝ} (P : Partition a b) (s : ℝ → ℝ)
    (hs : ∀ i : Fin P.n, StrictMonoOn s (Icc (P.point i.castSucc) (P.point i.succ))) :
    StrictMonoOn s (Icc a b) := by
  have hprefix : ∀ k (hk : k ≤ P.n),
      StrictMonoOn s (Icc (P.point 0) (P.point ⟨k, by omega⟩)) := by
    intro k
    induction k with
    | zero =>
      intro _
      change StrictMonoOn s (Icc (P.point 0) (P.point 0))
      intro x hx y hy hxy
      have hx : x = P.point 0 := by simpa only [Icc_self, mem_singleton_iff] using hx
      have hy : y = P.point 0 := by simpa only [Icc_self, mem_singleton_iff] using hy
      have he : x = y := hx.trans hy.symm
      exact (hxy.ne he).elim
    | succ k ih =>
      intro hk
      let i : Fin P.n := ⟨k, by omega⟩
      have hstart : P.point 0 ≤ P.point i.castSucc := P.strictMono.monotone (Fin.zero_le _)
      have hend : P.point i.castSucc ≤ P.point i.succ :=
        (P.strictMono (Fin.castSucc_lt_succ (i := i))).le
      have h := (ih (by omega)).union (hs i)
        (show IsGreatest (Icc (P.point 0) (P.point i.castSucc)) (P.point i.castSucc) from
          ⟨right_mem_Icc.mpr hstart, fun _ ht => ht.2⟩)
        (show IsLeast (Icc (P.point i.castSucc) (P.point i.succ)) (P.point i.castSucc) from
          ⟨left_mem_Icc.mpr hend, fun _ ht => ht.1⟩)
      change StrictMonoOn s (Icc (P.point 0) (P.point i.castSucc) ∪
        Icc (P.point i.castSucc) (P.point i.succ)) at h
      rw [Icc_union_Icc_eq_Icc hstart hend] at h
      exact h
  have h := hprefix P.n le_rfl
  change StrictMonoOn s (Icc (P.point 0) (P.point (Fin.last P.n))) at h
  simpa only [P.first, P.last] using h

/-- Summing clipped piece accumulations glues them at their cumulative
lengths. This identity holds at both endpoints of every closed piece. -/
lemma sum_clipped_increment {a b : ℝ} (P : Partition a b)
    (F : Fin P.n → ℝ → ℝ) (hF : ∀ i, F i (P.point i.castSucc) = 0)
    (i : Fin P.n) {t : ℝ} (ht : t ∈ Icc (P.point i.castSucc) (P.point i.succ)) :
    (∑ j, clippedAccumulation (F j) (P.point j.castSucc) (P.point j.succ) t) -
      (∑ j, clippedAccumulation (F j) (P.point j.castSucc) (P.point j.succ)
        (P.point i.castSucc)) = F i t := by
  classical
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · rw [clippedAccumulation_mem ht,
      clippedAccumulation_mem (left_mem_Icc.mpr (ht.1.trans ht.2)), hF, sub_zero]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hji | hij
    · have horder : P.point j.succ ≤ P.point i.castSucc :=
        P.strictMono.monotone (by exact Nat.succ_le_of_lt hji)
      rw [clippedAccumulation_right (P.strictMono.monotone (Fin.castSucc_le_succ j))
        (horder.trans ht.1),
        clippedAccumulation_right (P.strictMono.monotone (Fin.castSucc_le_succ j)) horder,
        sub_self]
    · have horder : P.point i.succ ≤ P.point j.castSucc :=
        P.strictMono.monotone (by exact Nat.succ_le_of_lt hij)
      rw [clippedAccumulation_left (ht.2.trans horder),
        clippedAccumulation_left (ht.1.trans ht.2 |>.trans horder), sub_self]
  · simp

/-- Transport the derivative through an arbitrary continuous inverse on the
image of one closed piece. This permits using a single global inverse at joins. -/
lemma reparametrize_piece {n : ℕ} {γ v : ℝ → E n} {s r : ℝ → ℝ} {a b c d : ℝ}
    (hv : C1Piece γ v a b) (hn : ∀ t ∈ Icc a b, v t ≠ 0)
    (himage : s '' Icc a b = Icc c d)
    (hr : IntervalInverse s r a b c d)
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt s ‖v t‖ (Icc a b) t) :
    ContinuousOn (fun u => ‖v (r u)‖⁻¹) (Icc c d) ∧
    (∀ u ∈ Icc c d, HasDerivWithinAt r ‖v (r u)‖⁻¹ (Icc c d) u) ∧
    C1Piece (γ ∘ r) (fun u => ‖v (r u)‖⁻¹ • v (r u)) c d ∧
    ∀ u ∈ Icc c d, ‖‖v (r u)‖⁻¹ • v (r u)‖ = 1 := by
  have hrc : ContinuousOn (fun u => ‖v (r u)‖⁻¹) (Icc c d) :=
    (hv.1.norm.comp hr.2.2.2 hr.1).inv₀ (fun u hu => norm_ne_zero_iff.mpr (hn _ (hr.1 hu)))
  have hrd : ∀ u ∈ Icc c d, HasDerivWithinAt r ‖v (r u)‖⁻¹ (Icc c d) u := by
    intro u hu
    have ht := hr.1 hu
    have he := hr.2.2.1 u hu
    have hd' := SingleVariableAnalysis.inverse_incrementDerivativeWithin s r (Icc a b)
      (r u) ‖v (r u)‖
      (by rw [himage, he]; exact
        (SingleVariableAnalysis.relativeContinuousAt_within_iff _ _ _).mpr (hr.2.2.2 u hu))
      (hr.2.1 _ ht) (by rw [himage]; exact hr.1) (by simpa only [himage] using hr.2.2.1)
      ((SingleVariableAnalysis.withinIncrementDerivative_iff_hasDerivWithinAt _ _ _ _).mpr (hd _ ht))
      (norm_ne_zero_iff.mpr (hn _ ht))
    rw [himage, he] at hd'
    simpa only [one_div] using
      (SingleVariableAnalysis.withinIncrementDerivative_iff_hasDerivWithinAt _ _ _ _).mp hd'
  refine ⟨hrc, hrd, ⟨hrc.smul (hv.1.comp hr.2.2.2 hr.1), ?_⟩, ?_⟩
  · intro u hu
    exact (hv.2 _ (hr.1 hu)).scomp u (hrd u hu) hr.1
  · intro u hu
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hn _ (hr.1 hu)))]

theorem piecewise_arc_length : Specs.D04.C09.ArcLength.piecewise_arc_lengthType := by
  classical
  intro n a b γ d hab hn hint
  let P := d.partition
  have hlt (i : Fin P.n) : P.point i.castSucc < P.point i.succ :=
    P.strictMono (Fin.castSucc_lt_succ (i := i))
  have hacc (i : Fin P.n) := real_accumulation_exists (fun t => ‖d.velocity i t‖) (hint i)
  choose F hF using hacc
  have hFzero (i : Fin P.n) : F i (P.point i.castSucc) = 0 :=
    accumulation_initial (hlt i).le (hF i)
  have hFd (i : Fin P.n) := accumulation_derivative (hint i) (hF i) (d.smooth i).1.norm
  have hFc (i : Fin P.n) : ContinuousOn (F i) (Icc (P.point i.castSucc) (P.point i.succ)) :=
    fun t ht => (hFd i t ht).continuousWithinAt
  let s (t : ℝ) := ∑ i, clippedAccumulation (F i) (P.point i.castSucc) (P.point i.succ) t
  have hsinc (i : Fin P.n) (t : ℝ) (ht : t ∈ Icc (P.point i.castSucc) (P.point i.succ)) :
      s t - s (P.point i.castSucc) = F i t := sum_clipped_increment P F hFzero i ht
  have hscontinuous : Continuous s := by
    exact continuous_finsetSum _ (fun i _ => clippedAccumulation_continuous (hlt i).le (hFc i))
  have hsderiv (i : Fin P.n) : ∀ t ∈ Icc (P.point i.castSucc) (P.point i.succ),
      HasDerivWithinAt s ‖d.velocity i t‖ (Icc (P.point i.castSucc) (P.point i.succ)) t := by
    intro t ht
    apply ((hFd i t ht).const_add (s (P.point i.castSucc))).congr_of_mem _ ht
    intro u hu
    have he := hsinc i u hu
    linarith
  have hsm : StrictMonoOn s (Icc a b) := strictMonoOn_partition P s (fun i =>
    positive_derivative_strictMono hscontinuous.continuousOn (hsderiv i)
      (fun t ht => norm_pos_iff.mpr (hn i t ht)))
  have ha : s a = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [clippedAccumulation_left (show a ≤ P.point i.castSucc from by
      simpa only [P.first] using P.strictMono.monotone (Fin.zero_le i.castSucc)), hFzero]
  have hb : s b = piecewiseSpeedIntegral d hint := by
    apply Finset.sum_congr rfl
    intro i _
    rw [clippedAccumulation_right (hlt i).le (show P.point i.succ ≤ b from by
      simpa only [P.last] using P.strictMono.monotone (Fin.le_last i.succ))]
    obtain ⟨hi, he⟩ := hF i (P.point i.succ) (right_mem_Icc.mpr (hlt i).le)
    exact he
  have himage : s '' Icc a b = Icc 0 (s b) := by
    rw [hscontinuous.continuousOn.image_Icc_of_monotoneOn hab.le hsm.monotoneOn, ha]
  have hbij : BijOn s (Icc a b) (Icc 0 (s b)) :=
    ⟨fun t ht => himage ▸ mem_image_of_mem s ht, hsm.injOn, fun u hu => himage.symm ▸ hu⟩
  have hI : SingleVariableAnalysis.RealInterval (Icc a b) := by
    intro x hx y hy z hxz hzy
    exact ⟨hx.1.trans hxz, hzy.trans hy.2⟩
  have hrelative : SingleVariableAnalysis.RelativeContinuous s (Icc a b) := by
    intro t ht
    exact (SingleVariableAnalysis.relativeContinuousAt_within_iff _ _ _).mpr
      (hscontinuous.continuousOn t ht)
  obtain ⟨hrmap, hrleft, hrright, hrcontinuous⟩ :=
    SingleVariableAnalysis.intervalInverse_properties s (Icc a b) hI hrelative (Or.inl hsm)
  let r := Function.invFunOn s (Icc a b)
  have hr : IntervalInverse s r a b 0 (s b) := by
    refine ⟨?_, hrleft, ?_, ?_⟩
    · rwa [← himage]
    · simpa only [himage] using hrright
    · rw [← himage]
      intro u hu
      exact (SingleVariableAnalysis.relativeContinuousAt_within_iff _ _ _).mp (hrcontinuous u hu)
  have hl : 0 < s b := by
    rw [← ha]
    exact hsm (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
  have hlength : length γ a b = ENNReal.ofReal (s b) := by
    rw [hb]
    exact (length_speed_integral d hint).1
  refine ⟨s, r, ha, hl, hb, hlength, hsm, hbij, hscontinuous.continuousOn, hr,
    γ.continuousOn.comp hr.2.2.2 hr.1, ?_⟩
  intro i
  dsimp only
  have hsub : Icc (P.point i.castSucc) (P.point i.succ) ⊆ Icc a b :=
    cell_subset_interval P i
  have hleft : P.point i.castSucc ∈ Icc a b := hsub (left_mem_Icc.mpr (hlt i).le)
  have hright : P.point i.succ ∈ Icc a b := hsub (right_mem_Icc.mpr (hlt i).le)
  have hsubimage : Icc (s (P.point i.castSucc)) (s (P.point i.succ)) ⊆ Icc 0 (s b) := by
    intro u hu
    exact ⟨(hbij.1 hleft).1.trans hu.1, hu.2.trans (hbij.1 hright).2⟩
  have hrpiece : IntervalInverse s r (P.point i.castSucc) (P.point i.succ)
      (s (P.point i.castSucc)) (s (P.point i.succ)) := by
    refine ⟨?_, fun t ht => hr.2.1 t (hsub ht),
      fun u hu => hr.2.2.1 u (hsubimage hu), hr.2.2.2.mono hsubimage⟩
    intro u hu
    have ht := hr.1 (hsubimage hu)
    constructor
    · exact (hsm.le_iff_le hleft ht).mp (by rw [hr.2.2.1 u (hsubimage hu)]; exact hu.1)
    · exact (hsm.le_iff_le ht hright).mp (by rw [hr.2.2.1 u (hsubimage hu)]; exact hu.2)
  refine ⟨?_, reparametrize_piece (d.smooth i) (hn i)
    (hscontinuous.continuousOn.image_Icc_of_monotoneOn (hlt i).le (hsm.monotoneOn.mono hsub))
    hrpiece (hsderiv i)⟩
  intro t ht
  obtain ⟨h, he⟩ := hF i t ht
  exact ⟨h, (hsinc i t ht).trans he⟩

/-- No integrability premise is added to piecewise regularity: continuity of
the finitely many velocities supplies the proper integrals. -/
theorem piecewise_regular_arc_length :
    Specs.D04.C09.ArcLength.piecewise_regular_arc_lengthType := by
  intro n a b γ hab hregular
  obtain ⟨d, hd⟩ := hregular
  exact ⟨d, speed_integrable d, piecewise_arc_length γ d hab hd (speed_integrable d)⟩

end D04.C09
