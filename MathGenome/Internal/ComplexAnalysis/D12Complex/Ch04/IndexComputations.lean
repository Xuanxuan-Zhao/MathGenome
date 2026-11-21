import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.IndexComputations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DiskCauchyFormula
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.IndexOperationsHomotopy
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.PrincipalLogarithm
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Data.Finset.Max
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

noncomputable section
open Set Metric
open scoped unitInterval

namespace D12Complex.IndexComputations

private theorem two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
  mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

theorem circle_index_interior :
    Specs.D12Complex.Ch04.IndexComputations.circle_index_interior_type := by
  intro c a r hr ha
  have htrace : a ∉ (DiskCauchyFormula.circlePath c r).trace := by
    rw [DiskCauchyFormula.circlePath_trace c r hr.le]
    exact ne_of_lt (mem_ball_iff_norm.mpr ha)
  rw [IndexOperationsHomotopy.path_index_eq_integral _ _ htrace]
  simp only [one_div]
  rw [DiskCauchyFormula.circle_integral_sub_inv c a r hr ha]
  exact inv_mul_cancel₀ two_pi_I_ne_zero

theorem circle_index_exterior :
    Specs.D12Complex.Ch04.IndexComputations.circle_index_exterior_type := by
  intro c a r hr ha
  have hne : ∀ z ∈ closedBall c r, z - a ≠ 0 := by
    intro z hz
    apply sub_ne_zero.mpr
    intro h
    subst z
    exact (not_le.mpr ha) (mem_closedBall_iff_norm.mp hz)
  have hc : ContinuousOn (fun z : ℂ => (z - a)⁻¹) (closedBall c r) :=
    (continuousOn_id.sub continuousOn_const).inv₀ hne
  have hi : circleIntegral (fun z : ℂ => (z - a)⁻¹) c r = 0 := by
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le
      (s := ∅) countable_empty hc
    intro z hz
    exact (differentiableAt_id.sub_const a).inv (hne z (ball_subset_closedBall hz.1))
  have htrace : a ∉ (DiskCauchyFormula.circlePath c r).trace := by
    rw [DiskCauchyFormula.circlePath_trace c r hr.le]
    intro h
    exact (not_le.mpr ha) (mem_closedBall_iff_norm.mp (sphere_subset_closedBall h))
  rw [IndexOperationsHomotopy.path_index_eq_integral _ _ htrace]
  simp only [one_div]
  rw [DiskCauchyFormula.integral_eq_circleIntegral c r _ hr.le
    (hc.mono sphere_subset_closedBall), hi, mul_zero]

/-- Contract the path to its source inside the given convex set. -/
theorem closed_path_index_zero_of_convex :
    Specs.D12Complex.Ch04.IndexComputations.closed_path_index_zero_of_convex_type := by
  intro γ K a hclosed hK htrace ha
  let z := γ γ.path.a
  have hz : z ∈ K := htrace ⟨γ.path.a, left_mem_Icc.mpr γ.path.ordered, rfl⟩
  have ht (t : I) : γ.path.a + (γ.path.b - γ.path.a) * (t : ℝ) ∈
      Icc γ.path.a γ.path.b := by
    have hd := sub_nonneg.mpr γ.path.ordered
    constructor <;> nlinarith [t.property.1, t.property.2]
  let q : C(I, ℂ) := ⟨fun t => γ (γ.path.a + (γ.path.b - γ.path.a) * (t : ℝ)),
    γ.path.continuousOn.comp_continuous (by fun_prop) ht⟩
  let H : C(I × I, ℂ) :=
    ⟨fun p => (1 - (p.1 : ℝ)) • q p.2 + (p.1 : ℝ) • z, by fun_prop⟩
  let δ := PiecewiseC1Path.const 0 1 zero_le_one z
  have hγ : a ∉ γ.trace := fun h => ha (htrace h)
  have hδ : a ∉ δ.trace := by
    change a ∉ (ComplexPath.const 0 1 zero_le_one z).trace
    rw [ComplexPath.const_trace]
    simpa only [mem_singleton_iff] using (fun (h : a = z) => ha (h.symm ▸ hz))
  have heq := IndexOperationsHomotopy.free_loop_index γ δ a hγ hδ hclosed
    (PiecewiseC1Path.const_closed _ _ _ _) H
    (fun p h => ha (h ▸ hK (htrace ⟨_, ht p.2, rfl⟩) hz
      (sub_nonneg.mpr p.1.property.2) p.1.property.1 (by ring)))
    (by intro t; simp [H, q])
    (by intro t; simp [H, δ, PiecewiseC1Path.const, PiecewiseC1Path.path, ComplexPath.const])
    (by
      intro s
      have he : γ γ.path.b = γ γ.path.a := hclosed
      simp [H, q, he])
  exact heq.trans (IndexOperationsHomotopy.path_index_const 0 1 zero_le_one z a
    ((fun (h : a = z) => ha (h.symm ▸ hz))))

/-- A single logarithm branch gives the empty-crossing computation. -/
theorem closed_path_index_zero_of_avoids_ray :
    Specs.D12Complex.Ch04.IndexComputations.closed_path_index_zero_of_avoids_ray_type := by
  intro γ a η hclosed hη hmiss
  let Ω : Set ℂ := {z | -((z - a) / η) ∈ PrincipalSlitPlane}
  let F : ℂ → ℂ := fun z => PrincipalLog (-((z - a) / η))
  have hΩ : IsOpen Ω :=
    PrincipalLogarithm.isOpen_principalSlitPlane.preimage (by fun_prop)
  have hne (z : ℂ) (hz : z ∈ Ω) : z - a ≠ 0 := by
    have hh := PrincipalLogarithm.principalSlitPlane_ne_zero _ hz
    intro h
    apply hh
    simp [h]
  have hd (z : ℂ) (hz : z ∈ Ω) : HasDerivAt F (1 / (z - a)) z := by
    have hh : HasDerivAt F (1 / -((z - a) / η) * -(1 / η)) z := by
      simpa only [F, Function.comp_def, Pi.neg_apply, id_eq] using
        (PrincipalLogarithm.hasDerivAt_principalLog _ hz).comp z
          (((hasDerivAt_id z).sub_const a).div_const η).neg
    convert hh using 1
    field_simp [hη, hne z hz]
  have hF : Primitives.IsPrimitive Ω (fun z => 1 / (z - a)) F :=
    ⟨⟨hΩ, fun z hz => (hd z hz).differentiableAt⟩, fun z hz => (hd z hz).deriv⟩
  have hγ : γ.trace ⊆ Ω := by
    rintro w ⟨t, ht, rfl⟩
    change -((γ t - a) / η) ∉ Complex.ofReal '' Iic (0 : ℝ)
    rintro ⟨s, hs, he⟩
    apply hmiss t ht
    refine ⟨-s, neg_nonneg.mpr hs, ?_⟩
    have hh : (γ t - a) / η = -(s : ℂ) := by linear_combination he
    have hh' := (div_eq_iff hη).mp hh
    simpa using hh'
  have hi := Primitives.piecewise_endpoint Ω (fun z => 1 / (z - a)) F
    (continuousOn_const.div (continuousOn_id.sub continuousOn_const) hne) hF γ hγ
  have havoid : a ∉ γ.trace := by
    intro h
    exact hne a (hγ h) (sub_self a)
  rw [IndexOperationsHomotopy.path_index_eq_integral _ _ havoid, hi, hclosed, sub_self, mul_zero]

/-- Bridge the source's empty interior crossing set to avoidance of the whole
closed ray on the full closed parameter interval. -/
theorem path_index_empty_ray_crossings :
    Specs.D12Complex.Ch04.IndexComputations.path_index_empty_ray_crossings_type := by
  intro γ a η hclosed ha hunit hstart hcross
  have hη : η ≠ 0 := by
    intro he
    simp [he] at hunit
  have hmiss : ∀ t ∈ Icc γ.path.a γ.path.b,
      ¬ ∃ s : ℝ, 0 ≤ s ∧ γ t - a = (s : ℂ) * η := by
    intro t ht
    by_cases hleft : t = γ.path.a
    · simpa only [hleft] using hstart
    by_cases hright : t = γ.path.b
    · have he : γ γ.path.b = γ γ.path.a := hclosed
      simpa only [hright, he] using hstart
    rintro ⟨s, hs, he⟩
    rcases eq_or_lt_of_le hs with heq | hpos
    · have he' : γ t = a := sub_eq_zero.mp (by simpa [← heq] using he)
      exact ha ⟨t, ht, he'⟩
    · exact hcross t ⟨lt_of_le_of_ne ht.1 (Ne.symm hleft),
        lt_of_le_of_ne ht.2 hright⟩ ⟨s, hpos, he⟩
  simpa only [Finset.sum_empty] using
    closed_path_index_zero_of_avoids_ray γ a η hclosed hη hmiss

open MeasureTheory Filter
open scoped Topology

/-- FTC with finitely many jumps. `left` and `right` are the actual one-sided
limits; no values or derivatives at a jump are prescribed. -/
theorem integral_eq_endpoint_sub_add_jumps (f g left right : ℝ → ℂ)
    (S : Finset ℝ) :
    ∀ (u v : ℝ), u < v → (∀ x ∈ S, x ∈ Ioo u v) →
    (∀ x ∈ Ioo u v, x ∉ S → HasDerivAt f (g x) x) →
    IntervalIntegrable g volume u v →
    (∀ x ∈ S, Tendsto f (𝓝[<] x) (𝓝 (left x))) →
    (∀ x ∈ S, Tendsto f (𝓝[>] x) (𝓝 (right x))) →
    Tendsto f (𝓝[>] u) (𝓝 (right u)) →
    Tendsto f (𝓝[<] v) (𝓝 (left v)) →
    (∫ x in u..v, g x) = left v - right u + ∑ x ∈ S, (left x - right x) := by
  classical
  induction S using Finset.induction_on_max with
  | empty =>
    intro u v huv _ hd hi _ _ hu hv
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto huv
      (fun x hx => hd x hx (by simp)) hi hu hv
  | insert c S hmax ih =>
    intro u v huv hS hd hi hl hr hu hv
    have hc : c ∈ Ioo u v := hS c (Finset.mem_insert_self _ _)
    have hcs : c ∉ S := fun h => (lt_irrefl c) (hmax c h)
    have hSu : ∀ x ∈ S, x ∈ Ioo u c := by
      intro x hx
      exact ⟨(hS x (Finset.mem_insert_of_mem hx)).1, hmax x hx⟩
    have hleft := ih u c hc.1 hSu
      (fun x hx hxs => hd x ⟨hx.1, hx.2.trans hc.2⟩ (by
        simp only [Finset.mem_insert, not_or]; exact ⟨hx.2.ne, hxs⟩))
      (hi.mono_set (by simpa [uIcc_of_le huv.le, uIcc_of_le hc.1.le] using
        (Icc_subset_Icc (a₁ := u) (b₁ := c) le_rfl hc.2.le)))
      (fun x hx => hl x (Finset.mem_insert_of_mem hx))
      (fun x hx => hr x (Finset.mem_insert_of_mem hx)) hu
      (hl c (Finset.mem_insert_self _ _))
    have hright : (∫ x in c..v, g x) = left v - right c :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hc.2
        (fun x hx => hd x ⟨hc.1.trans hx.1, hx.2⟩ (by
          simp only [Finset.mem_insert, not_or]
          exact ⟨hx.1.ne', fun h => (not_lt_of_gt hx.1) (hmax x h)⟩))
        (hi.mono_set (by simpa [uIcc_of_le huv.le, uIcc_of_le hc.2.le] using
          (Icc_subset_Icc (a₁ := c) (b₁ := v) hc.1.le le_rfl)))
        (hr c (Finset.mem_insert_self _ _)) hv
    rw [← intervalIntegral.integral_add_adjacent_intervals (a := u) (b := c) (c := v)
      (hi.mono_set (by simpa [uIcc_of_le huv.le, uIcc_of_le hc.1.le] using
        (Icc_subset_Icc (a₁ := u) (b₁ := c) le_rfl hc.2.le)))
      (hi.mono_set (by simpa [uIcc_of_le huv.le, uIcc_of_le hc.2.le] using
        (Icc_subset_Icc (a₁ := c) (b₁ := v) hc.1.le le_rfl))), hleft, hright, Finset.sum_insert hcs]
    abel

/-- The sign on each side of a simple real zero is fixed by its derivative. -/
theorem signs_near_simple_zero {f : ℝ → ℝ} {d c : ℝ}
    (hd : HasDerivAt f d c) (hf : f c = 0) (hpos : 0 < d) :
    (∀ᶠ t in 𝓝[<] c, f t < 0) ∧ (∀ᶠ t in 𝓝[>] c, 0 < f t) := by
  have hs := hasDerivAt_iff_tendsto_slope_left_right.mp hd
  constructor
  · have hh := hs.1.eventually (Ioi_mem_nhds hpos)
    filter_upwards [hh, self_mem_nhdsWithin] with t ht htc
    have hp : 0 < (f t) / (t - c) := by simpa [slope, hf, smul_eq_mul, div_eq_inv_mul] using ht
    exact (div_pos_iff.mp hp).resolve_left (by intro h; linarith [h.2, show t < c from htc]) |>.1
  · have hh := hs.2.eventually (Ioi_mem_nhds hpos)
    filter_upwards [hh, self_mem_nhdsWithin] with t ht htc
    have hp : 0 < (f t) / (t - c) := by simpa [slope, hf, smul_eq_mul, div_eq_inv_mul] using ht
    exact (div_pos_iff.mp hp).resolve_right (by intro h; linarith [h.2, show c < t from htc]) |>.1

/-- The two branch limits at a transverse meeting with the positive real ray.
The order of the limits records the orientation of the crossing. -/
theorem log_limits_at_transverse_crossing {w : ℝ → ℂ} {d : ℂ} {c : ℝ}
    (hd : HasDerivAt w d c) (hre : 0 < (w c).re) (him : (w c).im = 0)
    (hne : d.im ≠ 0) :
    let signVal : ℂ := if 0 < d.im then 1 else -1
    Tendsto (fun t => Complex.log (-w t)) (𝓝[<] c)
      (𝓝 ((Real.log ‖w c‖ : ℂ) + signVal * (Real.pi : ℂ) * Complex.I)) ∧
    Tendsto (fun t => Complex.log (-w t)) (𝓝[>] c)
      (𝓝 ((Real.log ‖w c‖ : ℂ) - signVal * (Real.pi : ℂ) * Complex.I)) := by
  have hw : ContinuousAt (fun t => -w t) c := hd.continuousAt.neg
  have hdi : HasDerivAt (fun t => (w t).im) d.im c :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt c hd
  have hneg : (-w c).re < 0 := by simpa using neg_neg_of_pos hre
  have hzero : (-w c).im = 0 := by simp [him]
  have hup := Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hneg hzero
  have hdown := Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hneg hzero
  dsimp
  by_cases hp : 0 < d.im
  · simp only [ite_eq_left hp, one_mul]
    have hs := signs_near_simple_zero hdi him hp
    constructor
    · simpa only [norm_neg, Function.comp_def, Pi.neg_apply, one_mul] using hup.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hw.tendsto.mono_left nhdsWithin_le_nhds,
          hs.1.mono (fun t ht => by change 0 ≤ (-w t).im; simpa using (neg_pos.mpr ht).le)⟩)
    · simpa only [norm_neg, Function.comp_def, Pi.neg_apply, one_mul] using hdown.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hw.tendsto.mono_left nhdsWithin_le_nhds,
          hs.2.mono (fun t ht => by change (-w t).im < 0; simpa using neg_neg_of_pos ht)⟩)
  · simp only [ite_eq_right hp, neg_mul, sub_neg_eq_add]
    have hn : d.im < 0 := lt_of_le_of_ne (le_of_not_gt hp) hne
    have hs := signs_near_simple_zero hdi.neg (by simp [him]) (neg_pos.mpr hn)
    constructor
    · simpa only [norm_neg, Function.comp_def, Pi.neg_apply, one_mul, sub_eq_add_neg] using hdown.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hw.tendsto.mono_left nhdsWithin_le_nhds,
          hs.1.mono (fun t ht => by change (-w t).im < 0; exact ht)⟩)
    · simpa only [norm_neg, Function.comp_def, Pi.neg_apply, one_mul] using hup.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hw.tendsto.mono_left nhdsWithin_le_nhds,
          hs.2.mono (fun t ht => by change 0 ≤ (-w t).im; exact ht.le)⟩)

/-- A point different from all partition nodes lies in an open piece. -/
theorem exists_open_piece_of_not_node {n : ℕ} (node : Fin (n + 1) → ℝ)
    {t : ℝ} (hfirst : node 0 < t) (hlast : t < node (Fin.last n))
    (hne : ∀ i, t ≠ node i) :
    ∃ i : Fin n, t ∈ Ioo (node i.castSucc) (node i.succ) := by
  induction n with
  | zero => exact (not_lt_of_gt hfirst hlast).elim
  | succ n ih =>
    by_cases ht : t < node (0 : Fin (n + 1)).succ
    · exact ⟨0, hfirst, ht⟩
    · have hlt : node (0 : Fin (n + 1)).succ < t :=
        lt_of_le_of_ne (le_of_not_gt ht) (hne _).symm
      obtain ⟨i, hi⟩ := ih (fun j => node j.succ) hlt hlast (fun j => hne j.succ)
      exact ⟨i.succ, by simpa only [Fin.succ_castSucc] using hi⟩

/-- The full finite transverse ray-crossing formula, counting parameter times. -/
theorem path_index_signed_ray_crossings :
    Specs.D12Complex.Ch04.IndexComputations.path_index_signed_ray_crossings_type := by
  classical
  intro γ a η S hclosed ha hunit hstart hS hcorner htrans
  obtain ⟨P, hP⟩ := hcorner
  have hη : η ≠ 0 := by intro h; simp [h] at hunit
  have hSin : ∀ t ∈ S, t ∈ Ioo γ.path.a γ.path.b := fun t ht => (hS t).mp ht |>.1
  by_cases hab : γ.path.a < γ.path.b
  swap
  · have he : γ.path.a = γ.path.b := le_antisymm γ.path.ordered (le_of_not_gt hab)
    have hSe : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro t ht; have hh := hSin t ht; rw [he] at hh; exact (not_lt_of_gt hh.1 hh.2))
    rw [hSe, Finset.sum_empty]
    exact IndexOperationsHomotopy.path_index_degenerate γ a he ha
  let w : ℝ → ℂ := fun t => (γ t - a) / η
  let f : ℝ → ℂ := fun t => Complex.log (-w t)
  let g : ℝ → ℂ := fun t => 1 / (γ t - a) * deriv γ t
  let signVal : ℝ → ℂ := fun t => if 0 < (deriv γ t / η).im then 1 else -1
  let A : ℝ → ℂ := fun t => (Real.log ‖w t‖ : ℂ)
  let left : ℝ → ℂ := fun t => if t ∈ S then A t + signVal t * Real.pi * Complex.I else f t
  let right : ℝ → ℂ := fun t => if t ∈ S then A t - signVal t * Real.pi * Complex.I else f t
  let T : Finset ℝ := S ∪ (Finset.univ.image P.node).filter (fun t => t ∈ Ioo γ.path.a γ.path.b)
  have hwne (t : ℝ) (ht : t ∈ Icc γ.path.a γ.path.b) : γ t - a ≠ 0 :=
    sub_ne_zero.mpr (fun hh => ha ⟨t, ht, hh⟩)
  have hoff (t : ℝ) (ht : t ∈ Icc γ.path.a γ.path.b) (hts : t ∉ S) :
      -w t ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_contra hh
    push Not at hh
    have him : (w t).im = 0 := by simpa using hh.2
    have hre : 0 ≤ (w t).re := by simpa using hh.1
    have hreal : w t = ((w t).re : ℂ) := by
      apply Complex.ext <;> simp [him]
    have heq : γ t - a = ((w t).re : ℂ) * η := (div_eq_iff hη).mp hreal
    by_cases hleft : t = γ.path.a
    · exact hstart ⟨(w t).re, hre, by simpa only [← hleft] using heq⟩
    by_cases hright : t = γ.path.b
    · apply hstart
      refine ⟨(w t).re, hre, ?_⟩
      simpa only [hright, show γ γ.path.b = γ γ.path.a from hclosed] using heq
    have hpos : 0 < (w t).re := lt_of_le_of_ne hre (by
      intro hz; apply hwne t ht; simpa [← hz] using heq)
    exact hts ((hS t).mpr ⟨⟨lt_of_le_of_ne ht.1 (Ne.symm hleft),
      lt_of_le_of_ne ht.2 hright⟩, (w t).re, hpos, heq⟩)
  have hwcont : ContinuousOn w (Icc γ.path.a γ.path.b) :=
    (γ.path.continuousOn.sub continuousOn_const).div_const η
  have hfcont (t : ℝ) (ht : t ∈ Icc γ.path.a γ.path.b) (hts : t ∉ S) :
      ContinuousWithinAt f (Icc γ.path.a γ.path.b) t :=
    by
      have hh : ContinuousWithinAt (fun x => -w x) (Icc γ.path.a γ.path.b) t :=
        (hwcont t ht).neg
      exact hh.clog (hoff t ht hts)
  have hc (t : ℝ) (ht : t ∈ S) :
      Tendsto f (𝓝[<] t) (𝓝 (left t)) ∧ Tendsto f (𝓝[>] t) (𝓝 (right t)) := by
    obtain ⟨i, hi⟩ := hP t ht
    have hd : HasDerivAt w (deriv γ t / η) t :=
      (((P.differentiableAt_piece i hi).hasDerivAt).sub_const a).div_const η
    obtain ⟨s, hs, he⟩ := ((hS t).mp ht).2
    have hew : w t = (s : ℂ) := (div_eq_iff hη).mpr he
    have hh := log_limits_at_transverse_crossing hd (by simpa [hew] using hs)
      (by simp [hew]) (htrans t ht)
    simpa only [f, left, right, A, signVal, ite_eq_left ht] using hh
  have hTin : ∀ t ∈ T, t ∈ Ioo γ.path.a γ.path.b := by
    intro t ht
    rcases Finset.mem_union.mp ht with hs | hn
    · exact hSin t hs
    · exact (Finset.mem_filter.mp hn).2
  have hst : S ⊆ T := Finset.subset_union_left
  have hlimit (t : ℝ) (ht : t ∈ T) :
      Tendsto f (𝓝[<] t) (𝓝 (left t)) ∧ Tendsto f (𝓝[>] t) (𝓝 (right t)) := by
    by_cases hs : t ∈ S
    · exact hc t hs
    · have hti := hTin t ht
      have hh : ContinuousAt f t := (hfcont t ⟨hti.1.le, hti.2.le⟩ hs).continuousAt
        (Icc_mem_nhds hti.1 hti.2)
      simpa only [left, right, ite_eq_right hs] using
        And.intro (hh.tendsto.mono_left nhdsWithin_le_nhds)
          (hh.tendsto.mono_left nhdsWithin_le_nhds)
  have hnotleft : γ.path.a ∉ S := by
    intro h; exact (lt_irrefl _) (hSin _ h).1
  have hnotright : γ.path.b ∉ S := by
    intro h; exact (lt_irrefl _) (hSin _ h).2
  have hleftlim : Tendsto f (𝓝[>] γ.path.a) (𝓝 (right γ.path.a)) := by
    have hh := (hfcont _ (left_mem_Icc.mpr hab.le) hnotleft).tendsto
    rw [nhdsWithin_Icc_eq_nhdsGE hab] at hh
    simpa only [right, ite_eq_right hnotleft] using hh.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hrightlim : Tendsto f (𝓝[<] γ.path.b) (𝓝 (left γ.path.b)) := by
    have hh := (hfcont _ (right_mem_Icc.mpr hab.le) hnotright).tendsto
    rw [nhdsWithin_Icc_eq_nhdsLE hab] at hh
    simpa only [left, ite_eq_right hnotright] using hh.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)
  have hderiv (t : ℝ) (ht : t ∈ Ioo γ.path.a γ.path.b) (hnt : t ∉ T) :
      HasDerivAt f (g t) t := by
    have hns : t ∉ S := fun hs => hnt (hst hs)
    have hnn : ∀ i, t ≠ P.node i := by
      intro i he
      apply hnt
      apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he.symm⟩, ht⟩
    obtain ⟨i, hi⟩ := exists_open_piece_of_not_node P.node
      (by simpa only [P.first] using ht.1) (by simpa only [P.last] using ht.2) hnn
    have hd : HasDerivAt (fun t => -w t) (-(deriv γ t / η)) t :=
      ((((P.differentiableAt_piece i hi).hasDerivAt).sub_const a).div_const η).neg
    have hh := hd.clog_real (hoff t ⟨ht.1.le, ht.2.le⟩ hns)
    convert hh using 1
    dsimp [g, w]
    field_simp [hη, hwne t ⟨ht.1.le, ht.2.le⟩]
  have hint : IntervalIntegrable g volume γ.path.a γ.path.b :=
    C1Partition.parameter_integrable γ.path P _ (IndexOperationsHomotopy.reciprocal_continuousOn γ a ha)
  have heq := integral_eq_endpoint_sub_add_jumps f g left right T _ _ hab hTin hderiv hint
    (fun t ht => (hlimit t ht).1) (fun t ht => (hlimit t ht).2) hleftlim hrightlim
  have hend : left γ.path.b = right γ.path.a := by
    simp only [left, right, ite_eq_right hnotleft, ite_eq_right hnotright, f, w]
    rw [show γ γ.path.b = γ γ.path.a from hclosed]
  have hsum : (∑ t ∈ T, (left t - right t)) =
      (2 * Real.pi * Complex.I : ℂ) * ∑ t ∈ S, signVal t := by
    rw [Finset.mul_sum]
    calc
      (∑ t ∈ T, (left t - right t)) =
          ∑ t ∈ T, if t ∈ S then (2 * Real.pi * Complex.I : ℂ) * signVal t else 0 := by
        apply Finset.sum_congr rfl
        intro t ht
        by_cases hs : t ∈ S <;> simp only [left, right, hs, ite_true, ite_false]
        · ring
        · ring
      _ = ∑ t ∈ S, (2 * Real.pi * Complex.I : ℂ) * signVal t := by
        have hh := Finset.sum_subset hst (f := fun t =>
          if t ∈ S then (2 * Real.pi * Complex.I : ℂ) * signVal t else 0)
          (by intro t ht hts; simp [hts])
        simpa only [Finset.sum_ite_mem, Finset.inter_self] using hh.symm
  rw [hend, sub_self, zero_add, hsum] at heq
  rw [IndexOperationsHomotopy.path_index_eq_integral γ a ha,
    PiecewiseC1Path.integral, C1Partition.integral_eq_intervalIntegral γ.path γ.partition _
      (IndexOperationsHomotopy.reciprocal_continuousOn γ a ha)]
  change (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (∫ t in γ.path.a..γ.path.b, g t) = _
  rw [heq, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]

open Specs.D12Complex.Ch04.IndexComputations (rectangle_traversal half_disk_traversal)

@[fun_prop] theorem ofReal_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n Complex.ofReal :=
  Complex.ofRealCLM.contDiff

private def smoothPath (u v : ℝ) (huv : u ≤ v) (f : ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) : PiecewiseC1Path :=
  ⟨⟨u, v, huv, f, hf.continuous.continuousOn⟩,
    ⟨C1Partition.single _ hf.contDiffOn⟩⟩

open private glue_piecewise from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations

theorem rectangle_boundary_exists :
    Specs.D12Complex.Ch04.IndexComputations.rectangle_boundary_exists_type := by
  intro c η w h _ _ _
  let p₀ := smoothPath 0 1 (by norm_num)
    (fun t => c + ((w * t : ℝ) : ℂ) * η) (by fun_prop)
  let p₁ := smoothPath 1 2 (by norm_num)
    (fun t => c + ((w : ℂ) + ((h * (t - 1) : ℝ) : ℂ) * Complex.I) * η) (by fun_prop)
  let p₂ := smoothPath 2 3 (by norm_num)
    (fun t => c + (((w * (3 - t) : ℝ) : ℂ) + (h : ℂ) * Complex.I) * η) (by fun_prop)
  let p₃ := smoothPath 3 4 (by norm_num)
    (fun t => c + ((h * (4 - t) : ℝ) : ℂ) * Complex.I * η) (by fun_prop)
  obtain ⟨q₁, ha₁, hb₁, h₀, h₁⟩ := glue_piecewise p₀ p₁ rfl (by
    change c + ((w * 1 : ℝ) : ℂ) * η = c + ((w : ℂ) + ((h * (1 - 1) : ℝ) : ℂ) * Complex.I) * η
    simp)
  change q₁.path.a = 0 at ha₁
  change q₁.path.b = 2 at hb₁
  obtain ⟨q₂, ha₂, hb₂, hq₁, h₂⟩ := glue_piecewise q₁ p₂ hb₁ (by
    change q₁ q₁.path.b = p₂ p₂.path.a
    rw [hb₁, h₁ (by change (2 : ℝ) ∈ Icc 1 2; norm_num)]
    change c + ((w : ℂ) + ((h * (2 - 1) : ℝ) : ℂ) * Complex.I) * η =
      c + (((w * (3 - 2) : ℝ) : ℂ) + (h : ℂ) * Complex.I) * η
    norm_num)
  change q₂.path.b = 3 at hb₂
  obtain ⟨q₃, ha₃, hb₃, hq₂, h₃⟩ := glue_piecewise q₂ p₃ hb₂ (by
    change q₂ q₂.path.b = p₃ p₃.path.a
    rw [hb₂, h₂ (by change (3 : ℝ) ∈ Icc 2 3; norm_num)]
    change c + (((w * (3 - 3) : ℝ) : ℂ) + (h : ℂ) * Complex.I) * η =
      c + ((h * (4 - 3) : ℝ) : ℂ) * Complex.I * η
    norm_num)
  refine ⟨q₃, ha₃.trans (ha₂.trans ha₁), hb₃, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [hq₂ (by simpa only [ha₂, ha₁, hb₂] using
                  (show t ∈ Icc (0 : ℝ) 3 from ⟨ht.1, ht.2.trans (by norm_num)⟩)),
        hq₁ (by simpa only [ha₁, hb₁] using
                  (show t ∈ Icc (0 : ℝ) 2 from ⟨ht.1, ht.2.trans (by norm_num)⟩)), h₀ ht]
    rfl
  · intro t ht
    rw [hq₂ (by simpa only [ha₂, ha₁, hb₂] using
                  (show t ∈ Icc (0 : ℝ) 3 from ⟨(by norm_num : (0 : ℝ) ≤ 1).trans ht.1,
                    ht.2.trans (by norm_num)⟩)),
        hq₁ (by simpa only [ha₁, hb₁] using
                  (show t ∈ Icc (0 : ℝ) 2 from ⟨(by norm_num : (0 : ℝ) ≤ 1).trans ht.1, ht.2⟩)), h₁ ht]
    rfl
  · intro t ht
    rw [hq₂ (by simpa only [ha₂, ha₁, hb₂] using
                  (show t ∈ Icc (0 : ℝ) 3 from ⟨(by norm_num : (0 : ℝ) ≤ 2).trans ht.1, ht.2⟩)), h₂ ht]
    rfl
  · exact h₃

/-- The specified four sides furnish a partition without an artificial corner
at any point in the interior of a side. -/
def rectangle_partition (γ : PiecewiseC1Path) {c η : ℂ} {w h : ℝ}
    (ht : rectangle_traversal γ c η w h) : C1Partition γ.path := by
  let h₀ := ht.2.2.1
  let h₁ := ht.2.2.2.1
  let h₂ := ht.2.2.2.2.1
  let h₃ := ht.2.2.2.2.2
  refine { count := 4
           node := fun i => (i.val : ℝ)
           strictMono := by
             intro i j hij
             change (i.val : ℝ) < (j.val : ℝ)
             exact_mod_cast (show i.val < j.val from hij)
           first := by norm_num; exact ht.1.symm
           last := by norm_num; exact ht.2.1.symm
           smooth := ?_ }
  intro i
  fin_cases i <;> norm_num only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat]
  · exact (by fun_prop : ContDiff ℝ 1 (fun t => c + ((w * t : ℝ) : ℂ) * η)).contDiffOn.congr h₀
  · exact (by fun_prop : ContDiff ℝ 1 (fun t =>
      c + ((w : ℂ) + ((h * (t - 1) : ℝ) : ℂ) * Complex.I) * η)).contDiffOn.congr h₁
  · exact (by fun_prop : ContDiff ℝ 1 (fun t =>
      c + (((w * (3 - t) : ℝ) : ℂ) + (h : ℂ) * Complex.I) * η)).contDiffOn.congr h₂
  · exact (by fun_prop : ContDiff ℝ 1 (fun t =>
      c + ((h * (4 - t) : ℝ) : ℂ) * Complex.I * η)).contDiffOn.congr h₃

/-- Normalize the four side formulas by the given nonzero rotation. -/
theorem rectangle_coordinates (γ : PiecewiseC1Path) {c η : ℂ} {w h : ℝ}
    (hη : η ≠ 0) (ht : rectangle_traversal γ c η w h) :
    (∀ t ∈ Icc (0 : ℝ) 1, (γ t - c) / η = (w * t : ℝ)) ∧
    (∀ t ∈ Icc (1 : ℝ) 2, (γ t - c) / η = (w : ℂ) + (h * (t - 1) : ℝ) * Complex.I) ∧
    (∀ t ∈ Icc (2 : ℝ) 3, (γ t - c) / η = (w * (3 - t) : ℝ) + (h : ℂ) * Complex.I) ∧
    (∀ t ∈ Icc (3 : ℝ) 4, (γ t - c) / η = (h * (4 - t) : ℝ) * Complex.I) := by
  rcases ht with ⟨_, _, h₀, h₁, h₂, h₃⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht; rw [h₀ t ht]; simp [hη]
  · intro t ht; rw [h₁ t ht]; simp [hη]
  · intro t ht; rw [h₂ t ht]; simp [hη]
  · intro t ht; rw [h₃ t ht]; simp only [add_sub_cancel_left]; exact mul_div_cancel_right₀ _ hη

/-- Affine coordinates preserve real convex combinations whose weights sum to one. -/
theorem affine_coordinate_combination (c η z z' : ℂ) (α β : ℝ) (hs : α + β = 1) :
    (α • z + β • z' - c) / η = α • ((z - c) / η) + β • ((z' - c) / η) := by
  have he : α • c + β • c = c := by rw [← add_smul, hs, one_smul]
  calc
    (α • z + β • z' - c) / η = (α • (z - c) + β • (z' - c)) / η := by
      congr 1
      simp only [smul_sub]
      calc
        α • z + β • z' - c = α • z + β • z' - (α • c + β • c) := by rw [he]
        _ = _ := by abel
    _ = _ := by simp only [add_div, smul_div_assoc]

/-- The explicit closed coordinate rectangle is convex. -/
theorem convex_coordinate_rectangle (c η : ℂ) (w h : ℝ) :
    Convex ℝ {z : ℂ | 0 ≤ ((z - c) / η).re ∧ ((z - c) / η).re ≤ w ∧
      0 ≤ ((z - c) / η).im ∧ ((z - c) / η).im ≤ h} := by
  intro z hz z' hz' α β hα hβ hs
  rw [mem_ofPred_eq, affine_coordinate_combination c η z z' α β hs]
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  refine ⟨add_nonneg (mul_nonneg hα hz.1) (mul_nonneg hβ hz'.1), ?_,
    add_nonneg (mul_nonneg hα hz.2.2.1) (mul_nonneg hβ hz'.2.2.1), ?_⟩
  · calc α * ((z - c) / η).re + β * ((z' - c) / η).re ≤ α * w + β * w :=
          add_le_add (mul_le_mul_of_nonneg_left hz.2.1 hα) (mul_le_mul_of_nonneg_left hz'.2.1 hβ)
         _ = w := by rw [← add_mul, hs, one_mul]
  · calc α * ((z - c) / η).im + β * ((z' - c) / η).im ≤ α * h + β * h :=
          add_le_add (mul_le_mul_of_nonneg_left hz.2.2.2 hα) (mul_le_mul_of_nonneg_left hz'.2.2.2 hβ)
         _ = h := by rw [← add_mul, hs, one_mul]

/-- Trace containment, with the four explicit boundary alternatives. -/
theorem rectangle_trace_coordinates (γ : PiecewiseC1Path) {c η : ℂ} {w h : ℝ}
    (hη : η ≠ 0) (hw : 0 < w) (hh : 0 < h) (ht : rectangle_traversal γ c η w h) :
    ∀ z ∈ γ.trace,
      (0 ≤ ((z - c) / η).re ∧ ((z - c) / η).re ≤ w ∧
       0 ≤ ((z - c) / η).im ∧ ((z - c) / η).im ≤ h) ∧
      (((z - c) / η).re = 0 ∨ ((z - c) / η).re = w ∨
       ((z - c) / η).im = 0 ∨ ((z - c) / η).im = h) := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := rectangle_coordinates γ hη ht
  rintro z ⟨t, hti, rfl⟩
  rw [ht.1, ht.2.1] at hti
  by_cases ht₀ : t ≤ 1
  · rw [h₀ t ⟨hti.1, ht₀⟩]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨⟨mul_nonneg hw.le hti.1, by nlinarith, le_rfl, hh.le⟩, Or.inr (Or.inr (Or.inl trivial))⟩
  by_cases ht₁ : t ≤ 2
  · rw [h₁ t ⟨(lt_of_not_ge ht₀).le, ht₁⟩]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_I_re, Complex.mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, neg_zero, add_zero, zero_add]
    exact ⟨⟨hw.le, le_rfl, by nlinarith, by nlinarith⟩, Or.inr (Or.inl trivial)⟩
  by_cases ht₂ : t ≤ 3
  · rw [h₂ t ⟨(lt_of_not_ge ht₁).le, ht₂⟩]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_I_re, Complex.mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, neg_zero, add_zero, zero_add]
    exact ⟨⟨by nlinarith, by nlinarith, hh.le, le_rfl⟩, Or.inr (Or.inr (Or.inr trivial))⟩
  · rw [h₃ t ⟨(lt_of_not_ge ht₂).le, hti.2⟩]
    simp only [Complex.mul_I_re, Complex.mul_I_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero]
    exact ⟨⟨le_rfl, hw.le, mul_nonneg hh.le (sub_nonneg.mpr hti.2), by nlinarith [lt_of_not_ge ht₂]⟩, Or.inl trivial⟩

theorem rectangle_closed (γ : PiecewiseC1Path) {c η : ℂ} {w h : ℝ}
    (ht : rectangle_traversal γ c η w h) : γ.IsClosed := by
  change γ γ.path.b = γ γ.path.a
  rw [ht.1, ht.2.1, ht.2.2.1 0 (by norm_num), ht.2.2.2.2.2 4 (by norm_num)]
  norm_num

theorem rectangle_index_exterior (γ : PiecewiseC1Path) (c η a : ℂ) (w h : ℝ)
    (hunit : ‖η‖ = 1) (hw : 0 < w) (hh : 0 < h) (ht : rectangle_traversal γ c η w h)
    (ha : ¬ (0 ≤ ((a - c) / η).re ∧ ((a - c) / η).re ≤ w ∧
      0 ≤ ((a - c) / η).im ∧ ((a - c) / η).im ≤ h)) : γ.index a = 0 := by
  have hη : η ≠ 0 := by intro h; simp [h] at hunit
  exact closed_path_index_zero_of_convex γ _ a (rectangle_closed γ ht)
    (convex_coordinate_rectangle c η w h)
    (fun z hz => (rectangle_trace_coordinates γ hη hw hh ht z hz).1) ha

/-- A horizontal ray from an interior point meets exactly the upward right side. -/
theorem rectangle_index_interior (γ : PiecewiseC1Path) (c η a : ℂ) (w h : ℝ)
    (hunit : ‖η‖ = 1) (hw : 0 < w) (hh : 0 < h) (ht : rectangle_traversal γ c η w h)
    (ha : 0 < ((a - c) / η).re ∧ ((a - c) / η).re < w ∧
      0 < ((a - c) / η).im ∧ ((a - c) / η).im < h) : γ.index a = 1 := by
  classical
  have hη : η ≠ 0 := by intro h; simp [h] at hunit
  let b := (a - c) / η
  let t₀ : ℝ := 1 + b.im / h
  have ht₀ : t₀ ∈ Ioo (1 : ℝ) 2 := by
    dsimp [t₀]
    constructor
    · linarith [div_pos ha.2.2.1 hh]
    · have hd : b.im / h < 1 := (div_lt_one hh).mpr ha.2.2.2
      linarith
  have hnotrace : a ∉ γ.trace := by
    intro htr
    rcases (rectangle_trace_coordinates γ hη hw hh ht a htr).2 with h | h | h | h <;> linarith [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2]
  have hsub (z : ℂ) : (z - a) / η = (z - c) / η - b := by dsimp [b]; ring
  obtain ⟨h₀, h₁, h₂, h₃⟩ := rectangle_coordinates γ hη ht
  have hstart : ¬ ∃ s : ℝ, 0 ≤ s ∧ γ γ.path.a - a = (s : ℂ) * η := by
    rintro ⟨s, _, he⟩
    have he' := congrArg (fun z : ℂ => (z / η).im) he
    rw [ht.1, hsub, h₀ 0 (by norm_num)] at he'
    simp [hη] at he'
    linarith [ha.2.2.1]
  have hmeet : ∀ t : ℝ, t ∈ ({t₀} : Finset ℝ) ↔ t ∈ Ioo γ.path.a γ.path.b ∧
      ∃ s : ℝ, 0 < s ∧ γ t - a = (s : ℂ) * η := by
    intro t
    simp only [Finset.mem_singleton]
    constructor
    · rintro rfl
      refine ⟨by rw [ht.1, ht.2.1]; constructor <;> linarith [ht₀.1, ht₀.2],
        w - b.re, sub_pos.mpr ha.2.1, ?_⟩
      apply (div_eq_iff hη).mp
      rw [hsub, h₁ t₀ ⟨ht₀.1.le, ht₀.2.le⟩]
      apply Complex.ext <;> simp [t₀, Complex.sub_re, Complex.sub_im]
      field_simp
      ring
    · rintro ⟨hti, s, hs, he⟩
      rw [ht.1, ht.2.1] at hti
      have he' : (γ t - c) / η - b = (s : ℂ) := by
        rw [← hsub, he, mul_div_cancel_right₀ _ hη]
      have hre := congrArg Complex.re he'
      have him := congrArg Complex.im he'
      by_cases ht₁ : t ≤ 1
      · rw [h₀ t ⟨hti.1.le, ht₁⟩] at him
        simp only [Complex.sub_im, Complex.ofReal_im, zero_sub] at him
        linarith [ha.2.2.1]
      by_cases ht₂ : t ≤ 2
      · rw [h₁ t ⟨(lt_of_not_ge ht₁).le, ht₂⟩] at him
        simp only [Complex.sub_im, Complex.add_im, Complex.mul_I_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_add] at him
        dsimp [t₀]
        have he : t - 1 = b.im / h := (eq_div_iff hh.ne').mpr (by linarith)
        linarith
      by_cases ht₃ : t ≤ 3
      · rw [h₂ t ⟨(lt_of_not_ge ht₂).le, ht₃⟩] at him
        simp only [Complex.sub_im, Complex.add_im, Complex.mul_I_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_add] at him
        linarith [ha.2.2.2]
      · rw [h₃ t ⟨(lt_of_not_ge ht₃).le, hti.2.le⟩] at hre
        simp only [Complex.sub_re, Complex.mul_I_re, Complex.ofReal_re, Complex.ofReal_im,
          neg_zero, zero_sub] at hre
        linarith [ha.1]
  have hderiv : deriv γ t₀ = (h : ℂ) * Complex.I * η := by
    have hd : HasDerivAt (fun t : ℝ =>
        c + ((w : ℂ) + ((h * (t - 1) : ℝ) : ℂ) * Complex.I) * η)
        ((h : ℂ) * Complex.I * η) t₀ := by
      have hd : HasDerivAt (fun t : ℝ => ((h * (t - 1) : ℝ) : ℂ)) (h : ℂ) t₀ := by
        simpa using (((hasDerivAt_id t₀).sub_const 1).const_mul h).ofReal_comp
      convert (((hd.mul_const Complex.I).const_add (w : ℂ)).mul_const η).const_add c using 1
    apply HasDerivAt.deriv
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht₀.1 ht₀.2] with t hti
    exact ht.2.2.2.1 t ⟨hti.1.le, hti.2.le⟩
  have hsign : 0 < (deriv γ t₀ / η).im := by rw [hderiv, mul_div_cancel_right₀ _ hη]; simpa using hh
  have hcorners : ∃ P : C1Partition γ.path, ∀ t ∈ ({t₀} : Finset ℝ),
      ∃ i : Fin P.count, t ∈ Ioo (P.node i.castSucc) (P.node i.succ) := by
    refine ⟨rectangle_partition γ ht, ?_⟩
    intro t hti
    obtain rfl := Finset.mem_singleton.mp hti
    refine ⟨(1 : Fin 4), ?_⟩
    simpa [rectangle_partition] using ht₀
  have hc := path_index_signed_ray_crossings γ a η {t₀} (rectangle_closed γ ht)
    hnotrace hunit hstart hmeet hcorners (by
      intro t hti; obtain rfl := Finset.mem_singleton.mp hti; exact hsign.ne')
  simpa only [Finset.sum_singleton, ite_eq_left hsign] using hc

theorem rectangle_index : Specs.D12Complex.Ch04.IndexComputations.rectangle_index_type := by
  intro γ c η a w h hunit hw hh ht
  exact ⟨rectangle_index_interior γ c η a w h hunit hw hh ht,
    rectangle_index_exterior γ c η a w h hunit hw hh ht⟩

theorem half_disk_boundary_exists :
    Specs.D12Complex.Ch04.IndexComputations.half_disk_boundary_exists_type := by
  intro c η r _ _
  let p₀ := smoothPath 0 1 (by norm_num)
    (fun t => c + ((r * (2 * t - 1) : ℝ) : ℂ) * η) (by fun_prop)
  let p₁ := smoothPath 1 2 (by norm_num)
    (fun t => c + (r : ℂ) * Complex.exp (((Real.pi * (t - 1) : ℝ) : ℂ) * Complex.I) * η)
    (by fun_prop)
  obtain ⟨γ, ha, hb, h₀, h₁⟩ := glue_piecewise p₀ p₁ rfl (by
    change c + ((r * (2 * 1 - 1) : ℝ) : ℂ) * η =
      c + (r : ℂ) * Complex.exp (((Real.pi * (1 - 1) : ℝ) : ℂ) * Complex.I) * η
    norm_num)
  exact ⟨γ, ha, hb, h₀, h₁⟩

def half_disk_partition (γ : PiecewiseC1Path) {c η : ℂ} {r : ℝ}
    (ht : half_disk_traversal γ c η r) : C1Partition γ.path := by
  refine { count := 2
           node := fun i => (i.val : ℝ)
           strictMono := by
             intro i j hij
             change (i.val : ℝ) < (j.val : ℝ)
             exact_mod_cast (show i.val < j.val from hij)
           first := by norm_num; exact ht.1.symm
           last := by norm_num; exact ht.2.1.symm
           smooth := ?_ }
  intro i
  fin_cases i <;> norm_num only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat]
  · exact (by fun_prop : ContDiff ℝ 1 (fun t =>
      c + ((r * (2 * t - 1) : ℝ) : ℂ) * η)).contDiffOn.congr ht.2.2.1
  · exact (by fun_prop : ContDiff ℝ 1 (fun t => c + (r : ℂ) *
      Complex.exp (((Real.pi * (t - 1) : ℝ) : ℂ) * Complex.I) * η)).contDiffOn.congr ht.2.2.2

theorem half_disk_closed (γ : PiecewiseC1Path) {c η : ℂ} {r : ℝ}
    (ht : half_disk_traversal γ c η r) : γ.IsClosed := by
  change γ γ.path.b = γ γ.path.a
  rw [ht.1, ht.2.1, ht.2.2.1 0 (by norm_num), ht.2.2.2 2 (by norm_num)]
  norm_num only [mul_zero, sub_zero, mul_one, sub_self, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_zero, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_ofNat,
    mul_neg, mul_one, neg_mul, zero_mul]
  rw [Complex.exp_pi_mul_I]
  ring

/-- Containment and boundary alternatives for the concrete upper half-disk. -/
theorem half_disk_trace_coordinates (γ : PiecewiseC1Path) {c η : ℂ} {r : ℝ}
    (hunit : ‖η‖ = 1) (hr : 0 < r) (ht : half_disk_traversal γ c η r) :
    ∀ z ∈ γ.trace, (‖z - c‖ ≤ r ∧ 0 ≤ ((z - c) / η).im) ∧
      (‖z - c‖ = r ∨ ((z - c) / η).im = 0) := by
  have hη : η ≠ 0 := by intro h; simp [h] at hunit
  rintro z ⟨t, hti, rfl⟩
  rw [ht.1, ht.2.1] at hti
  by_cases hlow : t ≤ 1
  · rw [ht.2.2.1 t ⟨hti.1, hlow⟩, add_sub_cancel_left, mul_div_cancel_right₀ _ hη]
    simp only [norm_mul, hunit, mul_one, Complex.norm_real, Complex.ofReal_im]
    have habs : |r * (2 * t - 1)| ≤ r := abs_le.mpr ⟨by nlinarith [hti.1], by nlinarith⟩
    exact ⟨⟨by simpa only [Real.norm_eq_abs, ← abs_mul] using habs, le_rfl⟩, Or.inr trivial⟩
  · rw [ht.2.2.2 t ⟨(lt_of_not_ge hlow).le, hti.2⟩, add_sub_cancel_left,
      mul_div_cancel_right₀ _ hη]
    have hsin : 0 ≤ Real.sin (Real.pi * (t - 1)) := Real.sin_nonneg_of_mem_Icc
      ⟨mul_nonneg Real.pi_pos.le (by linarith), by nlinarith [Real.pi_pos, hti.2]⟩
    have hn : ‖(r : ℂ) * Complex.exp (((Real.pi * (t - 1) : ℝ) : ℂ) * Complex.I) * η‖ = r := by
      simp [Complex.norm_exp, hunit, abs_of_pos hr]
    have him : 0 ≤ ((r : ℂ) * Complex.exp (((Real.pi * (t - 1) : ℝ) : ℂ) * Complex.I)).im := by
      simpa [Complex.mul_im, Complex.exp_im] using mul_nonneg hr.le hsin
    exact ⟨⟨hn.le, him⟩, Or.inl hn⟩

theorem half_disk_index_exterior (γ : PiecewiseC1Path) (c η a : ℂ) (r : ℝ)
    (hunit : ‖η‖ = 1) (hr : 0 < r) (ht : half_disk_traversal γ c η r)
    (ha : r < ‖a - c‖ ∨ ((a - c) / η).im < 0) : γ.index a = 0 := by
  let K : Set ℂ := closedBall c r ∩ {z | 0 ≤ ((z - c) / η).im}
  have hK : Convex ℝ K := by
    apply (convex_closedBall c r).inter
    intro z hz z' hz' α β hα hβ hs
    rw [mem_ofPred_eq, affine_coordinate_combination c η z z' α β hs]
    simpa only [Complex.add_im, Complex.smul_im, smul_eq_mul] using
      add_nonneg (mul_nonneg hα hz) (mul_nonneg hβ hz')
  apply closed_path_index_zero_of_convex γ K a (half_disk_closed γ ht) hK
  · intro z hz
    have hh := (half_disk_trace_coordinates γ hunit hr ht z hz).1
    exact ⟨mem_closedBall_iff_norm.mpr hh.1, hh.2⟩
  · rintro ⟨ha₁, ha₂⟩
    rcases ha with ha | ha
    · exact (not_le_of_gt ha) (mem_closedBall_iff_norm.mp ha₁)
    · exact (not_le_of_gt ha) ha₂

/-- A vertical ray from an interior point meets the upper arc once, with
positive transverse sign. Its time is written using the real inverse cosine. -/
theorem half_disk_index_interior (γ : PiecewiseC1Path) (c η a : ℂ) (r : ℝ)
    (hunit : ‖η‖ = 1) (hr : 0 < r) (ht : half_disk_traversal γ c η r)
    (ha : ‖a - c‖ < r ∧ 0 < ((a - c) / η).im) : γ.index a = 1 := by
  classical
  have hη : η ≠ 0 := by intro h; simp [h] at hunit
  let b : ℂ := (a - c) / η
  let θ : ℝ := Real.arccos (b.re / r)
  let t₀ : ℝ := 1 + θ / Real.pi
  let ζ : ℂ := η * Complex.I
  have hb : ‖b‖ < r := by simpa [b, norm_div, hunit] using ha.1
  have hx : -1 < b.re / r ∧ b.re / r < 1 := by
    have hbr := (Complex.abs_re_le_norm b).trans_lt hb
    have hbr' := abs_lt.mp hbr
    exact ⟨(lt_div_iff₀ hr).mpr (by linarith), (div_lt_one hr).mpr hbr'.2⟩
  have hθpos : 0 < θ := Real.arccos_pos.mpr hx.2
  have hθpi : θ < Real.pi := Real.arccos_lt_pi.mpr hx.1
  have ht₀ : t₀ ∈ Ioo (1 : ℝ) 2 := by
    dsimp [t₀]
    constructor
    · linarith [div_pos hθpos Real.pi_pos]
    · linarith [(div_lt_one Real.pi_pos).mpr hθpi]
  have hangle : Real.pi * (t₀ - 1) = θ := by
    dsimp [t₀]
    field_simp
    ring
  have hcos : r * Real.cos θ = b.re := by
    rw [Real.cos_arccos hx.1.le hx.2.le]
    exact mul_div_cancel₀ _ hr.ne'
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθpos hθpi
  have hheight : b.im < r * Real.sin θ := by
    have hnorm := Complex.sq_norm_sub_sq_re b
    have htrig := Real.sin_sq_add_cos_sq θ
    have hrr : ‖b‖ ^ 2 < r ^ 2 := by nlinarith [norm_nonneg b]
    have hid : (r * Real.sin θ) ^ 2 + (r * Real.cos θ) ^ 2 = r ^ 2 := by
      nlinarith [sq_nonneg r]
    rw [hcos] at hid
    nlinarith [mul_pos hr hsin, ha.2]
  have hζunit : ‖ζ‖ = 1 := by simp [ζ, hunit]
  have hζ : ζ ≠ 0 := mul_ne_zero hη Complex.I_ne_zero
  have hnotrace : a ∉ γ.trace := by
    intro htr
    rcases (half_disk_trace_coordinates γ hunit hr ht a htr).2 with h | h
    · exact ha.1.ne h
    · exact ha.2.ne' h
  have hsub (z : ℂ) : (z - a) / η = (z - c) / η - b := by dsimp [b]; ring
  have hlow (t : ℝ) (hti : t ∈ Icc (0 : ℝ) 1) : (γ t - c) / η = (r * (2 * t - 1) : ℝ) := by
    rw [ht.2.2.1 t hti]; simp only [add_sub_cancel_left, mul_div_cancel_right₀ _ hη]
  have harc (t : ℝ) (hti : t ∈ Icc (1 : ℝ) 2) :
      (γ t - c) / η = (r : ℂ) * Complex.exp (((Real.pi * (t - 1) : ℝ) : ℂ) * Complex.I) := by
    rw [ht.2.2.2 t hti]; simp only [add_sub_cancel_left, mul_div_cancel_right₀ _ hη]
  have hnormalize (t s : ℝ) (he : γ t - a = (s : ℂ) * ζ) :
      (γ t - c) / η - b = (s : ℂ) * Complex.I := by
    rw [← hsub, he]
    dsimp [ζ]
    field_simp
  have hstart : ¬ ∃ s : ℝ, 0 ≤ s ∧ γ γ.path.a - a = (s : ℂ) * ζ := by
    rintro ⟨s, hs, he⟩
    have hh := congrArg Complex.im (hnormalize _ _ he)
    rw [ht.1, hlow 0 (by norm_num)] at hh
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_sub] at hh
    linarith [ha.2]
  have hmeet : ∀ t : ℝ, t ∈ ({t₀} : Finset ℝ) ↔ t ∈ Ioo γ.path.a γ.path.b ∧
      ∃ s : ℝ, 0 < s ∧ γ t - a = (s : ℂ) * ζ := by
    intro t
    simp only [Finset.mem_singleton]
    constructor
    · rintro rfl
      refine ⟨by rw [ht.1, ht.2.1]; constructor <;> linarith [ht₀.1, ht₀.2],
        r * Real.sin θ - b.im, sub_pos.mpr hheight, ?_⟩
      have he : (γ t₀ - a) / η = ((r * Real.sin θ - b.im : ℝ) : ℂ) * Complex.I := by
        rw [hsub, harc t₀ ⟨ht₀.1.le, ht₀.2.le⟩, hangle]
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im, hcos, -Complex.ofReal_sin, -Complex.ofReal_cos]
      have he' := (div_eq_iff hη).mp he
      simpa only [ζ, mul_assoc, mul_comm Complex.I η] using he'
    · rintro ⟨hti, s, hs, he⟩
      rw [ht.1, ht.2.1] at hti
      have he' := hnormalize t s he
      by_cases ht₁ : t ≤ 1
      · have him := congrArg Complex.im he'
        rw [hlow t ⟨hti.1.le, ht₁⟩] at him
        simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_sub] at him
        linarith [ha.2]
      · have hre := congrArg Complex.re he'
        rw [harc t ⟨(lt_of_not_ge ht₁).le, hti.2.le⟩] at hre
        simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.exp_re, Complex.mul_I_im, Real.exp_zero,
          one_mul, zero_mul, sub_zero, Complex.I_re, mul_zero] at hre
        have hcos' : Real.cos (Real.pi * (t - 1)) = b.re / r :=
          (eq_div_iff hr.ne').mpr (by nlinarith)
        have hangle' : θ = Real.pi * (t - 1) := by
          dsimp [θ]
          rw [← hcos', Real.arccos_cos]
          · exact mul_nonneg Real.pi_pos.le (by linarith [lt_of_not_ge ht₁])
          · nlinarith [Real.pi_pos, hti.2]
        dsimp [t₀]
        rw [hangle']
        field_simp
        ring
  have hderiv : deriv γ t₀ = (r : ℂ) *
      (Complex.exp ((θ : ℂ) * Complex.I) * ((Real.pi : ℂ) * Complex.I)) * η := by
    have hdArg : HasDerivAt (fun t : ℝ => (((Real.pi * (t - 1) : ℝ) : ℂ) * Complex.I))
        ((Real.pi : ℂ) * Complex.I) t₀ := by
      simpa using ((((hasDerivAt_id t₀).sub_const 1).const_mul Real.pi).ofReal_comp.mul_const Complex.I)
    have hd := (((hdArg.cexp.const_mul (r : ℂ)).mul_const η).const_add c)
    rw [hangle] at hd
    apply HasDerivAt.deriv
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht₀.1 ht₀.2] with t hti
    exact ht.2.2.2 t ⟨hti.1.le, hti.2.le⟩
  have hsign : 0 < (deriv γ t₀ / ζ).im := by
    have he : deriv γ t₀ / ζ = (r : ℂ) * (Real.pi : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [hderiv]
      dsimp [ζ]
      field_simp
    rw [he]
    simpa [Complex.mul_im, Complex.exp_im] using mul_pos (mul_pos hr Real.pi_pos) hsin
  have hcorners : ∃ P : C1Partition γ.path, ∀ t ∈ ({t₀} : Finset ℝ),
      ∃ i : Fin P.count, t ∈ Ioo (P.node i.castSucc) (P.node i.succ) := by
    refine ⟨half_disk_partition γ ht, ?_⟩
    intro t hti
    obtain rfl := Finset.mem_singleton.mp hti
    refine ⟨(1 : Fin 2), ?_⟩
    simpa [half_disk_partition] using ht₀
  have hc := path_index_signed_ray_crossings γ a ζ {t₀} (half_disk_closed γ ht)
    hnotrace hζunit hstart hmeet hcorners (by
      intro t hti; obtain rfl := Finset.mem_singleton.mp hti; exact hsign.ne')
  simpa only [Finset.sum_singleton, ite_eq_left hsign] using hc

theorem half_disk_index : Specs.D12Complex.Ch04.IndexComputations.half_disk_index_type := by
  intro γ c η a r hunit hr ht
  exact ⟨half_disk_index_interior γ c η a r hunit hr ht,
    half_disk_index_exterior γ c η a r hunit hr ht⟩

end D12Complex.IndexComputations
