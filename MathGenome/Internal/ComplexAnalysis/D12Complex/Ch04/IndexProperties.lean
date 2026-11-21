import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.IndexProperties
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.WindingIndex
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PiecewiseC1Length
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Sequences
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace D12Complex.IndexProperties

/-- Exponentiating the logarithmic integral on one smooth interval gives
the ratio of endpoint values. This proof does not select an argument. -/
theorem exp_integral_log_derivative {f : ℝ → ℂ} {u v : ℝ} (huv : u < v)
    (hf : ContDiffOn ℝ 1 f (Icc u v)) (hne : ∀ t ∈ Icc u v, f t ≠ 0) :
    Complex.exp (∫ t in u..v, (f t)⁻¹ * derivWithin f (Icc u v) t) = f v / f u := by
  let d := derivWithin f (Icc u v)
  let g := fun t => (f t)⁻¹ * d t
  have hd : ContinuousOn d (Icc u v) :=
    ((contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc huv)).mp hf).2
  have hg : ContinuousOn g (Icc u v) := (hf.continuousOn.inv₀ hne).mul hd
  let G : ℝ → ℂ := IccExtend huv.le (fun t : Icc u v => g t)
  have hG : Continuous G := hg.domRestrict.Icc_extend'
  have hGeq : ∀ t ∈ Icc u v, G t = g t := by
    intro t ht
    exact IccExtend_of_mem huv.le _ ht
  let F := fun t => ∫ s in u..t, G s
  have hF : ∀ t, HasDerivAt F (G t) t :=
    fun t => (hG.integral_hasStrictDerivAt u t).hasDerivAt
  let H := fun t => Complex.exp (-F t) * f t
  have hH : DifferentiableOn ℝ H (Icc u v) := by
    intro t ht
    exact (((hF t).neg.cexp.differentiableAt.differentiableWithinAt).mul
      (hf.differentiableOn one_ne_zero t ht))
  have hHz : ∀ t ∈ Icc u v, HasDerivWithinAt H 0 (Icc u v) t := by
    intro t ht
    have hf' := (hf.differentiableOn one_ne_zero t ht).hasDerivWithinAt
    have hh := ((hF t).neg.cexp.hasDerivWithinAt).mul hf'
    convert hh using 1
    rw [hGeq t ht]
    dsimp [g, d]
    field_simp [hne t ht]
    ring
  have hc := constant_of_derivWithin_zero hH
    (fun t ht => (hHz t (Ico_subset_Icc_self ht)).derivWithin (uniqueDiffOn_Icc huv t
      (Ico_subset_Icc_self ht))) v (right_mem_Icc.mpr huv.le)
  have hInt : F v = ∫ t in u..v, (f t)⁻¹ * derivWithin f (Icc u v) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hGeq t (by simpa [uIcc_of_le huv.le] using ht)
  have hEq : Complex.exp (-(F v)) * f v = f u := by
    simpa [H, F] using hc
  apply (eq_div_iff (hne u (left_mem_Icc.mpr huv.le))).mpr
  have hh := congrArg (fun z => Complex.exp (F v) * z) hEq
  rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul] at hh
  rw [← hInt]
  exact hh.symm

/-- Algebraic assembly of endpoint identities, including the empty partition. -/
theorem exp_sum_endpoint : ∀ {n : ℕ} (z : Fin (n + 1) → ℂ) (c : Fin n → ℂ),
    (∀ i, Complex.exp (c i) * z i.castSucc = z i.succ) →
    Complex.exp (∑ i, c i) * z 0 = z (Fin.last n) := by
  intro n
  induction n with
  | zero => intro z c _; simp
  | succ n ih =>
    intro z c h
    have ht := ih (fun i => z i.succ) (fun i => c i.succ) (fun i => by
      simpa only [Fin.succ_castSucc] using h i.succ)
    rw [Fin.sum_univ_succ, Complex.exp_add]
    calc
      Complex.exp (c 0) * Complex.exp (∑ i : Fin n, c i.succ) * z 0 =
          Complex.exp (∑ i : Fin n, c i.succ) * (Complex.exp (c 0) * z 0) := by ring
      _ = Complex.exp (∑ i : Fin n, c i.succ) * z (0 : Fin (n + 1)).succ := by
        rw [← h 0]; rfl
      _ = z (Fin.last (n + 1)) := ht

/-- The exponential of the integral of dz/(z-a), before imposing closedness. -/
theorem path_exp_reciprocal_integral (γ : PiecewiseC1Path) (a : ℂ)
    (ha : a ∉ γ.trace) :
    Complex.exp (γ.integral (fun z => 1 / (z - a))) * (γ γ.path.a - a) =
      γ γ.path.b - a := by
  let P := γ.partition
  have hne (t : ℝ) (ht : t ∈ Icc γ.path.a γ.path.b) : γ t - a ≠ 0 := by
    exact sub_ne_zero.mpr (fun h => ha ⟨t, ht, h⟩)
  have hp (i : Fin P.count) :
      Complex.exp (∫ t in P.node i.castSucc..P.node i.succ,
        1 / (γ t - a) * derivWithin γ (P.pieceSet i) t) *
          (γ (P.node i.castSucc) - a) = γ (P.node i.succ) - a := by
    have hh := exp_integral_log_derivative (P.piece_lt i)
      ((P.smooth i).sub contDiffOn_const)
      (fun t ht => hne t (P.piece_subset i ht))
    simp only [derivWithin_sub_const, ← one_div] at hh
    change Complex.exp (∫ t in P.node i.castSucc..P.node i.succ,
      1 / (γ t - a) * derivWithin γ (Icc (P.node i.castSucc) (P.node i.succ)) t) * _ = _
    rw [hh]
    exact div_mul_cancel₀ _ (hne _ (P.piece_subset i (left_mem_Icc.mpr (P.piece_lt i).le)))
  have hh := exp_sum_endpoint (fun i => γ (P.node i) - a) _ hp
  simpa only [P.first, P.last, P, PiecewiseC1Path.integral, C1Partition.integral] using hh

theorem closed_path_integral_integer (γ : PiecewiseC1Path) (hclosed : γ.IsClosed)
    (a : ℂ) (ha : a ∉ γ.trace) :
    ∃ n : ℤ, γ.integral (fun z => 1 / (z - a)) =
      (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  apply Complex.exp_eq_one_iff.mp
  have hh := path_exp_reciprocal_integral γ a ha
  have he : γ γ.path.b = γ γ.path.a := hclosed
  rw [he] at hh
  have hne : γ γ.path.a - a ≠ 0 :=
    sub_ne_zero.mpr (fun h => ha ⟨γ.path.a, left_mem_Icc.mpr γ.path.ordered, h⟩)
  exact (mul_right_cancel₀ hne (hh.trans (one_mul _).symm))

theorem cycle_index_integer :
    Specs.D12Complex.Ch04.IndexProperties.cycle_index_integer_type := by
  intro Γ a ha
  have hp : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hγ (γ : PiecewiseC1Path) (hγ : γ ∈ Γ.chain.support) :
      ∃ n : ℤ, γ.integral (fun z => 1 / (z - a)) =
        (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) :=
    closed_path_integral_integer γ (Γ.property γ hγ) a
      (fun hz => ha ⟨γ, hγ, hz⟩)
  classical
  choose n hn using hγ
  refine ⟨∑ γ ∈ Γ.chain.support, Γ.chain γ * (if h : γ ∈ Γ.chain.support then n γ h else 0), ?_⟩
  rw [Γ.index_eq_integral a ha]
  unfold IntegralCycle.integral IntegralChain.integral Finsupp.sum
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro γ hγ
  rw [hn γ hγ, dite_eq_left hγ]
  field_simp

/-- The reciprocal kernels converge uniformly on any compact set avoiding
the limiting pole. The parameter is allowed to approach from any direction. -/
theorem reciprocal_tendstoUniformlyOn {K : Set ℂ} (hK : IsCompact K)
    {a : ℂ} (ha : a ∉ K) :
    TendstoUniformlyOn (fun b z : ℂ => 1 / (z - b)) (fun z => 1 / (z - a)) (𝓝 a) K := by
  have hc : ContinuousOn (fun p : ℂ × ℂ => 1 / (p.2 - p.1)) (Kᶜ ×ˢ K) := by
    apply continuousOn_const.div (continuous_snd.sub continuous_fst).continuousOn
    intro p hp
    exact sub_ne_zero.mpr (fun h => hp.1 (h ▸ hp.2))
  intro U hU
  obtain ⟨V, hV, hUV⟩ := hK.mem_uniformity_of_prod
    (f := fun b z : ℂ => 1 / (z - b)) (s := Kᶜ) (q := a)
    hc ha (symmetrize_mem_uniformity hU)
  rw [nhdsWithin_eq_nhds.mpr (hK.isClosed.isOpen_compl.mem_nhds ha)] at hV
  filter_upwards [hV] with b hb z hz
  exact (hUV b hb z hz).2

theorem chain_index_continuousOn (Γ : IntegralChain) : ContinuousOn Γ.index Γ.traceᶜ := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply SeqContinuous.continuous
  intro s a hs
  have hs' : Tendsto (fun n => (s n : ℂ)) atTop (𝓝 (a : ℂ)) :=
    (continuous_subtype_val.tendsto a).comp hs
  have hu := reciprocal_tendstoUniformlyOn (PiecewiseC1Length.chain_trace_compact Γ) a.property
  have hu' : TendstoUniformlyOn (fun n z => 1 / (z - (s n : ℂ)))
      (fun z => 1 / (z - (a : ℂ))) atTop Γ.trace := fun U hU => hs'.eventually (hu U hU)
  have hi := PiecewiseC1Length.chain_integral_tendsto_uniform Γ _ _
    (fun n => Γ.reciprocal_continuousOn_trace (s n) (s n).property) hu'
  change Tendsto (fun n => Γ.index (s n)) atTop (𝓝 (Γ.index a))
  have heq (b : {b : ℂ // b ∉ Γ.trace}) := Γ.index_eq_integral b b.property
  simp_rw [heq]
  exact tendsto_const_nhds.mul hi

theorem cycle_index_continuousOn :
    Specs.D12Complex.Ch04.IndexProperties.cycle_index_continuousOn_type := by
  intro Γ
  exact chain_index_continuousOn Γ.chain

theorem integer_eq_of_norm_sub_lt_one {z w : ℂ} (hz : ∃ m : ℤ, z = (m : ℂ))
    (hw : ∃ n : ℤ, w = (n : ℂ)) (h : ‖z - w‖ < 1) : z = w := by
  obtain ⟨m, rfl⟩ := hz
  obtain ⟨n, rfl⟩ := hw
  rw [← Int.cast_sub, Complex.norm_intCast, ← Int.cast_abs] at h
  have hi : |m - n| < 1 := by exact_mod_cast h
  have he : m = n := by have := abs_lt.mp hi; omega
  rw [he]

theorem cycle_index_locally_constant :
    Specs.D12Complex.Ch04.IndexProperties.cycle_index_locally_constant_type := by
  intro Γ a ha
  have hopen : IsOpen Γ.traceᶜ := (PiecewiseC1Length.chain_trace_compact Γ.chain).isClosed.isOpen_compl
  have hc : ContinuousAt Γ.index a := (cycle_index_continuousOn Γ).continuousAt (hopen.mem_nhds ha)
  have hdist : ∀ᶠ b in 𝓝 a, ‖Γ.index b - Γ.index a‖ < 1 :=
    by simpa only [Metric.mem_ball, dist_eq_norm] using
      hc.eventually (Metric.ball_mem_nhds _ zero_lt_one)
  filter_upwards [hopen.mem_nhds ha, hdist] with b hb hdist
  exact ⟨hb, integer_eq_of_norm_sub_lt_one (cycle_index_integer Γ b hb)
    (cycle_index_integer Γ a ha) hdist⟩

/-- The length bound for the normalized integral, with any positive uniform
lower bound on the distance from the pole to the active trace. -/
theorem chain_index_norm_le (Γ : IntegralChain) (a : ℂ) (ha : a ∉ Γ.trace)
    {δ : ℝ} (hδ : 0 < δ) (hd : ∀ z ∈ Γ.trace, δ ≤ ‖z - a‖) :
    ‖Γ.index a‖ ≤ ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ * Γ.lengthBound / δ := by
  rw [Γ.index_eq_integral a ha, norm_mul]
  have hi := PiecewiseC1Length.chain_norm_integral_le_mul_bound Γ (fun z => 1 / (z - a))
    (Γ.reciprocal_continuousOn_trace a ha) (M := 1 / δ) (fun z hz => by
      rw [norm_div, norm_one]
      exact one_div_le_one_div_of_le hδ (hd z hz))
  apply (mul_le_mul_of_nonneg_left hi (norm_nonneg _)).trans_eq
  ring

theorem chain_lengthBound_nonneg (Γ : IntegralChain) : 0 ≤ Γ.lengthBound := by
  unfold IntegralChain.lengthBound
  exact Finset.sum_nonneg (fun γ _ => mul_nonneg (abs_nonneg _)
    (PiecewiseC1Length.length_nonneg γ))

theorem cycle_index_zero_outside_ball (Γ : IntegralCycle) :
    ∃ R : ℝ, ∀ a : ℂ, R < ‖a‖ → Γ.index a = 0 := by
  obtain ⟨R, hR⟩ := (PiecewiseC1Length.chain_trace_compact Γ.chain).isBounded.exists_norm_le
  let C : ℝ := ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖
  let L : ℝ := Γ.chain.lengthBound
  have hCL : 0 ≤ C * L := mul_nonneg (norm_nonneg _) (chain_lengthBound_nonneg _)
  have hδ : 0 < C * L + 1 := by positivity
  refine ⟨R + (C * L + 1), fun a ha => ?_⟩
  have hat : a ∉ Γ.trace := by
    intro hat
    have := hR a hat
    linarith
  have hd : ∀ z ∈ Γ.chain.trace, C * L + 1 ≤ ‖z - a‖ := by
    intro z hz
    have := hR z hz
    have hn := norm_sub_norm_le a z
    rw [norm_sub_rev] at hn
    linarith
  have hb := chain_index_norm_le Γ.chain a hat hδ hd
  have hsmall : ‖Γ.index a‖ < 1 := hb.trans_lt (by
    change C * L / (C * L + 1) < 1
    exact (div_lt_one hδ).mpr (lt_add_one _))
  exact integer_eq_of_norm_sub_lt_one (cycle_index_integer Γ a hat) ⟨0, by simp⟩
    (by simpa only [sub_zero] using hsmall)

theorem cycle_index_bounded_support :
    Specs.D12Complex.Ch04.IndexProperties.cycle_index_bounded_support_type := by
  intro Γ
  obtain ⟨R, hR⟩ := cycle_index_zero_outside_ball Γ
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨R, fun a ha => le_of_not_gt (fun h => ?_)⟩
  exact ha (hR a h)

/-- Constancy holds on every complementary connected component. -/
theorem cycle_index_constant_on_component (Γ : IntegralCycle) (a : ℂ)
    (ha : a ∉ Γ.trace) {b : ℂ} (hb : b ∈ connectedComponentIn Γ.traceᶜ a) :
    Γ.index b = Γ.index a := by
  have hsub := connectedComponentIn_subset Γ.traceᶜ a
  have hd : IsDiscrete (Set.range ((↑) : ℤ → ℂ)) :=
    Complex.isClosedEmbedding_intCast.isEmbedding.isInducing.isDiscrete_range
  apply isPreconnected_connectedComponentIn.constant_of_mapsTo hd
    ((cycle_index_continuousOn Γ).mono hsub) _ hb (mem_connectedComponentIn ha)
  intro z hz
  obtain ⟨n, hn⟩ := cycle_index_integer Γ z (hsub hz)
  exact ⟨n, hn.symm⟩

theorem cycle_index_zero_on_unbounded_component :
    Specs.D12Complex.Ch04.IndexProperties.cycle_index_zero_on_unbounded_component_type := by
  intro Γ a ha hUnbounded
  by_contra hne
  apply hUnbounded
  apply (cycle_index_bounded_support Γ).subset
  intro b hb
  change Γ.index b ≠ 0
  rw [cycle_index_constant_on_component Γ a ha hb]
  exact hne

end D12Complex.IndexProperties
