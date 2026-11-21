import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.DivisorSumConstraint
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.DivisorDegree
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.IndexProperties
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.ResidueCycle
import Mathlib.Tactic.FieldSimp
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace D12Complex.DivisorSumConstraint
open TorusSurface EllipticResidueSum WeakGoursat

/-- Expose the canonical independent definition in the implementation interface. -/
abbrev divisorLists : Specs.D12Complex.Ch22.DivisorSumConstraint.DivisorLists_type := DivisorLists

lemma two_pi_I_ne_zero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero

/-- Multiplying the logarithmic derivative by the coordinate weights its residue
by the actual representative, including negative and repeated orders. -/
lemma residue_coordinate_logDeriv {f : ℂ → ℂ} {a : ℂ}
    (hf : MeromorphicAt f a) (ho : meromorphicOrderAt f a ≠ ⊤) :
    Residue.residue (fun z => z * logDeriv f z) a =
      a * ((meromorphicOrderAt f a).untop₀ : ℂ) := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ho
  obtain ⟨h, hh, he⟩ := LogarithmicDerivative.expansion_germ hf hm.symm
  have han : AnalyticAt ℂ (fun z => (m : ℂ) + z * h z) a :=
    analyticAt_const.add (analyticAt_id.mul hh)
  have he' := eventually_nhdsWithin_iff.mp he
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (han.eventually_analyticAt.and he')
  have hres := LogarithmicDerivative.residue_of_expansion hr
    (show HolomorphicOn (Metric.ball a r) (fun z => (m : ℂ) + z * h z) from
      ⟨Metric.isOpen_ball, fun z hz => (hball (Metric.mem_ball.mp hz)).1.differentiableAt⟩)
    (show ∀ z ∈ puncturedDisk a r,
      z * logDeriv f z = (a * (m : ℂ)) / (z - a) + ((m : ℂ) + z * h z) from by
      intro z hz
      have hza := sub_ne_zero.mp (norm_pos_iff.mp hz.1)
      rw [(hball (by simpa only [dist_eq_norm] using hz.2)).2 hza]
      field_simp
      ring)
  simpa [← hm] using hres

/-- Periodic side pairing with the coordinate weight. The sign agrees with the
positive bottom/right/top/left traversal in the paper. -/
lemma segment_translate_weighted {ω₁ ω₂ : ℂ} {h : ℂ → ℂ}
    (hp : Periodic ω₁ ω₂ h) (a b l : ℂ) (hl : l ∈ lattice ω₁ ω₂)
    (hc : ContinuousOn h (segmentPath a b).trace)
    (hcl : ContinuousOn h (segmentPath (a + l) (b + l)).trace) :
    (segmentPath (a + l) (b + l)).integral (fun z => z * h z) =
      (segmentPath a b).integral (fun z => z * h z) +
        l * (segmentPath a b).integral h := by
  rw [segment_integral_formula _ _ (fun z => z * h z) (continuousOn_id.mul hcl),
    segment_integral_formula _ _ (fun z => z * h z) (continuousOn_id.mul hc),
    segment_integral_formula _ _ _ hc]
  have hi : IntervalIntegrable (fun t : ℝ =>
      (a + t • (b - a)) * h (a + t • (b - a)) * (b - a)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact ((continuousOn_const.add (continuousOn_id.smul continuousOn_const)).mul
      (hc.comp (by fun_prop) (fun t ht => ⟨t, ht, rfl⟩))).mul continuousOn_const
  have hj : IntervalIntegrable (fun t : ℝ =>
      h (a + t • (b - a)) * (b - a)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact (hc.comp (by fun_prop) (fun t ht => ⟨t, ht, rfl⟩)).mul continuousOn_const
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hi (hj.const_mul l)]
  apply intervalIntegral.integral_congr
  intro t _
  have he : a + l + t • (b - a) = (a + t • (b - a)) + l := by abel
  simp only [add_sub_add_right_eq_sub, he, hp _ l hl]
  ring

/-- Opposite sides of a positive parallelogram give minus the second period
on the bottom integral and plus the first period on the upward left integral. -/
lemma parallelogram_weighted_integral {ω₁ ω₂ : ℂ} {h : ℂ → ℂ}
    (hp : Periodic ω₁ ω₂ h) (a : ℂ)
    (hbottom : ContinuousOn h (segmentPath a (a + ω₁)).trace)
    (hright : ContinuousOn h (segmentPath (a + ω₁) (a + ω₁ + ω₂)).trace)
    (htop : ContinuousOn h (segmentPath (a + ω₁ + ω₂) (a + ω₂)).trace)
    (hleft : ContinuousOn h (segmentPath (a + ω₂) a).trace) :
    parallelogramBoundaryIntegral a ω₁ ω₂ (fun z => z * h z) =
      ω₁ * (segmentPath a (a + ω₂)).integral h -
        ω₂ * (segmentPath a (a + ω₁)).integral h := by
  have hω₁ : ω₁ ∈ lattice ω₁ ω₂ := Submodule.subset_span (by simp)
  have hω₂ : ω₂ ∈ lattice ω₁ ω₂ := Submodule.subset_span (by simp)
  have hleft' : ContinuousOn h (segmentPath a (a + ω₂)).trace := by
    rwa [segment_trace_reverse] at hleft
  have htop' : ContinuousOn h (segmentPath (a + ω₂) (a + ω₁ + ω₂)).trace := by
    rwa [segment_trace_reverse] at htop
  have heq : a + ω₂ + ω₁ = a + ω₁ + ω₂ := by abel
  have hr := segment_translate_weighted hp a (a + ω₂) ω₁ hω₁ hleft'
    (by simpa only [heq] using hright)
  rw [heq] at hr
  have ht := segment_translate_weighted hp a (a + ω₁) ω₂ hω₂ hbottom htop'
  have htr := segment_reverse_integral (a + ω₂) (a + ω₁ + ω₂)
    (fun z => z * h z) (continuousOn_id.mul htop')
  have hlr := segment_reverse_integral a (a + ω₂)
    (fun z => z * h z) (continuousOn_id.mul hleft')
  unfold parallelogramBoundaryIntegral
  rw [htr, hlr, hr, ht]
  ring

/-- The scalar finite part is analytic and nonzero off the full divisor. -/
lemma regular_off_divisor {F : ℂ → RiemannSphere} (hF : ScalarMeromorphicOn univ F)
    {a : ℂ} (ha : meromorphicOrderAt (scalarFinitePart F) a = 0) :
    AnalyticAt ℂ (scalarFinitePart F) a ∧ scalarFinitePart F a ≠ 0 := by
  have hreg := (LogarithmicDerivative.order_zero_iff_regular hF (mem_univ a)).mp ha
  refine ⟨scalarMeromorphicOn_finite_analytic univ F hF a (mem_univ a) hreg.2, ?_⟩
  obtain h | ⟨c, hc⟩ := sphere_eq_infty_or_finite (F a)
  · exact (hreg.2 h).elim
  · simp only [scalarFinitePart, hc, finiteCoordinate_sphereFinite]
    exact fun h => hreg.1 (hc.trans (congrArg sphereFinite h))

/-- A nonvanishing analytic function with equal endpoint values has an integer
logarithmic period on a segment. No global logarithm is assumed. -/
lemma segment_logDeriv_integer (f : ℂ → ℂ) (a b : ℂ)
    (han : ∀ z ∈ (segmentPath a b).trace, AnalyticAt ℂ f z)
    (hne : ∀ z ∈ (segmentPath a b).trace, f z ≠ 0) (he : f b = f a) :
    ∃ n : ℤ, (segmentPath a b).integral (logDeriv f) =
      (n : ℂ) * (2 * Real.pi * Complex.I : ℂ) := by
  let γ : ℝ → ℂ := fun t => a + t • (b - a)
  have ht (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ (segmentPath a b).trace :=
    ⟨t, ht, rfl⟩
  have hc : ContDiffOn ℝ 1 (fun t => f (γ t)) (Icc (0 : ℝ) 1) := by
    intro t ht'
    exact (((han _ (ht t ht')).contDiffAt.restrict_scalars ℝ).comp t
      ((contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffAt)).contDiffWithinAt
  have hd (t : ℝ) (ht' : t ∈ Icc (0 : ℝ) 1) :
      derivWithin (fun t => f (γ t)) (Icc (0 : ℝ) 1) t = deriv f (γ t) * (b - a) := by
    simpa only [Function.comp_def, smul_eq_mul, mul_comm] using
      (((han _ (ht t ht')).differentiableAt.hasDerivAt.scomp t
      (segmentPath_hasDerivAt a b t)).hasDerivWithinAt).derivWithin
        (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1) t ht')
  have hcLog : ContinuousOn (logDeriv f) (segmentPath a b).trace := by
    intro z hz
    exact ((han z hz).deriv.continuousAt.div (han z hz).continuousAt (hne z hz)).continuousWithinAt
  have hexp := IndexProperties.exp_integral_log_derivative (by norm_num : (0 : ℝ) < 1)
    hc (fun t ht' => hne _ (ht t ht'))
  have hi : (∫ t in (0 : ℝ)..1,
      (f (γ t))⁻¹ * derivWithin (fun t => f (γ t)) (Icc (0 : ℝ) 1) t) =
      (segmentPath a b).integral (logDeriv f) := by
    rw [segment_integral_formula _ _ _ hcLog]
    apply intervalIntegral.integral_congr
    intro t ht'
    dsimp only
    rw [hd t (by simpa using ht')]
    simp only [γ, logDeriv_apply, div_eq_mul_inv]
    ring
  rw [hi] at hexp
  have hfa : f a ≠ 0 := by simpa [γ] using hne _ (ht 0 (by simp))
  have hx : Complex.exp ((segmentPath a b).integral (logDeriv f)) = 1 := by
    simpa [γ, he, hfa] using hexp
  exact Complex.exp_eq_one_iff.mp hx

open private periodBasis periodBasis_zero periodBasis_one from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.LatticeGeometry

/-- The accepted polygon cycle with its four individual side traces retained. -/
lemma full_parallelogram_cycle {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (a : ℂ) :
    ∃ Γ : IntegralCycle,
      Γ.trace = ((segmentPath a (a + ω₁)).trace ∪
        (segmentPath (a + ω₁) (a + ω₁ + ω₂)).trace) ∪
        ((segmentPath (a + ω₁ + ω₂) (a + ω₂)).trace ∪ (segmentPath (a + ω₂) a).trace) ∧
      Γ.trace ⊆ frontier (Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a ω₁ ω₂) ∧
      ∀ g : ℂ → ℂ, ContinuousOn g Γ.trace →
        Γ.integral g = parallelogramBoundaryIntegral a ω₁ ω₂ g := by
  obtain ⟨Γ, htr, hi⟩ := parallelogram_cycle a ω₁ ω₂
  refine ⟨Γ, htr, ?_, hi⟩
  let b := periodBasis h₁ h₂
  have hb₀ : b 0 = ω₁ := periodBasis_zero h₁ h₂
  have hb₁ : b 1 = ω₂ := periodBasis_one h₁ h₂
  rw [htr, ← hb₀, ← hb₁]
  rintro z ((⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩))
  · change t ∈ Icc (0 : ℝ) 1 at ht
    convert parallelogram_boundary_point b a t 0 ht (by simp) (by simp) using 1
    simp [segmentPath, PiecewiseC1Path.path]
  · change t ∈ Icc (0 : ℝ) 1 at ht
    convert parallelogram_boundary_point b a 1 t (by simp) ht (by simp) using 1
    simp [segmentPath, PiecewiseC1Path.path]
  · change t ∈ Icc (0 : ℝ) 1 at ht
    have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    convert parallelogram_boundary_point b a (1 - t) 1 ht' (by simp) (by simp) using 1
    simp only [segmentPath, PiecewiseC1Path.path, one_smul, sub_smul, smul_sub, smul_add]
    abel
  · change t ∈ Icc (0 : ℝ) 1 at ht
    have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    convert parallelogram_boundary_point b a 0 (1 - t) (by simp) ht' (by simp) using 1
    simp only [segmentPath, PiecewiseC1Path.path, zero_smul, add_zero, sub_smul, one_smul, smul_sub, smul_add]
    abel

/-- The weighted residue calculation for one complete representative set.
This is the analytic step; it assumes neither the divisor sum nor a logarithm. -/
lemma exists_weighted_representatives {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) {F : ℂ → RiemannSphere}
    (hF : ScalarMeromorphicOn univ F) (hp : Periodic ω₁ ω₂ F)
    (hn : ¬ ∃ c : ℂ, ∀ z, F z = sphereFinite c) :
    ∃ s : Finset ℂ,
      CompletePoleRepresentatives ω₁ ω₂ (logDeriv (scalarFinitePart F)) s ∧
      (∑ z ∈ s, z * ((meromorphicOrderAt (scalarFinitePart F) z).untop₀ : ℂ)) ∈
        lattice ω₁ ω₂ := by
  classical
  let f := scalarFinitePart F
  let h := logDeriv f
  have hm (z) : MeromorphicAt f z :=
    LocalQuotientsArithmetic.scalar_meromorphicAt univ F hF z (mem_univ z)
  have ho (z) : meromorphicOrderAt f z ≠ ⊤ := by
    simpa only [sub_zero] using DivisorDegree.shifted_finite_order hF hn 0 z
  have hpf : Periodic ω₁ ω₂ f := fun z l hl => congrArg finiteCoordinate (hp z l hl)
  have hph : Periodic ω₁ ω₂ h := DivisorDegree.logDeriv_periodic hpf
  have hmh (z) : MeromorphicAt h z := (hm z).logDeriv
  have hreg (z) (hz : z ∉ poleSet h) : AnalyticAt ℂ f z ∧ f z ≠ 0 := by
    apply regular_off_divisor hF
    exact not_ne_iff.mp (fun hne => hz ((DivisorDegree.logDeriv_pole_iff (hm z) (ho z)).mpr hne))
  have hhol : HolomorphicOn (univ \ poleSet h) h := by
    refine ⟨isOpen_univ.sdiff (poleSet_closed_discrete hmh).1, fun z hz => ?_⟩
    exact ((hreg z hz.2).1.deriv.div (hreg z hz.2).1 (hreg z hz.2).2).differentiableAt
  obtain ⟨a, havoid, hreps⟩ := allowed_parallelogram ω₁ ω₂ h₁ h₂ h hmh hph
  let P := Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a ω₁ ω₂
  have hP : IsCompact P :=
    (by simp : ({a, a + ω₁, a + ω₁ + ω₂, a + ω₂} : Set ℂ).Finite).isCompact_convexHull ℝ
  have hfinite : (poleSet h ∩ interior P).Finite :=
    (finite_poles_on_compact hmh hP).subset (fun _ hz => ⟨interior_subset hz.2, hz.1⟩)
  let s := hfinite.toFinset
  have hmem (z) : z ∈ s ↔ z ∈ poleSet h ∧ z ∈ interior P := hfinite.mem_toFinset
  have hs : CompletePoleRepresentatives ω₁ ω₂ h s := by
    refine ⟨fun z hz => ((hmem z).mp hz).1, ?_, ?_⟩
    · intro x hx y hy hxy
      obtain ⟨w, _, huniq⟩ := hreps x ((hmem x).mp hx).1
      exact (huniq x ⟨((hmem x).mp hx).2, rfl⟩).trans
        (huniq y ⟨((hmem y).mp hy).2, hxy.symm⟩).symm
    · ext q
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, ((hmem z).mp hz).1, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨w, hw, _⟩ := hreps z hz
        have hl := (projection_eq_iff w z).mp hw.2
        have hwp : w ∈ poleSet h := by
          simpa using (pole_translation hph z (w - z) hl).mpr hz
        exact ⟨w, (hmem w).mpr ⟨hwp, hw.1⟩, hw.2⟩
  obtain ⟨Γ, htr, htrace, hInt⟩ := full_parallelogram_cycle h₁ h₂ a
  have havoid' : Disjoint Γ.trace (poleSet h) := havoid.mono_left htrace
  have hzreg (z) (hz : z ∈ Γ.trace) : AnalyticAt ℂ f z ∧ f z ≠ 0 :=
    hreg z (fun hh => Set.disjoint_left.mp havoid' hz hh)
  have hc : ContinuousOn h Γ.trace := fun z hz =>
    (hhol.2 z ⟨mem_univ z, fun hh => Set.disjoint_left.mp havoid' hz hh⟩).continuousAt.continuousWithinAt
  have hindex : ∀ z ∈ poleSet h, Γ.index z = if z ∈ s then 1 else 0 := by
    intro z hz
    have hztr : z ∉ Γ.trace := fun hztr => Set.disjoint_left.mp havoid' hztr hz
    rw [Γ.index_eq_integral z hztr, hInt _ (Γ.chain.reciprocal_continuousOn_trace z hztr)]
    by_cases hzI : z ∈ interior P
    · rw [parallelogram_reciprocal_integral_of_mem_interior h₁ h₂ a z hzI,
        ite_eq_left ((hmem z).mpr ⟨hz, hzI⟩), inv_mul_cancel₀ two_pi_I_ne_zero]
    · have hzP : z ∉ P := fun hzP => Set.disjoint_left.mp havoid
        ((mem_frontier_iff_notMem_interior hzP).mpr hzI) hz
      rw [parallelogram_reciprocal_integral_of_notMem hzP, mul_zero]
      simp [hmem, hzI]
  have hweightedHol : HolomorphicOn (univ \ poleSet h) (fun z => z * h z) :=
    ⟨hhol.1, fun z hz => differentiableAt_id.mul (hhol.2 z hz)⟩
  obtain ⟨t, ht, hres⟩ := ResidueCycle.residue_theorem univ (poleSet h)
    (fun z => z * h z) Γ isOpen_univ (subset_univ _)
    ((poleSet_closed_discrete hmh).1.preimage continuous_subtype_val)
    (poleSet_closed_discrete hmh).2 hweightedHol (subset_univ _) havoid' (by simp)
  have hts : t = s := by
    ext z
    rw [ht]
    by_cases hz : z ∈ poleSet h
    · rw [hindex z hz]
      by_cases hz' : z ∈ s <;> simp [hz, hz']
    · have hzs : z ∉ s := fun hh => hz (hs.1 hh)
      simp [hz, hzs]
  have hsum : ∑ z ∈ t, Γ.index z * Residue.residue (fun z => z * h z) z =
      ∑ z ∈ s, z * ((meromorphicOrderAt f z).untop₀ : ℂ) := by
    rw [hts]
    apply Finset.sum_congr rfl
    intro z hz
    rw [hindex z (hs.1 hz), ite_eq_left hz, one_mul]
    exact residue_coordinate_logDeriv (hm z) (ho z)
  rw [hsum, hInt (fun z => z * h z) (continuousOn_id.mul hc)] at hres
  have hbottom : (segmentPath a (a + ω₁)).trace ⊆ Γ.trace := by
    rw [htr]; exact fun _ hz => Or.inl (Or.inl hz)
  have hright : (segmentPath (a + ω₁) (a + ω₁ + ω₂)).trace ⊆ Γ.trace := by
    rw [htr]; exact fun _ hz => Or.inl (Or.inr hz)
  have htop : (segmentPath (a + ω₁ + ω₂) (a + ω₂)).trace ⊆ Γ.trace := by
    rw [htr]; exact fun _ hz => Or.inr (Or.inl hz)
  have hleft : (segmentPath (a + ω₂) a).trace ⊆ Γ.trace := by
    rw [htr]; exact fun _ hz => Or.inr (Or.inr hz)
  have hup : (segmentPath a (a + ω₂)).trace ⊆ Γ.trace := by
    rw [segment_trace_reverse]; exact hleft
  have hω₁ : ω₁ ∈ lattice ω₁ ω₂ := Submodule.subset_span (by simp)
  have hω₂ : ω₂ ∈ lattice ω₁ ω₂ := Submodule.subset_span (by simp)
  obtain ⟨n₁, hn₁⟩ := segment_logDeriv_integer f a (a + ω₁)
    (fun z hz => (hzreg z (hbottom hz)).1) (fun z hz => (hzreg z (hbottom hz)).2)
    (hpf a ω₁ hω₁)
  obtain ⟨n₂, hn₂⟩ := segment_logDeriv_integer f a (a + ω₂)
    (fun z hz => (hzreg z (hup hz)).1) (fun z hz => (hzreg z (hup hz)).2)
    (hpf a ω₂ hω₂)
  rw [parallelogram_weighted_integral hph a (hc.mono hbottom) (hc.mono hright)
    (hc.mono htop) (hc.mono hleft), hn₁, hn₂] at hres
  have he : (∑ z ∈ s, z * ((meromorphicOrderAt f z).untop₀ : ℂ)) =
      (n₂ : ℂ) * ω₁ - (n₁ : ℂ) * ω₂ := by
    apply mul_left_cancel₀ two_pi_I_ne_zero
    calc
      (2 * Real.pi * Complex.I : ℂ) * (∑ z ∈ s, z * ((meromorphicOrderAt f z).untop₀ : ℂ)) =
        ω₁ * ((n₂ : ℂ) * (2 * Real.pi * Complex.I : ℂ)) -
          ω₂ * ((n₁ : ℂ) * (2 * Real.pi * Complex.I : ℂ)) := hres.symm
      _ = _ := by ring
  refine ⟨s, hs, he ▸ ?_⟩
  simpa only [zsmul_eq_mul] using
    sub_mem ((lattice ω₁ ω₂).smul_mem n₂ hω₁) ((lattice ω₁ ω₂).smul_mem n₁ hω₂)

/-- Counted multiset sums may be taken over any finite superset of the support. -/
lemma multiset_sum_counts {G : Type*} [AddCommMonoid G] [DecidableEq G] (A : Multiset G)
    (Q : Finset G) (hA : ∀ q ∈ A, q ∈ Q) :
    A.sum = ∑ q ∈ Q, A.count q • q := by
  classical
  rw [Finset.sum_multiset_count]
  apply Finset.sum_subset (fun q hq => hA q (Multiset.mem_toFinset.mp hq))
  intro q _ hq
  rw [Multiset.count_eq_zero.mpr (fun hh => hq (Multiset.mem_toFinset.mpr hh)), zero_smul]

/-- Arbitrary lists, including repeated entries, have the same signed torus sum
as a complete set of distinct divisor classes with their signed orders. -/
lemma lists_projection_sum {ω₁ ω₂ : ℂ} {F : ℂ → RiemannSphere}
    (hF : ScalarMeromorphicOn univ F)
    (hn : ¬ ∃ c : ℂ, ∀ z, F z = sphereFinite c)
    {a b : Multiset ℂ} (hab : DivisorLists ω₁ ω₂ F a b)
    {s : Finset ℂ} (hs : CompletePoleRepresentatives ω₁ ω₂ (logDeriv (scalarFinitePart F)) s) :
    projection ω₁ ω₂ (a.sum - b.sum) =
      ∑ z ∈ s, (meromorphicOrderAt (scalarFinitePart F) z).untop₀ • projection ω₁ ω₂ z := by
  classical
  let π := projection ω₁ ω₂
  let Q := s.image π
  have hm (z) : MeromorphicAt (scalarFinitePart F) z :=
    LocalQuotientsArithmetic.scalar_meromorphicAt univ F hF z (mem_univ z)
  have ho (z) : meromorphicOrderAt (scalarFinitePart F) z ≠ ⊤ := by
    simpa only [sub_zero] using DivisorDegree.shifted_finite_order hF hn 0 z
  have hQ (q) (hqa : (a.map π).count q ≠ 0 ∨ (b.map π).count q ≠ 0) : q ∈ Q := by
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (lattice ω₁ ω₂).toAddSubgroup q
    change π z ∈ Q
    have hz : meromorphicOrderAt (scalarFinitePart F) z ≠ 0 := by
      intro hz
      have ha := (hab z).1
      have hb := (hab z).2
      simp only [hz, WithTop.untop₀_zero, Int.toNat_zero, neg_zero] at ha hb
      rcases hqa with hqa | hqb
      · exact hqa ha
      · exact hqb hb
    have hp : z ∈ poleSet (logDeriv (scalarFinitePart F)) :=
      (DivisorDegree.logDeriv_pole_iff (hm z) (ho z)).mpr hz
    have himg : π z ∈ projection ω₁ ω₂ '' (↑s : Set ℂ) :=
      hs.2.2.symm ▸ (show π z ∈ poleClasses ω₁ ω₂ (logDeriv (scalarFinitePart F)) from ⟨z, hp, rfl⟩)
    obtain ⟨w, hw, he⟩ := himg
    exact Finset.mem_image.mpr ⟨w, hw, he⟩
  have ha := multiset_sum_counts (a.map π) Q (fun q hq => hQ q
    (Or.inl (Nat.ne_of_gt (Multiset.count_pos.mpr hq))))
  have hb := multiset_sum_counts (b.map π) Q (fun q hq => hQ q
    (Or.inr (Nat.ne_of_gt (Multiset.count_pos.mpr hq))))
  rw [map_sub, π.map_multiset_sum, π.map_multiset_sum, ha, hb, ← Finset.sum_sub_distrib]
  rw [Finset.sum_image (by exact hs.2.1)]
  apply Finset.sum_congr rfl
  intro z _
  rw [(hab z).1, (hab z).2]
  rw [← natCast_zsmul, ← natCast_zsmul, sub_eq_add_neg, ← sub_zsmul, Int.toNat_sub_toNat_neg]

/-- The lattice-class identity, for every choice of repeated divisor representatives. -/
theorem divisor_sum_constraint :
    Specs.D12Complex.Ch22.DivisorSumConstraint.divisor_sum_constraint_type := by
  intro ω₁ ω₂ h₁ h₂ F hF hp hn a b hab
  obtain ⟨s, hs, hsum⟩ := exists_weighted_representatives h₁ h₂ hF hp hn
  have hzero : projection ω₁ ω₂
      (∑ z ∈ s, z * ((meromorphicOrderAt (scalarFinitePart F) z).untop₀ : ℂ)) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr hsum
  have he : projection ω₁ ω₂ (a.sum - b.sum) = 0 := by
    rw [lists_projection_sum hF hn hab hs]
    convert hzero using 1
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [mul_comm, ← zsmul_eq_mul, map_zsmul]
  exact (QuotientAddGroup.eq_zero_iff _).mp he

end D12Complex.DivisorSumConstraint
