import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.HarnackConvergence
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.HarnackInequality
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.DiskDirichlet
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
open Complex Metric Real Filter Set InnerProductSpace
open scoped Topology

namespace D12Complex.HarnackConvergence

lemma ConvergesOnCompacts.tendsto_at {Ω : Set ℂ} {u : ℕ → ℂ → ℝ} {v : ℂ → ℝ}
    (h : ConvergesOnCompacts Ω u v) {z : ℂ} (hz : z ∈ Ω) :
    Tendsto (fun n => u n z) atTop (𝓝 (v z)) :=
  (h {z} isCompact_singleton (singleton_subset_iff.mpr hz)).tendsto_at (mem_singleton z)

lemma harmonic_sub {Ω : Set ℂ} {u v : ℂ → ℝ}
    (hu : HarmonicOn Ω u) (hv : HarmonicOn Ω v) : HarmonicOn Ω (fun z => u z - v z) :=
  (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd Ω _ hu.1).mpr
    (((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd Ω u hu.1).mp hu).sub
      ((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd Ω v hu.1).mp hv))

/-- Uniform convergence survives multiplication by a fixed bounded real kernel. -/
lemma uniform_mul_of_bound {S : Set ℂ} {u : ℕ → ℂ → ℝ} {v k : ℂ → ℝ}
    (h : TendstoUniformlyOn u v atTop S) {M : ℝ}
    (hM : ∀ z ∈ S, ‖k z‖ ≤ M) :
    TendstoUniformlyOn (fun n z => k z * u n z) (fun z => k z * v z) atTop S := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let C := |M| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h (ε / C) (div_pos hε hC)] with n hn
  intro z hz
  calc
    dist (k z * v z) (k z * u n z) = ‖k z‖ * dist (v z) (u n z) := by
      simp only [Real.dist_eq, ← mul_sub, abs_mul, Real.norm_eq_abs]
    _ ≤ C * dist (v z) (u n z) :=
      mul_le_mul_of_nonneg_right ((hM z hz).trans (by dsimp [C]; linarith [le_abs_self M]))
        dist_nonneg
    _ < C * (ε / C) := mul_lt_mul_of_pos_left (hn z hz) hC
    _ = ε := mul_div_cancel₀ ε hC.ne'

/-- Pass to the limit in a Poisson integral on one fixed circle. -/
lemma poissonIntegral_tendsto {R : ℝ} (hR : 0 < R)
    {u : ℕ → ℂ → ℝ} {v : ℂ → ℝ}
    (hu : ∀ n, ContinuousOn (u n) (sphere 0 R))
    (hv : TendstoUniformlyOn u v atTop (sphere 0 R))
    {z : ℂ} (hz : ‖z‖ < R) :
    Tendsto (fun n => PoissonHarmonic.poissonIntegral R (u n) z) atTop
      (𝓝 (PoissonHarmonic.poissonIntegral R v z)) := by
  have hk := DiskDirichlet.kernel_continuousOn hR hz
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn hk
  have hm := uniform_mul_of_bound hv hM
  have hm' : TendstoUniformlyOn
      (fun n t => PoissonHarmonic.kernel R z (circleMap 0 R t) * u n (circleMap 0 R t))
      (fun t => PoissonHarmonic.kernel R z (circleMap 0 R t) * v (circleMap 0 R t))
      atTop (uIcc 0 (2 * Real.pi)) :=
    (hm.comp (circleMap 0 R)).mono (fun t _ => circleMap_mem_sphere 0 hR.le t)
  have hc : ∀ᶠ n : ℕ in atTop, ContinuousOn
      (fun t => PoissonHarmonic.kernel R z (circleMap 0 R t) * u n (circleMap 0 R t))
      (uIcc 0 (2 * Real.pi)) := by
    exact Eventually.of_forall fun n => (hk.mul (hu n)).comp
      (continuous_circleMap 0 R).continuousOn (fun t _ => circleMap_mem_sphere 0 hR.le t)
  exact tendsto_const_nhds.mul
    (TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn hc hm')

/-- Locally uniform limits are harmonic in the original C²/Laplacian sense.
The proof identifies the limit with a Poisson solution on an interior disk. -/
lemma harmonic_limit {Ω : Set ℂ} {u : ℕ → ℂ → ℝ} {v : ℂ → ℝ}
    (hΩ : IsOpen Ω) (hu : ∀ n, HarmonicOn Ω (u n))
    (hv : ConvergesOnCompacts Ω u v) : HarmonicOn Ω v := by
  apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd Ω v hΩ).mpr
  intro a ha
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ a ha
  let R := r / 2
  have hR : 0 < R := half_pos hr
  have hclosed : closedBall a R ⊆ Ω :=
    (closedBall_subset_ball (by dsimp [R]; linarith)).trans hsub
  let τ : ℂ → ℂ := fun z => a + z
  have hτ : HolomorphicOn (ball (0 : ℂ) R) τ :=
    ⟨isOpen_ball, fun _ _ => (differentiableAt_const a).add differentiableAt_id⟩
  have hmap : MapsTo τ (closedBall 0 R) (closedBall a R) := by
    intro z hz
    simpa [τ, mem_closedBall, dist_eq_norm] using hz
  have huc (n : ℕ) : ContinuousOn (u n ∘ τ) (closedBall 0 R) :=
    ((hu n).2.1.continuousOn.mono hclosed).comp
      (continuous_const.add continuous_id).continuousOn hmap
  have huh (n : ℕ) : HarmonicOn (ball 0 R) (u n ∘ τ) :=
    HarmonicFoundation.harmonicOn_comp_holomorphic Ω (ball 0 R) (u n) τ (hu n) hτ
      (fun z hz => hclosed (hmap (ball_subset_closedBall hz)))
  have hconv : TendstoUniformlyOn (fun n => u n ∘ τ) (v ∘ τ) atTop (closedBall 0 R) :=
    ((hv _ (isCompact_closedBall a R) hclosed).comp τ).mono hmap
  have hvc : ContinuousOn (v ∘ τ) (sphere 0 R) :=
    (hconv.continuousOn (Frequently.of_forall huc)).mono sphere_subset_closedBall
  have heq (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) :
      PoissonHarmonic.poissonIntegral R (v ∘ τ) z = v (τ z) := by
    have hp := poissonIntegral_tendsto hR
      (fun n => (huc n).mono sphere_subset_closedBall)
      (hconv.mono sphere_subset_closedBall) (by simpa using hz)
    have hpoint := hconv.tendsto_at (ball_subset_closedBall hz)
    have hrep (n : ℕ) := DiskDirichlet.dirichlet_representation hR (huc n) (huh n) hz
    exact tendsto_nhds_unique (hp.congr (fun n => hrep n)) hpoint
  have hph := PoissonHarmonic.poissonIntegral_harmonic R (v ∘ τ) hR hvc
  have hh : HarmonicOn (ball a R)
      (fun z => PoissonHarmonic.poissonIntegral R (v ∘ τ) (z - a)) :=
    HarmonicFoundation.harmonicOn_comp_holomorphic (ball 0 R) (ball a R) _
      (fun z => z - a) hph
      ⟨isOpen_ball, fun _ _ => differentiableAt_id.sub (differentiableAt_const a)⟩
      (fun z hz => by simpa [mem_ball, dist_eq_norm] using hz)
  have hha := (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ isOpen_ball).mp hh
  have hlocal : (fun z => PoissonHarmonic.poissonIntegral R (v ∘ τ) (z - a)) =ᶠ[𝓝 a] v := by
    filter_upwards [ball_mem_nhds a hR] with z hz
    simpa [τ] using heq (z - a) (by simpa [mem_ball, dist_eq_norm] using hz)
  exact (harmonicAt_congr_nhds hlocal).mp (hha a (mem_ball_self hR))

/-- Boundedness at one point propagates to every point. Subtracting the
first term makes the Harnack comparison applicable without a sign premise. -/
lemma bounded_at_each_point {Ω : Set ℂ} {u : ℕ → ℂ → ℝ} (hΩ : IsDomain Ω)
    (hu : ∀ n, HarmonicOn Ω (u n)) (hm : ∀ z ∈ Ω, Monotone (fun n => u n z))
    {a : ℂ} (ha : a ∈ Ω) (hb : BddAbove (range (fun n => u n a))) :
    ∀ z ∈ Ω, BddAbove (range (fun n => u n z)) := by
  obtain ⟨M, hM⟩ := hb
  intro z hz
  obtain ⟨C, hC, hcomp⟩ := HarnackInequality.harnack_compact Ω hΩ a ha {z}
    isCompact_singleton (singleton_subset_iff.mpr hz)
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  refine ⟨u 0 z + C * (M - u 0 a), ?_⟩
  rintro _ ⟨n, rfl⟩
  have h := (hcomp (fun w => u n w - u 0 w) (harmonic_sub (hu n) (hu 0))
    (fun w hw => sub_nonneg.mpr (hm w hw (Nat.zero_le n))) z (mem_singleton z)).2
  have hb' : u n a ≤ M := hM (mem_range_self n)
  have hc := mul_le_mul_of_nonneg_left (sub_le_sub_right hb' (u 0 a)) hC0
  linarith

/-- The nonnegative difference estimate passes to the finite pointwise limit,
and controls the whole compact set by the error at the basepoint. -/
lemma compact_convergence_of_pointwise {Ω : Set ℂ} {u : ℕ → ℂ → ℝ} {v : ℂ → ℝ}
    (hΩ : IsDomain Ω) (hu : ∀ n, HarmonicOn Ω (u n))
    (hm : ∀ z ∈ Ω, Monotone (fun n => u n z)) {a : ℂ} (ha : a ∈ Ω)
    (hv : ∀ z ∈ Ω, Tendsto (fun n => u n z) atTop (𝓝 (v z))) :
    ConvergesOnCompacts Ω u v := by
  intro K hK hKΩ
  obtain ⟨C, hC, hcomp⟩ := HarnackInequality.harnack_compact Ω hΩ a ha K hK hKΩ
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hle (n : ℕ) (z : ℂ) (hz : z ∈ Ω) : u n z ≤ v z := by
    exact ge_of_tendsto (hv z hz) ((eventually_ge_atTop n).mono (fun m hnm => hm z hz hnm))
  have hbound (n : ℕ) (z : ℂ) (hz : z ∈ K) :
      v z - u n z ≤ C * (v a - u n a) := by
    apply le_of_tendsto_of_tendsto ((hv z (hKΩ hz)).sub_const (u n z))
      (tendsto_const_nhds.mul ((hv a ha).sub_const (u n a)))
    filter_upwards [eventually_ge_atTop n] with m hnm
    exact (hcomp (fun w => u m w - u n w) (harmonic_sub (hu m) (hu n))
      (fun w hw => sub_nonneg.mpr (hm w hw hnm)) z hz).2
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have herror : Tendsto (fun n => v a - u n a) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => v a) atTop (𝓝 (v a)) := tendsto_const_nhds
    simpa using hconst.sub (hv a ha)
  filter_upwards [herror.eventually (gt_mem_nhds (div_pos hε hC0))] with n hn
  intro z hz
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hle n z (hKΩ hz)))]
  exact (hbound n z hz).trans_lt ((lt_div_iff₀' hC0).mp hn)

lemma finite_limit_of_bounded {Ω : Set ℂ} {u : ℕ → ℂ → ℝ}
    (hΩ : IsDomain Ω) (hu : ∀ n, HarmonicOn Ω (u n))
    (hm : ∀ z ∈ Ω, Monotone (fun n => u n z)) {a : ℂ} (ha : a ∈ Ω)
    (hb : BddAbove (range (fun n => u n a))) :
    ∃ v : ℂ → ℝ, HarmonicOn Ω v ∧ ConvergesOnCompacts Ω u v := by
  let v : ℂ → ℝ := fun z => ⨆ n, u n z
  have hv : ∀ z ∈ Ω, Tendsto (fun n => u n z) atTop (𝓝 (v z)) := by
    intro z hz
    exact tendsto_atTop_ciSup (hm z hz) (bounded_at_each_point hΩ hu hm ha hb z hz)
  have hc := compact_convergence_of_pointwise hΩ hu hm ha hv
  exact ⟨v, harmonic_limit hΩ.2.1 hu hc, hc⟩

/-- The lower Harnack bound and a compact lower bound for the first term
turn unbounded basepoint values into uniform compact divergence. -/
lemma compact_divergence_of_unbounded {Ω : Set ℂ} {u : ℕ → ℂ → ℝ}
    (hΩ : IsDomain Ω) (hu : ∀ n, HarmonicOn Ω (u n))
    (hm : ∀ z ∈ Ω, Monotone (fun n => u n z)) {a : ℂ} (ha : a ∈ Ω)
    (hb : ¬ BddAbove (range (fun n => u n a))) : DivergesOnCompacts Ω u := by
  intro K hK hKΩ T
  obtain ⟨C, hC, hcomp⟩ := HarnackInequality.harnack_compact Ω hΩ a ha K hK hKΩ
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn ((hu 0).2.1.continuousOn.mono hKΩ)
  have htop := tendsto_atTop_atTop_of_monotone' (hm a ha) hb
  filter_upwards [htop.eventually (eventually_gt_atTop (C * (T + M) + u 0 a))] with n hn
  intro z hz
  have hlo := (hcomp (fun w => u n w - u 0 w) (harmonic_sub (hu n) (hu 0))
    (fun w hw => sub_nonneg.mpr (hm w hw (Nat.zero_le n))) z hz).1
  have hfirst : -M ≤ u 0 z := by
    have hab : |u 0 z| ≤ M := by simpa only [Real.norm_eq_abs] using hM z hz
    exact (abs_le.mp hab).1
  have hmul : C * (T + M) < u n a - u 0 a := by linarith
  have hh : T + M < C⁻¹ * (u n a - u 0 a) := (lt_inv_mul_iff₀ hC0).mpr hmul
  linarith

theorem bounded_iff_finite_limit :
    Specs.D12Complex.Ch13.HarnackConvergence.bounded_iff_finite_limit_type := by
  intro Ω u hΩ hu hm a ha
  constructor
  · exact finite_limit_of_bounded hΩ hu hm ha
  · rintro ⟨v, _, hv⟩
    exact (hv.tendsto_at ha).bddAbove_range

lemma DivergesOnCompacts.tendsto_at {Ω : Set ℂ} {u : ℕ → ℂ → ℝ}
    (h : DivergesOnCompacts Ω u) {a : ℂ} (ha : a ∈ Ω) :
    Tendsto (fun n => u n a) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro T
  exact (h {a} isCompact_singleton (singleton_subset_iff.mpr ha) T).mono
    (fun n hn => (hn a (mem_singleton a)).le)

theorem unbounded_iff_compact_divergence :
    Specs.D12Complex.Ch13.HarnackConvergence.unbounded_iff_compact_divergence_type := by
  intro Ω u hΩ hu hm a ha
  constructor
  · exact compact_divergence_of_unbounded hΩ hu hm ha
  · intro hd hb
    have hfin := tendsto_atTop_ciSup (hm a ha) hb
    exact not_tendsto_atTop_of_tendsto_nhds hfin (hd.tendsto_at ha)

theorem harnack_convergence :
    Specs.D12Complex.Ch13.HarnackConvergence.harnack_convergence_type := by
  classical
  intro Ω u hΩ hu hm
  obtain ⟨a, ha⟩ := hΩ.1
  by_cases hb : BddAbove (range (fun n => u n a))
  · exact Or.inl (finite_limit_of_bounded hΩ hu hm ha hb)
  · exact Or.inr (compact_divergence_of_unbounded hΩ hu hm ha hb)

theorem no_mixed_limits :
    Specs.D12Complex.Ch13.HarnackConvergence.no_mixed_limits_type := by
  intro Ω u hΩ hu hm a ha b hb L hL
  obtain ⟨v, _, hv⟩ := finite_limit_of_bounded hΩ hu hm ha hL.bddAbove_range
  exact not_tendsto_atTop_of_tendsto_nhds (hv.tendsto_at hb)

end D12Complex.HarnackConvergence
