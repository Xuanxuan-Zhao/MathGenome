import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.TrotterKatoApproximation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.LaplaceResolvent
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.GeneratorDeterminesSemigroup
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open Filter Topology Set MeasureTheory
open scoped NNReal
namespace ExpandedFA.Semigroups.TrotterKatoApproximation
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
local instance : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
local instance : IsScalarTower ℝ 𝕜 X := IsScalarTower.restrictScalars ℝ 𝕜 X
open TrotterKatoSpec LaplaceResolventSpec

/-- Locally uniform convergence implies convergence of every real Laplace
resolvent above the common growth exponent. -/
theorem resolvent_convergence_of_semigroup (S : ℕ → C0Semigroup 𝕜 X)
    (T : C0Semigroup 𝕜 X) (M ω : ℝ)
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω)
    (hS : C0SemigroupSpec.commonExponentialBoundValue S M ω)
    (h : LocallyUniformStrongConvergence S T) (r : ℝ) (hr : ω < r) :
    StrongResolventConvergence S T r := by
  intro x
  have hb n : C0SemigroupSpec.exponentialBoundValue (S n) M ω :=
    ⟨hS.1, hS.2 n⟩
  have hc U (hU : C0SemigroupSpec.exponentialBoundValue U M ω) :=
    (LaplaceResolvent.canonical_resolvent U M ω (algebraMap ℝ 𝕜 r) hU
      (by simpa using hr)).2.1 x
  simp_rw [hc _ (hb _), hc T hT]
  apply tendsto_integral_of_dominated_convergence
    (fun t : ℝ => Real.exp (-(r - ω) * t) * (M * ‖x‖))
  · intro n
    exact ((LaplaceResolvent.continuous_orbit (S n) _ x).aestronglyMeasurable).restrict
  · exact (LaplaceResolvent.scalar_moment_integrable 0 (sub_pos.mpr hr)).mul_const
      (M * ‖x‖) |>.congr (by filter_upwards [] with t; simp)
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa [mul_comm] using LaplaceResolvent.norm_orbit_le (S n) (hb n)
      (algebraMap ℝ 𝕜 r) x ht.le
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp := (h x t ht.le).tendsto_at ⟨ht.le, le_rfl⟩
    exact hp.const_smul _


omit [CompleteSpace X] in
/-- Strong convergence of uniformly bounded operators is uniform on compact sets. -/
theorem uniform_on_compact (F : ℕ → X →L[𝕜] X) (G : X →L[𝕜] X)
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀ n, ‖F n‖ ≤ C) (hG : ‖G‖ ≤ C)
    (h : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (G x)))
    {K : Set X} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n x => F n x) G atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hd : 0 < ε / (3 * (C + 1)) := div_pos hε (by positivity)
  obtain ⟨D, _, hD, hcover⟩ := hK.finite_cover_balls hd
  have hev : ∀ᶠ n in atTop, ∀ y ∈ D, dist (G y) (F n y) < ε / 3 :=
    hD.eventually_all.mpr (fun y _ => by
      simpa only [dist_comm] using Metric.tendsto_nhds.mp (h y) (ε / 3) (by positivity))
  filter_upwards [hev] with n hn x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
  have hl (L : X →L[𝕜] X) (hL : ‖L‖ ≤ C) :
      dist (L x) (L y) ≤ C * dist x y := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  have hδ : C * dist x y < ε / 3 := by
    have hxy' : dist x y < ε / (3 * (C + 1)) := hxy
    have hh : dist x y < ε / 3 / (C + 1) := by convert hxy' using 1; field_simp
    have hh' := (lt_div_iff₀ (show 0 < C + 1 by positivity)).mp hh
    have hnxy := dist_nonneg (x := x) (y := y)
    nlinarith
  calc
    dist (G x) (F n x) ≤ dist (G x) (G y) + dist (G y) (F n y) +
        dist (F n y) (F n x) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
      apply add_lt_add (add_lt_add ((hl G hG).trans_lt hδ) (hn y hy))
      rw [dist_comm]
      exact (hl (F n) (hF n)).trans_lt hδ
    _ = ε := by ring


/-- A comparison-orbit derivative; only strong continuity and the derivative
domains of the two vectors enter this product rule. -/
theorem comparison_derivative (S T : C0Semigroup 𝕜 X) (L : X →L[𝕜] X)
    (x : (C0SemigroupSpec.generatorValue T).domain) (t : ℝ≥0) (s : ℝ)
    (hs : 0 ≤ s) (hst : s < (t : ℝ))
    (hz : L (T.operators s.toNNReal x) ∈ (C0SemigroupSpec.generatorValue S).domain) :
    HasDerivWithinAt (fun r : ℝ => S.operators ((t : ℝ) - r).toNNReal
      (L (T.operators r.toNNReal x)))
      (S.operators ((t : ℝ) - s).toNNReal
        (L (T.operators s.toNNReal (C0SemigroupSpec.generatorValue T x)) -
          C0SemigroupSpec.generatorValue S ⟨L (T.operators s.toNNReal x), hz⟩)) (Ici s) s := by
  apply HasDerivWithinAt.Ici_of_Ioi
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mpr
  let y : (C0SemigroupSpec.generatorValue T).domain :=
    ⟨T.operators s.toNNReal x,
      SemigroupGrowthAndGenerator.domain_invariant T s.toNNReal x x.2⟩
  let z : (C0SemigroupSpec.generatorValue S).domain := ⟨L (T.operators s.toNNReal x), hz⟩
  have hshift : Tendsto (fun r : ℝ => r - s) (𝓝[>] s) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · convert! ((tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun r : ℝ => r) (𝓝[>] s) (𝓝 s)).sub_const s) using 1
      simp
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact sub_pos.mpr (show s < r from hr)
  have hT := (L.continuous.tendsto _).comp (generator_has_limit T y)
  have hS := generator_has_limit S z
  change Tendsto (fun h => L (differenceQuotient T h y)) _ _ at hT
  change Tendsto (fun h => differenceQuotient S h z) _ _ at hS
  have hlim := (hT.sub hS).comp hshift
  have htime : Tendsto (fun r : ℝ => ((t : ℝ) - r).toNNReal)
      (𝓝[>] s) (𝓝 (((t : ℝ) - s).toNNReal)) :=
    (continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hcomm : C0SemigroupSpec.generatorValue T y = T.operators s.toNNReal (C0SemigroupSpec.generatorValue T x) :=
    SemigroupGrowthAndGenerator.generator_commutes T s.toNNReal x y.2
  change Tendsto (fun r => L (differenceQuotient T (r - s) y) -
    differenceQuotient S (r - s) z) _ (𝓝 (L (C0SemigroupSpec.generatorValue T y) - C0SemigroupSpec.generatorValue S z)) at hlim
  rw [hcomm] at hlim
  have hprod := GeneratorDeterminesSemigroup.tendsto_apply S htime hlim
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hst).filter_mono nhdsWithin_le_nhds] with r hrs hrt
  rw [slope_def_module]
  change S.operators ((t : ℝ) - r).toNNReal
    (L (differenceQuotient T (r - s) (T.operators s.toNNReal x)) -
      differenceQuotient S (r - s) (L (T.operators s.toNNReal x))) = _
  rw [T.differenceQuotient_real, S.differenceQuotient_real]
  rw [L.map_smul_of_tower, ← smul_sub,
    (S.operators ((t : ℝ) - r).toNNReal).map_smul_of_tower]
  congr 1
  rw [map_sub, map_sub, map_sub, map_sub]
  simp only [sub_sub_sub_cancel_right]
  have hTtime : (r - s).toNNReal + s.toNNReal = r.toNNReal := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, Real.coe_toNNReal _ (sub_nonneg.mpr (le_of_lt hrs)),
      Real.coe_toNNReal _ hs, Real.coe_toNNReal _ (hs.trans (le_of_lt hrs))]
    ring
  have hStime : ((t : ℝ) - r).toNNReal + (r - s).toNNReal =
      ((t : ℝ) - s).toNNReal := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, Real.coe_toNNReal _ (sub_nonneg.mpr (le_of_lt hrt)),
      Real.coe_toNNReal _ (sub_nonneg.mpr (le_of_lt hrs)),
      Real.coe_toNNReal _ (sub_nonneg.mpr hst.le)]
    ring
  rw [← T.add_apply, hTtime, ← S.add_apply, hStime]

/-- A resolvent commutes with its semigroup, on all ambient vectors. -/
theorem resolvent_semigroup_commute (T : C0Semigroup 𝕜 X) (ζ : 𝕜)
    (R : Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue T) ζ) (t : ℝ≥0) (x : X) :
    R.inverse (T.operators t x) = T.operators t (R.inverse x) := by
  have hm := SemigroupGrowthAndGenerator.domain_invariant T t _ (R.mem_domain x)
  calc
    R.inverse (T.operators t x) = R.inverse
        (ζ • T.operators t (R.inverse x) - C0SemigroupSpec.generatorValue T ⟨_, hm⟩) := by
      congr 1
      rw [SemigroupGrowthAndGenerator.generator_commutes T t ⟨_, R.mem_domain x⟩ hm,
        ← map_smul, ← map_sub, R.right_inverse]
    _ = _ := R.left_inverse ⟨_, hm⟩

/-- The generator evaluated on its resolvent range. -/
theorem generator_resolvent (T : C0Semigroup 𝕜 X) (ζ : 𝕜)
    (R : Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue T) ζ) (x : X) :
    C0SemigroupSpec.generatorValue T ⟨R.inverse x, R.mem_domain x⟩ = ζ • R.inverse x - x := by
  have h := R.right_inverse x
  exact (eq_sub_iff_add_eq.mpr (by
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm))


/-- The comparison of two semigroups after smoothing with their resolvents.
Its derivative depends only on the difference of the resolvents. -/
theorem resolvent_comparison_derivative (S T : C0Semigroup 𝕜 X) (ζ : 𝕜)
    (Q : Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue S) ζ)
    (R : Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue T) ζ)
    (x : X) (t : ℝ≥0) (s : ℝ) (hs : 0 ≤ s) (hst : s < (t : ℝ)) :
    HasDerivWithinAt (fun r : ℝ => S.operators ((t : ℝ) - r).toNNReal
      (Q.inverse (T.operators r.toNNReal (R.inverse x))))
      (S.operators ((t : ℝ) - s).toNNReal
        (R.inverse (T.operators s.toNNReal x) - Q.inverse (T.operators s.toNNReal x)))
      (Ici s) s := by
  have hd := comparison_derivative S T Q.inverse ⟨R.inverse x, R.mem_domain x⟩
    t s hs hst (Q.mem_domain _)
  convert hd using 1
  congr 1
  rw [generator_resolvent, generator_resolvent, map_sub, map_smul, map_sub, map_smul]
  rw [resolvent_semigroup_commute T ζ R]
  abel

/-- A deterministic bound for the smoothed comparison. -/
theorem resolvent_comparison_bound (S T : C0Semigroup 𝕜 X) (ζ : 𝕜)
    (Q : Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue S) ζ)
    (R : Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue T) ζ)
    (x : X) (t : ℝ≥0) {C ε : ℝ} (hC : 0 ≤ C)
    (hS : ∀ u : ℝ≥0, u ≤ t → ‖S.operators u‖ ≤ C)
    (hε : ∀ s ∈ Icc (0 : ℝ) (t : ℝ),
      ‖R.inverse (T.operators s.toNNReal x) - Q.inverse (T.operators s.toNNReal x)‖ ≤ ε) :
    ‖S.operators t (Q.inverse (R.inverse x)) -
        Q.inverse (R.inverse (T.operators t x))‖ ≤ C * ε * (t : ℝ) := by
  let f : ℝ → X := fun s => S.operators ((t : ℝ) - s).toNNReal
    (Q.inverse (T.operators s.toNNReal (R.inverse x)))
  have hc : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro s
    apply GeneratorDeterminesSemigroup.tendsto_apply S
    · exact (continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).continuousAt
    · exact Q.inverse.continuous.continuousAt.comp (T.continuous_real_orbit _).continuousAt
  have hd := fun s (hs : s ∈ Ico (0 : ℝ) (t : ℝ)) =>
    resolvent_comparison_derivative S T ζ Q R x t s hs.1 hs.2
  have hb : ∀ s ∈ Ico (0 : ℝ) (t : ℝ),
      ‖S.operators ((t : ℝ) - s).toNNReal
        (R.inverse (T.operators s.toNNReal x) - Q.inverse (T.operators s.toNNReal x))‖ ≤ C * ε := by
    intro s hs
    apply ((S.operators _).le_opNorm _).trans
    apply mul_le_mul (hS _ ?_) (hε s ⟨hs.1, hs.2.le⟩) (norm_nonneg _) hC
    simpa only [Real.toNNReal_coe] using
      Real.toNNReal_le_toNNReal (show (t : ℝ) - s ≤ (t : ℝ) by linarith [hs.1])
  have hh := norm_image_sub_le_of_norm_deriv_right_le_segment hc.continuousOn hd hb
    (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩
  dsimp only [f] at hh
  rw [sub_self, Real.toNNReal_zero, S.zero_apply, sub_zero, Real.toNNReal_coe,
    T.zero_apply, ← resolvent_semigroup_commute T ζ R] at hh
  simpa only [norm_sub_rev] using hh

/-- Resolvents have dense range, and so do their squares. -/
theorem resolvent_denseRange (T : C0Semigroup 𝕜 X) (ζ : 𝕜)
    (R : Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue T) ζ) :
    DenseRange R.inverse := by
  apply T.generator_domain_dense.mono
  intro x hx
  exact ⟨ζ • x - C0SemigroupSpec.generatorValue T ⟨x, hx⟩, R.left_inverse ⟨x, hx⟩⟩


/-- The common exponential estimate gives a common bound on each time interval. -/
theorem interval_bound (T : C0Semigroup 𝕜 X) {M ω b : ℝ}
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ b) :
    ‖T.operators t‖ ≤ M * Real.exp (|ω| * b) := by
  apply (hT.2 t).trans
  apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one hT.1)
  exact Real.exp_le_exp.mpr (mul_le_mul (le_abs_self ω) ht t.coe_nonneg (abs_nonneg ω))

/-- A bounded family extends uniform strong convergence from a dense range. -/
theorem uniform_of_dense_range (S : ℕ → C0Semigroup 𝕜 X) (T : C0Semigroup 𝕜 X)
    (D : X → X) (hD : DenseRange D) {b C : ℝ} (hC : 0 ≤ C)
    (hS : ∀ n (t : ℝ), t ∈ Icc 0 b → ‖(S n).operators t.toNNReal‖ ≤ C)
    (hT : ∀ t : ℝ, t ∈ Icc 0 b → ‖T.operators t.toNNReal‖ ≤ C)
    (h : ∀ y, TendstoUniformlyOn (fun n (t : ℝ) => (S n).operators t.toNNReal (D y))
      (fun t : ℝ => T.operators t.toNNReal (D y)) atTop (Icc 0 b)) :
    ∀ x, TendstoUniformlyOn (fun n (t : ℝ) => (S n).operators t.toNNReal x)
      (fun t : ℝ => T.operators t.toNNReal x) atTop (Icc 0 b) := by
  intro x
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨y, hy⟩ := hD.exists_dist_lt x
    (div_pos hε (show 0 < 6 * (C + 1) by positivity))
  have hy' : C * dist x (D y) < ε / 6 := by
    have hh : dist x (D y) < ε / 6 / (C + 1) := by
      convert hy using 1; field_simp
    have hh' := (lt_div_iff₀ (show 0 < C + 1 by positivity)).mp hh
    have hn := dist_nonneg (x := x) (y := D y)
    nlinarith
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (h y) (ε / 3) (by positivity)] with n hn t ht
  have hl (L : X →L[𝕜] X) (hL : ‖L‖ ≤ C) :
      dist (L x) (L (D y)) < ε / 6 := by
    rw [dist_eq_norm, ← map_sub]
    exact ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))).trans_lt (by
        simpa only [dist_eq_norm] using hy')
  calc
    _ ≤ dist (T.operators t.toNNReal x) (T.operators t.toNNReal (D y)) +
        dist (T.operators t.toNNReal (D y)) ((S n).operators t.toNNReal (D y)) +
        dist ((S n).operators t.toNNReal (D y)) ((S n).operators t.toNNReal x) :=
      dist_triangle4 _ _ _ _
    _ < ε / 6 + ε / 3 + ε / 6 := by
      apply add_lt_add (add_lt_add (hl _ (hT t ht)) (hn t ht))
      rw [dist_comm]
      exact hl _ (hS n t ht)
    _ < ε := by linarith

/-- The difficult direction, proved by a deterministic two-resolvent comparison.
See also Schnaubelt, Evolution Equations, Theorem 3.14, pp. 83–85. -/
theorem semigroup_convergence_of_resolvent (S : ℕ → C0Semigroup 𝕜 X)
    (T : C0Semigroup 𝕜 X) (M ω : ℝ)
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω)
    (hS : C0SemigroupSpec.commonExponentialBoundValue S M ω)
    (r : ℝ) (hr : ω < r) (h : StrongResolventConvergence S T r) :
    LocallyUniformStrongConvergence S T := by
  let ζ : 𝕜 := algebraMap ℝ 𝕜 r
  have hr' : ω < RCLike.re ζ := by simpa [ζ] using hr
  have hb n : C0SemigroupSpec.exponentialBoundValue (S n) M ω := ⟨hS.1, hS.2 n⟩
  let R := LaplaceResolvent.inverse T M ω ζ hT hr'
  let Q := fun n => LaplaceResolvent.inverse (S n) M ω ζ (hb n) hr'
  have hcanon (U : C0Semigroup 𝕜 X)
      (P : Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue U) ζ) :
      Unbounded.OperatorDomainsSpec.resolventValue ζ (C0SemigroupSpec.generatorValue U) =
        P.inverse := by
    have hm : Nonempty (Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue U) ζ) := ⟨P⟩
    simp only [Unbounded.OperatorDomainsSpec.resolventValue, dite_eq_left hm]
    exact Unbounded.resolvent_inverse_unique ζ _ hm.some P
  have hQ : ∀ x, Tendsto (fun n => (Q n).inverse x) atTop (𝓝 (R.inverse x)) := by
    intro x
    have hh := h x
    change Tendsto (fun n => Unbounded.OperatorDomainsSpec.resolventValue ζ
      (C0SemigroupSpec.generatorValue (S n)) x) _
      (𝓝 (Unbounded.OperatorDomainsSpec.resolventValue ζ (C0SemigroupSpec.generatorValue T) x)) at hh
    simpa only [hcanon T R, hcanon _ (Q _)] using hh
  have hM : 0 ≤ M := le_trans zero_le_one hT.1
  have hQR n : ‖(Q n).inverse‖ ≤ M / (r - ω) := by
    simpa [ζ] using
      ((LaplaceResolvent.resolvent_powers (S n) M ω ζ (hb n) hr' (Q n) 0).2)
  have hRR : ‖R.inverse‖ ≤ M / (r - ω) := by
    simpa [ζ] using
      ((LaplaceResolvent.resolvent_powers T M ω ζ hT hr' R 0).2)
  have hcompact (K : Set X) (hK : IsCompact K) :=
    uniform_on_compact (fun n => (Q n).inverse) R.inverse
      (div_nonneg hM (sub_pos.mpr hr).le) hQR hRR hQ hK
  intro x b hb0
  let C := M * Real.exp (|ω| * b)
  have hC : 0 ≤ C := mul_nonneg hM (Real.exp_pos _).le
  have hCS n (t : ℝ) (ht : t ∈ Icc 0 b) : ‖(S n).operators t.toNNReal‖ ≤ C := by
    apply interval_bound (S n) (hb n)
    simpa only [Real.coe_toNNReal _ ht.1] using ht.2
  have hCT (t : ℝ) (ht : t ∈ Icc 0 b) : ‖T.operators t.toNNReal‖ ≤ C := by
    apply interval_bound T hT
    simpa only [Real.coe_toNNReal _ ht.1] using ht.2
  have hdR := resolvent_denseRange T ζ R
  have hdRR := hdR.comp hdR R.inverse.continuous
  apply uniform_of_dense_range S T (R.inverse ∘ R.inverse) hdRR hC hCS hCT _ x
  intro y
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ := ε / (2 * (C + C * b + 1))
  have hden : 0 < C + C * b + 1 := by positivity
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hev (v : X) : ∀ᶠ n in atTop, ∀ s ∈ Icc (0 : ℝ) b,
      ‖R.inverse (T.operators s.toNNReal v) - (Q n).inverse (T.operators s.toNNReal v)‖ < δ := by
    have hu := hcompact _ ((isCompact_Icc : IsCompact (Icc (0 : ℝ) b)).image (T.continuous_real_orbit v))
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu δ hδ] with n hn s hs
    simpa only [dist_eq_norm] using hn _ ⟨s, hs, rfl⟩
  filter_upwards [hev y, hev (R.inverse y)] with n hn hnR t ht
  have h0 := hnR 0 ⟨le_rfl, hb0⟩
  simp only [Real.toNNReal_zero, T.zero_apply] at h0
  have h1 : ‖(S n).operators t.toNNReal (R.inverse (R.inverse y)) -
      (S n).operators t.toNNReal ((Q n).inverse (R.inverse y))‖ ≤ C * δ := by
    rw [← map_sub]
    exact ((S n).operators _).le_opNorm _ |>.trans
      (mul_le_mul (hCS n t ht) h0.le (norm_nonneg _) hC)
  have h2 : ‖(S n).operators t.toNNReal ((Q n).inverse (R.inverse y)) -
      (Q n).inverse (R.inverse (T.operators t.toNNReal y))‖ ≤ C * δ * b := by
    have he := resolvent_comparison_bound (S n) T ζ (Q n) R y t.toNNReal hC
      (fun u hu => interval_bound (S n) (hb n) u
        ((show (u : ℝ) ≤ (t.toNNReal : ℝ) from hu).trans
          (by simpa only [Real.coe_toNNReal _ ht.1] using ht.2)))
      (fun s hs => (hn s ⟨hs.1, hs.2.trans
        (by simpa only [Real.coe_toNNReal _ ht.1] using ht.2)⟩).le)
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hδ.le)
    simpa only [Real.coe_toNNReal _ ht.1] using ht.2
  have h3 : ‖(Q n).inverse (R.inverse (T.operators t.toNNReal y)) -
      T.operators t.toNNReal (R.inverse (R.inverse y))‖ ≤ δ := by
    rw [resolvent_semigroup_commute T ζ R]
    have hh := (hnR t ht).le
    rw [resolvent_semigroup_commute T ζ R] at hh
    simpa only [norm_sub_rev] using hh
  rw [dist_eq_norm, norm_sub_rev]
  change ‖(S n).operators t.toNNReal (R.inverse (R.inverse y)) -
    T.operators t.toNNReal (R.inverse (R.inverse y))‖ < ε
  calc
    _ ≤ ‖(S n).operators t.toNNReal (R.inverse (R.inverse y)) -
          (S n).operators t.toNNReal ((Q n).inverse (R.inverse y))‖ +
        ‖(S n).operators t.toNNReal ((Q n).inverse (R.inverse y)) -
          (Q n).inverse (R.inverse (T.operators t.toNNReal y))‖ +
        ‖(Q n).inverse (R.inverse (T.operators t.toNNReal y)) -
          T.operators t.toNNReal (R.inverse (R.inverse y))‖ := by
      simpa only [dist_eq_norm] using dist_triangle4
        ((S n).operators t.toNNReal (R.inverse (R.inverse y)))
        ((S n).operators t.toNNReal ((Q n).inverse (R.inverse y)))
        ((Q n).inverse (R.inverse (T.operators t.toNNReal y)))
        (T.operators t.toNNReal (R.inverse (R.inverse y)))
    _ ≤ C * δ + C * δ * b + δ := add_le_add (add_le_add h1 h2) h3
    _ = ε / 2 := by dsimp [δ]; field_simp [ne_of_gt hden]
    _ < ε := by linarith


/-- Strong convergence of one real resolvent above ω is equivalent to locally
uniform strong semigroup convergence, with one common growth bound. -/
theorem common_growth_equivalence : CommonGrowthEquivalence (𝕜 := 𝕜) (X := X) := by
  intro S T M ω hT hS r hr
  exact ⟨semigroup_convergence_of_resolvent S T M ω hT hS r hr,
    fun h => resolvent_convergence_of_semigroup S T M ω hT hS h r hr⟩

/-- Existence of one convergent real resolvent, uniform strong semigroup
convergence, and convergence of all real resolvents above ω are equivalent. -/
theorem one_every_resolvent : OneEveryResolvent (𝕜 := 𝕜) (X := X) := by
  intro S T M ω hT hS
  have he := common_growth_equivalence S T M ω hT hS
  constructor
  · constructor
    · rintro ⟨r, hr, h⟩
      exact (he r hr).mp h
    · intro h
      exact ⟨ω + 1, by linarith, (he (ω + 1) (by linarith)).mpr h⟩
  · constructor
    · intro h r hr
      exact (he r hr).mpr h
    · intro h
      exact (he (ω + 1) (by linarith)).mp (h (ω + 1) (by linarith))

/-- The original contraction-semigroup formulation, including convergence at
some and at every positive real resolvent parameter. -/
theorem contraction_equivalence : ContractionEquivalence (𝕜 := 𝕜) (X := X) := by
  intro S T hT hS
  apply one_every_resolvent S T 1 0
  · exact ⟨le_rfl, by simpa only [zero_mul, Real.exp_zero, mul_one] using hT⟩
  · exact ⟨le_rfl, by simpa only [zero_mul, Real.exp_zero, mul_one] using hS⟩

end ExpandedFA.Semigroups.TrotterKatoApproximation
