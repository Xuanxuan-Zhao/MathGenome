import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.SecantError
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.Definitions
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.LagrangeRemainder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
namespace NumAnalysis206.Newton
open Set Filter Polynomial
open scoped Topology
open NumAnalysis206.Approximation
open Specs.NumAnalysis206.Newton (secantSlopeValue secantStepValue)

/-- A polynomial of degree at most n has constant nth derivative, including when
its actual degree is smaller than n. -/
theorem polynomial_iterated_derivative_constant (q : ℝ[X]) (n : ℕ)
    (hq : q.degree < ((n + 1 : ℕ) : WithBot ℕ)) :
    derivative^[n] q = C ((n.factorial : ℝ) * q.coeff n) := by
  have hd : q.natDegree ≤ n := by
    by_cases hz : q = 0
    · simp [hz]
    · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hz).mpr hq)
  have he : (derivative^[n] q).natDegree = 0 := by
    have := natDegree_iterate_derivative q n
    omega
  rw [eq_C_of_natDegree_eq_zero he, coeff_iterate_derivative]
  simp [Nat.descFactorial_self, nsmul_eq_mul]

/-- Mean-value representation of the canonical divided difference on a list of
n+1 distinct real nodes, in the finite convex hull of those nodes. -/
theorem dividedDifference_mean_value {a b : ℝ} {n : ℕ} {f : ℝ → ℝ}
    {D : ℕ → ℝ → ℝ} (hD : IntervalJet a b n f D) (l : List (ℝ × ℝ))
    (hlen : l.length = n + 1) (hx : (l.map Prod.fst).Nodup)
    (hmem : ∀ z ∈ l, z.1 ∈ Icc a b) (hval : ∀ z ∈ l, z.2 = f z.1) :
    ∃ ξ ∈ convexHull ℝ ((l.map Prod.fst).toFinset : Set ℝ),
      dividedDifference l = D n ξ / n.factorial := by
  classical
  let q := listInterpolant l
  let S := (l.map Prod.fst).toFinset
  have hne : l ≠ [] := by intro h; simp [h] at hlen
  have hcard : S.card = n + 1 := by
    rw [List.toFinset_card_of_nodup hx, List.length_map, hlen]
  have hSmem : ∀ t ∈ S, t ∈ Icc a b := by
    intro t ht
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
    exact hmem z hz
  have hab : a ≤ b := by
    obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil l hne
    exact (hmem z hz).1.trans (hmem z hz).2
  have hzero : ∀ t ∈ S, D 0 t - (derivative^[0] q).eval t = 0 := by
    intro t ht
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
    rw [hD.1 (hmem z hz)]
    simpa [q, listInterpolant_eval l hx z hz] using (sub_eq_zero.mpr (hval z hz).symm)
  obtain ⟨ξ, hξ, heq⟩ := exists_jet_zero_finset S hab hcard
    (jet_sub_polynomial hD q) hSmem hzero
  refine ⟨ξ, hξ, ?_⟩
  have hq : q.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    simpa [q, hlen] using listInterpolant_degree l hx
  change D n ξ - (derivative^[n] q).eval ξ = 0 at heq
  rw [polynomial_iterated_derivative_constant q n hq, eval_C] at heq
  rw [dividedDifference_eq_coeff l hne hx]
  simp only [hlen, Nat.add_sub_cancel]
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  exact (eq_div_iff hf).mpr (by nlinarith [heq])

theorem secant_error_identity : Specs.NumAnalysis206.Newton.SecantError.errorIdentity := by
  intro f p u v hp huv hup hvp hs
  have huv' : v - u ≠ 0 := sub_ne_zero.mpr huv.symm
  have hup' : p - u ≠ 0 := sub_ne_zero.mpr hup.symm
  have hvp' : p - v ≠ 0 := sub_ne_zero.mpr hvp.symm
  change v - f v / secantSlopeValue f u v - p = _
  change _ = (dividedDifference [(u, f u), (v, f v), (p, f p)] /
    secantSlopeValue f u v) * (v - p) * (u - p)
  rw [show dividedDifference [(u, f u), (v, f v), (p, f p)] =
      (secantSlopeValue f v p - secantSlopeValue f u v) / (p - u) by
    exact dividedDifference_recursion (u, f u) (p, f p) [(v, f v)]]
  have heq : secantSlopeValue f u v * (v - u) = f v - f u := by
    rw [secantSlope_eq_div, div_mul_cancel₀ _ huv']
  rw [secantSlope_eq_div f v p, hp]
  field_simp [hs, hup', hvp']
  ring

theorem secantStep_of_root : Specs.NumAnalysis206.Newton.SecantError.stepOfRoot := by
  intro f u v hv
  change v - f v / secantSlopeValue f u v = v
  simp [hv]

theorem secantStep_ne_current : Specs.NumAnalysis206.Newton.SecantError.stepNeCurrent := by
  intro f u v hv hs heq
  change v - f v / secantSlopeValue f u v = v at heq
  exact (div_ne_zero hv hs) (by linarith)

/-- The convex-hull witness remains in the interval on which the jet is supplied. -/
theorem dividedDifference_mean_value_interval {a b : ℝ} {n : ℕ} {f : ℝ → ℝ}
    {D : ℕ → ℝ → ℝ} (hD : IntervalJet a b n f D) (l : List (ℝ × ℝ))
    (hlen : l.length = n + 1) (hx : (l.map Prod.fst).Nodup)
    (hmem : ∀ z ∈ l, z.1 ∈ Icc a b) (hval : ∀ z ∈ l, z.2 = f z.1) :
    ∃ ξ ∈ Icc a b, dividedDifference l = D n ξ / n.factorial := by
  obtain ⟨ξ, hξ, heq⟩ := dividedDifference_mean_value hD l hlen hx hmem hval
  refine ⟨ξ, ?_, heq⟩
  apply convexHull_min (t := Icc a b) ?_ (convex_Icc a b) hξ
  intro t ht
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
  exact hmem z hz

theorem secant_slope_lower : Specs.NumAnalysis206.Newton.SecantError.slopeLower := by
  intro f D a b m u v hD hm hu hv huv
  obtain ⟨ξ, hξ, heq⟩ := dividedDifference_mean_value_interval
    (jet_truncate (by decide : 1 ≤ 2) hD) [(u, f u), (v, f v)] rfl
    (by simpa using huv) (by simpa using And.intro hu hv) (by simp)
  have heq' : secantSlopeValue f u v = D 1 ξ := by
    change dividedDifference [(u, f u), (v, f v)] = _
    simpa using heq
  rw [heq']
  exact hm ξ hξ

theorem secant_error_bound : Specs.NumAnalysis206.Newton.SecantError.errorBound := by
  intro f D a b m M p u v hD hp hm hM hbound hpm hu hv huv hup hvp
  have hs := secant_slope_lower f D a b m u v hD (fun t ht => (hbound t ht).1) hu hv huv
  have hspos : 0 < |secantSlopeValue f u v| := hm.trans_le hs
  have hsne : secantSlopeValue f u v ≠ 0 := abs_pos.mp hspos
  obtain ⟨ξ, hξ, heq⟩ := dividedDifference_mean_value_interval hD
    [(u, f u), (v, f v), (p, f p)] rfl
    (by simpa [List.nodup_cons] using And.intro (And.intro huv hup) hvp)
    (by simpa using And.intro hu (And.intro hv hpm)) (by simp)
  have heq' : dividedDifference [(u, f u), (v, f v), (p, f p)] = D 2 ξ / 2 := by
    simpa using heq
  rw [secant_error_identity f p u v hp huv hup hvp hsne]
  change |(dividedDifference [(u, f u), (v, f v), (p, f p)] /
    secantSlopeValue f u v) * (v - p) * (u - p)| ≤ _
  rw [heq', mul_assoc, abs_mul, abs_div, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  calc
    |D 2 ξ| / 2 / |secantSlopeValue f u v| ≤ M / 2 / |secantSlopeValue f u v| :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (hbound ξ hξ).2 (by norm_num))
        hspos.le
    _ ≤ M / 2 / m := div_le_div_of_nonneg_left (by positivity) hm hs
    _ = M / (2 * m) := by ring

/-- Continuity of the jet and mean-value witnesses in arbitrarily small hulls
imply convergence of divided differences when all their nodes coalesce. -/
theorem dividedDifference_tendsto {a b p : ℝ} {k : ℕ} {f : ℝ → ℝ}
    {D : ℕ → ℝ → ℝ} (hD : IntervalJet a b k f D) (hp : p ∈ Icc a b)
    (l : ℕ → List (ℝ × ℝ))
    (hdata : ∀ᶠ i in atTop, (l i).length = k + 1 ∧ ((l i).map Prod.fst).Nodup ∧
      (∀ z ∈ l i, z.1 ∈ Icc a b) ∧ (∀ z ∈ l i, z.2 = f z.1))
    (hclose : ∀ δ > 0, ∀ᶠ i in atTop, ∀ z ∈ l i, dist z.1 p < δ) :
    Tendsto (fun i => dividedDifference (l i)) atTop (𝓝 (D k p / k.factorial)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hc : ContinuousWithinAt (fun t => D k t / (k.factorial : ℝ)) (Icc a b) p :=
    (hD.2.1 k le_rfl p hp).div_const _
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousWithinAt_iff.mp hc ε hε
  filter_upwards [hdata, hclose δ hδ] with i hi hnear
  obtain ⟨ξ, hξ, heq⟩ := dividedDifference_mean_value hD (l i) hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hξmem : ξ ∈ Icc a b := by
    apply convexHull_min (t := Icc a b) ?_ (convex_Icc a b) hξ
    intro t ht
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
    exact hi.2.2.1 z hz
  have hξnear : dist ξ p < δ := by
    change ξ ∈ Metric.ball p δ
    apply convexHull_min (t := Metric.ball p δ) ?_ (convex_ball p δ) hξ
    intro t ht
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
    exact hnear z hz
  rw [heq]
  exact hcont hξmem hξnear

theorem secant_local_bounds : Specs.NumAnalysis206.Newton.SecantError.localBounds := by
  intro f p hf hn
  have h1 : ContDiffAt ℝ 1 (deriv f) p := hf.derivWithin (by norm_num)
  have h2 : ContDiffAt ℝ 0 (deriv (deriv f)) p := h1.derivWithin (by norm_num)
  have hm : 0 < |deriv f p| / 2 := half_pos (abs_pos.mpr hn)
  have hl : ∀ᶠ t in 𝓝 p, |deriv f p| / 2 < |deriv f t| :=
    h1.continuousAt.abs (Ioi_mem_nhds (by linarith [abs_pos.mpr hn]))
  have hu : ∀ᶠ t in 𝓝 p, |deriv (deriv f) t| < |deriv (deriv f) p| + 1 :=
    h2.continuousAt.abs (Iio_mem_nhds (by linarith))
  have hevent : ∀ᶠ t in 𝓝 p, ContDiffAt ℝ 2 f t ∧
      |deriv f p| / 2 < |deriv f t| ∧ |deriv (deriv f) t| < |deriv (deriv f) p| + 1 := by
    filter_upwards [hf.eventually (by norm_num), hl, hu] with t ht hlt hut
    exact ⟨ht, hlt, hut⟩
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hevent
  have hlocal (t : ℝ) (ht : t ∈ Icc (p - ε / 2) (p + ε / 2)) :
      ContDiffAt ℝ 2 f t ∧ |deriv f p| / 2 < |deriv f t| ∧
        |deriv (deriv f) t| < |deriv (deriv f) p| + 1 := by
    apply hsub
    change dist t p < ε
    rw [Real.dist_eq]
    have : |t - p| ≤ ε / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    linarith
  refine ⟨ε / 2, |deriv f p| / 2, |deriv (deriv f) p| + 1,
    half_pos hε, hm, by positivity, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro t ht
      simp
    · intro j hj t ht
      have hc := (hlocal t ht).1.continuousAt_iteratedFDeriv (k := j) (by exact_mod_cast hj)
      have hc' : ContinuousAt (iteratedDeriv j f) t := by
        rw [iteratedDeriv_eq_equiv_comp]
        exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin j) ℝ).symm.continuous.continuousAt.comp hc
      exact hc'.continuousWithinAt
    · intro j hj t ht
      have hd := (hlocal t ht).1.differentiableAt_iteratedFDeriv (m := j) (by exact_mod_cast hj)
      have hd' : DifferentiableAt ℝ (iteratedDeriv j f) t := by
        simpa only [iteratedDeriv_eq_equiv_comp,
          LinearIsometryEquiv.comp_differentiableAt_iff] using hd
      change HasDerivWithinAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f t) _ t
      rw [iteratedDeriv_succ]
      exact hd'.hasDerivAt.hasDerivWithinAt
  · intro t ht
    exact ⟨(hlocal t ht).2.1.le, (hlocal t ht).2.2.le⟩

theorem secant_coefficient_limit : Specs.NumAnalysis206.Newton.SecantError.coefficientLimit := by
  intro f p hf hp hn u v hu hv hdistinct
  obtain ⟨R, m, M, hR, hm, hM, hD, hbound⟩ := secant_local_bounds f p hf hn
  have hpm : p ∈ Icc (p - R) (p + R) := ⟨by linarith, by linarith⟩
  have hI : Icc (p - R) (p + R) ∈ 𝓝 p := Icc_mem_nhds (by linarith) (by linarith)
  have humem := hu.eventually hI
  have hvmem := hv.eventually hI
  have hfirst := dividedDifference_tendsto (jet_truncate (by decide : 1 ≤ 2) hD) hpm
    (fun i => [(u i, f (u i)), (v i, f (v i))]) (by
      filter_upwards [humem, hvmem, hdistinct] with i hui hvi hdi
      refine ⟨rfl, ?_, ?_, ?_⟩
      · simpa using hdi.1
      · simpa using And.intro hui hvi
      · simp) (by
      intro δ hδ
      filter_upwards [Metric.tendsto_nhds.mp hu δ hδ, Metric.tendsto_nhds.mp hv δ hδ]
        with i hui hvi
      simpa using And.intro hui hvi)
  have hsecond := dividedDifference_tendsto hD hpm
    (fun i => [(u i, f (u i)), (v i, f (v i)), (p, f p)]) (by
      filter_upwards [humem, hvmem, hdistinct] with i hui hvi hdi
      refine ⟨rfl, ?_, ?_, ?_⟩
      · simpa [List.nodup_cons] using And.intro (And.intro hdi.1 hdi.2.1) hdi.2.2
      · simpa using And.intro hui (And.intro hvi hpm)
      · simp) (by
      intro δ hδ
      filter_upwards [Metric.tendsto_nhds.mp hu δ hδ, Metric.tendsto_nhds.mp hv δ hδ]
        with i hui hvi
      simpa [hδ] using And.intro hui hvi)
  have ht1 : Tendsto (fun i => secantSlopeValue f (u i) (v i)) atTop (𝓝 (deriv f p)) := by
    simpa [secantSlopeValue, dividedDifference] using hfirst
  have ht2 : Tendsto (fun i => dividedDifference
      [(u i, f (u i)), (v i, f (v i)), (p, f p)]) atTop (𝓝 (deriv (deriv f) p / 2)) := by
    simpa [iteratedDeriv_succ] using hsecond
  have ht := (ht2.div ht1 hn).abs
  simpa only [dividedDifference, Pi.div_apply, div_div] using ht

theorem secant_local_estimates : Specs.NumAnalysis206.Newton.SecantError.localEstimates := by
  intro f p hf hp hn
  obtain ⟨R, m, M, hR, hm, hM, hD, hbound⟩ := secant_local_bounds f p hf hn
  have hbound' : ∀ t ∈ Icc (p - R) (p + R),
      m ≤ |iteratedDeriv 1 f t| ∧ |iteratedDeriv 2 f t| ≤ M := by
    simpa [iteratedDeriv_succ] using hbound
  refine ⟨R, m, M, hR, hm, hM, ?_⟩
  intro u hu v hv huv hup hvp
  have hs := secant_slope_lower f (fun j => iteratedDeriv j f) (p - R) (p + R) m u v
    hD (fun t ht => (hbound' t ht).1) hu hv huv
  have hsne : secantSlopeValue f u v ≠ 0 := abs_pos.mp (hm.trans_le hs)
  refine ⟨hs, secant_error_identity f p u v hp huv hup hvp hsne, ?_⟩
  exact secant_error_bound f (fun j => iteratedDeriv j f) (p - R) (p + R) m M p u v
    hD hp hm hM hbound' ⟨by linarith, by linarith⟩ hu hv huv hup hvp

end NumAnalysis206.Newton
