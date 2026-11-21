import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.PeriodicMultipliers
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.LinearizedStability
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.LinearizedInstability
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

noncomputable section
open Module Filter Function Set Metric
open scoped Topology
namespace D13Unified.Ch15.PeriodicMultipliers
open D13Unified.Ch15.DiscreteDefinitions

lemma finiteOrbit_nonempty {X : Type*} (F : X → X) (p : X) {m : ℕ} (hm : 0 < m) :
    (finiteOrbit F p m).Nonempty :=
  ⟨p, ⟨⟨0, hm⟩, rfl⟩⟩

lemma finiteOrbit_finite {X : Type*} (F : X → X) (p : X) (m : ℕ) :
    (finiteOrbit F p m).Finite := Set.finite_range _

lemma mem_finiteOrbit_iterate {X : Type*} {F : X → X} {p : X} {m : ℕ}
    (hm : 0 < m) (hp : IsPeriodicPt F m p) (n : ℕ) : F^[n] p ∈ finiteOrbit F p m :=
  ⟨⟨n % m, Nat.mod_lt _ hm⟩, hp.iterate_mod_apply n⟩

lemma contDiffAt_iterate_orbit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} {p : E} {m : ℕ} (hm : 0 < m) (hp : IsPeriodicPt F m p)
    (hF : ∀ z ∈ finiteOrbit F p m, ContDiffAt ℝ 1 F z) (j n : ℕ) :
    ContDiffAt ℝ 1 (F^[n]) (F^[j] p) := by
  induction n with
  | zero => simpa using (contDiffAt_id : ContDiffAt ℝ 1 (id : E → E) (F^[j] p))
  | succ n ih =>
    rw [Function.iterate_succ']
    apply ContDiffAt.comp _ _ ih
    rw [← Function.iterate_add_apply]
    exact hF _ (mem_finiteOrbit_iterate hm hp _)

lemma local_lipschitz_radial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : E → E} {p : E} (hG : ContDiffAt ℝ 1 G p) :
    ∃ L : ℝ, 0 < L ∧ ∃ r : ℝ, 0 < r ∧ ∀ x, dist x p < r →
      dist (G x) (G p) ≤ L * dist x p := by
  obtain ⟨K, V, hV, hLip⟩ := hG.exists_lipschitzOnWith
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨(K : ℝ) + 1, by positivity, r, hr, fun x hx => ?_⟩
  exact (hLip.dist_le_mul x (hrV hx) p (mem_of_mem_nhds hV)).trans
    (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)

/-- A quantitative set estimate implies both set stability and attraction. -/
lemma set_stability_of_exponential_estimate {X : Type*} [MetricSpace X]
    {F : X → X} {O : Set X} (h : SetExponentiallyAttracting F O) :
    SetLyapunovStable F O ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, infDist x O < δ →
      Tendsto (fun n : ℕ => infDist (F^[n] x) O) atTop (𝓝 0) := by
  obtain ⟨C, hC, q, hq, hq1, δ, hδ, hbound⟩ := h
  constructor
  · intro ε hε
    refine ⟨min δ (ε / C), lt_min hδ (div_pos hε hC), fun x hx n => ?_⟩
    calc
      _ ≤ C * q ^ n * infDist x O := hbound x (hx.trans_le (min_le_left _ _)) n
      _ ≤ C * infDist x O := mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right hC.le (pow_le_one₀ hq.le hq1.le)) infDist_nonneg
      _ < ε := by
        have := (lt_div_iff₀ hC).mp (hx.trans_le (min_le_right _ _))
        nlinarith
  · refine ⟨δ, hδ, fun x hx => ?_⟩
    apply squeeze_zero (fun n => infDist_nonneg) (hbound x hx)
    simpa using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1).const_mul C).mul_const (infDist x O)

/-- Uniform radial Lipschitz bounds for finitely many local C¹ maps. -/
lemma uniform_local_radial {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (G : ι → E → E) (p : ι → E)
    (hG : ∀ i ∈ s, ContDiffAt ℝ 1 (G i) (p i)) :
    ∃ L : ℝ, 0 < L ∧ ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, ∀ x, dist x (p i) < r →
      dist (G i x) (G i (p i)) ≤ L * dist x (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, 1, by norm_num, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨L₁, hL₁, r₁, hr₁, h₁⟩ := local_lipschitz_radial (hG i (by simp))
    obtain ⟨L₂, hL₂, r₂, hr₂, h₂⟩ := ih (fun j hj => hG j (by simp [hj]))
    refine ⟨max L₁ L₂, hL₁.trans_le (le_max_left _ _),
      min r₁ r₂, lt_min hr₁ hr₂, fun j hj x hx => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (h₁ x (hx.trans_le (min_le_left _ _))).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)
    · exact (h₂ j hj x (hx.trans_le (min_le_right _ _))).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg)

lemma finite_iterate_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} {p : E} {m : ℕ} (hm : 0 < m) (hp : IsPeriodicPt F m p)
    (hF : ∀ z ∈ finiteOrbit F p m, ContDiffAt ℝ 1 F z) :
    ∃ L : ℝ, 0 < L ∧ ∃ r : ℝ, 0 < r ∧ ∀ i : Fin m, ∀ j : ℕ, j ≤ m →
      ∀ x, dist x (F^[i.val] p) < r →
        dist (F^[j] x) (F^[j] (F^[i.val] p)) ≤ L * dist x (F^[i.val] p) := by
  obtain ⟨L, hL, r, hr, hbound⟩ := uniform_local_radial
    (Finset.univ : Finset (Fin m × Fin (m + 1)))
    (fun ij => F^[ij.2.val]) (fun ij => F^[ij.1.val] p)
    (fun ij _ => contDiffAt_iterate_orbit hm hp hF _ _)
  exact ⟨L, hL, r, hr, fun i j hj x hx =>
    hbound (i, ⟨j, by omega⟩) (Finset.mem_univ _) x hx⟩

/-- Converting a geometric rate per period to a rate per iterate, allowing
two bounded portions of a period for entry and remainder. -/
lemma rate_per_iterate {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {m : ℕ} (hm : 0 < m) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ n k : ℕ, n ≤ m * k + 2 * m →
      a ^ k ≤ q ^ n / q ^ (2 * m) := by
  let q : ℝ := a ^ ((m : ℝ)⁻¹)
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hq : 0 < q := Real.rpow_pos_of_pos ha _
  have hq1 : q < 1 := (Real.rpow_inv_lt_iff_of_pos ha.le zero_lt_one.le hmR).mpr (by simpa)
  have hqm : q ^ m = a := Real.rpow_inv_natCast_pow ha.le hm.ne'
  refine ⟨q, hq, hq1, fun n k hn => ?_⟩
  apply (le_div_iff₀ (pow_pos hq _)).mpr
  calc
    a ^ k * q ^ (2 * m) = q ^ (m * k + 2 * m) := by rw [← hqm, ← pow_mul, ← pow_add]
    _ ≤ q ^ n := pow_le_pow_of_le_one hq.le hq1.le hn

/-- Lift an exponential return-map estimate at one phase to a distance
estimate for the whole finite periodic orbit. -/
lemma set_exponential_of_return_estimate {E : Type*} [NormedAddCommGroup E]
    {F : E → E} {p : E} {m : ℕ} (hm : 0 < m) (hp : IsPeriodicPt F m p)
    (hreturn : LocallyExponentiallyStable (F^[m]) p)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hlip : ∀ i : Fin m, ∀ j : ℕ, j ≤ m → ∀ x,
      dist x (F^[i.val] p) < r →
      dist (F^[j] x) (F^[j] (F^[i.val] p)) ≤ L * dist x (F^[i.val] p)) :
    SetExponentiallyAttracting F (finiteOrbit F p m) := by
  obtain ⟨C, hC, a, ha, ha1, δ, hδ, hreturn⟩ := hreturn
  have hret : ∀ y, dist y p < δ → ∀ k : ℕ,
      dist ((F^[m])^[k] y) p ≤ C * a ^ k * dist y p := by
    simpa only [dist_eq_norm] using hreturn
  obtain ⟨q, hq, hq1, hrate⟩ := rate_per_iterate ha ha1 hm
  let K := max L (L * C * L)
  have hK : 0 < K := hL.trans_le (le_max_left _ _)
  let η := min r (min (δ / L) (r / (C * L)))
  have hη : 0 < η := lt_min hr (lt_min (div_pos hδ hL) (div_pos hr (mul_pos hC hL)))
  refine ⟨K / q ^ (2 * m), div_pos hK (pow_pos hq _), q, hq, hq1, η, hη,
    fun x hx n => ?_⟩
  obtain ⟨z, hz, hdist⟩ := (finiteOrbit_finite F p m).isCompact.exists_infDist_eq_dist
    (finiteOrbit_nonempty F p hm) x
  obtain ⟨i, rfl⟩ := hz
  have hxη : dist x (F^[i.val] p) < η := by rwa [hdist] at hx
  have hxr : dist x (F^[i.val] p) < r := hxη.trans_le (min_le_left _ _)
  have hxδ : L * dist x (F^[i.val] p) < δ := by
    have := (lt_div_iff₀ hL).mp
      (hxη.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith
  have hxCr : C * L * dist x (F^[i.val] p) < r := by
    have := (lt_div_iff₀ (mul_pos hC hL)).mp
      (hxη.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith
  have hpieces : ∃ k : ℕ, n ≤ m * k + 2 * m ∧
      infDist (F^[n] x) (finiteOrbit F p m) ≤ K * a ^ k * dist x (F^[i.val] p) := by
    by_cases hn : n < m - i.val
    · refine ⟨0, by omega, ?_⟩
      have hz : F^[n] (F^[i.val] p) ∈ finiteOrbit F p m := by
        rw [← Function.iterate_add_apply]
        exact mem_finiteOrbit_iterate hm hp _
      calc
        _ ≤ dist (F^[n] x) (F^[n] (F^[i.val] p)) := infDist_le_dist_of_mem hz
        _ ≤ L * dist x (F^[i.val] p) := hlip i n (by omega) x hxr
        _ ≤ K * a ^ 0 * dist x (F^[i.val] p) := by
          simpa only [pow_zero, mul_one] using
            mul_le_mul_of_nonneg_right (le_max_left L (L * C * L)) dist_nonneg
    · let t := m - i.val
      let y := F^[t] x
      have htp : F^[t] (F^[i.val] p) = p := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel i.isLt.le]
        exact hp.eq
      have hy : dist y p ≤ L * dist x (F^[i.val] p) := by
        simpa only [htp] using hlip i t (Nat.sub_le _ _) x hxr
      have hyδ : dist y p < δ := hy.trans_lt hxδ
      let k := (n - t) / m
      let j := (n - t) % m
      have hj : j < m := Nat.mod_lt _ hm
      have hdecomp : n = j + m * k + t := by
        have := Nat.mod_add_div (n - t) m
        have htn : t ≤ n := Nat.le_of_not_gt hn
        dsimp [j, k]
        omega
      have hnkm : n ≤ m * k + 2 * m := by
        have ht : t ≤ m := Nat.sub_le _ _
        omega
      have hk : dist ((F^[m])^[k] y) p ≤ C * a ^ k * dist y p := hret y hyδ k
      have hsmall : dist ((F^[m])^[k] y) p < r := by
        calc
          _ ≤ C * a ^ k * dist y p := hk
          _ ≤ C * dist y p := mul_le_mul_of_nonneg_right
            (mul_le_of_le_one_right hC.le (pow_le_one₀ ha.le ha1.le)) dist_nonneg
          _ ≤ C * (L * dist x (F^[i.val] p)) := mul_le_mul_of_nonneg_left hy hC.le
          _ < r := by nlinarith [hxCr]
      have hfull : F^[n] x = F^[j] ((F^[m])^[k] y) := by
        rw [hdecomp, Function.iterate_add_apply, Function.iterate_add_apply,
          Function.iterate_mul]
      have hlast := hlip (⟨0, hm⟩ : Fin m) j hj.le ((F^[m])^[k] y) (by simpa using hsmall)
      simp only [Function.iterate_zero_apply] at hlast
      refine ⟨k, hnkm, ?_⟩
      calc
        _ = infDist (F^[j] ((F^[m])^[k] y)) (finiteOrbit F p m) := by rw [hfull]
        _ ≤ dist (F^[j] ((F^[m])^[k] y)) (F^[j] p) :=
          infDist_le_dist_of_mem (mem_finiteOrbit_iterate hm hp _)
        _ ≤ L * dist ((F^[m])^[k] y) p := hlast
        _ ≤ L * (C * a ^ k * dist y p) := mul_le_mul_of_nonneg_left hk hL.le
        _ ≤ L * (C * a ^ k * (L * dist x (F^[i.val] p))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hy (mul_nonneg hC.le (pow_nonneg ha.le _))) hL.le
        _ = (L * C * L) * a ^ k * dist x (F^[i.val] p) := by ring
        _ ≤ K * a ^ k * dist x (F^[i.val] p) := by
          gcongr
          exact le_max_right _ _
  obtain ⟨k, hnk, hbound⟩ := hpieces
  calc
    _ ≤ K * a ^ k * dist x (F^[i.val] p) := hbound
    _ ≤ K * (q ^ n / q ^ (2 * m)) * dist x (F^[i.val] p) := by
      gcongr
      exact hrate n k hnk
    _ = K / q ^ (2 * m) * q ^ n * infDist x (finiteOrbit F p m) := by rw [hdist]; ring

/-- An isolated phase and a small first exit of the return map give an exit
from the entire finite set. Continuity bounds the overshoot, so the exiting
sample cannot land near a different phase. -/
lemma not_setStable_of_return_exits {E : Type} [NormedAddCommGroup E]
    (F : E → E) (p : E) (m : ℕ) (O : Set E) (hO : O.Finite) (hpO : p ∈ O)
    (hG : ContinuousAt (F^[m]) p) (hfix : F^[m] p = p)
    (hexit : ∀ V : Set E, IsOpen V → p ∈ V →
      D13Unified.Ch15.LinearizedInstability.LocallyUnstable (F^[m]) V p) :
    ¬ SetLyapunovStable F O := by
  have hclosed : IsClosed (O \ {p}) := (hO.subset sdiff_subset).isClosed
  have hnhds : (O \ {p})ᶜ ∈ 𝓝 p := hclosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨s, hs, hsep⟩ := Metric.mem_nhds_iff.mp hnhds
  have hdist : ∀ z ∈ O, z ≠ p → s ≤ dist z p := by
    intro z hz hzp
    by_contra h
    exact hsep (by simpa using (lt_of_not_ge h)) ⟨hz, hzp⟩
  have hnear : ∀ᶠ x in 𝓝 p, dist (F^[m] x) p < s / 2 := by
    simpa only [hfix] using (Metric.tendsto_nhds.mp hG) (s / 2) (half_pos hs)
  obtain ⟨t, ht, hstep⟩ := Metric.eventually_nhds_iff.mp hnear
  obtain ⟨ε, hε, _, hescape⟩ := hexit (Metric.ball p t) isOpen_ball (mem_ball_self ht)
  intro hstable
  obtain ⟨δ, hδ, hstay⟩ := hstable (min ε (s / 2)) (lt_min hε (half_pos hs))
  obtain ⟨x, _, hx, N, hN, hleave, hbefore⟩ := hescape δ hδ
  have hinput : (F^[m])^[N - 1] x ∈ Metric.ball p t :=
    (hbefore (N - 1) (by omega)).2
  have hlast : F^[m] ((F^[m])^[N - 1] x) = (F^[m])^[N] x := by
    rw [← Function.iterate_succ_apply' (F^[m]) (N - 1) x]
    congr 1
    omega
  have hsmall : dist ((F^[m])^[N] x) p < s / 2 := by
    rw [← hlast]
    exact hstep hinput
  have hlarge : min ε (s / 2) ≤ infDist ((F^[m])^[N] x) O := by
    apply (Metric.le_infDist ⟨p, hpO⟩).mpr
    intro z hz
    by_cases hzp : z = p
    · subst z
      exact (min_le_left _ _).trans (by simpa [dist_eq_norm] using hleave)
    · have htri := dist_triangle z ((F^[m])^[N] x) p
      have hfar := hdist z hz hzp
      rw [dist_comm z ((F^[m])^[N] x)] at htri
      exact (min_le_right _ _).trans (by linarith)
  have hinit : infDist x O < δ :=
    (infDist_le_dist_of_mem hpO).trans_lt (by simpa [dist_eq_norm] using hx)
  have hstay' := hstay x hinit (m * N)
  rw [Function.iterate_mul] at hstay'
  exact (not_lt_of_ge hlarge) hstay'

/-- The attracting multiplier alternative with one uniform estimate for all
initial phases and every natural-number iterate. -/
theorem periodicAttraction : Specs.D13Unified.Ch15.PeriodicMultipliers.periodicAttraction := by
  intro E _ _ _ d b F p m hperiod hF hspec
  have hG : ContDiffAt ℝ 1 (F^[m]) p := by
    simpa using contDiffAt_iterate_orbit hperiod.1 hperiod.2.1 hF 0 m
  obtain ⟨V, hV, hGV⟩ := hG.contDiffOn le_rfl (by simp)
  obtain ⟨U, hUV, hU, hpU⟩ := _root_.mem_nhds_iff.mp hV
  have hret : LocallyExponentiallyStable (F^[m]) p :=
    (D13Unified.Ch15.LinearizedStability.linearizedAttraction b (F^[m]) U p
      hU hpU (hGV.mono hUV) hperiod.2.1.eq hspec).2.1
  obtain ⟨L, hL, r, hr, hlip⟩ := finite_iterate_bounds hperiod.1 hperiod.2.1 hF
  have hexp := set_exponential_of_return_estimate hperiod.1 hperiod.2.1 hret hL hr hlip
  exact ⟨hexp, set_stability_of_exponential_estimate hexp⟩

/-- Periodic-orbit instability, with the overshoot kept in the distinguished
phase neighborhood rather than merely invoking fixed-point instability. -/
theorem periodicInstability : Specs.D13Unified.Ch15.PeriodicMultipliers.periodicInstability := by
  intro E _ _ _ d b F p m hperiod hF hspec
  have hG : ContDiffAt ℝ 1 (F^[m]) p := by
    simpa using contDiffAt_iterate_orbit hperiod.1 hperiod.2.1 hF 0 m
  apply not_setStable_of_return_exits F p m _ (finiteOrbit_finite F p m)
    ⟨⟨0, hperiod.1⟩, rfl⟩ hG.continuousAt hperiod.2.1.eq
  intro V hV hpV
  exact D13Unified.Ch15.LinearizedInstability.linearizedInstability b (F^[m]) V p
    (fderiv ℝ (F^[m]) p) hV hpV hperiod.2.1.eq hG hG.differentiableAt_one.hasFDerivAt hspec

end D13Unified.Ch15.PeriodicMultipliers
