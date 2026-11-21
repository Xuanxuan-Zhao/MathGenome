import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.LaxEquivalence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.SemigroupGrowthAndGenerator
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07UniformBoundedness
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.FieldSimp

noncomputable section
open Filter Topology Set
open scoped NNReal
namespace ExpandedFA.Semigroups.LaxEquivalence
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
open LaxSpec

lemma grid_of_converges {T : C0Semigroup 𝕜 X} {C : Steps 𝕜 X}
    (hc : Converges T C) : GridConverges T C := by
  intro x B ε hε
  obtain ⟨δ, hδ, hd⟩ := hc x B ε hε
  exact ⟨δ, hδ, fun h hh hhδ n hn => hd h hh hhδ n hn (n • h) hn (by simpa)⟩

/-- The corrected converse: a contradicting sequence of small steps would be a
pointwise bounded family with unbounded operator norms. -/
theorem grid_convergence_implies_stability {T : C0Semigroup 𝕜 X} {C : Steps 𝕜 X}
    (hc : GridConverges T C) : AsymptoticallyStable C := by
  classical
  intro B
  by_contra hn
  have bad : ∀ k : ℕ, ∃ h : ℝ≥0, ∃ n : ℕ,
      0 < h ∧ (h : ℝ) < 1 / ((k : ℝ) + 1) ∧ n • h ≤ B ∧
        (k : ℝ) + 1 < ‖(C h) ^ n‖ := by
    intro k
    by_contra hb
    push Not at hb
    apply hn
    refine ⟨1 / ((k : ℝ) + 1), (k : ℝ) + 1, by positivity, by positivity, ?_⟩
    intro h hh hhk n hnB
    exact hb h n hh hhk hnB
  choose u n hu using bad
  have hu0 : Tendsto (fun k => (u k : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun k => (u k).coe_nonneg) (fun k => (hu k).2.1.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have error_limit (x : X) : Tendsto
      (fun k => ((C (u k)) ^ (n k)) x - T.operators (n k • u k) x) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := hc x B ε hε
    have hev : ∀ᶠ k in atTop, (u k : ℝ) < δ := (tendsto_order.1 hu0).2 δ hδ
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    exact ⟨N, fun k hk => by
      simpa only [dist_zero_right] using hd (u k) (hu k).1 (hN k hk) (n k) (hu k).2.2.1⟩
  obtain ⟨K, hK, hTb⟩ := T.bounded_on_interval B
  have pointwise : ∀ x : X, ∃ M : ℝ, ∀ k : ℕ, ‖((C (u k)) ^ (n k)) x‖ ≤ M := by
    intro x
    obtain ⟨M, hM⟩ := (Metric.isBounded_range_of_tendsto _ (error_limit x)).exists_norm_le
    refine ⟨M + K * ‖x‖, fun k => ?_⟩
    calc
      _ ≤ ‖((C (u k)) ^ (n k)) x - T.operators (n k • u k) x‖ +
          ‖T.operators (n k • u k) x‖ := by
        convert norm_add_le (((C (u k)) ^ (n k)) x - T.operators (n k • u k) x)
          (T.operators (n k • u k) x) using 1; simp
      _ ≤ M + K * ‖x‖ := add_le_add (hM _ (mem_range_self k))
        (((T.operators _).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (hTb _ (hu k).2.2.1) (norm_nonneg x)))
  obtain ⟨M, _, hM⟩ := ExpandedFA.P1.C07UniformBoundedness.uniform_boundedness
    𝕜 X X ℕ (fun k => (C (u k)) ^ (n k)) pointwise
  obtain ⟨k, hk⟩ := exists_nat_gt M
  exact (not_lt_of_ge (hM k)) (lt_trans (by linarith : M < (k : ℝ) + 1) (hu k).2.2.2)

theorem necessity : LaxSpec.Necessity := by
  intro 𝕜 X _ _ _ _ T C hc
  exact grid_convergence_implies_stability (grid_of_converges hc)


/-- A discrete variation-of-constants estimate, with no commutation assumption
between the numerical step and the exact semigroup. -/
lemma telescoping_bound (T : C0Semigroup 𝕜 X) (C : X →L[𝕜] X)
    (h : ℝ≥0) (n : ℕ) (x : X) (M r : ℝ) (hM : 0 ≤ M)
    (hp : ∀ k : ℕ, k ≤ n → ‖C ^ k‖ ≤ M)
    (he : ∀ j : ℕ, j < n →
      ‖C (T.operators (j • h) x) - T.operators h (T.operators (j • h) x)‖ ≤ r) :
    ‖(C ^ n) x - T.operators (n • h) x‖ ≤ (n : ℝ) * (M * r) := by
  let v : ℕ → X := fun j => (C ^ (n - j)) (T.operators (j • h) x)
  have hv : ∀ j : ℕ, j < n → dist (v j) (v (j + 1)) ≤ M * r := by
    intro j hj
    have hpow : n - j = (n - (j + 1)) + 1 := by omega
    have hid : v j - v (j + 1) = (C ^ (n - (j + 1)))
        (C (T.operators (j • h) x) - T.operators h (T.operators (j • h) x)) := by
      dsimp [v]
      rw [hpow, pow_succ, mul_apply_eq_comp, map_sub]
      congr 1
      rw [← T.add_apply, succ_nsmul, add_comm h]
    rw [dist_eq_norm, hid]
    exact ((C ^ (n - (j + 1))).le_opNorm _).trans
      (mul_le_mul (hp _ (by omega)) (he j hj) (norm_nonneg _) hM)
  have hb := dist_le_range_sum_of_dist_le (f := v) n (fun {_} hj => hv _ hj)
  simpa [v, dist_eq_norm, Finset.sum_const, nsmul_eq_mul] using hb

/-- Turning quotient consistency into the uniform `o(h)` local error. The
semigroup quotient on an orbit is transported by `T(s)`, so only the generator
limit at the initial vector is needed for the exact step. -/
lemma uniform_local_error (T : C0Semigroup 𝕜 X) (C : Steps 𝕜 X)
    (hc : OrbitConsistent T C) (x : (generator T).domain) (B : ℝ≥0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ≥0, 0 < h → (h : ℝ) < δ →
      ∀ s : ℝ≥0, s ≤ B →
        ‖C h (T.operators s x) - T.operators h (T.operators s x)‖ ≤ (h : ℝ) * ε := by
  obtain ⟨K, hK, hTb⟩ := T.bounded_on_interval B
  have hKp : 0 < K := by linarith
  obtain ⟨δ₁, hδ₁, hd₁⟩ := hc x B (ε / 2) (by positivity)
  have hlim := generator_has_limit T x
  change Tendsto (fun h : ℝ => differenceQuotient T h x) (𝓝[>] 0) (𝓝 (generator T x)) at hlim
  obtain ⟨δ₂, hδ₂, hd₂⟩ := Metric.tendsto_nhdsWithin_nhds.mp
    hlim (ε / (2 * K)) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro h hh hhδ s hs
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hdC := hd₁ h hh (lt_of_lt_of_le hhδ (min_le_left _ _)) s hs
  have hdT : ‖differenceQuotient T (h : ℝ) x - generator T x‖ < ε / (2 * K) := by
    simpa only [dist_eq_norm, Real.toNNReal_coe] using
      hd₂ (show (h : ℝ) ∈ Ioi 0 from hhR)
        (by simpa [Real.dist_eq, abs_of_nonneg hhR.le] using
          lt_of_lt_of_le hhδ (min_le_right δ₁ δ₂))
  have hq : ‖quotient C h (T.operators s x) -
      differenceQuotient T (h : ℝ) (T.operators s x)‖ ≤ ε := by
    calc
      _ ≤ ‖quotient C h (T.operators s x) - T.operators s (generator T x)‖ +
          ‖T.operators s (generator T x) -
            differenceQuotient T (h : ℝ) (T.operators s x)‖ := by
        simpa only [dist_eq_norm] using dist_triangle
          (quotient C h (T.operators s x)) (T.operators s (generator T x))
          (differenceQuotient T (h : ℝ) (T.operators s x))
      _ ≤ ε / 2 + K * (ε / (2 * K)) := by
        apply add_le_add hdC.le
        rw [T.differenceQuotient_commute, ← map_sub]
        exact ((T.operators s).le_opNorm _).trans
          (mul_le_mul (hTb s hs) (by simpa only [norm_sub_rev] using hdT.le)
            (norm_nonneg _) (by linarith))
      _ = ε := by field_simp; ring
  have ha : (algebraMap ℝ 𝕜 (h : ℝ)) ≠ 0 :=
    (map_ne_zero (algebraMap ℝ 𝕜)).mpr hhR.ne'
  have hid : C h (T.operators s x) - T.operators h (T.operators s x) =
      (algebraMap ℝ 𝕜 (h : ℝ)) •
        (quotient C h (T.operators s x) -
          differenceQuotient T (h : ℝ) (T.operators s x)) := by
    change _ = (algebraMap ℝ 𝕜 (h : ℝ)) •
      ((algebraMap ℝ 𝕜 (h : ℝ))⁻¹ • (C h (T.operators s x) - T.operators s x) -
       (algebraMap ℝ 𝕜 (h : ℝ))⁻¹ •
         (T.operators (h : ℝ).toNNReal (T.operators s x) - T.operators s x))
    rw [Real.toNNReal_coe, smul_sub, smul_inv_smul₀ ha, smul_inv_smul₀ ha]
    abel
  rw [hid, norm_smul, norm_algebraMap', Real.norm_eq_abs, abs_of_nonneg hhR.le]
  exact mul_le_mul_of_nonneg_left hq hhR.le


lemma domain_grid_convergence (T : C0Semigroup 𝕜 X) (C : Steps 𝕜 X)
    (hs : Stable C) (hc : OrbitConsistent T C) (x : (generator T).domain)
    (B : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ≥0, 0 < h → (h : ℝ) < δ →
      ∀ n : ℕ, n • h ≤ B → ‖((C h) ^ n) x - T.operators (n • h) x‖ < ε := by
  obtain ⟨M, hM, hMb⟩ := hs B
  let η : ℝ := ε / ((M + 1) * ((B : ℝ) + 1))
  have hden : 0 < (M + 1) * ((B : ℝ) + 1) := by positivity
  have hη : 0 < η := div_pos hε hden
  obtain ⟨δ, hδ, hd⟩ := uniform_local_error T C hc x B η hη
  refine ⟨δ, hδ, ?_⟩
  intro h hh hhδ n hn
  have hnR : (n : ℝ) * (h : ℝ) ≤ B := by
    exact_mod_cast (show (n : ℝ≥0) * h ≤ B from by simpa only [nsmul_eq_mul] using hn)
  have hb := telescoping_bound T (C h) h n x M ((h : ℝ) * η) hM
    (fun k hk => hMb h hh k ((nsmul_le_nsmul_left (show 0 ≤ h from zero_le) hk).trans hn))
    (fun j hj => hd h hh hhδ (j • h)
      ((nsmul_le_nsmul_left (show 0 ≤ h from zero_le) hj.le).trans hn))
  calc
    _ ≤ (n : ℝ) * (M * ((h : ℝ) * η)) := hb
    _ = (M * ((n : ℝ) * (h : ℝ))) * η := by ring
    _ ≤ (M * (B : ℝ)) * η :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnR hM) hη.le
    _ < ((M + 1) * ((B : ℝ) + 1)) * η :=
      mul_lt_mul_of_pos_right (by nlinarith [B.coe_nonneg]) hη
    _ = ε := mul_div_cancel₀ ε hden.ne'

/-- Density extends the convergence from the exact generator domain to every
vector. Both numerical and exact operators have a common bound on this interval. -/
theorem stable_consistent_grid_convergence (T : C0Semigroup 𝕜 X) (C : Steps 𝕜 X)
    (hs : Stable C) (hc : OrbitConsistent T C) : GridConverges T C := by
  intro x B ε hε
  obtain ⟨M, hM, hMb⟩ := hs B
  obtain ⟨K, hK, hTb⟩ := T.bounded_on_interval B
  have hsum : 0 < M + K := by linarith
  obtain ⟨y, hy, hxy⟩ := T.generator_domain_dense.exists_dist_lt x
    (show 0 < ε / (2 * (M + K)) from div_pos hε (mul_pos (by norm_num) hsum))
  obtain ⟨δ, hδ, hd⟩ := domain_grid_convergence T C hs hc ⟨y, hy⟩ B (ε / 2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro h hh hhδ n hn
  have hp := hMb h hh n hn
  have ht := hTb (n • h) hn
  have he := hd h hh hhδ n hn
  have hid : ((C h) ^ n) x - T.operators (n • h) x =
      (((C h) ^ n) (x - y) + (((C h) ^ n) y - T.operators (n • h) y)) +
        T.operators (n • h) (y - x) := by
    simp only [map_sub]; abel
  have hxy' : ‖x - y‖ < ε / (2 * (M + K)) := by simpa only [dist_eq_norm] using hxy
  calc
    _ ≤ (M + K) * ‖x - y‖ + ‖((C h) ^ n) y - T.operators (n • h) y‖ := by
      rw [hid]
      calc
        _ ≤ (‖((C h) ^ n) (x - y)‖ + ‖((C h) ^ n) y - T.operators (n • h) y‖) +
            ‖T.operators (n • h) (y - x)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ (M * ‖x - y‖ + ‖((C h) ^ n) y - T.operators (n • h) y‖) + K * ‖x - y‖ := by
          apply add_le_add
          · apply add_le_add _ le_rfl
            exact (((C h) ^ n).le_opNorm _).trans
              (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
          · simpa only [norm_sub_rev] using ((T.operators (n • h)).le_opNorm (y - x)).trans
              (mul_le_mul_of_nonneg_right ht (norm_nonneg _))
        _ = _ := by ring
    _ < (M + K) * (ε / (2 * (M + K))) + ε / 2 :=
      add_lt_add (mul_lt_mul_of_pos_left hxy' hsum) he
    _ = ε := by field_simp; ring

/-- Strong continuity on a compact time interval converts grid convergence into
convergence with a separately varying target time. -/
lemma moving_time_convergence {T : C0Semigroup 𝕜 X} {C : Steps 𝕜 X}
    (hc : GridConverges T C) : Converges T C := by
  intro x B ε hε
  obtain ⟨δ₁, hδ₁, hd₁⟩ := hc x B (ε / 2) (by positivity)
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous
    (s := Icc (0 : ℝ≥0) B) (T.continuous_orbit x).continuousOn
  obtain ⟨δ₂, hδ₂, hd₂⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / 2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro h hh hhδ n hn t ht hnt
  have hg := hd₁ h hh (lt_of_lt_of_le hhδ (min_le_left _ _)) n hn
  have he := hd₂ (n • h) ⟨zero_le, hn⟩ t ⟨zero_le, ht⟩
    (lt_of_lt_of_le hnt (min_le_right _ _))
  have htri := dist_triangle (((C h) ^ n) x) (T.operators (n • h) x) (T.operators t x)
  simp only [dist_eq_norm] at he htri
  exact htri.trans_lt (by linarith)

theorem sufficiency : LaxSpec.Sufficiency := by
  intro 𝕜 X _ _ _ _ T C hs _hcore hc
  have hg := stable_consistent_grid_convergence T C hs hc
  exact ⟨hg, moving_time_convergence hg⟩

end ExpandedFA.Semigroups.LaxEquivalence
