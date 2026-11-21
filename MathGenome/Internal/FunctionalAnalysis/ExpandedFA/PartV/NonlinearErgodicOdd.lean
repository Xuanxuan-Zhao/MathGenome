import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.NonlinearErgodicOdd
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.NonlinearErgodicWeak
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace ExpandedFA.PartV.NonlinearErgodicOdd
universe u v
abbrev Nonexpansive := @NonlinearErgodicWeak.Spec.Nonexpansive

section Real
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem odd_map_comparison_real {R : H → H} (hR : Nonexpansive R)
    (ho : ∀ x, R (-x) = -R x) (x y : H) :
    2 * |⟪x, y⟫_ℝ - ⟪R x, R y⟫_ℝ| ≤
      ‖x‖ ^ 2 + ‖y‖ ^ 2 - ‖R x‖ ^ 2 - ‖R y‖ ^ 2 := by
  have hm := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hR x y)
  have hp := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hR x (-y))
  simp only [ho, sub_neg_eq_add] at hp
  rw [norm_sub_sq_real, norm_sub_sq_real] at hm
  rw [norm_add_sq_real, norm_add_sq_real] at hp
  have hab : |⟪x, y⟫_ℝ - ⟪R x, R y⟫_ℝ| ≤
      (‖x‖ ^ 2 + ‖y‖ ^ 2 - ‖R x‖ ^ 2 - ‖R y‖ ^ 2) / 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

theorem odd_zero {R : H → H} (ho : ∀ x, R (-x) = -R x) : R 0 = 0 := by
  have h := ho 0
  simp only [neg_zero] at h
  have : R 0 + R 0 = 0 := eq_neg_iff_add_eq_zero.mp h
  have hs : (2 : ℝ) • R 0 = 0 := by simpa [two_smul] using this
  exact (smul_eq_zero.mp hs).resolve_left (by norm_num)

omit [InnerProductSpace ℝ H] in
theorem iterate_odd {R : H → H} (ho : ∀ x, R (-x) = -R x) (n : ℕ) :
    ∀ x, R^[n] (-x) = -R^[n] x := by
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; simp only [Function.iterate_succ_apply', ih, ho]

omit [InnerProductSpace ℝ H] in
theorem iterate_nonexpansive {R : H → H} (hR : Nonexpansive R) (n : ℕ) :
    Nonexpansive R^[n] := by
  induction n with
  | zero => intro x y; exact le_rfl
  | succ n ih =>
    intro x y
    simpa only [Function.iterate_succ_apply'] using (hR _ _).trans (ih x y)

theorem orbit_sq_antitone {R : H → H} (hR : Nonexpansive R)
    (ho : ∀ x, R (-x) = -R x) (f : H) :
    Antitone (fun n => ‖R^[n] f‖ ^ 2) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := hR (R^[n] f) 0
  simp only [odd_zero ho, sub_zero] at h
  simpa only [Function.iterate_succ_apply'] using
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h

/-- Comparing a pair with its common translate along the orbit. -/
theorem orbit_shift_comparison {R : H → H} (hR : Nonexpansive R)
    (ho : ∀ x, R (-x) = -R x) (f : H) (n i k : ℕ) :
    2 * |⟪R^[n] f, R^[n + i] f⟫_ℝ -
      ⟪R^[n + k] f, R^[n + k + i] f⟫_ℝ| ≤
      (‖R^[n] f‖ ^ 2 - ‖R^[n + k] f‖ ^ 2) +
      (‖R^[n + i] f‖ ^ 2 - ‖R^[n + k + i] f‖ ^ 2) := by
  have h := odd_map_comparison_real (iterate_nonexpansive hR k) (iterate_odd ho k)
    (R^[n] f) (R^[n + i] f)
  have he (a : ℕ) : R^[k] (R^[a] f) = R^[a + k] f := by
    rw [← Function.iterate_add_apply, Nat.add_comm]
  rw [he, he] at h
  have he' : n + i + k = n + k + i := by omega
  rw [he'] at h
  linarith


/-- Norm defects control all correlations, with no completeness assumption
on the ambient inner product space. -/
theorem uniform_orbit_comparison_real {R : H → H} (hR : Nonexpansive R)
    (ho : ∀ x, R (-x) = -R x) (f : H) :
    ∃ (L : ℝ) (ell : ℕ → ℝ),
      Tendsto (fun n => ‖R^[n] f‖ ^ 2) atTop (𝓝 L) ∧
      Antitone (fun n => ‖R^[n] f‖ ^ 2) ∧
      (∀ n, 0 ≤ ‖R^[n] f‖ ^ 2 - L) ∧
      ∀ n i, |⟪R^[n] f, R^[n + i] f⟫_ℝ - ell i| ≤ ‖R^[n] f‖ ^ 2 - L := by
  let a := fun n => ‖R^[n] f‖ ^ 2
  have ha : Antitone a := orbit_sq_antitone hR ho f
  have hb : BddBelow (Set.range a) := ⟨0, by rintro _ ⟨n, rfl⟩; exact sq_nonneg _⟩
  let L := ⨅ n, a n
  have hl : Tendsto a atTop (𝓝 L) := tendsto_atTop_ciInf ha hb
  have hlo (n : ℕ) : L ≤ a n := ha.le_of_tendsto hl n
  let δ := fun n => a n - L
  have hd : Tendsto δ atTop (𝓝 0) := by simpa only [sub_self] using hl.sub_const L
  have hshift (n m i : ℕ) (hnm : n ≤ m) :
      |⟪R^[n] f, R^[n + i] f⟫_ℝ - ⟪R^[m] f, R^[m + i] f⟫_ℝ| ≤ δ n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have h := orbit_shift_comparison hR ho f n i k
    have hni := ha (Nat.le_add_right n i)
    have hlow := hlo (n + k)
    have hlow' := hlo (n + k + i)
    change 2 * |_ - _| ≤ (a n - a (n + k)) + (a (n + i) - a (n + k + i)) at h
    change |_ - _| ≤ a n - L
    linarith
  have hc (i : ℕ) : CauchySeq (fun n => ⟪R^[n] f, R^[n + i] f⟫_ℝ) := by
    apply cauchySeq_of_le_tendsto_0' δ _ hd
    intro n m hnm
    simpa only [Real.dist_eq] using hshift n m i hnm
  choose ell he using fun i => cauchySeq_tendsto_of_complete (hc i)
  refine ⟨L, ell, hl, ha, fun n => sub_nonneg.mpr (hlo n), ?_⟩
  intro n i
  have ht := ((tendsto_const_nhds (x := ⟪R^[n] f, R^[n + i] f⟫_ℝ)).sub (he i)).abs
  exact le_of_tendsto ht ((eventually_ge_atTop n).mono fun m hm => hshift n m i hm)

/-- A bounded factor times a strongly vanishing vector gives a vanishing
real inner product. -/
theorem inner_tendsto_zero_of_bounded {z d : ℕ → H} {C : ℝ}
    (hz : ∀ n, ‖z n‖ ≤ C) (hd : Tendsto d atTop (𝓝 0)) :
    Tendsto (fun n => ⟪z n, d n⟫_ℝ) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht : Tendsto (fun n => C * ‖d n‖) atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using hd.norm.const_mul C
  apply squeeze_zero (fun n => norm_nonneg _) _ ht
  intro n
  rw [Real.norm_eq_abs]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hz n) (norm_nonneg _))

omit [InnerProductSpace ℝ H] in
theorem regular_shift {z : ℕ → H}
    (hr : Tendsto (fun n => z (n + 1) - z n) atTop (𝓝 0)) (i : ℕ) :
    Tendsto (fun n => z (n + i) - z n) atTop (𝓝 0) := by
  induction i with
  | zero => simpa only [Nat.add_zero, sub_self] using
      (tendsto_const_nhds (x := (0 : H)) : Tendsto (fun _ : ℕ => (0 : H)) atTop (𝓝 0))
  | succ i ih =>
    have ht := (hr.comp (tendsto_add_atTop_nat i)).add ih
    simpa only [Function.comp_def, Nat.add_assoc, sub_add_sub_cancel, add_zero] using ht

/-- Oddness and asymptotic regularity turn the weak iteration theorem into
strong convergence. This argument works in arbitrary Hilbert dimension. -/
theorem strong_orbit_of_regular [CompleteSpace H] {R : H → H}
    (hR : Nonexpansive R) (ho : ∀ x, R (-x) = -R x) (f : H)
    (hr : Tendsto (fun n => R^[n + 1] f - R^[n] f) atTop (𝓝 0)) :
    ∃ p, Tendsto (fun n => R^[n] f) atTop (𝓝 p) := by
  obtain ⟨L, ell, hl, ha, hδ, he⟩ := uniform_orbit_comparison_real hR ho f
  let z := fun n => R^[n] f
  let δ := fun n => ‖z n‖ ^ 2 - L
  have hd : Tendsto δ atTop (𝓝 0) := by simpa only [sub_self] using hl.sub_const L
  have hb (n : ℕ) : ‖z n‖ ≤ ‖f‖ := by
    have h := ha (Nat.zero_le n)
    change ‖z n‖ ^ 2 ≤ ‖f‖ ^ 2 at h
    nlinarith [norm_nonneg (z n), norm_nonneg f]
  have hell (i : ℕ) : ell i = L := by
    have hi := inner_tendsto_zero_of_bounded hb (regular_shift (z := z) hr i)
    have hi' : Tendsto (fun n => ⟪z n, z (n + i)⟫_ℝ) atTop (𝓝 L) := by
      have ht := hl.add hi
      simp only [inner_sub_right, real_inner_self_eq_norm_sq] at ht
      convert ht using 1
      · funext n; dsimp [z]; ring
      · simp
    have he' : Tendsto (fun n => ⟪z n, z (n + i)⟫_ℝ) atTop (𝓝 (ell i)) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      simpa only [Real.norm_eq_abs] using squeeze_zero (fun n => abs_nonneg _)
        (fun n => he n i) hd
    exact tendsto_nhds_unique he' hi'
  have hdist (n m : ℕ) (hnm : n ≤ m) : ‖z n - z m‖ ^ 2 ≤ 4 * δ n := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hi := (abs_le.mp (he n i)).1
    rw [hell i] at hi
    have hm := ha (Nat.le_add_right n i)
    change ‖z (n + i)‖ ^ 2 ≤ ‖z n‖ ^ 2 at hm
    rw [norm_sub_sq_real]
    change _ ≤ 4 * (‖z n‖ ^ 2 - L)
    change -(‖z n‖ ^ 2 - L) ≤ ⟪z n, z (n + i)⟫_ℝ - L at hi
    linarith
  have hc : CauchySeq z := by
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε
    have ht : ∀ᶠ n in atTop, δ n < ε ^ 2 / 4 :=
      (tendsto_order.mp hd).2 _ (by positivity)
    obtain ⟨N, hN⟩ := ht.exists
    refine ⟨N, fun n hn => ?_⟩
    have h := hdist N n hn
    rw [dist_comm, dist_eq_norm]
    nlinarith [norm_nonneg (z N - z n)]
  exact cauchySeq_tendsto_of_complete hc

theorem averaged_odd {T : H → H} (ho : ∀ x, T (-x) = -T x) :
    ∀ x, NonlinearErgodicWeak.Spec.averaged ℝ T (-x) =
      -NonlinearErgodicWeak.Spec.averaged ℝ T x := by
  intro x
  change (1 / 2 : ℝ) • (-x + T (-x)) = -((1 / 2 : ℝ) • (x + T x))
  rw [ho, ← neg_add, smul_neg]

theorem averaged_strong_real [CompleteSpace H] {T : H → H}
    (hT : Nonexpansive T) (hp : ∃ p, T p = p) (ho : ∀ x, T (-x) = -T x) (f : H) :
    ∃ p, T p = p ∧ NonlinearErgodicWeak.Spec.WeaklyConverges ℝ
      (fun n => (NonlinearErgodicWeak.Spec.averaged ℝ T)^[n] f) p ∧
      Tendsto (fun n => ‖(NonlinearErgodicWeak.Spec.averaged ℝ T)^[n] f - p‖)
        atTop (𝓝 0) := by
  obtain ⟨⟨q, hq, hwq⟩, _⟩ := NonlinearErgodicWeak.nonlinear_ergodic_weak_real hT hp f
  have hr : Tendsto (fun n => (NonlinearErgodicWeak.Spec.averaged ℝ T)^[n + 1] f -
      (NonlinearErgodicWeak.Spec.averaged ℝ T)^[n] f) atTop (𝓝 0) := by
    obtain ⟨p, hp⟩ := hp
    have hs := (NonexpansiveDemiclosure.averaged_square_summable ℝ H T hT p hp f).1
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact NonlinearErgodicWeak.tendsto_zero_of_sq (fun n => norm_nonneg _) hs.tendsto_atTop_zero
  obtain ⟨p, hlim⟩ := strong_orbit_of_regular
    (NonexpansiveDemiclosure.averaged_nonexpansive ℝ H T hT) (averaged_odd ho) f hr
  have hw : NonlinearErgodicWeak.Spec.WeaklyConverges ℝ
      (fun n => (NonlinearErgodicWeak.Spec.averaged ℝ T)^[n] f) p := by
    intro φ
    exact φ.continuous.continuousAt.tendsto.comp hlim
  have he : p = q := NonlinearErgodicWeak.weak_limit_unique ℝ hw hwq
  subst q
  exact ⟨p, hq, hw, tendsto_iff_norm_sub_tendsto_zero.mp hlim⟩

/-- A scalar arithmetic mean, kept separate from vector scalar actions. -/
def scalarMean (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i

theorem scalarMean_shift {a : ℕ → ℝ} {l : ℝ}
    (ha : Tendsto (scalarMean a) atTop (𝓝 l)) (k : ℕ) :
    Tendsto (scalarMean (fun i => a (k + i))) atTop (𝓝 l) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hm := ha.comp (show Tendsto (fun n : ℕ => k + n) atTop atTop by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat k)
  have ht := ((tendsto_const_nhds (x := (1 : ℝ))).add (hi.const_mul (k : ℝ))).mul hm
  have ht' := ht.sub (hi.mul_const (∑ i ∈ Finset.range k, a i))
  have hh : Tendsto (fun n : ℕ =>
      (1 + (k : ℝ) * (n : ℝ)⁻¹) * scalarMean a (k + n) -
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range k, a i) atTop (𝓝 l) := by
    simpa only [Function.comp_def, mul_zero, add_zero, one_mul, zero_mul, sub_zero] using ht'
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hknR : ((k + n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs := Finset.sum_range_add a k n
  dsimp [scalarMean]
  rw [hs]
  field_simp
  push_cast
  ring

/-- Uniformly close scalar means retain the same uniform error bound. -/
theorem scalarMean_abs_sub_le {a b : ℕ → ℝ} {C : ℝ}
    (h : ∀ i, |a i - b i| ≤ C) {n : ℕ} (hn : 0 < n) :
    |scalarMean a n - scalarMean b n| ≤ C := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [scalarMean, scalarMean, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  calc
    (n : ℝ)⁻¹ * |∑ i ∈ Finset.range n, (a i - b i)| ≤
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, |a i - b i| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (n : ℝ)⁻¹ * ∑ _i ∈ Finset.range n, C :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h i) (by positivity)
    _ = C := by simp [← mul_assoc, inv_mul_cancel₀ hnR]

/-- A sequence uniformly approximable by convergent sequences, with errors
vanishing as the approximation index increases, converges. The limits of
the approximations converge to its limit as well. -/
theorem limit_of_uniform_approximations {X a δ : ℕ → ℝ} {b : ℕ → ℕ → ℝ}
    (hd : Tendsto δ atTop (𝓝 0))
    (hb : ∀ n, Tendsto (b n) atTop (𝓝 (a n)))
    (he : ∀ n p, 0 < p → |b n p - X p| ≤ δ n) :
    ∃ l, Tendsto X atTop (𝓝 l) ∧ Tendsto a atTop (𝓝 l) ∧
      ∀ n, |a n - l| ≤ δ n := by
  have hc : CauchySeq X := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨n, hn⟩ := ((tendsto_order.mp hd).2 (ε / 4) (by positivity)).exists
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hb n).cauchySeq (ε / 2) (by positivity)
    refine ⟨max N 1, fun m hm p hp => ?_⟩
    have hmN : N ≤ m := le_trans (le_max_left _ _) hm
    have hpN : N ≤ p := le_trans (le_max_left _ _) hp
    have hm0 : 0 < m := lt_of_lt_of_le (by omega : 0 < max N 1) hm
    have hp0 : 0 < p := lt_of_lt_of_le (by omega : 0 < max N 1) hp
    have hmerr : |X m - b n m| ≤ δ n := by simpa only [abs_sub_comm] using he n m hm0
    have hperr := he n p hp0
    have hmid : |b n m - b n p| < ε / 2 := by simpa only [Real.dist_eq] using hN m hmN p hpN
    rw [Real.dist_eq]
    calc
      |X m - X p| ≤ |X m - b n m| + |b n m - b n p| + |b n p - X p| := by
        linarith [abs_sub_le (X m) (b n m) (X p), abs_sub_le (b n m) (b n p) (X p)]
      _ < ε := by linarith
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
  have he' (n : ℕ) : |a n - l| ≤ δ n := by
    exact le_of_tendsto (((hb n).sub hl).abs)
      ((eventually_gt_atTop 0).mono fun p hp => he n p hp)
  refine ⟨l, hl, ?_, he'⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using squeeze_zero (fun n => abs_nonneg _) he' hd

/-- Weak convergence of the vector means identifies the limit of the scalar
correlation means; no convergence of the original orbit is assumed. -/
theorem correlation_means_tendsto {z : ℕ → H} {q : H} {ell δ : ℕ → ℝ}
    (hw : NonlinearErgodicWeak.Spec.WeaklyConverges ℝ
      (NonlinearErgodicWeak.Spec.cesaro ℝ z) q)
    (hd : Tendsto δ atTop (𝓝 0))
    (he : ∀ n i, |⟪z n, z (n + i)⟫_ℝ - ell i| ≤ δ n) :
    Tendsto (scalarMean ell) atTop (𝓝 (‖q‖ ^ 2)) := by
  have hraw (n : ℕ) : Tendsto (scalarMean (fun i => ⟪z n, z i⟫_ℝ))
      atTop (𝓝 ⟪z n, q⟫_ℝ) := by
    have h := hw (innerSL ℝ (z n))
    change Tendsto (fun j => ⟪z n, NonlinearErgodicWeak.Spec.cesaro ℝ z j⟫_ℝ)
      atTop (𝓝 ⟪z n, q⟫_ℝ) at h
    change Tendsto (fun p : ℕ => (p : ℝ)⁻¹ * ∑ i ∈ Finset.range p, ⟪z n, z i⟫_ℝ)
      atTop (𝓝 ⟪z n, q⟫_ℝ)
    simpa only [NonlinearErgodicWeak.Spec.cesaro, real_inner_smul_right, inner_sum] using h
  obtain ⟨l, hl, ha, _⟩ := limit_of_uniform_approximations hd
    (fun n => scalarMean_shift (hraw n) n)
    (fun n p hp => scalarMean_abs_sub_le (he n) hp)
  have hac : Tendsto (scalarMean (fun n => ⟪z n, q⟫_ℝ)) atTop (𝓝 l) := ha.cesaro
  have hqc : Tendsto (scalarMean (fun n => ⟪z n, q⟫_ℝ)) atTop (𝓝 (‖q‖ ^ 2)) := by
    have h := hw (innerSL ℝ q)
    change Tendsto (fun j => ⟪q, NonlinearErgodicWeak.Spec.cesaro ℝ z j⟫_ℝ)
      atTop (𝓝 ⟪q, q⟫_ℝ) at h
    change Tendsto (fun p : ℕ => (p : ℝ)⁻¹ * ∑ i ∈ Finset.range p, ⟪z i, q⟫_ℝ)
      atTop (𝓝 (‖q‖ ^ 2))
    simpa only [NonlinearErgodicWeak.Spec.cesaro, real_inner_smul_right, inner_sum,
      real_inner_self_eq_norm_sq, real_inner_comm q] using h
  exact (tendsto_nhds_unique hac hqc) ▸ hl

/-- The triangular Gram-matrix estimate. Dropping the nonnegative diagonal
makes the formula valid also at the zero index. -/
theorem prefix_energy_bound {z : ℕ → H} {ell δ : ℕ → ℝ}
    (hd : ∀ n, 0 ≤ δ n)
    (he : ∀ n i, |⟪z n, z (n + i)⟫_ℝ - ell i| ≤ δ n) (N : ℕ) :
    ‖∑ i ∈ Finset.range N, z i‖ ^ 2 ≤
      2 * (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j + 1), ell i) +
      2 * (N : ℝ) * ∑ i ∈ Finset.range N, δ i := by
  have hb (N : ℕ) : (∑ i ∈ Finset.range (N + 1), ⟪z i, z N⟫_ℝ) ≤
      (∑ i ∈ Finset.range (N + 1), ell i) + ∑ i ∈ Finset.range (N + 1), δ i := by
    have hx : (∑ i ∈ Finset.range (N + 1), ⟪z i, z N⟫_ℝ) ≤
        ∑ i ∈ Finset.range (N + 1), (ell (N - i) + δ i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have h := (abs_le.mp (he i (N - i))).2
      rw [Nat.add_sub_of_le hiN] at h
      linarith
    rw [Finset.sum_add_distrib] at hx
    have href : (∑ i ∈ Finset.range (N + 1), ell (N - i)) =
        ∑ i ∈ Finset.range (N + 1), ell i := by
      simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect ell (N + 1)
    rwa [href] at hx
  induction N with
  | zero => simp
  | succ N ih =>
    have h := hb N
    rw [Finset.sum_range_succ, real_inner_self_eq_norm_sq] at h
    rw [Finset.sum_range_succ, norm_add_sq_real, sum_inner]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    rw [Finset.sum_range_succ] at h
    rw [Finset.sum_range_succ δ N] at h ⊢
    nlinarith [sq_nonneg ‖z N‖, mul_nonneg (Nat.cast_nonneg N (α := ℝ)) (hd N)]

/-- The triangularly weighted means of a sequence whose arithmetic means
converge have the same limit. -/
theorem triangular_means_tendsto {ell : ℕ → ℝ} {X : ℝ}
    (hX : Tendsto (scalarMean ell) atTop (𝓝 X)) :
    Tendsto (fun N : ℕ => 2 * ((N : ℝ)⁻¹) ^ 2 *
      ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j + 1), ell i) atTop (𝓝 X) := by
  let a := fun j => scalarMean ell (j + 1)
  have ha : Tendsto a atTop (𝓝 X) := hX.comp (tendsto_add_atTop_nat 1)
  have herror : Tendsto (fun N => 2 * scalarMean (fun j => |a j - X|) N)
      atTop (𝓝 0) := by
    have ht := (ha.sub_const X).abs.cesaro
    simpa only [scalarMean, sub_self, abs_zero, mul_zero] using ht.const_mul 2
  have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hm : Tendsto (fun N : ℕ => (1 + (N : ℝ)⁻¹) * X) atTop (𝓝 X) := by
    simpa only [add_zero, one_mul] using ((tendsto_const_nhds (x := (1 : ℝ))).add hi).mul_const X
  have hsum (N : ℕ) : 2 * (∑ j ∈ Finset.range N, ((j : ℝ) + 1)) =
      (N : ℝ) * ((N : ℝ) + 1) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]; nlinarith
  have hpre (j : ℕ) : (∑ i ∈ Finset.range (j + 1), ell i) = ((j : ℝ) + 1) * a j := by
    have hj : ((j + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    dsimp [a, scalarMean]
    rw [← Nat.cast_add_one]
    rw [← mul_assoc, mul_inv_cancel₀ hj, one_mul]
  let F := fun N : ℕ => 2 * ((N : ℝ)⁻¹) ^ 2 *
    ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j + 1), ell i
  have herr : Tendsto (fun N => F N - (1 + (N : ℝ)⁻¹) * X) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) _ herror
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
    have hmain : 2 * ((N : ℝ)⁻¹) ^ 2 *
        (∑ j ∈ Finset.range N, (((j : ℝ) + 1) * X)) = (1 + (N : ℝ)⁻¹) * X := by
      rw [← Finset.sum_mul]
      have hs := hsum N
      field_simp
      rw [hs]
      ring
    have heq : F N - (1 + (N : ℝ)⁻¹) * X =
        2 * ((N : ℝ)⁻¹) ^ 2 * ∑ j ∈ Finset.range N, (((j : ℝ) + 1) * (a j - X)) := by
      dsimp [F]
      simp_rw [hpre]
      rw [← hmain, ← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ 2 * ((N : ℝ)⁻¹) ^ 2)]
    calc
      2 * ((N : ℝ)⁻¹) ^ 2 * |∑ j ∈ Finset.range N, (((j : ℝ) + 1) * (a j - X))| ≤
          2 * ((N : ℝ)⁻¹) ^ 2 * ∑ j ∈ Finset.range N, |((j : ℝ) + 1) * (a j - X)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ ≤ 2 * ((N : ℝ)⁻¹) ^ 2 * ∑ j ∈ Finset.range N, ((N : ℝ) * |a j - X|) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (j : ℝ) + 1)]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        have h := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
        exact_mod_cast h
      _ = 2 * scalarMean (fun j => |a j - X|) N := by
        rw [← Finset.mul_sum]
        dsimp [scalarMean]
        field_simp
  have ht := herr.add hm
  simpa only [sub_add_cancel, zero_add] using ht

/-- Uniform correlations upgrade weak convergence of arithmetic means to
strong convergence. Expanding the distance to q avoids any separate
sequential compactness or lower-semicontinuity assumption. -/
theorem strong_cesaro_of_correlations {z : ℕ → H} {q : H} {ell δ : ℕ → ℝ}
    (hw : NonlinearErgodicWeak.Spec.WeaklyConverges ℝ
      (NonlinearErgodicWeak.Spec.cesaro ℝ z) q)
    (hd : Tendsto δ atTop (𝓝 0)) (hd0 : ∀ n, 0 ≤ δ n)
    (he : ∀ n i, |⟪z n, z (n + i)⟫_ℝ - ell i| ≤ δ n) :
    Tendsto (fun N => ‖NonlinearErgodicWeak.Spec.cesaro ℝ z N - q‖) atTop (𝓝 0) := by
  have hX := correlation_means_tendsto hw hd he
  have htri := triangular_means_tendsto hX
  have hδ : Tendsto (fun N => 2 * scalarMean δ N) atTop (𝓝 0) := by
    simpa only [scalarMean, mul_zero] using hd.cesaro.const_mul 2
  let b := fun N : ℕ => 2 * ((N : ℝ)⁻¹) ^ 2 *
      (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j + 1), ell i) + 2 * scalarMean δ N
  have hb : Tendsto b atTop (𝓝 (‖q‖ ^ 2)) := by
    simpa only [add_zero] using htri.add hδ
  have hbound : ∀ᶠ N in atTop, ‖NonlinearErgodicWeak.Spec.cesaro ℝ z N‖ ^ 2 ≤ b N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
    rw [NonlinearErgodicWeak.Spec.cesaro, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)), mul_pow]
    calc
      ((N : ℝ)⁻¹) ^ 2 * ‖∑ i ∈ Finset.range N, z i‖ ^ 2 ≤
          ((N : ℝ)⁻¹) ^ 2 * (2 * (∑ j ∈ Finset.range N,
            ∑ i ∈ Finset.range (j + 1), ell i) +
            2 * (N : ℝ) * ∑ i ∈ Finset.range N, δ i) :=
        mul_le_mul_of_nonneg_left (prefix_energy_bound hd0 he N) (sq_nonneg _)
      _ = b N := by
        dsimp [b, scalarMean]
        field_simp
  have hinner : Tendsto (fun N => ⟪NonlinearErgodicWeak.Spec.cesaro ℝ z N, q⟫_ℝ)
      atTop (𝓝 (‖q‖ ^ 2)) := by
    have h := hw (innerSL ℝ q)
    change Tendsto (fun N => ⟪q, NonlinearErgodicWeak.Spec.cesaro ℝ z N⟫_ℝ)
      atTop (𝓝 ⟪q, q⟫_ℝ) at h
    simpa only [real_inner_comm q, real_inner_self_eq_norm_sq] using h
  have hres : Tendsto (fun N => b N -
      2 * ⟪NonlinearErgodicWeak.Spec.cesaro ℝ z N, q⟫_ℝ + ‖q‖ ^ 2) atTop (𝓝 0) := by
    have ht := (hb.sub (hinner.const_mul 2)).add_const (‖q‖ ^ 2)
    have hz : ‖q‖ ^ 2 - 2 * ‖q‖ ^ 2 + ‖q‖ ^ 2 = (0 : ℝ) := by ring
    simpa only [hz] using ht
  apply NonlinearErgodicWeak.tendsto_zero_of_sq (fun N => norm_nonneg _)
  apply squeeze_zero' (Eventually.of_forall fun N => sq_nonneg _) _ hres
  filter_upwards [hbound] with N hN
  rw [norm_sub_sq_real]
  linarith

theorem cesaro_strong_real [CompleteSpace H] {T : H → H}
    (hT : Nonexpansive T) (hp : ∃ p, T p = p) (ho : ∀ x, T (-x) = -T x) (f : H) :
    ∃ q, T q = q ∧ NonlinearErgodicWeak.Spec.WeaklyConverges ℝ
      (NonlinearErgodicWeak.Spec.cesaro ℝ (fun j => T^[j] f)) q ∧
      Tendsto (fun n => ‖NonlinearErgodicWeak.Spec.cesaro ℝ (fun j => T^[j] f) n - q‖)
        atTop (𝓝 0) := by
  obtain ⟨_, ⟨q, hq, hwq⟩⟩ := NonlinearErgodicWeak.nonlinear_ergodic_weak_real hT hp f
  obtain ⟨L, ell, hl, _, hd0, he⟩ := uniform_orbit_comparison_real hT ho f
  have hd : Tendsto (fun n => ‖T^[n] f‖ ^ 2 - L) atTop (𝓝 0) := by
    simpa only [sub_self] using hl.sub_const L
  exact ⟨q, hq, hwq, strong_cesaro_of_correlations hwq hd hd0 he⟩

end Real

theorem odd_map_comparison : Spec.OddMapComparison.{u, v} := by
  intro 𝕜 H _ _ _ R hR ho
  let := ExpandedFA.Hilbert.Conventions.Spec.RealificationValue 𝕜 H
  exact odd_map_comparison_real hR ho

theorem uniform_orbit_comparison : Spec.UniformOrbitComparison.{u, v} := by
  intro 𝕜 H _ _ _ R hR ho f
  let := ExpandedFA.Hilbert.Conventions.Spec.RealificationValue 𝕜 H
  exact uniform_orbit_comparison_real hR ho f

theorem averaged_strong : Spec.AveragedStrong.{u, v} := by
  intro 𝕜 H _ _ _ _ T hT hp ho f
  let := ExpandedFA.Hilbert.Conventions.Spec.RealificationValue 𝕜 H
  obtain ⟨p, hp, hw, hs⟩ := averaged_strong_real hT hp ho f
  exact ⟨p, hp, NonlinearErgodicWeak.weaklyConverges_of_real 𝕜 hw, hs⟩

theorem nonlinear_ergodic_odd : Spec.NonlinearErgodicOdd.{u, v} := by
  intro 𝕜 H _ _ _ _ T hT hp ho f
  let := ExpandedFA.Hilbert.Conventions.Spec.RealificationValue 𝕜 H
  obtain ⟨p, hpT, hwp, hsp⟩ := averaged_strong_real hT hp ho f
  obtain ⟨q, hqT, hwq, hsq⟩ := cesaro_strong_real hT hp ho f
  exact ⟨⟨p, hpT, NonlinearErgodicWeak.weaklyConverges_of_real 𝕜 hwp, hsp⟩,
    ⟨q, hqT, NonlinearErgodicWeak.weaklyConverges_of_real 𝕜 hwq, hsq⟩⟩

theorem ergodic_norms_tendsto : Spec.NormConvergence.{u, v} := by
  intro 𝕜 H _ _ _ _ T hT hp ho f p q hwp hwq
  obtain ⟨⟨r, _, hwr, hsr⟩, ⟨s, _, hws, hss⟩⟩ := nonlinear_ergodic_odd 𝕜 H T hT hp ho f
  have hpr : p = r := NonlinearErgodicWeak.weak_limit_unique 𝕜 hwp hwr
  have hqs : q = s := NonlinearErgodicWeak.weak_limit_unique 𝕜 hwq hws
  subst p
  subst q
  exact ⟨(tendsto_iff_norm_sub_tendsto_zero.mpr hsr).norm,
    (tendsto_iff_norm_sub_tendsto_zero.mpr hss).norm⟩

end ExpandedFA.PartV.NonlinearErgodicOdd
