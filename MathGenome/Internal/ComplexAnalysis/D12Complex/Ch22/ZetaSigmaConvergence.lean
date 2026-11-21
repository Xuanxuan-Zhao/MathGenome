import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.ZetaSigmaConvergence
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.WeierstrassSeries
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch16.CanonicalFactors
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option maxHeartbeats 1000000
noncomputable section
open Set Filter
open scoped Topology
namespace D12Complex.Ch22.ZetaSigmaConvergence
abbrev lattice := Specs.D12Complex.Ch22.LatticeGeometry.lattice
abbrev NonzeroLattice := Specs.D12Complex.Ch22.ZetaSigmaConvergence.NonzeroLattice
abbrev zetaTerm := Specs.D12Complex.Ch22.ZetaSigmaConvergence.zetaTerm
abbrev factor := Specs.D12Complex.Ch16.CanonicalFactors.factor_value

abbrev zeta : ℂ → ℂ → ℂ → ℂ := Specs.D12Complex.Ch22.ZetaSigmaConvergence.zeta
abbrev sigma : ℂ → ℂ → ℂ → ℂ := Specs.D12Complex.Ch22.ZetaSigmaConvergence.sigma

theorem factor_two : Specs.D12Complex.Ch22.ZetaSigmaConvergence.factor_two_type := by
  intro w
  norm_num [Specs.D12Complex.Ch16.CanonicalFactors.factor_value, Finset.sum_range_succ]

/-- Cancellation takes place inside each summand before any infinite sum. -/
theorem zetaTerm_eq (z l : ℂ) (hl : l ≠ 0) (hz : z - l ≠ 0) :
    zetaTerm l z = z ^ 2 / (l ^ 2 * (z - l)) := by
  unfold zetaTerm Specs.D12Complex.Ch22.ZetaSigmaConvergence.zetaTerm
  field_simp
  ring

/-- Uniform estimate for the far regularized zeta tail. -/
theorem zetaTerm_bound (r : ℝ) (hr : 0 < r) (z l : ℂ)
    (hz : ‖z‖ < r) (hl : 2 * r ≤ ‖l‖) :
    ‖zetaTerm l z‖ ≤ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
  have hl0 : 0 < ‖l‖ := by linarith
  have hd : ‖l‖ / 2 ≤ ‖z - l‖ := by
    have := norm_sub_norm_le l z
    rw [norm_sub_rev] at this
    linarith
  have hd0 : 0 < ‖z - l‖ := lt_of_lt_of_le (by positivity) hd
  rw [zetaTerm_eq z l (norm_pos_iff.mp hl0) (norm_pos_iff.mp hd0)]
  simp only [norm_div, norm_mul, norm_pow]
  calc
    ‖z‖ ^ 2 / (‖l‖ ^ 2 * ‖z - l‖) ≤ r ^ 2 / (‖l‖ ^ 2 * (‖l‖ / 2)) := by
      exact div_le_div₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg z) hz.le _)
        (by positivity) (mul_le_mul_of_nonneg_left hd (by positivity))
    _ = 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
      rw [show (-3 : ℝ) = -(3 : ℝ) by norm_num,
        Real.rpow_neg (norm_nonneg l), Real.rpow_ofNat]
      field_simp

lemma cofinite_nonzero_norm_ge (L : PeriodPair) (R : ℝ) :
    ∀ᶠ l : {l : L.lattice // l ≠ 0} in cofinite, R ≤ ‖(l.1 : ℂ)‖ :=
  Subtype.val_injective.tendsto_cofinite.eventually
    (WeierstrassSeries.cofinite_norm_ge L R)

lemma term_continuousOn {ω₁ ω₂ : ℂ} {K : Set ℂ}
    (hK : K ⊆ (lattice ω₁ ω₂ : Set ℂ)ᶜ) (l : NonzeroLattice ω₁ ω₂) :
    ContinuousOn (zetaTerm (l.1 : ℂ)) K := by
  apply ContinuousOn.add _ (continuousOn_id.div_const _)
  apply ContinuousOn.add _ continuousOn_const
  apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
  intro z hz
  exact sub_ne_zero.mpr (fun he => hK hz ((show z = (l.1 : ℂ) from he).symm ▸ l.1.2))

theorem zeta_normal : Specs.D12Complex.Ch22.ZetaSigmaConvergence.zeta_normal_type := by
  intro ω₁ ω₂ h₁ h₂ K hK hsub
  let L := WeierstrassSeries.periodPair h₁ h₂
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.exists_pos_norm_lt
  apply WeierstrassSeries.compact_majorant hK (term_continuousOn hsub)
    ((LatticeGeometry.power_summable ω₁ ω₂ h₁ h₂ 3 (by norm_num)).mul_left (2 * r ^ 2))
    (fun l => by positivity)
  filter_upwards [cofinite_nonzero_norm_ge L (2 * r)] with l hl
  intro z hz
  exact zetaTerm_bound r hr z l.1 (hKr z hz) hl

lemma factor_differentiable (l : ℂ) : Differentiable ℂ (fun z => factor 2 (z / l)) := by
  intro z
  exact (CanonicalFactors.factor_entire 2).2 (z / l) (mem_univ _) |>.comp z
    (differentiableAt_id.div_const l)

/-- Genus two matches the inverse-cube lattice summability exponent. -/
lemma factor_bound (r : ℝ) (hr : 0 < r) (z l : ℂ)
    (hz : ‖z‖ < r) (hl : 2 * r ≤ ‖l‖) :
    ‖factor 2 (z / l) - 1‖ ≤ 6 * r ^ 3 * ‖l‖ ^ (-3 : ℝ) := by
  have hl0 : 0 < ‖l‖ := by linarith
  have hw : ‖z / l‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_iff₀ hl0]
    linarith
  calc
    _ ≤ 6 * ‖z / l‖ ^ 3 := CanonicalFactors.norm_factor_sub_one_le 2 _ hw
    _ ≤ 6 * (r / ‖l‖) ^ 3 := by
      rw [norm_div]
      gcongr
    _ = 6 * r ^ 3 * ‖l‖ ^ (-3 : ℝ) := by
      rw [show (-3 : ℝ) = -(3 : ℝ) by norm_num,
        Real.rpow_neg (norm_nonneg l), Real.rpow_ofNat, div_pow, div_eq_mul_inv]
      ring

theorem sigma_normal : Specs.D12Complex.Ch22.ZetaSigmaConvergence.sigma_normal_type := by
  intro ω₁ ω₂ h₁ h₂ K hK
  let L := WeierstrassSeries.periodPair h₁ h₂
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.exists_pos_norm_lt
  apply WeierstrassSeries.compact_majorant
    (f := fun (l : NonzeroLattice ω₁ ω₂) z => factor 2 (z / (l.1 : ℂ)) - 1) hK
    (fun l => ((factor_differentiable (l.1 : ℂ)).continuous.sub continuous_const).continuousOn)
    ((LatticeGeometry.power_summable ω₁ ω₂ h₁ h₂ 3 (by norm_num)).mul_left (6 * r ^ 3))
    (fun l => by positivity)
  filter_upwards [cofinite_nonzero_norm_ge L (2 * r)] with l hl
  intro z hz
  exact factor_bound r hr z l.1 (hKr z hz) hl

lemma lattice_compl_open {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) :
    IsOpen (lattice ω₁ ω₂ : Set ℂ)ᶜ :=
  (WeierstrassSeries.periodPair h₁ h₂).isClosed_lattice.isOpen_compl

theorem zeta_locallyUniform :
    Specs.D12Complex.Ch22.ZetaSigmaConvergence.zeta_locallyUniform_type := by
  intro ω₁ ω₂ h₁ h₂
  apply hasSumLocallyUniformlyOn_of_forall_compact (lattice_compl_open h₁ h₂)
  intro K hsub hK
  obtain ⟨u, hu, hbound⟩ := zeta_normal ω₁ ω₂ h₁ h₂ K hK hsub
  exact hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr (tendstoUniformlyOn_tsum hu hbound)

theorem sigma_locallyUniform :
    Specs.D12Complex.Ch22.ZetaSigmaConvergence.sigma_locallyUniform_type := by
  intro ω₁ ω₂ h₁ h₂
  apply hasProdLocallyUniformly_of_forall_compact
  intro K hK
  obtain ⟨u, hu, hbound⟩ := sigma_normal ω₁ ω₂ h₁ h₂ K hK
  simpa only [add_sub_cancel] using hu.hasProdUniformlyOn_one_add hK
    (Eventually.of_forall hbound)
    (fun l => ((factor_differentiable (l.1 : ℂ)).continuous.sub continuous_const).continuousOn)

lemma term_differentiableOn {ω₁ ω₂ : ℂ} {K : Set ℂ}
    (hK : K ⊆ (lattice ω₁ ω₂ : Set ℂ)ᶜ) (l : NonzeroLattice ω₁ ω₂) :
    DifferentiableOn ℂ (zetaTerm (l.1 : ℂ)) K := by
  apply DifferentiableOn.add _ (differentiableOn_id.div_const _)
  apply DifferentiableOn.add _ (differentiableOn_const _)
  apply DifferentiableOn.div (differentiableOn_const _)
    (differentiableOn_id.sub (differentiableOn_const _))
  intro z hz
  exact sub_ne_zero.mpr (fun he => hK hz ((show z = (l.1 : ℂ) from he).symm ▸ l.1.2))

theorem zeta_holomorphic :
    Specs.D12Complex.Ch22.ZetaSigmaConvergence.zeta_holomorphic_type := by
  intro ω₁ ω₂ h₁ h₂
  have hopen := lattice_compl_open h₁ h₂
  have hsum := (zeta_locallyUniform ω₁ ω₂ h₁ h₂).differentiableOn
    (Eventually.of_forall (fun s => DifferentiableOn.fun_sum
      (fun l _ => term_differentiableOn (Subset.refl _) l))) hopen
  refine ⟨hopen, fun z hz => ?_⟩
  have hz0 : z ≠ 0 := fun he => hz (he.symm ▸ (zero_mem (lattice ω₁ ω₂)))
  exact ((differentiableAt_const (1 : ℂ)).div differentiableAt_id hz0).add
    (hsum.differentiableAt (hopen.mem_nhds hz))

theorem sigma_entire : Specs.D12Complex.Ch22.ZetaSigmaConvergence.sigma_entire_type := by
  intro ω₁ ω₂ h₁ h₂
  have hc := (sigma_locallyUniform ω₁ ω₂ h₁ h₂).hasProdLocallyUniformlyOn (s := univ)
  have hd := hc.differentiableOn
    (Eventually.of_forall (fun s => DifferentiableOn.fun_finsetProd
      (fun l _ => (factor_differentiable (l.1 : ℂ)).differentiableOn))) isOpen_univ
  exact ⟨isOpen_univ, fun z _ => differentiableAt_id.mul
    (hd.differentiableAt (isOpen_univ.mem_nhds (mem_univ z)))⟩

/-- The negation bijection preserves the actual nonzero lattice index set. -/
def negIndex (ω₁ ω₂ : ℂ) : NonzeroLattice ω₁ ω₂ ≃ NonzeroLattice ω₁ ω₂ where
  toFun l := ⟨-l.1, neg_ne_zero.mpr l.2⟩
  invFun l := ⟨-l.1, neg_ne_zero.mpr l.2⟩
  left_inv l := by ext; simp
  right_inv l := by ext; simp

theorem zeta_odd : Specs.D12Complex.Ch22.ZetaSigmaConvergence.zeta_odd_type := by
  intro ω₁ ω₂ _ _ z
  change 1 / (-z) + ∑' l : NonzeroLattice ω₁ ω₂, zetaTerm (l.1 : ℂ) (-z) =
    -(1 / z + ∑' l : NonzeroLattice ω₁ ω₂, zetaTerm (l.1 : ℂ) z)
  rw [← (negIndex ω₁ ω₂).tsum_eq (fun l => zetaTerm (l.1 : ℂ) (-z))]
  have he (l : NonzeroLattice ω₁ ω₂) :
      zetaTerm (((negIndex ω₁ ω₂) l).1 : ℂ) (-z) = -zetaTerm (l.1 : ℂ) z := by
    change 1 / (-z - -(l.1 : ℂ)) + 1 / -(l.1 : ℂ) + (-z) / (-(l.1 : ℂ)) ^ 2 = _
    rw [show -z - -(l.1 : ℂ) = -(z - (l.1 : ℂ)) by ring]
    simp only [div_neg, neg_div, neg_sq]
    unfold zetaTerm Specs.D12Complex.Ch22.ZetaSigmaConvergence.zetaTerm
    ring
  simp_rw [he, tsum_neg]
  simp [neg_add_rev, add_comm]

theorem sigma_odd : Specs.D12Complex.Ch22.ZetaSigmaConvergence.sigma_odd_type := by
  intro ω₁ ω₂ _ _ z
  change (-z) * ∏' l : NonzeroLattice ω₁ ω₂, factor 2 (-z / (l.1 : ℂ)) =
    -(z * ∏' l : NonzeroLattice ω₁ ω₂, factor 2 (z / (l.1 : ℂ)))
  rw [← (negIndex ω₁ ω₂).tprod_eq (fun l => factor 2 (-z / (l.1 : ℂ)))]
  simp [negIndex]

lemma nonzero_coe {ω₁ ω₂ : ℂ} (l : NonzeroLattice ω₁ ω₂) : (l.1 : ℂ) ≠ 0 := by
  intro h
  apply l.2
  exact Subtype.ext h

lemma sigma_summable_at {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) (z : ℂ) :
    Summable (fun l : NonzeroLattice ω₁ ω₂ => ‖factor 2 (z / (l.1 : ℂ)) - 1‖) := by
  obtain ⟨u, hu, hb⟩ := sigma_normal ω₁ ω₂ h₁ h₂ {z} isCompact_singleton
  exact hu.of_norm_bounded (fun l => by simpa only [norm_norm] using hb l z (mem_singleton z))

theorem sigma_zero_iff : Specs.D12Complex.Ch22.ZetaSigmaConvergence.sigma_zero_iff_type := by
  intro ω₁ ω₂ h₁ h₂ z
  change z * (∏' l : NonzeroLattice ω₁ ω₂, factor 2 (z / (l.1 : ℂ))) = 0 ↔ _
  constructor
  · intro hz
    by_contra hnot
    have hz0 : z ≠ 0 := fun h => hnot (h.symm ▸ zero_mem _)
    have hfac (l : NonzeroLattice ω₁ ω₂) : factor 2 (z / (l.1 : ℂ)) ≠ 0 := by
      change CanonicalFactors.factor 2 (z / (l.1 : ℂ)) ≠ 0
      rw [ne_eq, CanonicalFactors.factor_eq_zero_iff]
      intro h
      exact hnot ((div_eq_one_iff_eq (nonzero_coe l)).mp h ▸ l.1.2)
    have hp : (∏' l : NonzeroLattice ω₁ ω₂, factor 2 (z / (l.1 : ℂ))) ≠ 0 := by
      simpa only [add_sub_cancel] using
        tprod_one_add_ne_zero_of_summable
          (f := fun l : NonzeroLattice ω₁ ω₂ => factor 2 (z / (l.1 : ℂ)) - 1)
          (by simpa only [add_sub_cancel] using hfac) (sigma_summable_at h₁ h₂ z)
    exact mul_ne_zero hz0 hp hz
  · intro hz
    by_cases hz0 : z = 0
    · simp [hz0]
    · let l : NonzeroLattice ω₁ ω₂ := ⟨⟨z, hz⟩, fun h => hz0 (congrArg Subtype.val h)⟩
      have hf : factor 2 (z / (l.1 : ℂ)) = 0 := by
        change CanonicalFactors.factor 2 (z / (l.1 : ℂ)) = 0
        rw [CanonicalFactors.factor_eq_zero_iff]
        exact div_self hz0
      rw [(hasProd_zero_of_exists_eq_zero ⟨l, hf⟩).tprod_eq, mul_zero]

lemma term_hasDerivAt (l z : ℂ) (hz : z - l ≠ 0) :
    HasDerivAt (zetaTerm l) (-(1 / (z - l) ^ 2 - 1 / l ^ 2)) z := by
  have h := (((hasDerivAt_id z).sub_const l).inv hz).add_const (1 / l)
    |>.add ((hasDerivAt_id z).div_const (l ^ 2))
  change HasDerivAt (fun w : ℂ => 1 / (w - l) + 1 / l + w / l ^ 2) _ z
  convert h using 1
  · funext w
    simp only [Pi.add_apply, Pi.inv_apply, id_eq, one_div]
  · change -(1 / (z - l) ^ 2 - 1 / l ^ 2) = -1 / (z - l) ^ 2 + 1 / l ^ 2
    ring

theorem zeta_derivative : Specs.D12Complex.Ch22.ZetaSigmaConvergence.zeta_derivative_type := by
  intro ω₁ ω₂ h₁ h₂ z hz
  have hopen := lattice_compl_open h₁ h₂
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hz)
  have hsmall : Metric.closedBall z (r / 2) ⊆ (lattice ω₁ ω₂ : Set ℂ)ᶜ := by
    intro w hw
    exact hball (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hw) (by linarith)))
  obtain ⟨u, hu, hbound⟩ := zeta_normal ω₁ ω₂ h₁ h₂ _ (isCompact_closedBall z (r / 2)) hsmall
  have hb : Metric.ball z (r / 2) ⊆ (lattice ω₁ ω₂ : Set ℂ)ᶜ :=
    Metric.ball_subset_closedBall.trans hsmall
  have hzmem : z ∈ Metric.ball z (r / 2) := Metric.mem_ball_self (by positivity)
  have hsum := Complex.hasSum_deriv_of_summable_norm hu
    (fun l => term_differentiableOn hb l) Metric.isOpen_ball
    (fun l w hw => hbound l w (Metric.ball_subset_closedBall hw)) hzmem
  have hs : HasSum (fun l : NonzeroLattice ω₁ ω₂ =>
      -(1 / (z - (l.1 : ℂ)) ^ 2 - 1 / (l.1 : ℂ) ^ 2))
      (deriv (fun w => ∑' l : NonzeroLattice ω₁ ω₂, zetaTerm (l.1 : ℂ) w) z) := by
    convert hsum using 1
    funext l
    exact (term_hasDerivAt (l.1 : ℂ) z
      (sub_ne_zero.mpr (fun he => hz (he.symm ▸ l.1.2)))).deriv.symm
  have hd := (Complex.differentiableOn_tsum_of_summable_norm hu
    (fun l => term_differentiableOn hb l) Metric.isOpen_ball
    (fun l w hw => hbound l w (Metric.ball_subset_closedBall hw))).differentiableAt
      (Metric.isOpen_ball.mem_nhds hzmem)
  have hz0 : z ≠ 0 := fun he => hz (he.symm ▸ zero_mem _)
  have hi : HasDerivAt (fun w : ℂ => 1 / w) (-(1 / z ^ 2)) z := by
    simpa only [one_div] using hasDerivAt_inv hz0
  convert hi.add hd.hasDerivAt using 1
  · rfl
  change -Specs.D12Complex.Ch22.WeierstrassSeries.weierstrassP ω₁ ω₂ z = _
  rw [WeierstrassSeries.series_representation ω₁ ω₂ h₁ h₂ z, ← hs.tsum_eq, tsum_neg]
  ring

lemma factor_logDeriv (l z : ℂ) (hl : l ≠ 0) (hz : z ≠ l) :
    logDeriv (fun w => factor 2 (w / l)) z = zetaTerm l z := by
  have hpoly := ((hasDerivAt_id z).div_const l).add
    (((hasDerivAt_id z).div_const l).pow 2 |>.div_const 2)
  have hd := ((hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_id z).div_const l)).mul
    hpoly.cexp
  have heq : (fun w => factor 2 (w / l)) =
      (fun w : ℂ => (1 - w / l) * Complex.exp (w / l + (w / l) ^ 2 / 2)) :=
    funext (fun w => factor_two (w / l))
  have hn : 1 - z / l ≠ 0 := by
    intro h
    exact hz ((div_eq_one_iff_eq hl).mp ((sub_eq_zero.mp h).symm))
  change HasDerivAt (fun w : ℂ => (1 - w / l) * Complex.exp (w / l + (w / l) ^ 2 / 2))
    ((0 - 1 / l) * Complex.exp (z / l + (z / l) ^ 2 / 2) +
      (1 - z / l) * (Complex.exp (z / l + (z / l) ^ 2 / 2) *
        (1 / l + 2 * (z / l) ^ 1 * (1 / l) / 2))) z at hd
  rw [heq, logDeriv_apply, hd.deriv]
  change _ = 1 / (z - l) + 1 / l + z / l ^ 2
  field_simp [hl, hn, sub_ne_zero.mpr hz, Complex.exp_ne_zero]
  ring

lemma factor_ne_zero_at {ω₁ ω₂ : ℂ} {z : ℂ} (hz : z ∉ lattice ω₁ ω₂)
    (l : NonzeroLattice ω₁ ω₂) : factor 2 (z / (l.1 : ℂ)) ≠ 0 := by
  change CanonicalFactors.factor 2 (z / (l.1 : ℂ)) ≠ 0
  rw [ne_eq, CanonicalFactors.factor_eq_zero_iff]
  intro h
  exact hz ((div_eq_one_iff_eq (nonzero_coe l)).mp h ▸ l.1.2)

lemma finite_sigma_logDeriv {ω₁ ω₂ : ℂ} {z : ℂ} (hz : z ∉ lattice ω₁ ω₂)
    (s : Finset (NonzeroLattice ω₁ ω₂)) :
    logDeriv (fun w : ℂ => w * ∏ l ∈ s, factor 2 (w / (l.1 : ℂ))) z =
      1 / z + ∑ l ∈ s, zetaTerm (l.1 : ℂ) z := by
  have hz0 : z ≠ 0 := fun h => hz (h.symm ▸ zero_mem _)
  rw [logDeriv_fun_mul (f := fun w : ℂ => w)
    (g := fun w : ℂ => ∏ l ∈ s, factor 2 (w / (l.1 : ℂ))) z hz0
    (Finset.prod_ne_zero_iff.mpr (fun l _ => factor_ne_zero_at hz l))
    differentiableAt_id (DifferentiableAt.fun_finsetProd (fun l _ => factor_differentiable _ z)),
    logDeriv_id', logDeriv_fun_prod (s := s)
      (f := fun (l : NonzeroLattice ω₁ ω₂) (w : ℂ) => factor 2 (w / (l.1 : ℂ)))
      (fun l _ => factor_ne_zero_at hz l) (fun l _ => factor_differentiable _ z)]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  exact factor_logDeriv _ _ (nonzero_coe l) (fun he => hz (he.symm ▸ l.1.2))

theorem sigma_logDeriv : Specs.D12Complex.Ch22.ZetaSigmaConvergence.sigma_logDeriv_type := by
  intro ω₁ ω₂ h₁ h₂ z hz
  let I := NonzeroLattice ω₁ ω₂
  have hprod := (sigma_locallyUniform ω₁ ω₂ h₁ h₂).hasProdLocallyUniformlyOn (s := univ)
  have hpd := hprod.differentiableOn
    (Eventually.of_forall (fun s => DifferentiableOn.fun_finsetProd
      (fun l _ => (factor_differentiable (l.1 : ℂ)).differentiableOn))) isOpen_univ
  have hid : TendstoLocallyUniformlyOn (fun _ : Finset I => (id : ℂ → ℂ)) id atTop univ := by
    intro V hV x hx
    refine ⟨univ, univ_mem, Eventually.of_forall (fun s y hy => ?_)⟩
    exact refl_mem_uniformity hV
  have hlim : TendstoLocallyUniformlyOn
      (fun s : Finset I => fun w : ℂ => w * ∏ l ∈ s, factor 2 (w / (l.1 : ℂ)))
      (sigma ω₁ ω₂) atTop univ :=
    hid.mul₀ hprod continuousOn_id hpd.continuousOn
  have hnonzero : sigma ω₁ ω₂ z ≠ 0 := (sigma_zero_iff ω₁ ω₂ h₁ h₂ z).not.mpr hz
  have hlog := Complex.logDeriv_tendsto isOpen_univ (mem_univ z) hlim
    (Eventually.of_forall (fun s => differentiableOn_id.mul
      (DifferentiableOn.fun_finsetProd (fun l _ => (factor_differentiable _).differentiableOn)))) hnonzero
  have hzet := (tendsto_const_nhds (x := (1 / z : ℂ))).add
    ((zeta_locallyUniform ω₁ ω₂ h₁ h₂).hasSum hz)
  have he : (fun s : Finset I =>
      logDeriv (fun w : ℂ => w * ∏ l ∈ s, factor 2 (w / (l.1 : ℂ))) z) =
      (fun s : Finset I => 1 / z + ∑ l ∈ s, zetaTerm (l.1 : ℂ) z) :=
    funext (finite_sigma_logDeriv hz)
  rw [he] at hlog
  exact tendsto_nhds_unique hlog hzet

lemma restricted_product_limit {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (s : Set (NonzeroLattice ω₁ ω₂)) :
    HasProdLocallyUniformly
      (fun (l : s) z => factor 2 (z / (l.1.1 : ℂ)))
      (fun z => ∏' l : s, factor 2 (z / (l.1.1 : ℂ))) := by
  apply hasProdLocallyUniformly_of_forall_compact
  intro K hK
  obtain ⟨u, hu, hb⟩ := sigma_normal ω₁ ω₂ h₁ h₂ K hK
  simpa only [add_sub_cancel] using (hu.subtype (· ∈ s)).hasProdUniformlyOn_one_add hK
    (Eventually.of_forall (fun l z hz => hb l.1 z hz))
    (fun l => ((factor_differentiable (l.1.1 : ℂ)).continuous.sub continuous_const).continuousOn)

lemma restricted_product_differentiable {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (s : Set (NonzeroLattice ω₁ ω₂)) :
    Differentiable ℂ (fun z => ∏' l : s, factor 2 (z / (l.1.1 : ℂ))) := by
  have h := (restricted_product_limit h₁ h₂ s).hasProdLocallyUniformlyOn (s := univ)
    |>.differentiableOn
      (Eventually.of_forall (fun t => DifferentiableOn.fun_finsetProd
        (fun l _ => (factor_differentiable (l.1.1 : ℂ)).differentiableOn))) isOpen_univ
  intro z
  exact h.differentiableAt (isOpen_univ.mem_nhds (mem_univ z))

lemma product_differentiable {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) :
    Differentiable ℂ (fun z => ∏' l : NonzeroLattice ω₁ ω₂, factor 2 (z / (l.1 : ℂ))) := by
  have h := (sigma_locallyUniform ω₁ ω₂ h₁ h₂).hasProdLocallyUniformlyOn (s := univ)
    |>.differentiableOn
      (Eventually.of_forall (fun t => DifferentiableOn.fun_finsetProd
        (fun l _ => (factor_differentiable (l.1 : ℂ)).differentiableOn))) isOpen_univ
  intro z
  exact h.differentiableAt (isOpen_univ.mem_nhds (mem_univ z))

theorem sigma_simple_zero : Specs.D12Complex.Ch22.ZetaSigmaConvergence.sigma_simple_zero_type := by
  classical
  intro ω₁ ω₂ h₁ h₂ a ha
  have hp := product_differentiable h₁ h₂
  by_cases ha0 : a = 0
  · subst a
    change analyticOrderAt ((id : ℂ → ℂ) * (fun z : ℂ => ∏' l : NonzeroLattice ω₁ ω₂,
      factor 2 (z / (l.1 : ℂ)))) 0 = 1
    rw [analyticOrderAt_mul analyticAt_id (hp.analyticAt 0),
      analyticOrderAt_id, (hp.analyticAt 0).analyticOrderAt_eq_zero.mpr, add_zero]
    simp [factor, Specs.D12Complex.Ch16.CanonicalFactors.factor_value]
  · let l₀ : NonzeroLattice ω₁ ω₂ := ⟨⟨a, ha⟩, fun h => ha0 (congrArg Subtype.val h)⟩
    let s : Set (NonzeroLattice ω₁ ω₂) := {l₀}ᶜ
    let T : ℂ → ℂ := fun z => ∏' l : s, factor 2 (z / (l.1.1 : ℂ))
    have hT := restricted_product_differentiable h₁ h₂ s
    have hT0 : T a ≠ 0 := by
      have hfac (l : s) : factor 2 (a / (l.1.1 : ℂ)) ≠ 0 := by
        change CanonicalFactors.factor 2 (a / (l.1.1 : ℂ)) ≠ 0
        rw [ne_eq, CanonicalFactors.factor_eq_zero_iff]
        intro he
        have hal : a = (l.1.1 : ℂ) := (div_eq_one_iff_eq (nonzero_coe l.1)).mp he
        have heq : l.1 = l₀ := Subtype.ext (Subtype.ext hal.symm)
        exact l.2 (mem_singleton_iff.mpr heq)
      simpa only [add_sub_cancel] using
        tprod_one_add_ne_zero_of_summable
          (f := fun l : s => factor 2 (a / (l.1.1 : ℂ)) - 1)
          (by simpa only [add_sub_cancel] using hfac) ((sigma_summable_at h₁ h₂ a).subtype (· ∈ s))
    have heq : sigma ω₁ ω₂ = (fun z : ℂ => z * (factor 2 (z / a) * T z)) := by
      funext z
      have htail := (restricted_product_limit h₁ h₂ s).hasProd (x := z)
      have hsplit := (HasProd.mul_compl (s := {l₀})
        (f := fun l : NonzeroLattice ω₁ ω₂ => factor 2 (z / (l.1 : ℂ)))
        (hasProd_singleton l₀ (fun l => factor 2 (z / (l.1 : ℂ)))) htail).tprod_eq
      change z * (∏' l : NonzeroLattice ω₁ ω₂, factor 2 (z / (l.1 : ℂ))) = _
      rw [hsplit]
    have hcomp : analyticOrderAt (fun z : ℂ => factor 2 (z / a)) a = 1 := by
      have hi : deriv (fun z : ℂ => z / a) a ≠ 0 := by
        change deriv (fun z : ℂ => id z / a) a ≠ 0
        rw [((hasDerivAt_id a).div_const a).deriv]
        exact one_div_ne_zero ha0
      have h := analyticOrderAt_comp_of_deriv_ne_zero
        (f := CanonicalFactors.factor 2) (g := fun z : ℂ => z / a)
        (differentiable_id.div_const a |>.analyticAt a) hi
      rw [div_self ha0] at h
      exact h.trans (CanonicalFactors.factor_simple_zero 2)
    change analyticOrderAt (sigma ω₁ ω₂) a = 1
    rw [heq]
    change analyticOrderAt ((id : ℂ → ℂ) * ((fun z : ℂ => factor 2 (z / a)) * T)) a = 1
    rw [analyticOrderAt_mul analyticAt_id (((factor_differentiable a).analyticAt a).mul (hT.analyticAt a)),
      analyticAt_id.analyticOrderAt_eq_zero.mpr ha0,
      analyticOrderAt_mul ((factor_differentiable a).analyticAt a) (hT.analyticAt a),
      (hT.analyticAt a).analyticOrderAt_eq_zero.mpr hT0, hcomp, add_zero, zero_add]

lemma off_lattice_eventually {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) (a : ℂ) :
    ∀ᶠ z in 𝓝[≠] a, z ∉ lattice ω₁ ω₂ := by
  let L := WeierstrassSeries.periodPair h₁ h₂
  have hev : ∀ᶠ z in 𝓝 a, z ∈ ((L.lattice : Set ℂ) \ {a})ᶜ := L.compl_lattice_sdiff_singleton_mem_nhds a
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hza
  intro hzl
  exact hz ⟨hzl, hza⟩

lemma sigma_analytic {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) :
    AnalyticOnNhd ℂ (sigma ω₁ ω₂) univ :=
  fun z _ => (show Differentiable ℂ (sigma ω₁ ω₂) from
    fun w => (sigma_entire ω₁ ω₂ h₁ h₂).2 w (mem_univ w)).analyticAt z

lemma logDeriv_eventually_zeta {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) (a : ℂ) :
    logDeriv (sigma ω₁ ω₂) =ᶠ[𝓝[≠] a] zeta ω₁ ω₂ := by
  filter_upwards [off_lattice_eventually h₁ h₂ a] with z hz
  exact sigma_logDeriv ω₁ ω₂ h₁ h₂ z hz

theorem zeta_meromorphic : Specs.D12Complex.Ch22.ZetaSigmaConvergence.zeta_meromorphic_type := by
  intro ω₁ ω₂ h₁ h₂ a
  exact ((sigma_analytic h₁ h₂ a (mem_univ a)).meromorphicAt.logDeriv).congr
    (logDeriv_eventually_zeta h₁ h₂ a)

theorem zeta_pole_order : Specs.D12Complex.Ch22.ZetaSigmaConvergence.zeta_pole_order_type := by
  intro ω₁ ω₂ h₁ h₂ a ha
  have hs := sigma_analytic h₁ h₂ a (mem_univ a)
  have ho : meromorphicOrderAt (sigma ω₁ ω₂) a = 1 := by
    rw [hs.meromorphicOrderAt_eq, sigma_simple_zero ω₁ ω₂ h₁ h₂ a ha]
    rfl
  rw [← meromorphicOrderAt_congr (logDeriv_eventually_zeta h₁ h₂ a)]
  exact meromorphicOrderAt_logDeriv_eq_neg_one hs.meromorphicAt
    (by rw [ho]; norm_num) (by rw [ho]; norm_num)

theorem meromorphic_identities : Specs.D12Complex.Ch22.ZetaSigmaConvergence.meromorphic_identities_type := by
  intro ω₁ ω₂ h₁ h₂
  refine ⟨(zeta_meromorphic ω₁ ω₂ h₁ h₂).deriv,
    (fun a => (sigma_analytic h₁ h₂ a (mem_univ a)).meromorphicAt.logDeriv), fun a => ?_⟩
  refine ⟨?_, logDeriv_eventually_zeta h₁ h₂ a⟩
  filter_upwards [off_lattice_eventually h₁ h₂ a] with z hz
  exact (zeta_derivative ω₁ ω₂ h₁ h₂ z hz).deriv

theorem zeta_principal_part : Specs.D12Complex.Ch22.ZetaSigmaConvergence.zeta_principal_part_type := by
  intro ω₁ ω₂ h₁ h₂ a ha
  have hs := sigma_analytic h₁ h₂ a (mem_univ a)
  obtain ⟨g, hg, hg0, he⟩ := hs.analyticOrderAt_eq_natCast.mp
    (sigma_simple_zero ω₁ ω₂ h₁ h₂ a ha)
  have heq : sigma ω₁ ω₂ =ᶠ[𝓝 a] (fun z => (z - a) * g z) := by
    filter_upwards [he] with z hz
    simpa only [pow_one, smul_eq_mul] using hz
  refine ⟨fun z => deriv g z / g z, hg.deriv.div hg hg0, ?_⟩
  filter_upwards [logDeriv_eventually_zeta h₁ h₂ a,
    heq.filter_mono nhdsWithin_le_nhds,
    heq.deriv.filter_mono nhdsWithin_le_nhds,
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (hg.continuousAt.eventually (eventually_ne_nhds hg0)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hzeta hv hd hgz hgnz hza
  change zeta ω₁ ω₂ z = 1 / (z - a) + deriv g z / g z
  rw [← hzeta]
  change deriv (sigma ω₁ ω₂) z / sigma ω₁ ω₂ z = _
  rw [hd, hv, deriv_fun_mul (c := fun w : ℂ => w - a) (d := g)
    (differentiableAt_id.sub_const a) hgz.differentiableAt]
  simp only [deriv_sub_const, deriv_id'', one_mul]
  field_simp [hgnz, sub_ne_zero.mpr hza]

end D12Complex.Ch22.ZetaSigmaConvergence
