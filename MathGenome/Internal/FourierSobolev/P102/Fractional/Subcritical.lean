import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Subcritical
import MathGenome.Internal.FourierSobolev.P102.Fractional.Density
import MathGenome.Internal.FourierSobolev.P102.Fractional.Extension
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
The subcritical embedding from paper.tex, Theorem U5-05.

For a smooth compactly supported real function, its critical moment `M` is
finite. At a point with `a = ‖f x‖ / 2 > 0`, Chebyshev bounds the high level
set by `M / a ^ q`. A ball of twice that volume therefore contains at least
`M / a ^ q` of its complement. Integrating the resulting pointwise energy
bound gives `M ^ (p / q) ≤ C * energy`. The zero-moment case is separate.
Density and Fatou remove the smoothness and support restrictions, and norm
contraction treats real or complex scalars. Restriction after extension gives
the bounded-domain estimate.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace P102.Fractional
universe u

variable {d : ℕ} {s : ℝ} {p : ℝ≥0∞}

theorem sobolevExponent_ne_top : sobolevExponent d s p ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem sobolevExponent_toReal (hd : 0 < d) (_hs : 0 < s)
    (hp : p ≠ 0) (hpt : p ≠ ∞) (hsp : s * p.toReal < (d : ℝ)) :
    (sobolevExponent d s p).toReal =
      (d : ℝ) * p.toReal / ((d : ℝ) - s * p.toReal) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hp' := ENNReal.toReal_pos hp hpt
  exact ENNReal.toReal_ofReal (le_of_lt (div_pos (mul_pos hd' hp') (sub_pos.mpr hsp)))

theorem lt_sobolevExponent (hd : 0 < d) (hs : 0 < s)
    (hp : p ≠ 0) (hpt : p ≠ ∞) (hsp : s * p.toReal < (d : ℝ)) :
    p < sobolevExponent d s p := by
  have hp' := ENNReal.toReal_pos hp hpt
  apply (ENNReal.toReal_lt_toReal hpt sobolevExponent_ne_top).mp
  rw [sobolevExponent_toReal hd hs hp hpt hsp]
  apply (lt_div_iff₀ (sub_pos.mpr hsp)).mpr
  nlinarith [mul_pos hs hp']

/-- The exact reciprocal relation used by the fractional embedding. -/
theorem sobolevExponent_reciprocal (hd : 0 < d) (hs : 0 < s)
    (hp : p ≠ 0) (hpt : p ≠ ∞) (hsp : s * p.toReal < (d : ℝ)) :
    1 / (sobolevExponent d s p).toReal = 1 / p.toReal - s / (d : ℝ) := by
  rw [sobolevExponent_toReal hd hs hp hpt hsp]
  have hd' : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr hd).ne'
  have hp' : p.toReal ≠ 0 := (ENNReal.toReal_pos hp hpt).ne'
  field_simp

variable {𝕜 : Type*} [RCLike 𝕜] {G : Set (Domain d)} [Fact (1 ≤ p)]

/-- The graph's second coordinate has precisely the seminorm as its extended
norm. This also supplies its finiteness without using `toReal` on infinity. -/
theorem seminorm_eq_enorm_snd (hpt : p ≠ ∞) (u : Space 𝕜 G s p) :
    seminorm G s p (firstProjection u) = ‖u.val.snd‖ₑ := by
  rw [Lp.enorm_def, eLpNorm_congr_ae u.property,
    eLpNorm_increment_eq_seminorm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      hpt (Lp.aestronglyMeasurable _)]
  rfl

theorem seminorm_firstProjection_ne_top (hpt : p ≠ ∞) (u : Space 𝕜 G s p) :
    seminorm G s p (firstProjection u) ≠ ∞ := by
  rw [seminorm_eq_enorm_snd hpt]
  exact enorm_ne_top

/-- Full-norm identity with no loss of information at infinity. -/
theorem enorm_space (hpt : p ≠ ∞) (u : Space 𝕜 G s p) :
    ‖u‖ₑ = eLpNorm (firstProjection u) p (domainMeasure G) +
      seminorm G s p (firstProjection u) := by
  rw [← ofReal_norm, space_norm hpt, ENNReal.ofReal_add (norm_nonneg _)
    ENNReal.toReal_nonneg, ofReal_norm, Lp.enorm_def,
    ENNReal.ofReal_toReal (seminorm_firstProjection_ne_top hpt u)]

/-- The seminorm is controlled by the inherited sum norm. -/
theorem seminorm_le_enorm (hpt : p ≠ ∞) (u : Space 𝕜 G s p) :
    seminorm G s p (firstProjection u) ≤ ‖u‖ₑ := by
  rw [enorm_space hpt]
  exact le_add_left le_rfl

/-- The first coordinate is continuous for the actual sum norm. -/
theorem continuous_firstProjection :
    Continuous (@firstProjection d 𝕜 _ G s p _) :=
  (WithLp.continuous_fst 1 _ _).comp continuous_subtype_val

/-- Continuity of the seminorm on the graph, without continuity assumptions
on the functions representing its elements. -/
theorem continuous_seminorm_firstProjection (hpt : p ≠ ∞) :
    Continuous (fun u : Space 𝕜 G s p => seminorm G s p (firstProjection u)) := by
  simp_rw [seminorm_eq_enorm_snd hpt]
  exact ((WithLp.continuous_snd 1 _ _).comp continuous_subtype_val).enorm

/-- Fatou passes a uniform homogeneous estimate from the dense smooth classes
to every whole-space class. The upper bounds converge in the seminorm itself,
so this step introduces no zero-order term. -/
theorem subcritical_bound_of_dense (hpt : p ≠ ∞) {q : ℝ≥0∞} {C : ℝ≥0}
    (hDense : Dense (smoothCompactElements (d := d) 𝕜 s p))
    (hSmooth : ∀ v ∈ smoothCompactElements (d := d) 𝕜 s p,
      eLpNorm (firstProjection v) q (domainMeasure Set.univ) ≤
        (C : ℝ≥0∞) * seminorm Set.univ s p (firstProjection v))
    (u : Space 𝕜 (Set.univ : Set (Domain d)) s p) :
    eLpNorm (firstProjection u) q (domainMeasure Set.univ) ≤
      (C : ℝ≥0∞) * seminorm Set.univ s p (firstProjection u) := by
  obtain ⟨v, hv, hvu⟩ := mem_closure_iff_seq_limit.mp (hDense u)
  have hfirst : Tendsto (fun n => firstProjection (v n)) atTop (𝓝 (firstProjection u)) :=
    (continuous_firstProjection.tendsto u).comp hvu
  obtain ⟨a, ha, halim⟩ := (tendstoInMeasure_of_tendsto_Lp hfirst).exists_seq_tendsto_ae
  have hboundlim : Tendsto
      (fun n => (C : ℝ≥0∞) * seminorm Set.univ s p (firstProjection (v (a n))))
      atTop (𝓝 ((C : ℝ≥0∞) * seminorm Set.univ s p (firstProjection u))) :=
    ENNReal.Tendsto.const_mul
      ((continuous_seminorm_firstProjection hpt).tendsto u |>.comp
        (hvu.comp ha.tendsto_atTop)) (Or.inr ENNReal.coe_ne_top)
  apply (Lp.eLpNorm_lim_le_liminf_eLpNorm
    (fun n => Lp.aestronglyMeasurable (firstProjection (v (a n)) ))
    (firstProjection u) (Lp.aestronglyMeasurable _) halim).trans
  exact (Filter.liminf_le_liminf (Eventually.of_forall
    (fun n => hSmooth (v (a n)) (hv (a n))))).trans_eq hboundlim.liminf_eq

/-- Taking absolute value does not increase the Gagliardo seminorm. This is
the bridge from real scalar estimates to arbitrary real or complex scalars. -/
theorem seminorm_norm_le (hpt : p ≠ ∞) {f : Domain d → 𝕜}
    (hf : AEStronglyMeasurable f (domainMeasure G)) :
    seminorm G s p (fun x => ‖f x‖) ≤ seminorm G s p f := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  rw [← eLpNorm_increment_eq_seminorm hp0 hpt hf.norm,
    ← eLpNorm_increment_eq_seminorm hp0 hpt hf]
  apply eLpNorm_mono (increment_aestronglyMeasurable hf.norm)
  intro z
  exact abs_norm_sub_norm_le (f z.1) (f z.2)

/-- The norm of a representative is itself an element of the real Gagliardo
space, including at p = 1. -/
def normElement (u : Space 𝕜 G s p) : Space ℝ G s p :=
  ofMemLp (fun x => ‖firstProjection u x‖) (Lp.memLp _).norm
    (((memLp_congr_ae u.property).mp (Lp.memLp u.val.snd)).norm.mono'
      (increment_aestronglyMeasurable (Lp.aestronglyMeasurable _).norm)
      (Eventually.of_forall fun z => abs_norm_sub_norm_le
        (firstProjection u z.1) (firstProjection u z.2)))

theorem normElement_ae (u : Space 𝕜 G s p) :
    (firstProjection (normElement u) : Domain d → ℝ) =ᵐ[domainMeasure G]
      (fun x => ‖firstProjection u x‖) :=
  ofMemLp_ae _ _ _

/-- A bound for all real Gagliardo classes at the given exponents implies the
identical bound for any RCLike scalar field, with the same constant. -/
theorem subcritical_bound_of_real (hpt : p ≠ ∞) {q : ℝ≥0∞} {C : ℝ≥0}
    (hReal : ∀ v : Space ℝ (Set.univ : Set (Domain d)) s p,
      eLpNorm (firstProjection v) q (domainMeasure Set.univ) ≤
        (C : ℝ≥0∞) * seminorm Set.univ s p (firstProjection v))
    (u : Space 𝕜 (Set.univ : Set (Domain d)) s p) :
    eLpNorm (firstProjection u) q (domainMeasure Set.univ) ≤
      (C : ℝ≥0∞) * seminorm Set.univ s p (firstProjection u) := by
  calc
    _ = eLpNorm (firstProjection (normElement u)) q (domainMeasure Set.univ) := by
      rw [eLpNorm_congr_ae (normElement_ae u), eLpNorm_norm _ (Lp.aestronglyMeasurable _)]
    _ ≤ (C : ℝ≥0∞) * seminorm Set.univ s p (firstProjection (normElement u)) :=
      hReal _
    _ ≤ (C : ℝ≥0∞) * seminorm Set.univ s p (firstProjection u) := by
      apply mul_le_mul_right
      rw [seminorm_congr (normElement_ae u)]
      exact seminorm_norm_le hpt (Lp.aestronglyMeasurable _)

/-- Once the homogeneous whole-space assertion is proved, the given extension
premise yields the original bounded-domain assertion. Neither hypothesis is
an assumed implementation: both are explicit propositions in this reduction. -/
theorem subcritical_bounded_of_whole
    (hExtension : Specs.P102.Fractional.Extension.extension.{u})
    (hWhole : Specs.P102.Fractional.Subcritical.wholeSpace.{u}) :
    Specs.P102.Fractional.Subcritical.boundedDomain.{u} := by
  intro n G hG s hs0 hs1 p _ hpt hsp 𝕜 _
  obtain ⟨K, hK, D, E, hE, hSupport, hBound⟩ :=
    hExtension n G hG s hs0 hs1 p hpt 𝕜
  obtain ⟨C, hC⟩ := hWhole (n + 1) (Nat.succ_pos _) s hs0 hs1 p hpt hsp 𝕜
  refine ⟨C * D, fun u => ?_⟩
  have hEu := hC (E u)
  have hmem : MemLp (firstProjection u) (sobolevExponent (n + 1) s p)
      (domainMeasure G) := by
    apply (memLp_congr_ae (hE u)).mp
    apply hEu.1.mono_measure
    simp only [domainMeasure, Measure.restrict_univ]
    exact Measure.restrict_le_self
  refine ⟨hmem, ?_⟩
  calc
    _ = eLpNorm (firstProjection (E u)) (sobolevExponent (n + 1) s p)
        (domainMeasure G) := eLpNorm_congr_ae (hE u).symm
    _ ≤ eLpNorm (firstProjection (E u)) (sobolevExponent (n + 1) s p)
        (domainMeasure Set.univ) := eLpNorm_mono_measure _ (by
          simp only [domainMeasure, Measure.restrict_univ]
          exact Measure.restrict_le_self)
    _ ≤ (C : ℝ≥0∞) * seminorm Set.univ s p (firstProjection (E u)) := hEu.2
    _ ≤ (C : ℝ≥0∞) * ‖E u‖ₑ := mul_le_mul_right (seminorm_le_enorm hpt _) _
    _ ≤ (C : ℝ≥0∞) * ((D : ℝ≥0∞) * ‖u‖ₑ) := by
      apply mul_le_mul_right
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (NNReal.coe_nonneg D)]
      apply ENNReal.ofReal_le_ofReal
      simpa only [space_norm hpt u] using hBound u
    _ = ((C * D : ℝ≥0) : ℝ≥0∞) *
        (eLpNorm (firstProjection u) p (domainMeasure G) +
          seminorm G s p (firstProjection u)) := by
      rw [ENNReal.coe_mul, mul_assoc, enorm_space hpt]

/-- The smooth test-function formulation used by the density reduction.
It is proved below by `real_smooth_subcritical_bound`. -/
def RealSmoothSubcriticalBound : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (s : ℝ), 0 < s → s < 1 →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → s * p.toReal < (d : ℝ) →
  ∃ C : ℝ≥0, ∀ f : Domain d → ℝ,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f →
    eLpNorm f (sobolevExponent d s p) (domainMeasure Set.univ) ≤
      (C : ℝ≥0∞) * seminorm Set.univ s p f

/-- Real smooth bounds, density, Fatou, and the norm contraction together
give the full original whole-space assertion, with no support restriction.
The smooth bound is proved below by `real_smooth_subcritical_bound`. -/
theorem subcritical_whole_of_real_smooth
    (hSmooth : RealSmoothSubcriticalBound) :
    Specs.P102.Fractional.Subcritical.wholeSpace.{u} := by
  intro d hd s hs0 hs1 p _ hpt hsp 𝕜 _
  obtain ⟨C, hC⟩ := hSmooth d hd s hs0 hs1 p hpt hsp
  have hReal : ∀ v : Space ℝ (Set.univ : Set (Domain d)) s p,
      eLpNorm (firstProjection v) (sobolevExponent d s p) (domainMeasure Set.univ) ≤
        (C : ℝ≥0∞) * seminorm Set.univ s p (firstProjection v) := by
    apply subcritical_bound_of_dense hpt
      (smoothCompact_dense d hd ℝ s hs0 hs1 p hpt)
    intro v hv
    obtain ⟨f, hfs, hfc, hfv⟩ := hv
    rw [eLpNorm_congr_ae hfv.symm, seminorm_congr hfv.symm]
    exact hC f hfs hfc
  refine ⟨C, fun u => ?_⟩
  have hb := subcritical_bound_of_real hpt hReal u
  refine ⟨hb.trans_lt ?_, hb⟩
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top
    (lt_top_iff_ne_top.mpr (seminorm_firstProjection_ne_top hpt u))

/-- The extension premise and a real smooth estimate suffice for the domain
estimate. This is a reduction lemma; it does not define
either of the original actual targets. -/
theorem subcritical_domain_of_real_smooth
    (hExtension : Specs.P102.Fractional.Extension.extension.{u})
    (hSmooth : RealSmoothSubcriticalBound) :
    Specs.P102.Fractional.Subcritical.boundedDomain.{u} :=
  subcritical_bounded_of_whole hExtension (subcritical_whole_of_real_smooth hSmooth)

/-- A ball with much more mass than the high level set forces a lower bound
for the inner Gagliardo integral. No diagonal contribution is used. -/
theorem inner_energy_ball_lower_bound {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {f : Domain d → 𝕜} (hf : Continuous f) {x : Domain d} {a R k r : ℝ}
    (ha : 0 < a) (hx : 2 * a ≤ ‖f x‖) (hk : 0 ≤ k) (hr : 0 ≤ r) :
    (ENNReal.ofReal a ^ r / ENNReal.ofReal R ^ k) *
        (volume (Metric.ball x R) - volume {y | a < ‖f y‖}) ≤
      ∫⁻ y, if x = y then 0 else
        ‖f x - f y‖ₑ ^ r / ENNReal.ofReal ‖x - y‖ ^ k := by
  let T := Metric.ball x R \ {y | a < ‖f y‖}
  have hT : MeasurableSet T := measurableSet_ball.diff
    (isOpen_lt continuous_const hf.norm).measurableSet
  calc
    _ ≤ (ENNReal.ofReal a ^ r / ENNReal.ofReal R ^ k) * volume T :=
      mul_le_mul_right le_measure_sdiff _
    _ = ∫⁻ y in T, ENNReal.ofReal a ^ r / ENNReal.ofReal R ^ k :=
      (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ y in T, if x = y then 0 else
        ‖f x - f y‖ₑ ^ r / ENNReal.ofReal ‖x - y‖ ^ k := by
      apply setLIntegral_mono' hT
      intro y hy
      have hyf : ‖f y‖ ≤ a := le_of_not_gt hy.2
      have hxy : x ≠ y := by
        intro h
        subst y
        linarith
      rw [ite_eq_right hxy]
      apply ENNReal.div_le_div
      · apply ENNReal.rpow_le_rpow _ hr
        rw [← ofReal_norm]
        apply ENNReal.ofReal_le_ofReal
        have := norm_sub_norm_le (f x) (f y)
        linarith
      · apply ENNReal.rpow_le_rpow _ hk
        apply ENNReal.ofReal_le_ofReal
        exact le_of_lt (by
          simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy.1)
    _ ≤ ∫⁻ y, if x = y then 0 else
        ‖f x - f y‖ₑ ^ r / ENNReal.ofReal ‖x - y‖ ^ k :=
      lintegral_mono' Measure.restrict_le_self le_rfl

/-- Chebyshev with the exact moment appearing in the proof. -/
theorem measure_high_level_le_moment {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {f : Domain d → 𝕜} (hf : Continuous f) {a q : ℝ}
    (ha : 0 < a) (hq : 0 ≤ q) :
    volume {y | a < ‖f y‖} ≤
      (∫⁻ y, ‖f y‖ₑ ^ q) / ENNReal.ofReal a ^ q := by
  have hpow0 := (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr ha)
    ENNReal.ofReal_ne_top (p := q)).ne'
  have hpowt := ENNReal.rpow_ne_top_of_nonneg hq ENNReal.ofReal_ne_top (x := ENNReal.ofReal a)
  apply le_trans (measure_mono (fun y hy => ?_))
    (meas_ge_le_lintegral_div (hf.enorm.measurable.pow_const q).aemeasurable hpow0 hpowt)
  apply ENNReal.rpow_le_rpow _ hq
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (le_of_lt hy)

/-- Balls can be chosen with twice any specified finite positive mass. -/
theorem exists_ball_volume_twice {d : ℕ} (hd : 0 < d) (x : Domain d)
    {m : ℝ} (hm : 0 < m) :
    ∃ R : ℝ, 0 < R ∧
      volume (Metric.ball x R) = ENNReal.ofReal (2 * m) ∧
      R = (2 * m / (volume (Metric.ball (0 : Domain d) 1)).toReal) ^
        (1 / (d : ℝ)) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let v := volume (Metric.ball (0 : Domain d) 1)
  have hv0 : v ≠ 0 := (Metric.isOpen_ball.measure_pos volume
    (Metric.nonempty_ball.mpr zero_lt_one)).ne'
  have hvt : v ≠ ∞ := (measure_ball_lt_top).ne
  have hv : 0 < v.toReal := ENNReal.toReal_pos hv0 hvt
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  let R := (2 * m / v.toReal) ^ (1 / (d : ℝ))
  have hbase : 0 < 2 * m / v.toReal := div_pos (by linarith) hv
  have hR : 0 < R := Real.rpow_pos_of_pos hbase _
  refine ⟨R, hR, ?_, rfl⟩
  rw [Measure.addHaar_ball volume x hR.le, finrank_euclideanSpace,
    Fintype.card_fin]
  have hpow : R ^ d = 2 * m / v.toReal := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
    rw [one_div_mul_cancel hd'.ne', Real.rpow_one]
  rw [hpow]
  change ENNReal.ofReal (2 * m / v.toReal) * v = _
  conv_lhs => rhs; rw [← ENNReal.ofReal_toReal hvt]
  rw [← ENNReal.ofReal_mul hbase.le]
  congr 1
  exact div_mul_cancel₀ _ hv.ne'

/-- The scaling algebra, kept in real powers with strictly positive bases. -/
theorem ball_moment_scaling {a A v D k r q : ℝ}
    (ha : 0 < a) (hA : 0 < A) (hv : 0 < v) (_hD : 0 < D) :
    a ^ r * (A / a ^ q) /
        (((2 * (A / a ^ q) / v) ^ (1 / D)) ^ k) =
      (v / 2) ^ (k / D) * A ^ (1 - k / D) *
        a ^ (r - q * (1 - k / D)) := by
  have haq := Real.rpow_pos_of_pos ha q
  have hm : 0 < A / a ^ q := div_pos hA haq
  have hv2 : 0 < v / 2 := by positivity
  have heq : 2 * (A / a ^ q) / v = (A / a ^ q) / (v / 2) := by ring
  rw [← Real.rpow_mul (by positivity : 0 ≤ 2 * (A / a ^ q) / v),
    show 1 / D * k = k / D by ring, heq,
    Real.div_rpow hm.le hv2.le]
  calc
    _ = (v / 2) ^ (k / D) *
        ((A / a ^ q) / (A / a ^ q) ^ (k / D)) * a ^ r := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    _ = (v / 2) ^ (k / D) * (A / a ^ q) ^ (1 - k / D) * a ^ r := by
      rw [Real.rpow_sub hm, Real.rpow_one]
    _ = (v / 2) ^ (k / D) * A ^ (1 - k / D) *
        (a ^ r / a ^ (q * (1 - k / D))) := by
      rw [Real.div_rpow hA.le haq.le, ← Real.rpow_mul ha.le]
      ring
    _ = _ := by rw [Real.rpow_sub ha]

/-- The inner energy controls the critical moment, with a constant independent
of the function. The moment bound used here is finite and strictly positive. -/
theorem inner_energy_critical_lower_bound {d : ℕ} (hd : 0 < d)
    {f : Domain d → ℝ} (hf : Continuous f) {A r q k : ℝ}
    (hA : 0 < A) (hr : 0 < r) (hq : 0 < q) (hk : 0 ≤ k)
    (hexp : r - q * (1 - k / (d : ℝ)) = q)
    (hMoment : (∫⁻ y, ‖f y‖ₑ ^ q) ≤ ENNReal.ofReal A)
    (x : Domain d) :
    ENNReal.ofReal (((volume (Metric.ball (0 : Domain d) 1)).toReal / 2) ^
        (k / (d : ℝ)) / 2 ^ q * A ^ (1 - k / (d : ℝ)) * ‖f x‖ ^ q) ≤
      ∫⁻ y, if x = y then 0 else
        ‖f x - f y‖ₑ ^ r / ENNReal.ofReal ‖x - y‖ ^ k := by
  by_cases hx0 : f x = 0
  · simp only [hx0, norm_zero, Real.zero_rpow hq.ne', mul_zero, ENNReal.ofReal_zero]
    exact bot_le
  have hx : 0 < ‖f x‖ := norm_pos_iff.mpr hx0
  let a := ‖f x‖ / 2
  have ha : 0 < a := by dsimp [a]; positivity
  let m := A / a ^ q
  have hm : 0 < m := div_pos hA (Real.rpow_pos_of_pos ha q)
  let v := (volume (Metric.ball (0 : Domain d) 1)).toReal
  have hv : 0 < v := ENNReal.toReal_pos
    ((Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr zero_lt_one)).ne')
    (measure_ball_lt_top.ne)
  obtain ⟨R, hR, hBR, hRe⟩ := exists_ball_volume_twice hd x hm
  have hhigh : volume {y | a < ‖f y‖} ≤ ENNReal.ofReal m := by
    refine (measure_high_level_le_moment hf ha hq.le).trans ?_
    calc
      _ ≤ ENNReal.ofReal A / ENNReal.ofReal a ^ q :=
        ENNReal.div_le_div hMoment le_rfl
      _ = _ := by
        rw [ENNReal.ofReal_rpow_of_pos ha, ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos ha q)]
  have hmass : ENNReal.ofReal m ≤ volume (Metric.ball x R) - volume {y | a < ‖f y‖} := by
    apply ENNReal.le_sub_of_add_le_right (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hhigh)
    calc
      _ ≤ ENNReal.ofReal m + ENNReal.ofReal m := add_le_add le_rfl hhigh
      _ = _ := by rw [hBR, ← ENNReal.ofReal_add hm.le hm.le]; congr 1; ring
  have hinner := inner_energy_ball_lower_bound (x := x) hf ha (by dsimp [a]; linarith) hk hr.le
    (R := R)
  have hscaled : (ENNReal.ofReal a ^ r / ENNReal.ofReal R ^ k) * ENNReal.ofReal m ≤
      ∫⁻ y, if x = y then 0 else
        ‖f x - f y‖ₑ ^ r / ENNReal.ofReal ‖x - y‖ ^ k :=
    (mul_le_mul_right hmass _).trans hinner
  convert hscaled using 1
  rw [ENNReal.ofReal_rpow_of_pos ha, ENNReal.ofReal_rpow_of_pos hR,
    ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hR k),
    ← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg hR.le _))]
  congr 1
  rw [hRe]
  change (v / 2) ^ (k / (d : ℝ)) / 2 ^ q * A ^ (1 - k / (d : ℝ)) * ‖f x‖ ^ q =
    a ^ r / ((2 * (A / a ^ q) / v) ^ (1 / (d : ℝ))) ^ k * (A / a ^ q)
  conv_rhs => rw [div_mul_eq_mul_div]
  rw [ball_moment_scaling ha hA hv (Nat.cast_pos.mpr hd), hexp]
  dsimp only [a]
  rw [Real.div_rpow hx.le (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Integration of the ball estimate. Finiteness is needed only for the
moment of the smooth compact test function, never as an extra target hypothesis. -/
theorem critical_moment_energy_lower_bound {d : ℕ} (hd : 0 < d)
    {f : Domain d → ℝ} (hf : Continuous f) {r q k : ℝ}
    (hr : 0 < r) (hq : 0 < q) (hk : 0 ≤ k)
    (hexp : r - q * (1 - k / (d : ℝ)) = q)
    (hfinite : (∫⁻ y, ‖f y‖ₑ ^ q) ≠ ∞) :
    ENNReal.ofReal (((volume (Metric.ball (0 : Domain d) 1)).toReal / 2) ^
        (k / (d : ℝ)) / 2 ^ q) *
        (∫⁻ y, ‖f y‖ₑ ^ q) ^ (2 - k / (d : ℝ)) ≤
      ∫⁻ x, ∫⁻ y, if x = y then 0 else
        ‖f x - f y‖ₑ ^ r / ENNReal.ofReal ‖x - y‖ ^ k := by
  let M := ∫⁻ y, ‖f y‖ₑ ^ q
  let A := M.toReal
  let K := ((volume (Metric.ball (0 : Domain d) 1)).toReal / 2) ^
    (k / (d : ℝ)) / 2 ^ q
  have hpowpos : 0 < 2 - k / (d : ℝ) := by nlinarith
  by_cases hM : M = 0
  · change ENNReal.ofReal K * M ^ (2 - k / (d : ℝ)) ≤ _
    rw [hM, ENNReal.zero_rpow_of_pos hpowpos, mul_zero]
    exact bot_le
  have hA : 0 < A := ENNReal.toReal_pos hM hfinite
  have hMreal : ENNReal.ofReal A = M := ENNReal.ofReal_toReal hfinite
  have hK : 0 ≤ K := div_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (by norm_num) _)
  have hpoint := inner_energy_critical_lower_bound hd hf hA hr hq hk hexp
    (le_of_eq hMreal.symm)
  have hi := lintegral_mono (μ := volume) hpoint
  have hcalc : (∫⁻ x, ENNReal.ofReal (K * A ^ (1 - k / (d : ℝ)) * ‖f x‖ ^ q)) =
      ENNReal.ofReal K * M ^ (2 - k / (d : ℝ)) := by
    simp_rw [ENNReal.ofReal_mul (mul_nonneg hK (Real.rpow_nonneg hA.le _)),
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq.le, ofReal_norm]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    change ENNReal.ofReal (K * A ^ (1 - k / (d : ℝ))) * M = _
    rw [← hMreal, ENNReal.ofReal_rpow_of_pos hA,
      ← ENNReal.ofReal_mul (mul_nonneg hK (Real.rpow_nonneg hA.le _)),
      ← ENNReal.ofReal_mul hK]
    congr 1
    rw [show 2 - k / (d : ℝ) = (1 - k / (d : ℝ)) + 1 by ring,
      Real.rpow_add hA, Real.rpow_one]
    ring
  rw [← hcalc]
  exact hi

/-- The real smooth homogeneous estimate, proved by selecting a ball using
the finite critical moment. This proof also covers p = 1. -/
theorem real_smooth_subcritical_bound : RealSmoothSubcriticalBound := by
  intro d hd s hs0 hs1 p _ hpt hsp
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  let q := sobolevExponent d s p
  have hq0 : q ≠ 0 := (lt_trans (pos_iff_ne_zero.mpr hp0)
    (lt_sobolevExponent hd hs0 hp0 hpt hsp)).ne'
  have hqt : q ≠ ∞ := sobolevExponent_ne_top
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  let k := (d : ℝ) + s * p.toReal
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have he : p.toReal - q.toReal * (1 - k / (d : ℝ)) = q.toReal := by
    dsimp [q, k]
    rw [sobolevExponent_toReal hd hs0 hp0 hpt hsp]
    field_simp [hd'.ne', (sub_pos.mpr hsp).ne', mul_comm]
    ring
  have he' : 2 - k / (d : ℝ) = p.toReal / q.toReal := by
    apply (eq_div_iff hqr.ne').mpr
    nlinarith [he]
  let K := ((volume (Metric.ball (0 : Domain d) 1)).toReal / 2) ^
    (k / (d : ℝ)) / 2 ^ q.toReal
  have hv : 0 < (volume (Metric.ball (0 : Domain d) 1)).toReal :=
    ENNReal.toReal_pos
      ((Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr zero_lt_one)).ne')
      measure_ball_lt_top.ne
  have hK : 0 < K := div_pos
    (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos (by norm_num) _)
  let C : ℝ≥0 := ⟨K ^ (-1 / p.toReal), (Real.rpow_pos_of_pos hK _).le⟩
  refine ⟨C, fun f hfs hfc => ?_⟩
  have hfm : MemLp f q volume := hfs.continuous.memLp_of_hasCompactSupport hfc
  have hfinite := (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hq0 hqt hfm).ne
  have hb := critical_moment_energy_lower_bound hd hfs.continuous hpr hqr hk he hfinite
  change ENNReal.ofReal K * (∫⁻ y, ‖f y‖ₑ ^ q.toReal) ^ (2 - k / (d : ℝ)) ≤ _ at hb
  rw [he'] at hb
  have hroot := ENNReal.rpow_le_rpow hb (one_div_pos.mpr hpr).le
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hpr).le,
    ENNReal.ofReal_rpow_of_pos hK, ← ENNReal.rpow_mul,
    show p.toReal / q.toReal * (1 / p.toReal) = 1 / q.toReal by field_simp] at hroot
  have hcancel : ENNReal.ofReal (K ^ (-1 / p.toReal)) *
      ENNReal.ofReal (K ^ (1 / p.toReal)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hK.le _), ← Real.rpow_add hK]
    rw [show -1 / p.toReal + 1 / p.toReal = 0 by ring, Real.rpow_zero,
      ENNReal.ofReal_one]
  change eLpNorm f q (domainMeasure Set.univ) ≤
    (C : ℝ≥0∞) * seminorm Set.univ s p f
  simp only [domainMeasure, Measure.restrict_univ]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt hfs.continuous.aestronglyMeasurable]
  rw [← ENNReal.ofReal_coe_nnreal]
  simp only [seminorm, energy, domainMeasure, Measure.restrict_univ]
  change (∫⁻ y, ‖f y‖ₑ ^ q.toReal) ^ (1 / q.toReal) ≤
    ENNReal.ofReal (K ^ (-1 / p.toReal)) *
      (∫⁻ x, ∫⁻ y, if x = y then 0 else
        ‖f x - f y‖ₑ ^ p.toReal / ENNReal.ofReal ‖x - y‖ ^ k) ^ (1 / p.toReal)
  calc
    _ = ENNReal.ofReal (K ^ (-1 / p.toReal)) *
        (ENNReal.ofReal (K ^ (1 / p.toReal)) *
          (∫⁻ y, ‖f y‖ₑ ^ q.toReal) ^ (1 / q.toReal)) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ _ := mul_le_mul_right hroot _

/-- The homogeneous whole-space fractional Sobolev estimate for every
Gagliardo class, including p = 1, with no support hypothesis. -/
theorem subcritical_whole_space :
    Specs.P102.Fractional.Subcritical.wholeSpace.{u} :=
  subcritical_whole_of_real_smooth.{u} real_smooth_subcritical_bound

/-- The bounded Lipschitz domain estimate, obtained by restriction after the
proved bounded linear extension. -/
theorem subcritical_bounded_domain :
    Specs.P102.Fractional.Subcritical.boundedDomain.{u} :=
  subcritical_bounded_of_whole.{u} bounded_linear_extension.{u}
    subcritical_whole_space.{u}

end P102.Fractional
