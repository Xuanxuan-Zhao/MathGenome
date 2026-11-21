import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.FractionalSobolev
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace ExpandedFA.PartIV.FractionalSobolev

/-- The two pointwise controls combined before integration. -/
def multiplierIncrementBound {d : ℕ} (M L : ℝ≥0) (h : Fin d → ℝ) : ℝ≥0 :=
  min (L * ‖WithLp.toLp 2 h‖₊) (2 * M)

/-- The integral in the quantitative multiplier estimate, with zero diagonal. -/
def multiplierIncrementIntegral (d : ℕ) (s : ℝ) (p : ℝ≥0∞) (M L : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ h : Fin d → ℝ, differenceKernel s p h * (multiplierIncrementBound M L h : ℝ≥0∞) ^ p.toReal

private lemma multiplierIncrementBound_measurable {d : ℕ} (M L : ℝ≥0) :
    Measurable (multiplierIncrementBound (d := d) M L) := by
  exact (continuous_const.mul (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).nnnorm).min
    continuous_const |>.measurable

private lemma multiplier_increment_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a : (Fin d → ℝ) → 𝕜) (M L : ℝ≥0)
    (hM : ∀ x, ‖a x‖ ≤ M)
    (hL : ∀ x y, ‖a x - a y‖ ≤ L * euclideanLength (x - y)) (x h : Fin d → ℝ) :
    ‖a (x + h) - a x‖ ≤ (multiplierIncrementBound M L h : ℝ) := by
  simp only [multiplierIncrementBound, NNReal.coe_min, NNReal.coe_mul, NNReal.coe_ofNat,
    coe_nnnorm]
  refine le_min ?_ ((norm_sub_le _ _).trans ?_)
  · simpa only [add_sub_cancel_left, euclideanLength] using hL (x + h) x
  · linarith [hM (x + h), hM x]

/-- The original quantitative estimate for the pth power of the difference seminorm. -/
theorem fractional_multiplier_energy_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (a : (Fin d → ℝ) → 𝕜) (M L : ℝ≥0)
    (hM : ∀ x, ‖a x‖ ≤ M)
    (hL : ∀ x y, ‖a x - a y‖ ≤ L * euclideanLength (x - y))
    (u : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) :
    let v := lpMultiply p a M L hM hL u
    ‖v‖ ≤ M * ‖u‖ ∧
    differenceEnergy s p v ≤ (2 : ℝ≥0∞) ^ (p.toReal - 1) *
      ((M : ℝ≥0∞) ^ p.toReal * differenceEnergy s p u +
        ‖u‖ₑ ^ p.toReal * multiplierIncrementIntegral d s p M L) := by
  let v := lpMultiply p a M L hM hL u
  change ‖v‖ ≤ M * ‖u‖ ∧ _
  have hv : v =ᵐ[volume] fun x => a x * u x := lpMultiply_representative p a M L hM hL u
  constructor
  · apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hv] with x hx
    rw [hx, norm_mul]
    exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
  let q := p.toReal
  let C : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (q - 1)
  let D := multiplierIncrementBound (d := d) M L
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))
  have hq : 1 ≤ q := by
    simpa [q] using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hu := (Lp.stronglyMeasurable u).measurable
  have hpow : (∫⁻ x, ‖u x‖ₑ ^ q) = ‖u‖ₑ ^ q := by
    rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (Lp.aestronglyMeasurable u),
      ← ENNReal.rpow_mul, one_div_mul_cancel (zero_lt_one.trans_le hq).ne', ENNReal.rpow_one]
  have hincrement (h : Fin d → ℝ) :
      (∫⁻ x, ‖v (x + h) - v x‖ₑ ^ q) ≤ C *
        ((M : ℝ≥0∞) ^ q * (∫⁻ x, ‖u (x + h) - u x‖ₑ ^ q) +
          (D h : ℝ≥0∞) ^ q * ‖u‖ₑ ^ q) := by
    let f := fun x => (M : ℝ≥0∞) ^ q * ‖u (x + h) - u x‖ₑ ^ q
    let g := fun x => (D h : ℝ≥0∞) ^ q * ‖u x‖ₑ ^ q
    have huf : Measurable (fun x => ‖u (x + h) - u x‖ₑ ^ q) :=
      ((hu.comp (measurable_id.add_const h)).sub hu).enorm.pow_const _
    have hug : Measurable (fun x => ‖u x‖ₑ ^ q) := hu.enorm.pow_const _
    have hf : Measurable f := measurable_const.mul huf
    have hg : Measurable g := measurable_const.mul hug
    have hpoint : (fun x => ‖v (x + h) - v x‖ₑ ^ q) ≤ᵐ[volume] fun x => C * (f x + g x) := by
      have ht := (measurePreserving_add_right (volume : Measure (Fin d → ℝ)) h).quasiMeasurePreserving
      filter_upwards [hv, ht.ae_eq_comp hv] with x hx hxh
      change v (x + h) = a (x + h) * u (x + h) at hxh
      rw [hx, hxh, show a (x + h) * u (x + h) - a x * u x =
        a (x + h) * (u (x + h) - u x) + (a (x + h) - a x) * u x by ring]
      have ha : ‖a (x + h)‖ₑ ≤ (M : ℝ≥0∞) := by
        exact_mod_cast hM (x + h)
      have hd : ‖a (x + h) - a x‖ₑ ≤ (D h : ℝ≥0∞) := by
        exact_mod_cast multiplier_increment_le a M L hM hL x h
      calc
        _ ≤ (‖a (x + h) * (u (x + h) - u x)‖ₑ + ‖(a (x + h) - a x) * u x‖ₑ) ^ q :=
          ENNReal.rpow_le_rpow (enorm_add_le _ _) hq0
        _ ≤ ((M : ℝ≥0∞) * ‖u (x + h) - u x‖ₑ + (D h : ℝ≥0∞) * ‖u x‖ₑ) ^ q := by
          rw [enorm_mul, enorm_mul]
          exact ENNReal.rpow_le_rpow (add_le_add (mul_le_mul_of_nonneg_right ha bot_le)
            (mul_le_mul_of_nonneg_right hd bot_le)) hq0
        _ ≤ C * (f x + g x) := by
          simpa only [f, g, C, ENNReal.mul_rpow_of_nonneg _ _ hq0] using
            ENNReal.rpow_add_le_mul_rpow_add_rpow
              ((M : ℝ≥0∞) * ‖u (x + h) - u x‖ₑ) ((D h : ℝ≥0∞) * ‖u x‖ₑ) hq
    calc
      _ ≤ ∫⁻ x, C * (f x + g x) := lintegral_mono_ae hpoint
      _ = _ := by
        have hfg : Measurable (fun x => f x + g x) := hf.add hg
        rw [lintegral_const_mul C hfg, lintegral_add_left hf]
        dsimp only [f, g]
        rw [lintegral_const_mul _ huf, lintegral_const_mul _ hug, hpow]
  rw [difference_energy_weighted_integral s p hp v, difference_energy_weighted_integral s p hp u]
  have htrans : ∀ (z : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) (h : Fin d → ℝ),
      (∫⁻ x, ‖z (x + h) - z x‖ₑ ^ q) = ‖lpIncrement p h z‖ₑ ^ q := by
    intro z h
    rw [← lintegral_congr_ae ((lpIncrement_representative p z h).mono
      (fun x hx => congrArg (fun z : 𝕜 => ‖z‖ₑ ^ q) hx))]
    rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp
      (Lp.aestronglyMeasurable (lpIncrement p h z)), ← ENNReal.rpow_mul,
      one_div_mul_cancel (zero_lt_one.trans_le hq).ne', ENNReal.rpow_one]
  have hu' : Measurable (fun h => ‖lpIncrement p h u‖ₑ ^ q) :=
    (lpIncrement_continuous p hp u).enorm.measurable.pow_const q
  have hD : Measurable (fun h => (D h : ℝ≥0∞) ^ q) :=
    (multiplierIncrementBound_measurable (d := d) M L).coe_nnreal_ennreal.pow_const q
  have hDI :
      (∫⁻ h, (D h : ℝ≥0∞) ^ q ∂differenceMeasure s p) = multiplierIncrementIntegral d s p M L :=
    lintegral_withDensity_eq_lintegral_mul volume (differenceKernel_measurable s p) hD
  calc
    _ ≤ ∫⁻ h, C * ((M : ℝ≥0∞) ^ q * ‖lpIncrement p h u‖ₑ ^ q +
            ‖u‖ₑ ^ q * (D h : ℝ≥0∞) ^ q) ∂differenceMeasure s p := by
      apply lintegral_mono
      intro h
      simpa only [htrans, mul_comm ((D h : ℝ≥0∞) ^ q)] using hincrement h
    _ = _ := by
      have hf : Measurable (fun h => (M : ℝ≥0∞) ^ q * ‖lpIncrement p h u‖ₑ ^ q) :=
        measurable_const.mul hu'
      have hg : Measurable (fun h => ‖u‖ₑ ^ q * (D h : ℝ≥0∞) ^ q) := measurable_const.mul hD
      rw [lintegral_const_mul C (hf.add hg : Measurable (fun h => _ + _)),
        lintegral_add_left hf, lintegral_const_mul _ hu',
        lintegral_const_mul _ hD, hDI]


/-- Surface area of the Euclidean unit sphere for the polar decomposition of volume. -/
def unitSphereArea (d : ℕ) : ℝ :=
  (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere.real univ

private def multiplierRadialMajorant (d : ℕ) (s q : ℝ) (M L : ℝ≥0) (r : ℝ) : ℝ :=
  if r < 1 then (L : ℝ) ^ q * r ^ (-(d : ℝ) + (1 - s) * q)
  else (2 * (M : ℝ)) ^ q * r ^ (-(d : ℝ) - s * q)

private lemma multiplierRadial_integral (d : ℕ) (hd : 0 < d) (s q : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) (hq : 0 < q) (M L : ℝ≥0) :
    let F := multiplierRadialMajorant d s q M L
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => F ‖x‖) ∧
    (∫ x : EuclideanSpace ℝ (Fin d), F ‖x‖) =
      unitSphereArea d * ((L : ℝ) ^ q / (q * (1 - s)) + (2 * (M : ℝ)) ^ q / (s * q)) := by
  let F := multiplierRadialMajorant d s q M L
  let A := (1 - s) * q
  let B := s * q
  have hA : 0 < A := mul_pos (sub_pos.mpr hs1) hq
  have hB : 0 < B := mul_pos hs0 hq
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hd)
  let G := fun r : ℝ => r ^ (d - 1) * F r
  have hnear (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      G r = (L : ℝ) ^ q * r ^ (A - 1) := by
    dsimp [G, F, multiplierRadialMajorant]
    rw [ite_eq_left hr.2, mul_left_comm, ← Real.rpow_natCast r (d - 1), ← Real.rpow_add hr.1]
    congr 2
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    dsimp [A]
    ring
  have hfar (r : ℝ) (hr : r ∈ Ici (1 : ℝ)) :
      G r = (2 * (M : ℝ)) ^ q * r ^ (-B - 1) := by
    dsimp [G, F, multiplierRadialMajorant]
    rw [ite_eq_right (not_lt.mpr hr), mul_left_comm, ← Real.rpow_natCast r (d - 1),
      ← Real.rpow_add (zero_lt_one.trans_le hr)]
    congr 2
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    dsimp [B]
    ring
  have hi₁ : IntegrableOn G (Ioo 0 1) := by
    have h : IntegrableOn (fun r : ℝ => r ^ (A - 1)) (Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)
    exact (integrableOn_congr_fun hnear measurableSet_Ioo).mpr (h.const_mul _)
  have hi₂ : IntegrableOn G (Ici 1) := by
    have h : IntegrableOn (fun r : ℝ => r ^ (-B - 1)) (Ici 1) :=
      (integrableOn_Ici_iff_integrableOn_Ioi).mpr
        (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one)
    exact (integrableOn_congr_fun hfar measurableSet_Ici).mpr (h.const_mul _)
  have hsplit : Ioo (0 : ℝ) 1 ∪ Ici 1 = Ioi 0 := by
    ext r
    simp only [mem_union, mem_Ioo, mem_Ici, mem_Ioi]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases hr : r < 1
      · exact Or.inl ⟨h, hr⟩
      · exact Or.inr (le_of_not_gt hr)
  have hdisj : Disjoint (Ioo (0 : ℝ) 1) (Ici 1) := by
    rw [Set.disjoint_left]
    intro r hr ht
    exact (not_lt_of_ge ht) hr.2
  have hI₁ : (∫ r in Ioo (0 : ℝ) 1, G r) = (L : ℝ) ^ q / (q * (1 - s)) := by
    rw [setIntegral_congr_fun measurableSet_Ioo hnear, integral_const_mul,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith : -1 < A - 1))]
    rw [sub_add_cancel, Real.one_rpow, Real.zero_rpow hA.ne', sub_zero]
    dsimp [A]
    rw [mul_comm (1 - s) q, div_eq_mul_inv]
    simp [div_eq_mul_inv]
  have hI₂ : (∫ r in Ici (1 : ℝ), G r) = (2 * (M : ℝ)) ^ q / (s * q) := by
    rw [setIntegral_congr_fun measurableSet_Ici hfar, integral_const_mul,
      integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one,
      sub_add_cancel, Real.one_rpow]
    simp [B, div_eq_mul_inv]
  constructor
  · rw [integrable_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin d)))]
    simpa only [G, finrank_euclideanSpace_fin, smul_eq_mul, ← hsplit] using hi₁.union hi₂
  · rw [integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin d)))]
    rw [unitSphereArea, Measure.toSphere_real_apply_univ]
    simp only [finrank_euclideanSpace_fin, smul_eq_mul, nsmul_eq_mul]
    rw [← hsplit, setIntegral_union hdisj measurableSet_Ici hi₁ hi₂, hI₁, hI₂]
    ring

/-- The unit-ball split with the separate Lipschitz and supremum constants. -/
theorem fractional_multiplier_integral_le (d : ℕ) (hd : 0 < d) (s : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞) (M L : ℝ≥0) :
    multiplierIncrementIntegral d s p M L ≤ ENNReal.ofReal
      (unitSphereArea d * ((L : ℝ) ^ p.toReal / (p.toReal * (1 - s)) +
        (2 * (M : ℝ)) ^ p.toReal / (s * p.toReal))) := by
  let q := p.toReal
  have hq : 0 < q := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  let F := multiplierRadialMajorant d s q M L
  have hF (r : ℝ) (hr : 0 ≤ r) : 0 ≤ F r := by
    unfold F multiplierRadialMajorant
    split <;> exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hr _)
  obtain ⟨hint, hformula⟩ := multiplierRadial_integral d hd s q hs0 hs1 hq M L
  let e := PiLp.volume_preserving_toLp (Fin d)
  have hint' : Integrable (fun h : Fin d → ℝ => F (euclideanLength h)) :=
    e.integrable_comp_of_integrable hint
  have hnonneg : 0 ≤ᵐ[volume] fun h : Fin d → ℝ => F (euclideanLength h) :=
    Filter.Eventually.of_forall fun h => hF _ (norm_nonneg _)
  unfold multiplierIncrementIntegral
  calc
    _ ≤ ∫⁻ h : Fin d → ℝ, ENNReal.ofReal (F (euclideanLength h)) := by
      apply lintegral_mono
      intro h
      by_cases hh : h = 0
      · simp [hh]
      let r := euclideanLength h
      have hr : 0 < r := lt_of_le_of_ne (norm_nonneg _) (by
        intro hz
        exact hh ((euclideanLength_eq_zero h).mp hz.symm))
      have hD : (multiplierIncrementBound M L h : ℝ) = min ((L : ℝ) * r) (2 * (M : ℝ)) := by
        simp [multiplierIncrementBound, r, euclideanLength]
      have hkernel : differenceKernel s p h = ENNReal.ofReal (r ^ (-(d + s * q))) := by
        unfold differenceKernel
        rw [ite_eq_right hh, ENNReal.ofReal_rpow_of_pos hr]
      have hpower : (multiplierIncrementBound M L h : ℝ≥0∞) ^ q =
          ENNReal.ofReal ((multiplierIncrementBound M L h : ℝ) ^ q) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg (NNReal.coe_nonneg _) hq.le,
          ENNReal.ofReal_coe_nnreal]
      change differenceKernel s p h * (multiplierIncrementBound M L h : ℝ≥0∞) ^ q ≤ _
      rw [hkernel, hpower, ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _), hD]
      apply ENNReal.ofReal_le_ofReal
      change r ^ (-(d + s * q)) * min ((L : ℝ) * r) (2 * (M : ℝ)) ^ q ≤ F r
      unfold F multiplierRadialMajorant
      split
      · calc
          _ ≤ r ^ (-(d + s * q)) * ((L : ℝ) * r) ^ q :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (le_min (by positivity) (by positivity)) (min_le_left _ _) hq.le)
              (Real.rpow_nonneg hr.le _)
          _ = _ := by
            rw [Real.mul_rpow L.coe_nonneg hr.le, mul_left_comm, ← Real.rpow_add hr]
            congr 2
            ring
      · calc
          _ ≤ r ^ (-(d + s * q)) * (2 * (M : ℝ)) ^ q :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (le_min (by positivity) (by positivity)) (min_le_right _ _) hq.le)
              (Real.rpow_nonneg hr.le _)
          _ = _ := by rw [mul_comm]; congr 2; ring
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hint' hnonneg]
      congr 1
      rw [show (∫ h : Fin d → ℝ, F (euclideanLength h)) =
          ∫ x : EuclideanSpace ℝ (Fin d), F ‖x‖ from
        e.integral_comp ((PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurableEmbedding
          (fun _ _ h => congrArg WithLp.ofLp h)) (fun x => F ‖x‖)]
      exact hformula

/-- The multiplier error integral vanishes in dimension zero. -/
theorem fractional_multiplier_integral_zero_dimension (s : ℝ) (p : ℝ≥0∞) (M L : ℝ≥0) :
    multiplierIncrementIntegral 0 s p M L = 0 := by
  unfold multiplierIncrementIntegral
  have h (x : Fin 0 → ℝ) : x = 0 := Subsingleton.elim _ _
  calc
    _ = ∫⁻ _ : Fin 0 → ℝ, (0 : ℝ≥0∞) := by
      apply lintegral_congr
      intro x
      rw [h x, differenceKernel_zero, zero_mul]
    _ = 0 := lintegral_zero

end ExpandedFA.PartIV.FractionalSobolev
