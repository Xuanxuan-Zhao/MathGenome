import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.LocalizationMultiplier
import MathGenome.Internal.FourierSobolev.P102.Fractional.Space
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.NNRealPreprocessor
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology
namespace P102.Fractional.LocalizationMultiplier
open P102.Fractional
variable {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
variable {G : Set (Domain d)} {s : ℝ} {p : ℝ≥0∞}

/-- Reconstruct an element of the canonical graph directly from a raw Lp
representative of finite energy, with the exact sum norm. -/
theorem exists_space_representative [Fact (1 ≤ p)] (hpt : p ≠ ∞)
    {u : Domain d → 𝕜} (hu : MemLp u p (domainMeasure G))
    (he : energy G s p u < ∞) :
    ∃ v : Space 𝕜 G s p,
      (firstProjection v : Domain d → 𝕜) =ᵐ[domainMeasure G] u ∧
      ‖v‖ = (eLpNorm u p (domainMeasure G)).toReal + (seminorm G s p u).toReal := by
  have he' : energy G s p (hu.toLp u) < ∞ := by
    rw [energy_congr hu.coeFn_toLp]
    exact he
  obtain ⟨v, hv⟩ := (firstProjection_range hpt (hu.toLp u)).mpr he'
  refine ⟨v, ?_, ?_⟩
  · rw [hv]
    exact hu.coeFn_toLp
  · rw [space_norm hpt, hv, Lp.norm_toLp, seminorm_congr hu.coeFn_toLp]

/-- Assemble a bounded operator on the graph spaces from a linear operation
on representatives. All analytical obligations are explicit: a.e. compatibility,
Lp membership, finite energy, and the bound for the exact manuscript norm. -/
theorem exists_continuousLinearMap_of_representatives
    {e : ℕ} {J : Set (Domain e)} [Fact (1 ≤ p)] (hpt : p ≠ ∞)
    (A : (Domain d → 𝕜) →ₗ[𝕜] (Domain e → 𝕜))
    (hcongr : ∀ u v, u =ᵐ[domainMeasure G] v →
      A u =ᵐ[domainMeasure J] A v)
    (hmem : ∀ u : Space 𝕜 G s p,
      MemLp (A (firstProjection u)) p (domainMeasure J))
    (henergy : ∀ u : Space 𝕜 G s p,
      energy J s p (A (firstProjection u)) < ∞)
    (C : ℝ)
    (hbound : ∀ u : Space 𝕜 G s p,
      (eLpNorm (A (firstProjection u)) p (domainMeasure J)).toReal +
        (seminorm J s p (A (firstProjection u))).toReal ≤ C * ‖u‖) :
    ∃ T : Space 𝕜 G s p →L[𝕜] Space 𝕜 J s p,
      ∀ u, (firstProjection (T u) : Domain e → 𝕜) =ᵐ[domainMeasure J]
        A (firstProjection u) ∧ ‖T u‖ ≤ C * ‖u‖ := by
  classical
  choose f hf hnorm using fun u =>
    exists_space_representative hpt (hmem u) (henergy u)
  have hadd : ∀ u v, f (u + v) = f u + f v := by
    intro u v
    apply firstProjection_injective
    apply Lp.ext
    have hi : A (firstProjection (u + v)) =ᵐ[domainMeasure J]
        A ((firstProjection u : Domain d → 𝕜) + (firstProjection v : Domain d → 𝕜)) := by
      apply hcongr
      exact Lp.coeFn_add (firstProjection u) (firstProjection v)
    rw [A.map_add] at hi
    filter_upwards [hf (u + v), hi, hf u, hf v,
      Lp.coeFn_add (firstProjection (f u)) (firstProjection (f v))]
      with x hx hi hu hv hsum
    change firstProjection (f (u + v)) x =
      (firstProjection (f u) + firstProjection (f v)) x
    rw [hx, hi, Pi.add_apply, ← hu, ← hv, hsum]
    rfl
  have hsmul : ∀ (c : 𝕜) u, f (c • u) = c • f u := by
    intro c u
    apply firstProjection_injective
    apply Lp.ext
    have hi : A (firstProjection (c • u)) =ᵐ[domainMeasure J]
        A (c • (firstProjection u : Domain d → 𝕜)) := by
      apply hcongr
      exact Lp.coeFn_smul c (firstProjection u)
    rw [A.map_smul] at hi
    filter_upwards [hf (c • u), hi, hf u,
      Lp.coeFn_smul c (firstProjection (f u))] with x hx hi hu hmul
    change firstProjection (f (c • u)) x = (c • firstProjection (f u)) x
    rw [hx, hi, Pi.smul_apply, ← hu, hmul]
    rfl
  let B : Space 𝕜 G s p →ₗ[𝕜] Space 𝕜 J s p :=
    { toFun := f, map_add' := hadd, map_smul' := hsmul }
  have hB : ∀ u, ‖B u‖ ≤ C * ‖u‖ := by
    intro u
    change ‖f u‖ ≤ _
    rw [hnorm u]
    exact hbound u
  exact ⟨B.mkContinuous C hB, fun u => ⟨hf u, hB u⟩⟩

/-- The exact algebraic product increment used by the multiplier estimate. -/
theorem multiplier_increment (φ u : Domain d → 𝕜) (x y : Domain d) :
    φ x * u x - φ y * u y =
      φ y * (u x - u y) + (φ x - φ y) * u x := by
  ring


/-- A radial majorant with integrable near and far powers. -/
def radialMajorant (d : ℕ) (s q : ℝ) (x : Domain d) : ℝ :=
  if ‖x‖ < 1 then ‖x‖ ^ (- (d : ℝ) + (1 - s) * q)
  else ‖x‖ ^ (- (d : ℝ) - s * q)

theorem radialMajorant_nonneg (d : ℕ) (s q : ℝ) (x : Domain d) :
    0 ≤ radialMajorant d s q x := by
  unfold radialMajorant
  split_ifs <;> positivity

/-- The analytic integrability condition uses precisely 0<s<1 and q>0. -/
theorem integrable_radialMajorant (hd : 1 ≤ d) (hs : 0 < s) (hs1 : s < 1)
    {q : ℝ} (hq : 0 < q) : Integrable (radialMajorant d s q) := by
  have : Nontrivial (Domain d) := Module.nontrivial_of_finrank_pos
    (R := ℝ) (by simpa [Domain] using (Nat.zero_lt_of_lt hd))
  let f : ℝ → ℝ := fun r =>
    if r < 1 then r ^ (-(d : ℝ) + (1-s)*q) else r ^ (-(d : ℝ)-s*q)
  change Integrable (fun x : Domain d => f ‖x‖)
  rw [integrable_fun_norm_addHaar]
  have hdim : Module.finrank ℝ (Domain d) = d := by simp [Domain]
  rw [hdim]
  have hnear : IntegrableOn (fun r : ℝ => r ^ (d-1) • f r) (Ioo 0 1) := by
    have h : IntegrableOn (fun r : ℝ => r ^ ((1-s)*q-1)) (Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by nlinarith)
    apply h.congr_fun _ measurableSet_Ioo
    intro r hr
    dsimp [f]
    rw [ite_eq_left hr.2, ← Real.rpow_natCast,
      ← Real.rpow_add hr.1]
    congr 1
    have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by simpa using (Nat.cast_sub (R := ℝ) hd)
    rw [this]
    ring
  have hfar : IntegrableOn (fun r : ℝ => r ^ (d-1) • f r) (Ici 1) := by
    have h : IntegrableOn (fun r : ℝ => r ^ (-s*q-1)) (Ici 1) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact integrableOn_Ioi_rpow_of_lt (by nlinarith) zero_lt_one
    apply h.congr_fun _ measurableSet_Ici
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
    dsimp [f]
    rw [ite_eq_right (not_lt_of_ge hr), ← Real.rpow_natCast,
      ← Real.rpow_add hr0]
    congr 1
    have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by simpa using (Nat.cast_sub (R := ℝ) hd)
    rw [this]
    ring
  have heq : Ioo (0 : ℝ) 1 ∪ Ici 1 = Ioi 0 := by
    ext r
    simp only [mem_union, mem_Ioo, mem_Ici, mem_Ioi]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases hr : r < 1
      · exact Or.inl ⟨h, hr⟩
      · exact Or.inr (le_of_not_gt hr)
  rw [← heq]
  exact hnear.union hfar

theorem radialMajorant_measurable (d : ℕ) (s q : ℝ) :
    Measurable (radialMajorant d s q) := by
  unfold radialMajorant
  apply Measurable.ite (measurableSet_lt measurable_norm measurable_const) <;> fun_prop

def radialMass (d : ℕ) (s q : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : Domain d, ENNReal.ofReal (radialMajorant d s q x)

theorem radialMass_lt_top (hd : 1 ≤ d) (hs : 0 < s) (hs1 : s < 1)
    {q : ℝ} (hq : 0 < q) : radialMass d s q < ∞ :=
  (hasFiniteIntegral_iff_ofReal (ae_of_all _ (radialMajorant_nonneg d s q))).mp
    (integrable_radialMajorant hd hs hs1 hq).hasFiniteIntegral

theorem radial_row_le (x : Domain d) (s q : ℝ) (G : Set (Domain d)) :
    (∫⁻ y, ENNReal.ofReal (radialMajorant d s q (x-y)) ∂domainMeasure G) ≤
      radialMass d s q := by
  apply le_trans (lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl))
  exact (lintegral_sub_left_eq_self (μ := volume)
    (fun z : Domain d => ENNReal.ofReal (radialMajorant d s q z)) x).le

/-- The multiplier is measurable only on the domain, which suffices. -/
theorem multiplier_aestronglyMeasurable {L : ℝ≥0} {φ : Domain d → 𝕜}
    (hG : IsOpen G) (hφ : LipschitzOnWith L φ G) :
    AEStronglyMeasurable φ (domainMeasure G) :=
  hφ.continuousOn.aestronglyMeasurable hG.measurableSet

theorem eLpNorm_mul_le {M L : ℝ≥0} {φ u : Domain d → 𝕜}
    (hG : IsOpen G) (hφ : LipschitzOnWith L φ G)
    (hM : ∀ x ∈ G, ‖φ x‖ ≤ M) (hu : MemLp u p (domainMeasure G)) :
    eLpNorm (fun x => φ x * u x) p (domainMeasure G) ≤
      (M : ℝ≥0∞) * eLpNorm u p (domainMeasure G) := by
  have hbound : ∀ᵐ x ∂domainMeasure G, ‖φ x * u x‖ ≤ (M : ℝ) * ‖u x‖ := by
    filter_upwards [self_mem_ae_restrict hG.measurableSet] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg _)
  convert eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      ((multiplier_aestronglyMeasurable hG hφ).mul hu.aestronglyMeasurable) hbound p using 1
  simp

theorem memLp_mul {M L : ℝ≥0} {φ u : Domain d → 𝕜}
    (hG : IsOpen G) (hφ : LipschitzOnWith L φ G)
    (hM : ∀ x ∈ G, ‖φ x‖ ≤ M) (hu : MemLp u p (domainMeasure G)) :
    MemLp (fun x => φ x * u x) p (domainMeasure G) :=
  (eLpNorm_mul_le hG hφ hM hu).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hu)

/-- The difference quotient is dominated by one fixed integrable radial kernel.
No extension of the multiplier outside G is used. -/
theorem multiplier_difference_le {M L : ℝ≥0} {φ : Domain d → 𝕜}
    (hφ : LipschitzOnWith L φ G) (hM : ∀ x ∈ G, ‖φ x‖ ≤ M)
    {q : ℝ} (hq : 0 ≤ q) {x y : Domain d} (hx : x ∈ G) (hy : y ∈ G)
    (hxy : x ≠ y) :
    ‖φ x - φ y‖ₑ ^ q / ENNReal.ofReal ‖x-y‖ ^ ((d : ℝ) + s*q) ≤
      ((L + 2*M : ℝ≥0) : ℝ≥0∞) ^ q *
        ENNReal.ofReal (radialMajorant d s q (x-y)) := by
  let A : ℝ≥0∞ := ((L + 2*M : ℝ≥0) : ℝ≥0∞)
  let R := ENNReal.ofReal ‖x-y‖
  have hr : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hR0 : R ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hRt : R ≠ ∞ := ENNReal.ofReal_ne_top
  by_cases hnear : ‖x-y‖ < 1
  · have hdiff : ‖φ x-φ y‖ₑ ≤ A*R := by
      rw [← ofReal_norm]
      change ENNReal.ofReal ‖φ x-φ y‖ ≤ _
      have hbound : ‖φ x-φ y‖ ≤ ((L+2*M : ℝ≥0) : ℝ) * ‖x-y‖ := by
        calc
          _ ≤ (L : ℝ) * ‖x-y‖ := by
            simpa only [dist_eq_norm] using hφ.dist_le_mul x hx y hy
          _ ≤ _ := by gcongr; exact le_add_of_nonneg_right (by positivity)
      simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg (L+2*M)),
        ENNReal.ofReal_coe_nnreal, A, R] using ENNReal.ofReal_le_ofReal hbound
    calc
      _ ≤ (A*R)^q / R^((d : ℝ)+s*q) := by gcongr
      _ = A^q * R^(q-((d : ℝ)+s*q)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq, mul_div_assoc,
          ENNReal.rpow_sub _ _ hR0 hRt]
      _ = _ := by
        rw [radialMajorant, ite_eq_left hnear, ENNReal.ofReal_rpow_of_pos hr]
        congr 3
        ring
  · have hdiff : ‖φ x-φ y‖ₑ ≤ A := by
      rw [← ofReal_norm]
      have hbound : ‖φ x-φ y‖ ≤ ((L+2*M : ℝ≥0) : ℝ) := by
        calc
          _ ≤ ‖φ x‖ + ‖φ y‖ := norm_sub_le _ _
          _ ≤ (M : ℝ) + M := add_le_add (hM x hx) (hM y hy)
          _ ≤ _ := by simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat]; nlinarith [L.coe_nonneg]
      simpa only [ENNReal.ofReal_coe_nnreal, A] using ENNReal.ofReal_le_ofReal hbound
    calc
      _ ≤ A^q / R^((d : ℝ)+s*q) := by gcongr
      _ = A^q * R^(-((d : ℝ)+s*q)) := by rw [ENNReal.rpow_neg, div_eq_mul_inv]
      _ = _ := by
        rw [radialMajorant, ite_eq_right hnear, ENNReal.ofReal_rpow_of_pos hr]
        congr 3
        ring

def density (s : ℝ) (q : ℝ) (u : Domain d → 𝕜) (x y : Domain d) : ℝ≥0∞ :=
  if x = y then 0 else ‖u x-u y‖ₑ^q / ENNReal.ofReal ‖x-y‖^((d : ℝ)+s*q)

theorem density_mul_le {M L : ℝ≥0} {φ u : Domain d → 𝕜}
    (hφ : LipschitzOnWith L φ G) (hM : ∀ x ∈ G, ‖φ x‖ ≤ M)
    {q : ℝ} (hq : 0 ≤ q) {x y : Domain d} (hx : x ∈ G) (hy : y ∈ G) :
    density s q (fun x => φ x*u x) x y ≤
      (2 : ℝ≥0∞)^q * ((M : ℝ≥0∞)^q * density s q u x y +
        ((L+2*M : ℝ≥0) : ℝ≥0∞)^q * ‖u x‖ₑ^q *
          ENNReal.ofReal (radialMajorant d s q (x-y))) := by
  by_cases hxy : x = y
  · simp [density, hxy]
  have hpow : ‖φ x*u x-φ y*u y‖ₑ^q ≤ (2 : ℝ≥0∞)^q *
      (‖φ y‖ₑ^q * ‖u x-u y‖ₑ^q + ‖φ x-φ y‖ₑ^q * ‖u x‖ₑ^q) := by
    rw [multiplier_increment]
    apply le_trans (ENNReal.rpow_le_rpow (enorm_add_le _ _) hq)
    simpa only [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hq] using
      ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow
        ‖φ y*(u x-u y)‖ₑ ‖(φ x-φ y)*u x‖ₑ hq
  have hMy : ‖φ y‖ₑ ≤ (M : ℝ≥0∞) := by
    simpa only [ofReal_norm, ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal (hM y hy)
  rw [density, ite_eq_right hxy, density, ite_eq_right hxy]
  calc
    _ ≤ ((2 : ℝ≥0∞)^q *
      (‖φ y‖ₑ^q * ‖u x-u y‖ₑ^q + ‖φ x-φ y‖ₑ^q * ‖u x‖ₑ^q)) /
        ENNReal.ofReal ‖x-y‖^((d : ℝ)+s*q) := by gcongr
    _ = (2 : ℝ≥0∞)^q * (‖φ y‖ₑ^q *
        (‖u x-u y‖ₑ^q / ENNReal.ofReal ‖x-y‖^((d : ℝ)+s*q)) +
        (‖φ x-φ y‖ₑ^q / ENNReal.ofReal ‖x-y‖^((d : ℝ)+s*q))*‖u x‖ₑ^q) := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ _ := by
      gcongr 1
      apply add_le_add
      · gcongr 1
        exact ENNReal.rpow_le_rpow hMy hq
      · calc
          _ ≤ (((L+2*M : ℝ≥0) : ℝ≥0∞)^q *
              ENNReal.ofReal (radialMajorant d s q (x-y)))*‖u x‖ₑ^q := by
            gcongr 1
            exact multiplier_difference_le hφ hM hq hx hy hxy
          _ = _ := by ring

/-- Raw energy comparison, with explicit finite scalar coefficients. -/
theorem energy_mul_le {M L : ℝ≥0} {φ u : Domain d → 𝕜}
    (hG : IsOpen G) (hφ : LipschitzOnWith L φ G)
    (hM : ∀ x ∈ G, ‖φ x‖ ≤ M) (hu : MemLp u p (domainMeasure G)) :
    energy G s p (fun x => φ x*u x) ≤ (2 : ℝ≥0∞)^p.toReal *
      ((M : ℝ≥0∞)^p.toReal * energy G s p u +
        ((L+2*M : ℝ≥0) : ℝ≥0∞)^p.toReal * radialMass d s p.toReal *
          (∫⁻ x, ‖u x‖ₑ^p.toReal ∂domainMeasure G)) := by
  let q := p.toReal
  let B : ℝ≥0∞ := (2 : ℝ≥0∞)^q
  let D : ℝ≥0∞ := (M : ℝ≥0∞)^q
  let A : ℝ≥0∞ := ((L+2*M : ℝ≥0) : ℝ≥0∞)^q
  let I := radialMass d s q
  have hq : 0 ≤ q := ENNReal.toReal_nonneg
  have hBt : B ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hq (by norm_num)
  have hDt : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hq ENNReal.coe_ne_top
  have hrow (x : Domain d) (hx : x ∈ G) :
      (∫⁻ y, density s q (fun x => φ x*u x) x y ∂domainMeasure G) ≤
        B*(D*(∫⁻ y, density s q u x y ∂domainMeasure G)+ A*I*‖u x‖ₑ^q) := by
    have hK : Measurable (fun y : Domain d => ENNReal.ofReal (radialMajorant d s q (x-y))) :=
      (radialMajorant_measurable d s q).ennreal_ofReal.comp (measurable_const.sub measurable_id)
    calc
      _ ≤ ∫⁻ y, B*(D*density s q u x y + A*‖u x‖ₑ^q *
          ENNReal.ofReal (radialMajorant d s q (x-y))) ∂domainMeasure G := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict hG.measurableSet] with y hy
        exact density_mul_le hφ hM hq hx hy
      _ = B*(D*(∫⁻ y, density s q u x y ∂domainMeasure G)+
          A*‖u x‖ₑ^q * (∫⁻ y, ENNReal.ofReal (radialMajorant d s q (x-y)) ∂domainMeasure G)) := by
        rw [lintegral_const_mul' _ _ hBt, lintegral_add_right _ (hK.const_mul _),
          lintegral_const_mul' _ _ hDt, lintegral_const_mul _ hK]
      _ ≤ _ := by
        rw [mul_assoc A, mul_comm (‖u x‖ₑ^q), ← mul_assoc]
        gcongr
        exact radial_row_le x s q G
  change (∫⁻ x, ∫⁻ y, density s q (fun x => φ x*u x) x y
    ∂domainMeasure G ∂domainMeasure G) ≤ _
  calc
    _ ≤ ∫⁻ x, B*(D*(∫⁻ y, density s q u x y ∂domainMeasure G) + A*I*‖u x‖ₑ^q)
        ∂domainMeasure G := by
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict hG.measurableSet] with x hx
      exact hrow x hx
    _ = _ := by
      rw [lintegral_const_mul' _ _ hBt,
        lintegral_add_right' _ ((hu.aestronglyMeasurable.enorm.pow_const q).const_mul (A*I)),
        lintegral_const_mul' _ _ hDt,
        lintegral_const_mul'' _ (hu.aestronglyMeasurable.enorm.pow_const q)]
      rfl

/-- An integral comparison yields a useful, deliberately coarse, root bound
uniformly for p ≥ 1. -/
theorem root_le_mul_root [Fact (1 ≤ p)] (hpt : p ≠ ∞)
    {a b C : ℝ≥0∞} (hC : 1 ≤ C) (hab : a ≤ C * b) :
    a ^ (1 / p.toReal) ≤ C * b ^ (1 / p.toReal) := by
  have hp : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hpt (Fact.out : 1 ≤ p)
  have hq : (1 : ℝ) / p.toReal ≤ 1 :=
    (div_le_iff₀ (by linarith : 0 < p.toReal)).mpr (by simpa using hp)
  calc
    _ ≤ (C * b) ^ (1 / p.toReal) := ENNReal.rpow_le_rpow hab (by positivity)
    _ = C ^ (1 / p.toReal) * b ^ (1 / p.toReal) := ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ ≤ C * b ^ (1 / p.toReal) := by
      gcongr
      simpa only [ENNReal.rpow_one] using
        ENNReal.rpow_le_rpow_of_exponent_le hC hq

/-- A coarse subadditivity estimate, sufficient for the exact sum norm. -/
theorem root_sum_le [Fact (1 ≤ p)] (hpt : p ≠ ∞)
    {a b c C : ℝ≥0∞} (hC : 1 ≤ C) (h : a ≤ C*(b+c)) :
    a^(1/p.toReal) ≤ (2*C)*(b^(1/p.toReal)+c^(1/p.toReal)) := by
  have hp : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hpt (Fact.out : 1 ≤ p)
  have hr : (1 : ℝ)/p.toReal ≤ 1 :=
    (div_le_iff₀ (by linarith : 0 < p.toReal)).mpr (by simpa using hp)
  calc
    _ ≤ C*(b+c)^(1/p.toReal) := root_le_mul_root hpt hC h
    _ ≤ C*((2 : ℝ≥0∞)^(1/p.toReal)*(b^(1/p.toReal)+c^(1/p.toReal))) := by
      gcongr
      exact ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow b c (by positivity)
    _ ≤ C*((2 : ℝ≥0∞)*(b^(1/p.toReal)+c^(1/p.toReal))) := by
      gcongr
      simpa only [ENNReal.rpow_one] using
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2) hr
    _ = _ := by ring

/-- Pointwise scalar multiplication is scalar-linear, for real and complex fields. -/
def multiplierLinear (φ : Domain d → 𝕜) :
    (Domain d → 𝕜) →ₗ[𝕜] (Domain d → 𝕜) where
  toFun u x := φ x*u x
  map_add' u v := by ext x; simp [mul_add]
  map_smul' c u := by ext x; simp [mul_left_comm]

theorem multiplier_congr (φ : Domain d → 𝕜) {u v : Domain d → 𝕜}
    (h : u =ᵐ[domainMeasure G] v) :
    (fun x => φ x*u x) =ᵐ[domainMeasure G] (fun x => φ x*v x) := by
  filter_upwards [h] with x hx
  rw [hx]

/-- The full uniform bounded Lipschitz scalar multiplier theorem. The witness
is chosen before the field, open domain, multiplier, and Lp representative. -/
theorem bounded_lipschitz_multiplier :
    Specs.P102.Fractional.LocalizationMultiplier.boundedMultiplier := by
  intro d hd s hs hs1 p _ hpt M L
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  let I := radialMass d s p.toReal
  let K : ℝ≥0∞ := (2 : ℝ≥0∞)^p.toReal *
    ((M : ℝ≥0∞)^p.toReal + ((L+2*M : ℝ≥0) : ℝ≥0∞)^p.toReal * I)
  have hI : I < ∞ := radialMass_lt_top hd hs hs1 hp
  have hK : K ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg hp.le (by norm_num)
    · apply ENNReal.add_ne_top.mpr
      constructor
      · exact ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.coe_ne_top
      · exact ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.coe_ne_top) hI.ne
  let C₀ : ℝ≥0 := K.toNNReal+1
  have hKC : K ≤ (C₀ : ℝ≥0∞) := by
    rw [show (C₀ : ℝ≥0∞) = K+1 by simp [C₀, ENNReal.coe_toNNReal hK]]
    exact le_self_add
  have hC₀ : (1 : ℝ≥0∞) ≤ C₀ := by
    change (1 : ℝ≥0∞) ≤ ↑(K.toNNReal+1)
    simp only [ENNReal.coe_add, ENNReal.coe_one]
    exact le_add_self
  let C : ℝ≥0 := M+2*C₀
  have hC₀C : (C₀ : ℝ≥0∞) ≤ C := by
    exact_mod_cast (show C₀ ≤ M+2*C₀ by nlinarith [C₀.coe_nonneg, M.coe_nonneg])
  refine ⟨C, ?_⟩
  intro 𝕜 _ G hG φ hφ hM
  have henergy : ∀ u : Domain d → 𝕜, MemLp u p (domainMeasure G) →
      energy G s p (fun x => φ x*u x) ≤ (C₀ : ℝ≥0∞) *
        (energy G s p u + ∫⁻ x, ‖u x‖ₑ^p.toReal ∂domainMeasure G) := by
    intro u hu
    calc
      _ ≤ (2 : ℝ≥0∞)^p.toReal *
        ((M : ℝ≥0∞)^p.toReal * energy G s p u +
          ((L+2*M : ℝ≥0) : ℝ≥0∞)^p.toReal * I *
            (∫⁻ x, ‖u x‖ₑ^p.toReal ∂domainMeasure G)) := energy_mul_le hG hφ hM hu
      _ ≤ K*(energy G s p u + ∫⁻ x, ‖u x‖ₑ^p.toReal ∂domainMeasure G) := by
        have halg (a b e m : ℝ≥0∞) : a*e+b*m ≤ (a+b)*(e+m) := by
          calc
            _ ≤ (a+b)*e+(a+b)*m := by
              gcongr <;> [exact le_self_add; exact le_add_self]
            _ = _ := by ring
        dsimp only [K]
        rw [mul_assoc ((2 : ℝ≥0∞)^p.toReal)]
        gcongr 1
        exact halg _ _ _ _
      _ ≤ _ := by gcongr
  refine ⟨fun u hu => (henergy u hu).trans (by gcongr), ?_⟩
  have hmass (u : Domain d → 𝕜) (hu : MemLp u p (domainMeasure G)) :
      (∫⁻ x, ‖u x‖ₑ^p.toReal ∂domainMeasure G) < ∞ :=
    (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt hu.aestronglyMeasurable).mp hu
  have hfinite (u : Space 𝕜 G s p) :
      energy G s p (fun x => φ x*firstProjection u x) < ∞ := by
    apply (henergy (firstProjection u) (Lp.memLp _)).trans_lt
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top
      (ENNReal.add_lt_top.mpr ⟨(firstProjection_range hpt _).mp ⟨u, rfl⟩,
        hmass _ (Lp.memLp _)⟩)
  apply exists_continuousLinearMap_of_representatives hpt (multiplierLinear φ)
    (fun _ _ h => multiplier_congr φ h)
    (fun u => memLp_mul hG hφ hM (Lp.memLp _)) hfinite C
  intro u
  have hlu := Lp.memLp (firstProjection u)
  have he : energy G s p (firstProjection u) < ∞ :=
    (firstProjection_range hpt _).mp ⟨u, rfl⟩
  have hse : seminorm G s p (firstProjection u) < ∞ :=
    ENNReal.rpow_lt_top_of_nonneg (by positivity) he.ne
  have hLp := eLpNorm_mul_le hG hφ hM hlu
  have hsem : seminorm G s p (fun x => φ x*firstProjection u x) ≤
      (2*(C₀ : ℝ≥0∞)) * (seminorm G s p (firstProjection u) +
        eLpNorm (firstProjection u) p (domainMeasure G)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hlu.aestronglyMeasurable]
    exact root_sum_le hpt hC₀ (henergy _ hlu)
  have hLp' := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hlu.ne) hLp
  have hsem' := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by finiteness)
      (ENNReal.add_ne_top.mpr ⟨hse.ne, hlu.ne⟩)) hsem
  simp only [ENNReal.toReal_mul, ENNReal.toReal_add hse.ne hlu.ne,
    ENNReal.coe_toReal, ENNReal.toReal_ofNat] at hLp' hsem'
  rw [space_norm hpt, Lp.norm_def]
  change (eLpNorm (fun x => φ x*firstProjection u x) p (domainMeasure G)).toReal +
    (seminorm G s p (fun x => φ x*firstProjection u x)).toReal ≤ _
  dsimp only [C]
  push_cast
  nlinarith [ENNReal.toReal_nonneg (a := seminorm G s p (firstProjection u))]

end P102.Fractional.LocalizationMultiplier
