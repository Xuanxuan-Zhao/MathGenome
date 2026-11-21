import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.LocalizationZero
import MathGenome.Internal.FourierSobolev.P102.Fractional.Space
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace P102.Fractional.ZeroExtension
variable {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
variable {G H : Set (Domain d)} {s : ℝ} {p : ℝ≥0∞}

/-- Zero extension respects the source a.e. class, on every larger domain. -/
theorem indicator_congr (hG : MeasurableSet G) {u v : Domain d → 𝕜}
    (huv : u =ᵐ[domainMeasure G] v) :
    G.indicator u =ᵐ[domainMeasure H] G.indicator v := by
  apply ae_restrict_of_ae
  have huv' := (ae_restrict_iff' hG).mp huv
  filter_upwards [huv'] with x hx
  by_cases hxG : x ∈ G
  · simp [hxG, hx hxG]
  · simp [hxG]

/-- Zero extension preserves the raw Lp integral exactly. -/
theorem mass_indicator (hG : MeasurableSet G) (hGH : G ⊆ H)
    (hp : 0 < p.toReal) (u : Domain d → 𝕜) :
    (∫⁻ x, ‖G.indicator u x‖ₑ ^ p.toReal ∂domainMeasure H) =
      ∫⁻ x, ‖u x‖ₑ ^ p.toReal ∂domainMeasure G := by
  classical
  have hfun : (fun x => ‖G.indicator u x‖ₑ ^ p.toReal) =
      G.indicator (fun x => ‖u x‖ₑ ^ p.toReal) := by
    funext x
    by_cases hx : x ∈ G <;> simp [hx, ENNReal.zero_rpow_of_pos hp]
  rw [hfun, lintegral_indicator hG]
  simp only [domainMeasure, Measure.restrict_restrict hG,
    Set.inter_eq_left.mpr hGH]

/-- Reconstruct the canonical graph element, retaining the exact sum norm. -/
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

/-- Exact radial tail in Euclidean space. This supplies a uniform constant,
independent of the domain and of the center of the tail. -/
theorem radial_tail (hd : 1 ≤ d) {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫⁻ z : Domain d in {z | r < ‖z‖},
      (ENNReal.ofReal ‖z‖ ^ ((d : ℝ) + a))⁻¹) =
      ENNReal.ofReal ((d : ℝ) * volume.real (Metric.ball (0 : Domain d) 1) / a) *
        ENNReal.ofReal (r ^ (-a)) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let f : ℝ → ℝ := (Ioi r).indicator (fun t => t ^ (-(d : ℝ) - a))
  have hf_nonneg (t : ℝ) : 0 ≤ f t := by
    dsimp [f]
    by_cases ht : t ∈ Ioi r
    · simp only [indicator_of_mem ht]
      exact Real.rpow_nonneg (hr.trans ht).le _
    · simp [ht]
  have hrad : (fun t : ℝ => t ^ (Module.finrank ℝ (Domain d) - 1) • f t) =
      (Ioi r).indicator (fun t => t ^ (-a - 1)) := by
    funext t
    by_cases ht : t ∈ Ioi r
    · have ht0 : 0 < t := hr.trans ht
      simp only [f, indicator_of_mem ht, smul_eq_mul,
        finrank_euclideanSpace, Fintype.card_fin]
      rw [← Real.rpow_natCast, ← Real.rpow_add ht0]
      congr 1
      rw [Nat.cast_sub hd]
      push_cast
      ring
    · simp [f, ht]
  have h1 : Integrable ((Ioi r).indicator (fun t : ℝ => t ^ (-a - 1))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr
      (integrableOn_Ioi_rpow_of_lt (by linarith) hr)
  have hfi : Integrable (fun z : Domain d => f ‖z‖) volume := by
    rw [integrable_fun_norm_addHaar volume, hrad]
    exact h1.integrableOn
  have hscalar : (∫ t : ℝ in Ioi 0, t ^ (Module.finrank ℝ (Domain d) - 1) • f t) =
      r ^ (-a) / a := by
    rw [hrad, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.mpr (Ioi_subset_Ioi hr.le), integral_Ioi_rpow_of_lt (by linarith) hr]
    rw [show -a - 1 + 1 = -a by ring, neg_div_neg_eq]
  have hreal : (∫ z : Domain d, f ‖z‖) =
      ((d : ℝ) * volume.real (Metric.ball (0 : Domain d) 1) / a) * r ^ (-a) := by
    rw [integral_fun_norm_addHaar volume f, hscalar]
    simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, nsmul_eq_mul]
    ring
  have htail : (∫⁻ z : Domain d in {z | r < ‖z‖},
      (ENNReal.ofReal ‖z‖ ^ ((d : ℝ) + a))⁻¹) =
      ∫⁻ z : Domain d, ENNReal.ofReal (f ‖z‖) := by
    rw [← lintegral_indicator (by measurability : MeasurableSet {z : Domain d | r < ‖z‖})]
    apply lintegral_congr
    intro z
    by_cases hz : r < ‖z‖
    · simp only [mem_ofPred_eq, hz, indicator_of_mem, f, mem_Ioi]
      rw [show -(d : ℝ) - a = -((d : ℝ) + a) by ring,
        Real.rpow_neg (norm_nonneg z),
        ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos (lt_trans hr hz) _),
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg z) (by positivity)]
    · simp [hz, f]
  rw [htail, ← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ fun z => hf_nonneg ‖z‖),
    hreal, ENNReal.ofReal_mul (by positivity)]

/-- An intentionally nonoptimal finite geometric constant. Using δ/2 avoids
any dependence on whether the separating sphere is included. -/
def tailConstant (d : ℕ) (a : ℝ) : ℝ :=
  ((d : ℝ) * volume.real (Metric.ball (0 : Domain d) 1) / a) * (2 : ℝ) ^ a

theorem tailConstant_nonneg {a : ℝ} (ha : 0 < a) : 0 ≤ tailConstant d a := by
  unfold tailConstant
  positivity

/-- Every row of the cross kernel is controlled by the whole Euclidean tail. -/
theorem separated_row_bound (hd : 1 ≤ d) {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (x : Domain d) (D : Set (Domain d))
    (hsep : ∀ y ∈ D, δ ≤ dist x y) :
    (∫⁻ y in D, (ENNReal.ofReal ‖x - y‖ ^ ((d : ℝ) + a))⁻¹) ≤
      ENNReal.ofReal (tailConstant d a) * ENNReal.ofReal (δ ^ (-a)) := by
  have hr : 0 < δ / 2 := by positivity
  have ht : (∫⁻ y in {y : Domain d | δ / 2 < ‖x - y‖},
      (ENNReal.ofReal ‖x - y‖ ^ ((d : ℝ) + a))⁻¹) =
      ∫⁻ z : Domain d in {z | δ / 2 < ‖z‖},
        (ENNReal.ofReal ‖z‖ ^ ((d : ℝ) + a))⁻¹ := by
    rw [← lintegral_indicator (by measurability :
      MeasurableSet {y : Domain d | δ / 2 < ‖x - y‖}),
      ← lintegral_indicator (by measurability :
        MeasurableSet {z : Domain d | δ / 2 < ‖z‖})]
    simpa only [Set.indicator, mem_ofPred_eq] using
      (lintegral_sub_left_eq_self (μ := volume)
        (fun z : Domain d => if δ / 2 < ‖z‖ then
          (ENNReal.ofReal ‖z‖ ^ ((d : ℝ) + a))⁻¹ else 0) x)
  calc
    _ ≤ ∫⁻ y in {y : Domain d | δ / 2 < ‖x - y‖},
        (ENNReal.ofReal ‖x - y‖ ^ ((d : ℝ) + a))⁻¹ := by
      apply lintegral_mono_set
      intro y hy
      dsimp
      rw [← dist_eq_norm]
      linarith [hsep y hy]
    _ = _ := by
      rw [ht, radial_tail hd ha hr]
      rw [Real.div_rpow hδ.le (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul,
        ENNReal.ofReal_mul (by positivity)]
      unfold tailConstant
      rw [ENNReal.ofReal_mul (by positivity)]
      ac_rfl

/-- The diagonal-zero density in the original definition. -/
def density (s : ℝ) (p : ℝ≥0∞) (u : Domain d → 𝕜) (x y : Domain d) : ℝ≥0∞ :=
  if x = y then 0 else
    ‖u x - u y‖ₑ ^ p.toReal / ENNReal.ofReal ‖x - y‖ ^ ((d : ℝ) + s * p.toReal)

theorem density_symm (u : Domain d → 𝕜) (x y : Domain d) :
    density s p u x y = density s p u y x := by
  simp only [density]
  by_cases h : x = y
  · simp [h]
  · simp [h, Ne.symm h, enorm_sub_rev, norm_sub_rev]

theorem density_aemeasurable {u : Domain d → 𝕜}
    (hu : AEStronglyMeasurable u (domainMeasure H)) :
    AEMeasurable (fun z : Domain d × Domain d => density s p u z.1 z.2)
      ((domainMeasure H).prod (domainMeasure H)) := by
  have hi := increment_aestronglyMeasurable_prod hu
  have he := hi.enorm.pow_const p.toReal
  unfold increment at he
  have hf : (fun z : Domain d × Domain d => density s p u z.1 z.2) =
      fun z => kernel d s p z * ‖u z.1 - u z.2‖ₑ ^ p.toReal := by
    funext z
    by_cases hz : z.1 = z.2 <;> simp [density, kernel, hz, div_eq_mul_inv, mul_comm]
  rw [hf]
  exact kernel_measurable.aemeasurable.mul he

/-- Partition the larger domain into the original domain and its artificial edge. -/
theorem domainMeasure_split (hG : MeasurableSet G) (hGH : G ⊆ H) :
    domainMeasure H = domainMeasure G + domainMeasure (H \ G) := by
  unfold domainMeasure
  rw [← Measure.restrict_union' disjoint_sdiff_right hG, union_sdiff_cancel hGH]

/-- The cross integral with its mass always evaluated on the original side. -/
def crossIntegral (G D : Set (Domain d)) (s : ℝ) (p : ℝ≥0∞)
    (u : Domain d → 𝕜) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, ‖u x‖ₑ ^ p.toReal /
    ENNReal.ofReal ‖x - y‖ ^ ((d : ℝ) + s * p.toReal)
      ∂domainMeasure D ∂domainMeasure G

/-- Exact four-region decomposition. Symmetry gives two copies of the cross term;
there is no loss in the coefficient of the old energy. -/
theorem energy_indicator_split (hG : MeasurableSet G) (hH : MeasurableSet H)
    (hGH : G ⊆ H) (hp : 0 < p.toReal) {u : Domain d → 𝕜}
    (hu : AEStronglyMeasurable u (domainMeasure G)) :
    energy H s p (G.indicator u) = energy G s p u +
      2 * crossIntegral G (H \ G) s p u := by
  classical
  let D := H \ G
  let v := G.indicator u
  have hD : MeasurableSet D := hH.diff hG
  have hv : AEStronglyMeasurable v (domainMeasure H) := by
    have hv' : AEStronglyMeasurable v volume :=
      (aestronglyMeasurable_indicator_iff hG).mpr hu
    exact hv'.mono_measure Measure.restrict_le_self
  have hGG : (domainMeasure G).prod (domainMeasure G) ≤
      (domainMeasure H).prod (domainMeasure H) :=
    Measure.prod_mono (Measure.restrict_mono hGH le_rfl) (Measure.restrict_mono hGH le_rfl)
  have hGD : (domainMeasure G).prod (domainMeasure D) ≤
      (domainMeasure H).prod (domainMeasure H) :=
    Measure.prod_mono (Measure.restrict_mono hGH le_rfl)
      (Measure.restrict_mono sdiff_subset le_rfl)
  have hDG : (domainMeasure D).prod (domainMeasure G) ≤
      (domainMeasure H).prod (domainMeasure H) :=
    Measure.prod_mono (Measure.restrict_mono sdiff_subset le_rfl)
      (Measure.restrict_mono hGH le_rfl)
  have hDD : (domainMeasure D).prod (domainMeasure D) ≤
      (domainMeasure H).prod (domainMeasure H) :=
    Measure.prod_mono (Measure.restrict_mono sdiff_subset le_rfl)
      (Measure.restrict_mono sdiff_subset le_rfl)
  have hf := density_aemeasurable (s := s) (p := p) hv
  have heGG : (∫⁻ x, ∫⁻ y, density s p v x y ∂domainMeasure G ∂domainMeasure G) =
      energy G s p u := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hG] with x hx
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hG] with y hy
    simp [density, v, hx, hy]
  have heDD : (∫⁻ x, ∫⁻ y, density s p v x y ∂domainMeasure D ∂domainMeasure D) = 0 := by
    trans ∫⁻ x, (0 : ℝ≥0∞) ∂domainMeasure D
    · apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hD] with x hx
      trans ∫⁻ y, (0 : ℝ≥0∞) ∂domainMeasure D
      · apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem hD] with y hy
        simp [density, v, hx.2, hy.2, ENNReal.zero_rpow_of_pos hp]
      · simp
    · simp
  have heGD : (∫⁻ x, ∫⁻ y, density s p v x y ∂domainMeasure D ∂domainMeasure G) =
      crossIntegral G D s p u := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hG] with x hx
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hD] with y hy
    have hxy : x ≠ y := fun heq => hy.2 (heq ▸ hx)
    simp [density, v, hx, hy.2, hxy]
  have heDG : (∫⁻ x, ∫⁻ y, density s p v x y ∂domainMeasure G ∂domainMeasure D) =
      crossIntegral G D s p u := by
    rw [lintegral_lintegral_swap (hf.mono_measure hDG)]
    simp_rw [density_symm (s := s) (p := p) v]
    exact heGD
  change (∫⁻ x, ∫⁻ y, density s p v x y ∂domainMeasure H ∂domainMeasure H) = _
  rw [← lintegral_prod _ hf, domainMeasure_split hG hGH, Measure.prod_add,
    Measure.add_prod, Measure.add_prod]
  simp only [lintegral_add_measure]
  rw [lintegral_prod _ (hf.mono_measure hGG), lintegral_prod _ (hf.mono_measure hDG),
    lintegral_prod _ (hf.mono_measure hGD), lintegral_prod _ (hf.mono_measure hDD),
    heGG, heGD, heDG, heDD]
  change _ = energy G s p u + 2 * crossIntegral G D s p u
  ring

/-- Integrate the separated rows against the original Lp mass. -/
theorem crossIntegral_bound (hd : 1 ≤ d) (hs : 0 < s) (hp : 0 < p.toReal)
    {δ : ℝ} (hδ : 0 < δ) {u : Domain d → 𝕜}
    (hsep : ∀ᵐ x ∂domainMeasure G, u x ≠ 0 → ∀ y ∈ H \ G, δ ≤ dist x y) :
    crossIntegral G (H \ G) s p u ≤
      ENNReal.ofReal (tailConstant d (s * p.toReal)) * ENNReal.ofReal (δ ^ (-s * p.toReal)) *
        (∫⁻ x, ‖u x‖ₑ ^ p.toReal ∂domainMeasure G) := by
  have ha : 0 < s * p.toReal := mul_pos hs hp
  let B := ENNReal.ofReal (tailConstant d (s * p.toReal)) *
    ENNReal.ofReal (δ ^ (-s * p.toReal))
  have hB : B ≠ ∞ := by dsimp [B]; finiteness
  calc
    _ ≤ ∫⁻ x, B * ‖u x‖ₑ ^ p.toReal ∂domainMeasure G := by
      apply lintegral_mono_ae
      filter_upwards [hsep] with x hx
      by_cases hux : u x = 0
      · simp [hux, ENNReal.zero_rpow_of_pos hp]
      · simp_rw [div_eq_mul_inv]
        rw [lintegral_const_mul' _ _ (by finiteness)]
        rw [mul_comm B]
        gcongr
        simpa [B, neg_mul, domainMeasure] using
          separated_row_bound hd ha hδ x (H \ G) (hx hux)
    _ = _ := lintegral_const_mul' B _ hB

/-- Quantitative comparison of the original diagonal-zero double integrals. -/
theorem energy_indicator_bound (hd : 1 ≤ d) (hs : 0 < s) (hp : 0 < p.toReal)
    (hG : MeasurableSet G) (hH : MeasurableSet H) (hGH : G ⊆ H)
    {δ : ℝ} (hδ : 0 < δ) {u : Domain d → 𝕜}
    (hu : AEStronglyMeasurable u (domainMeasure G))
    (hsep : ∀ᵐ x ∂domainMeasure G, u x ≠ 0 → ∀ y ∈ H \ G, δ ≤ dist x y) :
    energy H s p (G.indicator u) ≤ energy G s p u +
      ENNReal.ofReal (2 * tailConstant d (s * p.toReal)) *
        ENNReal.ofReal (δ ^ (-s * p.toReal)) *
          (∫⁻ x, ‖u x‖ₑ ^ p.toReal ∂domainMeasure G) := by
  rw [energy_indicator_split hG hH hGH hp hu]
  have hc := crossIntegral_bound hd hs hp hδ hsep
  calc
    _ ≤ energy G s p u + 2 *
        (ENNReal.ofReal (tailConstant d (s * p.toReal)) *
          ENNReal.ofReal (δ ^ (-s * p.toReal)) *
            (∫⁻ x, ‖u x‖ₑ ^ p.toReal ∂domainMeasure G)) := by gcongr
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num; ring

/-- The ordinary Lp norm is unchanged, also for empty or unbounded domains. -/
theorem eLpNorm_indicator (hG : MeasurableSet G) (hGH : G ⊆ H)
    (u : Domain d → 𝕜) :
    eLpNorm (G.indicator u) p (domainMeasure H) = eLpNorm u p (domainMeasure G) := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hG.nullMeasurableSet]
  simp only [domainMeasure, Measure.restrict_restrict hG, inter_eq_left.mpr hGH]

/-- Taking a root of order at least one costs at most one plus the coefficient. -/
theorem root_le_one_add (A : ℝ≥0∞) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    A ^ q ≤ 1 + A := by
  by_cases hA : A ≤ 1
  · calc
      _ ≤ (1 : ℝ≥0∞) ^ q := ENNReal.rpow_le_rpow hA hq0
      _ ≤ 1 + A := by simp
  · calc
      _ ≤ A ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le (le_of_not_ge hA) hq1
      _ ≤ 1 + A := by simp

/-- The energy comparison implies existence and the stated bound for the exact
Gagliardo sum norm. This lemma assumes only the proved raw comparison. -/
theorem exists_extension_of_energy_bound [Fact (1 ≤ p)] (hpt : p ≠ ∞)
    (hG : MeasurableSet G) (hGH : G ⊆ H) (A : ℝ≥0∞) (hA : A ≠ ∞)
    (u : Space 𝕜 G s p)
    (henergy : energy H s p (G.indicator (firstProjection u)) ≤
      energy G s p (firstProjection u) +
        A * (∫⁻ x, ‖firstProjection u x‖ₑ ^ p.toReal ∂domainMeasure G)) :
    ∃ v : Space 𝕜 H s p,
      (firstProjection v : Domain d → 𝕜) =ᵐ[domainMeasure H] G.indicator (firstProjection u) ∧
      ‖v‖ ≤ (2 + A.toReal) * ‖u‖ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hp1 : (1 : ℝ) ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hpt (Fact.out : 1 ≤ p)
  have hq0 : 0 ≤ 1 / p.toReal := by positivity
  have hq1 : (1 : ℝ) / p.toReal ≤ 1 := (div_le_iff₀ hp).mpr (by simpa using hp1)
  have hu := Lp.memLp (firstProjection u)
  have hmass : (∫⁻ x, ‖firstProjection u x‖ₑ ^ p.toReal ∂domainMeasure G) < ∞ :=
    (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt hu.aestronglyMeasurable).mp
      hu.eLpNorm_lt_top
  have he : energy G s p (firstProjection u) < ∞ :=
    (firstProjection_range hpt (firstProjection u)).mp ⟨u, rfl⟩
  have heH : energy H s p (G.indicator (firstProjection u)) < ∞ :=
    henergy.trans_lt (ENNReal.add_lt_top.mpr ⟨he,
      ENNReal.mul_lt_top hA.lt_top hmass⟩)
  have hLp : eLpNorm (G.indicator (firstProjection u)) p (domainMeasure H) =
      eLpNorm (firstProjection u) p (domainMeasure G) := eLpNorm_indicator hG hGH _
  have huH : MemLp (G.indicator (firstProjection u)) p (domainMeasure H) := by
    show eLpNorm _ _ _ < ∞
    rw [hLp]
    exact hu.eLpNorm_lt_top
  obtain ⟨v, hv, hnorm⟩ := exists_space_representative hpt huH heH
  refine ⟨v, hv, ?_⟩
  have hsem : seminorm H s p (G.indicator (firstProjection u)) ≤
      seminorm G s p (firstProjection u) +
        (1 + A) * eLpNorm (firstProjection u) p (domainMeasure G) := by
    unfold seminorm
    calc
      _ ≤ (energy G s p (firstProjection u) +
          A * (∫⁻ x, ‖firstProjection u x‖ₑ ^ p.toReal ∂domainMeasure G)) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow henergy hq0
      _ ≤ energy G s p (firstProjection u) ^ (1 / p.toReal) +
          (A * (∫⁻ x, ‖firstProjection u x‖ₑ ^ p.toReal ∂domainMeasure G)) ^ (1 / p.toReal) :=
        ENNReal.rpow_add_le_add_rpow _ _ hq0 hq1
      _ = energy G s p (firstProjection u) ^ (1 / p.toReal) +
          A ^ (1 / p.toReal) * eLpNorm (firstProjection u) p (domainMeasure G) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq0,
          eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hu.aestronglyMeasurable]
      _ ≤ _ := by gcongr; exact root_le_one_add A hq0 hq1
  have hse : seminorm G s p (firstProjection u) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hq0 he.ne
  have hfin : seminorm G s p (firstProjection u) +
      (1 + A) * eLpNorm (firstProjection u) p (domainMeasure G) ≠ ∞ := by
    finiteness
  have hsem' := ENNReal.toReal_mono hfin hsem
  rw [ENNReal.toReal_add hse (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_add (by simp) hA, ENNReal.toReal_one] at hsem'
  rw [hnorm, hLp, space_norm hpt, Lp.norm_def]
  nlinarith [ENNReal.toReal_nonneg (a := seminorm G s p (firstProjection u)),
    ENNReal.toReal_nonneg (a := eLpNorm (firstProjection u) p (domainMeasure G)),
    ENNReal.toReal_nonneg (a := A)]

end P102.Fractional.ZeroExtension

namespace P102.Fractional.ZeroExtension
/-- Zero extension across separated artificial edges, including the uniform
energy estimate and realization in the canonical Gagliardo graph space. -/
theorem zero_extension_away : Specs.P102.Fractional.LocalizationZero.zeroExtensionAway := by
  intro d hd s hs _hs1 p _ hpt
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  let C : ℝ≥0 := ⟨2 * ZeroExtension.tailConstant d (s * p.toReal),
    mul_nonneg (by norm_num) (ZeroExtension.tailConstant_nonneg (mul_pos hs hp))⟩
  refine ⟨C, ?_⟩
  intro 𝕜 _ G H hG hH hGH δ hδ
  have hC : (C : ℝ≥0∞) = ENNReal.ofReal (2 * ZeroExtension.tailConstant d (s * p.toReal)) := by
    exact ENNReal.ofReal_coe_nnreal.symm
  constructor
  · intro u hu hsep
    rw [hC]
    exact ZeroExtension.energy_indicator_bound hd hs hp hG.measurableSet hH.measurableSet hGH
      hδ hu.aestronglyMeasurable hsep
  · intro u hsep
    let A : ℝ≥0∞ := (C : ℝ≥0∞) * ENNReal.ofReal (δ ^ (-s * p.toReal))
    have hA : A ≠ ∞ := by dsimp [A]; finiteness
    have he : energy H s p (G.indicator (firstProjection u)) ≤
        energy G s p (firstProjection u) +
          A * (∫⁻ x, ‖firstProjection u x‖ₑ ^ p.toReal ∂domainMeasure G) := by
      dsimp [A]
      rw [hC]
      exact ZeroExtension.energy_indicator_bound hd hs hp hG.measurableSet hH.measurableSet hGH
        hδ (Lp.aestronglyMeasurable _) hsep
    have hAr : A.toReal = (C : ℝ) * δ ^ (-s * p.toReal) := by
      simp only [A, ENNReal.toReal_mul, ENNReal.coe_toReal,
        ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le _)]
    simpa only [hAr] using
      ZeroExtension.exists_extension_of_energy_bound hpt hG.measurableSet hGH A hA u he
end P102.Fractional.ZeroExtension

