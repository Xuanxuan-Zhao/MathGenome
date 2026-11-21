import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.LocalizationPullback
import MathGenome.Internal.FourierSobolev.P102.Fractional.Space
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal NNReal Topology
namespace P102.Fractional.Pullback
open P102.Fractional

variable {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
variable {G H : Set (Domain d)} {s : ℝ} {p : ℝ≥0∞}

/-- Lipschitz distortion for Lebesgue outer measure, for arbitrary subsets.
No differentiability, boundedness or regularity of the subset is needed. -/
theorem volume_image_le {A : Set (Domain d)} {f : Domain d → Domain d}
    {K : ℝ≥0} (hf : LipschitzOnWith K f A) :
    volume (f '' A) ≤ (K : ℝ≥0∞) ^ d * volume A := by
  let μ : Measure (Domain d) := hausdorffMeasure (Module.finrank ℝ (Domain d))
  have hv := isAddLeftInvariant_eq_smul (volume : Measure (Domain d)) μ
  have hi := hf.hausdorffMeasure_image_le
    (show (0 : ℝ) ≤ Module.finrank ℝ (Domain d) from Nat.cast_nonneg _)
  have hi' : μ (f '' A) ≤ (K : ℝ≥0∞) ^ d * μ A := by
    simpa [μ, Domain, ENNReal.rpow_natCast] using hi
  have hvA := congrArg (fun ν : Measure (Domain d) => ν A) hv
  have hvI := congrArg (fun ν : Measure (Domain d) => ν (f '' A)) hv
  rw [hvA, hvI]
  change (addHaarScalarFactor (volume : Measure (Domain d)) μ : ℝ≥0∞) * μ (f '' A) ≤
    (K : ℝ≥0∞) ^ d * ((addHaarScalarFactor (volume : Measure (Domain d)) μ : ℝ≥0∞) * μ A)
  calc
    _ ≤ (addHaarScalarFactor (volume : Measure (Domain d)) μ : ℝ≥0∞) *
        ((K : ℝ≥0∞) ^ d * μ A) := by gcongr
    _ = _ := by ac_rfl

/-- An ambient version of the chart coordinate map. -/
def coordinate (F : G ≃ₜ H) (x : Domain d) : Domain d := by
  classical
  exact if hx : x ∈ G then F ⟨x, hx⟩ else 0

@[simp] theorem coordinate_apply (F : G ≃ₜ H) (x : G) :
    coordinate F x = (F x : Domain d) := by simp [coordinate, x.property]

/-- The coordinate map is measurable on the ambient space, even for an empty chart. -/
theorem coordinate_measurable (hG : MeasurableSet G) (F : G ≃ₜ H) :
    Measurable (coordinate F) := by
  classical
  have he := (MeasurableEmbedding.subtype_coe hG).measurable_extend
    (measurable_subtype_coe.comp F.continuous.measurable)
    (measurable_const : Measurable (fun _ : Domain d => (0 : Domain d)))
  convert he using 1
  funext x
  by_cases hx : x ∈ G
  · simpa [coordinate, hx, Function.comp_def] using
      (Subtype.val_injective.extend_apply (fun y : G => (F y : Domain d))
        (fun _ => (0 : Domain d)) ⟨x, hx⟩).symm
  · rw [Function.extend_apply' _ _ x (by simpa using hx)]
    simp [coordinate, hx]

/-- Subtype Lipschitz bounds give the corresponding ambient bound on the chart. -/
theorem coordinate_lipschitzOn {K : ℝ≥0} (F : G ≃ₜ H) (hF : LipschitzWith K F) :
    LipschitzOnWith K (coordinate F) G := by
  intro x hx y hy
  simpa only [← coordinate_apply F ⟨x, hx⟩, ← coordinate_apply F ⟨y, hy⟩,
    Subtype.edist_eq] using hF.edist_le_mul ⟨x, hx⟩ ⟨y, hy⟩

/-- Source preimages are images by the inverse chart, including empty sets. -/
theorem coordinate_preimage_inter (F : G ≃ₜ H) (A : Set (Domain d)) :
    coordinate F ⁻¹' A ∩ G = coordinate F.symm '' (A ∩ H) := by
  ext x
  constructor
  · rintro ⟨hxA, hxG⟩
    refine ⟨F ⟨x, hxG⟩, ⟨?_, (F ⟨x, hxG⟩).property⟩, ?_⟩
    · simpa only [Set.mem_preimage, coordinate_apply F ⟨x, hxG⟩] using hxA
    · simp
  · rintro ⟨y, ⟨hyA, hyH⟩, rfl⟩
    have hG' : coordinate F.symm y ∈ G := by
      simpa only [coordinate_apply F.symm ⟨y, hyH⟩] using (F.symm ⟨y, hyH⟩).property
    refine ⟨?_, hG'⟩
    simpa only [Set.mem_preimage, coordinate_apply F.symm ⟨y, hyH⟩,
      coordinate_apply F (F.symm ⟨y, hyH⟩), F.apply_symm_apply] using hyA

/-- The inverse Lipschitz bound controls pushforward restricted volume. -/
theorem map_domainMeasure_le (hG : IsOpen G) (_hH : IsOpen H)
    (F : G ≃ₜ H) {K' : ℝ≥0} (hF' : LipschitzWith K' F.symm) :
    (domainMeasure G).map (coordinate F) ≤
      (K' : ℝ≥0∞) ^ d • domainMeasure H := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply (coordinate_measurable hG.measurableSet F) hA,
    domainMeasure, Measure.restrict_apply
      ((coordinate_measurable hG.measurableSet F) hA),
    coordinate_preimage_inter, Measure.smul_apply,
    domainMeasure, Measure.restrict_apply hA]
  exact volume_image_le ((coordinate_lipschitzOn F.symm hF').mono Set.inter_subset_right)

/-- Null sets pull back to null sets solely from the Lipschitz hypotheses. -/
theorem coordinate_quasiMeasurePreserving (hG : IsOpen G) (hH : IsOpen H)
    (F : G ≃ₜ H) {K' : ℝ≥0} (hF' : LipschitzWith K' F.symm) :
    QuasiMeasurePreserving (coordinate F) (domainMeasure G) (domainMeasure H) :=
  ⟨coordinate_measurable hG.measurableSet F,
    absolutelyContinuous_of_le_smul (map_domainMeasure_le hG hH F hF')⟩

/-- Pullback respects a.e. representatives on arbitrary open charts. -/
theorem raw_congr (hG : IsOpen G) (hH : IsOpen H)
    (F : G ≃ₜ H) {K' : ℝ≥0} (hF' : LipschitzWith K' F.symm)
    {u v : Domain d → 𝕜} (huv : u =ᵐ[domainMeasure H] v) :
    raw F u =ᵐ[domainMeasure G] raw F v := by
  have hh := (coordinate_quasiMeasurePreserving hG hH F hF').ae huv
  filter_upwards [hh, ae_restrict_mem hG.measurableSet] with x hx hxG
  simpa [raw, coordinate, hxG] using hx

/-- Exact change to the pushforward measure for any nonnegative integrand.
The measurable embedding of the chart subtype removes a measurability restriction
on the integrand. -/
theorem lintegral_coordinate (hG : IsOpen G) (hH : IsOpen H)
    (F : G ≃ₜ H) (f : Domain d → ℝ≥0∞) :
    (∫⁻ x, f (coordinate F x) ∂domainMeasure G) =
      ∫⁻ y, f y ∂(domainMeasure G).map (coordinate F) := by
  let ν : Measure G := volume.comap Subtype.val
  have hmap : ν.map (fun x : G => (F x : Domain d)) =
      (domainMeasure G).map (coordinate F) := by
    have hfun : (fun x : G => (F x : Domain d)) = coordinate F ∘ Subtype.val := by
      funext x
      simp
    rw [hfun, ← Measure.map_map (coordinate_measurable hG.measurableSet F)
      measurable_subtype_coe]
    rw [show ν.map Subtype.val = domainMeasure G from map_comap_subtype_coe hG.measurableSet volume]
  rw [← hmap]
  change _ = ∫⁻ y, f y ∂ν.map (Subtype.val ∘ F)
  rw [((MeasurableEmbedding.subtype_coe hH.measurableSet).comp
    F.measurableEmbedding).lintegral_map]
  simpa only [coordinate_apply, Function.comp_apply, domainMeasure, ν] using
    (lintegral_subtype_comap (μ := volume) hG.measurableSet
      (fun x => f (coordinate F x))).symm

/-- Quantitative change of coordinates, also valid for nonmeasurable nonnegative
integrands. -/
theorem lintegral_coordinate_le (hG : IsOpen G) (hH : IsOpen H)
    (F : G ≃ₜ H) {K' : ℝ≥0} (hF' : LipschitzWith K' F.symm)
    (f : Domain d → ℝ≥0∞) :
    (∫⁻ x, f (coordinate F x) ∂domainMeasure G) ≤
      (K' : ℝ≥0∞) ^ d * ∫⁻ y, f y ∂domainMeasure H := by
  rw [lintegral_coordinate hG hH F f]
  calc
    _ ≤ ∫⁻ y, f y ∂((K' : ℝ≥0∞) ^ d • domainMeasure H) :=
      lintegral_mono' (map_domainMeasure_le hG hH F hF') le_rfl
    _ = _ := by rw [lintegral_smul_measure]; rfl

/-- The raw density, retaining the original diagonal convention. -/
def density (s : ℝ) (p : ℝ≥0∞) (u : Domain d → 𝕜)
    (x y : Domain d) : ℝ≥0∞ :=
  if x = y then 0 else
    ‖u x - u y‖ₑ ^ p.toReal / ENNReal.ofReal ‖x - y‖ ^ ((d : ℝ) + s * p.toReal)

/-- Forward Lipschitz control compares the singular densities pointwise. -/
theorem density_raw_le {K : ℝ≥0} (F : G ≃ₜ H) (hF : LipschitzWith K F)
    (hα : 0 ≤ (d : ℝ) + s * p.toReal) (u : Domain d → 𝕜)
    {x y : Domain d} (hx : x ∈ G) (hy : y ∈ G) :
    density s p (raw F u) x y ≤
      (K : ℝ≥0∞) ^ ((d : ℝ) + s * p.toReal) *
        density s p u (coordinate F x) (coordinate F y) := by
  classical
  have heq : coordinate F x = coordinate F y ↔ x = y := by
    constructor
    · intro h
      exact congrArg Subtype.val (F.injective
        (show F ⟨x, hx⟩ = F ⟨y, hy⟩ from Subtype.ext
          (by simpa [coordinate, hx, hy] using h)))
    · exact congrArg (coordinate F)
  by_cases hxy : x = y
  · simp [density, hxy]
  have hD : ENNReal.ofReal ‖coordinate F x - coordinate F y‖ ^ ((d : ℝ) + s * p.toReal) ≤
      (K : ℝ≥0∞) ^ ((d : ℝ) + s * p.toReal) *
        ENNReal.ofReal ‖x - y‖ ^ ((d : ℝ) + s * p.toReal) := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hα]
    apply ENNReal.rpow_le_rpow _ hα
    have hh := (coordinate_lipschitzOn F hF).dist_le_mul x hx y hy
    simpa only [dist_eq_norm, ENNReal.ofReal_mul (NNReal.coe_nonneg K),
      ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hh
  have h0 : ENNReal.ofReal ‖x - y‖ ^ ((d : ℝ) + s * p.toReal) ≠ 0 := by
    exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr
      (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))) ENNReal.ofReal_ne_top).ne'
  have ht : ENNReal.ofReal ‖x - y‖ ^ ((d : ℝ) + s * p.toReal) ≠ ∞ := by
    finiteness
  have hT0 : ENNReal.ofReal ‖coordinate F x - coordinate F y‖ ^
      ((d : ℝ) + s * p.toReal) ≠ 0 := by
    exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr
      (norm_pos_iff.mpr (sub_ne_zero.mpr (heq.not.mpr hxy)))) ENNReal.ofReal_ne_top).ne'
  have hTt : ENNReal.ofReal ‖coordinate F x - coordinate F y‖ ^
      ((d : ℝ) + s * p.toReal) ≠ ∞ := by finiteness
  have hi : (1 : ℝ≥0∞) / ENNReal.ofReal ‖x - y‖ ^ ((d : ℝ) + s * p.toReal) ≤
      (K : ℝ≥0∞) ^ ((d : ℝ) + s * p.toReal) *
        (ENNReal.ofReal ‖coordinate F x - coordinate F y‖ ^
          ((d : ℝ) + s * p.toReal))⁻¹ := by
    apply (ENNReal.div_le_iff h0 ht).mpr
    calc
      1 = (ENNReal.ofReal ‖coordinate F x - coordinate F y‖ ^
          ((d : ℝ) + s * p.toReal))⁻¹ *
          ENNReal.ofReal ‖coordinate F x - coordinate F y‖ ^
          ((d : ℝ) + s * p.toReal) := (ENNReal.inv_mul_cancel hT0 hTt).symm
      _ ≤ (ENNReal.ofReal ‖coordinate F x - coordinate F y‖ ^
          ((d : ℝ) + s * p.toReal))⁻¹ *
          ((K : ℝ≥0∞) ^ ((d : ℝ) + s * p.toReal) *
          ENNReal.ofReal ‖x - y‖ ^ ((d : ℝ) + s * p.toReal)) := by gcongr
      _ = _ := by ac_rfl
  simp only [one_div] at hi
  simp only [density, heq, ite_eq_right hxy, raw, dite_eq_left hx, dite_eq_left hy]
  rw [← coordinate_apply F ⟨x, hx⟩, ← coordinate_apply F ⟨y, hy⟩]
  simp only [div_eq_mul_inv]
  calc
    _ ≤ ‖u (coordinate F x) - u (coordinate F y)‖ₑ ^ p.toReal *
      ((K : ℝ≥0∞) ^ ((d : ℝ) + s * p.toReal) *
      (ENNReal.ofReal ‖coordinate F x - coordinate F y‖ ^
        ((d : ℝ) + s * p.toReal))⁻¹) := by gcongr
    _ = _ := by ac_rfl

/-- The raw Lp mass estimate. -/
theorem mass_raw_le (hG : IsOpen G) (hH : IsOpen H)
    (F : G ≃ₜ H) {K' : ℝ≥0} (hF' : LipschitzWith K' F.symm)
    (u : Domain d → 𝕜) :
    (∫⁻ x, ‖raw F u x‖ₑ ^ p.toReal ∂domainMeasure G) ≤
      (K' : ℝ≥0∞) ^ d * ∫⁻ y, ‖u y‖ₑ ^ p.toReal ∂domainMeasure H := by
  calc
    _ = ∫⁻ x, ‖u (coordinate F x)‖ₑ ^ p.toReal ∂domainMeasure G := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hG.measurableSet] with x hx
      simp [raw, coordinate, hx]
    _ ≤ _ := lintegral_coordinate_le hG hH F hF' (fun y => ‖u y‖ₑ ^ p.toReal)

/-- Applying the volume estimate in each variable gives the complete double
integral estimate. This stronger raw statement needs no measurability of u. -/
theorem energy_raw_le (hG : IsOpen G) (hH : IsOpen H)
    (F : G ≃ₜ H) {K K' : ℝ≥0} (hF : LipschitzWith K F)
    (hF' : LipschitzWith K' F.symm) (hα : 0 ≤ (d : ℝ) + s * p.toReal)
    (u : Domain d → 𝕜) :
    energy G s p (raw F u) ≤
      ((K' : ℝ≥0∞) ^ d * (K' : ℝ≥0∞) ^ d *
        (K : ℝ≥0∞) ^ ((d : ℝ) + s * p.toReal)) * energy H s p u := by
  let A : ℝ≥0∞ := (K' : ℝ≥0∞) ^ d
  let B : ℝ≥0∞ := (K : ℝ≥0∞) ^ ((d : ℝ) + s * p.toReal)
  have hAt : A ≠ ∞ := by dsimp [A]; finiteness
  have hBt : B ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hα ENNReal.coe_ne_top
  have hrow (x : Domain d) :
      (∫⁻ y, density s p u (coordinate F x) (coordinate F y) ∂domainMeasure G) ≤
        A * ∫⁻ y, density s p u (coordinate F x) y ∂domainMeasure H :=
    lintegral_coordinate_le hG hH F hF' (density s p u (coordinate F x))
  change (∫⁻ x, ∫⁻ y, density s p (raw F u) x y
    ∂domainMeasure G ∂domainMeasure G) ≤ _
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, B * density s p u (coordinate F x) (coordinate F y)
        ∂domainMeasure G ∂domainMeasure G := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hG.measurableSet] with x hx
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hG.measurableSet] with y hy
      exact density_raw_le F hF hα u hx hy
    _ = B * ∫⁻ x, ∫⁻ y, density s p u (coordinate F x) (coordinate F y)
        ∂domainMeasure G ∂domainMeasure G := by
      simp_rw [lintegral_const_mul' B _ hBt]
    _ ≤ B * ∫⁻ x, A * ∫⁻ y, density s p u (coordinate F x) y
        ∂domainMeasure H ∂domainMeasure G := by
      gcongr with x
      exact hrow x
    _ = B * (A * ∫⁻ x, ∫⁻ y, density s p u (coordinate F x) y
        ∂domainMeasure H ∂domainMeasure G) := by
      rw [lintegral_const_mul' A _ hAt]
    _ ≤ B * (A * (A * ∫⁻ x, ∫⁻ y, density s p u x y
        ∂domainMeasure H ∂domainMeasure H)) := by
      gcongr
      exact lintegral_coordinate_le hG hH F hF'
        (fun x => ∫⁻ y, density s p u x y ∂domainMeasure H)
    _ = _ := by change B * (A * (A * energy H s p u)) = _; dsimp [A, B]; ac_rfl

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

/-- The chart operation is linear on raw representatives. -/
def rawLinear (F : G ≃ₜ H) :
    (Domain d → 𝕜) →ₗ[𝕜] (Domain d → 𝕜) where
  toFun := raw F
  map_add' u v := by
    classical
    funext x
    by_cases hx : x ∈ G <;> simp [raw, hx]
  map_smul' c u := by
    classical
    funext x
    by_cases hx : x ∈ G <;> simp [raw, hx]

/-- On the integration domain the zero-off-domain formula is composition. -/
theorem raw_ae_comp (hG : IsOpen G) (F : G ≃ₜ H) (u : Domain d → 𝕜) :
    raw F u =ᵐ[domainMeasure G] u ∘ coordinate F := by
  filter_upwards [ae_restrict_mem hG.measurableSet] with x hx
  simp [raw, coordinate, hx]

/-- Measurability of the pullback follows from the proved null-set estimate. -/
theorem raw_aestronglyMeasurable (hG : IsOpen G) (hH : IsOpen H)
    (F : G ≃ₜ H) {K' : ℝ≥0} (hF' : LipschitzWith K' F.symm)
    {u : Domain d → 𝕜} (hu : AEStronglyMeasurable u (domainMeasure H)) :
    AEStronglyMeasurable (raw F u) (domainMeasure G) :=
  (hu.comp_quasiMeasurePreserving (coordinate_quasiMeasurePreserving hG hH F hF')).congr
    (raw_ae_comp hG F u).symm

/-- A mass comparison with a uniform constant controls the Lp norm. -/
theorem eLpNorm_raw_le [Fact (1 ≤ p)] (hpt : p ≠ ∞)
    (hG : IsOpen G) (hH : IsOpen H) (F : G ≃ₜ H)
    {K' C : ℝ≥0} (hF' : LipschitzWith K' F.symm) (hC : 1 ≤ C)
    (hAC : K' ^ d ≤ C) {u : Domain d → 𝕜}
    (hu : MemLp u p (domainMeasure H)) :
    MemLp (raw F u) p (domainMeasure G) ∧
      eLpNorm (raw F u) p (domainMeasure G) ≤
        (C : ℝ≥0∞) * eLpNorm u p (domainMeasure H) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hm := raw_aestronglyMeasurable hG hH F hF' hu.aestronglyMeasurable
  have hb : eLpNorm (raw F u) p (domainMeasure G) ≤
      (C : ℝ≥0∞) * eLpNorm u p (domainMeasure H) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hm,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hu.aestronglyMeasurable]
    apply root_le_mul_root hpt (by exact_mod_cast hC)
    exact (mass_raw_le hG hH F hF' u).trans (by gcongr; exact_mod_cast hAC)
  exact ⟨hb.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hu.eLpNorm_lt_top), hb⟩

/-- The full bi-Lipschitz pullback theorem on the canonical Gagliardo spaces. -/
theorem bilipschitz_pullback :
    Specs.P102.Fractional.LocalizationPullback.bilipschitzPullback := by
  intro d hd s hs hs1 p _ hpt K K'
  have hα : 0 ≤ (d : ℝ) + s * p.toReal := by positivity
  let A : ℝ≥0 := K' ^ d
  let B : ℝ≥0 := K ^ ((d : ℝ) + s * p.toReal)
  let C : ℝ≥0 := max 1 (A + A * A * B)
  have hC : 1 ≤ C := le_max_left _ _
  have hAC : A ≤ C := (le_add_of_nonneg_right (by positivity)).trans (le_max_right _ _)
  have hEC : A * A * B ≤ C :=
    (le_add_of_nonneg_left (by positivity)).trans (le_max_right _ _)
  refine ⟨C, ?_⟩
  intro 𝕜 _ G H hG hH F hF hF'
  have he (u : Domain d → 𝕜) :
      energy G s p (raw F u) ≤ (C : ℝ≥0∞) * energy H s p u := by
    calc
      _ ≤ (↑(A * A * B) : ℝ≥0∞) * energy H s p u := by
        simpa only [A, B, ENNReal.coe_mul, ENNReal.coe_pow,
          ENNReal.coe_rpow_of_nonneg K hα] using energy_raw_le hG hH F hF hF' hα u
      _ ≤ _ := by gcongr
  have hm (u : Domain d → 𝕜) :
      (∫⁻ x, ‖raw F u x‖ₑ ^ p.toReal ∂domainMeasure G) ≤
        (C : ℝ≥0∞) * ∫⁻ x, ‖u x‖ₑ ^ p.toReal ∂domainMeasure H := by
    exact (mass_raw_le hG hH F hF' u).trans (by gcongr; exact_mod_cast hAC)
  refine ⟨fun _ _ h => raw_congr hG hH F hF' h, fun u _ => ⟨he u, hm u⟩, ?_⟩
  have hLp (u : Space 𝕜 H s p) :=
    eLpNorm_raw_le hpt hG hH F hF' hC hAC (Lp.memLp (firstProjection u))
  have henergy (u : Space 𝕜 H s p) :
      energy G s p (raw F (firstProjection u)) < ∞ := by
    exact (he _).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
      ((firstProjection_range hpt (firstProjection u)).mp ⟨u, rfl⟩))
  apply exists_continuousLinearMap_of_representatives hpt (rawLinear F)
    (fun _ _ h => raw_congr hG hH F hF' h)
    (fun u => (hLp u).1) henergy (C : ℝ)
  intro u
  have hlu := Lp.memLp (firstProjection u)
  have hse : seminorm H s p (firstProjection u) < ∞ :=
    (firstProjection_range_seminorm hpt (firstProjection u)).mp ⟨u, rfl⟩
  have hsem : seminorm G s p (raw F (firstProjection u)) ≤
      (C : ℝ≥0∞) * seminorm H s p (firstProjection u) :=
    root_le_mul_root hpt (by exact_mod_cast hC) (he _)
  have hLp' := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hlu.eLpNorm_lt_top.ne) (hLp u).2
  have hsem' := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hse.ne) hsem
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal] at hLp' hsem'
  change (eLpNorm (raw F (firstProjection u)) p (domainMeasure G)).toReal +
    (seminorm G s p (raw F (firstProjection u))).toReal ≤ _
  rw [space_norm hpt, Lp.norm_def, mul_add]
  exact add_le_add hLp' hsem'

end P102.Fractional.Pullback

