import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Localization
import MathGenome.Internal.FourierSobolev.P102.Fractional.Space
import MathGenome.Internal.FourierSobolev.P102.Fractional.LocalizationMultiplier
import MathGenome.Internal.FourierSobolev.P102.Fractional.LocalizationPullback
import MathGenome.Internal.FourierSobolev.P102.Fractional.LocalizationZero
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace P102.Fractional

variable {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
variable {G H : Set (Domain d)} {s : ℝ} {p : ℝ≥0∞}

/-- Bounded Lipschitz multiplication, with one uniform constant for the raw
energy estimate and the operator on the canonical sum-norm graph space. -/
theorem bounded_lipschitz_multiplier :
    Specs.P102.Fractional.Localization.boundedMultiplier := by
  exact LocalizationMultiplier.bounded_lipschitz_multiplier

/-- Bi-Lipschitz chart pullback, including compatibility with a.e. classes,
the energy and mass estimates, and the bounded scalar-linear operator. -/
theorem bilipschitz_pullback :
    Specs.P102.Fractional.Localization.bilipschitzPullback := by
  exact Pullback.bilipschitz_pullback

/-- Zero extension across a separated artificial edge. The original energy
has coefficient one, and the same constant controls the sum-norm bound. -/
theorem zero_extension_away :
    Specs.P102.Fractional.Localization.zeroExtensionAway := by
  exact ZeroExtension.zero_extension_away

/-- Restricting the domain decreases the original double integral. -/
theorem energy_mono_domain (hGH : G ⊆ H) (u : Domain d → 𝕜) :
    energy G s p u ≤ energy H s p u := by
  unfold energy domainMeasure
  apply lintegral_mono' (Measure.restrict_mono hGH le_rfl)
  intro x
  exact lintegral_mono' (Measure.restrict_mono hGH le_rfl) (fun _ => le_rfl)

/-- Almost-everywhere independence of the zero-extension representative. -/
theorem zeroExtend_congr (hG : MeasurableSet G) {u v : Domain d → 𝕜}
    (huv : u =ᵐ[domainMeasure G] v) :
    zeroExtend G u =ᵐ[domainMeasure H] zeroExtend G v := by
  apply ae_restrict_of_ae
  have huv' := (ae_restrict_iff' hG).mp huv
  filter_upwards [huv'] with x hx
  by_cases hxG : x ∈ G
  · simp [zeroExtend, hxG, hx hxG]
  · simp [zeroExtend, hxG]

/-- The separation condition does not depend on the Lp representative. -/
theorem supportedAway_congr {δ : ℝ} {u v : Domain d → 𝕜}
    (huv : u =ᵐ[domainMeasure G] v) :
    SupportedAway G H δ u ↔ SupportedAway G H δ v := by
  constructor <;> intro h
  · filter_upwards [h, huv] with x hx heq
    simpa only [heq] using hx
  · filter_upwards [h, huv] with x hx heq
    simpa only [heq] using hx

/-- Zero extension preserves the Lp mass exactly. -/
theorem lpMass_zeroExtend (hG : MeasurableSet G) (hGH : G ⊆ H)
    (hp : 0 < p.toReal) (u : Domain d → 𝕜) :
    lpMass H p (zeroExtend G u) = lpMass G p u := by
  classical
  have hfun : (fun x => ‖zeroExtend G u x‖ₑ ^ p.toReal) =
      G.indicator (fun x => ‖u x‖ₑ ^ p.toReal) := by
    funext x
    by_cases hx : x ∈ G <;> simp [zeroExtend, hx, ENNReal.zero_rpow_of_pos hp]
  unfold lpMass
  rw [hfun, lintegral_indicator hG]
  simp only [domainMeasure, Measure.restrict_restrict hG,
    Set.inter_eq_left.mpr hGH]

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

@[simp] theorem flatReflection_apply {n : ℕ} (x : Domain (n + 1))
    (i : Fin (n + 1)) :
    flatReflection x i = if i = 0 then -x i else x i := rfl

@[simp] theorem flatReflection_height {n : ℕ} (x : Domain (n + 1)) :
    flatReflection x 0 = -x 0 := by simp

@[simp] theorem flatReflection_involutive {n : ℕ} (x : Domain (n + 1)) :
    flatReflection (flatReflection x) = x := by
  ext i
  by_cases hi : i = 0 <;> simp [hi]

/-- Reflection as a linear isometry, for change of variables with volume. -/
def flatReflectionLinearIsometryEquiv (n : ℕ) :
    Domain (n + 1) ≃ₗᵢ[ℝ] Domain (n + 1) where
  toFun := flatReflection
  invFun := flatReflection
  left_inv := flatReflection_involutive
  right_inv := flatReflection_involutive
  map_add' x y := by
    ext i
    by_cases hi : i = 0 <;> simp [hi, add_comm]
  map_smul' c x := by
    ext i
    by_cases hi : i = 0 <;> simp [hi]
  norm_map' x := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = 0 <;> simp [hi]

/-- Reflection preserves Lebesgue volume in every positive dimension. -/
theorem flatReflection_measurePreserving (n : ℕ) :
    MeasurePreserving (flatReflection : Domain (n + 1) → Domain (n + 1)) :=
  (flatReflectionLinearIsometryEquiv n).measurePreserving

/-- The distance across the flat face is at least the reflected same-side
 distance, precisely the t+u versus |t-u| comparison in the source. -/
theorem dist_le_dist_flatReflection {n : ℕ} {x y : Domain (n + 1)}
    (hx : x ∈ upperHalfSpace n) (hy : y ∈ upperHalfSpace n) :
    dist x y ≤ dist x (flatReflection y) := by
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i = 0
  · subst i
    simp only [flatReflection_height, Real.dist_eq, sq_abs]
    have hx' : 0 < x 0 := hx
    have hy' : 0 < y 0 := hy
    nlinarith [mul_pos hx' hy']
  · simp [hi]

/-- Even reflection respects the original a.e. class, including on the face
where the definition explicitly assigns zero. -/
theorem evenExtend_congr {n : ℕ} {u v : Domain (n + 1) → 𝕜}
    (huv : u =ᵐ[domainMeasure (upperHalfSpace n)] v) :
    evenExtend u =ᵐ[domainMeasure Set.univ] evenExtend v := by
  have hH : MeasurableSet (upperHalfSpace n) := by
    unfold upperHalfSpace
    exact (isOpen_lt continuous_const
      (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0)).measurableSet
  have h := (ae_restrict_iff' hH).mp huv
  have hr := (flatReflection_measurePreserving n).quasiMeasurePreserving.ae h
  apply ae_restrict_of_ae
  filter_upwards [h, hr] with x hx hrx
  by_cases hzero : x 0 = 0
  · simp [evenExtend, hzero]
  by_cases hpos : 0 < x 0
  · simp [evenExtend, hzero, hpos, hx hpos]
  · have hneg : x 0 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hzero
    have hrpos : flatReflection x ∈ upperHalfSpace n := by
      change 0 < flatReflection x 0
      simpa using neg_pos.mpr hneg
    simp [evenExtend, hzero, hpos, hrx hrpos]

/-- The raw Lp mass is doubled by reflection. No trace value on the face
is assumed: the extension is zero there. -/
theorem lpMass_evenExtend {n : ℕ} {u : Domain (n + 1) → 𝕜}
    (hp : 0 < p.toReal)
    (hu : AEStronglyMeasurable u (domainMeasure (upperHalfSpace n))) :
    lpMass Set.univ p (evenExtend u) = 2 * lpMass (upperHalfSpace n) p u := by
  classical
  have hH : MeasurableSet (upperHalfSpace n) := by
    exact (isOpen_lt continuous_const
      (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0)).measurableSet
  let f : Domain (n + 1) → ℝ≥0∞ :=
    (upperHalfSpace n).indicator (fun x => ‖u x‖ₑ ^ p.toReal)
  have hf : AEMeasurable f volume :=
    (aemeasurable_indicator_iff hH).mpr (hu.enorm.pow_const p.toReal)
  have heq : (fun x => ‖evenExtend u x‖ₑ ^ p.toReal) =
      (fun x => f x + f (flatReflection x)) := by
    funext x
    rcases lt_trichotomy (x 0) 0 with hx | hx | hx
    · have hneg : ¬ 0 < x 0 := not_lt_of_ge hx.le
      simp [f, upperHalfSpace, evenExtend, ne_of_lt hx, hx, hneg]
    · simp [f, upperHalfSpace, evenExtend, hx, ENNReal.zero_rpow_of_pos hp]
    · simp [f, upperHalfSpace, evenExtend, ne_of_gt hx, hx, not_lt_of_ge hx.le]
  unfold lpMass
  simp only [domainMeasure, Measure.restrict_univ]
  rw [heq, lintegral_add_left' hf,
    (flatReflection_measurePreserving n).lintegral_comp_emb
      (flatReflectionLinearIsometryEquiv n).toHomeomorph.measurableEmbedding]
  dsimp only [f]
  rw [lintegral_indicator hH, two_mul]

@[simp] theorem evenExtend_of_pos {n : ℕ} (u : Domain (n + 1) → 𝕜)
    {x : Domain (n + 1)} (hx : 0 < x 0) : evenExtend u x = u x := by
  simp [evenExtend, ne_of_gt hx, hx]

@[simp] theorem evenExtend_reflection {n : ℕ} (u : Domain (n + 1) → 𝕜)
    (x : Domain (n + 1)) : evenExtend u (flatReflection x) = evenExtend u x := by
  rcases lt_trichotomy (x 0) 0 with hx | hx | hx
  · simp [evenExtend, ne_of_lt hx, hx, not_lt_of_ge hx.le]
  · simp [evenExtend, hx]
  · simp [evenExtend, ne_of_gt hx, hx, not_lt_of_ge hx.le]

/-- The flat face has zero Lebesgue measure, including in dimension one. -/
theorem flatFace_null (n : ℕ) :
    volume {x : Domain (n + 1) | x 0 = 0} = 0 := by
  let l : Domain (n + 1) →ₗ[ℝ] ℝ := PiLp.projₗ 2 (fun _ : Fin (n + 1) => ℝ) 0
  have hl : LinearMap.ker l ≠ ⊤ := by
    intro heq
    have hmem : WithLp.toLp 2 (fun _ : Fin (n + 1) => (1 : ℝ)) ∈ LinearMap.ker l := by
      rw [heq]
      trivial
    have : (1 : ℝ) = 0 := hmem
    norm_num at this
  exact MeasureTheory.Measure.addHaar_submodule volume (LinearMap.ker l) hl

/-- Split an arbitrary nonnegative integral into the two reflected open
half-spaces. No measurability of the integrand is needed. -/
theorem lintegral_halfSpace_reflection (n : ℕ) (f : Domain (n + 1) → ℝ≥0∞) :
    ∫⁻ x, f x = (∫⁻ x, f x ∂domainMeasure (upperHalfSpace n)) +
      ∫⁻ x, f (flatReflection x) ∂domainMeasure (upperHalfSpace n) := by
  have hH : MeasurableSet (upperHalfSpace n) :=
    (isOpen_lt continuous_const
      (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0)).measurableSet
  have heq : (upperHalfSpace n)ᶜ =ᵐ[volume]
      flatReflection ⁻¹' upperHalfSpace n := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (flatFace_null n)] with x hx
    change x 0 ≠ 0 at hx
    simp only [Set.mem_compl_iff, upperHalfSpace, Set.mem_ofPred_eq,
      Set.mem_preimage, flatReflection_height, neg_pos]
    exact propext ⟨fun h => lt_of_le_of_ne (le_of_not_gt h) hx,
      fun h => not_lt_of_ge h.le⟩
  have hchange := (flatReflection_measurePreserving n).setLIntegral_comp_preimage_emb
    (flatReflectionLinearIsometryEquiv n).toHomeomorph.measurableEmbedding
    (fun x => f (flatReflection x)) (upperHalfSpace n)
  simp only [flatReflection_involutive] at hchange
  rw [← lintegral_add_compl f hH, Measure.restrict_congr_set heq, hchange]
  rfl

/-- The diagonal convention is included in this raw density. -/
def energyIntegrand (s : ℝ) (p : ℝ≥0∞) (u : Domain d → 𝕜)
    (x y : Domain d) : ℝ≥0∞ :=
  if x = y then 0 else
    ‖u x - u y‖ₑ ^ p.toReal / ENNReal.ofReal ‖x - y‖ ^ ((d : ℝ) + s * p.toReal)

/-- The same-side reflected density agrees exactly with the original. -/
theorem energyIntegrand_reflection {n : ℕ} (u : Domain (n + 1) → 𝕜)
    (x y : Domain (n + 1)) :
    energyIntegrand s p (evenExtend u) (flatReflection x) (flatReflection y) =
      energyIntegrand s p (evenExtend u) x y := by
  have heq : flatReflection x = flatReflection y ↔ x = y :=
    (flatReflectionLinearIsometryEquiv n).injective.eq_iff
  have hnorm : ‖flatReflection x - flatReflection y‖ = ‖x - y‖ := by
    exact (flatReflectionLinearIsometryEquiv n).dist_map x y
  simp only [energyIntegrand, heq, evenExtend_reflection, hnorm]

/-- Each cross-face density is bounded by the same-side density. On the
same-side diagonal the numerator is zero, so the convention causes no gap. -/
theorem energyIntegrand_cross_le {n : ℕ} (hs : 0 ≤ s) (hp : 0 < p.toReal)
    (u : Domain (n + 1) → 𝕜) {x y : Domain (n + 1)}
    (hx : x ∈ upperHalfSpace n) (hy : y ∈ upperHalfSpace n) :
    energyIntegrand s p (evenExtend u) x (flatReflection y) ≤
      energyIntegrand s p u x y := by
  have hxy : x ≠ flatReflection y := by
    intro h
    have hx' : 0 < x 0 := hx
    have hy' : 0 < y 0 := hy
    have := congrArg (fun z : Domain (n + 1) => z 0) h
    simp only [flatReflection_height] at this
    linarith
  simp only [energyIntegrand, ite_eq_right hxy, evenExtend_reflection,
    evenExtend_of_pos u hx, evenExtend_of_pos u hy]
  by_cases heq : x = y
  · simp [heq, ENNReal.zero_rpow_of_pos hp]
  · rw [ite_eq_right heq]
    apply ENNReal.div_le_div_left
    apply ENNReal.rpow_le_rpow
    · exact ENNReal.ofReal_le_ofReal (by
        simpa only [dist_eq_norm] using dist_le_dist_flatReflection hx hy)
    · positivity

/-- The full reflected energy is at most four times the half-space energy. -/
theorem energy_evenExtend {n : ℕ} (hs : 0 ≤ s) (hp : 0 < p.toReal)
    (u : Domain (n + 1) → 𝕜) :
    energy Set.univ s p (evenExtend u) ≤ 4 * energy (upperHalfSpace n) s p u := by
  let f := energyIntegrand s p (evenExtend u)
  let g := energyIntegrand s p u
  have hsame : ∀ x ∈ upperHalfSpace n, ∀ y ∈ upperHalfSpace n,
      f x y = g x y := by
    intro x hx y hy
    simp only [f, g, energyIntegrand, evenExtend_of_pos u hx, evenExtend_of_pos u hy]
  have hrow : ∀ x ∈ upperHalfSpace n,
      (∫⁻ y, f x y) ≤ 2 * ∫⁻ y, g x y ∂domainMeasure (upperHalfSpace n) := by
    intro x hx
    rw [lintegral_halfSpace_reflection n]
    calc
      _ ≤ (∫⁻ y, g x y ∂domainMeasure (upperHalfSpace n)) +
          ∫⁻ y, g x y ∂domainMeasure (upperHalfSpace n) := by
        apply add_le_add
        · apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem (by
            exact (isOpen_lt continuous_const
              (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0)).measurableSet)]
            with y hy
          exact (hsame x hx y hy).le
        · apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem (by
            exact (isOpen_lt continuous_const
              (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0)).measurableSet)]
            with y hy
          exact energyIntegrand_cross_le hs hp u hx hy
      _ = _ := (two_mul _).symm
  have hrowR : ∀ x, (∫⁻ y, f (flatReflection x) y) = ∫⁻ y, f x y := by
    intro x
    rw [← (flatReflection_measurePreserving n).lintegral_comp_emb
      (flatReflectionLinearIsometryEquiv n).toHomeomorph.measurableEmbedding
      (fun y => f (flatReflection x) y)]
    apply lintegral_congr
    intro y
    exact energyIntegrand_reflection u x y
  change (∫⁻ x, ∫⁻ y, f x y ∂domainMeasure Set.univ ∂domainMeasure Set.univ) ≤ _
  simp only [domainMeasure, Measure.restrict_univ]
  rw [lintegral_halfSpace_reflection n]
  simp only [hrowR]
  calc
    _ ≤ (∫⁻ x, 2 * ∫⁻ y, g x y ∂domainMeasure (upperHalfSpace n)
          ∂domainMeasure (upperHalfSpace n)) +
        (∫⁻ x, 2 * ∫⁻ y, g x y ∂domainMeasure (upperHalfSpace n)
          ∂domainMeasure (upperHalfSpace n)) := by
      apply add_le_add <;> apply lintegral_mono_ae <;>
        filter_upwards [ae_restrict_mem (by
          exact (isOpen_lt continuous_const
            (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0)).measurableSet)]
          with x hx <;> exact hrow x hx
    _ = 4 * energy (upperHalfSpace n) s p u := by
      rw [lintegral_const_mul' _ _ (by norm_num)]
      change 2 * energy (upperHalfSpace n) s p u +
        2 * energy (upperHalfSpace n) s p u = _
      rw [← add_mul]
      norm_num

/-- Reflection is a scalar-linear operation on representatives. -/
def evenExtendLinear (n : ℕ) :
    (Domain (n + 1) → 𝕜) →ₗ[𝕜] (Domain (n + 1) → 𝕜) where
  toFun := evenExtend
  map_add' u v := by
    funext x
    by_cases hz : x 0 = 0 <;> by_cases hp : 0 < x 0 <;>
      simp [evenExtend, hz, hp]
  map_smul' c u := by
    funext x
    by_cases hz : x 0 = 0 <;> by_cases hp : 0 < x 0 <;>
      simp [evenExtend, hz, hp]

/-- The reflected representative is measurable whenever the source is. -/
theorem evenExtend_aestronglyMeasurable {n : ℕ} {u : Domain (n + 1) → 𝕜}
    (hu : AEStronglyMeasurable u (domainMeasure (upperHalfSpace n))) :
    AEStronglyMeasurable (evenExtend u) (domainMeasure Set.univ) := by
  have hH : MeasurableSet (upperHalfSpace n) :=
    (isOpen_lt continuous_const
      (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0)).measurableSet
  have hz : AEStronglyMeasurable (zeroExtend (upperHalfSpace n) u) volume :=
    (aestronglyMeasurable_indicator_iff hH).mpr hu
  have hzr := hz.comp_quasiMeasurePreserving
    (flatReflection_measurePreserving n).quasiMeasurePreserving
  have heq : evenExtend u = fun x => zeroExtend (upperHalfSpace n) u x +
      zeroExtend (upperHalfSpace n) u (flatReflection x) := by
    funext x
    rcases lt_trichotomy (x 0) 0 with hx | hx | hx
    · simp [evenExtend, zeroExtend, upperHalfSpace, ne_of_lt hx, hx,
        not_lt_of_ge hx.le]
    · simp [evenExtend, zeroExtend, upperHalfSpace, hx]
    · simp [evenExtend, zeroExtend, upperHalfSpace, ne_of_gt hx, hx,
        not_lt_of_ge hx.le]
  rw [heq]
  exact (hz.add hzr).restrict

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

/-- Reflection carries Lp representatives to Lp, with norm at most twice the
source norm. -/
theorem memLp_evenExtend {n : ℕ} [Fact (1 ≤ p)] (hpt : p ≠ ∞)
    {u : Domain (n + 1) → 𝕜} (hu : MemLp u p (domainMeasure (upperHalfSpace n))) :
    MemLp (evenExtend u) p (domainMeasure Set.univ) ∧
      eLpNorm (evenExtend u) p (domainMeasure Set.univ) ≤
        2 * eLpNorm u p (domainMeasure (upperHalfSpace n)) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hm := evenExtend_aestronglyMeasurable hu.aestronglyMeasurable
  have he : eLpNorm (evenExtend u) p (domainMeasure Set.univ) ≤
      2 * eLpNorm u p (domainMeasure (upperHalfSpace n)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hm,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hu.aestronglyMeasurable]
    apply root_le_mul_root hpt (by norm_num : (1:ℝ≥0∞) ≤ 2)
    exact (lpMass_evenExtend hp hu.aestronglyMeasurable).le
  exact ⟨he.trans_lt (ENNReal.mul_lt_top (by norm_num) hu.eLpNorm_lt_top), he⟩

/-- Bounded even reflection on the actual Gagliardo spaces, with the fourfold
energy comparison and doubled Lp mass of the source. -/
theorem even_reflection : Specs.P102.Fractional.Localization.evenReflection := by
  intro n s hs hs1 p _ hpt 𝕜 _
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  refine ⟨fun _ _ h => evenExtend_congr h, ?_, ?_⟩
  · intro u hu
    exact ⟨energy_evenExtend hs.le hp u, lpMass_evenExtend hp hu.aestronglyMeasurable⟩
  have henergy : ∀ u : Space 𝕜 (upperHalfSpace n) s p,
      energy Set.univ s p (evenExtend (firstProjection u)) < ∞ := by
    intro u
    exact (energy_evenExtend hs.le hp (firstProjection u)).trans_lt
      (ENNReal.mul_lt_top (by norm_num)
        ((firstProjection_range hpt (firstProjection u)).mp ⟨u, rfl⟩))
  apply exists_continuousLinearMap_of_representatives hpt (evenExtendLinear n)
    (fun _ _ h => evenExtend_congr h)
    (fun u => (memLp_evenExtend hpt (Lp.memLp (firstProjection u))).1)
    henergy 4
  intro u
  have hlu := Lp.memLp (firstProjection u)
  have he := (firstProjection_range hpt (firstProjection u)).mp ⟨u, rfl⟩
  have hse : seminorm (upperHalfSpace n) s p (firstProjection u) < ∞ := by
    rw [← eLpNorm_increment_eq_seminorm hp0 hpt hlu.aestronglyMeasurable]
    exact ((memLp_increment_iff hp0 hpt hlu.aestronglyMeasurable).mpr he).eLpNorm_lt_top
  have hLp := (memLp_evenExtend hpt hlu).2
  have hsem : seminorm Set.univ s p (evenExtend (firstProjection u)) ≤
      4 * seminorm (upperHalfSpace n) s p (firstProjection u) :=
    root_le_mul_root hpt (by norm_num) (energy_evenExtend hs.le hp (firstProjection u))
  have hLp' := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by norm_num) hlu.eLpNorm_lt_top.ne) hLp
  have hsem' := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by norm_num) hse.ne) hsem
  rw [ENNReal.toReal_mul] at hLp' hsem'
  rw [space_norm hpt, Lp.norm_def]
  change (eLpNorm (evenExtend (firstProjection u)) p (domainMeasure Set.univ)).toReal +
      (seminorm Set.univ s p (evenExtend (firstProjection u))).toReal ≤ _
  norm_num at hLp' hsem'
  nlinarith [ENNReal.toReal_nonneg (a := eLpNorm (firstProjection u) p
    (domainMeasure (upperHalfSpace n)))]

end P102.Fractional
