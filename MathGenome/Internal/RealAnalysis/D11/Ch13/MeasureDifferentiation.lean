import MathGenome.Internal.RealAnalysis.D11.Ch13.RegularShrinking
import MathGenome.Internal.RealAnalysis.D11.Ch13.LebesgueDifferentiation
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.MeasureDifferentiation
import Mathlib.MeasureTheory.Covering.DensityTheorem

/-! Differentiation of finite Borel measures, paper.tex:4467–4499.
The Vitali-family singular-measure lemma supplies the independent singular
step; elementary ball and cube comparisons transfer it to the source families.
All density integrals are taken in the canonical completed Lebesgue space. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
universe u
namespace D11.Ch13.MeasureDifferentiation
open D11.Ch03 D11.Ch03.LebesgueMeasures
open D11.Ch13.RegularShrinking D11.Ch13.AveragesMaximalDefinition
variable {n : ℕ} [NeZero n]

lemma completed_eq_native (E : Set (Point n))
    (hE : MeasurableSet[lebesgueSpace n] E) :
    lebesgue n E = (volume : Measure (Point n)) E :=
  (lebesgue_apply n E hE).trans (native_outer_agreement n E).symm

/-- The singular theorem in a native Borel Vitali family, followed by the
open-ball comparison. No assertion about the singular ratios is assumed. -/
lemma singular_balls_borel (σ : Measure (Point n)) [IsFiniteMeasure σ]
    (hs : σ ⟂ₘ (volume : Measure (Point n))) :
    ∀ᵐ x ∂(volume : Measure (Point n)),
      Tendsto (fun r => measureRatio σ (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let v := IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure (Point n)) 0
  filter_upwards [v.ae_eventually_measure_zero_of_singular hs] with x hx
  have hclosed : Tendsto
      (fun r => σ (closedBall x r) / (volume : Measure (Point n)) (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply hx.comp
    apply IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt _
      (fun _ : ℝ => x) id tendsto_id
    exact Eventually.of_forall (fun r => by simp)
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hclosed
  simp only [ENNReal.toReal_zero] at hreal
  apply squeeze_zero (fun r => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) _ hreal
  intro r
  change (σ (ball x r)).toReal / (lebesgue n (ball x r)).toReal ≤
    (σ (closedBall x r) / (volume : Measure (Point n)) (closedBall x r)).toReal
  rw [ENNReal.toReal_div, completed_eq_native _ (ball_measurable x r),
    Measure.addHaar_closedBall_eq_addHaar_ball (volume : Measure (Point n)) x r]
  exact div_le_div_of_nonneg_right
    (ENNReal.toReal_mono (measure_ne_top σ _) (measure_mono ball_subset_closedBall))
    ENNReal.toReal_nonneg

/-- Passing from Borel volume to its completed extension preserves conull
statements. This uses the proved Borel restriction identity. -/
theorem singular_centered_balls :
    Specs.D11.Ch13.MeasureDifferentiation.singular_centered_balls := by
  intro n _ σ _ hs
  have h := singular_balls_borel σ hs
  change ∀ᵐ x ∂Specs.D11.Ch03.LebesgueMeasures.borelMeasure_value n,
    Tendsto (fun r => measureRatio σ (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) at h
  rw [← borel_restriction n (native_borel_le n)] at h
  exact ae_of_ae_trim (native_borel_le n) h

/-- Monotonicity of finite masses and comparable positive volumes. -/
lemma ratio_comparison (σ : Measure (Point n)) [IsFiniteMeasure σ]
    {S T : Set (Point n)} {C : ℝ} (hST : S ⊆ T)
    (hS : 0 < (lebesgue n S).toReal) (hT : 0 < (lebesgue n T).toReal)
    (hvol : (lebesgue n T).toReal ≤ C * (lebesgue n S).toReal) :
    measureRatio σ S ≤ C * measureRatio σ T := by
  have hi := ENNReal.toReal_mono (measure_ne_top σ T) (measure_mono hST)
  have ht : 0 ≤ (σ T).toReal := ENNReal.toReal_nonneg
  change (σ S).toReal / (lebesgue n S).toReal ≤ C * ((σ T).toReal / (lebesgue n T).toReal)
  apply (div_le_iff₀ hS).mpr
  calc
    _ ≤ (C * (lebesgue n S).toReal) * (σ T).toReal / (lebesgue n T).toReal := by
      apply (le_div_iff₀ hT).mpr
      nlinarith [mul_le_mul_of_nonneg_left hvol ht,
        mul_le_mul_of_nonneg_right hi hT.le]
    _ = _ := by ring

/-- Every nondegenerate cube has a finite positive completed volume. -/
lemma cube_volume (e : Point n ≃ᵢ Point n) {s : ℝ} (hs : 0 < s) :
    0 < lebesgue n (closedCube e s) ∧ lebesgue n (closedCube e s) < ∞ := by
  constructor
  · exact (ball_measure (e 0) (s / 2) (half_pos hs)).1.trans_le
      (measure_mono (ball_subset_closedCube e s))
  · exact (measure_mono (closedCube_subset_ball e hs)).trans_lt
      (ball_measure (e 0) (((n : ℝ) + 1) * s) (by positivity)).2.1

/-- A dimensional bound uniform in position, orientation and side length. -/
lemma cube_ratio_comparison (σ : Measure (Point n)) [IsFiniteMeasure σ]
    (e : Point n ≃ᵢ Point n) {s : ℝ} (hs : 0 < s) {x : Point n}
    (hx : x ∈ closedCube e s) :
    measureRatio σ (closedCube e s) ≤
      (2 ^ n / ((2 * ((n : ℝ) + 1)) ^ n)⁻¹) *
        measureRatio σ (ball x (2 * (((n : ℝ) + 1) * s))) := by
  let c : ℝ := ((2 * ((n : ℝ) + 1)) ^ n)⁻¹
  let r : ℝ := ((n : ℝ) + 1) * s
  have hc : 0 < c := by dsimp [c]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hQ := cube_volume e hs
  have hf : ENNReal.ofReal c * lebesgue n (ball (e 0) r) ≤
      lebesgue n (closedCube e s) := closedCube_volume_ratio e s
  have hfracR : c * (lebesgue n (ball (e 0) r)).toReal ≤
      (lebesgue n (closedCube e s)).toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] using
      ENNReal.toReal_mono hQ.2.ne hf
  apply ratio_comparison σ
    ((closedCube_subset_ball e hs).trans
      (subset_centered_ball (closedCube_subset_ball e hs hx)))
    (ENNReal.toReal_pos hQ.1.ne' hQ.2.ne)
    (ball_measure x (2 * r) (by positivity)).2.2
  calc
    _ = 2 ^ n * (lebesgue n (ball (e 0) r)).toReal :=
      ball_real_scaling x (e 0) r 2 (by norm_num)
    _ ≤ 2 ^ n * ((lebesgue n (closedCube e s)).toReal / c) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) n)
      exact (le_div_iff₀ hc).mpr (by nlinarith [hfracR])
    _ = _ := by dsimp [c]; ring

/-- Positivity transfers the centered singular-ball limit to every cube
family, with a constant independent of that family. -/
theorem singular_cubes_of_balls (σ : Measure (Point n)) [IsFiniteMeasure σ]
    {x : Point n}
    (hx : Tendsto (fun r => measureRatio σ (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    CubeLimit.{u} σ 0 x := by
  intro ι l e s hs hxs hslim
  refine ⟨fun i => cube_volume (e i) (hs i), ?_⟩
  have hr : Tendsto (fun i => 2 * (((n : ℝ) + 1) * s i)) l (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using (hslim.const_mul ((n : ℝ) + 1)).const_mul 2, ?_⟩
    exact Eventually.of_forall (fun i =>
      mul_pos (by norm_num) (mul_pos (by positivity) (hs i)))
  have hu := (hx.comp hr).const_mul (2 ^ n / ((2 * ((n : ℝ) + 1)) ^ n)⁻¹)
  simp only [mul_zero] at hu
  apply squeeze_zero (fun i => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (fun i => cube_ratio_comparison σ (e i) (hs i) (hxs i)) hu

/-- Finite total mass forces the density to be in L1, even when its
representative is only completed-measurable. -/
lemma density_integrable (ν : Measure (Point n)) [IsFiniteMeasure ν]
    (g : Point n → ℝ) (σ : Measure (Point n))
    (h : DensityDecomposition ν σ g) : Integrable g (lebesgue n) := by
  have heq := h.2.2.2 univ MeasurableSet.univ
  rw [Measure.restrict_univ] at heq
  refine ⟨h.1.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal h.2.1).mpr ?_⟩
  exact (le_add_right le_rfl |>.trans_eq heq.symm).trans_lt (measure_lt_top ν univ)

lemma singular_finite (ν : Measure (Point n)) [IsFiniteMeasure ν]
    (g : Point n → ℝ) (σ : Measure (Point n))
    (h : DensityDecomposition ν σ g) : IsFiniteMeasure σ := by
  constructor
  have heq := h.2.2.2 univ MeasurableSet.univ
  exact (le_add_left le_rfl |>.trans_eq heq.symm).trans_lt (measure_lt_top ν univ)

/-- The Borel decomposition evaluated on a cube is a sum of ordinary real
masses. Integrability and finite denominators have been established first. -/
lemma ratio_decomposition (ν : Measure (Point n)) [IsFiniteMeasure ν]
    (g : Point n → ℝ) (σ : Measure (Point n))
    (h : DensityDecomposition ν σ g) (E : Set (Point n))
    (hE : MeasurableSet E) :
    measureRatio ν E = setMean g E + measureRatio σ E := by
  have hi := density_integrable ν g σ h
  have hn : ∀ᵐ x ∂(lebesgue n).restrict E, 0 ≤ g x := ae_restrict_of_ae h.2.1
  have heq := h.2.2.2 E hE
  have hI : (∫⁻ y in E, ENNReal.ofReal (g y) ∂lebesgue n) ≠ ∞ :=
    (hasFiniteIntegral_iff_ofReal hn).mp hi.restrict.2 |>.ne
  have : IsFiniteMeasure σ := singular_finite ν g σ h
  have hreal : (ν E).toReal = (∫ y in E, g y ∂lebesgue n) + (σ E).toReal := by
    change ν E = (∫⁻ y in E, ENNReal.ofReal (g y) ∂lebesgue n) + σ E at heq
    rw [heq, ENNReal.toReal_add hI (measure_ne_top σ E),
      ← integral_eq_lintegral_of_nonneg_ae hn hi.restrict.aestronglyMeasurable]
  change (ν E).toReal / (lebesgue n E).toReal =
    (lebesgue n E).toReal⁻¹ * (∫ y in E, g y ∂lebesgue n) +
      (σ E).toReal / (lebesgue n E).toReal
  rw [hreal]
  ring

/-- The same completed null set works for every shrinking cube family. -/
theorem measure_differentiation :
    Specs.D11.Ch13.MeasureDifferentiation.measure_differentiation.{u} := by
  intro n _ ν _ g σ h
  have hi := density_integrable ν g σ h
  have : IsFiniteMeasure σ := singular_finite ν g σ h
  let hf := D11.Ch13.MaximalWeak11.locallyIntegrable_of_integrable g h.1 hi
  have hgood := (singular_centered_balls σ h.2.2.1).and
    (D11.Ch13.LebesgueDifferentiation.ae_lebesguePoint g hf)
  obtain ⟨N, hsub, hNm, hN0⟩ := @exists_measurable_superset_of_null (Point n) (lebesgueSpace n)
    (lebesgue n) _ (ae_iff.mp hgood)
  refine ⟨hi, N, hNm, hN0, ?_⟩
  intro x hx
  have hxp : Tendsto (fun r => measureRatio σ (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      lebesguePoint g hf x := by
    by_contra hnot
    exact hx (hsub hnot)
  have hσ : CubeLimit.{u} σ 0 x := singular_cubes_of_balls σ hxp.1
  refine ⟨hxp.1, hσ, ?_⟩
  intro ι l e s hs hxs hslim
  have ha := cubes_shrinking g hf x hxp.2 l e s hs hxs hslim
  have hb := hσ l e s hs hxs hslim
  refine ⟨hb.1, ?_⟩
  have hadd := ha.2.2.add hb.2
  simp only [add_zero] at hadd
  apply hadd.congr'
  exact Eventually.of_forall (fun i =>
    (ratio_decomposition ν g σ h _ (closedCube_isClosed (e i) (s i)).measurableSet).symm)

/-- Integration of a Borel density is unchanged by completion, including
restriction to any Borel set. -/
lemma setLIntegral_completed_eq (f : Point n → ℝ≥0∞) (hf : Measurable f)
    (E : Set (Point n)) (hE : MeasurableSet E) :
    (∫⁻ y in E, f y ∂lebesgue n) = ∫⁻ y in E, f y ∂(volume : Measure (Point n)) := by
  calc
    _ = ∫⁻ y, f y ∂((lebesgue n).restrict E).trim (native_borel_le n) :=
      (lintegral_trim (native_borel_le n) hf).symm
    _ = _ := by
      rw [← restrict_trim (native_borel_le n) (lebesgue n) hE]
      have ht : (lebesgue n).trim (native_borel_le n) = (volume : Measure (Point n)) :=
        borel_restriction n (native_borel_le n)
      rw [ht]

/-- Native Borel Lebesgue decomposition supplies a real-valued representative;
its possibly infinite RN values are replaced by zero through `toReal`, and
the RN finiteness theorem proves that this changes nothing almost everywhere. -/
theorem exists_density_decomposition :
    Specs.D11.Ch13.MeasureDifferentiation.exists_density_decomposition := by
  intro n _ ν _
  let m : Measure (Point n) := volume
  let f := ν.rnDeriv m
  let g : Point n → ℝ := fun x => (f x).toReal
  let σ := ν.singularPart m
  have hfm : Measurable f := Measure.measurable_rnDeriv ν m
  have hgm : Measurable g := hfm.ennreal_toReal
  have hfinite : ∀ᵐ x ∂m, f x ≠ ∞ :=
    (Measure.rnDeriv_lt_top ν m).mono (fun _ hx => hx.ne)
  have h : DensityDecomposition ν σ g := by
    refine ⟨hgm.mono (native_borel_le n) le_rfl,
      ae_of_all _ (fun _ => ENNReal.toReal_nonneg),
      Measure.mutuallySingular_singularPart ν m, ?_⟩
    intro E hE
    have heq : ν E = σ E + (m.withDensity f) E := by
      have ht := congrArg (fun ρ : Measure (Point n) => ρ E)
        (Measure.haveLebesgueDecomposition_add ν m)
      simpa only [Measure.add_apply] using ht
    change ν E = (∫⁻ y in E, ENNReal.ofReal (g y) ∂lebesgue n) + σ E
    rw [heq, setLIntegral_completed_eq (fun y => ENNReal.ofReal (g y))
        (by exact ENNReal.measurable_ofReal.comp hgm) E hE,
      withDensity_apply _ hE, add_comm]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae hfinite] with y hy
    exact (ENNReal.ofReal_toReal hy).symm
  exact ⟨g, σ, h, density_integrable ν g σ h⟩

/-- The translation specialization of the shared cube is exactly the
closed axis-parallel cube of center c and full side length s. -/
lemma closedCube_translate (c : Point n) (s : ℝ) :
    closedCube (IsometryEquiv.constVAdd c) s =
      {y : Point n | ∀ j, |y j - c j| ≤ s / 2} := by
  ext y
  change (∃ z : Point n, (∀ j, |z j| ≤ s / 2) ∧ c + z = y) ↔
    ∀ j, |y j - c j| ≤ s / 2
  constructor
  · rintro ⟨z, hz, rfl⟩ j
    simpa using hz j
  · intro hy
    refine ⟨y - c, ?_, by simp⟩
    intro j
    simpa using hy j

/-- An explicit specialization to the source's coordinate cubes. It uses
exactly the same point x, so it preserves the common exceptional set. -/
lemma axis_parallel_cubes {ν : Measure (Point n)} {a : ℝ} {x : Point n}
    (hx : CubeLimit.{u} ν a x) {ι : Type u} (l : Filter ι)
    (c : ι → Point n) (s : ι → ℝ) (hs : ∀ i, 0 < s i)
    (hxs : ∀ i, ∀ j, |x j - c i j| ≤ s i / 2)
    (hslim : Tendsto s l (𝓝 0)) :
    (∀ i, 0 < lebesgue n {y : Point n | ∀ j, |y j - c i j| ≤ s i / 2} ∧
      lebesgue n {y : Point n | ∀ j, |y j - c i j| ≤ s i / 2} < ∞) ∧
    Tendsto (fun i => measureRatio ν {y : Point n | ∀ j, |y j - c i j| ≤ s i / 2})
      l (𝓝 a) := by
  have hm : ∀ i, x ∈ closedCube (IsometryEquiv.constVAdd (c i)) (s i) := by
    intro i
    rw [closedCube_translate]
    exact hxs i
  have h := hx l (fun i => IsometryEquiv.constVAdd (c i)) s hs hm hslim
  simp only [closedCube_translate] at h
  exact h

end D11.Ch13.MeasureDifferentiation
