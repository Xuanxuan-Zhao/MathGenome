import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyGrandAtomic
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyLevelDecomposition
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hardy.AtomicHardySpace
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Order.Filter.AtTopBot.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Interval

set_option autoImplicit false

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ExpandedFA.PartIV.HardyGrandAtomic
open ExpandedFA.Fourier HardyLevel HardyWhitney HardyMaximalSpec
open ExpandedFA.Hardy.AtomicHardySpaceSpec
open ExpandedFA.Hardy.AtomicHardySpace

/-- A uniform radius factor converting the cubical coordinates to Euclidean balls. -/
def ballFactor (d : ℕ) (C : ℝ) : ℝ :=
  C * (‖(HardyLevel.TestEstimates.coordinateEquiv d).symm.toContinuousLinearMap‖ + 1) + 1

lemma ballFactor_pos (d : ℕ) {C : ℝ} (hC : 0 ≤ C) : 0 < ballFactor d C := by
  unfold ballFactor
  positivity

lemma cube_subset_ball {d : ℕ} (Q : DyadicCube d) {C : ℝ} (hC : 0 ≤ C) :
    cubeRegion Q C ⊆ Metric.ball (WithLp.toLp 2 Q.center) (Q.side * ballFactor d C) := by
  intro x hx
  let e := HardyLevel.TestEstimates.coordinateEquiv d
  have hx' : ‖e x - Q.center‖ ≤ C * Q.side / 2 := by
    simpa [cubeRegion, DyadicCube.dilate, Metric.mem_closedBall, dist_eq_norm,
      coordinates, e, HardyLevel.TestEstimates.coordinateEquiv,
      PiLp.coe_continuousLinearEquiv] using hx
  have heq : x - e.symm Q.center = e.symm (e x - Q.center) := by simp
  change dist x (e.symm Q.center) < Q.side * ballFactor d C
  rw [dist_eq_norm, heq]
  have hb := e.symm.toContinuousLinearMap.le_opNorm (e x - Q.center)
  have hb' := mul_le_mul_of_nonneg_left hx' (norm_nonneg e.symm.toContinuousLinearMap)
  have hs := Q.side_pos
  have hn := norm_nonneg e.symm.toContinuousLinearMap
  dsimp [ballFactor]
  change ‖e.symm (e x - Q.center)‖ < _
  change ‖e.symm (e x - Q.center)‖ < Q.side * (C * (‖e.symm.toContinuousLinearMap‖ + 1) + 1)
  have hnC : 0 ≤ C * Q.side := mul_nonneg hC hs.le
  have hnprod : 0 ≤ ‖e.symm.toContinuousLinearMap‖ * C * Q.side := mul_nonneg (mul_nonneg hn hC) hs.le
  calc
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * (C * Q.side / 2) := hb.trans hb'
    _ < _ := by nlinarith

lemma ball_volume {d : ℕ} (Q : DyadicCube d) (R : ℝ) :
    volume.real (Metric.ball (WithLp.toLp 2 Q.center) (Q.side * R)) =
      Q.side ^ d * volume.real (Metric.ball (0 : Euclidean d) R) := by
  simp only [measureReal_def, Measure.addHaar_ball_mul_of_pos volume _ Q.side_pos,
    ENNReal.toReal_mul, finrank_euclideanSpace, Fintype.card_fin,
    ENNReal.toReal_ofReal (pow_nonneg Q.side_nonneg _)]

/-- A bounded, supported, cancelling L¹ function is a positive multiple of a
canonical atom, with no choice of a new Hardy-space model. -/
lemma normalize_piece {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (p : Euclidean d → 𝕜) (hp : Integrable p) (hz : (∫ x, p x) = 0)
    (z : Euclidean d) (r B : ℝ) (hr : 0 < r) (hB : 0 < B)
    (hs : ∀ᵐ x, x ∉ Metric.ball z r → p x = 0)
    (hb : ∀ᵐ x, ‖p x‖ ≤ B) :
    ∃ a : AtomValue (𝕜 := 𝕜) (volume : Measure (Euclidean d)),
      (B * volume.real (Metric.ball z r)) • a.val = hp.toL1 p := by
  let v := volume.real (Metric.ball z r)
  have hv : 0 < v := ENNReal.toReal_pos (Metric.measure_ball_pos volume z hr).ne'
    measure_ball_ne_top
  let t := B * v
  have ht : 0 < t := mul_pos hB hv
  have hnorm : ∀ᵐ x, ‖t⁻¹ • p x‖ ≤ v⁻¹ := by
    filter_upwards [hb] with x hx
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    calc
      _ ≤ t⁻¹ * B := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr ht.le)
      _ = v⁻¹ := by dsimp [t]; field_simp
  obtain ⟨a, ha⟩ := euclidean_atom_realization d (fun x => t⁻¹ • p x)
    (hp.smul t⁻¹).aestronglyMeasurable
    (by rw [integral_smul, hz, smul_zero])
    ⟨z, r, hr, by
      filter_upwards [hs, hnorm] with x hx hn
      exact ⟨fun h => by rw [hx h, smul_zero], hn⟩⟩
  refine ⟨a, ?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul t a.val, ha, hp.coeFn_toL1] with x hx hy hz
  rw [hx]
  change t • a.val x = _
  rw [hy, smul_smul, mul_inv_cancel₀ ht.ne', one_smul, hz]

section Pairing
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}

lemma pairing_integrable (φ : Schwartz 𝕜 d) (f : HardyMaximalSpec.L1 𝕜 d) :
    Integrable (fun x => φ x * f x) :=
  (MeasureTheory.L1.integrable_coeFn f).bdd_mul φ.continuous.aestronglyMeasurable
    (Eventually.of_forall (φ.norm_le_seminorm ℝ))

/-- Evaluation against a Schwartz test is continuous on genuine L¹. -/
def pairing (φ : Schwartz 𝕜 d) : HardyMaximalSpec.L1 𝕜 d →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, φ x * f x
      map_add' := fun f g => by
        calc
          _ = ∫ x, (φ x * f x + φ x * g x) := integral_congr_ae (by
            filter_upwards [Lp.coeFn_add f g] with x hx
            simp only [hx, Pi.add_apply, mul_add])
          _ = _ := integral_add (pairing_integrable φ f) (pairing_integrable φ g)
      map_smul' := fun c f => by
        calc
          _ = ∫ x, c • (φ x * f x) := integral_congr_ae (by
            filter_upwards [Lp.coeFn_smul c f] with x hx
            simp only [hx, Pi.smul_apply, smul_eq_mul, mul_left_comm])
          _ = _ := integral_smul _ _ }
    (SchwartzMap.seminorm ℝ 0 0 φ) (fun f => by
      rw [MeasureTheory.L1.norm_eq_integral_norm]
      apply (norm_integral_le_integral_norm _).trans
      rw [← integral_const_mul]
      apply integral_mono (pairing_integrable φ f).norm
        ((MeasureTheory.L1.integrable_coeFn f).norm.const_mul _)
      intro x
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (φ.norm_le_seminorm ℝ x) (norm_nonneg _))

lemma pairing_toL1 (φ : Schwartz 𝕜 d) (f : Euclidean d → 𝕜) (hf : Integrable f) :
    pairing φ (hf.toL1 f) = ∫ x, φ x * f x := by
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toL1] with x hx
  rw [hx]

/-- Schwartz tests distinguish L¹ functions, for both source scalar fields. -/
lemma eq_of_pairing_eq (f g : HardyMaximalSpec.L1 𝕜 d)
    (h : ∀ φ : Schwartz 𝕜 d, pairing φ f = pairing φ g) : f = g := by
  apply Lp.ext
  apply ae_eq_of_integral_contDiff_smul_eq
    (MeasureTheory.L1.integrable_coeFn f).locallyIntegrable
    (MeasureTheory.L1.integrable_coeFn g).locallyIntegrable
  intro ψ hψ hc
  let φ : Schwartz 𝕜 d :=
    (hc.comp_left (map_zero (RCLike.ofRealCLM (K := 𝕜)))).toSchwartzMap
      ((RCLike.ofRealCLM (K := 𝕜)).contDiff.comp hψ)
  have hh := h φ
  change (∫ x, (ψ x : 𝕜) * f x) = (∫ x, (ψ x : 𝕜) * g x) at hh
  simpa only [RCLike.real_smul_eq_coe_mul] using hh

/-- An absolutely summable family of consecutive differences is identified
by the two limits at opposite ends of the integer levels. -/
lemma identify_level_sum (g : ℤ → HardyMaximalSpec.L1 𝕜 d)
    (f : HardyMaximalSpec.L1 𝕜 d)
    (hs : Summable (fun k => g (k + 1) - g k))
    (hi : Tendsto g atTop (𝓝 f))
    (hlo : ∀ φ : Schwartz 𝕜 d, Tendsto (fun k => pairing φ (g k)) atBot (𝓝 0)) :
    (∑' k, (g (k + 1) - g k)) = f := by
  apply eq_of_pairing_eq
  intro φ
  have ht := ((pairing φ).hasSum hs.hasSum).comp Finset.tendsto_Ico_neg
  have htel (n : ℕ) :
      (∑ k ∈ Finset.Ico (-(n : ℤ)) n, pairing φ (g (k + 1) - g k)) =
        pairing φ (g n) - pairing φ (g (-(n : ℤ))) := by
    simp only [map_sub]
    have hh := Finset.sum_Ico_int_sub n (fun k => pairing φ (g k))
    calc
      _ = -(∑ k ∈ Finset.Ico (-(n : ℤ)) n,
          (pairing φ (g k) - pairing φ (g (k + 1)))) := by
        simp only [Finset.sum_sub_distrib]
        abel
      _ = _ := by rw [hh, neg_sub]
  change Tendsto (fun n : ℕ => ∑ k ∈ Finset.Ico (-(n : ℤ)) n,
    pairing φ (g (k + 1) - g k)) atTop _ at ht
  simp_rw [htel] at ht
  have ht' := ((pairing φ).continuous.tendsto _ |>.comp
    (hi.comp tendsto_natCast_atTop_atTop)).sub
      ((hlo φ).comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop))
  simpa only [sub_zero] using tendsto_nhds_unique ht ht'

end Pairing

lemma bounded_atomic_sequence {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (h : HardyMaximalSpec.Hardy 𝕜 d) {R : ℝ} (hR : 0 ≤ R) (hh : ‖h‖ ≤ R) :
    ∃ (a : ℕ → AtomValue (𝕜 := 𝕜) (volume : Measure (Euclidean d))) (b : ℕ → 𝕜),
      Summable (fun j => ‖b j‖) ∧ (∑' j, ‖b j‖) ≤ 2 * R ∧
      Summable (fun j => ‖b j • (a j).val‖) ∧
      HasSum (fun j => b j • (a j).val) (EmbeddingValue volume h) := by
  have := euclidean_atoms_nonempty d 𝕜
  have hc : ∃ c : CoefficientsValue (𝕜 := 𝕜) (volume : Measure (Euclidean d)),
      SynthesisValue volume c = EmbeddingValue volume h ∧ ‖c‖ ≤ 2 * R := by
    rcases hR.eq_or_lt with he | he
    · have hz : h = 0 := norm_eq_zero.mp (by simpa [← he] using hh)
      refine ⟨0, by simp [hz], ?_⟩
      simp [← he]
    · obtain ⟨c, hc, hn⟩ := Submodule.Quotient.norm_mk_lt h he
      refine ⟨c, congrArg (EmbeddingValue volume) hc, ?_⟩
      linarith
  obtain ⟨c, hc, hn⟩ := hc
  obtain ⟨a, b, hb, hs⟩ := coefficient_sequence volume c
  refine ⟨a, b, hb.summable, hb.tsum_eq ▸ hn, ?_, hc ▸ hs⟩
  apply hb.summable.of_nonneg_of_le (fun j => norm_nonneg _)
  intro j
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (atom_norm_le volume (a j))

/-- Grand-maximal integrability gives the canonical atomic space, with an
absolutely L¹ convergent series and cancellation as a conclusion. -/
theorem grand_atomic : Specs.ExpandedFA.PartIV.HardyGrandAtomic.grandAtomicType := by
  classical
  intro 𝕜 _ d N hd hN
  obtain ⟨c, C, A, M, hc, hC, hA, hM, hlevels⟩ :=
    level_decomposition 𝕜 d N hd hN
  let R := ballFactor d C
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hR : 0 < R := ballFactor_pos d hC0.le
  let D := volume.real (Metric.ball (0 : Euclidean d) R)
  have hD : 0 < D := ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 hR).ne'
    measure_ball_ne_top
  refine ⟨4 * D * C, by positivity, ?_⟩
  intro f hf hG
  obtain ⟨Ω, W, hΩ, hW, hnest, hempty, hg, hgb, hhigh, hlow, hp, hpsum, hcoef⟩ :=
    hlevels f hf hG
  let I := Σ k : ℤ, (W k).cubes
  let p : I → Euclidean d → 𝕜 := fun i => piece f (W i.1) (W (i.1 + 1)) i.2
  have hpi (i : I) : Integrable (p i) := (hp i.1 i.2).1
  let P : I → HardyMaximalSpec.L1 𝕜 d := fun i => (hpi i).toL1 (p i)
  let coeff : I → ℝ := fun i =>
    (C * threshold i.1) * volume.real
      (Metric.ball (WithLp.toLp 2 i.2.val.center) (i.2.val.side * R))
  have hcoeffpos (i : I) : 0 < coeff i := by
    apply mul_pos (mul_pos hC0 (threshold_pos i.1))
    exact ENNReal.toReal_pos
      (Metric.measure_ball_pos volume _ (mul_pos i.2.val.side_pos hR)).ne' measure_ball_ne_top
  have hcoeffeq (i : I) : ENNReal.ofReal (coeff i) =
      ENNReal.ofReal D * (ENNReal.ofReal (C * threshold i.1) *
        volume (cubeRegion i.2.val 1)) := by
    dsimp [coeff]
    rw [ball_volume, cube_volume, DyadicCube.volume_carrier]
    rw [ENNReal.ofReal_mul (mul_nonneg hC0.le (threshold_pos _).le),
      ENNReal.ofReal_mul (pow_nonneg i.2.val.side_nonneg _)]
    dsimp [D]
    ring
  have hcoeffbound : (∑' i : I, ENNReal.ofReal (coeff i)) ≤
      ENNReal.ofReal (2 * D * C) * ∫⁻ x, grand N f x := by
    calc
      _ = ENNReal.ofReal D * ∑' k : ℤ, ∑' Q : (W k).cubes,
          ENNReal.ofReal (C * threshold k) * volume (cubeRegion Q.val 1) := by
        simp_rw [hcoeffeq]
        rw [ENNReal.tsum_mul_left]
        congr 1
        exact ENNReal.tsum_sigma (fun (k : ℤ) (Q : (W k).cubes) =>
          ENNReal.ofReal (C * threshold k) * volume (cubeRegion Q.val 1))
      _ ≤ ENNReal.ofReal D * (2 * ENNReal.ofReal C * ∫⁻ x, grand N f x) :=
        mul_le_mul_right hcoef _
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * D),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
        ring
  have hcoefffin : (∑' i : I, ENNReal.ofReal (coeff i)) ≠ ⊤ :=
    (lt_of_le_of_lt hcoeffbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hG)).ne
  have hcoeffsum : Summable coeff := by
    simpa only [ENNReal.toReal_ofReal (hcoeffpos _).le] using ENNReal.summable_toReal hcoefffin
  have hcoeffreal : (∑' i : I, coeff i) ≤ (2 * D * C) * (∫⁻ x, grand N f x).toReal := by
    have ht := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG.ne) hcoeffbound
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => (hcoeffpos i).le) hcoeffsum,
      ENNReal.toReal_ofReal (tsum_nonneg (fun i => (hcoeffpos i).le)),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * D * C)] at ht
    exact ht
  have hatom (i : I) : ∃ a : AtomValue (𝕜 := 𝕜) (volume : Measure (Euclidean d)),
      coeff i • a.val = P i := by
    apply normalize_piece (p i) (hpi i) (hp i.1 i.2).2.1
      (WithLp.toLp 2 i.2.val.center) (i.2.val.side * R) (C * threshold i.1)
      (mul_pos i.2.val.side_pos hR) (mul_pos hC0 (threshold_pos i.1))
    · filter_upwards [(hp i.1 i.2).2.2.1] with x hx
      exact fun h => hx (fun hx' => h (cube_subset_ball i.2.val hC0.le hx'))
    · exact (hp i.1 i.2).2.2.2
  choose a ha using hatom
  let H : I → HardyMaximalSpec.Hardy 𝕜 d := fun i => coeff i • atomElement volume (a i)
  have hHbound (i : I) : ‖H i‖ ≤ coeff i := by
    dsimp [H]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hcoeffpos i)]
    exact mul_le_of_le_one_right (hcoeffpos i).le (atomElement_norm volume (a i))
  have hHs : Summable (fun i => ‖H i‖) :=
    hcoeffsum.of_nonneg_of_le (fun i => norm_nonneg _) hHbound
  have hHs' : Summable H := hHs.of_norm
  have hHP (i : I) : EmbeddingValue volume (H i) = P i := by
    dsimp [H]
    rw [ContinuousLinearMap.map_smul_of_tower, embedding_atomElement, ha]
  have hPs : Summable P := by
    simpa only [hHP] using hHs'.mapL (EmbeddingValue volume)
  let g : ℤ → HardyMaximalSpec.L1 𝕜 d := fun k => (hg k).toL1 (good f (W k))
  have hlevel (k : ℤ) : (∑' Q : (W k).cubes, P ⟨k, Q⟩) = g (k + 1) - g k := by
    apply Lp.ext
    have hs : (∑' Q : (W k).cubes, ‖P ⟨k, Q⟩‖ₑ) ≠ ⊤ := by
      rw [tsum_enorm_ne_top_iff_summable_norm]
      apply ((hHs.sigma_factor k).of_nonneg_of_le (fun Q => norm_nonneg _))
      intro Q
      rw [← hHP]
      exact (embedding_properties volume).2 _
    filter_upwards [Lp.coeFn_tsum hs, (hpsum k).2,
      ae_all_iff.mpr (fun Q : (W k).cubes => (hpi ⟨k, Q⟩).coeFn_toL1),
      Lp.coeFn_sub (g (k + 1)) (g k), (hg (k + 1)).coeFn_toL1,
      (hg k).coeFn_toL1] with x hx hsum hpx hsub hnext hprev
    rw [hx, hsub]
    change (∑' Q : (W k).cubes, P ⟨k, Q⟩ x) = g (k + 1) x - g k x
    rw [hnext, hprev, ← hsum]
    exact tsum_congr (fun Q => hpx Q)
  have hgs : Summable (fun k => g (k + 1) - g k) := by
    simpa only [hlevel] using hPs.sigma
  have hhigh' : Tendsto g atTop (𝓝 (hf.toL1 f)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    convert hhigh using 1
    funext k
    rw [MeasureTheory.L1.dist_eq_integral_dist]
    apply integral_congr_ae
    filter_upwards [(hg k).coeFn_toL1, hf.coeFn_toL1] with x hx hy
    simp only [g, hx, hy, dist_eq_norm]
  have hlow' (φ : Schwartz 𝕜 d) :
      Tendsto (fun k => pairing φ (g k)) atBot (𝓝 0) := by
    simpa only [g, pairing_toL1] using hlow φ
  let h : HardyMaximalSpec.Hardy 𝕜 d := ∑' i, H i
  have he : EmbeddingValue volume h = hf.toL1 f := by
    calc
      _ = ∑' i, P i := (hHs'.hasSum.mapL (EmbeddingValue volume)).tsum_eq.symm.trans
        (tsum_congr hHP)
      _ = ∑' k, (g (k + 1) - g k) := by rw [hPs.tsum_sigma]; simp only [hlevel]
      _ = _ := identify_level_sum g _ hgs hhigh' hlow'
  have hn : ‖h‖ ≤ (2 * D * C) * (∫⁻ x, grand N f x).toReal :=
    (hHs'.hasSum.norm_le_of_bounded hcoeffsum.hasSum hHbound).trans hcoeffreal
  obtain ⟨as, bs, hbs, hbn, habs, hsum⟩ := bounded_atomic_sequence h (by positivity) hn
  refine ⟨h, he, ?_, ⟨as, bs, hbs, ?_, habs, he ▸ hsum⟩, ?_⟩
  · calc
      ‖h‖ ≤ (2 * D * C) * (∫⁻ x, grand N f x).toReal := hn
      _ ≤ 2 * ((2 * D * C) * (∫⁻ x, grand N f x).toReal) := by
        apply le_mul_of_one_le_left (by positivity) (by norm_num)
      _ = _ := by ring
  · convert hbn using 1; ring
  · calc
      _ = ∫ x, (hf.toL1 f) x := (integral_congr_ae hf.coeFn_toL1).symm
      _ = ∫ x, EmbeddingValue volume h x := by rw [he]
      _ = 0 := integral_zero volume h

end ExpandedFA.PartIV.HardyGrandAtomic
