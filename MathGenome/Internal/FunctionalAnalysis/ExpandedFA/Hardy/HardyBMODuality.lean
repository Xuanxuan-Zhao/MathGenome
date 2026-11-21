import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.HardyBMODuality
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hardy.HardyDualBMORepresentation
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology lp
namespace ExpandedFA.Hardy.HardyBMODuality
open HardyDualBMORepresentationSpec HardyBMODualitySpec
variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
open scoped Classical

/-- The elementary endpoint estimate uses local integrability only. -/
lemma atom_pairing_bound (g : BMOQuotientSpec.BMOFunctionValue d 𝕜) (a : Atom d 𝕜) :
    ‖∫ x, a.val x * g.val x‖ ≤ (bmoENorm g.val).toReal := by
  obtain ⟨c, r, hr, hz, ht, hb⟩ := a.property.2
  let B := Metric.ball c r
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hμ : 0 < volume.real B :=
    ENNReal.toReal_pos hz ht
  have hsub := HardyDualBMORepresentation.integrable_atom_mul
    (fun x => g.val x - ballMean g.val c r) (g.property.1.sub (locallyIntegrable_const _)) a
  have heq : (∫ x, a.val x * g.val x) =
      ∫ x, a.val x * (g.val x - ballMean g.val c r) := by
    rw [show (fun x => a.val x * (g.val x - ballMean g.val c r)) =
      (fun x => a.val x * g.val x - a.val x * ballMean g.val c r) by funext x; ring,
      integral_sub (HardyDualBMORepresentation.integrable_atom_mul g.val g.property.1 a)
        ((L1.integrable_coeFn a.val).mul_const _), integral_mul_const, a.property.1]
    simp
  have hi0 : IntegrableOn (fun x => (volume.real B)⁻¹ *
      ‖g.val x - ballMean g.val c r‖) B volume :=
    ((integrableOn_ball_of_locallyIntegrable g.property.1 c r).sub
      (integrableOn_const ht (C := ballMean g.val c r))).norm.const_mul _
  have hi : Integrable (B.indicator (fun x => (volume.real B)⁻¹ *
      ‖g.val x - ballMean g.val c r‖)) volume :=
    hi0.integrable_indicator hB
  rw [heq]
  calc
    _ ≤ ∫ x, B.indicator (fun x => (volume.real B)⁻¹ *
        ‖g.val x - ballMean g.val c r‖) x := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [hb] with x hx
      by_cases hxB : x ∈ B
      · simp only [Set.indicator_of_mem hxB, norm_mul]
        exact mul_le_mul_of_nonneg_right hx.2 (norm_nonneg _)
      · simp [Set.indicator_of_notMem hxB, hx.1 hxB]
    _ = (volume.real B)⁻¹ * ∫ x in B, ‖g.val x - ballMean g.val c r‖ := by
      rw [integral_indicator hB, integral_const_mul]
    _ ≤ (volume.real B)⁻¹ * (volume.real B * (bmoENorm g.val).toReal) := by
      exact mul_le_mul_of_nonneg_left
        (integral_norm_sub_ballMean_le g.property.1 g.property.2 c hr) (by positivity)
    _ = (bmoENorm g.val).toReal := by field_simp

/-- Atomic values determine a continuous functional on the completed quotient. -/
lemma ext_atoms {L K : H1 d 𝕜 →L[𝕜] 𝕜}
    (h : ∀ a : Atom d 𝕜, L (AtomicHardySpace.atomElement volume a) =
      K (AtomicHardySpace.atomElement volume a)) : L = K := by
  classical
  let Q := (AtomicHardySpaceSpec.KernelValue (𝕜 := 𝕜)
    (volume : Measure (Point d))).mkQL
  have he : L.comp Q = K.comp Q := by
    apply lp.ext_continuousLinearMap (by simp : (1 : ℝ≥0∞) ≠ ∞)
    intro a
    apply ContinuousLinearMap.ext
    intro k
    have hs : lp.single (E := fun _ : Atom d 𝕜 => 𝕜) 1 a k = k • lp.single 1 a (1 : 𝕜) := by
      apply lp.ext
      funext b
      simp only [← lp.single_smul, smul_eq_mul, mul_one]
    change L (Q (lp.single 1 a k)) = K (Q (lp.single 1 a k))
    rw [hs, map_smul, map_smul, map_smul]
    exact congrArg (fun z => k • z) (h a)
  ext x
  obtain ⟨c, rfl⟩ := (AtomicHardySpaceSpec.KernelValue
    (𝕜 := 𝕜) (volume : Measure (Point d))).mkQ_surjective x
  exact congrArg (fun T : _ →L[𝕜] 𝕜 => T c) he

lemma atom_value_of_represents {L : H1 d 𝕜 →L[𝕜] 𝕜} {g : Point d → 𝕜}
    (h : Represents L g) (a : Atom d 𝕜) :
    L (AtomicHardySpace.atomElement volume a) = ∫ x, a.val x * g x := by
  have := (h {a} (fun _ => 1) (AtomicHardySpace.atomElement volume a)
    (by simp [AtomicHardySpace.embedding_atomElement])).2
  simpa only [AtomicHardySpace.embedding_atomElement] using this

lemma represents_unique {L K : H1 d 𝕜 →L[𝕜] 𝕜} {g : Point d → 𝕜}
    (hL : Represents L g) (hK : Represents K g) : L = K :=
  ext_atoms fun a => (atom_value_of_represents hL a).trans (atom_value_of_represents hK a).symm

/-- A uniform bound on atoms is a bound on the dual of the atomic quotient. -/
lemma norm_le_of_atom_bound (L : H1 d 𝕜 →L[𝕜] 𝕜) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ a : Atom d 𝕜, ‖L (AtomicHardySpace.atomElement volume a)‖ ≤ M) :
    ‖L‖ ≤ M := by
  classical
  let Q := (AtomicHardySpaceSpec.KernelValue (𝕜 := 𝕜)
    (volume : Measure (Point d))).mkQL
  have hc (c : AtomicHardySpaceSpec.CoefficientsValue (𝕜 := 𝕜)
      (volume : Measure (Point d))) : ‖L (Q c)‖ ≤ M * ‖c‖ := by
    have hs := ((L.comp Q).hasSum
      (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ∞) c))
    have hcs : HasSum (fun a : Atom d 𝕜 => M * ‖c a‖) (M * ‖c‖) := by
      rw [AtomicHardySpace.coefficient_norm volume c]
      simpa using ((lp.memℓp c).summable (by simp)).hasSum.mul_left M
    apply hs.norm_le_of_bounded hcs
    intro a
    have he : lp.single (E := fun _ : Atom d 𝕜 => 𝕜) 1 a (c a) =
        c a • lp.single 1 a (1 : 𝕜) := by
      apply lp.ext
      funext b
      simp only [← lp.single_smul, smul_eq_mul, mul_one]
    change ‖L (Q (lp.single 1 a (c a)))‖ ≤ _
    rw [he, map_smul, map_smul, norm_smul, mul_comm M]
    exact mul_le_mul_of_nonneg_left (h a) (norm_nonneg _)
  apply L.opNorm_le_bound hM
  intro x
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨c, hcx, hcn⟩ := Submodule.Quotient.norm_mk_lt x
    (div_pos hε (by linarith : 0 < M + 1))
  have he : Q c = x := hcx
  calc
    ‖L x‖ = ‖L (Q c)‖ := by rw [he]
    _ ≤ M * ‖c‖ := hc c
    _ ≤ M * (‖x‖ + ε / (M + 1)) := mul_le_mul_of_nonneg_left hcn.le hM
    _ ≤ M * ‖x‖ + ε := by
      have hh : M * (ε / (M + 1)) ≤ ε := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by linarith : 0 < M + 1)).mpr
        nlinarith
      nlinarith

/-- For a bounded measurable function the pairing is an ordinary L¹ integral. -/
def boundedPairing (g : Point d → 𝕜) (hg : AEStronglyMeasurable g volume)
    (R : ℝ) (hR : ∀ᵐ x ∂volume, ‖g x‖ ≤ R) : H1 d 𝕜 →L[𝕜] 𝕜 := by
  let T : L1 d 𝕜 →ₗ[𝕜] 𝕜 := {
    toFun f := ∫ x, f x * g x
    map_add' f h := by
      have he : (fun x => (f + h) x * g x) =ᵐ[volume]
          (fun x => f x * g x + h x * g x) :=
        (Lp.coeFn_add f h).mono fun x hx => by simp only [hx, Pi.add_apply, add_mul]
      rw [integral_congr_ae he, integral_add
        ((L1.integrable_coeFn f).mul_bdd hg hR)
        ((L1.integrable_coeFn h).mul_bdd hg hR)]
    map_smul' k f := by
      have he : (fun x => (k • f) x * g x) =ᵐ[volume]
          (fun x => k * (f x * g x)) :=
        (Lp.coeFn_smul k f).mono fun x hx => by simp [hx, smul_eq_mul, mul_assoc]
      simp only [RingHom.id_apply, smul_eq_mul]
      rw [integral_congr_ae he, integral_const_mul] }
  have hb (f : L1 d 𝕜) : ‖T f‖ ≤ R * ‖f‖ := by
    change ‖∫ x, f x * g x‖ ≤ _
    rw [L1.norm_eq_integral_norm, ← integral_const_mul]
    apply norm_integral_le_of_norm_le ((L1.integrable_coeFn f).norm.const_mul R)
    filter_upwards [hR] with x hx
    rw [norm_mul, mul_comm R]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
  exact (T.mkContinuous R hb).comp (AtomicHardySpaceSpec.EmbeddingValue volume)

lemma boundedPairing_atom (g : Point d → 𝕜) (hg : AEStronglyMeasurable g volume)
    (R : ℝ) (hR : ∀ᵐ x ∂volume, ‖g x‖ ≤ R) (a : Atom d 𝕜) :
    boundedPairing g hg R hR (AtomicHardySpace.atomElement volume a) =
      ∫ x, a.val x * g x := by
  change (∫ x, AtomicHardySpaceSpec.EmbeddingValue volume
    (AtomicHardySpace.atomElement volume a) x * g x) = _
  rw [AtomicHardySpace.embedding_atomElement]

/-- Clipping real coordinates also works uniformly for the real and complex fields. -/
def clipReal (n : ℕ) (t : ℝ) : ℝ := max (-(n : ℝ)) (min n t)

lemma clipReal_lipschitz (n : ℕ) : LipschitzWith 1 (clipReal n) :=
  (LipschitzWith.id.const_min (n : ℝ)).const_max (-(n : ℝ))

lemma clipReal_zero (n : ℕ) : clipReal n 0 = 0 := by
  simp [clipReal]

lemma clipReal_abs_le (n : ℕ) (t : ℝ) : |clipReal n t| ≤ n := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_left _ _)⟩

lemma clipReal_eq (n : ℕ) (t : ℝ) (h : |t| ≤ n) : clipReal n t = t := by
  rcases abs_le.mp h with ⟨h₁, h₂⟩
  simp only [clipReal, min_eq_right h₂, max_eq_right h₁]

def clip (n : ℕ) (z : 𝕜) : 𝕜 :=
  (clipReal n (RCLike.re z) : 𝕜) + (clipReal n (RCLike.im z) : 𝕜) * RCLike.I

lemma clip_zero (n : ℕ) : clip n (0 : 𝕜) = 0 := by simp [clip, clipReal_zero]

lemma clip_bound (n : ℕ) (z : 𝕜) : ‖clip n z‖ ≤ 2 * n := by
  calc
    _ ≤ ‖(clipReal n (RCLike.re z) : 𝕜)‖ +
      ‖(clipReal n (RCLike.im z) : 𝕜) * RCLike.I‖ := norm_add_le _ _
    _ ≤ |clipReal n (RCLike.re z)| + |clipReal n (RCLike.im z)| := by
      simp only [norm_mul, RCLike.norm_ofReal]
      gcongr
      rw [RCLike.norm_I]; split_ifs <;> norm_num
    _ ≤ (n : ℝ) + n := add_le_add (clipReal_abs_le _ _) (clipReal_abs_le _ _)
    _ = _ := by ring

lemma clip_sub_bound (n : ℕ) (z w : 𝕜) : ‖clip n z - clip n w‖ ≤ 2 * ‖z - w‖ := by
  have hre := (clipReal_lipschitz n).dist_le_mul (RCLike.re z) (RCLike.re w)
  have him := (clipReal_lipschitz n).dist_le_mul (RCLike.im z) (RCLike.im w)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hre him
  calc
    _ = ‖((clipReal n (RCLike.re z) - clipReal n (RCLike.re w) : ℝ) : 𝕜) +
        ((clipReal n (RCLike.im z) - clipReal n (RCLike.im w) : ℝ) : 𝕜) * RCLike.I‖ := by
      congr 1
      simp only [clip, map_sub]
      ring
    _ ≤ |clipReal n (RCLike.re z) - clipReal n (RCLike.re w)| +
        |clipReal n (RCLike.im z) - clipReal n (RCLike.im w)| := by
      apply (norm_add_le _ _).trans
      simp only [norm_mul, RCLike.norm_ofReal]
      gcongr
      rw [RCLike.norm_I]; split_ifs <;> norm_num
    _ ≤ |RCLike.re (z - w)| + |RCLike.im (z - w)| := by
      simpa using add_le_add hre him
    _ ≤ ‖z - w‖ + ‖z - w‖ := add_le_add (RCLike.abs_re_le_norm _) (RCLike.abs_im_le_norm _)
    _ = _ := by ring

lemma clip_lipschitz (n : ℕ) : LipschitzWith 2 (clip (𝕜 := 𝕜) n) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [dist_eq_norm, NNReal.coe_ofNat] using clip_sub_bound n z w

lemma clip_eventually_eq (z : 𝕜) : ∀ᶠ n : ℕ in atTop, clip n z = z := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
  filter_upwards [eventually_ge_atTop N] with n hn
  have hzn : ‖z‖ ≤ n := hN.trans (by exact_mod_cast hn)
  simp only [clip, clipReal_eq n _ ((RCLike.abs_re_le_norm z).trans hzn),
    clipReal_eq n _ ((RCLike.abs_im_le_norm z).trans hzn), RCLike.re_add_im]

lemma clip_locallyIntegrable (g : Point d → 𝕜) (hg : LocallyIntegrable g volume) (n : ℕ) :
    LocallyIntegrable (fun x => clip n (g x)) volume := by
  apply locallyIntegrable_of_ae_bound
    ((clip_lipschitz n).continuous.comp_aestronglyMeasurable hg.aestronglyMeasurable)
  exact Eventually.of_forall fun x => clip_bound n (g x)

lemma clip_bmo_bound (g : BMOQuotientSpec.BMOFunctionValue d 𝕜) (n : ℕ) :
    bmoENorm (fun x => clip n (g.val x)) ≤ ENNReal.ofReal (4 * (bmoENorm g.val).toReal) := by
  let f : Point d → 𝕜 := fun x => clip n (g.val x)
  have hf : LocallyIntegrable f volume := clip_locallyIntegrable g.val g.property.1 n
  change (⨆ c, ⨆ r : ℝ, ⨆ (_ : 0 < r), BMOQuotientSpec.MeanOscillationValue f c r) ≤ _
  refine iSup_le fun c => iSup_le fun r => iSup_le fun hr => ?_
  apply (meanOscillation_le_twice_integral hf (clip n (ballMean g.val c r)) c hr).trans
  apply ENNReal.ofReal_le_ofReal
  have hμ : 0 < volume.real (Metric.ball c r) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume c hr).ne' measure_ball_lt_top.ne
  have hi : IntegrableOn (fun x => ‖g.val x - ballMean g.val c r‖) (Metric.ball c r) volume :=
    ((integrableOn_ball_of_locallyIntegrable g.property.1 c r).sub
      (integrableOn_const (C := ballMean g.val c r) measure_ball_ne_top)).norm
  have hif : IntegrableOn (fun x => ‖f x - clip n (ballMean g.val c r)‖)
      (Metric.ball c r) volume :=
    ((integrableOn_ball_of_locallyIntegrable hf c r).sub
      (integrableOn_const (C := clip n (ballMean g.val c r)) measure_ball_ne_top)).norm
  have hbound : (∫ x in Metric.ball c r, ‖f x - clip n (ballMean g.val c r)‖) ≤
      2 * (volume.real (Metric.ball c r) * (bmoENorm g.val).toReal) := by
    calc
      _ ≤ ∫ x in Metric.ball c r, 2 * ‖g.val x - ballMean g.val c r‖ :=
        integral_mono hif (hi.const_mul 2) (fun x => clip_sub_bound n _ _)
      _ = 2 * ∫ x in Metric.ball c r, ‖g.val x - ballMean g.val c r‖ := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (integral_norm_sub_ballMean_le g.property.1 g.property.2 c hr) (by norm_num)
  calc
    _ ≤ 2 * ((volume.real (Metric.ball c r))⁻¹ *
        (2 * (volume.real (Metric.ball c r) * (bmoENorm g.val).toReal))) := by gcongr
    _ = 4 * (bmoENorm g.val).toReal := by field_simp; ring

/-- Truncation converges under each atom's integral, by an integrable dominator. -/
lemma clip_atom_tendsto (g : Point d → 𝕜) (hg : LocallyIntegrable g volume)
    (a : Atom d 𝕜) :
    Tendsto (fun n => ∫ x, a.val x * clip n (g x)) atTop (𝓝 (∫ x, a.val x * g x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => 2 * ‖a.val x * g x‖)
  · intro n
    exact (Lp.aestronglyMeasurable a.val).mul
      ((clip_lipschitz n).continuous.comp_aestronglyMeasurable hg.aestronglyMeasurable)
  · exact (HardyDualBMORepresentation.integrable_atom_mul g hg a).norm.const_mul 2
  · intro n
    filter_upwards with x
    have hb : ‖clip n (g x)‖ ≤ 2 * ‖g x‖ := by
      simpa only [clip_zero, sub_zero] using clip_sub_bound n (g x) 0
    simp only [norm_mul]
    nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (a.val x))]
  · filter_upwards with x
    exact tendsto_const_nhds.congr' ((clip_eventually_eq (g x)).mono fun n hn => by simp only [hn])

/-- Finite atom sums are a dense linear image in the source's completed space. -/
def finiteSynthesis : (Atom d 𝕜 →₀ 𝕜) →ₗ[𝕜] H1 d 𝕜 :=
  Finsupp.linearCombination 𝕜 (AtomicHardySpace.atomElement volume)

lemma quotient_single (a : Atom d 𝕜) (k : 𝕜) :
    (AtomicHardySpaceSpec.KernelValue (𝕜 := 𝕜) (volume : Measure (Point d))).mkQL
      (lp.single 1 a k) = k • AtomicHardySpace.atomElement volume a := by
  classical
  have he : lp.single (E := fun _ : Atom d 𝕜 => 𝕜) 1 a k =
      k • lp.single 1 a (1 : 𝕜) := by
    apply lp.ext
    funext b
    simp only [← lp.single_smul, smul_eq_mul, mul_one]
  rw [he, map_smul]
  rfl

lemma finiteSynthesis_dense : DenseRange (finiteSynthesis (d := d) (𝕜 := 𝕜)) := by
  classical
  intro x
  let Q := (AtomicHardySpaceSpec.KernelValue (𝕜 := 𝕜)
    (volume : Measure (Point d))).mkQL
  obtain ⟨c, rfl⟩ := (AtomicHardySpaceSpec.KernelValue
    (𝕜 := 𝕜) (volume : Measure (Point d))).mkQ_surjective x
  have hs : HasSum (fun a : Atom d 𝕜 => c a • AtomicHardySpace.atomElement volume a)
      (Q c) := by
    simpa only [Q, quotient_single] using Q.hasSum
      (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ∞) c)
  apply mem_closure_of_tendsto hs
  apply Eventually.of_forall
  intro s
  refine ⟨∑ a ∈ s, Finsupp.single a (c a), ?_⟩
  simp only [map_sum, finiteSynthesis, Finsupp.linearCombination_single]

/-- Algebraic integration on the free space of finite atom sums. -/
def finitePairing (g : Point d → 𝕜) : (Atom d 𝕜 →₀ 𝕜) →ₗ[𝕜] 𝕜 :=
  Finsupp.linearCombination 𝕜 (fun a => ∫ x, a.val x * g x)

lemma boundedPairing_finite (g : Point d → 𝕜) (hg : AEStronglyMeasurable g volume)
    (R : ℝ) (hR : ∀ᵐ x ∂volume, ‖g x‖ ≤ R) (c : Atom d 𝕜 →₀ 𝕜) :
    boundedPairing g hg R hR (finiteSynthesis c) = finitePairing g c := by
  simp only [finiteSynthesis, finitePairing, Finsupp.linearCombination_apply,
    Finsupp.sum, map_sum, map_smul, boundedPairing_atom]

lemma finitePairing_clip_tendsto (g : Point d → 𝕜) (hg : LocallyIntegrable g volume)
    (c : Atom d 𝕜 →₀ 𝕜) :
    Tendsto (fun n => finitePairing (fun x => clip n (g x)) c) atTop
      (𝓝 (finitePairing g c)) := by
  simp only [finitePairing, Finsupp.linearCombination_apply, Finsupp.sum]
  apply tendsto_finsetSum
  intro a _
  exact (clip_atom_tendsto g hg a).const_smul (c a)

lemma finitePairing_bound (g : BMOQuotientSpec.BMOFunctionValue d 𝕜)
    (c : Atom d 𝕜 →₀ 𝕜) :
    ‖finitePairing g.val c‖ ≤ 4 * (bmoENorm g.val).toReal * ‖finiteSynthesis c‖ := by
  have hb (n : ℕ) : ‖finitePairing (fun x => clip n (g.val x)) c‖ ≤
      4 * (bmoENorm g.val).toReal * ‖finiteSynthesis c‖ := by
    let gn : BMOQuotientSpec.BMOFunctionValue d 𝕜 :=
      ⟨fun x => clip n (g.val x), clip_locallyIntegrable g.val g.property.1 n,
        (clip_bmo_bound g n).trans_lt ENNReal.ofReal_lt_top⟩
    have hn : (bmoENorm gn.val).toReal ≤ 4 * (bmoENorm g.val).toReal :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (clip_bmo_bound g n)
    let L := boundedPairing gn.val
      ((clip_lipschitz n).continuous.comp_aestronglyMeasurable g.property.1.aestronglyMeasurable)
      (2 * n) (Eventually.of_forall fun x => clip_bound n (g.val x))
    have hL : ‖L‖ ≤ 4 * (bmoENorm g.val).toReal :=
      (norm_le_of_atom_bound L (by positivity) (fun a => by
        rw [boundedPairing_atom]
        exact atom_pairing_bound gn a)).trans hn
    rw [← boundedPairing_finite gn.val
      ((clip_lipschitz n).continuous.comp_aestronglyMeasurable g.property.1.aestronglyMeasurable)
      (2 * n) (Eventually.of_forall fun x => clip_bound n (g.val x)) c]
    exact L.le_of_opNorm_le hL _
  exact le_of_tendsto (finitePairing_clip_tendsto g.val g.property.1 c).norm
    (Eventually.of_forall hb)

/-- The pairing on H¹ is the continuous extension of integration on finite sums. -/
def bmoFunctional (g : BMOQuotientSpec.BMOFunctionValue d 𝕜) : H1 d 𝕜 →L[𝕜] 𝕜 :=
  (finitePairing g.val).extendOfNorm finiteSynthesis

lemma bmoFunctional_atom (g : BMOQuotientSpec.BMOFunctionValue d 𝕜) (a : Atom d 𝕜) :
    bmoFunctional g (AtomicHardySpace.atomElement volume a) = ∫ x, a.val x * g.val x := by
  have h := LinearMap.extendOfNorm_eq (f := finitePairing g.val)
    finiteSynthesis_dense ⟨4 * (bmoENorm g.val).toReal, finitePairing_bound g⟩
    (Finsupp.single a (1 : 𝕜))
  simpa only [finiteSynthesis, finitePairing, Finsupp.linearCombination_single, one_smul,
    bmoFunctional] using h

lemma bmoFunctional_represents (g : BMOQuotientSpec.BMOFunctionValue d 𝕜) :
    Represents (bmoFunctional g) g.val :=
  HardyDualBMORepresentation.represents_of_atom_pairings _ _ g.property.1 (bmoFunctional_atom g)

set_option maxHeartbeats 800000 in
lemma bmoFunctional_norm (g : BMOQuotientSpec.BMOFunctionValue d 𝕜) :
    ‖bmoFunctional g‖ ≤ 4 * (bmoENorm g.val).toReal :=
  LinearMap.opNorm_extendOfNorm_le (f := finitePairing g.val)
    (e := finiteSynthesis (d := d) (𝕜 := 𝕜)) finiteSynthesis_dense
    (by positivity) (finitePairing_bound g)

theorem bmo_extension : BMOExtension := by
  intro d 𝕜 _ g
  exact ⟨bmoFunctional g, bmoFunctional_represents g, bmoFunctional_norm g,
    fun L hL => represents_unique hL (bmoFunctional_represents g)⟩

lemma represents_of_modConstants {L : H1 d 𝕜 →L[𝕜] 𝕜}
    {g g' : BMOQuotientSpec.BMOFunctionValue d 𝕜} (hL : Represents L g.val)
    (h : BMOQuotientSpec.ModConstantsValue g' g) : Represents L g'.val := by
  obtain ⟨k, hk⟩ := h
  apply HardyDualBMORepresentation.represents_of_atom_pairings L g'.val g'.property.1
  intro a
  rw [atom_value_of_represents hL a]
  have he : (fun x => a.val x * g'.val x) =ᵐ[volume]
      (fun x => a.val x * g.val x + a.val x * k) := by
    filter_upwards [hk] with x hx
    simp only [hx, mul_add]
  rw [integral_congr_ae he, integral_add
    (HardyDualBMORepresentation.integrable_atom_mul g.val g.property.1 a)
    ((L1.integrable_coeFn a.val).mul_const k), integral_mul_const, a.property.1]
  simp

lemma modConstants_of_represents {L : H1 d 𝕜 →L[𝕜] 𝕜}
    {g g' : BMOQuotientSpec.BMOFunctionValue d 𝕜}
    (h : Represents L g.val) (h' : Represents L g'.val) :
    BMOQuotientSpec.ModConstantsValue g' g := by
  apply HardyDualBMORepresentation.atom_separation d 𝕜 g.val g'.val g.property.1 g'.property.1
  intro a
  exact (atom_value_of_represents h a).symm.trans (atom_value_of_represents h' a)

/-- Full real/complex Hardy–BMO duality, with dimension-only norm constants,
a.e. uniqueness modulo constants, and pairing on the actual completed H¹. -/
theorem hardy_bmo_duality : Duality := by
  refine ⟨bmo_extension, ?_⟩
  intro d
  obtain ⟨C, hC, hrep⟩ := HardyDualBMORepresentation.representation d
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _
  refine ⟨fun L => ?_, ?_⟩
  · obtain ⟨g, hg, _, _⟩ := hrep 𝕜 L
    exact ⟨g, hg⟩
  · intro g L hg
    have hLn : ‖L‖ ≤ 4 * (bmoENorm g.val).toReal := by
      rw [represents_unique hg (bmoFunctional_represents g)]
      exact bmoFunctional_norm g
    obtain ⟨g₀, hg₀, hnorm₀, _⟩ := hrep 𝕜 L
    have heq : bmoENorm g.val = bmoENorm g₀.val :=
      bmoENorm_eq_of_modConstants (modConstants_of_represents hg₀ hg)
    have hgn : (bmoENorm g.val).toReal ≤ C * ‖L‖ := by
      rw [heq]
      exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC.le (norm_nonneg L)) hnorm₀
    exact ⟨hLn, hgn, fun g' =>
      ⟨fun hg' => modConstants_of_represents hg hg', represents_of_modConstants hg⟩⟩

end ExpandedFA.Hardy.HardyBMODuality
