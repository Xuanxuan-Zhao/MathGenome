import MathGenome.Internal.FourierSobolev.Specs.P102.U4.GraphAreaPieces
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace P102.U4.GraphPieces

@[simp] theorem affineGraph_apply {m : ℕ} (a x : Space m) :
    affineGraph a x = WithLp.toLp 2 (x, inner ℝ a x) := rfl

theorem ambient_finrank (m : ℕ) : Module.finrank ℝ (Ambient m) = m + 1 := by
  rw [(WithLp.linearEquiv 2 ℝ (Space m × ℝ)).finrank_eq]
  simp [Space, Module.finrank_prod]

def ambientCoordinates (m : ℕ) : Ambient m ≃ₗᵢ[ℝ] Space (m + 1) :=
  (stdOrthonormalBasis ℝ (Ambient m)).repr.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (ambient_finrank m)))

theorem ambient_coordinates : Expected.AmbientCoordinates :=
  fun m => ⟨ambientCoordinates m⟩

theorem normalized_isometry_image {m n : ℕ} (i : Space m → Space n)
    (hi : Isometry i) (S : Set (Space m)) :
    (μHE[m] : Measure (Space n)) (i '' S) = volume S := by
  rw [hi.euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]

theorem normalized_lipschitz_image_le
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {K : ℝ≥0} {f : X → Y} {S : Set X} (hf : LipschitzOnWith K f S) (m : ℕ) :
    (μHE[m] : Measure Y) (f '' S) ≤ (K : ℝ≥0∞) ^ m * (μHE[m] : Measure X) S := by
  simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply,
    ENNReal.smul_def, smul_eq_mul]
  have h := hf.hausdorffMeasure_image_le (d := (m : ℝ)) (by positivity)
  rw [ENNReal.rpow_natCast] at h
  calc
    _ ≤ _ := mul_le_mul_right h _
    _ = _ := by ac_rfl

theorem lipschitz_distortion : Expected.LipschitzDistortion := by
  intro m K f S hf
  exact normalized_lipschitz_image_le hf m

theorem affineGraph_normDet_sq {m : ℕ} (a : Space m) :
    (affineGraph a).normDet ^ 2 = 1 + ‖a‖ ^ 2 := by
  have h := (affineGraph a).normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin m) ℝ)
  have hgram : Matrix.gram ℝ (fun i => affineGraph a (EuclideanSpace.basisFun (Fin m) ℝ i)) =
      1 + Matrix.replicateCol Unit (fun i => a i) * Matrix.replicateRow Unit (fun i => a i) := by
    ext i j
    simp [Matrix.gram, WithLp.prod_inner_apply, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_right,
      Matrix.mul_apply, Matrix.one_apply, mul_comm, eq_comm]
  rw [hgram, Matrix.det_one_add_replicateCol_mul_replicateRow] at h
  rw [EuclideanSpace.norm_sq_eq]
  simpa [dotProduct, Real.norm_eq_abs, sq_abs, pow_two] using h

theorem affineGraph_normDet {m : ℕ} (a : Space m) :
    (affineGraph a).normDet = jacobian a := by
  rw [jacobian, ← affineGraph_normDet_sq a, Real.sqrt_sq (affineGraph a).normDet_nonneg]

theorem affine_jacobian : Expected.AffineJacobian := by
  intro m a S
  have h := (affineGraph a).euclideanHausdorffMeasure_image_eq_normDet_mul_volume S
  simpa [Space, affineGraph_normDet] using h

theorem normalized_zero_eq_count
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] :
    (μHE[0] : Measure X) = Measure.count := by
  classical
  rw [Measure.euclideanHausdorffMeasure_zero]
  have hf (t : Finset X) : (μH[0] : Measure X) t = t.card := by
    rw [← sum_measure_singleton]
    simp
  ext S hS
  by_cases hfin : S.Finite
  · rw [← hfin.coe_toFinset, hf, Measure.count_apply_finset]
  · rw [Measure.count_apply_infinite hfin]
    apply top_unique
    rw [← ENNReal.iSup_natCast]
    apply iSup_le
    intro n
    obtain ⟨t, ht, hcard⟩ := Set.Infinite.exists_subset_card_eq hfin n
    rw [← hcard, ← hf]
    exact measure_mono ht

theorem normalization : Expected.Normalization :=
  ⟨fun _ _ i hi S => normalized_isometry_image i hi S, fun _ => normalized_zero_eq_count⟩

theorem image_measurability : Expected.ImageMeasurability := by
  classical
  intro m U γ hγ S hS hSU
  let g : Space m → ℝ := (U : Set (Space m)).piecewise γ (fun _ => 0)
  have hg : Measurable g :=
    hγ.measurable_piecewise continuousOn_const U.isOpen.measurableSet
  have hB : MeasurableSet {p : Space m × ℝ | p.1 ∈ S ∧ p.2 = g p.1} :=
    (hS.preimage measurable_fst).inter (measurableSet_graph hg)
  have heq : graph γ '' S =
      (WithLp.ofLp : Ambient m → Space m × ℝ) ⁻¹'
        {p : Space m × ℝ | p.1 ∈ S ∧ p.2 = g p.1} := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, by simp [g, hSU hx, graph]⟩
    · rintro ⟨hp, heq⟩
      refine ⟨p.ofLp.1, hp, ?_⟩
      apply (WithLp.equiv 2 (Space m × ℝ)).injective
      simp only [graph, WithLp.equiv_apply]
      exact Prod.ext rfl (by simpa only [g, Set.piecewise, ite_eq_left (hSU hp)] using heq.symm)
  rw [heq]
  exact hB.preimage (WithLp.homeomorphProd 2 (Space m) ℝ).continuous.measurable

/-- The Borel gradient required in the partition theorem is available under the
original Lipschitz hypothesis. Riesz representation converts the scalar Fréchet
derivative to a vector in the shared Euclidean coordinate model. -/
theorem gradient_existence : Expected.GradientExistence := by
  intro m hm U γ L hL
  let a : Space m → Space m :=
    fun x => (InnerProductSpace.toDual ℝ (Space m)).symm (fderiv ℝ γ x)
  have ha : Measurable a :=
    (InnerProductSpace.toDual ℝ (Space m)).symm.continuous.measurable.comp (measurable_fderiv ℝ γ)
  refine ⟨a, ha, ?_⟩
  filter_upwards [hL.ae_differentiableWithinAt U.isOpen.measurableSet,
    ae_restrict_mem U.isOpen.measurableSet] with x hx hxU
  have hd := (hx.differentiableAt (U.isOpen.mem_nhds hxU)).hasFDerivAt
  have heq : innerSL ℝ (a x) = fderiv ℝ γ x := by
    ext v
    exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := v) (y := fderiv ℝ γ x)
  rwa [heq]

theorem jacobian_eq_norm {m : ℕ} (a : Space m) :
    jacobian a = ‖(WithLp.toLp 2 (a, (1 : ℝ)) : Ambient m)‖ := by
  simp [jacobian, WithLp.prod_norm_eq_of_L2, add_comm]

theorem one_le_jacobian {m : ℕ} (a : Space m) : 1 ≤ jacobian a := by
  rw [jacobian_eq_norm]
  simpa using (WithLp.norm_snd_le (p := 2) (Space m) (WithLp.toLp 2 (a, (1 : ℝ))))

theorem abs_jacobian_sub_le {m : ℕ} (a b : Space m) :
    |jacobian a - jacobian b| ≤ ‖a - b‖ := by
  rw [jacobian_eq_norm, jacobian_eq_norm]
  have h := abs_norm_sub_norm_le
    (WithLp.toLp 2 (a, (1 : ℝ)) : Ambient m) (WithLp.toLp 2 (b, (1 : ℝ)))
  simpa [← WithLp.toLp_sub, WithLp.norm_toLp_fst] using h

theorem jacobian_comparison {m : ℕ} {a b : Space m} {ε : ℝ}
    (hε : 0 ≤ ε) (hab : ‖a - b‖ < ε / 2) :
    (1 - ε) * jacobian a ≤ jacobian b ∧
      jacobian b ≤ (1 + ε) * jacobian a := by
  have h := abs_le.mp ((abs_jacobian_sub_le a b).trans hab.le)
  have hj := one_le_jacobian a
  have hmul : ε ≤ ε * jacobian a := by nlinarith
  constructor <;> nlinarith

theorem base_norm_le_affineGraph {m : ℕ} (b v : Space m) :
    ‖v‖ ≤ ‖affineGraph b v‖ := by
  simpa using (WithLp.norm_fst_le (p := 2) (Space m) (affineGraph b v))

theorem graph_increment_error {m : ℕ} (γ : Space m → ℝ) (b x y : Space m) :
    ‖graph γ y - graph γ x - affineGraph b (y - x)‖ =
      |γ y - γ x - inner ℝ b (y - x)| := by
  change ‖(WithLp.toLp 2 (y, γ y) - WithLp.toLp 2 (x, γ x) -
    WithLp.toLp 2 (y - x, inner ℝ b (y - x)) : Ambient m)‖ = _
  simp [← WithLp.toLp_sub, WithLp.norm_toLp_snd, Real.norm_eq_abs]

/-- The exact two-sided length estimate used in the diameter-cover argument. -/
theorem graph_increment_comparison {m : ℕ} (γ : Space m → ℝ) (b x y : Space m)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : |γ y - γ x - inner ℝ b (y - x)| ≤ ε * ‖y - x‖) :
    (1 - ε) * ‖affineGraph b (y - x)‖ ≤ ‖graph γ y - graph γ x‖ ∧
      ‖graph γ y - graph γ x‖ ≤ (1 + ε) * ‖affineGraph b (y - x)‖ := by
  have he : ‖graph γ y - graph γ x - affineGraph b (y - x)‖ ≤
      ε * ‖affineGraph b (y - x)‖ := by
    rw [graph_increment_error]
    exact h.trans (mul_le_mul_of_nonneg_left (base_norm_le_affineGraph b (y - x)) hε)
  have hh := abs_le.mp ((abs_norm_sub_norm_le
    (graph γ y - graph γ x) (affineGraph b (y - x))).trans he)
  constructor <;> nlinarith

/-- Hausdorff comparison with the affine graph, before comparing Jacobians. -/
theorem graph_measure_comparison {m : ℕ} (γ : Space m → ℝ) (b : Space m)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) {S : Set (Space m)}
    (herr : ∀ x ∈ S, ∀ y ∈ S,
      |γ y - γ x - inner ℝ b (y - x)| ≤ ε * ‖y - x‖) :
    ENNReal.ofReal ((1 - ε) ^ m) *
        (ENNReal.ofReal (jacobian b) * volume S) ≤
      (μHE[m] : Measure (Ambient m)) (graph γ '' S) ∧
    (μHE[m] : Measure (Ambient m)) (graph γ '' S) ≤
      ENNReal.ofReal ((1 + ε) ^ m) *
        (ENNReal.ofReal (jacobian b) * volume S) := by
  have hδ : 0 < 1 - ε := sub_pos.mpr hε1
  let K : ℝ≥0 := ⟨1 + ε, by positivity⟩
  let K' : ℝ≥0 := ⟨(1 - ε)⁻¹, inv_nonneg.mpr hδ.le⟩
  let f : Ambient m → Ambient m := fun z => graph γ z.ofLp.1
  let g : Ambient m → Ambient m := fun z => affineGraph b z.ofLp.1
  have hf : LipschitzOnWith K f (affineGraph b '' S) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    change ‖graph γ x - graph γ y‖ ≤ (1 + ε) * ‖affineGraph b x - affineGraph b y‖
    rw [← map_sub]
    exact (graph_increment_comparison γ b y x hε (herr y hy x hx)).2
  have hg : LipschitzOnWith K' g (graph γ '' S) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    change ‖affineGraph b x - affineGraph b y‖ ≤ (1 - ε)⁻¹ * ‖graph γ x - graph γ y‖
    rw [← map_sub, le_inv_mul_iff₀ hδ]
    exact (graph_increment_comparison γ b y x hε (herr y hy x hx)).1
  have hforward : f '' (affineGraph b '' S) = graph γ '' S := by
    simp [image_image, f]
  have hbackward : g '' (graph γ '' S) = affineGraph b '' S := by
    rw [image_image]
    rfl
  have hupper := normalized_lipschitz_image_le hf m
  have hlower := normalized_lipschitz_image_le hg m
  rw [hforward, affine_jacobian] at hupper
  rw [hbackward, affine_jacobian] at hlower
  have hK : (K : ℝ≥0∞) ^ m = ENNReal.ofReal ((1 + ε) ^ m) := by
    rw [ENNReal.ofReal_pow (by positivity)]
    congr 1
    exact (ENNReal.ofReal_eq_coe_nnreal (by positivity)).symm
  have hK' : (K' : ℝ≥0∞) ^ m = (ENNReal.ofReal ((1 - ε) ^ m))⁻¹ := by
    rw [ENNReal.ofReal_pow hδ.le, ENNReal.inv_pow]
    congr 1
    rw [← ENNReal.ofReal_inv_of_pos hδ]
    exact (ENNReal.ofReal_eq_coe_nnreal (by positivity)).symm
  rw [hK] at hupper
  rw [hK'] at hlower
  constructor
  · have hc0 : ENNReal.ofReal ((1 - ε) ^ m) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (pow_pos hδ m)).ne'
    have hct : ENNReal.ofReal ((1 - ε) ^ m) ≠ ∞ := ENNReal.ofReal_ne_top
    calc
      _ ≤ ENNReal.ofReal ((1 - ε) ^ m) *
          ((ENNReal.ofReal ((1 - ε) ^ m))⁻¹ * μHE[m] (graph γ '' S)) :=
        mul_le_mul_right hlower _
      _ = _ := by rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 hct, one_mul]
  · exact hupper

theorem measurable_jacobian {m : ℕ} : Measurable (jacobian (m := m)) := by
  unfold jacobian
  fun_prop

theorem piece_estimate : Expected.PieceEstimate := by
  intro m γ a b ε hε hε2 ha E hnear herr S hS hSE
  have hδ : 0 < 1 - ε := by linarith
  have hplus : 0 < 1 + ε := by linarith
  have hcmp := graph_measure_comparison γ b hε.le (by linarith)
    (fun x hx y hy => herr x (hSE hx) y (hSE hy))
  have hmeas : Measurable (fun x => ENNReal.ofReal (jacobian (a x))) :=
    (measurable_jacobian.comp ha).ennreal_ofReal
  have hlow : ENNReal.ofReal (1 - ε) *
      (∫⁻ x in S, ENNReal.ofReal (jacobian (a x))) ≤
        ENNReal.ofReal (jacobian b) * volume S := by
    rw [← lintegral_const_mul _ hmeas, ← setLIntegral_const]
    apply setLIntegral_mono' hS
    intro x hx
    rw [← ENNReal.ofReal_mul hδ.le]
    exact ENNReal.ofReal_le_ofReal
      (jacobian_comparison hε.le (hnear x (hSE hx))).1
  have hupp : ENNReal.ofReal (jacobian b) * volume S ≤
      ENNReal.ofReal (1 + ε) *
        (∫⁻ x in S, ENNReal.ofReal (jacobian (a x))) := by
    rw [← lintegral_const_mul _ hmeas, ← setLIntegral_const]
    apply setLIntegral_mono' hS
    intro x hx
    rw [← ENNReal.ofReal_mul hplus.le]
    exact ENNReal.ofReal_le_ofReal
      (jacobian_comparison hε.le (hnear x (hSE hx))).2
  constructor
  · have h := (mul_le_mul_right hlow (ENNReal.ofReal ((1 - ε) ^ m))).trans hcmp.1
    simpa only [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hδ.le m),
      ← pow_succ] using h
  · have h := hcmp.2.trans (mul_le_mul_right hupp (ENNReal.ofReal ((1 + ε) ^ m)))
    simpa only [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hplus.le m),
      ← pow_succ] using h

theorem exists_rationalVector_near {m : ℕ} (b : Space m) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : Fin m → ℚ, ‖b - rationalVector q‖ < δ := by
  have hd : DenseRange (fun q : Fin m → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  let he := (EuclideanSpace.equiv (Fin m) ℝ).symm
  have hd' : DenseRange (rationalVector (m := m)) := by
    change DenseRange (fun q : Fin m → ℚ => WithLp.toLp 2 (fun i => (q i : ℝ)))
    simpa only [he, EuclideanSpace.equiv, PiLp.coe_symm_continuousLinearEquiv,
      Function.comp_def] using
      he.surjective.denseRange.comp hd he.continuous
  simpa only [dist_eq_norm] using hd'.exists_dist_lt b hδ

/-- A countable Borel partition obtained from Mathlib's differentiability
decomposition. A scalar function is embedded along a unit vector so that the
library's density-point estimate for square derivative matrices applies.
Removing the Borel sets where that estimate fails loses only a null set. -/
theorem affine_partition : Expected.Partition := by
  classical
  intro m hm U γ L hL a ha ε hε hε2
  obtain ⟨s₀, hs₀ae, hs₀m, hs₀deriv⟩ := ha.2.exists_measurable_mem
  let s : Set (Space m) := (U : Set (Space m)) ∩ s₀
  have hs : MeasurableSet s := U.isOpen.measurableSet.inter hs₀m
  have hsae : ∀ᵐ x ∂volume.restrict (U : Set (Space m)), x ∈ s := by
    filter_upwards [hs₀ae, ae_restrict_mem U.isOpen.measurableSet] with x hx hxU
    exact ⟨hxU, hx⟩
  let e : Space m := EuclideanSpace.basisFun (Fin m) ℝ ⟨0, hm⟩
  have he : ‖e‖ = 1 := (EuclideanSpace.basisFun (Fin m) ℝ).orthonormal.norm_eq_one _
  let F : Space m → Space m := fun x => γ x • e
  let F' : Space m → Space m →L[ℝ] Space m :=
    fun x => InnerProductSpace.rankOne ℝ e (a x)
  have hF' (x : Space m) (hx : x ∈ s) : HasFDerivAt F (F' x) x :=
    (hs₀deriv x hx.2).smul_const e
  let δ : ℝ≥0 := ⟨ε / 8, by positivity⟩
  have hδ : (0 : ℝ) < δ := by change 0 < ε / 8; linarith
  obtain ⟨t, A, htdisj, htm, htcover, htapprox, htA⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt F s F'
      (fun x hx => (hF' x hx).hasFDerivWithinAt) (fun _ => δ)
      (fun _ => by exact_mod_cast hδ.ne')
  let y : ℕ → Space m := fun n =>
    if h : s.Nonempty then (htA h n).choose else 0
  let b : ℕ → Space m := fun n => a (y n)
  have hAb (hsne : s.Nonempty) (n : ℕ) :
      A n = InnerProductSpace.rankOne ℝ e (b n) := by
    dsimp [b, y]
    rw [dite_eq_left hsne]
    exact (htA hsne n).choose_spec.2
  have hclose (n : ℕ) :
      ∀ᵐ x ∂volume.restrict (s ∩ t n), ‖a x - b n‖ ≤ (δ : ℝ) := by
    by_cases hsne : s.Nonempty
    · have hd := (htapprox n).norm_fderiv_sub_le volume (hs.inter (htm n)) F'
        (fun x hx => (hF' x hx.1).hasFDerivWithinAt)
      filter_upwards [hd] with x hx
      have hx' : ‖F' x - A n‖ ≤ (δ : ℝ) := hx
      rw [hAb hsne n] at hx'
      change ‖InnerProductSpace.rankOne ℝ e (a x) -
        InnerProductSpace.rankOne ℝ e (b n)‖ ≤ (δ : ℝ) at hx'
      simpa only [← map_sub, InnerProductSpace.norm_rankOne, he, one_mul] using hx'
    · have hsempty : s = ∅ := not_nonempty_iff_eq_empty.mp hsne
      simp [hsempty]
  choose q hq using (fun n => exists_rationalVector_near (b n) hδ)
  let E : ℕ → Set (Space m) := fun n =>
    (s ∩ t n) ∩ {x | ‖a x - b n‖ ≤ (δ : ℝ)}
  have hEm (n : ℕ) : MeasurableSet (E n) :=
    (hs.inter (htm n)).inter (measurableSet_le (ha.1.sub_const (b n)).norm measurable_const)
  have hES (n : ℕ) : E n ⊆ s ∩ t n := inter_subset_left
  have hEcover : volume ((U : Set (Space m)) \ ⋃ n, E n) = 0 := by
    have hglobal (n : ℕ) : ∀ᵐ x ∂volume,
        x ∈ s ∩ t n → ‖a x - b n‖ ≤ (δ : ℝ) :=
      (ae_restrict_iff' (hs.inter (htm n))).mp (hclose n)
    have hsU := (ae_restrict_iff' U.isOpen.measurableSet).mp hsae
    have hall := ae_all_iff.mpr hglobal
    have hcov : ∀ᵐ x ∂volume, x ∈ U → x ∈ ⋃ n, E n := by
      filter_upwards [hsU, hall] with x hxs hxall hxU
      have hxs' := hxs hxU
      obtain ⟨n, hxn⟩ := mem_iUnion.mp (htcover hxs')
      exact mem_iUnion.mpr ⟨n, ⟨⟨hxs', hxn⟩, hxall n ⟨hxs', hxn⟩⟩⟩
    convert (ae_iff.mp hcov) using 1
    congr 1
    ext x
    simp only [mem_sdiff, mem_ofPred_eq, not_imp]
    rfl
  refine ⟨E, q, hEm, (fun n x hx => ((hES n hx).1).1), ?_, hEcover, ?_, ?_⟩
  · intro i j hij
    exact (htdisj hij).mono (fun _ hx => (hES i hx).2) (fun _ hx => (hES j hx).2)
  · intro n x hx
    calc
      ‖a x - rationalVector (q n)‖ ≤ ‖a x - b n‖ + ‖b n - rationalVector (q n)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < (δ : ℝ) + δ := add_lt_add_of_le_of_lt hx.2 (hq n)
      _ < ε / 2 := by change ε / 8 + ε / 8 < ε / 2; linarith
  · intro n x hx y hy
    have hsne : s.Nonempty := ⟨x, (hES n hx).1⟩
    have happ := htapprox n y (hES n hy) x (hES n hx)
    rw [hAb hsne n] at happ
    change ‖γ y • e - γ x • e - inner ℝ (b n) (y - x) • e‖ ≤
      (δ : ℝ) * ‖y - x‖ at happ
    simp only [← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs] at happ
    have hinner : |inner ℝ (b n - rationalVector (q n)) (y - x)| ≤
        ‖b n - rationalVector (q n)‖ * ‖y - x‖ := by
      simpa only [Real.norm_eq_abs] using
        norm_inner_le_norm (𝕜 := ℝ) (b n - rationalVector (q n)) (y - x)
    calc
      |γ y - γ x - inner ℝ (rationalVector (q n)) (y - x)| =
          |(γ y - γ x - inner ℝ (b n) (y - x)) +
            inner ℝ (b n - rationalVector (q n)) (y - x)| := by
        congr 1
        rw [inner_sub_left]
        ring
      _ ≤ |γ y - γ x - inner ℝ (b n) (y - x)| +
          |inner ℝ (b n - rationalVector (q n)) (y - x)| := abs_add_le _ _
      _ ≤ (δ : ℝ) * ‖y - x‖ + ‖b n - rationalVector (q n)‖ * ‖y - x‖ :=
        add_le_add happ hinner
      _ ≤ ε * ‖y - x‖ := by
        have hq' := (hq n).le
        have hnn := norm_nonneg (y - x)
        change ‖b n - rationalVector (q n)‖ ≤ ε / 8 at hq'
        change ε / 8 * ‖y - x‖ + ‖b n - rationalVector (q n)‖ * ‖y - x‖ ≤ ε * ‖y - x‖
        nlinarith

theorem graph_area_pieces : Expected.Theorem := by
  intro m hm U γ L hL a ha ε hε hε2
  obtain ⟨E, q, hE⟩ := affine_partition m hm U γ L hL a ha ε hε hε2
  refine ⟨E, q, hE, ?_⟩
  intro n S hS hSE
  exact ⟨image_measurability m U γ hL.continuousOn S hS (hSE.trans (hE.2.1 n)),
    piece_estimate m γ a (rationalVector (q n)) ε hε hε2 ha.1 (E n)
      (hE.2.2.2.2.1 n) (hE.2.2.2.2.2 n) S hS hSE⟩

end P102.U4.GraphPieces
