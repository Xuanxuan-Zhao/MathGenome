import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.CzHardyInvariance
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyMolecules
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hardy.HardyCZEndpoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.SchwartzFourierConvention
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal lp FourierTransform

namespace ExpandedFA.PartIV.CzHardyInvariance
open SingularIntegrals StandardConvolution CZWeak
open Hardy.AtomicHardySpaceSpec Hardy.HardyCZEndpointSpec CzHardyInvarianceSpec

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}

lemma operatorSize_nonneg (T : StandardConvolutionOperator 𝕜 d) : 0 ≤ operatorSize T := by
  unfold operatorSize
  have := T.kernel.constant_nonneg
  positivity

lemma atomClass_eq (a : Atoms 𝕜 d) :
    atomClass a = Hardy.AtomicHardySpace.atomElement volume a := rfl

lemma embedding_atomClass (a : Atoms 𝕜 d) :
    EmbeddingValue volume (atomClass a) = a.val :=
  Hardy.AtomicHardySpace.embedding_atomElement volume a

lemma atomClass_norm (a : Atoms 𝕜 d) : ‖atomClass a‖ ≤ 1 :=
  Hardy.AtomicHardySpace.atomElement_norm volume a

/-- The kernel estimate holds on the closed exterior, including |x-c| = 2r. -/
lemma atom_tail (T : StandardConvolutionOperator 𝕜 d) (a : Atoms 𝕜 d)
    (c : Space d) (r : ℝ) (hr : 0 < r)
    (h2 : MemLp (a.val : Space d → 𝕜) 2)
    (hs : SupportedAE (a.val : Space d → 𝕜) (Metric.closedBall c r)) :
    ∀ᵐ x ∂volume, 2 * r ≤ ‖x - c‖ →
      ‖T.operator (h2.toLp a.val) x‖ ≤
        ((d : ℝ) * T.kernel.constant * 2 ^ (d + 1)) * r / ‖x - c‖ ^ (d + 1) := by
  let A := (d : ℝ) * T.kernel.constant * 2 ^ (d + 1)
  have hA : 0 ≤ A := by dsimp [A]; have := T.kernel.constant_nonneg; positivity
  have ha := MeasureTheory.L1.integrable_coeFn a.val
  have hrep := cancellation_representation 𝕜 d T a.val (Metric.closedBall c r)
    (isCompact_closedBall c r) ha h2 hs a.property.1 c
  filter_upwards [hrep] with x hx hdist
  have hxn : x - c ≠ 0 := norm_pos_iff.mp (by linarith)
  have hxS : x ∉ Metric.closedBall c r := by
    simp only [Metric.mem_closedBall, dist_eq_norm, not_le]
    linarith
  obtain ⟨hki, hke⟩ := hx hxS
  have hbound : ∀ᵐ y ∂volume,
      ‖(T.kernel.function (x - y) - T.kernel.function (x - c)) * a.val y‖ ≤
        (A * r / ‖x - c‖ ^ (d + 1)) * ‖a.val y‖ := by
    filter_upwards [hs] with y hy
    by_cases hyS : y ∈ Metric.closedBall c r
    · have hyd : ‖y - c‖ ≤ r := by simpa [dist_eq_norm] using hyS
      have hh : ‖y - c‖ ≤ ‖x - c‖ / 2 := by linarith
      have hk := kernel_difference 𝕜 d T.kernel (x - c) (y - c) hxn hh
      have halg : x - c - (y - c) = x - y := by abel
      rw [halg] at hk
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply hk.trans
      change A * ‖y - c‖ / ‖x - c‖ ^ (d + 1) ≤ A * r / ‖x - c‖ ^ (d + 1)
      gcongr
    · simp [hy hyS]
  rw [hke]
  calc
    ‖∫ y, (T.kernel.function (x - y) - T.kernel.function (x - c)) * a.val y‖ ≤
        ∫ y, ‖(T.kernel.function (x - y) - T.kernel.function (x - c)) * a.val y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y, (A * r / ‖x - c‖ ^ (d + 1)) * ‖a.val y‖ :=
      integral_mono_ae hki.norm (ha.norm.const_mul _) hbound
    _ = (A * r / ‖x - c‖ ^ (d + 1)) * ‖a.val‖ := by
      rw [integral_const_mul, MeasureTheory.L1.norm_eq_integral_norm]
    _ ≤ _ := mul_le_of_le_one_right (by positivity)
      (Hardy.AtomicHardySpace.atom_norm_le volume a)

/-- The reciprocal square-root ball volume factors into its unit-volume and
radius contributions. -/
lemma inverse_ball_volume (c : Space d) (r : ℝ) (hr : 0 < r) :
    (volume.real (Metric.ball c r))⁻¹ =
      ((volume.real (Metric.ball (0 : Space d) 1)) ^ (-1 / 2 : ℝ) *
        r ^ (-(d : ℝ) / 2)) ^ 2 := by
  have hV : 0 < volume.real (Metric.ball (0 : Space d) 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ zero_lt_one).ne' measure_ball_ne_top
  rw [HardyMolecules.ball_volume_center c r hr, mul_inv, mul_pow]
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hV.le,
    ← Real.rpow_natCast _ 2, ← Real.rpow_mul hr.le]
  norm_num only [Nat.cast_ofNat, neg_div, neg_mul, div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Real.rpow_neg_one, Real.rpow_neg hr.le, Real.rpow_natCast]
  ring

/-- Uniform normalized L² and pointwise-tail estimates, including d = 0. -/
theorem normalized_bounds : NormalizedBounds := by
  intro 𝕜 _ d T a
  obtain ⟨c, r, hr, hs, h2, he⟩ := Hardy.HardyCZEndpoint.atom_energy a
  refine ⟨c, r, h2, hr, ?_, ?_⟩
  · have he' : ‖h2.toLp a.val‖ ^ 2 ≤ (volume.real (Metric.ball c r))⁻¹ := by
      rw [norm_L2_sq]
      exact (integral_congr_ae (h2.coeFn_toLp.mono fun x hx =>
        congrArg (fun z : 𝕜 => ‖z‖ ^ 2) hx)).le.trans he
    rw [inverse_ball_volume c r hr] at he'
    have hn : ‖h2.toLp a.val‖ ≤
        (volume.real (Metric.ball (0 : Space d) 1)) ^ (-1 / 2 : ℝ) *
          r ^ (-(d : ℝ) / 2) := by
      have : 0 ≤ (volume.real (Metric.ball (0 : Space d) 1)) ^ (-1 / 2 : ℝ) *
          r ^ (-(d : ℝ) / 2) := by positivity
      nlinarith [norm_nonneg (h2.toLp a.val)]
    calc
      _ = ‖T.operator (h2.toLp a.val)‖ := (Lp.norm_def _).symm
      _ ≤ ‖T.operator‖ * ‖h2.toLp a.val‖ := T.operator.le_opNorm _
      _ ≤ ‖T.operator‖ *
          ((volume.real (Metric.ball (0 : Space d) 1)) ^ (-1 / 2 : ℝ) *
            r ^ (-(d : ℝ) / 2)) := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      _ ≤ operatorSize T * r ^ (-(d : ℝ) / 2) := by
        unfold operatorSize
        have := T.kernel.constant_nonneg
        have h : 0 ≤ (d : ℝ) * T.kernel.constant * 2 ^ (d + 1) := by positivity
        nlinarith [Real.rpow_nonneg hr.le (-(d : ℝ) / 2)]
  · filter_upwards [atom_tail T a c r hr h2 hs] with x hx hd
    apply (hx hd).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hr.le
    exact le_add_of_nonneg_left (by positivity)

/-- Every L¹ atomic representation converges in the quotient Hardy norm. -/
lemma atomic_series (a : ℕ → Atoms 𝕜 d) (b : ℕ → 𝕜)
    (hb : Summable (fun j => ‖b j‖)) (h : Hardy 𝕜 d)
    (hf : HasSum (fun j => b j • (a j).val) (EmbeddingValue volume h)) :
    HasSum (fun j => b j • atomClass (a j)) h := by
  have hs : Summable (fun j => b j • atomClass (a j)) :=
    hb.of_norm_bounded (fun j => by
      rw [norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _) (atomClass_norm _))
  have he : EmbeddingValue volume (∑' j, b j • atomClass (a j)) =
      EmbeddingValue volume h := by
    apply HasSum.unique _ hf
    simpa only [map_smul, embedding_atomClass] using
      (EmbeddingValue volume).hasSum hs.hasSum
  exact (Hardy.AtomicHardySpace.embedding_properties volume).1 he ▸ hs.hasSum

/-- A bounded endpoint map lifts if its atoms admit uniformly bounded Hardy
lifts. The proof uses all ℓ¹ coefficients, then the actual quotient norm. -/
lemma lift_of_atom_bound (E : Hardy 𝕜 d →L[𝕜] CZWeak.L1 𝕜 d) (M : ℝ)
    (hM : 0 ≤ M)
    (ha : ∀ a : Atoms 𝕜 d, ∃ u : Hardy 𝕜 d,
      EmbeddingValue volume u = E (atomClass a) ∧ ‖u‖ ≤ M) :
    ∃ U : Hardy 𝕜 d →L[𝕜] Hardy 𝕜 d,
      ‖U‖ ≤ M ∧ (EmbeddingValue volume).comp U = E := by
  choose u hu hun using ha
  have hseq (c : CoefficientsValue (𝕜 := 𝕜) (volume : Measure (Space d))) :
      ∃ g : Hardy 𝕜 d,
        EmbeddingValue volume g = E ((KernelValue volume).mkQ c) ∧ ‖g‖ ≤ M * ‖c‖ := by
    have := Hardy.AtomicHardySpace.euclidean_atoms_nonempty d 𝕜
    obtain ⟨a, b, hb, hf⟩ := Hardy.AtomicHardySpace.coefficient_sequence volume c
    have hsrc := atomic_series a b hb.summable ((KernelValue volume).mkQ c) hf
    have hs : Summable (fun j => b j • u (a j)) :=
      (hb.summable.mul_left M).of_norm_bounded (fun j => by
        rw [norm_smul, mul_comm M]
        exact mul_le_mul_of_nonneg_left (hun _) (norm_nonneg _))
    refine ⟨∑' j, b j • u (a j), ?_, ?_⟩
    · apply HasSum.unique ((EmbeddingValue volume).hasSum hs.hasSum)
      simpa only [map_smul, hu] using E.hasSum hsrc
    · apply hs.hasSum.norm_le_of_bounded
        (by simpa only [tsum_mul_left, hb.tsum_eq] using (hb.summable.mul_left M).hasSum)
      intro j
      rw [norm_smul, mul_comm M]
      exact mul_le_mul_of_nonneg_left (hun _) (norm_nonneg _)
  have hbound (h : Hardy 𝕜 d) :
      ∃ g : Hardy 𝕜 d, EmbeddingValue volume g = E h ∧ ‖g‖ ≤ M * ‖h‖ := by
    obtain ⟨c₀, hc₀⟩ := (KernelValue (𝕜 := 𝕜) (volume : Measure (Space d))).mkQ_surjective h
    obtain ⟨g, hg, _⟩ := hseq c₀
    rw [hc₀] at hg
    refine ⟨g, hg, le_of_forall_pos_le_add fun ε hε => ?_⟩
    have hδ : 0 < ε / (M + 1) := div_pos hε (by linarith)
    obtain ⟨c, hc, hcn⟩ := Submodule.Quotient.norm_mk_lt h hδ
    obtain ⟨g', hg', hgn⟩ := hseq c
    change (KernelValue volume).mkQ c = h at hc
    rw [hc] at hg'
    have hgg : g = g' := (Hardy.AtomicHardySpace.embedding_properties volume).1
      (hg.trans hg'.symm)
    rw [hgg]
    calc
      ‖g'‖ ≤ M * ‖c‖ := hgn
      _ ≤ M * (‖h‖ + ε / (M + 1)) := mul_le_mul_of_nonneg_left hcn.le hM
      _ ≤ M * ‖h‖ + ε := by
        have hsmall : M * (ε / (M + 1)) ≤ ε := by
          rw [← mul_div_assoc]
          apply (div_le_iff₀ (by linarith : 0 < M + 1)).mpr
          nlinarith
        nlinarith
  choose g hg hgn using hbound
  let L : Hardy 𝕜 d →ₗ[𝕜] Hardy 𝕜 d := {
    toFun := g
    map_add' x y := by
      apply (Hardy.AtomicHardySpace.embedding_properties volume).1
      rw [map_add, hg, hg, hg, map_add]
    map_smul' k x := by
      change g (k • x) = k • g x
      apply (Hardy.AtomicHardySpace.embedding_properties volume).1
      rw [map_smul, hg, hg, map_smul] }
  let U := L.mkContinuous M hgn
  exact ⟨U, U.opNorm_le_bound hM hgn, by apply ContinuousLinearMap.ext; intro h; exact hg h⟩

/-- The geometric bounds become a genuine molecule once cancellation is known. -/
lemma atom_molecule_of_cancellation (hc : AtomCancellation) : AtomMolecule := by
  intro 𝕜 _ d T a
  obtain ⟨c, r, h2, hr, hn, ht⟩ := normalized_bounds 𝕜 d T a
  exact ⟨c, r, h2, hr, operatorSize_nonneg T, Lp.memLp _, hn, (hc 𝕜 d T a h2).2, ht⟩

lemma atom_bound_of_cancellation (hc : AtomCancellation) : CzHardyInvarianceSpec.AtomBound := by
  intro d
  obtain ⟨C, hC, hm⟩ := HardyMolecules.molecule.{0} d
  refine ⟨C, hC, fun 𝕜 _ T a => ?_⟩
  obtain ⟨c, r, h2, hg⟩ := atom_molecule_of_cancellation hc 𝕜 d T a
  obtain ⟨hi, h, he, hn, _⟩ := hm (T.operator (h2.toLp a.val)) c r (operatorSize T) hg
  exact ⟨h2, hi, h, he, hn⟩

/-- Continuous maps on Hardy space are determined by their values on atoms. -/
lemma maps_eq_of_atoms {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (E E' : Hardy 𝕜 d →L[𝕜] F)
    (he : ∀ a : Atoms 𝕜 d, E (atomClass a) = E' (atomClass a)) : E = E' := by
  ext h
  obtain ⟨a, b, hb, hs⟩ :=
    (Hardy.AtomicHardySpace.euclidean_sequence_range d (EmbeddingValue volume h)).mp ⟨h, rfl⟩
  have hsum := atomic_series a b hb h hs
  apply (E.hasSum hsum).unique
  simpa only [map_smul, he] using E'.hasSum hsum

lemma endpoint_with_atom_agreement (T : StandardConvolutionOperator 𝕜 d) :
    ∃ E : Hardy 𝕜 d →L[𝕜] CZWeak.L1 𝕜 d,
      (∀ (a : Atoms 𝕜 d) (h2 : MemLp (a.val : Space d → 𝕜) 2),
        (E (atomClass a) : Space d → 𝕜) =ᵐ[volume]
          (T.operator (h2.toLp a.val) : Space d → 𝕜)) ∧
      (∀ (S : CZWeak.L1 𝕜 d →ₗ[𝕜] MeasurableClasses 𝕜 d),
        IsCompatibleExtension T S → ∀ h : Hardy 𝕜 d,
          (E h : Space d → 𝕜) =ᵐ[volume]
            (S (EmbeddingValue volume h) : Space d → 𝕜)) := by
  obtain ⟨E, _, hE⟩ := Hardy.HardyCZEndpoint.endpoint 𝕜 d T
  refine ⟨E, ?_, hE⟩
  intro a h2
  obtain ⟨S, hS, _⟩ := unique_extension 𝕜 d T
  have he := hE S hS (atomClass a)
  rw [embedding_atomClass] at he
  have hc := hS.1 a.val (Lp.memLp a.val) h2
  rw [Lp.toLp_coeFn] at hc
  exact he.trans hc

/-- Representation independence and the quotient-norm estimate follow from
the uniform atomic bound and the already accepted endpoint map. -/
lemma invariance_of_atom_bound (hb : CzHardyInvarianceSpec.AtomBound) : Invariance := by
  intro d
  obtain ⟨C, hC, hbound⟩ := hb d
  refine ⟨C, hC, fun 𝕜 _ T => ?_⟩
  obtain ⟨E, hEa, hES⟩ := endpoint_with_atom_agreement T
  have ha (a : Atoms 𝕜 d) : ∃ u : Hardy 𝕜 d,
      EmbeddingValue volume u = E (atomClass a) ∧ ‖u‖ ≤ C * operatorSize T := by
    obtain ⟨h2, hi, u, hu, hn⟩ := hbound 𝕜 T a
    refine ⟨u, hu.trans ?_, hn⟩
    exact Lp.ext (hi.coeFn_toL1.trans (hEa a h2).symm)
  obtain ⟨U, hU, he⟩ := lift_of_atom_bound E (C * operatorSize T)
    (mul_nonneg hC.le (operatorSize_nonneg T)) ha
  refine ⟨U, hU, ?_, ?_, ?_⟩
  · intro E' hE'
    rw [he]
    apply maps_eq_of_atoms
    intro a
    obtain ⟨h2, _⟩ := Hardy.HardyCZEndpoint.atom_estimate 𝕜 d T a
    exact Lp.ext ((hEa a h2).trans (hE' a h2).symm)
  · intro S hS h
    have hh := DFunLike.congr_fun he h
    change EmbeddingValue volume (U h) = E h at hh
    rw [hh]
    exact hES S hS h
  · intro a b hb h hf
    have hs := U.hasSum (atomic_series a b hb h hf)
    simpa only [map_smul] using hs

/-- Essential boundedness of the multiplier suffices; the multiplier need
not be continuous at zero. This lemma still requires the actual Fourier
product identity, which must be established for the given operator. -/
lemma continuous_zero_of_bounded_multiplier {X : Type} [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure X} [Measure.IsOpenPosMeasure μ]
    {f g m : X → ℂ} (hf : Continuous f) (hg : Continuous g)
    (M : ℝ) (hm : ∀ᵐ x ∂μ, ‖m x‖ ≤ M) (he : f =ᵐ[μ] fun x => m x * g x)
    {x : X} (hzero : g x = 0) : f x = 0 := by
  have hb : ∀ᵐ y ∂μ, ‖f y‖ ≤ M * ‖g y‖ := by
    filter_upwards [hm, he] with y hy hey
    rw [hey, norm_mul]
    exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
  have hclosed : IsClosed {y | ‖f y‖ ≤ M * ‖g y‖} :=
    isClosed_le hf.norm (continuous_const.mul hg.norm)
  have hset := (Measure.dense_of_ae hb).closure_eq
  rw [hclosed.closure_eq] at hset
  have hx : ‖f x‖ ≤ M * ‖g x‖ := by
    change x ∈ {y | ‖f y‖ ≤ M * ‖g y‖}
    rw [hset]
    trivial
  apply norm_eq_zero.mp
  rw [hzero, norm_zero, mul_zero] at hx
  exact le_antisymm hx (norm_nonneg _)

lemma integralFourier_continuous {d : ℕ} {f : Fourier.Euclidean d → ℂ} (hf : Integrable f) :
    Continuous (Fourier.integralFourier f) := by
  have he : Fourier.integralFourier f = 𝓕 f := funext (Fourier.integralFourier_eq_native f)
  rw [he]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf

lemma bounded_multiplier_cancellation {d : ℕ} (f g m : Fourier.Euclidean d → ℂ)
    (hf : Integrable f) (hg : Integrable g) (hz : (∫ x, f x) = 0)
    (M : ℝ) (hm : ∀ᵐ ξ ∂volume, ‖m ξ‖ ≤ M)
    (he : Fourier.integralFourier g =ᵐ[volume] fun ξ => m ξ * Fourier.integralFourier f ξ) :
    (∫ x, g x) = 0 := by
  have hzero : Fourier.integralFourier f 0 = 0 := by simp [Fourier.integralFourier, hz]
  have h := continuous_zero_of_bounded_multiplier
    (integralFourier_continuous hg) (integralFourier_continuous hf) M hm he hzero
  simpa [Fourier.integralFourier] using h

/-! Spatial averaging supplies cancellation without assuming a multiplier.
The average at scale r is related to convolution by an exact L² dilation;
as r tends to infinity it converges to the total integral times the test. -/
namespace SpatialCancellation


def translate (y : Space d) (u : L2 𝕜 d) : L2 𝕜 d :=
  Lp.compMeasurePreserving (fun x => x - y) (measurePreserving_sub_right volume y) u

lemma translate_rep (y : Space d) (u : L2 𝕜 d) :
    (translate y u : Space d → 𝕜) =ᵐ[volume] fun x => u (x-y) :=
  Lp.coeFn_compMeasurePreserving _ _

lemma translate_norm (y : Space d) (u : L2 𝕜 d) : ‖translate y u‖ = ‖u‖ :=
  Lp.norm_compMeasurePreserving _ _

lemma translate_zero (u : L2 𝕜 d) : translate 0 u = u := by
  apply Lp.ext
  simpa using translate_rep 0 u

lemma translate_continuous (u : L2 𝕜 d) : Continuous (fun y => translate y u) := by
  let g : Space d → C(Space d, Space d) :=
    fun y => ⟨fun x => x-y, continuous_id.sub continuous_const⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_snd.sub continuous_fst)
  exact continuous_const.compMeasurePreservingLp hg
    (fun y => measurePreserving_sub_right volume y) (by norm_num)

def average (f : Space d → 𝕜) (h : Space d → Space d) (u : L2 𝕜 d) : L2 𝕜 d :=
  ∫ y, f y • translate (h y) u

lemma average_integrable {f : Space d → 𝕜} (hf : Integrable f)
    {h : Space d → Space d} (hh : Continuous h) (u : L2 𝕜 d) :
    Integrable (fun y => f y • translate (h y) u) := by
  apply (hf.norm.mul_const ‖u‖).mono'
    (hf.aestronglyMeasurable.smul ((translate_continuous u).comp hh).aestronglyMeasurable)
  exact ae_of_all _ fun y => by
    change ‖f y • translate (h y) u‖ ≤ ‖f y‖ * ‖u‖
    rw [norm_smul, translate_norm]

lemma average_commute (T : StandardConvolutionOperator 𝕜 d)
    {f : Space d → 𝕜} (hf : Integrable f) (u : L2 𝕜 d) :
    T.operator (average f id u) = average f id (T.operator u) := by
  rw [average, average, ← T.operator.integral_comp_comm (average_integrable hf continuous_id u)]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    change T.operator (f y • translate y u) = f y • translate y (T.operator u)
    rw [map_smul]
    congr 1
    apply Lp.ext
    exact (T.translation_invariant y u (translate y u) (translate_rep y u)).trans
      (translate_rep y (T.operator u)).symm

lemma average_product_integrable {f : Space d → 𝕜} (hf : Integrable f)
    {h : Space d → Space d} (hh : Continuous h) (u : L2 𝕜 d)
    (hu : Integrable (u : Space d → 𝕜)) :
    Integrable (fun z : Space d × Space d => f z.2 * u (z.1 - h z.2)) := by
  have hm : AEStronglyMeasurable
      (fun z : Space d × Space d => f z.2 * u (z.1 - h z.2)) (volume.prod volume) :=
    hf.aestronglyMeasurable.comp_snd.mul
      ((Lp.stronglyMeasurable u).comp_measurable
        (measurable_fst.sub (hh.measurable.comp measurable_snd))).aestronglyMeasurable
  apply (integrable_prod_iff' hm).mpr
  refine ⟨ae_of_all _ fun y => (hu.comp_sub_right (h y)).const_mul (f y), ?_⟩
  have he : (fun y => ∫ x, ‖f y * u (x - h y)‖) =
      fun y => ‖f y‖ * ∫ x, ‖u x‖ := by
    funext y
    simp only [norm_mul, integral_const_mul]
    congr 1
    exact integral_sub_right_eq_self (fun x => ‖u x‖) (h y)
  rw [he]
  exact hf.norm.mul_const _

lemma setIntegral_probe (s : Set (Space d)) (hs : MeasurableSet s)
    (hμs : volume s ≠ ⊤) (u : L2 𝕜 d) :
    (innerSL 𝕜 (indicatorConstLp 2 hs hμs (1 : 𝕜))) u = ∫ x in s, u x := by
  rw [innerSL_apply_apply, L2.inner_indicatorConstLp_eq_setIntegral_inner]
  simp [RCLike.inner_apply]

lemma average_rep {f : Space d → 𝕜} (hf : Integrable f)
    {h : Space d → Space d} (hh : Continuous h) (u : L2 𝕜 d)
    (hu : Integrable (u : Space d → 𝕜)) :
    (average f h u : Space d → 𝕜) =ᵐ[volume]
      fun x => ∫ y, f y * u (x - h y) := by
  have hprod := average_product_integrable hf hh u hu
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s hs hμs => integrableOn_Lp_of_measure_ne_top _ (by norm_num) hμs.ne)
    (fun _ _ _ => hprod.integral_prod_left.integrableOn)
  intro s hs hμs
  let P := innerSL 𝕜 (indicatorConstLp 2 hs hμs.ne (1 : 𝕜))
  calc
    (∫ x in s, average f h u x) = P (average f h u) :=
      (setIntegral_probe s hs hμs.ne _).symm
    _ = ∫ y, P (f y • translate (h y) u) :=
      (P.integral_comp_comm (average_integrable hf hh u)).symm
    _ = ∫ y, ∫ x in s, f y * u (x - h y) := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        change P (f y • translate (h y) u) = ∫ x in s, f y * u (x - h y)
        rw [map_smul]
        change f y * ((innerSL 𝕜 (indicatorConstLp 2 hs hμs.ne (1 : 𝕜))) (translate (h y) u)) = _
        rw [setIntegral_probe, integral_const_mul]
        congr 1
        exact setIntegral_congr_ae hs ((translate_rep (h y) u).mono fun x hx _ => hx)
    _ = ∫ x in s, ∫ y, f y * u (x - h y) := by
      exact (integral_integral_swap
        (hprod.mono_measure (Measure.prod_mono (Measure.restrict_le_self) le_rfl))).symm

lemma dilate_memLp (r : ℝ) (hr : r ≠ 0) (u : L2 𝕜 d) :
    MemLp (fun x : Space d => u (r • x)) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    ((Lp.aestronglyMeasurable u).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_smul volume hr))).mpr
  exact ((Lp.memLp u).integrable_norm_pow (by norm_num)).comp_smul hr

def dilateL2 (r : ℝ) (hr : r ≠ 0) (u : L2 𝕜 d) : L2 𝕜 d :=
  (dilate_memLp r hr u).toLp _

lemma dilateL2_rep (r : ℝ) (hr : r ≠ 0) (u : L2 𝕜 d) :
    (dilateL2 r hr u : Space d → 𝕜) =ᵐ[volume] fun x => u (r • x) :=
  (dilate_memLp r hr u).coeFn_toLp

lemma dilateL2_norm_sq (r : ℝ) (hr : r ≠ 0) (u : L2 𝕜 d) :
    ‖dilateL2 r hr u‖ ^ 2 = |(r ^ d)⁻¹| * ‖u‖ ^ 2 := by
  rw [norm_L2_sq, norm_L2_sq]
  have he := integral_congr_ae ((dilateL2_rep r hr u).mono fun x hx =>
    congrArg (fun z : 𝕜 => ‖z‖ ^ 2) hx)
  rw [he]
  simpa only [smul_eq_mul, finrank_euclideanSpace, Fintype.card_fin] using
    Measure.integral_comp_smul volume (fun x => ‖u x‖ ^ 2) r

lemma dilateL2_integrable (r : ℝ) (hr : r ≠ 0) (u : L2 𝕜 d)
    (hu : Integrable (u : Space d → 𝕜)) :
    Integrable (dilateL2 r hr u : Space d → 𝕜) :=
  (hu.comp_smul hr).congr (dilateL2_rep r hr u).symm

lemma average_dilation (r : ℝ) (hr : r ≠ 0) (f u : L2 𝕜 d)
    (hf : Integrable (f : Space d → 𝕜)) (hu : Integrable (u : Space d → 𝕜)) :
    dilateL2 r hr (average (dilateL2 r⁻¹ (inv_ne_zero hr) u) id f) =
      average f (fun y => r⁻¹ • y) u := by
  let v := dilateL2 r⁻¹ (inv_ne_zero hr) u
  have hv : Integrable (v : Space d → 𝕜) := dilateL2_integrable _ _ u hu
  have hleft := (Measure.quasiMeasurePreserving_smul volume hr).ae_eq_comp
    (average_rep hv continuous_id f hf)
  have hright := average_rep hf (h := fun y => r⁻¹ • y) (by fun_prop) u hu
  apply Lp.ext
  filter_upwards [dilateL2_rep r hr (average v id f), hleft, hright] with x hx hl hrx
  dsimp only [Function.comp_apply, id_eq] at hl
  rw [hx, hl, hrx]
  change (∫ y, v y * f (r • x - y)) = ∫ y, f y * u (x - r⁻¹ • y)
  calc
    _ = ∫ y, v (r • x - y) * f y := by
      simpa only [sub_sub_cancel] using
        (integral_sub_left_eq_self (fun y => v y * f (r • x-y)) volume (r • x)).symm
    _ = _ := by
      apply integral_congr_ae
      have he := (volume.measurePreserving_sub_left (r • x)).quasiMeasurePreserving.ae_eq_comp
        (dilateL2_rep r⁻¹ (inv_ne_zero hr) u)
      filter_upwards [he] with y hy
      dsimp only [Function.comp_apply] at hy
      rw [hy, smul_sub, smul_smul, inv_mul_cancel₀ hr, one_smul, mul_comm]

lemma average_dilated_norm_bound (T : StandardConvolutionOperator 𝕜 d)
    (r : ℝ) (hr : r ≠ 0) (f u : L2 𝕜 d)
    (hf : Integrable (f : Space d → 𝕜)) (hu : Integrable (u : Space d → 𝕜))
    (hTf : Integrable (T.operator f : Space d → 𝕜)) :
    ‖average (T.operator f) (fun y => r⁻¹ • y) u‖ ≤
      ‖T.operator‖ * ‖average f (fun y => r⁻¹ • y) u‖ := by
  let v := dilateL2 r⁻¹ (inv_ne_zero hr) u
  have hv : Integrable (v : Space d → 𝕜) := dilateL2_integrable _ _ u hu
  have hn := T.operator.le_opNorm (average v id f)
  have hpos : 0 < |(r ^ d)⁻¹| := abs_pos.mpr (inv_ne_zero (pow_ne_zero _ hr))
  have h1 := dilateL2_norm_sq r hr (T.operator (average v id f))
  have h2 := dilateL2_norm_sq r hr (average v id f)
  rw [average_commute T hv f, average_dilation r hr (T.operator f) u hTf hu] at h1
  rw [average_dilation r hr f u hf hu] at h2
  have hs : ‖average (T.operator f) (fun y => r⁻¹ • y) u‖ ^ 2 ≤
      (‖T.operator‖ * ‖average f (fun y => r⁻¹ • y) u‖) ^ 2 := by
    have hn' : ‖average v id (T.operator f)‖ ^ 2 ≤
        (‖T.operator‖ * ‖average v id f‖) ^ 2 := by
      rw [← average_commute T hv f]
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    calc
      _ = |(r ^ d)⁻¹| * ‖average v id (T.operator f)‖ ^ 2 := h1
      _ ≤ |(r ^ d)⁻¹| * (‖T.operator‖ * ‖average v id f‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hn' hpos.le
      _ = ‖T.operator‖ ^ 2 * ‖average f (fun y => r⁻¹ • y) u‖ ^ 2 := by rw [h2]; ring
      _ = _ := (mul_pow _ _ _).symm
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hs

lemma average_dilated_tendsto {f : Space d → 𝕜} (hf : Integrable f) (u : L2 𝕜 d) :
    Tendsto (fun n : ℕ => average f (fun y => ((n : ℝ) + 1)⁻¹ • y) u)
      atTop (𝓝 ((∫ y, f y) • u)) := by
  have he : (∫ y, f y) • u = ∫ y, f y • u := (integral_smul_const f u).symm
  rw [he]
  unfold average
  apply tendsto_integral_of_dominated_convergence (fun y => ‖f y‖ * ‖u‖)
  · intro n
    exact (average_integrable hf (h := fun y => ((n : ℝ) + 1)⁻¹ • y)
      (by fun_prop) u).aestronglyMeasurable
  · exact hf.norm.mul_const _
  · intro n
    exact ae_of_all _ fun y => by
      change ‖f y • translate (((n : ℝ) + 1)⁻¹ • y) u‖ ≤ ‖f y‖ * ‖u‖
      rw [norm_smul, translate_norm]
  · exact ae_of_all _ fun y => by
      have hy : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • y) atTop (𝓝 (0 : Space d)) := by
        simpa using
          ((tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop).inv_tendsto_atTop.smul_const y)
      simpa only [translate_zero, Function.comp_apply] using
        (tendsto_const_nhds.smul ((translate_continuous u).tendsto 0 |>.comp hy))

/-- Translation invariance and L² boundedness preserve mean zero whenever
both the input and its image are integrable. This argument is over either
scalar field and does not need a Fourier multiplier representation. -/
lemma integral_zero_of_translation_invariant (T : StandardConvolutionOperator 𝕜 d)
    (f : L2 𝕜 d) (hf : Integrable (f : Space d → 𝕜))
    (hTf : Integrable (T.operator f : Space d → 𝕜)) (hz : (∫ x, f x) = 0) :
    (∫ x, T.operator f x) = 0 := by
  let u : L2 𝕜 d := indicatorConstLp 2
    (measurableSet_ball (x := (0 : Space d)) (ε := 1)) measure_ball_ne_top (1 : 𝕜)
  have hu : Integrable (u : Space d → 𝕜) := by
    apply ((integrable_indicator_iff measurableSet_ball).mpr
      (integrableOn_const (C := (1 : 𝕜)) measure_ball_ne_top)).congr
    exact (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_ball)
      (hμs := measure_ball_ne_top) (c := (1 : 𝕜))).symm
  have hnu : 0 < ‖u‖ := by
    dsimp [u]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul]
    exact Real.rpow_pos_of_pos (ENNReal.toReal_pos
      (Metric.measure_ball_pos volume (0 : Space d) zero_lt_one).ne' measure_ball_ne_top) _
  have hlimf : Tendsto
      (fun n : ℕ => average f (fun y => ((n : ℝ) + 1)⁻¹ • y) u) atTop (𝓝 0) := by
    simpa only [hz, zero_smul] using average_dilated_tendsto hf u
  have hle := le_of_tendsto_of_tendsto
    (average_dilated_tendsto hTf u).norm (tendsto_const_nhds.mul hlimf.norm)
    (Eventually.of_forall (fun n : ℕ => average_dilated_norm_bound T
      ((n : ℝ) + 1) (by positivity) f u hf hu hTf))
  have hzero : ‖(∫ x, T.operator f x) • u‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    simpa only [norm_zero, mul_zero] using hle
  rw [norm_smul, mul_eq_zero] at hzero
  exact norm_eq_zero.mp (hzero.resolve_right hnu.ne')

end SpatialCancellation

/-- Atom cancellation for the original C¹ operator, over either scalar field
and in every dimension. Only translation invariance, L² boundedness and the
already established integrability of the atom image are needed here. -/
theorem atom_cancellation : AtomCancellation := by
  intro 𝕜 _ d T a h2
  obtain ⟨_, hi, _⟩ := Hardy.HardyCZEndpoint.atom_estimate 𝕜 d T a
  refine ⟨hi, ?_⟩
  apply SpatialCancellation.integral_zero_of_translation_invariant T (h2.toLp a.val)
    ((MeasureTheory.L1.integrable_coeFn a.val).congr h2.coeFn_toLp.symm) hi
  exact (integral_congr_ae h2.coeFn_toLp).trans a.property.1

theorem atom_molecule : AtomMolecule := atom_molecule_of_cancellation atom_cancellation

theorem atom_bound : CzHardyInvarianceSpec.AtomBound := atom_bound_of_cancellation atom_cancellation

theorem invariance : Invariance := invariance_of_atom_bound atom_bound

end ExpandedFA.PartIV.CzHardyInvariance
