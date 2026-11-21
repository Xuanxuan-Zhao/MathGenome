import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Weyl.GaussianCorner
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Weyl.RegularWeylRepresentation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.L1FourierUniqueness
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-! The Gaussian integral is constructed on vectors. In particular the proof
does not integrate the Weyl operators in the operator norm topology. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
universe u

namespace ExpandedFA.Weyl
open RegularWeylRepresentationSpec GaussianCornerSpec

theorem gaussianWeight_pos {d : ℕ} (z : PhaseSpace d) : 0 < gaussianWeight z :=
  Real.exp_pos _

theorem gaussianWeight_continuous (d : ℕ) : Continuous (gaussianWeight (d := d)) := by
  unfold gaussianWeight phaseSquare
  fun_prop

@[simp] theorem gaussianWeight_zero {d : ℕ} : gaussianWeight (0 : PhaseSpace d) = 1 := by
  simp [gaussianWeight, phaseSquare]

@[simp] theorem gaussianWeight_neg {d : ℕ} (z : PhaseSpace d) :
    gaussianWeight (-z) = gaussianWeight z := by
  simp [gaussianWeight, phaseSquare]

theorem gaussianNormalization_eq_inv (d : ℕ) :
    gaussianNormalization d = ((2 * Real.pi) ^ d)⁻¹ := by
  simp [gaussianNormalization, zpow_neg]

theorem gaussianNormalization_pos (d : ℕ) : 0 < gaussianNormalization d := by
  rw [gaussianNormalization_eq_inv]
  positivity

theorem gaussianWeight_product {d : ℕ} (z : PhaseSpace d) :
    gaussianWeight z =
      (∏ j, Real.exp (-(1 / 4 : ℝ) * (z.1 j) ^ 2)) *
        ∏ j, Real.exp (-(1 / 4 : ℝ) * (z.2 j) ^ 2) := by
  unfold gaussianWeight phaseSquare
  simp only [← Real.exp_sum, ← Real.exp_add]
  congr 1
  simp only [← Finset.mul_sum]
  ring

theorem gaussianWeight_integrable : GaussianWeightIntegrable := by
  intro d
  have hi : Integrable (fun q : Configuration d =>
      ∏ j, Real.exp (-(1 / 4 : ℝ) * (q j) ^ 2)) :=
    Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq (by norm_num))
  exact (hi.mul_prod hi).congr (Filter.Eventually.of_forall fun z =>
    (gaussianWeight_product z).symm)

variable {d : ℕ} {H : Type u} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

theorem gaussianOrbit_continuous (R : RegularRepresentation d H) (x : H) :
    Continuous (fun z : PhaseSpace d => gaussianWeight z • R.W z x) :=
  (gaussianWeight_continuous d).smul (R.strong_continuous x)

theorem gaussianOrbit_norm (R : RegularRepresentation d H) (x : H) (z : PhaseSpace d) :
    ‖gaussianWeight z • R.W z x‖ = gaussianWeight z * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (gaussianWeight_pos z),
    (R.W z).norm_map]

theorem gaussianOrbit_integrable : GaussianOrbitIntegrable.{u} := by
  intro d H _ _ _ R x
  exact ((gaussianWeight_integrable d).mul_const ‖x‖).mono'
    (gaussianOrbit_continuous R x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => le_of_eq (gaussianOrbit_norm R x z))

theorem gaussianIntegral_bound : GaussianIntegralBound.{u} := by
  intro d H _ _ _ R x
  calc
    ‖gaussianVectorIntegral R x‖ =
        |gaussianNormalization d| * ‖∫ z : PhaseSpace d, gaussianWeight z • R.W z x‖ := by
      rw [gaussianVectorIntegral, norm_smul, Real.norm_eq_abs]
    _ ≤ |gaussianNormalization d| * ∫ z : PhaseSpace d, ‖gaussianWeight z • R.W z x‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (abs_nonneg _)
    _ = |gaussianNormalization d| * (∫ z : PhaseSpace d, gaussianWeight z) * ‖x‖ := by
      simp_rw [gaussianOrbit_norm]
      rw [integral_mul_const]
      ring

def gaussianIntegralLinearMap (R : RegularRepresentation d H) : H →ₗ[ℂ] H where
  toFun := gaussianVectorIntegral R
  map_add' x y := by
    simp only [gaussianVectorIntegral, map_add, smul_add]
    rw [integral_add (gaussianOrbit_integrable R x) (gaussianOrbit_integrable R y), smul_add]
  map_smul' c x := by
    simp only [gaussianVectorIntegral, map_smul, RingHom.id_apply]
    simp_rw [smul_comm (gaussianWeight _) c]
    rw [integral_smul]
    exact smul_comm _ _ _

/-- A bounded operator obtained from the vector integral and its norm estimate. -/
def gaussianProjection (R : RegularRepresentation d H) : H →L[ℂ] H :=
  (gaussianIntegralLinearMap R).mkContinuous
    (|gaussianNormalization d| * ∫ z : PhaseSpace d, gaussianWeight z)
    (gaussianIntegral_bound R)

theorem gaussianProjection_apply (R : RegularRepresentation d H) (x : H) :
    gaussianProjection R x = gaussianVectorIntegral R x := rfl

theorem gaussianOperator_exists : GaussianOperatorExists.{u} := by
  intro d H _ _ _ R
  exact ⟨gaussianProjection R, gaussianProjection_apply R⟩

theorem weyl_neg_cancel (R : RegularRepresentation d H) (z : PhaseSpace d) (x : H) :
    R.W z (R.W (-z) x) = x := by
  rw [R.mul, weylPhase_neg_right, add_neg_cancel, one_smul, R.zero]

theorem weyl_inner_inverse (R : RegularRepresentation d H) (z : PhaseSpace d) (x y : H) :
    inner ℂ (R.W z x) y = inner ℂ x (R.W (-z) y) := by
  calc
    inner ℂ (R.W z x) y = inner ℂ (R.W z x) (R.W z (R.W (-z) y)) :=
      congrArg (inner ℂ (R.W z x)) (weyl_neg_cancel R z y).symm
    _ = inner ℂ x (R.W (-z) y) := (R.W z).inner_map_map _ _

theorem phaseSpace_neg_measurePreserving (d : ℕ) :
    MeasurePreserving (fun z : PhaseSpace d => -z) := by
  exact (Measure.measurePreserving_neg (volume : Measure (Configuration d))).prod
    (Measure.measurePreserving_neg (volume : Measure (Configuration d)))

private theorem inner_integral_left {f : PhaseSpace d → H} (hf : Integrable f) (y : H) :
    inner ℂ (∫ z, f z) y = ∫ z, inner ℂ (f z) y := by
  calc
    inner ℂ (∫ z, f z) y = conj (inner ℂ y (∫ z, f z)) := (inner_conj_symm _ _).symm
    _ = ∫ z, inner ℂ (f z) y := by
      rw [← integral_inner hf, ← integral_conj]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => inner_conj_symm _ _)

theorem gaussianIntegral_symmetric (R : RegularRepresentation d H) (x y : H) :
    inner ℂ (gaussianVectorIntegral R x) y =
      inner ℂ x (gaussianVectorIntegral R y) := by
  simp only [gaussianVectorIntegral, inner_smul_left_eq_smul, inner_smul_right_eq_smul]
  congr 1
  rw [inner_integral_left (gaussianOrbit_integrable R x),
    ← integral_inner (gaussianOrbit_integrable R y)]
  calc
    (∫ z : PhaseSpace d, inner ℂ (gaussianWeight z • R.W z x) y) =
        ∫ z : PhaseSpace d, inner ℂ x (gaussianWeight (-z) • R.W (-z) y) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        dsimp only
        rw [inner_smul_left_eq_smul, inner_smul_right_eq_smul,
          gaussianWeight_neg, weyl_inner_inverse]
    _ = ∫ z : PhaseSpace d, inner ℂ x (gaussianWeight z • R.W z y) :=
      (phaseSpace_neg_measurePreserving d).integral_comp
        (MeasurableEquiv.neg (PhaseSpace d)).measurableEmbedding
        (fun z : PhaseSpace d => inner ℂ x (gaussianWeight z • R.W z y))

theorem gaussianIntegral_selfAdjoint : GaussianSelfAdjoint.{u} := by
  intro d H _ _ _ R P hP
  apply (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr ?_).adjoint_eq
  intro x y
  change inner ℂ (P x) y = inner ℂ x (P y)
  rw [hP, hP]
  exact gaussianIntegral_symmetric R x y

/-- The symplectic form identifies phase space with its real linear dual. -/
theorem symplectic_dual_surjective (ℓ : PhaseSpace d →ₗ[ℝ] ℝ) :
    ∃ w : PhaseSpace d, ∀ z, SymplecticFormValue w z = ℓ z := by
  classical
  have decomp (z : PhaseSpace d) :
      z = (∑ j, z.1 j • (Pi.single j (1 : ℝ), (0 : Configuration d))) +
        ∑ j, z.2 j • ((0 : Configuration d), Pi.single j (1 : ℝ)) := by
    ext j <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  refine ⟨(fun j => -ℓ (0, Pi.single j 1), fun j => ℓ (Pi.single j 1, 0)), ?_⟩
  intro z
  conv_rhs => rw [decomp z]
  simp only [map_add, map_sum, map_smul, smul_eq_mul]
  unfold SymplecticFormValue
  simp only [sub_neg_eq_add, mul_neg, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weyl_conjugation (R : RegularRepresentation d H) (w z : PhaseSpace d) (x : H) :
    R.W w (R.W z (R.W (-w) x)) =
      Complex.exp ((SymplecticFormValue w z : ℝ) * Complex.I) • R.W z x := by
  rw [R.mul, R.mul, smul_smul]
  have hp : WeylPhaseValue w z * WeylPhaseValue (w + z) (-w) =
      Complex.exp ((SymplecticFormValue w z : ℝ) * Complex.I) := by
    unfold WeylPhaseValue
    rw [← Complex.exp_add, ← add_mul, ← Complex.ofReal_add]
    congr 2
    unfold SymplecticFormValue
    simp only [Prod.fst_neg, Prod.snd_neg, Prod.fst_add, Prod.snd_add,
      Pi.neg_apply, Pi.add_apply, Finset.sum_div, ← Finset.sum_add_distrib]
    norm_cast
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hp]
  congr 2
  abel_nf

/-- Fourier uniqueness in the original phase-space coordinates. The auxiliary
Euclidean change of coordinates transports the measure as well as the function. -/
theorem symplectic_continuous_uniqueness (f : PhaseSpace d → ℂ)
    (hf : Integrable f) (hc : Continuous f)
    (hz : ∀ w : PhaseSpace d,
      (∫ z, Complex.exp ((SymplecticFormValue w z : ℝ) * Complex.I) * f z) = 0) :
    ∀ z, f z = 0 := by
  let n := Module.finrank ℝ (PhaseSpace d)
  let e : PhaseSpace d ≃L[ℝ] Fourier.Euclidean n :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  let em := e.toHomeomorph.toMeasurableEquiv
  let μ := Measure.map em (volume : Measure (PhaseSpace d))
  have : SigmaFinite μ := em.sigmaFinite_map
  have hi : Integrable (fun v => f (em.symm v)) μ := by
    rw [integrable_map_equiv]
    simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using hf
  have hzero : ∀ ξ, Fourier.weightedIntegralFourier μ (fun v => f (em.symm v)) ξ = 0 := by
    intro ξ
    let ℓ : PhaseSpace d →ₗ[ℝ] ℝ :=
      (-2 * Real.pi) • (innerₗ (Fourier.Euclidean n) ξ).comp e.toLinearMap
    obtain ⟨w, hw⟩ := symplectic_dual_surjective ℓ
    unfold Fourier.weightedIntegralFourier
    rw [integral_map_equiv]
    calc
      _ = ∫ z : PhaseSpace d,
          Complex.exp ((SymplecticFormValue w z : ℝ) * Complex.I) * f z := by
        apply integral_congr_ae
        filter_upwards [] with z
        simp only [MeasurableEquiv.symm_apply_apply]
        congr 2
        rw [hw]
        simp only [ℓ, LinearMap.smul_apply, LinearMap.comp_apply, innerₗ_apply_apply,
          smul_eq_mul]
        change -2 * (Real.pi : ℂ) * Complex.I * (inner ℝ (e z) ξ : ℝ) =
          ((-2 * Real.pi * inner ℝ ξ (e z) : ℝ) : ℂ) * Complex.I
        rw [real_inner_comm]
        push_cast
        ring
      _ = 0 := hz w
  have h := Fourier.Uniqueness.weighted_uniqueness n μ (fun v => f (em.symm v)) hi hzero
  have h' : f =ᵐ[volume] 0 := by
    have hh := em.measurableEmbedding.ae_map_iff.mp h
    filter_upwards [hh] with z hz
    simpa only [MeasurableEquiv.symm_apply_apply, Pi.zero_apply] using hz
  exact fun z => congrFun (Measure.eq_of_ae_eq h' hc continuous_zero) z

/-- The Gaussian average cannot vanish in a nonzero regular representation. -/
theorem gaussianProjection_ne_zero (R : RegularRepresentation d H) : gaussianProjection R ≠ 0 := by
  intro hP
  have hA (x : H) : (∫ z : PhaseSpace d, gaussianWeight z • R.W z x) = 0 := by
    have h := congrArg (fun T : H →L[ℂ] H => T x) hP
    change gaussianNormalization d • (∫ z : PhaseSpace d, gaussianWeight z • R.W z x) = 0 at h
    exact (smul_eq_zero.mp h).resolve_left (ne_of_gt (gaussianNormalization_pos d))
  let := R.nontrivial_space
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  let f : PhaseSpace d → ℂ := fun z => inner ℂ x (gaussianWeight z • R.W z x)
  have hf : Integrable f := (gaussianOrbit_integrable R x).const_inner x
  have hc : Continuous f := continuous_const.inner (gaussianOrbit_continuous R x)
  have hz (w : PhaseSpace d) :
      (∫ z, Complex.exp ((SymplecticFormValue w z : ℝ) * Complex.I) * f z) = 0 := by
    let L := (R.W w).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
    have hv : (∫ z : PhaseSpace d,
        L (gaussianWeight z • R.W z (R.W (-w) x))) = 0 := by
      rw [L.integral_comp_comm (gaussianOrbit_integrable R (R.W (-w) x)), hA, map_zero]
    calc
      _ = ∫ z : PhaseSpace d, inner ℂ x
          (L (gaussianWeight z • R.W z (R.W (-w) x))) := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [L.map_smul]
        change _ = inner ℂ x (gaussianWeight z • R.W w (R.W z (R.W (-w) x)))
        rw [weyl_conjugation]
        simp only [f, inner_smul_right_eq_smul, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
        ring
      _ = inner ℂ x (∫ z : PhaseSpace d,
          L (gaussianWeight z • R.W z (R.W (-w) x))) :=
        integral_inner (L.integrable_comp (gaussianOrbit_integrable R (R.W (-w) x))) x
      _ = 0 := by rw [hv, inner_zero_right]
  have h0 := symplectic_continuous_uniqueness f hf hc hz 0
  have hxx : inner ℂ x x = 0 := by simpa only [f, gaussianWeight_zero, R.zero, one_smul] using h0
  exact hx (inner_self_eq_zero.mp hxx)

/-- Scalar kernel after the Weyl change of variables r = z + w + v. -/
def gaussianCornerKernel (w r z : PhaseSpace d) : ℂ :=
  ((gaussianWeight z * gaussianWeight (r - w - z) : ℝ) : ℂ) *
    Complex.exp (((SymplecticFormValue z (r + w) + SymplecticFormValue w r) / 2 : ℝ) * Complex.I)

private def cornerLinearQ (w r : PhaseSpace d) (j : Fin d) : ℂ :=
  ((r.1 j - w.1 j : ℝ) : ℂ) / 2 - Complex.I * ((r.2 j + w.2 j : ℝ) : ℂ) / 2

private def cornerLinearP (w r : PhaseSpace d) (j : Fin d) : ℂ :=
  ((r.2 j - w.2 j : ℝ) : ℂ) / 2 + Complex.I * ((r.1 j + w.1 j : ℝ) : ℂ) / 2

private def quadraticGaussian (c : Fin d → ℂ) (q : Configuration d) : ℂ :=
  Complex.exp (-(1 / 2 : ℂ) * ∑ j, (q j : ℂ) ^ 2 + ∑ j, c j * q j)

private theorem gaussianCornerKernel_factor (w r z : PhaseSpace d) :
    gaussianCornerKernel w r z =
      Complex.exp (((-phaseSquare (r - w) / 4 : ℝ) : ℂ) +
        ((SymplecticFormValue w r / 2 : ℝ) : ℂ) * Complex.I) *
        (quadraticGaussian (cornerLinearQ w r) z.1 *
          quadraticGaussian (cornerLinearP w r) z.2) := by
  unfold gaussianCornerKernel gaussianWeight quadraticGaussian
  simp only [Complex.ofReal_mul, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  unfold phaseSquare SymplecticFormValue cornerLinearQ cornerLinearP
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Pi.sub_apply, Pi.add_apply]
  push_cast
  simp only [neg_add, add_div, add_mul, mul_add, sub_div, sub_mul,
    ← Finset.sum_neg_distrib, Finset.sum_div, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem corner_exponent (w r : PhaseSpace d) :
    (((-phaseSquare (r - w) / 4 : ℝ) : ℂ) +
      ((SymplecticFormValue w r / 2 : ℝ) : ℂ) * Complex.I) +
      ((∑ j, (cornerLinearQ w r j) ^ 2) / (4 * (1 / 2 : ℂ)) +
        (∑ j, (cornerLinearP w r j) ^ 2) / (4 * (1 / 2 : ℂ))) =
      ((-phaseSquare r / 4 - phaseSquare w / 4 : ℝ) : ℂ) := by
  unfold phaseSquare SymplecticFormValue cornerLinearQ cornerLinearP
  simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply]
  push_cast
  simp only [neg_add, add_div, mul_add, sub_div, sub_mul,
    ← Finset.sum_neg_distrib, Finset.sum_div, Finset.sum_mul,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The Gaussian twisted convolution with an intervening Weyl operator. -/
theorem gaussianCornerKernel_integral (w r : PhaseSpace d) :
    (∫ z : PhaseSpace d, gaussianCornerKernel w r z) =
      (((2 * Real.pi) ^ d * gaussianWeight r * gaussianWeight w : ℝ) : ℂ) := by
  simp_rw [gaussianCornerKernel_factor]
  rw [integral_const_mul, Measure.volume_eq_prod, integral_prod_mul]
  unfold quadraticGaussian
  rw [GaussianFourier.integral_cexp_neg_mul_sum_add (by norm_num : 0 < (1 / 2 : ℂ).re),
    GaussianFourier.integral_cexp_neg_mul_sum_add (by norm_num : 0 < (1 / 2 : ℂ).re)]
  simp only [Fintype.card_fin]
  have hn : (Real.pi : ℂ) / (1 / 2) ≠ 0 := div_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (by norm_num)
  calc
    _ = ((Real.pi : ℂ) / (1 / 2)) ^ ((d : ℂ) / 2 + (d : ℂ) / 2) *
        Complex.exp (((( -phaseSquare (r - w) / 4 : ℝ) : ℂ) +
          ((SymplecticFormValue w r / 2 : ℝ) : ℂ) * Complex.I) +
          ((∑ j, (cornerLinearQ w r j) ^ 2) / (4 * (1 / 2 : ℂ)) +
            (∑ j, (cornerLinearP w r j) ^ 2) / (4 * (1 / 2 : ℂ)))) := by
      simp only [Complex.cpow_add _ _ hn, Complex.exp_add]
      ring
    _ = (((2 * Real.pi) ^ d * gaussianWeight r * gaussianWeight w : ℝ) : ℂ) := by
      rw [corner_exponent]
      have hd : (d : ℂ) / 2 + (d : ℂ) / 2 = d := by ring
      rw [hd, Complex.cpow_natCast]
      simp only [gaussianWeight, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp,
        Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
      have hb : (Real.pi : ℂ) / (1 / 2) = 2 * Real.pi := by ring
      rw [hb, sub_eq_add_neg, Complex.exp_add]
      simp only [neg_div, mul_assoc]

private instance phaseSpace_volume_leftInvariant :
    (volume : Measure (PhaseSpace d)).IsAddLeftInvariant := by
  change ((volume : Measure (Configuration d)).prod volume).IsAddLeftInvariant
  infer_instance

private instance phaseSpace_volume_rightInvariant :
    (volume : Measure (PhaseSpace d)).IsAddRightInvariant := by
  change ((volume : Measure (Configuration d)).prod volume).IsAddRightInvariant
  infer_instance

theorem gaussianCornerKernel_continuous :
    Continuous (fun p : PhaseSpace d × PhaseSpace d × PhaseSpace d =>
      gaussianCornerKernel p.1 p.2.1 p.2.2) := by
  unfold gaussianCornerKernel gaussianWeight phaseSquare SymplecticFormValue
  fun_prop

theorem gaussianCornerKernel_norm (w r z : PhaseSpace d) :
    ‖gaussianCornerKernel w r z‖ = gaussianWeight z * gaussianWeight (r - w - z) := by
  simp only [gaussianCornerKernel, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one,
    abs_of_pos (gaussianWeight_pos z), abs_of_pos (gaussianWeight_pos (r - w - z))]

/-- Fubini is justified by a product of Gaussian norm bounds after a
measure-preserving shear. -/
theorem gaussianCorner_integrable (R : RegularRepresentation d H) (w : PhaseSpace d) (x : H) :
    Integrable (fun p : PhaseSpace d × PhaseSpace d =>
      gaussianCornerKernel w p.2 p.1 • R.W p.2 x) (volume.prod volume) := by
  have hm : MeasurePreserving
      (fun p : PhaseSpace d × PhaseSpace d => (p.1, p.2 - w - p.1))
      (volume.prod volume) (volume.prod volume) :=
    (measurePreserving_prod_sub volume volume).comp
      ((MeasurePreserving.id volume).prod (measurePreserving_sub_right volume w))
  have hi := hm.integrable_comp_of_integrable
    ((gaussianWeight_integrable d).mul_prod (gaussianWeight_integrable d))
  refine (hi.mul_const ‖x‖).mono' ?_ ?_
  · exact ((gaussianCornerKernel_continuous.comp
      (continuous_const.prodMk (continuous_snd.prodMk continuous_fst))).smul
      ((R.strong_continuous x).comp continuous_snd)).aestronglyMeasurable
  · filter_upwards [] with p
    simp only [norm_smul, gaussianCornerKernel_norm, (R.W p.2).norm_map,
      Function.comp_apply]
    exact le_rfl

theorem gaussianCorner_weyl_integrand (R : RegularRepresentation d H)
    (w z v : PhaseSpace d) (x : H) :
    gaussianWeight z • R.W z (R.W w (gaussianWeight v • R.W v x)) =
      gaussianCornerKernel w (z + w + v) z • R.W (z + w + v) x := by
  have hv : z + w + v - w - z = v := by abel
  have hp : WeylPhaseValue z w * WeylPhaseValue (z + w) v =
      Complex.exp (((SymplecticFormValue z (z + w + v + w) +
        SymplecticFormValue w (z + w + v)) / 2 : ℝ) * Complex.I) := by
    unfold WeylPhaseValue
    rw [← Complex.exp_add, ← add_mul, ← Complex.ofReal_add]
    congr 2
    norm_cast
    unfold SymplecticFormValue
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply,
      Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [← Complex.coe_smul, map_smul]
  rw [R.mul z w, R.mul (z + w) v]
  simp only [smul_smul]
  rw [gaussianCornerKernel, hv, Complex.ofReal_mul, ← hp]
  congr 1
  ring

/-- The unnormalized strong integral satisfies the full Gaussian corner law. -/
theorem gaussianIntegral_sandwich_unnormalized (R : RegularRepresentation d H)
    (w : PhaseSpace d) (x : H) :
    (∫ z : PhaseSpace d, gaussianWeight z • R.W z
      (R.W w (∫ v : PhaseSpace d, gaussianWeight v • R.W v x))) =
      ((2 * Real.pi) ^ d * gaussianWeight w) •
        (∫ r : PhaseSpace d, gaussianWeight r • R.W r x) := by
  calc
    _ = ∫ z : PhaseSpace d, ∫ v : PhaseSpace d,
        gaussianCornerKernel w (z + w + v) z • R.W (z + w + v) x := by
      apply integral_congr_ae
      filter_upwards [] with z
      let L := (R.W z).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (R.W w).toContinuousLinearEquiv.toContinuousLinearMap
      have hL := L.integral_comp_comm (gaussianOrbit_integrable R x)
      change (∫ v : PhaseSpace d, R.W z (R.W w (gaussianWeight v • R.W v x))) =
        R.W z (R.W w (∫ v : PhaseSpace d, gaussianWeight v • R.W v x)) at hL
      rw [← hL, ← integral_smul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => gaussianCorner_weyl_integrand R w z v x
    _ = ∫ z : PhaseSpace d, ∫ r : PhaseSpace d,
        gaussianCornerKernel w r z • R.W r x := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact integral_add_left_eq_self
        (fun r : PhaseSpace d => gaussianCornerKernel w r z • R.W r x) (z + w)
    _ = ∫ r : PhaseSpace d, ∫ z : PhaseSpace d,
        gaussianCornerKernel w r z • R.W r x :=
      integral_integral_swap (gaussianCorner_integrable R w x)
    _ = ∫ r : PhaseSpace d, ((2 * Real.pi) ^ d * gaussianWeight r * gaussianWeight w) • R.W r x := by
      apply integral_congr_ae
      filter_upwards [] with r
      rw [integral_smul_const, gaussianCornerKernel_integral, Complex.coe_smul]
    _ = ((2 * Real.pi) ^ d * gaussianWeight w) •
        (∫ r : PhaseSpace d, gaussianWeight r • R.W r x) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with r
      rw [smul_smul]
      congr 1
      ring

theorem gaussianProjection_sandwich (R : RegularRepresentation d H) (w : PhaseSpace d) :
    ((gaussianProjection R).comp
      (R.W w).toContinuousLinearEquiv.toContinuousLinearMap).comp (gaussianProjection R) =
      (gaussianWeight w : ℂ) • gaussianProjection R := by
  ext x
  let A : H → H := fun y => ∫ z : PhaseSpace d, gaussianWeight z • R.W z y
  let c := gaussianNormalization d
  change gaussianProjection R (R.W w (c • A x)) = (gaussianWeight w : ℂ) • (c • A x)
  calc
    _ = c • gaussianProjection R (R.W w (A x)) := by
      rw [← Complex.coe_smul c (A x), map_smul, map_smul, Complex.coe_smul]
    _ = c • c • A (R.W w (A x)) := rfl
    _ = c • c • (((2 * Real.pi) ^ d * gaussianWeight w) • A x) := by
      rw [show A (R.W w (A x)) = ((2 * Real.pi) ^ d * gaussianWeight w) • A x from
        gaussianIntegral_sandwich_unnormalized R w x]
    _ = (gaussianWeight w : ℂ) • (c • A x) := by
      rw [Complex.coe_smul]
      simp only [smul_smul]
      congr 1
      dsimp only [c]
      rw [gaussianNormalization_eq_inv]
      have hK : (2 * Real.pi) ^ d ≠ 0 := pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      field_simp

/-- The Gaussian strong integral is an orthogonal projection. -/
theorem gaussianProjection_idempotent (R : RegularRepresentation d H) :
    (gaussianProjection R).comp (gaussianProjection R) = gaussianProjection R := by
  have h := gaussianProjection_sandwich R 0
  ext x
  change gaussianProjection R (gaussianProjection R x) = gaussianProjection R x
  have hx := congrArg (fun T : H →L[ℂ] H => T x) h
  change gaussianProjection R (R.W 0 (gaussianProjection R x)) =
    (gaussianWeight (0 : PhaseSpace d) : ℂ) • gaussianProjection R x at hx
  simpa only [R.zero, gaussianWeight_zero, Complex.ofReal_one, one_smul] using hx

/-- The complete Gaussian corner construction in every regular Weyl representation. -/
theorem gaussian_corner : GaussianCorner.{u} := by
  intro d H _ _ _ R
  exact ⟨gaussianProjection R, gaussianProjection_apply R,
    gaussianIntegral_selfAdjoint R (gaussianProjection R) (gaussianProjection_apply R),
    gaussianProjection_idempotent R, gaussianProjection_sandwich R,
    gaussianProjection_ne_zero R⟩

end ExpandedFA.Weyl
