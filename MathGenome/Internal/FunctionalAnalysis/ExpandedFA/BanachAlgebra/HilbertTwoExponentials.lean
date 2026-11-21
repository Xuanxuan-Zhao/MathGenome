import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.HilbertTwoExponentials
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.ExponentialComponent
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.BorelNormSpectrum
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.PolarDecomposition
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder

noncomputable section
open Set Filter
open scoped Topology
namespace ExpandedFA.BanachAlgebra.HilbertTwoExponentials
open SpectralMeasure SpectralMeasure.BorelNormSpectrum
universe u v

variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Uniform convergence of bounded Borel functions passes to operator norm. -/
lemma spectralIntegral_tendstoUniformly (E : ProjectionValuedMeasure S H)
    {f : S → ℂ} {a : ℕ → S → ℂ} (hf : BM f) (ha : ∀ n, BM (a n))
    (ht : TendstoUniformly a f atTop) :
    Tendsto (fun n => E.spectralIntegral (a n)) atTop (𝓝 (E.spectralIntegral f)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp ht (ε / 2) (by positivity)] with n hn
  rw [dist_comm, dist_eq_norm, ← integral_sub E hf (ha n)]
  exact (E.spectralIntegral_norm_le _ (bounded_sub hf (ha n)) (ε / 2)
    (by positivity) (fun s => (by simpa [dist_eq_norm] using (hn s).le))).trans_lt
      (by linarith)

lemma bounded_pow {f : S → ℂ} (hf : BM f) (n : ℕ) : BM (f ^ n) := by
  induction n with
  | zero =>
    convert (bounded_const (S := S) 1) using 1
    ext s
    simp
  | succ n ih => simpa only [pow_succ] using ih.mul hf

lemma spectralIntegral_pow (E : ProjectionValuedMeasure S H)
    {f : S → ℂ} (hf : BM f) (n : ℕ) :
    E.spectralIntegral (f ^ n) = E.spectralIntegral f ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    convert E.spectralIntegral_one using 1
  | succ n ih => rw [pow_succ, E.spectralIntegral_mul _ _ (bounded_pow hf n) hf, ih, pow_succ]

lemma bounded_sum {ι : Type*} (t : Finset ι) (f : ι → S → ℂ)
    (hf : ∀ i ∈ t, BM (f i)) : BM (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    convert (bounded_const (S := S) 0) using 1
    ext s
    simp
  | @insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma spectralIntegral_sum (E : ProjectionValuedMeasure S H)
    {ι : Type*} (t : Finset ι) (f : ι → S → ℂ) (hf : ∀ i ∈ t, BM (f i)) :
    E.spectralIntegral (∑ i ∈ t, f i) = ∑ i ∈ t, E.spectralIntegral (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    convert (integral_const E 0) using 1
    simp
  | @insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      E.spectralIntegral_add _ _ (hf i (Finset.mem_insert_self _ _))
        (bounded_sum t f (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

/-- The Borel calculus commutes with the exponential power series. -/
lemma spectralIntegral_exp (E : ProjectionValuedMeasure S H)
    {f : S → ℂ} (hf : BM f) :
    E.spectralIntegral (fun s => Complex.exp (f s)) = NormedSpace.exp (E.spectralIntegral f) := by
  obtain ⟨R, hR0, hR⟩ := hf.nonneg_bound
  let F : ℕ → S → ℂ := fun N =>
    ∑ n ∈ Finset.range N, (n.factorial : ℂ)⁻¹ • f ^ n
  have hF (N : ℕ) : BM (F N) :=
    bounded_sum _ _ (fun n _ => (bounded_pow hf n).smul _)
  have he : BM (fun s => Complex.exp (f s)) := by
    refine ⟨Complex.continuous_exp.measurable.comp hf.1, Real.exp R, fun s => ?_⟩
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (hR s))
  have ht : TendstoUniformly F (fun s => Complex.exp (f s)) atTop := by
    have hs := tendstoUniformlyOn_tsum_nat (Real.summable_pow_div_factorial R)
      (f := fun n s => (n.factorial : ℂ)⁻¹ * f s ^ n) (s := Set.univ) (by
        intro n s _
        simp only [norm_mul, norm_inv, norm_natCast, norm_pow]
        calc
          (n.factorial : ℝ)⁻¹ * ‖f s‖ ^ n ≤ (n.factorial : ℝ)⁻¹ * R ^ n :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hR s) n)
              (by positivity)
          _ = R ^ n / (n.factorial : ℝ) := by rw [div_eq_mul_inv, mul_comm])
    rw [tendstoUniformlyOn_univ] at hs
    convert hs using 1
    · ext N s
      simp [F, Finset.sum_apply, smul_eq_mul]
    · ext s
      simp only [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum ℂ, smul_eq_mul]
  have hi := spectralIntegral_tendstoUniformly E he hF ht
  have hterm (N : ℕ) : E.spectralIntegral (F N) =
      ∑ n ∈ Finset.range N, (n.factorial : ℂ)⁻¹ • E.spectralIntegral f ^ n := by
    rw [spectralIntegral_sum E _ _ (fun n _ => (bounded_pow hf n).smul _)]
    apply Finset.sum_congr rfl
    intro n _
    rw [E.spectralIntegral_smul _ _ (bounded_pow hf n), spectralIntegral_pow E hf n]
  simp_rw [hterm] at hi
  let : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℚ) (E.spectralIntegral f)).tendsto_sum_nat
  have hs' : Tendsto (fun N => ∑ n ∈ Finset.range N,
      (n.factorial : ℂ)⁻¹ • E.spectralIntegral f ^ n) atTop
      (𝓝 (NormedSpace.exp (E.spectralIntegral f))) := by
    simpa only [inv_natCast_smul_eq ℚ ℂ] using hs
  exact tendsto_nhds_unique hi hs'

/-- A Borel argument on the unit circle supplies a bounded self-adjoint
logarithm even when the spectrum is the whole circle. -/
lemma unitary_logarithm (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H)) :
    ∃ B : H →L[ℂ] H, IsSelfAdjoint B ∧ NormedSpace.exp (Complex.I • B) = U := by
  obtain ⟨E, hE, _⟩ := NormalPVM.normal_spectral_theorem H U
    (isStarNormal_of_mem_unitary hU)
  let f : spectrum ℂ U → ℂ := fun z => (Complex.arg (z : ℂ) : ℂ)
  have hf : BM f := by
    refine ⟨Complex.measurable_ofReal.comp (Complex.measurable_arg.comp measurable_subtype_coe),
      Real.pi, fun z => ?_⟩
    simpa only [f, Complex.norm_real, Real.norm_eq_abs] using Complex.abs_arg_le_pi (z : ℂ)
  have hself : IsSelfAdjoint (E.spectralIntegral f) := by
    change star (E.spectralIntegral f) = E.spectralIntegral f
    rw [← E.spectralIntegral_star f hf]
    congr 1
    ext z
    simp [f]
  refine ⟨E.spectralIntegral f, hself, ?_⟩
  rw [← E.spectralIntegral_smul _ _ hf, ← spectralIntegral_exp E (hf.smul Complex.I)]
  have heq : (fun z : spectrum ℂ U => Complex.exp ((Complex.I • f) z)) =
      (fun z : spectrum ℂ U => (z : ℂ)) := by
    funext z
    have hn := spectrum.norm_eq_one_of_unitary hU z.property
    simpa only [Pi.smul_apply, smul_eq_mul, f, mul_comm Complex.I,
      hn, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I (z : ℂ)
  rw [heq]
  exact NormalPVM.continuousIntegral_coordinate E hE

/-- Polar decomposition and the two logarithms give the specified ordered
product, with both exponents coming from self-adjoint operators. -/
theorem two_exponentials : Spec.TwoExponentials.{v} := by
  intro H _ _ _ T
  let t : H ≃L[ℂ] H := ContinuousLinearEquiv.unitsEquiv ℂ H T
  obtain ⟨U, hU, _⟩ := PolarDecomposition.polar_decomposition ℂ H H t.toContinuousLinearMap
  obtain ⟨e, he⟩ := PolarDecomposition.invertible_unitary ℂ H H t U hU
  have hu : U ∈ unitary (H →L[ℂ] H) := by
    rw [← he]
    exact (Unitary.linearIsometryEquiv.symm e).property
  obtain ⟨B, hB, hBexp⟩ := unitary_logarithm U hu
  let P : H →L[ℂ] H := PolarDecomposition.Spec.modulusValue (T : H →L[ℂ] H)
  obtain ⟨hP, hP2, _⟩ := PolarDecomposition.modulus_properties ℂ H H (T : H →L[ℂ] H)
  have hPunit : IsUnit P := by
    apply ((Commute.refl P).isUnit_mul_iff.mp ?_).1
    change IsUnit (P.comp P)
    rw [hP2]
    exact T.isUnit.star.mul T.isUnit
  have hPpos : IsStrictlyPositive P :=
    hPunit.isStrictlyPositive (ContinuousLinearMap.nonneg_iff_isPositive.mpr hP)
  refine ⟨B, CFC.log P, hB, IsSelfAdjoint.log, ?_⟩
  rw [hBexp, CFC.exp_log P hPpos]
  exact hU.2.2.2.symm

/-- The continuous two-exponential parametrization is onto the invertible
operators, so their norm topology is path connected, also on the zero space. -/
theorem invertibles_path_connected : Spec.InvertiblesPathConnected.{v} := by
  intro H _ _ _
  let A := H →L[ℂ] H
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  let F : A × A → Aˣ := fun p => ExponentialComponent.expUnit p.1 * ExponentialComponent.expUnit p.2
  have hF : Continuous F :=
    (ExponentialComponent.continuous_expUnit.comp continuous_fst).mul
      (ExponentialComponent.continuous_expUnit.comp continuous_snd)
  have hsurj : Function.Surjective F := by
    intro T
    obtain ⟨B, C, _, _, hT⟩ := two_exponentials H T
    refine ⟨(Complex.I • B, C), Units.ext ?_⟩
    simpa only [F, Units.val_mul, ExponentialComponent.coe_expUnit] using hT.symm
  exact hsurj.pathConnectedSpace hF

end ExpandedFA.BanachAlgebra.HilbertTwoExponentials
