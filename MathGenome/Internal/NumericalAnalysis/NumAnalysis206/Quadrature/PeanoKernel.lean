import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.PeanoKernel
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.IntervalTaylor
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-! Peano kernel representation (paper.tex:2077–2119, W55).
We lift the upstream interval Taylor formula to `C([a,b], ℝ)`, commute its
Bochner integral with an arbitrary continuous linear functional, and bound
the scalar integral using the uniform norm of the supplied final derivative.
No regularity outside the interval is used for the represented function. -/
namespace NumAnalysis206.Quadrature
open Set
open scoped BigOperators
open NumAnalysis206.Approximation

abbrev IntervalSpace := PeanoKernelSpec.IntervalSpace
noncomputable abbrev intervalPolynomial := @PeanoKernelSpec.polynomialValue
abbrev AnnihilatesPolynomials := @PeanoKernelSpec.annihilatesValue
noncomputable abbrev peanoSlice := @PeanoKernelSpec.sliceValue
noncomputable abbrev peanoKernel := @PeanoKernelSpec.kernelValue

variable {a b : ℝ} {r : ℕ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ}

/-- Joint continuity of the truncated powers, in the uniform norm on the interval. -/
theorem continuous_peanoSlice (r : ℕ) : Continuous (peanoSlice (a := a) (b := b) r) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ × Icc a b =>
    max ((p.2 : ℝ) - p.1) 0 ^ (r - 1) / ((r - 1).factorial : ℝ))
  fun_prop

theorem continuous_peanoKernel (E : IntervalSpace a b →L[ℝ] ℝ) (r : ℕ) :
    Continuous (peanoKernel E r) := E.continuous.comp (continuous_peanoSlice r)

/-- The Taylor polynomial, as an element of the continuous-function space. -/
noncomputable def peanoTaylor (D : ℕ → ℝ → ℝ) (r : ℕ) (a b : ℝ) : IntervalSpace a b :=
  ∑ k ∈ Finset.range r, (D k a / (k.factorial : ℝ)) •
    intervalPolynomial ((Polynomial.X - Polynomial.C a) ^ k)

private theorem peanoTaylor_apply (D : ℕ → ℝ → ℝ) (r : ℕ) (x : Icc a b) :
    peanoTaylor D r a b x = jetTaylorSum D r a x := by
  simp only [peanoTaylor, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    intervalPolynomial, PeanoKernelSpec.polynomialValue, ContinuousMap.coe_mk,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    smul_eq_mul, jetTaylorSum, IntervalTaylorSpec.sumValue]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem annihilates_peanoTaylor (E : IntervalSpace a b →L[ℝ] ℝ)
    (hE : AnnihilatesPolynomials E r) : E (peanoTaylor D r a b) = 0 := by
  simp only [peanoTaylor, map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro k hk
  have hp : ((Polynomial.X - Polynomial.C a) ^ k).degree < (r : WithBot ℕ) := by
    simpa [Polynomial.degree_pow, Polynomial.degree_X_sub_C] using
      (show (k : WithBot ℕ) < (r : WithBot ℕ) from
        WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hk))
  rw [hE _ hp, smul_zero]

/-- Taylor's identity holds in the Banach space, so any bounded functional may be applied. -/
private theorem peanoTaylor_identity (hab : a ≤ b) (hr : 2 ≤ r)
    (hD : IntervalJet a b r f D) :
    PeanoKernelSpec.functionValue hD = peanoTaylor D r a b +
      ∫ t in a..b, D r t • peanoSlice (a := a) (b := b) r t := by
  have hInt : IntervalIntegrable (fun t => D r t • peanoSlice (a := a) (b := b) r t)
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact (hD.2.1 r le_rfl).smul (continuous_peanoSlice r).continuousOn
  ext x
  have heval := (ContinuousMap.evalCLM ℝ x).intervalIntegral_comp_comm hInt
  change (∫ t in a..b, (D r t • peanoSlice r t) x) =
    (∫ t in a..b, D r t • peanoSlice (a := a) (b := b) r t) x at heval
  simp only [ContinuousMap.add_apply, peanoTaylor_apply, ← heval]
  have htaylor := jet_taylor_positive_part hab hr hD x.property
  change f x = jetTaylorSum D r a x + _
  convert htaylor using 1
  apply congrArg (fun z : ℝ => jetTaylorSum D r a x + z)
  apply intervalIntegral.integral_congr
  intro t ht
  change D r t * (max ((x : ℝ) - t) 0 ^ (r - 1) / ((r - 1).factorial : ℝ)) = _
  ring

/-- Peano representation for an arbitrary bounded real linear functional. -/
theorem peano_representation (E : IntervalSpace a b →L[ℝ] ℝ)
    (hab : a < b) (hr : 2 ≤ r) (hE : AnnihilatesPolynomials E r)
    (hD : IntervalJet a b r f D) :
    E (PeanoKernelSpec.functionValue hD) = ∫ t in a..b, D r t * peanoKernel E r t := by
  have hInt : IntervalIntegrable (fun t => D r t • peanoSlice (a := a) (b := b) r t)
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab.le]
    exact (hD.2.1 r le_rfl).smul (continuous_peanoSlice r).continuousOn
  rw [peanoTaylor_identity hab.le hr hD, map_add, annihilates_peanoTaylor E hE, zero_add,
    ← E.intervalIntegral_comp_comm hInt]
  apply intervalIntegral.integral_congr
  intro t ht
  exact E.map_smul (D r t) (peanoSlice r t)

/-- The uniform-derivative estimate in the Peano theorem. -/
theorem peano_bound (E : IntervalSpace a b →L[ℝ] ℝ)
    (hab : a < b) (hr : 2 ≤ r) (hE : AnnihilatesPolynomials E r)
    (hD : IntervalJet a b r f D) :
    |E (PeanoKernelSpec.functionValue hD)| ≤
      ‖PeanoKernelSpec.derivativeValue hD‖ * ∫ t in a..b, |peanoKernel E r t| := by
  rw [peano_representation E hab hr hE hD]
  have hK := continuous_peanoKernel E r
  have hi : IntervalIntegrable (fun t => |D r t * peanoKernel E r t|)
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab.le]
    exact ((hD.2.1 r le_rfl).mul hK.continuousOn).abs
  have hj : IntervalIntegrable
      (fun t => ‖PeanoKernelSpec.derivativeValue hD‖ * |peanoKernel E r t|)
      MeasureTheory.volume a b := (continuous_const.mul hK.abs).intervalIntegrable _ _
  calc
    |∫ t in a..b, D r t * peanoKernel E r t| ≤
        ∫ t in a..b, |D r t * peanoKernel E r t| :=
      intervalIntegral.abs_integral_le_integral_abs hab.le
    _ ≤ ∫ t in a..b, ‖PeanoKernelSpec.derivativeValue hD‖ * |peanoKernel E r t| := by
      apply intervalIntegral.integral_mono_on hab.le hi hj
      intro t ht
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        ((PeanoKernelSpec.derivativeValue hD).norm_coe_le_norm ⟨t, ht⟩) (abs_nonneg _)
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- The total signed mass is the error on the normalized degree-`r` monomial. -/
theorem peano_moment (E : IntervalSpace a b →L[ℝ] ℝ)
    (hab : a < b) (hr : 2 ≤ r) (hE : AnnihilatesPolynomials E r) :
    E (intervalPolynomial (Polynomial.C ((r.factorial : ℝ)⁻¹) * Polynomial.X ^ r)) =
      ∫ t in a..b, peanoKernel E r t := by
  let g : ℝ → ℝ := fun x => x ^ r / (r.factorial : ℝ)
  have hg : ContDiff ℝ r g := by dsimp [g]; fun_prop
  have hJ := jet_of_contDiff hab hg.contDiffOn
  have htop (t : ℝ) (ht : t ∈ Icc a b) : iteratedDerivWithin r g (Icc a b) t = 1 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hg.contDiffAt ht]
    simp [g, iteratedDeriv_div_const, iteratedDeriv_pow, Nat.descFactorial_self,
      Nat.factorial_ne_zero]
  have heq : PeanoKernelSpec.functionValue hJ =
      intervalPolynomial (Polynomial.C ((r.factorial : ℝ)⁻¹) * Polynomial.X ^ r) := by
    ext x
    change (x : ℝ) ^ r / (r.factorial : ℝ) =
      (Polynomial.C ((r.factorial : ℝ)⁻¹) * Polynomial.X ^ r).eval (x : ℝ)
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring
  rw [← heq, peano_representation E hab hr hE hJ]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab.le] at ht
  dsimp only
  rw [htop t ht, one_mul]

/-- For either constant sign, the absolute mass is exactly the monomial error. -/
theorem peano_mass (E : IntervalSpace a b →L[ℝ] ℝ)
    (hab : a < b) (hr : 2 ≤ r) (hE : AnnihilatesPolynomials E r)
    (hsign : (∀ t ∈ Icc a b, 0 ≤ peanoKernel E r t) ∨
      (∀ t ∈ Icc a b, peanoKernel E r t ≤ 0)) :
    (∫ t in a..b, |peanoKernel E r t|) =
      |E (intervalPolynomial (Polynomial.C ((r.factorial : ℝ)⁻¹) * Polynomial.X ^ r))| := by
  rw [peano_moment E hab hr hE]
  rcases hsign with hpos | hneg
  · rw [abs_of_nonneg (intervalIntegral.integral_nonneg hab.le hpos)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab.le] at ht
    exact abs_of_nonneg (hpos t ht)
  · have hn : (∫ t in a..b, peanoKernel E r t) ≤ 0 := by
      have hp := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) hab.le
        (fun t ht => neg_nonneg.mpr (hneg t ht))
      rw [intervalIntegral.integral_neg] at hp
      exact neg_nonneg.mp hp
    rw [abs_of_nonpos hn, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab.le] at ht
    exact abs_of_nonpos (hneg t ht)

/-- Integration on the interval is bounded for the uniform norm. -/
private theorem integral_interval_bound (hab : a ≤ b) (F : IntervalSpace a b) :
    ‖∫ t in a..b, F (projIcc a b hab t)‖ ≤ (b - a) * ‖F‖ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (fun t _ => F.norm_coe_le_norm (projIcc a b hab t))
  simpa [abs_of_nonneg (sub_nonneg.mpr hab), mul_comm] using h

/-- Integration, minus any finite real weighted sum of point evaluations,
constructs a bounded linear functional. The empty sum is allowed. -/
theorem exists_quadratureError (hab : a ≤ b) {ι : Type*} (s : Finset ι)
    (nodes : ι → Icc a b) (weights : ι → ℝ) :
    ∃ E : IntervalSpace a b →L[ℝ] ℝ,
      (∀ F, E F = PeanoKernelSpec.quadratureValue hab s nodes weights F) ∧
      ‖E‖ ≤ (b - a) + ∑ i ∈ s, |weights i| := by
  classical
  have hi (F : IntervalSpace a b) :
      IntervalIntegrable (fun t => F (projIcc a b hab t)) MeasureTheory.volume a b :=
    (F.continuous.comp continuous_projIcc).intervalIntegrable _ _
  let I : IntervalSpace a b →ₗ[ℝ] ℝ :=
    { toFun := fun F => ∫ t in a..b, F (projIcc a b hab t)
      map_add' := fun F G => intervalIntegral.integral_add (hi F) (hi G)
      map_smul' := fun c F => by
        simpa only [RingHom.id_apply, ContinuousMap.smul_apply, smul_eq_mul] using
          intervalIntegral.integral_const_mul c (fun t => F (projIcc a b hab t)) }
  let J : IntervalSpace a b →L[ℝ] ℝ := I.mkContinuous (b - a) (integral_interval_bound hab)
  let E : IntervalSpace a b →L[ℝ] ℝ :=
    J - ∑ i ∈ s, weights i • ContinuousMap.evalCLM ℝ (nodes i)
  refine ⟨E, ?_, ?_⟩
  · intro F
    simp [E, J, I, PeanoKernelSpec.quadratureValue]
  · apply E.opNorm_le_bound
    · exact add_nonneg (sub_nonneg.mpr hab) (Finset.sum_nonneg fun i _ => abs_nonneg _)
    intro F
    change ‖J F - (∑ i ∈ s, weights i • ContinuousMap.evalCLM ℝ (nodes i)) F‖ ≤ _
    calc
      _ ≤ ‖J F‖ + ‖(∑ i ∈ s, weights i • ContinuousMap.evalCLM ℝ (nodes i)) F‖ :=
        norm_sub_le _ _
      _ ≤ (b - a) * ‖F‖ + (∑ i ∈ s, |weights i|) * ‖F‖ := by
        apply add_le_add (integral_interval_bound hab F)
        simp only [sum_apply, smul_apply,
          ContinuousMap.evalCLM_apply, smul_eq_mul]
        calc
          ‖∑ i ∈ s, weights i * F (nodes i)‖ ≤ ∑ i ∈ s, ‖weights i * F (nodes i)‖ :=
            norm_sum_le _ _
          _ ≤ ∑ i ∈ s, |weights i| * ‖F‖ := by
            apply Finset.sum_le_sum
            intro i hi
            rw [norm_mul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (F.norm_coe_le_norm _) (abs_nonneg _)
          _ = _ := (Finset.sum_mul _ _ _).symm
      _ = _ := (add_mul _ _ _).symm

end NumAnalysis206.Quadrature
