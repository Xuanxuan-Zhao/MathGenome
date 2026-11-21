import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyCommutant
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyDisk

/-! The shift commutant on the canonical disk H².

The polynomial identity is extended using continuous point evaluation and
polynomial density. Testing the resulting functional identity proves boundedness
of T1; the already proved Hardy-space multiplier construction supplies the
other norm inequality. No boundedness or multiplier certificate for T1 is assumed. -/
noncomputable section
open scoped ComplexConjugate

namespace ExpandedFA.PartIV.HardyCommutant
open HardyDiskSpec HardyCommutantSpec
open HardyDisk (monomial_evaluation shift_zero shift_succ geometricSequence
  geometricSequence_norm shift_evaluation evaluationMap polynomial_density
  evaluation_injective bounded_multiplier multiplier
  multiplierVector_eval zeroExtend_apply analytic_evaluation)

private abbrev monomial (n : ℕ) : H2 := lp.single 2 n (1 : ℂ)

private theorem eval_one (z : ℂ) : eval (monomial 0) z = 1 := by
  simpa using monomial_evaluation 0 1 z

private theorem shift_monomial (n : ℕ) : shift (monomial n) = monomial (n + 1) := by
  apply lp.ext
  funext k
  cases k with
  | zero => simp [monomial, shift_zero, lp.single_apply]
  | succ k => simp [monomial, shift_succ, lp.single_apply, Pi.single_apply]

/-- The geometric coefficient vector is the actual Szegő reproducing kernel. -/
theorem reproducing_kernel : ReproducingKernel := by
  intro z
  have hz : conj z.val ∈ disk := by
    simpa only [HardyDiskSpec.disk, Metric.mem_ball, dist_zero_right, Complex.norm_conj] using z.property
  let k := geometricSequence ⟨conj z.val, hz⟩
  refine ⟨k, fun n => rfl, ?_, ?_⟩
  · intro f
    simp only [lp.inner_eq_tsum, RCLike.inner_apply, k, geometricSequence,
      map_pow, Complex.conj_conj]
    change (∑' n : ℕ, f n * z.val ^ n) = eval f z
    rfl
  · simpa only [k, Complex.norm_conj] using geometricSequence_norm ⟨conj z.val, hz⟩

/-- On each monomial the operator is already multiplication by its value on 1. -/
theorem monomial_action (T : H2 →L[ℂ] H2) (hT : CommutesWithShift T)
    (n : ℕ) (z : Disk) :
    eval (T (monomial n)) z = eval (T (monomial 0)) z * z.val ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← shift_monomial, hT, shift_evaluation _ _ z.property, ih, pow_succ]
    ring

/-- Equality of the two bounded evaluation functionals follows from their
polynomial action and the density of the monomials. -/
theorem evaluation_intertwining (T : H2 →L[ℂ] H2) (hT : CommutesWithShift T)
    (z : Disk) :
    (evaluationMap z).comp T = eval (T (monomial 0)) z • evaluationMap z := by
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr polynomial_density)
  rintro _ ⟨n, rfl⟩
  change eval (T (monomial n)) z = eval (T (monomial 0)) z * eval (monomial n) z
  rw [monomial_action T hT n z, monomial_evaluation]
  simp

theorem extension_from_polynomials : ExtensionFromPolynomials := by
  intro T hT f z
  exact DFunLike.congr_fun (evaluation_intertwining T hT z) f

theorem polynomial_action : PolynomialAction := by
  intro T hT f _ z
  exact extension_from_polynomials T hT f z

private theorem evaluationMap_ne_zero (z : Disk) : evaluationMap z ≠ 0 := by
  intro h
  have he := DFunLike.congr_fun h (monomial 0)
  change eval (monomial 0) z = 0 at he
  rw [eval_one] at he
  exact one_ne_zero he

/-- A nonzero bounded evaluation functional detects the pointwise multiplier
value. Cancellation of its positive norm is the dual form of kernel testing. -/
theorem norm_bound_of_evaluation_identity (T : H2 →L[ℂ] H2) (z : Disk) (c : ℂ)
    (h : (evaluationMap z).comp T = c • evaluationMap z) : ‖c‖ ≤ ‖T‖ := by
  have hp : 0 < ‖evaluationMap z‖ := norm_pos_iff.mpr (evaluationMap_ne_zero z)
  have hn := (evaluationMap z).opNorm_comp_le T
  rw [h, norm_smul] at hn
  nlinarith

theorem pointwise_norm_bound : PointwiseNormBound := by
  intro T b h z
  apply norm_bound_of_evaluation_identity T z (b.val z)
  ext f
  exact h f z

theorem kernel_test : KernelTest := by
  intro T b h z
  obtain ⟨k, hk, hrep, _⟩ := reproducing_kernel z
  refine ⟨k, hk, ?_, ?_⟩
  · intro he
    have hone := hrep (monomial 0)
    rw [he, inner_zero_left, eval_one] at hone
    exact zero_ne_one hone
  · apply ext_inner_right ℂ
    intro f
    rw [ContinuousLinearMap.adjoint_inner_left, hrep, h f z, inner_smul_left,
      hrep, Complex.conj_conj]

theorem multiplier_norm_upper : MultiplierNormUpper := bounded_multiplier

theorem multiplier_norm_lower : MultiplierNormLower := by
  intro T b h
  have : Nonempty Disk := ⟨⟨0, by simp [disk]⟩⟩
  exact ciSup_le (fun z => pointwise_norm_bound T b h z)

/-- Any operator with the specified analytic multiplication action equals the
canonical multiplier, by injectivity of analytic evaluation. -/
theorem eq_multiplier (T : H2 →L[ℂ] H2) (b : HInfinity) (h : IsMultiplication T b) :
    T = multiplier b := by
  apply ContinuousLinearMap.ext
  intro f
  apply evaluation_injective
  intro z hz
  calc
    eval (T f) z = b.val ⟨z, hz⟩ * eval f z := h f ⟨z, hz⟩
    _ = zeroExtend b.val z * eval f z := by
      rw [zeroExtend_apply b.val ⟨z, hz⟩]
    _ = eval (multiplier b f) z := (multiplierVector_eval b f hz).symm

theorem multiplier_norm : MultiplierNorm := by
  intro T b h
  apply le_antisymm
  · obtain ⟨M, hM, hnorm⟩ := multiplier_norm_upper b
    rw [eq_multiplier T b h, ← eq_multiplier M b hM]
    exact hnorm
  · exact multiplier_norm_lower T b h

/-- The symbol is T1. Holomorphy comes from H² evaluation, and its boundedness
is proved from commutation, rather than included as an assumed certificate. -/
def commutantSymbol (T : H2 →L[ℂ] H2) (hT : CommutesWithShift T) : HInfinity :=
  ⟨fun z => eval (T (monomial 0)) z, by
    constructor
    · apply (analytic_evaluation (T (monomial 0))).differentiableOn.congr
      intro z hz
      exact zeroExtend_apply (fun w : Disk => eval (T (monomial 0)) w) ⟨z, hz⟩
    · refine ⟨‖T‖, fun z => ?_⟩
      exact norm_bound_of_evaluation_identity T z _ (evaluation_intertwining T hT z)⟩

theorem shift_commutant : ShiftCommutant := by
  intro T hT
  let b := commutantSymbol T hT
  have hb : IsMultiplication T b := extension_from_polynomials T hT
  refine ⟨b, ⟨hb, multiplier_norm T b hb⟩, ?_⟩
  intro c hc
  apply Subtype.ext
  funext z
  have he := hc.1 (monomial 0) z
  rw [eval_one, mul_one] at he
  exact he.symm

theorem multiplier_commutes : MultiplierCommutes := by
  intro T b h f
  apply evaluation_injective
  intro z hz
  rw [h (shift f) ⟨z, hz⟩, shift_evaluation _ _ hz,
    shift_evaluation _ _ hz, h f ⟨z, hz⟩]
  ring

end ExpandedFA.PartIV.HardyCommutant
