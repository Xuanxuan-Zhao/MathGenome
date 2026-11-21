import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.YosidaConstruction
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.LaplaceResolvent
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.GeneratorDeterminesSemigroup
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NoncommRing

/-! The zero-shift Hille–Yosida construction (paper.tex 14746–14781).
The proof uses the original resolvent inverses, proves strong approximation
by density, and obtains the common exponential bound from all resolvent powers.
A comparison derivative gives uniform Cauchy convergence on bounded intervals.
The resulting C₀ semigroup extends A by passage to the integrated identity;
a common positive resolvent point proves equality of the full generator domains.
-/

noncomputable section
open Filter Topology Set
open scoped NNReal

namespace ExpandedFA.Semigroups.YosidaConstruction
open YosidaConstructionSpec

variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- Use the actual two-sided inverse underlying the canonical resolvent. -/
theorem positiveResolvent_eq (A : Unbounded.Operator 𝕜 X X) (r : ℝ)
    (hr : Nonempty (Unbounded.ResolventInverse A (algebraMap ℝ 𝕜 r))) :
    positiveResolvent A r = hr.some.inverse := by
  simp only [positiveResolvent, Unbounded.OperatorDomainsSpec.resolventValue, dite_eq_left hr]

/-- The resolvent commutes with A on A's exact domain. -/
theorem scaledResolvent_sub (A : Unbounded.Operator 𝕜 X X) (r : ℝ)
    (hr : Nonempty (Unbounded.ResolventInverse A (algebraMap ℝ 𝕜 r))) (x : A.domain) :
    scaledResolvent A r x - (x : X) = positiveResolvent A r (A x) := by
  have h := hr.some.left_inverse x
  rw [map_sub, map_smul] at h
  rw [scaledResolvent, smul_apply, positiveResolvent_eq A r hr]
  exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp h).trans (add_comm _ _))

/-- The scalar-square form of the bounded Yosida approximant. -/
theorem approximant_formula : ApproximantFormula (𝕜 := 𝕜) (X := X) := by
  intro A r
  simp only [approximant, scaledResolvent, smul_sub, smul_smul, pow_two]

/-- Both displayed definitions of the bounded Yosida approximant agree. -/
theorem approximant_identity : ApproximantIdentity (𝕜 := 𝕜) (X := X) := by
  intro A r hr x
  have h := hr.some.right_inverse x
  change algebraMap ℝ 𝕜 r • (algebraMap ℝ 𝕜 r • positiveResolvent A r x - x) = _
  congr 1
  change _ = A ⟨hr.some.inverse x, hr.some.mem_domain x⟩
  rw [positiveResolvent_eq A r hr]
  exact (sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp h).trans (add_comm _ _)))

/-- On D(A), A_rx = rR(r,A)Ax. -/
theorem approximant_apply_domain (A : Unbounded.Operator 𝕜 X X) (r : ℝ)
    (hr : Nonempty (Unbounded.ResolventInverse A (algebraMap ℝ 𝕜 r))) (x : A.domain) :
    approximant A r x = scaledResolvent A r (A x) := by
  change algebraMap ℝ 𝕜 r • (scaledResolvent A r x - (x : X)) = _
  rw [scaledResolvent_sub A r hr x]
  rfl

/-- The resolvent estimates themselves force M ≥ 0, even on the zero space. -/
theorem constant_nonneg {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : ResolventEstimates A M) : 0 ≤ M := by
  have hb := h.2 1 zero_lt_one 0
  simpa only [zero_add, pow_one, one_pow, div_one] using (norm_nonneg _).trans hb

/-- Uniform boundedness of rR(r,A) uses just the first power estimate. -/
theorem norm_scaledResolvent_le {A : Unbounded.Operator 𝕜 X X} {M r : ℝ}
    (h : ResolventEstimates A M) (hr : 0 < r) : ‖scaledResolvent A r‖ ≤ M := by
  have hb : ‖positiveResolvent A r‖ ≤ M / r := by simpa using h.2 r hr 0
  rw [scaledResolvent, norm_smul, norm_algebraMap' 𝕜, Real.norm_eq_abs, abs_of_pos hr]
  calc
    r * ‖positiveResolvent A r‖ ≤ r * (M / r) := mul_le_mul_of_nonneg_left hb hr.le
    _ = M := mul_div_cancel₀ M hr.ne'

/-- The domain estimate giving strong convergence before the density step. -/
theorem norm_scaledResolvent_sub_le {A : Unbounded.Operator 𝕜 X X} {M r : ℝ}
    (h : ResolventEstimates A M) (hr : 0 < r) (x : A.domain) :
    ‖scaledResolvent A r x - (x : X)‖ ≤ (M / r) * ‖A x‖ := by
  rw [scaledResolvent_sub A r (h.1 r hr) x]
  exact ((positiveResolvent A r).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (by simpa using h.2 r hr 0) (norm_nonneg _))

/-- Strong convergence first on the original operator domain. -/
theorem scaledResolvent_tendsto_domain {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : ResolventEstimates A M) (x : A.domain) :
    Tendsto (fun r : ℝ => scaledResolvent A r x) atTop (𝓝 (x : X)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero_norm'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    simpa only [norm_norm] using norm_scaledResolvent_sub_le h hr x
  · have hz : Tendsto (fun r : ℝ => M / r * ‖A x‖) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, zero_mul, mul_zero] using
        ((tendsto_const_nhds.mul tendsto_inv_atTop_zero).mul_const ‖A x‖ :
          Tendsto (fun r : ℝ => (M * r⁻¹) * ‖A x‖) atTop (𝓝 ((M * 0) * ‖A x‖)))
    exact hz

/-- Density and the common operator bound extend the resolvent limit to X. -/
theorem scaledResolvent_tendsto {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (hd : Dense (A.domain : Set X)) (h : ResolventEstimates A M) (x : X) :
    Tendsto (fun r : ℝ => scaledResolvent A r x) atTop (𝓝 x) := by
  have hM := constant_nonneg h
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := hd.exists_dist_lt x (div_pos hε (by positivity : 0 < 2 * (M + 1)))
  have hdist : ‖x - y‖ < ε / (2 * (M + 1)) := by simpa only [dist_eq_norm] using hxy
  have hyε := (Metric.tendsto_nhds.mp (scaledResolvent_tendsto_domain h ⟨y, hy⟩))
    (ε / 2) (half_pos hε)
  filter_upwards [hyε, eventually_gt_atTop (0 : ℝ)] with r hr hrpos
  rw [dist_eq_norm] at hr ⊢
  have hb : ‖scaledResolvent A r (x - y)‖ ≤ M * ‖x - y‖ :=
    ((scaledResolvent A r).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (norm_scaledResolvent_le h hrpos) (norm_nonneg _))
  have heq : scaledResolvent A r x - x =
      scaledResolvent A r (x - y) + (scaledResolvent A r y - y) - (x - y) := by
    rw [map_sub]; abel
  calc
    ‖scaledResolvent A r x - x‖ ≤
        ‖scaledResolvent A r (x - y)‖ + ‖scaledResolvent A r y - y‖ + ‖x - y‖ := by
      rw [heq]
      exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ M * ‖x - y‖ + ‖scaledResolvent A r y - y‖ + ‖x - y‖ := by gcongr
    _ = (M + 1) * ‖x - y‖ + ‖scaledResolvent A r y - y‖ := by ring
    _ < (M + 1) * (ε / (2 * (M + 1))) + ε / 2 := by gcongr
    _ = ε := by field_simp; ring

/-- The first requested strong limit, under precisely the source assumptions. -/
theorem scaled_resolvent_limit : ScaledResolventLimit (𝕜 := 𝕜) (X := X) := by
  intro A M h x
  exact scaledResolvent_tendsto h.1 h.2.2 x

/-- The approximants converge to A at every vector in its original domain. -/
theorem approximant_limit : ApproximantLimit (𝕜 := 𝕜) (X := X) := by
  intro A M h x
  apply (scaledResolvent_tendsto h.1 h.2.2 (A x)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (approximant_apply_domain A r (h.2.2.1 r hr) x).symm

/-- The zero-th power bound needed by the exponential series follows from
strong convergence; it does not require excluding the zero space. -/
theorem norm_id_le_constant {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (hd : Dense (A.domain : Set X)) (h : ResolventEstimates A M) :
    ‖ContinuousLinearMap.id 𝕜 X‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (constant_nonneg h)
  intro x
  have hl := (scaledResolvent_tendsto hd h x).norm
  apply le_of_tendsto hl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact ((scaledResolvent A r).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (norm_scaledResolvent_le h hr) (norm_nonneg _))

/-- All powers of rR(r,A), including power zero, have the same M bound. -/
theorem norm_scaledResolvent_pow_le {A : Unbounded.Operator 𝕜 X X} {M r : ℝ}
    (hd : Dense (A.domain : Set X)) (h : ResolventEstimates A M) (hr : 0 < r) (n : ℕ) :
    ‖scaledResolvent A r ^ n‖ ≤ M := by
  cases n with
  | zero =>
    change ‖ContinuousLinearMap.id 𝕜 X‖ ≤ M
    exact norm_id_le_constant hd h
  | succ n =>
    rw [scaledResolvent, smul_pow, norm_smul, norm_pow,
      norm_algebraMap' 𝕜, Real.norm_eq_abs, abs_of_pos hr]
    calc
      r ^ (n + 1) * ‖positiveResolvent A r ^ (n + 1)‖ ≤
          r ^ (n + 1) * (M / r ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left (h.2 r hr n) (pow_nonneg hr.le _)
      _ = M := mul_div_cancel₀ M (pow_ne_zero _ hr.ne')

/-- A bound on all powers controls the exponential series with the same M. -/
theorem norm_exp_smul_le (B : X →L[𝕜] X) {M a : ℝ}
    (ha : 0 ≤ a) (hB : ∀ n : ℕ, ‖B ^ n‖ ≤ M) :
    ‖NormedSpace.exp (algebraMap ℝ 𝕜 a • B)‖ ≤ M * Real.exp a := by
  have hs : HasSum (fun n : ℕ => M * ((n.factorial : ℝ)⁻¹ * a ^ n)) (M * Real.exp a) := by
    simpa only [smul_eq_mul, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).mul_left M
  apply (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜)
    (algebraMap ℝ 𝕜 a • B)).norm_le_of_bounded hs
  intro n
  rw [norm_smul, norm_inv, RCLike.norm_natCast, smul_pow, norm_smul, norm_pow,
    norm_algebraMap' 𝕜, Real.norm_eq_abs, abs_of_nonneg ha]
  calc
    (n.factorial : ℝ)⁻¹ * (a ^ n * ‖B ^ n‖) ≤
        (n.factorial : ℝ)⁻¹ * (a ^ n * M) := by
      gcongr
      exact hB n
    _ = M * ((n.factorial : ℝ)⁻¹ * a ^ n) := by ring

/-- Separate off the scalar part of the approximant before estimating. -/
theorem exponential_factorization (A : Unbounded.Operator 𝕜 X X) (r t : ℝ) :
    exponential A r t = NormedSpace.exp (algebraMap ℝ 𝕜 (-(t * r))) •
      NormedSpace.exp (algebraMap ℝ 𝕜 (t * r) • scaledResolvent A r) := by
  have hexp (z : 𝕜) : NormedSpace.exp (z • (1 : X →L[𝕜] X)) =
      NormedSpace.exp z • (1 : X →L[𝕜] X) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (NormedSpace.algebraMap_exp_comm (𝔸 := X →L[𝕜] X) z).symm
  have heq : algebraMap ℝ 𝕜 t • approximant A r =
      algebraMap ℝ 𝕜 (-(t * r)) • (1 : X →L[𝕜] X) +
      algebraMap ℝ 𝕜 (t * r) • scaledResolvent A r := by
    ext x
    simp only [approximant, smul_apply, sub_apply, ContinuousLinearMap.id_apply,
      one_apply_eq_self, add_apply, neg_apply, smul_sub, smul_smul, map_mul, map_neg, neg_smul]
    abel
  let : NormedAlgebra ℚ (X →L[𝕜] X) := NormedAlgebra.restrictScalars ℚ 𝕜 _
  rw [exponential, heq, NormedSpace.exp_add_of_commute
    (((Commute.one_left _).smul_left _).smul_right _), hexp, smul_mul_assoc, one_mul]

/-- The power estimates give a common bound for all positive Yosida parameters
and every nonnegative time, with precisely the original constant M. -/
theorem exponential_bound : ExponentialBound (𝕜 := 𝕜) (X := X) := by
  intro A M h r hr t ht
  rw [exponential_factorization, norm_smul,
    LaplaceResolvent.norm_scalar_exp, RCLike.algebraMap_eq_ofReal, RCLike.ofReal_re]
  calc
    Real.exp (-(t * r)) *
        ‖NormedSpace.exp (algebraMap ℝ 𝕜 (t * r) • scaledResolvent A r)‖ ≤
        Real.exp (-(t * r)) * (M * Real.exp (t * r)) :=
      mul_le_mul_of_nonneg_left
        (norm_exp_smul_le _ (mul_nonneg ht hr.le)
          (norm_scaledResolvent_pow_le h.1 h.2.2 hr)) (Real.exp_nonneg _)
    _ = M := by rw [mul_left_comm, ← Real.exp_add]; simp

/-- The bounded resolvent commutes with A on its original domain. -/
theorem resolvent_operator_commute {A : Unbounded.Operator 𝕜 X X} {z : 𝕜}
    (R : Unbounded.ResolventInverse A z) (x : A.domain) :
    A ⟨R.inverse x, R.mem_domain x⟩ = R.inverse (A x) := by
  have hL := R.left_inverse x
  rw [map_sub, map_smul] at hL
  exact sub_right_inj.mp ((R.right_inverse x).trans hL.symm)

/-- Two resolvents commute without any assumption that their parameters differ. -/
theorem resolvents_commute {A : Unbounded.Operator 𝕜 X X} {z w : 𝕜}
    (R : Unbounded.ResolventInverse A z) (S : Unbounded.ResolventInverse A w) :
    Commute R.inverse S.inverse := by
  ext x
  change R.inverse (S.inverse x) = S.inverse (R.inverse x)
  have hA := resolvent_operator_commute S ⟨R.inverse x, R.mem_domain x⟩
  calc
    R.inverse (S.inverse x) = R.inverse
        (z • S.inverse (R.inverse x) - A ⟨S.inverse (R.inverse x), S.mem_domain _⟩) := by
      congr 1
      rw [hA, ← map_smul, ← map_sub, R.right_inverse x]
    _ = S.inverse (R.inverse x) := R.left_inverse ⟨_, S.mem_domain _⟩

/-- All bounded Yosida approximants commute. -/
theorem approximants_commute {A : Unbounded.Operator 𝕜 X X} {M r s : ℝ}
    (h : ResolventEstimates A M) (hr : 0 < r) (hs : 0 < s) :
    Commute (approximant A r) (approximant A s) := by
  have hR : Commute (positiveResolvent A r) (positiveResolvent A s) := by
    rw [positiveResolvent_eq A r (h.1 r hr), positiveResolvent_eq A s (h.1 s hs)]
    exact resolvents_commute _ _
  have hB : Commute (scaledResolvent A r) (scaledResolvent A s) :=
    (hR.smul_left (algebraMap ℝ 𝕜 r)).smul_right (algebraMap ℝ 𝕜 s)
  exact (((hB.sub_left (Commute.one_left _)).sub_right (Commute.one_right _)).smul_left
    (algebraMap ℝ 𝕜 r)).smul_right (algebraMap ℝ 𝕜 s)

local instance : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
local instance : IsScalarTower ℝ 𝕜 X := IsScalarTower.restrictScalars ℝ 𝕜 X
local instance : NormedAlgebra ℝ (X →L[𝕜] X) :=
  { (inferInstance : NormedSpace ℝ (X →L[𝕜] X)),
    (inferInstance : Algebra ℝ (X →L[𝕜] X)) with }
local instance : NormedAlgebra ℚ (X →L[𝕜] X) := NormedAlgebra.restrictScalars ℚ 𝕜 _

/-- Real differentiability of the exponential in the operator algebra. -/
theorem hasDerivAt_exponential (A : Unbounded.Operator 𝕜 X X) (r t : ℝ) :
    HasDerivAt (exponential A r) (exponential A r t * approximant A r) t := by
  change HasDerivAt (fun u : ℝ => NormedSpace.exp (algebraMap ℝ 𝕜 u • approximant A r))
    (NormedSpace.exp (algebraMap ℝ 𝕜 t • approximant A r) * approximant A r) t
  simpa only [algebraMap_smul 𝕜] using
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) (approximant A r) t)

/-- Evaluation is a continuous linear map, also over the restricted real scalars. -/
theorem hasDerivAt_exponential_apply (A : Unbounded.Operator 𝕜 X X) (r t : ℝ) (x : X) :
    HasDerivAt (fun u : ℝ => exponential A r u x)
      (exponential A r t (approximant A r x)) t := by
  let L := (ContinuousLinearMap.apply 𝕜 X x).restrictScalars ℝ
  exact L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exponential A r t)

/-- Derivative of the comparison exponential, on the whole real time line. -/
theorem comparison_hasDerivAt {A : Unbounded.Operator 𝕜 X X} {M r s : ℝ}
    (h : ResolventEstimates A M) (hr : 0 < r) (hs : 0 < s) (t u : ℝ) (x : X) :
    HasDerivAt (fun v : ℝ => exponential A r (t - v) (exponential A s v x))
      (exponential A r (t - u) (exponential A s u ((approximant A s - approximant A r) x))) u := by
  have hleft := (hasDerivAt_exponential A r (t - u)).scomp u
    ((hasDerivAt_id u).const_sub t)
  have hd := hleft.mul (hasDerivAt_exponential A s u)
  let L := (ContinuousLinearMap.apply 𝕜 X x).restrictScalars ℝ
  have heval := L.hasFDerivAt.comp_hasDerivAt u hd
  convert heval using 1
  · rfl
  · dsimp [L]
    have hc : Commute (approximant A r) (exponential A s u) := by
      exact ((approximants_commute h hr hs).smul_right (algebraMap ℝ 𝕜 u)).exp_right
    have heq : exponential A r (t - u) * exponential A s u *
        (approximant A s - approximant A r) =
        (-(exponential A r (t - u) * approximant A r)) * exponential A s u +
          exponential A r (t - u) * (exponential A s u * approximant A s) := by
      rw [mul_sub, mul_assoc (exponential A r (t - u)) (exponential A s u) (approximant A r), ← hc.eq]
      noncomm_ring
    simpa only [neg_one_smul, mul_apply_eq_comp] using congrArg (fun B : X →L[𝕜] X => B x) heq

/-- The Duhamel comparison estimate, proved by the norm mean value theorem. -/
theorem norm_exponential_sub_le {A : Unbounded.Operator 𝕜 X X} {M r s : ℝ}
    (h : Hypotheses A M) (hr : 0 < r) (hs : 0 < s) (t : ℝ) (ht : 0 ≤ t) (x : X) :
    ‖exponential A r t x - exponential A s t x‖ ≤
      (M * M * ‖(approximant A r - approximant A s) x‖) * t := by
  let F := fun v : ℝ => exponential A r (t - v) (exponential A s v x)
  let F' := fun v : ℝ => exponential A r (t - v)
    (exponential A s v ((approximant A s - approximant A r) x))
  have hderiv : ∀ v ∈ Icc 0 t, HasDerivWithinAt F (F' v) (Icc 0 t) v := by
    intro v hv
    exact (comparison_hasDerivAt h.2.2 hr hs t v x).hasDerivWithinAt
  have hb : ∀ v ∈ Ico 0 t, ‖F' v‖ ≤ M * M * ‖(approximant A r - approximant A s) x‖ := by
    intro v hv
    have hM := constant_nonneg h.2.2
    calc
      ‖F' v‖ ≤ M * ‖exponential A s v ((approximant A s - approximant A r) x)‖ :=
        ((exponential A r (t - v)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (exponential_bound A M h r hr (t - v) (by linarith [hv.2])) (norm_nonneg _))
      _ ≤ M * (M * ‖(approximant A s - approximant A r) x‖) :=
        mul_le_mul_of_nonneg_left (((exponential A s v).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (exponential_bound A M h s hs v hv.1) (norm_nonneg _))) hM
      _ = M * M * ‖(approximant A r - approximant A s) x‖ := by
        rw [sub_apply, norm_sub_rev, ← sub_apply]; ring
  have he := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hb t ⟨ht, le_rfl⟩
  simpa only [F, sub_self, exponential, map_zero, zero_smul, NormedSpace.exp_zero,
    one_apply_eq_self, sub_zero, norm_sub_rev] using he

/-- The comparison estimate makes the exponential orbits uniformly Cauchy
on each bounded interval, first for a vector in D(A). -/
theorem uniformCauchySeqOn_domain {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : Hypotheses A M) (x : A.domain) (b : ℝ) (hb : 0 ≤ b) :
    UniformCauchySeqOn (fun r : ℝ => fun t : ℝ => exponential A r t x) atTop (Icc 0 b) := by
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  have hC : 0 ≤ M * M * b := mul_nonneg (mul_self_nonneg M) hb
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (approximant_limit A M h x)
    (ε / (2 * (M * M * b + 1))) (by positivity)
  refine ⟨max N 1, ?_⟩
  intro r hr s hs t ht
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one ((le_max_right N 1).trans hr)
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one ((le_max_right N 1).trans hs)
  have hdiff : ‖(approximant A r - approximant A s) x‖ < ε / (M * M * b + 1) := by
    have hrε := hN r ((le_max_left N 1).trans hr)
    have hsε := hN s ((le_max_left N 1).trans hs)
    rw [dist_eq_norm] at hrε hsε
    rw [sub_apply]
    calc
      ‖approximant A r x - approximant A s x‖ ≤
          ‖approximant A r x - A x‖ + ‖approximant A s x - A x‖ := by
        simpa only [norm_sub_rev (A x) (approximant A s x)] using
          norm_sub_le_norm_sub_add_norm_sub (approximant A r x) (A x) (approximant A s x)
      _ < ε / (2 * (M * M * b + 1)) + ε / (2 * (M * M * b + 1)) := add_lt_add hrε hsε
      _ = ε / (M * M * b + 1) := by field_simp; ring
  rw [dist_eq_norm]
  calc
    ‖exponential A r t x - exponential A s t x‖ ≤
        (M * M * ‖(approximant A r - approximant A s) x‖) * t :=
      norm_exponential_sub_le h hr0 hs0 t ht.1 x
    _ ≤ (M * M * b) * ‖(approximant A r - approximant A s) x‖ := by
      calc
        _ ≤ (M * M * ‖(approximant A r - approximant A s) x‖) * b :=
          mul_le_mul_of_nonneg_left ht.2 (mul_nonneg (mul_self_nonneg _) (norm_nonneg _))
        _ = _ := by ring
    _ < ε := by
      have hn := norm_nonneg ((approximant A r - approximant A s) x)
      have hx := (lt_div_iff₀ (by positivity : 0 < M * M * b + 1)).mp hdiff
      nlinarith

/-- The common bound extends the uniformly Cauchy property from D(A) to X. -/
theorem uniformCauchySeqOn {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : Hypotheses A M) (x : X) (b : ℝ) (hb : 0 ≤ b) :
    UniformCauchySeqOn (fun r : ℝ => fun t : ℝ => exponential A r t x) atTop (Icc 0 b) := by
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  have hM := constant_nonneg h.2.2
  obtain ⟨y, hy, hxy⟩ := h.1.exists_dist_lt x
    (div_pos hε (by positivity : 0 < 4 * (M + 1)))
  have hnorm : ‖x - y‖ < ε / (4 * (M + 1)) := by simpa only [dist_eq_norm] using hxy
  obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp
    (uniformCauchySeqOn_domain h ⟨y, hy⟩ b hb) (ε / 2) (half_pos hε)
  refine ⟨max N 1, ?_⟩
  intro r hr s hs t ht
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one ((le_max_right N 1).trans hr)
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one ((le_max_right N 1).trans hs)
  have hyε := hN r ((le_max_left N 1).trans hr) s ((le_max_left N 1).trans hs) t ht
  rw [dist_eq_norm] at hyε ⊢
  have bound (q : ℝ) (hq : 0 < q) :
      ‖exponential A q t (x - y)‖ ≤ M * ‖x - y‖ :=
    ((exponential A q t).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (exponential_bound A M h q hq t ht.1) (norm_nonneg _))
  have heq : exponential A r t x - exponential A s t x =
      exponential A r t (x - y) + (exponential A r t y - exponential A s t y) -
        exponential A s t (x - y) := by rw [map_sub, map_sub]; abel
  calc
    ‖exponential A r t x - exponential A s t x‖ ≤
        ‖exponential A r t (x - y)‖ + ‖exponential A r t y - exponential A s t y‖ +
          ‖exponential A s t (x - y)‖ := by
      rw [heq]; exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ M * ‖x - y‖ + ‖exponential A r t y - exponential A s t y‖ + M * ‖x - y‖ :=
      add_le_add (add_le_add (bound r hr0) le_rfl) (bound s hs0)
    _ = 2 * M * ‖x - y‖ + ‖exponential A r t y - exponential A s t y‖ := by ring
    _ < ε := by
      have hδ := (lt_div_iff₀ (by positivity : 0 < 4 * (M + 1))).mp hnorm
      nlinarith [norm_nonneg (x - y)]

/-- Completeness supplies the pointwise orbit limits. -/
theorem exists_orbit_limit {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : Hypotheses A M) (x : X) (t : ℝ) (ht : 0 ≤ t) :
    ∃ y : X, Tendsto (fun r : ℝ => exponential A r t x) atTop (𝓝 y) := by
  apply cauchy_map_iff_exists_tendsto.mp
  exact (uniformCauchySeqOn h x t ht).cauchy_map ⟨ht, le_rfl⟩

/-- The pointwise limit, with negative times immaterial to its intended use. -/
def orbitLimit (A : Unbounded.Operator 𝕜 X X) (t : ℝ) (x : X) : X :=
  limUnder atTop (fun r : ℝ => exponential A r t x)

theorem tendsto_orbitLimit {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : Hypotheses A M) (x : X) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun r : ℝ => exponential A r t x) atTop (𝓝 (orbitLimit A t x)) :=
  tendsto_nhds_limUnder (exists_orbit_limit h x t ht)

/-- Convergence is uniform down to time zero on every bounded time interval. -/
theorem tendstoUniformlyOn_orbitLimit {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : Hypotheses A M) (x : X) (b : ℝ) (hb : 0 ≤ b) :
    TendstoUniformlyOn (fun r : ℝ => fun t : ℝ => exponential A r t x)
      (fun t : ℝ => orbitLimit A t x) atTop (Icc 0 b) := by
  apply (uniformCauchySeqOn h x b hb).tendstoUniformlyOn_of_tendsto
  intro t ht
  exact tendsto_orbitLimit h x t ht.1

/-- Norm bounds pass to the strong limit. -/
theorem norm_orbitLimit_le {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : Hypotheses A M) (x : X) (t : ℝ) (ht : 0 ≤ t) :
    ‖orbitLimit A t x‖ ≤ M * ‖x‖ := by
  apply le_of_tendsto (tendsto_orbitLimit h x t ht).norm
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact ((exponential A r t).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (exponential_bound A M h r hr t ht) (norm_nonneg _))

/-- The limiting operators are bounded linear maps, by pointwise passage to limits. -/
def limitOperator {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : Hypotheses A M) (t : ℝ≥0) : X →L[𝕜] X :=
  LinearMap.mkContinuous
    { toFun := orbitLimit A t
      map_add' := fun x y => by
        apply tendsto_nhds_unique (tendsto_orbitLimit h (x + y) t t.coe_nonneg)
        simpa only [map_add] using
          (tendsto_orbitLimit h x t t.coe_nonneg).add (tendsto_orbitLimit h y t t.coe_nonneg)
      map_smul' := fun c x => by
        apply tendsto_nhds_unique (tendsto_orbitLimit h (c • x) t t.coe_nonneg)
        simpa only [map_smul, RingHom.id_apply] using
          (tendsto_orbitLimit h x t t.coe_nonneg).const_smul c }
    M (fun x => norm_orbitLimit_le h x t t.coe_nonneg)

@[simp] theorem limitOperator_apply {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : Hypotheses A M) (t : ℝ≥0) (x : X) : limitOperator h t x = orbitLimit A t x := rfl

theorem norm_limitOperator_le {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : Hypotheses A M) (t : ℝ≥0) : ‖limitOperator h t‖ ≤ M :=
  (limitOperator h t).opNorm_le_bound (constant_nonneg h.2.2)
    (norm_orbitLimit_le h · t t.coe_nonneg)

/-- Each bounded exponential is continuous in real time. -/
theorem continuous_exponential_apply (A : Unbounded.Operator 𝕜 X X) (r : ℝ) (x : X) :
    Continuous (fun t : ℝ => exponential A r t x) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_exponential_apply A r t x).continuousAt

/-- Local uniform convergence supplies continuity of every limiting orbit. -/
theorem continuousOn_orbitLimit {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : Hypotheses A M) (x : X) (b : ℝ) (hb : 0 ≤ b) :
    ContinuousOn (fun t : ℝ => orbitLimit A t x) (Icc 0 b) :=
  (tendstoUniformlyOn_orbitLimit h x b hb).continuousOn
    (Frequently.of_forall fun r => (continuous_exponential_apply A r x).continuousOn)

/-- The limit at time zero is exactly the identity, even on the zero space. -/
theorem orbitLimit_zero {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : Hypotheses A M) (x : X) : orbitLimit A 0 x = x := by
  apply tendsto_nhds_unique (tendsto_orbitLimit h x 0 le_rfl)
  simp only [exponential, map_zero, zero_smul, NormedSpace.exp_zero, one_apply_eq_self]
  exact tendsto_const_nhds

/-- The exponential semigroup identity holds for arbitrary real times. -/
theorem exponential_add (A : Unbounded.Operator 𝕜 X X) (r t s : ℝ) :
    exponential A r (t + s) = exponential A r t * exponential A r s := by
  simp only [exponential, map_add, add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl _).smul_left _).smul_right _)

/-- The uniform norm bound allows the input vector to vary with the parameter. -/
theorem tendsto_exponential_apply {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : Hypotheses A M) (t : ℝ) (ht : 0 ≤ t) {v : ℝ → X} {x : X}
    (hv : Tendsto v atTop (𝓝 x)) :
    Tendsto (fun r : ℝ => exponential A r t (v r)) atTop (𝓝 (orbitLimit A t x)) := by
  have hz : Tendsto (fun r : ℝ => exponential A r t (v r - x)) atTop (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      exact ((exponential A r t).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (exponential_bound A M h r hr t ht) (norm_nonneg _))
    · simpa only [sub_self, norm_zero, mul_zero] using
        tendsto_const_nhds.mul (hv.sub_const x).norm
  simpa only [map_sub, zero_add, sub_add_cancel] using
    hz.add (tendsto_orbitLimit h x t ht)

/-- The limiting operators satisfy the semigroup law. -/
theorem limitOperator_add {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : Hypotheses A M) (t s : ℝ≥0) :
    limitOperator h (t + s) = (limitOperator h t).comp (limitOperator h s) := by
  ext x
  apply tendsto_nhds_unique (tendsto_orbitLimit h x (t + s) (t + s).coe_nonneg)
  have hl := tendsto_exponential_apply h t t.coe_nonneg (tendsto_orbitLimit h x s s.coe_nonneg)
  simpa only [exponential_add, mul_apply_eq_comp, ContinuousLinearMap.comp_apply, limitOperator_apply] using hl

/-- The limit has the required strong right continuity at zero. -/
theorem limitOperator_strong_zero {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : Hypotheses A M) (x : X) :
    Tendsto (fun u : ℝ => limitOperator h u.toNNReal x) (𝓝[>] 0) (𝓝 x) := by
  have hc := (continuousOn_orbitLimit h x 1 zero_le_one) 0 ⟨le_rfl, zero_le_one⟩
  rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE zero_lt_one, orbitLimit_zero h x] at hc
  have hl := hc.mono_left (nhdsWithin_mono (0 : ℝ) Ioi_subset_Ici_self)
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  change orbitLimit A u x = orbitLimit A (u.toNNReal : ℝ) x
  rw [Real.coe_toNNReal _ (le_of_lt hu)]

/-- The C₀ semigroup obtained from the locally uniform strong limits. -/
def limitSemigroup {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : Hypotheses A M) : C0Semigroup 𝕜 X where
  operators := limitOperator h
  at_zero := by ext x; exact orbitLimit_zero h x
  add_time := limitOperator_add h
  strong_zero := limitOperator_strong_zero h

/-- Uniform convergence still holds when the input A_r x tends to Ax. -/
theorem tendstoUniformlyOn_exponential_approximant {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : Hypotheses A M) (x : A.domain) (b : ℝ) (hb : 0 ≤ b) :
    TendstoUniformlyOn (fun r : ℝ => fun t : ℝ => exponential A r t (approximant A r x))
      (fun t : ℝ => orbitLimit A t (A x)) atTop (Icc 0 b) := by
  have hM := constant_nonneg h.2.2
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have h1 := Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_orbitLimit h (A x) b hb)
    (ε / 2) (half_pos hε)
  have h2 := Metric.tendsto_nhds.mp (approximant_limit A M h x)
    (ε / (2 * (M + 1))) (by positivity)
  filter_upwards [h1, h2, eventually_gt_atTop (0 : ℝ)] with r hr1 hr2 hr0
  intro t ht
  have hdiff : ‖exponential A r t (A x) - exponential A r t (approximant A r x)‖ ≤
      M * ‖A x - approximant A r x‖ := by
    rw [← map_sub]
    exact ((exponential A r t).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (exponential_bound A M h r hr0 t ht.1) (norm_nonneg _))
  have hr1' := hr1 t ht
  rw [dist_eq_norm] at hr1' hr2 ⊢
  rw [norm_sub_rev] at hr2
  calc
    ‖orbitLimit A t (A x) - exponential A r t (approximant A r x)‖ ≤
        ‖orbitLimit A t (A x) - exponential A r t (A x)‖ +
          ‖exponential A r t (A x) - exponential A r t (approximant A r x)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖orbitLimit A t (A x) - exponential A r t (A x)‖ +
        M * ‖A x - approximant A r x‖ := add_le_add le_rfl hdiff
    _ < ε := by
      have he := (lt_div_iff₀ (by positivity : 0 < 2 * (M + 1))).mp hr2
      nlinarith [norm_nonneg (A x - approximant A r x)]

/-- The elementary integral identity for every bounded approximant. -/
theorem exponential_integral_identity (A : Unbounded.Operator 𝕜 X X) (r t : ℝ) (x : X) :
    exponential A r t x - x = ∫ s in (0 : ℝ)..t, exponential A r s (approximant A r x) := by
  have hid := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_hs : s ∈ uIcc 0 t) => hasDerivAt_exponential_apply A r s x)
    ((continuous_exponential_apply A r (approximant A r x)).intervalIntegrable 0 t)
  simpa only [exponential, map_zero, zero_smul, NormedSpace.exp_zero, one_apply_eq_self] using hid.symm

/-- Pass the integral identity to the limit on the original domain of A. -/
theorem limit_integral_identity {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : Hypotheses A M) (x : A.domain) (t : ℝ≥0) :
    (limitSemigroup h).operators t x - x = (limitSemigroup h).integratedOperator t (A x) := by
  have hu := tendstoUniformlyOn_exponential_approximant h x t t.coe_nonneg
  rw [← uIcc_of_le t.coe_nonneg] at hu
  have hint := hu.tendsto_intervalIntegral_of_continuousOn
    (μ := MeasureTheory.volume)
    (Eventually.of_forall fun r => (continuous_exponential_apply A r (approximant A r x)).continuousOn)
  have hexp := (tendsto_orbitLimit h x t t.coe_nonneg).sub_const (x : X)
  have heq : orbitLimit A t x - x = ∫ s in (0 : ℝ)..(t : ℝ), orbitLimit A s (A x) := by
    apply tendsto_nhds_unique hexp
    simpa only [← exponential_integral_identity] using hint
  change orbitLimit A t x - x = _
  rw [heq, C0Semigroup.integratedOperator_apply]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le t.coe_nonneg] at hs
  change orbitLimit A s (A x) = orbitLimit A (s.toNNReal : ℝ) (A x)
  rw [Real.coe_toNNReal _ hs.1]

/-- Every vector in the original domain has the required generator derivative. -/
theorem hasGeneratorLimit_domain {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : Hypotheses A M) (x : A.domain) : HasGeneratorLimit (limitSemigroup h) x (A x) :=
  ((limitSemigroup h).hasGeneratorLimit_iff_integrated x (A x)).mpr
    (limit_integral_identity h x)

/-- The generator of the limiting semigroup extends A as a partial linear map. -/
theorem operator_le_generator {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : Hypotheses A M) : A ≤ generator (limitSemigroup h) := by
  constructor
  · intro x hx
    exact ⟨A ⟨x, hx⟩, hasGeneratorLimit_domain h ⟨x, hx⟩⟩
  · intro x y hxy
    apply generator_limit_unique (limitSemigroup h) (y : X)
      (A x) (generator (limitSemigroup h) y)
    · rw [← hxy]
      exact hasGeneratorLimit_domain h x
    · exact generator_has_limit (limitSemigroup h) y

/-- A common resolvent point upgrades an operator extension to exact equality. -/
theorem eq_of_extension_of_resolvents (A B : Unbounded.Operator 𝕜 X X)
    (hAB : A ≤ B) (z : 𝕜) (R : Unbounded.ResolventInverse A z)
    (S : Unbounded.ResolventInverse B z) : A = B := by
  apply LinearPMap.eq_of_le_of_domain_eq hAB
  apply le_antisymm hAB.1
  intro x hx
  let y : A.domain := ⟨R.inverse (z • x - B ⟨x, hx⟩), R.mem_domain _⟩
  have hAy : A y = B ⟨(y : X), hAB.1 y.2⟩ := hAB.2 rfl
  have heq : (y : X) = x := by
    calc
      (y : X) = S.inverse (z • (y : X) - B ⟨(y : X), hAB.1 y.2⟩) :=
        (S.left_inverse ⟨(y : X), hAB.1 y.2⟩).symm
      _ = S.inverse (z • x - B ⟨x, hx⟩) := by
        rw [← hAy]
        exact congrArg S.inverse (R.right_inverse (z • x - B ⟨x, hx⟩))
      _ = x := S.left_inverse ⟨x, hx⟩
  rw [← heq]
  exact y.2

/-- Exact equality of generators includes equality of their whole domains. -/
theorem generator_limitSemigroup {A : Unbounded.Operator 𝕜 X X} {M : ℝ}
    (h : Hypotheses A M) : generator (limitSemigroup h) = A := by
  let T := limitSemigroup h
  have hb : C0SemigroupSpec.exponentialBoundValue T (max 1 M) 0 := by
    refine ⟨le_max_left _ _, ?_⟩
    intro t
    change ‖limitOperator h t‖ ≤ max 1 M * Real.exp (0 * (t : ℝ))
    simpa only [zero_mul, Real.exp_zero, mul_one] using
      (norm_limitOperator_le h t).trans (le_max_right 1 M)
  let S := LaplaceResolvent.inverse T (max 1 M) 0 (1 : 𝕜) hb (by simp)
  have hR := h.2.2.1 1 zero_lt_one
  rw [map_one] at hR
  exact (eq_of_extension_of_resolvents A (generator T) (operator_le_generator h)
    1 hR.some S).symm

/-- The zero-shift Hille–Yosida sufficiency and approximation theorem. -/
theorem generation : Generation (𝕜 := 𝕜) (X := X) := by
  intro A M h
  refine ⟨limitSemigroup h, generator_limitSemigroup h, norm_limitOperator_le h, ?_⟩
  intro x b hb
  have hu := tendstoUniformlyOn_orbitLimit h x b hb
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε] with r hr
  intro t ht
  change dist (orbitLimit A (t.toNNReal : ℝ) x) (exponential A r t x) < ε
  rw [Real.coe_toNNReal _ ht.1]
  exact hr t ht

end ExpandedFA.Semigroups.YosidaConstruction
