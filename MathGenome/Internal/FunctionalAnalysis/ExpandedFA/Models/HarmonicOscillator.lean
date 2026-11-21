import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.HarmonicOscillator
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.HermiteBasis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.ConfiningCompactResolvent

set_option maxHeartbeats 800000

noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped InnerProductSpace Topology ENNReal
attribute [local instance 2000] NormedAddCommGroup.toSeminormedAddCommGroup

namespace ExpandedFA.Models.HarmonicOscillator
open WeightedConfiningEnergySpace ConfiningSchrodingerRealization ConfiningCompactResolvent

@[simp] lemma potential_apply (x : ℝ) : potential.toContinuousMap x = x^2 := rfl

theorem confining : Spec.Confining := by
  intro M
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx
  have h₁ : M ≤ |x| := (le_max_left _ _).trans hx
  have h₂ : 1 ≤ |x| := (le_max_right _ _).trans hx
  change M ≤ x^2
  nlinarith [sq_abs x]

lemma positive_at_infinity : PositiveAtInfinity potential := confining.positiveAtInfinity

/-- A compact inverse gives the resolvent at zero, with the required minus
sign in the convention (ζI−A)⁻¹. -/
lemma compact_resolvent_of_inverse {𝕜 : Type} [RCLike 𝕜]
    (T : L2 𝕜 →L[𝕜] L2 𝕜) (hc : IsCompactOperator T)
    (A : L2 𝕜 →ₗ.[𝕜] L2 𝕜)
    (hg : ∀ u f, (u, f) ∈ A.graph ↔ T f = u) :
    ∃ R : ExpandedFA.Unbounded.ResolventInverse A 0, IsCompactOperator R.inverse := by
  have hm (f : L2 𝕜) : -T f ∈ A.domain :=
    LinearPMap.mem_domain_of_mem_graph ((hg (-T f) (-f)).mpr (by simp))
  let R : ExpandedFA.Unbounded.ResolventInverse A 0 :=
    { inverse := -T
      mem_domain := hm
      right_inverse := by
        intro f
        have he : A ⟨-T f, hm f⟩ = -f := by
          have h := (hg (-T f) (-f)).mpr (by simp)
          obtain ⟨y, hy, ha⟩ := (LinearPMap.mem_graph_iff A).mp h
          have he : y = ⟨-T f, hm f⟩ := Subtype.ext hy
          simpa only [he] using ha
        change (0 : 𝕜) • (-T f) - A ⟨-T f, hm f⟩ = f
        simp [he]
      left_inverse := by
        intro u
        have he := (hg (u : L2 𝕜) (A u)).mp (A.mem_graph u)
        change -T ((0 : 𝕜) • (u : L2 𝕜) - A u) = (u : L2 𝕜)
        simpa using he }
  exact ⟨R, hc.neg⟩

theorem realization_and_compact_resolvent : Spec.RealizationAndCompactResolvent := by
  intro 𝕜 _
  obtain ⟨T, hsol, _, _, _, _, A, hg, hd, hsa, hp, hdiff, _⟩ :=
    confining_realization 𝕜 potential positive_at_infinity
  refine ⟨A, hdiff, hd, hsa, hp, ?_⟩
  exact compact_resolvent_of_inverse T (compact_solution_operator 𝕜 potential confining T hsol) A hg



section Position
variable {𝕜 : Type} [RCLike 𝕜]

lemma position_weight_norm (x : Line) (z : 𝕜) :
    ‖(x 0 : 𝕜) * z‖ = ‖weight 𝕜 potential x * z‖ := by
  simp [weight, Real.sqrt_sq_eq_abs, norm_mul, RCLike.norm_ofReal]

lemma position_memLp (u : Space 𝕜 potential) :
    MemLp (fun x => (x 0 : 𝕜) * value u x) 2 lineMeasure := by
  apply (Lp.memLp (weighted u)).norm.mono'
    (((RCLike.continuous_ofReal.comp (continuous_apply 0)).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable (value u)))
  filter_upwards [weighted_ae potential u] with x hx
  change ‖(x 0 : 𝕜) * value u x‖ ≤ ‖weighted u x‖
  rw [hx, position_weight_norm]

/-- The signed multiplier is linear, in contrast to the stored absolute-value
weight; its norm is the same. -/
def position (u : Space 𝕜 potential) : L2 𝕜 :=
  (position_memLp u).toLp (fun x => (x 0 : 𝕜) * value u x)

lemma position_coe (u : Space 𝕜 potential) : IsPosition u (position u) :=
  MemLp.coeFn_toLp _

lemma position_unique (u : Space 𝕜 potential) {w : L2 𝕜} (hw : IsPosition u w) :
    w = position u := Lp.ext (hw.trans (position_coe u).symm)

lemma position_norm (u : Space 𝕜 potential) : ‖position u‖ = ‖weighted u‖ := by
  have he : ∀ᵐ x ∂lineMeasure, ‖position u x‖ = ‖weighted u x‖ := by
    filter_upwards [position_coe u, weighted_ae potential u] with x hx hy
    rw [hx, hy, position_weight_norm]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (he.mono fun _ h => h.ge))

def positionLinear : Space 𝕜 potential →ₗ[𝕜] L2 𝕜 :=
    { toFun := position
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [position_coe (u + v), position_coe u, position_coe v,
          Lp.coeFn_add (position u) (position v), Lp.coeFn_add (value u) (value v)]
          with x huv hu hv hadd hval
        change position (u + v) x = (position u + position v) x
        rw [huv, hadd]
        simp only [Pi.add_apply]
        rw [hu, hv]
        change (x 0 : 𝕜) * (value u + value v) x = _
        rw [hval]
        exact mul_add _ _ _
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [position_coe (c • u), position_coe u,
          Lp.coeFn_smul c (position u), Lp.coeFn_smul c (value u)]
          with x hcu hu hsmul hval
        change position (c • u) x = (c • position u) x
        rw [hcu, hsmul]
        simp only [Pi.smul_apply]
        rw [hu]
        change (x 0 : 𝕜) * (c • value u) x = _
        rw [hval]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring }

def positionL : Space 𝕜 potential →L[𝕜] L2 𝕜 :=
  positionLinear.mkContinuous 1 (by
    intro u
    change ‖position u‖ ≤ 1 * ‖u‖
    rw [one_mul, position_norm]
    exact weighted_norm_le u)

@[simp] lemma positionL_apply (u : Space 𝕜 potential) : positionL u = position u := rfl

end Position

theorem position_exists : Spec.PositionExists := by
  intro 𝕜 _ u
  exact ⟨position u, position_coe u, position_norm u⟩



section GroundState
open ExpandedFA.Distributions
variable {𝕜 : Type} [RCLike 𝕜]

lemma coordinate_ibp (φ : Tests 𝕜 (⊤ : Opens Line)) :
    (∫ x : Line, ‖φ x‖^2) =
      -(∫ x : Line, x 0 * (2 * ⟪φ x, testPartialCLM [0] φ x⟫_ℝ)) := by
  let g : Line → ℝ := fun x => ‖φ x‖^2
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := φ.contDiff.norm_sq 𝕜
  have hgs : HasCompactSupport g :=
    φ.hasCompactSupport.comp_left (g := fun z : 𝕜 => ‖z‖^2) (by simp)
  have hg' : Continuous (fun x => fderiv ℝ g x (coordinateVector (0 : Fin 1))) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcoord : ContDiff ℝ (⊤ : ℕ∞) (fun x : Line => x 0) :=
    (ContinuousLinearMap.proj (0 : Fin 1) : Line →L[ℝ] ℝ).contDiff
  have hi₁ : Integrable (fun x : Line =>
      fderiv ℝ (fun y : Line => y 0) x (coordinateVector (0 : Fin 1)) * g x) :=
    (((hcoord.continuous_fderiv (by simp)).clm_apply continuous_const).mul hg.continuous).integrable_of_hasCompactSupport hgs.mul_left
  have hi₂ : Integrable (fun x : Line => x 0 * fderiv ℝ g x (coordinateVector (0 : Fin 1))) :=
    ((continuous_apply 0).mul hg').integrable_of_hasCompactSupport
      (hgs.fderiv_apply ℝ (coordinateVector (0 : Fin 1))).mul_left
  have hi₃ : Integrable (fun x : Line => x 0 * g x) :=
    ((continuous_apply 0).mul hg.continuous).integrable_of_hasCompactSupport hgs.mul_left
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₃
    (fun x _ => hcoord.differentiable (by simp) x)
    (fun x _ => hg.differentiable (by simp) x)
  have hder (x : Line) :
      fderiv ℝ (fun y : Line => y 0) x (coordinateVector (0 : Fin 1)) = 1 := by
    rw [(hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 1) x).fderiv]
    simp [coordinateVector]
  simp only [hder, one_mul] at hi
  change (∫ x, x 0 * fderiv ℝ (fun y => ‖φ y‖^2) x (coordinateVector (0 : Fin 1))) = -_ at hi
  simp_rw [test_norm_sq_fderiv] at hi
  linarith

lemma smooth_ground_state_identity (u : Space 𝕜 potential)
    (φ : Tests 𝕜 (⊤ : Opens Line)) (hu : value u =ᵐ[lineMeasure] φ) :
    ‖derivative u + position u‖^2 =
      ‖derivative u‖^2 + ‖position u‖^2 - ‖value u‖^2 := by
  have hd := smooth_derivative_ae u φ hu
  have hpos := position_coe u
  have hip : ⟪derivative u, position u⟫_ℝ =
      ∫ x : Line, x 0 * ⟪φ x, testPartialCLM [0] φ x⟫_ℝ := by
    rw [L2.inner_def]
    simp only [lineMeasure, Opens.coe_top, Measure.restrict_univ]
    apply integral_congr_ae
    simp only [IsPosition, lineMeasure, Opens.coe_top, Measure.restrict_univ] at hd hpos hu
    filter_upwards [hd, hpos, hu] with x hx hy hz
    rw [hx, hy, hz, ← RCLike.real_smul_eq_coe_mul, real_inner_smul_right,
      real_inner_comm]
  have hn : ‖value u‖^2 = ∫ x : Line, ‖φ x‖^2 := by
    rw [WeightedConfiningEnergySpace.l2_norm_sq_integral]
    simp only [lineMeasure, Opens.coe_top, Measure.restrict_univ]
    apply integral_congr_ae
    simp only [lineMeasure, Opens.coe_top, Measure.restrict_univ] at hu
    exact hu.mono fun x hx => by simpa only [hx]
  have hi := coordinate_ibp φ
  have he : (∫ x : Line, x 0 * (2 * ⟪φ x, testPartialCLM [0] φ x⟫_ℝ)) =
      2 * ∫ x : Line, x 0 * ⟪φ x, testPartialCLM [0] φ x⟫_ℝ := by
    rw [← integral_const_mul]
    congr 1
    ext x
    ring
  rw [he, ← hip, ← hn] at hi
  rw [norm_add_sq_real]
  linarith

lemma ground_state_identity_position (u : Space 𝕜 potential) :
    ‖derivative u + position u‖^2 =
      ‖derivative u‖^2 + ‖position u‖^2 - ‖value u‖^2 := by
  let Z : Set (Space 𝕜 potential) := {u |
    ‖derivative u + position u‖^2 =
      ‖derivative u‖^2 + ‖position u‖^2 - ‖value u‖^2}
  have hclosed : IsClosed Z := isClosed_eq
    (((derivativeL potential).continuous.add positionL.continuous).norm.pow 2)
    ((((derivativeL potential).continuous.norm.pow 2).add
      (positionL.continuous.norm.pow 2)).sub ((valueL potential).continuous.norm.pow 2))
  have hsub : SmoothMembers 𝕜 potential ⊆ Z := by
    rintro v ⟨φ, hv⟩
    exact smooth_ground_state_identity v φ hv
  exact closure_minimal hsub hclosed (weighted_smooth_density 𝕜 potential u)

end GroundState

theorem ground_state_identity : Spec.GroundStateIdentity := by
  intro 𝕜 _ u w hw
  rw [position_unique u hw]
  exact ground_state_identity_position u

theorem ground_state_inequality : Spec.GroundStateInequality := by
  intro 𝕜 _ u w hw
  have hi := ground_state_identity 𝕜 u w hw
  nlinarith [sq_nonneg ‖derivative u + w‖]



section HermiteCoordinates
variable (𝕜 : Type) [RCLike 𝕜]

lemma coordinate_measure_preserving :
    MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ) lineMeasure volume := by
  exact (volume_preserving_funUnique (Fin 1) ℝ).comp line_to_volume

/-- Unitary change from the ordinary real line to the upstream Sobolev line.
Product Lebesgue volume has no scaling factor in dimension one. -/
def realLineL2Equiv : Lp 𝕜 2 (volume : Measure ℝ) ≃ₗᵢ[𝕜] L2 𝕜 :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ 𝕜 (MeasurableEquiv.funUnique (Fin 1) ℝ)
      coordinate_measure_preserving) (by
        intro u
        let e := MeasurableEquiv.funUnique (Fin 1) ℝ
        have hs : MeasurePreserving e.symm volume lineMeasure :=
          MeasurePreserving.symm e coordinate_measure_preserving
        let v := Lp.compMeasurePreserving e.symm hs u
        refine ⟨v, Lp.ext ?_⟩
        have hv := coordinate_measure_preserving.quasiMeasurePreserving.ae
          (Lp.coeFn_compMeasurePreserving u hs)
        filter_upwards [Lp.coeFn_compMeasurePreserving v coordinate_measure_preserving, hv]
          with x hx hy
        apply hx.trans
        change v (e x) = u x
        change v (e x) = u (e.symm (e x)) at hy
        simpa only [e.symm_apply_apply] using hy)

lemma realLineL2Equiv_coe (u : Lp 𝕜 2 (volume : Measure ℝ)) :
    realLineL2Equiv 𝕜 u =ᵐ[lineMeasure] fun x => u (x 0) := by
  exact Lp.coeFn_compMeasurePreserving u coordinate_measure_preserving

theorem hermite_basis_exists : Spec.HermiteBasisExists := by
  intro 𝕜 _
  obtain ⟨b, hb⟩ := HermiteBasis.complete_orthonormal_basis 𝕜
  let E := realLineL2Equiv 𝕜
  let c : HilbertBasis ℕ 𝕜 (L2 𝕜) := ⟨E.symm.trans b.repr⟩
  refine ⟨c, ?_⟩
  intro n
  have he : c n = E (b n) := rfl
  rw [he]
  have hb' := coordinate_measure_preserving.quasiMeasurePreserving.ae (hb n)
  exact (realLineL2Equiv_coe 𝕜 (b n)).trans hb'

end HermiteCoordinates



section Spectral
variable {𝕜 H : Type} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Exact coefficient domain for an inverse once its specified eigenvectors
have been proved. The lemma assumes only the explicit inverse graph. -/
lemma inverse_domain_of_eigenvectors (T : H →L[𝕜] H) (hs : T.IsSymmetric)
    (A : H →ₗ.[𝕜] H) (hg : ∀ u f, (u, f) ∈ A.graph ↔ T f = u)
    (b : HilbertBasis ℕ 𝕜 H) (a : ℕ → ℝ) (ha : ∀ n, a n ≠ 0)
    (he : ∀ n, (b n, (a n : 𝕜) • b n) ∈ A.graph) (u : H) :
    u ∈ A.domain ↔ Summable (fun n => (a n)^2 * ‖⟪b n, u⟫_𝕜‖^2) := by
  have ht (n : ℕ) : T (b n) = (((a n)⁻¹ : ℝ) : 𝕜) • b n := by
    have hn : (a n : 𝕜) ≠ 0 := by exact_mod_cast ha n
    have hv := (hg (b n) ((a n : 𝕜) • b n)).mp (he n)
    rw [map_smul] at hv
    have hh := congrArg (fun z : H => (a n : 𝕜)⁻¹ • z) hv
    simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul, RCLike.ofReal_inv] using hh
  have hdom : u ∈ A.domain ↔ u ∈ T.range := by
    rw [LinearPMap.mem_domain_iff]
    constructor
    · rintro ⟨f, hf⟩
      exact ⟨f, (hg u f).mp hf⟩
    · rintro ⟨f, hf⟩
      exact ⟨f, (hg u f).mpr hf⟩
  rw [hdom]
  simpa only [inv_inv] using diagonal_range T b (fun n => (a n)⁻¹)
    (fun n => inv_ne_zero (ha n)) ht hs u

end Spectral

/-- Exact first-order equality criterion. Identifying its kernel with Gaussian
multiples remains a separate mathematical step. -/
lemma ground_equality_iff_annihilation {𝕜 : Type} [RCLike 𝕜]
    (u : Space 𝕜 potential) (w : L2 𝕜) (hw : IsPosition u w) :
    ‖derivative u‖^2 + ‖w‖^2 = ‖value u‖^2 ↔ derivative u + w = 0 := by
  have hi := ground_state_identity 𝕜 u w hw
  constructor
  · intro he
    have hz : ‖derivative u + w‖^2 = 0 := by linarith
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · intro hz
    rw [hz, norm_zero, zero_pow (by decide)] at hi
    linarith

lemma realization_unique {𝕜 : Type} [RCLike 𝕜]
    {A B : L2 𝕜 →ₗ.[𝕜] L2 𝕜} (hA : IsRealization A) (hB : IsRealization B) : A = B := by
  apply LinearPMap.eq_of_eq_graph
  ext z
  exact (hA z.1 z.2).trans (hB z.1 z.2).symm

lemma realization_self_adjoint {𝕜 : Type} [RCLike 𝕜]
    {A : L2 𝕜 →ₗ.[𝕜] L2 𝕜} (hA : IsRealization A) : A.adjoint = A := by
  obtain ⟨B, hB, _, hs, _⟩ := realization_and_compact_resolvent 𝕜
  rwa [realization_unique hB hA] at hs

lemma hermite_basis_unique {𝕜 : Type} [RCLike 𝕜]
    {b c : HilbertBasis ℕ 𝕜 (L2 𝕜)} (hb : IsHermiteBasis b) (hc : IsHermiteBasis c) :
    (b : ℕ → L2 𝕜) = c := by
  funext n
  exact Lp.ext ((hb n).trans (hc n).symm)

section Factorization
variable {𝕜 : Type} [RCLike 𝕜]

private def pairL (F G : Space 𝕜 potential →L[𝕜] L2 𝕜) :
    Space 𝕜 potential →L[𝕜] WithLp 2 (L2 𝕜 × L2 𝕜) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 (L2 𝕜) (L2 𝕜)).symm.toContinuousLinearMap.comp
    (F.prod G)

lemma ground_state_form_identity (v u : Space 𝕜 potential) :
    energyForm v u = ⟪derivative v + position v, derivative u + position u⟫_𝕜 +
      ⟪value v, value u⟫_𝕜 := by
  let D := pairL (𝕜 := 𝕜) (derivativeL potential) (weightedL potential)
  let B := pairL (𝕜 := 𝕜) (derivativeL potential + positionL) (valueL potential)
  have hn (w : Space 𝕜 potential) : ‖D w‖ = ‖B w‖ := by
    have hi := ground_state_identity_position w
    have hd : ‖D w‖^2 = ‖derivative w‖^2 + ‖weighted w‖^2 :=
      WithLp.prod_norm_sq_eq_of_L2 _
    have hb : ‖B w‖^2 = ‖derivative w + position w‖^2 + ‖value w‖^2 :=
      WithLp.prod_norm_sq_eq_of_L2 _
    rw [position_norm] at hi
    nlinarith [norm_nonneg (D w), norm_nonneg (B w)]
  have he : ⟪D v, D u⟫_𝕜 = ⟪B v, B u⟫_𝕜 := by
    simp only [inner_eq_sum_norm_sq_div_four, ← map_add, ← map_sub, ← map_smul, hn]
  simpa only [D, B, pairL, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_symm_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
    WithLp.prod_inner_apply, WithLp.toLp_fst, WithLp.toLp_snd, Prod.fst, Prod.snd,
    derivativeL_apply, weightedL_apply, positionL_apply, valueL_apply, energyForm] using he

/-- Equality vectors already lie in the operator domain and have eigenvalue
one. This reduces Gaussian classification to the Hermite eigenbasis bridge. -/
lemma ground_equality_graph {𝕜 : Type} [RCLike 𝕜]
    (A : L2 𝕜 →ₗ.[𝕜] L2 𝕜) (hA : IsRealization A)
    (u : Space 𝕜 potential) (hu : ‖derivative u‖^2 + ‖weighted u‖^2 = ‖value u‖^2) :
    (value u, value u) ∈ A.graph := by
  have hz : derivative u + position u = 0 := by
    apply (ground_equality_iff_annihilation u (position u) (position_coe u)).mp
    simpa only [position_norm] using hu
  apply (hA _ _).mpr
  refine ⟨u, rfl, (form_distribution_equivalence 𝕜 potential u (value u)).mpr ?_⟩
  intro v
  rw [ground_state_form_identity, hz, inner_zero_right, zero_add]

end Factorization

lemma compact_resolvents_of_inverse {𝕜 : Type} [RCLike 𝕜]
    (T : L2 𝕜 →L[𝕜] L2 𝕜) (hc : IsCompactOperator T)
    (A : L2 𝕜 →ₗ.[𝕜] L2 𝕜)
    (hg : ∀ u f, (u, f) ∈ A.graph ↔ T f = u)
    (ζ : 𝕜) (R : ExpandedFA.Unbounded.ResolventInverse A ζ) :
    IsCompactOperator R.inverse := by
  have he : R.inverse = ζ • (T.comp R.inverse) - T := by
    apply ContinuousLinearMap.ext
    intro y
    have ha : A ⟨R.inverse y, R.mem_domain y⟩ = ζ • R.inverse y - y :=
      eq_sub_iff_add_eq.mpr (by
        simpa only [add_comm] using (sub_eq_iff_eq_add.mp (R.right_inverse y)).symm)
    have ht := (hg (R.inverse y) (A ⟨R.inverse y, R.mem_domain y⟩)).mp
      (A.mem_graph ⟨R.inverse y, R.mem_domain y⟩)
    rw [ha, map_sub, map_smul] at ht
    exact ht.symm
  rw [he]
  exact ((hc.comp_clm R.inverse).smul ζ).sub hc



/-- Once the differential eigenvector bridge is supplied, the full domain
criterion follows from the checked inverse-range theorem, without an extra
Sobolev or convergence assumption on the vector. -/
lemma spectral_domain_of_eigenvectors (hE : Spec.Eigenvectors) : Spec.SpectralDomain := by
  intro 𝕜 _ A hA b hb u
  obtain ⟨T, _, hs, _, _, _, B, hg, _, _, _, hB, _⟩ :=
    confining_realization 𝕜 potential positive_at_infinity
  have hBA : B = A := realization_unique hB hA
  subst B
  exact inverse_domain_of_eigenvectors T
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hs) A hg b
    (fun n : ℕ => 2 * (n : ℝ) + 1)
    (fun n => ne_of_gt (by positivity)) (hE 𝕜 A hA b hb) u



section WeakEnergy
open ExpandedFA.Sobolev ExpandedFA.Distributions
variable {𝕜 : Type} [RCLike 𝕜]

/-- Construct an actual weighted Sobolev member from its three L² components.
The sole analytic premise is the defining weak first derivative equation. -/
lemma energy_of_weak_derivative (f d w : L2 𝕜)
    (hd : ∀ ψ : Tests 𝕜 (⊤ : Opens Line),
      lpDistribution d ψ = -lpDistribution f (testPartialCLM [0] ψ))
    (hw : w =ᵐ[lineMeasure] fun x => weight 𝕜 potential x * f x) :
    ∃ u : Space 𝕜 potential, value u = f ∧ derivative u = d ∧ weighted u = w := by
  classical
  have hne : firstIndex ≠ zeroIndex 1 1 := by
    intro h
    have hh := congrArg (fun α : DerivativeIndex 1 1 => α.val 0) h
    norm_num [firstIndex, zeroIndex] at hh
  let jet : PiLp 2 (fun _ : DerivativeIndex 1 1 => L2 𝕜) :=
    WithLp.toLp 2 (fun α => if α = zeroIndex 1 1 then f else d)
  have hj0 : jet (zeroIndex 1 1) = f := by simp [jet]
  have hj1 : jet firstIndex = d := by simp [jet, hne]
  have hj : jet ∈ hilbertDerivativeGraph 𝕜 (⊤ : Opens Line) 1 := by
    intro α
    change lpDistribution (jet α) =
      Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
        𝕜 1 (⊤ : Opens Line) (natIndex α) (lpDistribution (jet (zeroIndex 1 1)))
    have hcases : α = zeroIndex 1 1 ∨ α = firstIndex := by
      have hα := indexEquiv.symm_apply_apply α
      generalize indexEquiv α = i at hα
      fin_cases i
      · exact Or.inl hα.symm
      · exact Or.inr hα.symm
    rcases hcases with rfl | rfl
    · rw [hj0]
      exact (derivative_zero (lpDistribution f)).symm
    · rw [hj0, hj1]
      ext ψ
      simpa only [Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue,
        firstIndex_word, Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue,
        List.length_singleton, pow_one, smul_apply,
        ContinuousLinearMap.comp_apply, smul_eq_mul, neg_one_mul] using hd ψ
  let h : H1 𝕜 := ⟨jet, hj⟩
  let u : Space 𝕜 potential := ⟨WithLp.toLp 2 (h, w), by
    change w =ᵐ[lineMeasure] fun x => weight 𝕜 potential x * jet (zeroIndex 1 1) x
    rw [hj0]
    exact hw⟩
  exact ⟨u, hj0, hj1, rfl⟩

end WeakEnergy

section SmoothDerivative
open ExpandedFA.Sobolev ExpandedFA.Distributions
variable {𝕜 : Type} [RCLike 𝕜]

lemma weak_derivative_of_smooth (F : Line → 𝕜) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (f d : L2 𝕜) (hf : f =ᵐ[lineMeasure] F)
    (hd : d =ᵐ[lineMeasure] fun x => fderiv ℝ F x (coordinateVector (0 : Fin 1))) :
    ∀ ψ : Tests 𝕜 (⊤ : Opens Line),
      lpDistribution d ψ = -lpDistribution f (testPartialCLM [0] ψ) := by
  intro ψ
  have hD : Continuous (fun x => fderiv ℝ F x (coordinateVector (0 : Fin 1))) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψ : Continuous (fun x => fderiv ℝ ψ x (coordinateVector (0 : Fin 1))) :=
    (ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi₁ : Integrable (fun x => fderiv ℝ F x (coordinateVector (0 : Fin 1)) * ψ x) :=
    (hD.mul ψ.continuous).integrable_of_hasCompactSupport ψ.hasCompactSupport.mul_left
  have hi₂ : Integrable (fun x => F x * fderiv ℝ ψ x (coordinateVector (0 : Fin 1))) :=
    (hF.continuous.mul hψ).integrable_of_hasCompactSupport
      (ψ.hasCompactSupport.fderiv_apply ℝ (coordinateVector (0 : Fin 1))).mul_left
  have hi₃ : Integrable (fun x => F x * ψ x) :=
    (hF.continuous.mul ψ.continuous).integrable_of_hasCompactSupport ψ.hasCompactSupport.mul_left
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₃
    (fun x _ => hF.differentiable (by simp) x)
    (fun x _ => ψ.contDiff.differentiable (by simp) x)
  have hdf : lpDistribution d ψ =
      ∫ x : Line, fderiv ℝ F x (coordinateVector (0 : Fin 1)) * ψ x := by
    rw [lpDistribution_apply]
    simp only [lineMeasure, Opens.coe_top, Measure.restrict_univ] at hd ⊢
    apply integral_congr_ae
    filter_upwards [hd] with x hx
    simp only [hx, mul_comm]
  have hff : lpDistribution f (testPartialCLM [0] ψ) =
      ∫ x : Line, F x * fderiv ℝ ψ x (coordinateVector (0 : Fin 1)) := by
    rw [lpDistribution_apply]
    simp only [lineMeasure, Opens.coe_top, Measure.restrict_univ] at hf ⊢
    apply integral_congr_ae
    filter_upwards [hf] with x hx
    simp only [hx, testPartial_single_apply, mul_comm]
  rw [hdf, hff]
  exact (neg_eq_iff_eq_neg.mpr hi).symm

end SmoothDerivative



section GaussianPolynomials
open Polynomial

private def gaussianPolynomial (P : ℝ[X]) (c : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-(x^2)/2) * P.eval x / c

private lemma gaussianPolynomial_deriv (P : ℝ[X]) (c : ℝ) :
    deriv (gaussianPolynomial P c) = gaussianPolynomial (P.derivative - X * P) c := by
  funext x
  change deriv (fun y => Real.exp (-(y^2)/2) * P.eval y / c) x =
    Real.exp (-(x^2)/2) * (P.derivative - X * P).eval x / c
  simpa only [eval_sub, eval_mul, eval_X] using
    ((HermiteBasis.gaussian_polynomial_hasDerivAt P x).div_const c).deriv

private lemma gaussianPolynomial_memLp (P : ℝ[X]) (c : ℝ) :
    MemLp (gaussianPolynomial P c) 2 volume := by
  change MemLp (fun x => Real.exp (-(x^2)/2) * P.eval x / c) 2 volume
  simpa only [ div_eq_mul_inv, mul_comm c⁻¹] using
    (HermiteBasis.polynomial_half_gaussian_memLp P).const_mul c⁻¹

lemma hermite_derivative_memLp (n : ℕ) : MemLp (deriv (HermiteBasis.h n)) 2 volume := by
  rw [HermiteBasis.h_polynomial]
  change MemLp (deriv (gaussianPolynomial (HermiteBasis.physicistsHermite n)
    (HermiteBasis.normalization n))) 2 volume
  rw [gaussianPolynomial_deriv]
  exact gaussianPolynomial_memLp _ _

lemma hermite_second_derivative_memLp (n : ℕ) :
    MemLp (deriv (deriv (HermiteBasis.h n))) 2 volume := by
  rw [HermiteBasis.h_polynomial]
  change MemLp (deriv (deriv (gaussianPolynomial (HermiteBasis.physicistsHermite n)
    (HermiteBasis.normalization n)))) 2 volume
  rw [gaussianPolynomial_deriv, gaussianPolynomial_deriv]
  exact gaussianPolynomial_memLp _ _

lemma hermite_power_memLp (n k : ℕ) :
    MemLp (fun x : ℝ => x^k * HermiteBasis.h n x) 2 volume := by
  convert gaussianPolynomial_memLp ((X^k) * HermiteBasis.physicistsHermite n)
    (HermiteBasis.normalization n) using 1
  ext x
  rw [HermiteBasis.h_polynomial]
  simp only [gaussianPolynomial, eval_mul, eval_pow, eval_X]
  ring

end GaussianPolynomials

section RealSmoothEnergy
open ExpandedFA.Sobolev ExpandedFA.Distributions
variable {𝕜 : Type} [RCLike 𝕜]

lemma coordinate_fderiv (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : Line) :
    fderiv ℝ (fun y : Line => (f (y 0) : 𝕜)) x (coordinateVector (0 : Fin 1)) =
      ((deriv f (x 0) : ℝ) : 𝕜) := by
  have hp := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 1) x
  have hh := ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).hasFDerivAt).comp x
    ((hf (x 0)).hasDerivAt.hasFDerivAt.comp x hp)
  change fderiv ℝ ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) ∘ f ∘ (fun y : Line => y 0)) x
    (coordinateVector (0 : Fin 1)) = _
  rw [hh.fderiv]
  simp [coordinateVector]

lemma coordinate_smooth (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Line => (f (x 0) : 𝕜)) :=
  (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp
    (hf.comp (ContinuousLinearMap.proj (0 : Fin 1) : Line →L[ℝ] ℝ).contDiff)

/-- All components are built from the real function; no membership certificate
is assumed for the original Hermite representative. -/
lemma real_smooth_energy (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf₂ : MemLp f 2 volume) (hd₂ : MemLp (deriv f) 2 volume)
    (hx₂ : MemLp (fun x : ℝ => x * f x) 2 volume) :
    ∃ u : Space 𝕜 potential,
      (value u =ᵐ[lineMeasure] fun x => (f (x 0) : 𝕜)) ∧
      (derivative u =ᵐ[lineMeasure] fun x => ((deriv f (x 0) : ℝ) : 𝕜)) := by
  have hm : MemLp (fun x : ℝ => |x| * f x) 2 volume := by
    apply hx₂.norm.mono' ((continuous_abs.mul hf.continuous).aestronglyMeasurable)
    filter_upwards [] with x
    simp [abs_mul]
  have hF : MemLp (fun x : Line => (f (x 0) : 𝕜)) 2 lineMeasure :=
    (hf₂.ofReal (K := 𝕜)).comp_measurePreserving coordinate_measure_preserving
  have hD : MemLp (fun x : Line => ((deriv f (x 0) : ℝ) : 𝕜)) 2 lineMeasure :=
    (hd₂.ofReal (K := 𝕜)).comp_measurePreserving coordinate_measure_preserving
  have hW : MemLp (fun x : Line => ((|x 0| * f (x 0) : ℝ) : 𝕜)) 2 lineMeasure :=
    (hm.ofReal (K := 𝕜)).comp_measurePreserving coordinate_measure_preserving
  let F := hF.toLp _
  let D := hD.toLp _
  let W := hW.toLp _
  have hdf : D =ᵐ[lineMeasure] fun x =>
      fderiv ℝ (fun y : Line => (f (y 0) : 𝕜)) x (coordinateVector (0 : Fin 1)) := by
    filter_upwards [hD.coeFn_toLp] with x hx
    rw [hx, coordinate_fderiv f (hf.differentiable (by simp))]
  have hweight : W =ᵐ[lineMeasure] fun x => weight 𝕜 potential x * F x := by
    filter_upwards [hW.coeFn_toLp, hF.coeFn_toLp] with x hx hy
    rw [hx, hy]
    simp [weight, Real.sqrt_sq_eq_abs]
  obtain ⟨u, hu, hd, _⟩ := energy_of_weak_derivative F D W
    (weak_derivative_of_smooth _ (coordinate_smooth f hf) F D hF.coeFn_toLp hdf) hweight
  exact ⟨u, hu ▸ hF.coeFn_toLp, hd ▸ hD.coeFn_toLp⟩

lemma hermite_energy (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    ∃ u : Space 𝕜 potential,
      (value u =ᵐ[lineMeasure] fun x => (HermiteBasis.h n (x 0) : 𝕜)) ∧
      (derivative u =ᵐ[lineMeasure] fun x => ((deriv (HermiteBasis.h n) (x 0) : ℝ) : 𝕜)) :=
  real_smooth_energy (HermiteBasis.h n) (HermiteBasis.smooth n)
    (HermiteBasis.square_integrable n) (hermite_derivative_memLp n)
    (by simpa only [pow_one] using hermite_power_memLp n 1)

end RealSmoothEnergy



section DifferentialAction
open ExpandedFA.Sobolev ExpandedFA.Distributions
variable {𝕜 : Type} [RCLike 𝕜]

lemma real_smooth_distribution_equation (f : ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (u : Space 𝕜 potential)
    (hu : value u =ᵐ[lineMeasure] fun x => (f (x 0) : 𝕜))
    (hdu : derivative u =ᵐ[lineMeasure] fun x => ((deriv f (x 0) : ℝ) : 𝕜))
    (hdd : MemLp (deriv (deriv f)) 2 volume)
    (hx : MemLp (fun x : ℝ => x^2 * f x) 2 volume)
    (ev : ℝ) (heq : ∀ x, -deriv (deriv f) x + x^2 * f x = ev * f x) :
    DistributionEquation u ((ev : 𝕜) • value u) := by
  have hf' : ContDiff ℝ (⊤ : ℕ∞) (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hd₂ : MemLp (fun x : Line => ((deriv (deriv f) (x 0) : ℝ) : 𝕜)) 2 lineMeasure :=
    (hdd.ofReal (K := 𝕜)).comp_measurePreserving coordinate_measure_preserving
  have hx₂ : MemLp (fun x : Line => ((x 0)^2 * f (x 0) : ℝ)) 2 lineMeasure :=
    hx.comp_measurePreserving coordinate_measure_preserving
  let D := hd₂.toLp _
  let X := (hx₂.ofReal (K := 𝕜)).toLp _
  have hD := hd₂.coeFn_toLp
  have hX := (hx₂.ofReal (K := 𝕜)).coeFn_toLp
  have hdf : D =ᵐ[lineMeasure] fun x =>
      fderiv ℝ (fun y : Line => ((deriv f (y 0) : ℝ) : 𝕜)) x (coordinateVector (0 : Fin 1)) := by
    filter_upwards [hD] with x hx
    rw [hx, coordinate_fderiv (deriv f) (hf'.differentiable (by simp))]
  have hweak := weak_derivative_of_smooth _ (coordinate_smooth (deriv f) hf')
    (derivative u) D hdu hdf
  have haction : -D + X = (ev : 𝕜) • value u := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (-D) X, Lp.coeFn_neg D, hD, hX,
      Lp.coeFn_smul (ev : 𝕜) (value u), hu] with x hadd hneg hd hx hsmul hval
    change (-D + X) x = ((ev : 𝕜) • value u) x
    rw [hadd, hsmul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hneg]
    simp only [Pi.neg_apply]
    rw [hd, hx, hval]
    have hh := congrArg (fun t : ℝ => (t : 𝕜)) (heq (x 0))
    simpa only [map_add, map_neg, map_mul, RCLike.ofReal_add, RCLike.ofReal_neg,
      RCLike.ofReal_mul] using hh
  intro φ
  have hsecond : lpDistribution (value u) (testPartialCLM [0, 0] φ) = lpDistribution D φ := by
    have h₁ := derivative_testing u (testPartialCLM [0] φ)
    have h₂ := hweak φ
    change lpDistribution (derivative u) (testPartialCLM [0] φ) =
      -lpDistribution (value u) (testPartialCLM [0, 0] φ) at h₁
    rw [h₁, neg_neg] at h₂
    exact h₂.symm
  have hpot : (∫ x, (potential.toContinuousMap (x 0) : 𝕜) * φ x * value u x ∂lineMeasure) =
      lpDistribution X φ := by
    rw [lpDistribution_apply]
    apply integral_congr_ae
    filter_upwards [hu, hX] with x hx hy
    change (potential.toContinuousMap (x 0) : 𝕜) * φ x * value u x = φ x * X x
    rw [hx, hy, potential_apply, RCLike.ofReal_mul]
    ring
  change -lpDistribution (value u) (testPartialCLM [0, 0] φ) + _ = _
  rw [hsecond, hpot]
  calc
    _ = lpDistribution (-D + X) φ := by
      change (-lpDistributionLM D + lpDistributionLM X) φ = lpDistributionLM (-D + X) φ
      rw [map_add, map_neg]
    _ = _ := by rw [haction]

end DifferentialAction

theorem eigenvectors : Spec.Eigenvectors := by
  intro 𝕜 _ A hA b hb n
  obtain ⟨u, hu, hdu⟩ := hermite_energy 𝕜 n
  have hv : value u = b n := Lp.ext (hu.trans (hb n).symm)
  have he := real_smooth_distribution_equation (HermiteBasis.h n) (HermiteBasis.smooth n)
    u hu hdu (hermite_second_derivative_memLp n) (hermite_power_memLp n 2)
    (2 * (n : ℝ) + 1) (HermiteBasis.differential_equation n)
  rw [← hv]
  exact (hA _ _).mpr ⟨u, rfl, he⟩

theorem spectral_domain : Spec.SpectralDomain := spectral_domain_of_eigenvectors eigenvectors



section GroundClassification
variable {𝕜 : Type} [RCLike 𝕜]

lemma realization_dense {A : L2 𝕜 →ₗ.[𝕜] L2 𝕜} (hA : IsRealization A) :
    Dense (A.domain : Set (L2 𝕜)) := by
  obtain ⟨B, hB, hd, _⟩ := realization_and_compact_resolvent 𝕜
  rwa [realization_unique hB hA] at hd

lemma eigenvalue_one_span (A : L2 𝕜 →ₗ.[𝕜] L2 𝕜) (hA : IsRealization A)
    (b : HilbertBasis ℕ 𝕜 (L2 𝕜)) (hb : IsHermiteBasis b)
    (u : L2 𝕜) (hu : (u, u) ∈ A.graph) : u = ⟪b 0, u⟫_𝕜 • b 0 := by
  have hs : A.IsFormalAdjoint A := by
    have hh := A.adjoint_isFormalAdjoint (realization_dense hA)
    rwa [realization_self_adjoint hA] at hh
  let v : A.domain := ⟨u, LinearPMap.mem_domain_of_mem_graph hu⟩
  have hv : A v = u := A.mem_graph_snd_inj (A.mem_graph v) hu rfl
  have hz (n : ℕ) (hn : n ≠ 0) : ⟪b n, u⟫_𝕜 = 0 := by
    have he := eigenvectors 𝕜 A hA b hb n
    let e : A.domain := ⟨b n, LinearPMap.mem_domain_of_mem_graph he⟩
    have hae : A e = ((2 * (n : ℝ) + 1 : ℝ) : 𝕜) • b n :=
      A.mem_graph_snd_inj (A.mem_graph e) he rfl
    have hh := hs e v
    change ⟪A e, u⟫_𝕜 = ⟪b n, A v⟫_𝕜 at hh
    rw [hae, hv, inner_smul_left, RCLike.conj_ofReal] at hh
    have hmul : (((2 * (n : ℝ) + 1 : ℝ) : 𝕜) - 1) * ⟪b n, u⟫_𝕜 = 0 := by
      rw [sub_mul, one_mul, hh, sub_self]
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hneReal : 2 * (n : ℝ) + 1 ≠ 1 := ne_of_gt (by linarith)
    have hne : ((2 * (n : ℝ) + 1 : ℝ) : 𝕜) ≠ 1 := by exact_mod_cast hneReal
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)
  apply b.repr.injective
  apply lp.ext
  funext n
  rw [b.repr_apply_apply, b.repr_apply_apply, inner_smul_right]
  rw [(orthonormal_iff_ite.mp b.orthonormal) n 0]
  by_cases hn : n = 0
  · subst n
    simp
  · simp [hn, hz n hn]

lemma hermite_zero (x : ℝ) : HermiteBasis.h 0 x =
    Real.exp (-(x^2)/2) / HermiteBasis.normalization 0 := by
  rw [HermiteBasis.h_polynomial]
  simp [HermiteBasis.physicistsHermite_zero]

theorem ground_state_equality : Spec.GroundStateEquality := by
  intro 𝕜 _ u w hw
  have hwN : ‖w‖ = ‖weighted u‖ := by rw [position_unique u hw, position_norm]
  obtain ⟨A, hA, _⟩ := realization_and_compact_resolvent 𝕜
  obtain ⟨b, hb⟩ := hermite_basis_exists 𝕜
  constructor
  · intro he
    have hg : (value u, value u) ∈ A.graph := ground_equality_graph A hA u (by rwa [← hwN])
    have hu := eigenvalue_one_span A hA b hb (value u) hg
    let c := ⟪b 0, value u⟫_𝕜
    refine ⟨c / (HermiteBasis.normalization 0 : 𝕜), ?_⟩
    rw [hu]
    filter_upwards [Lp.coeFn_smul c (b 0), hb 0] with x hx hy
    change (c • b 0) x = (c / (HermiteBasis.normalization 0 : 𝕜)) *
      (Real.exp (-((x 0)^2)/2) : 𝕜)
    rw [hx]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hy, hermite_zero, RCLike.ofReal_div]
    ring
  · rintro ⟨c, hc⟩
    have he := eigenvectors 𝕜 A hA b hb 0
    simp only [Nat.cast_zero, mul_zero, zero_add, RCLike.ofReal_one, one_smul] at he
    obtain ⟨z, hz, hdz⟩ := (hA _ _).mp he
    have hzenergy : ‖derivative z‖^2 + ‖weighted z‖^2 = ‖value z‖^2 := by
      have hv := (form_distribution_equivalence 𝕜 potential z (b 0)).mp hdz z
      rw [← hz] at hv
      have hr := congrArg RCLike.re hv
      simpa only [energyForm_diagonal, inner_self_eq_norm_sq] using hr
    let a : 𝕜 := c * (HermiteBasis.normalization 0 : 𝕜)
    have huz : u = a • z := by
      apply weighted_underlying_injective 𝕜 potential
      apply Lp.ext
      have hzb : value z =ᵐ[lineMeasure] fun x => (HermiteBasis.h 0 (x 0) : 𝕜) := by
        rw [hz]
        exact hb 0
      filter_upwards [hc, hzb, Lp.coeFn_smul a (value z)] with x hx hy hsmul
      change value u x = (a • value z) x
      rw [hx, hsmul]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hy, hermite_zero, RCLike.ofReal_div]
      dsimp only [a]
      have hn : (HermiteBasis.normalization 0 : 𝕜) ≠ 0 := by
        exact_mod_cast (HermiteBasis.normalization_positive 0).ne'
      field_simp
    rw [hwN, huz]
    change ‖derivativeL potential (a • z)‖^2 + ‖weightedL potential (a • z)‖^2 =
      ‖valueL potential (a • z)‖^2
    simp only [map_smul, norm_smul, mul_pow, derivativeL_apply, weightedL_apply, valueL_apply]
    rw [← mul_add, hzenergy]

end GroundClassification



section SchwartzGaussians
open scoped ContDiff
open Polynomial

private lemma gaussianPolynomial_smooth (P : ℝ[X]) (c : ℝ) :
    ContDiff ℝ ∞ (gaussianPolynomial P c) := by
  change ContDiff ℝ ∞ (fun x => Real.exp (-(x^2)/2) * P.eval x / c)
  exact ((Real.contDiff_exp.comp (((contDiff_id.pow 2).neg).div_const 2)).mul
    (by simpa only [Polynomial.coe_aeval_eq_eval] using P.contDiff_aeval (𝕜 := ℝ) ∞)).div_const c

private lemma gaussianPolynomial_zero_at_infty (P : ℝ[X]) (c : ℝ) :
    Tendsto (gaussianPolynomial P c) (cocompact ℝ) (𝓝 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    convert hP.add hQ using 1
    · ext x
      simp [gaussianPolynomial, mul_add, add_div]
    · simp
  | monomial k a =>
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hh := (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
      (by norm_num : (0 : ℝ) < 1/2) (k : ℝ)).mul_const |a/c|
    convert hh using 1
    · ext x
      simp only [gaussianPolynomial, eval_monomial, Real.norm_eq_abs, abs_div, abs_mul,
        abs_pow, abs_of_pos (Real.exp_pos _), Real.rpow_natCast]
      have he : Real.exp (-(x^2)/2) = Real.exp (-(1/2 : ℝ)*x^2) := by
        congr 1
        ring
      rw [he]
      ring
    · simp

private lemma gaussianPolynomial_bounded (P : ℝ[X]) (c : ℝ) :
    ∃ C : ℝ, ∀ x, ‖gaussianPolynomial P c x‖ ≤ C := by
  let F : ZeroAtInftyContinuousMap ℝ ℝ :=
    { toContinuousMap := ⟨gaussianPolynomial P c, (gaussianPolynomial_smooth P c).continuous⟩
      zero_at_infty' := gaussianPolynomial_zero_at_infty P c }
  obtain ⟨C, hC⟩ := F.isBounded_range.subset_closedBall (0 : ℝ)
  refine ⟨C, fun x => ?_⟩
  change ‖F x‖ ≤ C
  simpa only [Metric.mem_closedBall, dist_zero_right] using hC ⟨x, rfl⟩

/-- Gaussian polynomials are actual Schwartz functions, with decay of every
Fréchet derivative. This is proved rather than added as a membership premise. -/
private def gaussianPolynomialSchwartz (P : ℝ[X]) (c : ℝ) : SchwartzMap ℝ ℝ where
  toFun := gaussianPolynomial P c
  smooth' := gaussianPolynomial_smooth P c
  decay' := by
    intro k n
    have hi : ∀ n : ℕ, ∃ Q : ℝ[X], iteratedDeriv n (gaussianPolynomial P c) =
        gaussianPolynomial Q c := by
      intro n
      induction n with
      | zero => exact ⟨P, by simp⟩
      | succ n ih =>
        obtain ⟨Q, hQ⟩ := ih
        exact ⟨Q.derivative - X * Q, by rw [iteratedDeriv_succ, hQ, gaussianPolynomial_deriv]⟩
    obtain ⟨Q, hQ⟩ := hi n
    obtain ⟨C, hC⟩ := gaussianPolynomial_bounded ((X^k)*Q) c
    refine ⟨C, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hQ]
    convert hC x using 1
    simp only [gaussianPolynomial, eval_mul, eval_pow, eval_X, Real.norm_eq_abs,
      abs_div, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    ring

lemma hermite_schwartz (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    ∃ φ : SchwartzMap Line 𝕜, ∀ x, φ x = (HermiteBasis.h n (x 0) : 𝕜) := by
  let F := gaussianPolynomialSchwartz (HermiteBasis.physicistsHermite n)
    (HermiteBasis.normalization n)
  let G := SchwartzMap.postcompCLM (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) F
  let e : Line ≃L[ℝ] ℝ := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e G, ?_⟩
  intro x
  change (gaussianPolynomial (HermiteBasis.physicistsHermite n)
    (HermiteBasis.normalization n) (x 0) : 𝕜) = _
  rw [HermiteBasis.h_polynomial]
  rfl

end SchwartzGaussians



section SchwartzAction
open ExpandedFA.Sobolev ExpandedFA.Distributions LineDeriv
variable {𝕜 : Type} [RCLike 𝕜]

local instance lineMeasureTemperate : lineMeasure.HasTemperateGrowth := by
  change (volume.restrict (Set.univ : Set Line)).HasTemperateGrowth
  rw [Measure.restrict_univ]
  infer_instance

private def schwartzD : SchwartzMap Line 𝕜 →L[𝕜] SchwartzMap Line 𝕜 :=
  lineDerivOpCLM 𝕜 (SchwartzMap Line 𝕜) (coordinateVector (0 : Fin 1))

private lemma schwartzD_apply (φ : SchwartzMap Line 𝕜) (x : Line) :
    schwartzD φ x = fderiv ℝ φ x (coordinateVector (0 : Fin 1)) :=
  SchwartzMap.lineDerivOp_apply_eq_fderiv _ _ _

private def schwartzX : SchwartzMap Line 𝕜 →L[𝕜] SchwartzMap Line 𝕜 :=
  SchwartzMap.smulLeftCLM 𝕜 (fun x : Line => (x 0 : 𝕜))

private lemma coordinate_temperate : (fun x : Line => (x 0 : 𝕜)).HasTemperateGrowth :=
  ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).comp
    (ContinuousLinearMap.proj (0 : Fin 1) : Line →L[ℝ] ℝ)).hasTemperateGrowth

private lemma schwartzX_apply (φ : SchwartzMap Line 𝕜) (x : Line) :
    schwartzX φ x = (x 0 : 𝕜) * φ x := by
  change SchwartzMap.smulLeftCLM 𝕜 (fun y : Line => (y 0 : 𝕜)) φ x = _
  rw [SchwartzMap.smulLeftCLM_apply_apply (coordinate_temperate (𝕜 := 𝕜))]
  rfl

private def schwartzAction : SchwartzMap Line 𝕜 →L[𝕜] SchwartzMap Line 𝕜 :=
  -(schwartzD.comp schwartzD) + schwartzX.comp schwartzX

private lemma schwartzAction_apply (φ : SchwartzMap Line 𝕜) (x : Line) :
    schwartzAction φ x =
      -fderiv ℝ (fun y => fderiv ℝ φ y (fun _ => 1)) x (fun _ => 1) +
        ((x 0)^2 : 𝕜) * φ x := by
  have he : coordinateVector (0 : Fin 1) = (fun _ : Fin 1 => (1 : ℝ)) := by
    ext i
    fin_cases i
    simp [coordinateVector]
  change -(schwartzD (schwartzD φ) x) + schwartzX (schwartzX φ) x = _
  rw [schwartzD_apply, schwartzX_apply, schwartzX_apply]
  have hd : (schwartzD φ : Line → 𝕜) = fun y => fderiv ℝ φ y (fun _ => 1) := by
    funext y
    rw [schwartzD_apply, he]
  rw [hd, he]
  ring

private def schwartzLp : SchwartzMap Line 𝕜 →L[𝕜] L2 𝕜 :=
  SchwartzMap.toLpCLM 𝕜 𝕜 2 lineMeasure

private lemma schwartzLp_coe (φ : SchwartzMap Line 𝕜) :
    schwartzLp φ =ᵐ[lineMeasure] φ := SchwartzMap.coeFn_toLp φ 2 lineMeasure

private def schwartzGraphMap : SchwartzMap Line 𝕜 →ₗ[𝕜] (L2 𝕜 × L2 𝕜) :=
  schwartzLp.toLinearMap.prod (schwartzLp.comp schwartzAction).toLinearMap

private lemma schwartzGraph_range :
    ((schwartzGraphMap (𝕜 := 𝕜)).range : Set (L2 𝕜 × L2 𝕜)) = schwartzGraph 𝕜 := by
  ext z
  constructor
  · rintro ⟨φ, rfl⟩
    refine ⟨φ, schwartzLp_coe φ, ?_⟩
    exact (schwartzLp_coe (schwartzAction φ)).trans
      (Filter.Eventually.of_forall (schwartzAction_apply φ))
  · rintro ⟨φ, hu, hf⟩
    refine ⟨φ, Prod.ext (Lp.ext ((schwartzLp_coe φ).trans hu.symm)) ?_⟩
    apply Lp.ext
    exact ((schwartzLp_coe (schwartzAction φ)).trans
      (Filter.Eventually.of_forall (schwartzAction_apply φ))).trans hf.symm

lemma schwartz_graph_subset (A : L2 𝕜 →ₗ.[𝕜] L2 𝕜) (hA : IsRealization A) :
    schwartzGraph 𝕜 ⊆ (A.graph : Set (L2 𝕜 × L2 𝕜)) := by
  rintro ⟨f, g⟩ ⟨φ, hf, hg⟩
  let d := schwartzLp (schwartzD φ)
  let dd := schwartzLp (schwartzD (schwartzD φ))
  let xφ := schwartzLp (schwartzX φ)
  let xxφ := schwartzLp (schwartzX (schwartzX φ))
  have hd : d =ᵐ[lineMeasure] fun x => fderiv ℝ φ x (coordinateVector (0 : Fin 1)) :=
    (schwartzLp_coe (schwartzD φ)).trans (Filter.Eventually.of_forall (schwartzD_apply φ))
  have hdd : dd =ᵐ[lineMeasure] fun x =>
      fderiv ℝ (schwartzD φ) x (coordinateVector (0 : Fin 1)) :=
    (schwartzLp_coe (schwartzD (schwartzD φ))).trans
      (Filter.Eventually.of_forall (schwartzD_apply (schwartzD φ)))
  have hxφ : xφ =ᵐ[lineMeasure] fun x => (x 0 : 𝕜) * φ x :=
    (schwartzLp_coe (schwartzX φ)).trans (Filter.Eventually.of_forall (schwartzX_apply φ))
  have hxxφ : xxφ =ᵐ[lineMeasure] fun x => ((x 0)^2 : 𝕜) * φ x := by
    filter_upwards [schwartzLp_coe (schwartzX (schwartzX φ))] with x hx
    rw [hx, schwartzX_apply, schwartzX_apply]
    ring
  have hweight : MemLp (fun x => weight 𝕜 potential x * f x) 2 lineMeasure := by
    apply (Lp.memLp xφ).norm.mono'
      ((weight_continuous potential).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    filter_upwards [hxφ, hf] with x hx hy
    change ‖weight 𝕜 potential x * f x‖ ≤ ‖xφ x‖
    rw [hx, hy, position_weight_norm]
  let w := hweight.toLp _
  obtain ⟨u, hu, hdu, _⟩ := energy_of_weak_derivative f d w
    (weak_derivative_of_smooth φ (φ.smooth ⊤) f d hf hd) hweight.coeFn_toLp
  have hweak := weak_derivative_of_smooth (schwartzD φ) ((schwartzD φ).smooth ⊤)
    d dd (schwartzLp_coe (schwartzD φ)) hdd
  have haction : -dd + xxφ = g := by
    apply Lp.ext
    have hact := (schwartzLp_coe (schwartzAction φ)).trans
      (Filter.Eventually.of_forall (schwartzAction_apply φ))
    have heq : schwartzLp (schwartzAction φ) = -dd + xxφ := by
      change schwartzLp (-(schwartzD (schwartzD φ)) + schwartzX (schwartzX φ)) = _
      rw [map_add, map_neg]
    rw [heq] at hact
    exact hact.trans hg.symm
  apply (hA f g).mpr
  refine ⟨u, hu, ?_⟩
  intro ψ
  have hsecond : lpDistribution (value u) (testPartialCLM [0, 0] ψ) = lpDistribution dd ψ := by
    have h₁ := derivative_testing u (testPartialCLM [0] ψ)
    have h₂ := hweak ψ
    rw [hdu] at h₁
    change lpDistribution d (testPartialCLM [0] ψ) =
      -lpDistribution (value u) (testPartialCLM [0, 0] ψ) at h₁
    rw [h₁, neg_neg] at h₂
    exact h₂.symm
  have hpot : (∫ x, (potential.toContinuousMap (x 0) : 𝕜) * ψ x * value u x ∂lineMeasure) =
      lpDistribution xxφ ψ := by
    rw [lpDistribution_apply, hu]
    apply integral_congr_ae
    filter_upwards [hf, hxxφ] with x hx hy
    change (potential.toContinuousMap (x 0) : 𝕜) * ψ x * f x = ψ x * xxφ x
    rw [hx, hy, potential_apply, RCLike.ofReal_pow]
    ring
  change -lpDistribution (value u) (testPartialCLM [0, 0] ψ) + _ = _
  rw [hsecond, hpot]
  calc
    _ = lpDistribution (-dd + xxφ) ψ := by
      change (-lpDistributionLM dd + lpDistributionLM xxφ) ψ = lpDistributionLM (-dd + xxφ) ψ
      rw [map_add, map_neg]
    _ = _ := by rw [haction]

end SchwartzAction



section SchwartzCore
variable {𝕜 : Type} [RCLike 𝕜]

lemma hermite_graph_schwartz (A : L2 𝕜 →ₗ.[𝕜] L2 𝕜) (hA : IsRealization A)
    (b : HilbertBasis ℕ 𝕜 (L2 𝕜)) (hb : IsHermiteBasis b) (n : ℕ) :
    (b n, ((2 * (n : ℝ) + 1 : ℝ) : 𝕜) • b n) ∈ schwartzGraph 𝕜 := by
  obtain ⟨φ, hφ⟩ := hermite_schwartz 𝕜 n
  have hval : schwartzLp φ = b n :=
    Lp.ext (((schwartzLp_coe φ).trans (Filter.Eventually.of_forall hφ)).trans (hb n).symm)
  have hm : (schwartzLp φ, schwartzLp (schwartzAction φ)) ∈ schwartzGraph 𝕜 := by
    rw [← schwartzGraph_range]
    exact ⟨φ, rfl⟩
  have hg := schwartz_graph_subset A hA hm
  have he := eigenvectors 𝕜 A hA b hb n
  have hact : schwartzLp (schwartzAction φ) = ((2 * (n : ℝ) + 1 : ℝ) : 𝕜) • b n :=
    A.mem_graph_snd_inj hg he hval
  rwa [hval, hact] at hm

lemma schwartz_graph_closure (A : L2 𝕜 →ₗ.[𝕜] L2 𝕜) (hA : IsRealization A) :
    closure (schwartzGraph 𝕜) = (A.graph : Set (L2 𝕜 × L2 𝕜)) := by
  have hclosed : IsClosed (A.graph : Set (L2 𝕜 × L2 𝕜)) := by
    have hh := A.adjoint_isClosed (realization_dense hA)
    rwa [realization_self_adjoint hA] at hh
  apply le_antisymm (closure_minimal (schwartz_graph_subset A hA) hclosed)
  rintro ⟨u, f⟩ huf
  obtain ⟨b, hb⟩ := hermite_basis_exists 𝕜
  have hs : A.IsFormalAdjoint A := by
    have hh := A.adjoint_isFormalAdjoint (realization_dense hA)
    rwa [realization_self_adjoint hA] at hh
  let v : A.domain := ⟨u, LinearPMap.mem_domain_of_mem_graph huf⟩
  have hv : A v = f := A.mem_graph_snd_inj (A.mem_graph v) huf rfl
  have hcoeff (n : ℕ) : ⟪b n, f⟫_𝕜 =
      ((2 * (n : ℝ) + 1 : ℝ) : 𝕜) * ⟪b n, u⟫_𝕜 := by
    have he := eigenvectors 𝕜 A hA b hb n
    let e : A.domain := ⟨b n, LinearPMap.mem_domain_of_mem_graph he⟩
    have hae : A e = ((2 * (n : ℝ) + 1 : ℝ) : 𝕜) • b n :=
      A.mem_graph_snd_inj (A.mem_graph e) he rfl
    have hh := hs e v
    change ⟪A e, u⟫_𝕜 = ⟪b n, A v⟫_𝕜 at hh
    rw [hae, hv, inner_smul_left, RCLike.conj_ofReal] at hh
    exact hh.symm
  let S := (schwartzGraphMap (𝕜 := 𝕜)).range
  have hbase (n : ℕ) : (b n, ((2 * (n : ℝ) + 1 : ℝ) : 𝕜) • b n) ∈ S := by
    change (b n, ((2 * (n : ℝ) + 1 : ℝ) : 𝕜) • b n) ∈
      ((schwartzGraphMap (𝕜 := 𝕜)).range : Set (L2 𝕜 × L2 𝕜))
    rw [schwartzGraph_range]
    exact hermite_graph_schwartz A hA b hb n
  have hsum : HasSum (fun n : ℕ => ⟪b n, u⟫_𝕜 •
      (b n, ((2 * (n : ℝ) + 1 : ℝ) : 𝕜) • b n)) (u, f) := by
    have hh := (b.hasSum_repr u).prodMk (b.hasSum_repr f)
    simp only [b.repr_apply_apply] at hh
    convert hh using 1
    funext n
    change (⟪b n, u⟫_𝕜 • b n, ⟪b n, u⟫_𝕜 •
      (((2 * (n : ℝ) + 1 : ℝ) : 𝕜) • b n)) = _
    apply Prod.ext
    · rfl
    · rw [smul_smul, hcoeff, mul_comm]
  rw [← schwartzGraph_range]
  change (u, f) ∈ S.topologicalClosure
  apply S.isClosed_topologicalClosure.mem_of_tendsto hsum
  exact Filter.Eventually.of_forall fun s =>
    Submodule.le_topologicalClosure S (S.sum_mem fun n _ => S.smul_mem _ (hbase n))

end SchwartzCore

theorem essential_self_adjointness : Spec.EssentialSelfAdjointness := by
  intro 𝕜 _ A hA
  exact ⟨schwartz_graph_subset A hA, schwartz_graph_closure A hA, realization_self_adjoint hA⟩



/-- Every existing resolvent of this same differential realization is compact. -/
theorem all_resolvents_compact : Spec.AllResolventsCompact := by
  intro 𝕜 _ A hA ζ R
  obtain ⟨T, hsol, _, _, _, _, B, hg, _, _, _, hB, _⟩ :=
    confining_realization 𝕜 potential positive_at_infinity
  have hBA : B = A := realization_unique hB hA
  subst B
  exact compact_resolvents_of_inverse T
    (compact_solution_operator 𝕜 potential confining T hsol) A hg ζ R

end ExpandedFA.Models.HarmonicOscillator
