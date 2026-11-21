import Specs.ExpandedFA.PartV.VolterraOperator
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerIntegral
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic.Ring

/-!
The continuous-kernel Volterra operator from paper.tex 21872–21907.

The retraction `(t,s) ↦ (t, max a (min t s))` extends the kernel continuously
in the integration variable and agrees with it on `a ≤ s ≤ t`. Continuous
parameter integration gives a continuous output. The norm integral estimate
bounds it by `‖k‖ (t-a) ‖u‖`; this both constructs a bounded linear map and
proves the requested bound for any uniform kernel bound `M`.

All integrals are native Bochner integrals, definitionally the accepted
`ExpandedFA.FunctionSpaces.bochnerIntegral`. Ordered application of operator
values is retained; no commutation of kernel operators is used.
-/

noncomputable section
namespace ExpandedFA.PartV
open Set MeasureTheory

/-- The norm integral defining the Volterra operator. -/
def volterra_integral : VolterraOperatorSpec.IntegralType :=
  VolterraOperatorSpec.IntegralValue

/-- The canonical bounded linear Volterra operator selected by its integral
formula. The construction theorem proves that the selected map exists and has
that formula, as well as the bounds. -/
def volterra_operator : VolterraOperatorSpec.OperatorType :=
  VolterraOperatorSpec.OperatorValue

theorem volterra_kernel_maximum : VolterraOperatorSpec.KernelMaximum := by
  intro 𝕜 E _ _ _ a b hab k
  let : Nonempty (volterraTriangle a b) := ⟨⟨(a, a), le_rfl, le_rfl, hab⟩⟩
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ : Set (volterraTriangle a b)).Nonempty)
    k.continuous.norm.continuousOn
  refine ⟨norm_nonneg k, k.norm_coe_le_norm, p, le_antisymm (k.norm_coe_le_norm p) ?_⟩
  exact (ContinuousMap.norm_le _ (norm_nonneg _)).mpr (fun q => hp (Set.mem_univ q))

section
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
local instance : SMulCommClass ℝ 𝕜 E where
  smul_comm r c x := by
    change (algebraMap ℝ 𝕜 r) • (c • x) = c • ((algebraMap ℝ 𝕜 r) • x)
    simp only [smul_smul, mul_comm]
variable {a b : ℝ} (hab : a ≤ b)
  (k : C(volterraTriangle a b, E →L[𝕜] E)) (u : C(VolterraInterval a b, E))

theorem continuous_volterraRetraction :
    Continuous (fun p : VolterraInterval a b × ℝ => volterraRetraction p.1 p.2) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_const.max ((continuous_subtype_val.comp continuous_fst).min continuous_snd))

theorem continuous_volterraIntegrand :
    Continuous (fun p : VolterraInterval a b × ℝ => volterraIntegrand hab k u p.1 p.2) := by
  exact (k.continuous.comp continuous_volterraRetraction).clm_apply
    (u.continuous.comp (continuous_projIcc.comp continuous_snd))

theorem volterraIntegrand_eq (t : VolterraInterval a b) (s : ℝ)
    (hs : s ∈ Icc a (t : ℝ)) :
    volterraIntegrand hab k u t s =
      k ⟨((t : ℝ), s), hs.1, hs.2, t.property.2⟩
        (u ⟨s, hs.1, hs.2.trans t.property.2⟩) := by
  unfold volterraIntegrand
  have hr : volterraRetraction t s = ⟨((t : ℝ), s), hs.1, hs.2, t.property.2⟩ := by
    apply Subtype.ext
    simp [volterraRetraction, min_eq_right hs.2, max_eq_right hs.1]
  rw [hr, Set.projIcc_of_mem hab ⟨hs.1, hs.2.trans t.property.2⟩]

theorem continuous_volterraIntegral : Continuous (volterraIntegralValue hab k u) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (continuous_volterraIntegrand hab k u) continuous_subtype_val

theorem volterra_pointwise_estimate (t : VolterraInterval a b) :
    ‖volterraIntegralValue hab k u t‖ ≤ ‖k‖ * ((t : ℝ) - a) * ‖u‖ := by
  have hb : ∀ s ∈ Set.uIoc a (t : ℝ), ‖volterraIntegrand hab k u t s‖ ≤ ‖k‖ * ‖u‖ := by
    intro s _
    exact (k (volterraRetraction t s)).le_opNorm _ |>.trans
      (mul_le_mul (k.norm_coe_le_norm _) (u.norm_coe_le_norm _)
        (norm_nonneg _) (norm_nonneg k))
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [abs_of_nonneg (sub_nonneg.mpr t.property.1)] at h
  exact h.trans_eq (by ring)

variable [CompleteSpace E]

/-- The linear map is constructed from the actual integrals. -/
def volterraLinearMap : C(VolterraInterval a b, E) →ₗ[𝕜] C(VolterraInterval a b, E) where
  toFun u := ⟨volterraIntegralValue hab k u, continuous_volterraIntegral hab k u⟩
  map_add' u v := by
    ext t
    change volterraIntegralValue hab k (u + v) t =
      volterraIntegralValue hab k u t + volterraIntegralValue hab k v t
    unfold volterraIntegralValue
    simp only [volterraIntegrand, ContinuousMap.add_apply, map_add]
    apply intervalIntegral.integral_add
    · exact ((continuous_volterraIntegrand hab k u).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    · exact ((continuous_volterraIntegrand hab k v).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  map_smul' c u := by
    ext t
    change volterraIntegralValue hab k (c • u) t = c • volterraIntegralValue hab k u t
    simp only [volterraIntegralValue, volterraIntegrand, ContinuousMap.smul_apply, map_smul,
      intervalIntegral.integral_smul]

omit [CompleteSpace E] in
theorem volterra_uniform_estimate :
    ‖volterraLinearMap hab k u‖ ≤ (‖k‖ * (b - a)) * ‖u‖ := by
  apply (ContinuousMap.norm_le (volterraLinearMap hab k u) (mul_nonneg (mul_nonneg (norm_nonneg k)
    (sub_nonneg.mpr hab)) (norm_nonneg u))).mpr
  intro t
  exact (volterra_pointwise_estimate hab k u t).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (sub_le_sub_right t.property.2 a) (norm_nonneg k)) (norm_nonneg u))

/-- A reusable bounded linear Volterra operator; the proof of boundedness is
supplied by the integral estimate, with no dimension premise. -/
def volterraOperator : C(VolterraInterval a b, E) →L[𝕜] C(VolterraInterval a b, E) :=
  (volterraLinearMap hab k).mkContinuous (‖k‖ * (b - a)) (fun u => volterra_uniform_estimate hab k u)

end

theorem volterra_integrals_exist : VolterraOperatorSpec.IntegralsExist := by
  intro 𝕜 E _ _ _ _ a b hab k u
  let := NormedSpace.restrictScalars ℝ 𝕜 E
  constructor
  · intro t
    have hc := (continuous_volterraIntegrand hab k u).comp
      (continuous_const.prodMk continuous_id : Continuous (fun s : ℝ => (t, s)))
    exact ⟨hc, hc.intervalIntegrable _ _⟩
  · exact volterraIntegrand_eq hab k u

theorem volterra_integral_continuous : VolterraOperatorSpec.IntegralContinuous := by
  intro 𝕜 E _ _ _ _ a b hab k u
  exact continuous_volterraIntegral hab k u

theorem volterra_operator_properties : VolterraOperatorSpec.OperatorProperties := by
  intro 𝕜 E _ _ _ _ a b hab k
  have h_exists : ∃ V : C(VolterraInterval a b, E) →L[𝕜] C(VolterraInterval a b, E),
      ∀ u t, V u t = volterraIntegralValue hab k u t :=
    ⟨volterraOperator hab k, fun _ _ => rfl⟩
  have h_formula : ∀ u t, VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k u t =
      volterraIntegralValue hab k u t := Classical.epsilon_spec h_exists
  have h_eq : VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k = volterraOperator hab k := by
    ext u t
    exact h_formula u t
  refine ⟨h_formula, ?_, ?_⟩
  · intro u t
    rw [h_formula]
    exact volterra_pointwise_estimate hab k u t
  · rw [h_eq]
    exact LinearMap.mkContinuous_norm_le (volterraLinearMap hab k)
      (mul_nonneg (norm_nonneg k) (sub_nonneg.mpr hab))
      (fun u => volterra_uniform_estimate hab k u)

theorem volterra_operator_construction : VolterraOperatorSpec.OperatorConstruction := by
  intro 𝕜 E _ _ _ _ a b hab k
  exact ⟨volterra_operator 𝕜 E a b hab k,
    volterra_operator_properties 𝕜 E a b hab k⟩

theorem volterra_operator_bound : VolterraOperatorSpec.OperatorBound := by
  intro 𝕜 E _ _ _ _ a b hab k M hM
  have hnonneg : 0 ≤ M := (norm_nonneg (k ⟨(a, a), le_rfl, le_rfl, hab⟩)).trans
    (hM ⟨(a, a), le_rfl, le_rfl, hab⟩)
  have hk : ‖k‖ ≤ M := (ContinuousMap.norm_le k hnonneg).mpr hM
  exact (volterra_operator_properties 𝕜 E a b hab k).2.2.trans
    (mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hab))

theorem volterra_singleton_zero : VolterraOperatorSpec.SingletonZero := by
  intro 𝕜 E _ _ _ _ a k
  ext u t
  have ht : (t : ℝ) = a := le_antisymm t.property.2 t.property.1
  rw [(volterra_operator_properties 𝕜 E a a (le_refl a) k).1]
  simp [volterraIntegralValue, ht]

theorem volterra_singleton_evaluation : VolterraOperatorSpec.SingletonEvaluation := by
  intro 𝕜 E _ _ _ a
  let t₀ : VolterraInterval a a := ⟨a, le_rfl, le_rfl⟩
  have ht : ∀ t : VolterraInterval a a, t = t₀ := by
    intro t
    exact Subtype.ext (le_antisymm t.property.2 t.property.1)
  let e : C(VolterraInterval a a, E) ≃ₗ[𝕜] E :=
    { toFun := fun u => u t₀
      invFun := fun x => ContinuousMap.const _ x
      left_inv := by intro u; ext t; simp only [ContinuousMap.const_apply]; rw [ht t]
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨{ e with norm_map' := ?_ }, fun _ => rfl, fun _ _ => rfl⟩
  intro u
  apply le_antisymm (u.norm_coe_le_norm t₀)
  exact (ContinuousMap.norm_le u (norm_nonneg _)).mpr (fun t => by rw [ht t])

theorem volterra_banach_function_space : VolterraOperatorSpec.BanachFunctionSpace := by
  intro 𝕜 E _ _ _ _ a b
  exact ⟨inferInstance, fun u => u.norm_eq_iSup_norm,
    ContinuousMap.isUniformInducing_equivBoundedOfCompact _ _⟩

end ExpandedFA.PartV
