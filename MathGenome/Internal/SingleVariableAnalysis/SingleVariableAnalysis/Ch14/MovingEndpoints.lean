import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.MovingEndpoints
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch14.ProperDerivative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.FtcFirst
import Mathlib.Topology.Order.ProjIcc

/-! Leibniz's rule for the proper oriented Darboux integral. -/
namespace SingleVariableAnalysis.ParameterIntegral
open Set Filter Riemann
open scoped Topology

/-- Evaluation at a moving point splits the slope into its uniform-section
part and its fixed-section part. No differentiable structure on X is needed. -/
theorem hasDerivAt_moving_evaluation {X E : Type*} [TopologicalSpace X]
    [CompactSpace X] [LocallyCompactSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → C(X, E)} {u' : C(X, E)} {h : ℝ → X} {t : ℝ} {v : E}
    (hu : HasDerivAt u u' t) (hh : ContinuousAt h t)
    (hv : HasDerivAt (fun s => u t (h s)) v t) :
    HasDerivAt (fun s => u s (h s)) (u' (h t) + v) t := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have he := hu.tendsto_slope.eval (hh.tendsto.mono_left nhdsWithin_le_nhds)
  have hs := he.add hv.tendsto_slope
  convert hs using 1
  funext s
  simp only [slope_def_module, ContinuousMap.smul_apply, ContinuousMap.sub_apply,
    smul_sub]
  abel

/-- Convert the source's restricted real-increment definition to the library
within-derivative, retaining the actual restricted domain. -/
theorem incrementWithin_hasDerivWithinAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : ℝ → E} {v : E} {I : Set ℝ} {x : ℝ}
    (h : HasRealIncrementDerivativeWithin F v I x) : HasDerivWithinAt F v I x := by
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := (withinDerivative_epsilon_iff F v I x).mp h ε hε
  refine ⟨δ, hδ, fun y hy hxy => ?_⟩
  have hyx : y ≠ x := hy.2
  have he := hb (y-x) (by simpa using hy.1)
    (abs_pos.mpr (sub_ne_zero.mpr hyx)) (by simpa [Real.dist_eq] using hxy)
  simpa only [RealIncrementQuotient, add_sub_cancel, slope_def_module, dist_eq_norm] using he

/-- The Darboux primitive, as a continuous function on the spatial interval. -/
noncomputable def realPrimitive {L U : ℝ} (hLU : L ≤ U)
    (v : C(Icc L U, ℝ)) : C(Icc L U, ℝ) where
  toFun y := realIntegral (realExtension v)
    ((realExtension_integrable hLU v).subinterval le_rfl y.property.1 y.property.2)
  continuous_toFun := by
    obtain ⟨H, _, _, _, hc⟩ := real_accumulation (realExtension v)
      (realExtension_integrable hLU v)
    exact hc

lemma realExtension_add {L U : ℝ} (v w : C(Icc L U, ℝ)) :
    realExtension (v+w) = fun x => realExtension v x + realExtension w x := by
  classical
  funext x
  by_cases hx : x ∈ Icc L U <;>
    simp [realExtension, parameterSection, S.sectionValue, D.sectionValue, hx]

lemma realExtension_smul {L U : ℝ} (r : ℝ) (v : C(Icc L U, ℝ)) :
    realExtension (r • v) = fun x => r • realExtension v x := by
  classical
  funext x
  by_cases hx : x ∈ Icc L U <;>
    simp [realExtension, parameterSection, S.sectionValue, D.sectionValue, hx]

/-- Uniformly bounded linearity is for the actual Darboux values. -/
noncomputable def realPrimitiveCLM {L U : ℝ} (hLU : L ≤ U) :
    C(Icc L U, ℝ) →L[ℝ] C(Icc L U, ℝ) :=
  LinearMap.mkContinuous
    { toFun := realPrimitive hLU
      map_add' := by
        intro v w
        ext y
        dsimp only [realPrimitive, ContinuousMap.add_apply]
        obtain ⟨h, hv⟩ := real_add_value
          ((realExtension_integrable hLU v).subinterval le_rfl y.property.1 y.property.2)
          ((realExtension_integrable hLU w).subinterval le_rfl y.property.1 y.property.2)
        simpa only [realExtension_add, ContinuousMap.coe_mk] using hv
      map_smul' := by
        intro r v
        ext y
        dsimp only [realPrimitive, ContinuousMap.smul_apply, RingHom.id_apply]
        obtain ⟨h, hv⟩ := real_mul_value
          ((realExtension_integrable hLU v).subinterval le_rfl y.property.1 y.property.2) r
        simpa only [realExtension_smul, ContinuousMap.coe_mk, smul_eq_mul] using hv }
    (U-L) (by
      intro v
      apply (ContinuousMap.norm_le _ (mul_nonneg (sub_nonneg.mpr hLU) (norm_nonneg _))).mpr
      intro y
      change ‖realPrimitive hLU v y‖ ≤ (U-L) * ‖v‖
      dsimp only [realPrimitive]
      obtain ⟨hn, hb, _⟩ := real_norm_estimate (realExtension v)
        ((realExtension_integrable hLU v).subinterval le_rfl y.property.1 y.property.2)
      apply hb.trans
      apply (realIntegral_le_mul_bound hn ?_).trans
        (mul_le_mul_of_nonneg_right (sub_le_sub_right y.property.2 L) (norm_nonneg v))
      intro x hx
      have hx' : x ∈ Icc L U := ⟨hx.1, hx.2.trans y.property.2⟩
      have he := section_on_interval .real
        (fun x (_ : (univ : Set ℝ)) => v x) ⟨0, mem_univ _⟩ ⟨x, hx'⟩
      change ‖realExtension v x‖ ≤ ‖v‖
      rw [show realExtension v x = v ⟨x, hx'⟩ from he]
      exact v.norm_coe_le_norm _)

/-- FTC on the closed spatial interval, including its boundary and singleton case. -/
lemma realPrimitive_within {L U : ℝ} (hLU : L ≤ U)
    (v : C(Icc L U, ℝ)) (y : Icc L U) :
    HasDerivWithinAt
      (fun z => realPrimitive hLU v (projIcc L U hLU z))
      (v y) (Icc L U) y := by
  let F := fun z => realPrimitive hLU v (projIcc L U hLU z)
  have hv : ContinuousOn (realExtension v) (Icc L U) := by
    apply continuousOn_of_section_agreement v.continuous
    exact fun x => section_on_interval .real
      (fun x (_ : (univ : Set ℝ)) => v x) ⟨0, mem_univ _⟩ x
  have hF : Specs.SingleVariableAnalysis.Ch09.FtcFirst.realAccumulationOn
      (realExtension v) F L U := by
    intro z hz
    refine ⟨(realExtension_integrable hLU v).subinterval le_rfl hz.1 hz.2, ?_⟩
    simp only [F, projIcc_of_mem hLU hz]
    rfl
  have hd := incrementWithin_hasDerivWithinAt
    (real_ftc_first_within (realExtension v) F (realExtension_integrable hLU v)
      hF y y.property (hv y y.property))
  have he : realExtension v y = v y :=
    section_on_interval .real (fun x (_ : (univ : Set ℝ)) => v x) ⟨0, mem_univ _⟩ y
  rwa [he] at hd

/-- Oriented additivity identifies any integral between two endpoints with
one difference of primitives; it imposes no order between x and y. -/
lemma realPrimitive_sub {L U : ℝ} (hLU : L ≤ U)
    (v : C(Icc L U, ℝ)) (x y : Icc L U)
    (hxy : OrientedRealIntegrable (realExtension v) x y) :
    realPrimitive hLU v y - realPrimitive hLU v x =
      orientedRealIntegral (realExtension v) hxy := by
  have hi : RealIntegrable (realExtension v)
      (min L (min x y)) (max L (max x y)) :=
    (realExtension_integrable hLU v).subinterval
    (le_min le_rfl (le_min x.property.1 y.property.1))
    ((min_le_left L (min x y)).trans (le_max_left L (max x y)))
    (max_le hLU (max_le x.property.2 y.property.2))
  obtain ⟨h1, h2, h3, he⟩ := oriented_real_additivity (realExtension v) L x y hi
  rw [oriented_real_agreement _ x.property.1 h1
    ((realExtension_integrable hLU v).subinterval le_rfl x.property.1 x.property.2),
    oriented_real_agreement _ y.property.1 h3
    ((realExtension_integrable hLU v).subinterval le_rfl y.property.1 y.property.2)] at he
  dsimp only [realPrimitive]
  exact sub_eq_of_eq_add (he.symm.trans (add_comm _ _))

/-- The Darboux primitive, as a continuous function on the spatial interval. -/
noncomputable def complexPrimitive {L U : ℝ} (hLU : L ≤ U)
    (v : C(Icc L U, ℂ)) : C(Icc L U, ℂ) where
  toFun y := complexIntegral (complexExtension v)
    ((complexExtension_integrable hLU v).subinterval le_rfl y.property.1 y.property.2)
  continuous_toFun := by
    obtain ⟨H, _, _, _, hc⟩ := complex_accumulation (complexExtension v)
      (complexExtension_integrable hLU v)
    exact hc

lemma complexExtension_add {L U : ℝ} (v w : C(Icc L U, ℂ)) :
    complexExtension (v+w) = fun x => complexExtension v x + complexExtension w x := by
  classical
  funext x
  by_cases hx : x ∈ Icc L U <;>
    simp [complexExtension, parameterSection, S.sectionValue, D.sectionValue, hx]

lemma complexExtension_smul {L U : ℝ} (r : ℝ) (v : C(Icc L U, ℂ)) :
    complexExtension (r • v) = fun x => r • complexExtension v x := by
  classical
  funext x
  by_cases hx : x ∈ Icc L U <;>
    simp [complexExtension, parameterSection, S.sectionValue, D.sectionValue, hx]

/-- Uniformly bounded linearity is for the actual Darboux values. -/
noncomputable def complexPrimitiveCLM {L U : ℝ} (hLU : L ≤ U) :
    C(Icc L U, ℂ) →L[ℝ] C(Icc L U, ℂ) :=
  LinearMap.mkContinuous
    { toFun := complexPrimitive hLU
      map_add' := by
        intro v w
        ext y
        dsimp only [complexPrimitive, ContinuousMap.add_apply]
        obtain ⟨h, hv⟩ := complex_add_value
          ((complexExtension_integrable hLU v).subinterval le_rfl y.property.1 y.property.2)
          ((complexExtension_integrable hLU w).subinterval le_rfl y.property.1 y.property.2)
        simpa only [complexExtension_add, ContinuousMap.coe_mk] using hv
      map_smul' := by
        intro r v
        ext y
        dsimp only [complexPrimitive, ContinuousMap.smul_apply, RingHom.id_apply]
        obtain ⟨h, hv⟩ := complex_mul_value
          ((complexExtension_integrable hLU v).subinterval le_rfl y.property.1 y.property.2) (r : ℂ)
        simpa only [complexExtension_smul, ContinuousMap.coe_mk, Complex.real_smul] using hv }
    (U-L) (by
      intro v
      apply (ContinuousMap.norm_le _ (mul_nonneg (sub_nonneg.mpr hLU) (norm_nonneg _))).mpr
      intro y
      change ‖complexPrimitive hLU v y‖ ≤ (U-L) * ‖v‖
      dsimp only [complexPrimitive]
      obtain ⟨hn, hb, _⟩ := complex_norm_estimate (complexExtension v)
        ((complexExtension_integrable hLU v).subinterval le_rfl y.property.1 y.property.2)
      apply hb.trans
      apply (realIntegral_le_mul_bound hn ?_).trans
        (mul_le_mul_of_nonneg_right (sub_le_sub_right y.property.2 L) (norm_nonneg v))
      intro x hx
      have hx' : x ∈ Icc L U := ⟨hx.1, hx.2.trans y.property.2⟩
      have he := section_on_interval .complex
        (fun x (_ : (univ : Set ℝ)) => v x) ⟨0, mem_univ _⟩ ⟨x, hx'⟩
      change ‖complexExtension v x‖ ≤ ‖v‖
      rw [show complexExtension v x = v ⟨x, hx'⟩ from he]
      exact v.norm_coe_le_norm _)

/-- FTC on the closed spatial interval, including its boundary and singleton case. -/
lemma complexPrimitive_within {L U : ℝ} (hLU : L ≤ U)
    (v : C(Icc L U, ℂ)) (y : Icc L U) :
    HasDerivWithinAt
      (fun z => complexPrimitive hLU v (projIcc L U hLU z))
      (v y) (Icc L U) y := by
  let F := fun z => complexPrimitive hLU v (projIcc L U hLU z)
  have hv : ContinuousOn (complexExtension v) (Icc L U) := by
    apply continuousOn_of_section_agreement v.continuous
    exact fun x => section_on_interval .complex
      (fun x (_ : (univ : Set ℝ)) => v x) ⟨0, mem_univ _⟩ x
  have hF : Specs.SingleVariableAnalysis.Ch09.FtcFirst.complexAccumulationOn
      (complexExtension v) F L U := by
    intro z hz
    refine ⟨(complexExtension_integrable hLU v).subinterval le_rfl hz.1 hz.2, ?_⟩
    simp only [F, projIcc_of_mem hLU hz]
    rfl
  have hd := incrementWithin_hasDerivWithinAt
    (complex_ftc_first_within (complexExtension v) F (complexExtension_integrable hLU v)
      hF y y.property (hv y y.property))
  have he : complexExtension v y = v y :=
    section_on_interval .complex (fun x (_ : (univ : Set ℝ)) => v x) ⟨0, mem_univ _⟩ y
  rwa [he] at hd

/-- Oriented additivity identifies any integral between two endpoints with
one difference of primitives; it imposes no order between x and y. -/
lemma complexPrimitive_sub {L U : ℝ} (hLU : L ≤ U)
    (v : C(Icc L U, ℂ)) (x y : Icc L U)
    (hxy : OrientedComplexIntegrable (complexExtension v) x y) :
    complexPrimitive hLU v y - complexPrimitive hLU v x =
      orientedComplexIntegral (complexExtension v) hxy := by
  have hi : ComplexIntegrable (complexExtension v)
      (min L (min x y)) (max L (max x y)) :=
    (complexExtension_integrable hLU v).subinterval
    (le_min le_rfl (le_min x.property.1 y.property.1))
    ((min_le_left L (min x y)).trans (le_max_left L (max x y)))
    (max_le hLU (max_le x.property.2 y.property.2))
  obtain ⟨h1, h2, h3, he⟩ := oriented_complex_additivity (complexExtension v) L x y hi
  rw [oriented_complex_agreement _ x.property.1 h1
    ((complexExtension_integrable hLU v).subinterval le_rfl x.property.1 x.property.2),
    oriented_complex_agreement _ y.property.1 h3
    ((complexExtension_integrable hLU v).subinterval le_rfl y.property.1 y.property.2)] at he
  dsimp only [complexPrimitive]
  exact sub_eq_of_eq_add (he.symm.trans (add_comm _ _))

/-- Differentiate a primitive at one moving endpoint. The closed-interval
FTC and a chain rule within J allow the endpoint to touch L or U. -/
theorem primitive_endpoint_hasDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {L U : ℝ} (hLU : L ≤ U)
    (P : C(Icc L U, E) →L[ℝ] C(Icc L U, E))
    (hP : ∀ v (y : Icc L U), HasDerivWithinAt
      (fun z => P v (projIcc L U hLU z)) (v y) (Icc L U) y)
    {J : Set ℝ} (hJ : IsOpen J) {α : ℝ → ℝ}
    (hα : ∀ s ∈ J, α s ∈ Icc L U)
    {u : ℝ → C(Icc L U, E)} {u' : C(Icc L U, E)} {t a' : ℝ}
    (ht : t ∈ J) (hu : HasDerivAt u u' t) (ha : HasDerivAt α a' t) :
    HasDerivAt (fun s => P (u s) (projIcc L U hLU (α s)))
      (P u' ⟨α t, hα t ht⟩ + a' • u t ⟨α t, hα t ht⟩) t := by
  have hfix : HasDerivAt
      (fun s => P (u t) (projIcc L U hLU (α s)))
      (a' • u t ⟨α t, hα t ht⟩) t := by
    exact ((hP (u t) ⟨α t, hα t ht⟩).scomp t ha.hasDerivWithinAt hα).hasDerivAt
      (hJ.mem_nhds ht)
  have hp := hasDerivAt_moving_evaluation
    (P.hasFDerivAt.comp_hasDerivAt t hu)
    (continuous_projIcc.continuousAt.comp ha.continuousAt) hfix
  simpa only [Function.comp_def, projIcc_of_mem hLU (hα t ht)] using hp

namespace M
export Specs.SingleVariableAnalysis.Ch14.MovingEndpoints (realSection complexSection)
end M

lemma realSection_eq_extension {L U : ℝ} {J : Set ℝ}
    {f : ℝ → Icc L U → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (J ×ˢ univ))
    {t : ℝ} (ht : t ∈ J) :
    M.realSection f t = realExtension (sectionsOn J f hf t) := by
  classical
  funext x
  change (if hx : x ∈ Icc L U then f t ⟨x, hx⟩ else (0 : ℝ)) =
    (if hx : x ∈ Icc L U then sectionsOn J f hf t ⟨x, hx⟩ else (0 : ℝ))
  split_ifs with hx
  · exact (sectionsOn_apply hf ht ⟨x, hx⟩).symm
  · rfl

lemma orientedRealIntegral_eq_of_eq {a b : ℝ} {f g : ℝ → ℝ}
    (hf : OrientedRealIntegrable f a b) (hg : OrientedRealIntegrable g a b)
    (he : f = g) : orientedRealIntegral f hf = orientedRealIntegral g hg := by
  subst g
  rfl

/-- K03.14.moving_endpoints, with real values and real increments.
The same primitive difference proves the formula at crossings and at contacts
with the boundary of the spatial rectangle. -/
theorem real_moving_endpoints :
    Specs.SingleVariableAnalysis.Ch14.MovingEndpoints.realMovingEndpoints := by
  intro L U hLU J hJ α β hcα hcβ hα hβ f g hf hg hd
  let sf := sectionsOn J f hf
  let sg := sectionsOn J g hg
  let P := realPrimitiveCLM hLU
  have hi (t : ℝ) (ht : t ∈ J) :
      OrientedRealIntegrable (M.realSection f t) (α t) (β t) := by
    rw [realSection_eq_extension hf ht]
    exact oriented_real_integrable_of_mem (realExtension_integrable hLU (sf t))
      (hα t ht) (hβ t ht)
  have hgi (t : ℝ) (ht : t ∈ J) :
      OrientedRealIntegrable (M.realSection g t) (α t) (β t) := by
    rw [realSection_eq_extension hg ht]
    exact oriented_real_integrable_of_mem (realExtension_integrable hLU (sg t))
      (hα t ht) (hβ t ht)
  refine ⟨hi, hgi, ?_⟩
  intro F G hF hG t ht
  have hrepr (s : ℝ) (hs : s ∈ J) :
      P (sf s) (projIcc L U hLU (β s)) -
        P (sf s) (projIcc L U hLU (α s)) = F s := by
    rw [projIcc_of_mem hLU (hβ s hs), projIcc_of_mem hLU (hα s hs), hF s hs]
    exact (realPrimitive_sub hLU (sf s) ⟨α s, hα s hs⟩ ⟨β s, hβ s hs⟩
      (oriented_real_integrable_of_mem (realExtension_integrable hLU (sf s))
        (hα s hs) (hβ s hs))).trans
      (orientedRealIntegral_eq_of_eq _ _ (realSection_eq_extension hf hs).symm)
  have hgrepr : P (sg t) ⟨β t, hβ t ht⟩ - P (sg t) ⟨α t, hα t ht⟩ = G t := by
    rw [hG t ht]
    exact (realPrimitive_sub hLU (sg t) ⟨α t, hα t ht⟩ ⟨β t, hβ t ht⟩
      (oriented_real_integrable_of_mem (realExtension_integrable hLU (sg t))
        (hα t ht) (hβ t ht))).trans
      (orientedRealIntegral_eq_of_eq _ _ (realSection_eq_extension hg ht).symm)
  have hda : HasDerivAt α (deriv α t) t :=
    ((hcα.differentiableOn_one t ht).differentiableAt (hJ.mem_nhds ht)).hasDerivAt
  have hdb : HasDerivAt β (deriv β t) t :=
    ((hcβ.differentiableOn_one t ht).differentiableAt (hJ.mem_nhds ht)).hasDerivAt
  have hdu : HasDerivAt sf (sg t) t := sectionsOn_hasDerivAt hJ hf hg hd ht
  have ha := primitive_endpoint_hasDerivAt hLU P (realPrimitive_within hLU)
    hJ hα ht hdu hda
  have hb := primitive_endpoint_hasDerivAt hLU P (realPrimitive_within hLU)
    hJ hβ ht hdu hdb
  have hresult := (hb.sub ha).congr_of_eventuallyEq
    (Filter.Eventually.mono (hJ.mem_nhds ht) (fun s hs => (hrepr s hs).symm))
  convert hresult using 1
  rw [show sg t = sectionsOn J g hg t from rfl] at hgrepr
  rw [show sf t ⟨β t, hβ t ht⟩ = f t ⟨β t, hβ t ht⟩ from sectionsOn_apply hf ht _,
    show sf t ⟨α t, hα t ht⟩ = f t ⟨α t, hα t ht⟩ from sectionsOn_apply hf ht _]
  rw [← hgrepr]
  abel

lemma complexSection_eq_extension {L U : ℝ} {J : Set ℝ}
    {f : ℝ → Icc L U → ℂ}
    (hf : ContinuousOn (Function.uncurry f) (J ×ˢ univ))
    {t : ℝ} (ht : t ∈ J) :
    M.complexSection f t = complexExtension (sectionsOn J f hf t) := by
  classical
  funext x
  change (if hx : x ∈ Icc L U then f t ⟨x, hx⟩ else (0 : ℂ)) =
    (if hx : x ∈ Icc L U then sectionsOn J f hf t ⟨x, hx⟩ else (0 : ℂ))
  split_ifs with hx
  · exact (sectionsOn_apply hf ht ⟨x, hx⟩).symm
  · rfl

lemma orientedComplexIntegral_eq_of_eq {a b : ℝ} {f g : ℝ → ℂ}
    (hf : OrientedComplexIntegrable f a b) (hg : OrientedComplexIntegrable g a b)
    (he : f = g) : orientedComplexIntegral f hf = orientedComplexIntegral g hg := by
  subst g
  rfl

/-- K03.14.moving_endpoints, with complex values and real increments.
The same primitive difference proves the formula at crossings and at contacts
with the boundary of the spatial rectangle. -/
theorem complex_moving_endpoints :
    Specs.SingleVariableAnalysis.Ch14.MovingEndpoints.complexMovingEndpoints := by
  intro L U hLU J hJ α β hcα hcβ hα hβ f g hf hg hd
  let sf := sectionsOn J f hf
  let sg := sectionsOn J g hg
  let P := complexPrimitiveCLM hLU
  have hi (t : ℝ) (ht : t ∈ J) :
      OrientedComplexIntegrable (M.complexSection f t) (α t) (β t) := by
    rw [complexSection_eq_extension hf ht]
    exact oriented_complex_integrable_of_mem (complexExtension_integrable hLU (sf t))
      (hα t ht) (hβ t ht)
  have hgi (t : ℝ) (ht : t ∈ J) :
      OrientedComplexIntegrable (M.complexSection g t) (α t) (β t) := by
    rw [complexSection_eq_extension hg ht]
    exact oriented_complex_integrable_of_mem (complexExtension_integrable hLU (sg t))
      (hα t ht) (hβ t ht)
  refine ⟨hi, hgi, ?_⟩
  intro F G hF hG t ht
  have hrepr (s : ℝ) (hs : s ∈ J) :
      P (sf s) (projIcc L U hLU (β s)) -
        P (sf s) (projIcc L U hLU (α s)) = F s := by
    rw [projIcc_of_mem hLU (hβ s hs), projIcc_of_mem hLU (hα s hs), hF s hs]
    exact (complexPrimitive_sub hLU (sf s) ⟨α s, hα s hs⟩ ⟨β s, hβ s hs⟩
      (oriented_complex_integrable_of_mem (complexExtension_integrable hLU (sf s))
        (hα s hs) (hβ s hs))).trans
      (orientedComplexIntegral_eq_of_eq _ _ (complexSection_eq_extension hf hs).symm)
  have hgrepr : P (sg t) ⟨β t, hβ t ht⟩ - P (sg t) ⟨α t, hα t ht⟩ = G t := by
    rw [hG t ht]
    exact (complexPrimitive_sub hLU (sg t) ⟨α t, hα t ht⟩ ⟨β t, hβ t ht⟩
      (oriented_complex_integrable_of_mem (complexExtension_integrable hLU (sg t))
        (hα t ht) (hβ t ht))).trans
      (orientedComplexIntegral_eq_of_eq _ _ (complexSection_eq_extension hg ht).symm)
  have hda : HasDerivAt α (deriv α t) t :=
    ((hcα.differentiableOn_one t ht).differentiableAt (hJ.mem_nhds ht)).hasDerivAt
  have hdb : HasDerivAt β (deriv β t) t :=
    ((hcβ.differentiableOn_one t ht).differentiableAt (hJ.mem_nhds ht)).hasDerivAt
  have hdu : HasDerivAt sf (sg t) t := sectionsOn_hasDerivAt hJ hf hg hd ht
  have ha := primitive_endpoint_hasDerivAt hLU P (complexPrimitive_within hLU)
    hJ hα ht hdu hda
  have hb := primitive_endpoint_hasDerivAt hLU P (complexPrimitive_within hLU)
    hJ hβ ht hdu hdb
  have hresult := (hb.sub ha).congr_of_eventuallyEq
    (Filter.Eventually.mono (hJ.mem_nhds ht) (fun s hs => (hrepr s hs).symm))
  convert hresult using 1
  rw [show sg t = sectionsOn J g hg t from rfl] at hgrepr
  rw [show sf t ⟨β t, hβ t ht⟩ = f t ⟨β t, hβ t ht⟩ from sectionsOn_apply hf ht _,
    show sf t ⟨α t, hα t ht⟩ = f t ⟨α t, hα t ht⟩ from sectionsOn_apply hf ht _]
  rw [← hgrepr]
  abel

end SingleVariableAnalysis.ParameterIntegral
