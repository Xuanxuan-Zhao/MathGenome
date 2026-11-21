import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.ErgodicExponents
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.Birkhoff

namespace D13Unified.Ch18.ErgodicExponents
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- On a one-dimensional space a linear endomorphism is multiplication by
its determinant. This works with every norm on the space. -/
lemma apply_eq_det_smul (h : Module.finrank ℝ E = 1)
    (L : E →ₗ[ℝ] E) (v : E) (hv : v ≠ 0) : L v = LinearMap.det L • v := by
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one h hv (L v)
  have hL : L = c • LinearMap.id := by
    ext w
    obtain ⟨a, rfl⟩ := exists_smul_eq_of_finrank_eq_one h hv w
    simp [← hc, smul_smul, mul_comm]
  rw [hL, LinearMap.det_smul, h, pow_one, LinearMap.det_id, mul_one]
  rfl

lemma directionalRate_eq_volume (h : Module.finrank ℝ E = 1)
    (L : E →L[ℝ] E) (v : E) (hv : v ≠ 0) (t : ℝ) :
    Specs.D13Unified.Ch18.GrowthDefinitions.directionalRate L v t =
      Specs.D13Unified.Ch18.GrowthDefinitions.logarithmicRate t |LinearMap.det L.toLinearMap| := by
  unfold Specs.D13Unified.Ch18.GrowthDefinitions.directionalRate
  have he : L v = LinearMap.det L.toLinearMap • v := apply_eq_det_smul h _ v hv
  rw [he, norm_smul, Real.norm_eq_abs, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hv)]

/-- Differentiability of all iterates along an invariant set only needs
regularity on an open neighbourhood of that set. -/
lemma differentiableAt_iterate (F : E → E) {U K : Set E} (hU : IsOpen U)
    (hF : DifferentiableOn ℝ F U) (hKU : K ⊆ U) (hK : MapsTo F K K)
    (n : ℕ) {x : E} (hx : x ∈ K) : DifferentiableAt ℝ F^[n] x := by
  induction n with
  | zero => simpa using (differentiableAt_id : DifferentiableAt ℝ (id : E → E) x)
  | succ n ih =>
    rw [Function.iterate_succ']
    exact (hF.differentiableAt (hU.mem_nhds (hKU (hK.iterate n hx)))).comp x ih

lemma det_fderiv_iterate_succ (F : E → E) {U K : Set E} (hU : IsOpen U)
    (hF : DifferentiableOn ℝ F U) (hKU : K ⊆ U) (hK : MapsTo F K K)
    (n : ℕ) {x : E} (hx : x ∈ K) :
    LinearMap.det (fderiv ℝ F^[n+1] x).toLinearMap =
      LinearMap.det (fderiv ℝ F (F^[n] x)).toLinearMap *
        LinearMap.det (fderiv ℝ F^[n] x).toLinearMap := by
  rw [Function.iterate_succ', fderiv_comp x
    (hF.differentiableAt (hU.mem_nhds (hKU (hK.iterate n hx))))
    (differentiableAt_iterate F hU hF hKU hK n hx)]
  exact LinearMap.det_comp _ _

/-- Restricting the map to K preserves the ambient orbit. -/
lemma subtype_iterate (F : E → E) {K : Set E} (hK : MapsTo F K K)
    (n : ℕ) (x : K) :
    ((fun x : K => (⟨F x, hK x.property⟩ : K))^[n] x : E) = F^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', ih]

/-- The volume limit and, in dimension one, every directional limit. -/
theorem volume_exponent : Specs.D13Unified.Ch18.ErgodicExponents.volumeExponentStatement.{u} := by
  intro E _ _ _ _ F U K hU hF _hcompact hKU hK μ _ T J g hT hnz hlog
  have hdiff : DifferentiableOn ℝ F U := hF.differentiableOn (by simp)
  have horbit (n : ℕ) (x : K) : (T^[n] x : E) = F^[n] x :=
    subtype_iterate F hK n x
  have hgood : ∀ᵐ (x : K) ∂μ, ∀ j : ℕ, J 1 (F^[j] x) ≠ 0 := by
    rw [ae_all_iff]
    intro j
    have hj := (hT.iterate j).quasiMeasurePreserving.ae hnz
    filter_upwards [hj] with x hx
    simpa only [horbit] using hx
  obtain ⟨gstar, hgstar, hconv, _hl1, hinv, _hsets, hint, herg⟩ :=
    Ch19.Birkhoff.real_birkhoff T μ hT g hlog
  refine ⟨gstar, hgstar, hinv, hint, herg, ?_⟩
  filter_upwards [hgood, hconv] with x hx hcx
  have hformula : ∀ n : ℕ, J n x ≠ 0 ∧
      Real.log |J n x| = ∑ j ∈ Finset.range n, g (T^[j] x) := by
    intro n
    induction n with
    | zero => simp [J]
    | succ n ih =>
      have he : J (n+1) x = J 1 (F^[n] x) * J n x := by
        simpa only [J, Function.iterate_one] using
          det_fderiv_iterate_succ F hU hdiff hKU hK n x.property
      refine ⟨by rw [he]; exact mul_ne_zero (hx n) ih.1, ?_⟩
      rw [he, abs_mul, Real.log_mul (abs_ne_zero.mpr (hx n)) (abs_ne_zero.mpr ih.1),
        ih.2, Finset.sum_range_succ]
      simp only [g, horbit]
      exact add_comm _ _
  have hreal : Tendsto (fun n : ℕ => Real.log |J n x| / (n : ℝ))
      atTop (𝓝 (gstar x)) := by
    convert hcx using 1
    ext n
    rw [(hformula n).2]
    simp [Specs.D13Unified.Ch19.MeasureDefinitions.ergodicAverage,
      birkhoffAverage, birkhoffSum, div_eq_inv_mul]
  have hext : Tendsto (fun n : ℕ => Specs.D13Unified.Ch18.GrowthDefinitions.logarithmicRate (n : ℝ) |J n x|)
      atTop (𝓝 (gstar x : EReal)) := by
    have hc := continuous_coe_real_ereal.continuousAt.tendsto.comp hreal
    convert hc using 1
    ext n
    exact ite_eq_right (abs_ne_zero.mpr (hformula n).1)
  refine ⟨hx, hformula, hreal, hext, ?_⟩
  intro hdim v hv
  have hs := hext.comp (tendsto_add_atTop_nat 1)
  convert hs using 1
  ext n
  simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one] using
    directionalRate_eq_volume hdim (fderiv ℝ F^[n+1] x) v hv ((n+1 : ℕ) : ℝ)

set_option maxHeartbeats 800000 in
/-- In dimension one the volume limit is the existing directional exponent
defined in the shared growth interface. -/
theorem scalar_exponent : Specs.D13Unified.Ch18.ErgodicExponents.scalarExponentStatement.{u} := by
  intro E _ _ _ _ hdim F K hcompact hKU hK μ _ T J g hT hnz hlog
  obtain ⟨gstar, hgstar, hinv, hint, herg, hlim⟩ :=
    volume_exponent F.value F.domain K F.isOpen_domain F.contDiffOn hcompact hKU hK μ
      hT (by simpa only [Function.iterate_one] using hnz)
      (by simpa only [Function.iterate_one] using hlog)
  refine ⟨gstar, hgstar, hinv, hint, herg, ?_⟩
  filter_upwards [hlim] with x hx
  intro v hv
  have hd := hx.2.2.2.2 hdim v hv
  change Tendsto (fun n : ℕ => Specs.D13Unified.Ch18.GrowthDefinitions.directionalRate
    (fderivWithin ℝ F.value^[n+1] F.domain x) v ((n+1 : ℕ) : ℝ)) atTop (𝓝 (gstar x : EReal))
  simpa only [fderivWithin_of_isOpen F.isOpen_domain (hKU x.property),
    Nat.cast_add, Nat.cast_one] using hd

end
end D13Unified.Ch18.ErgodicExponents
