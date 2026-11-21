import MathGenome.Internal.LinearPDE.P201Specs.Heat.FormOperator
import MathGenome.Internal.LinearPDE.P201.Elliptic.ClosedForm
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.UniformSpace.Equiv

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProductSpace
universe u v
namespace P201.Heat
namespace CoerciveForm
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (d : CoerciveForm V H)

@[simp] theorem rangeEquiv_coe (x : V) : (d.rangeEquiv x : H) = d.j x := rfl

@[simp] theorem toEnergy_inclusion (x : V) :
    d.energyForm.inclusion (d.toEnergy x) = d.j x := rfl

@[simp] theorem energy_form (x y : V) :
    d.denseForm.form (d.rangeEquiv x) (d.rangeEquiv y) = d.a x y := by
  change d.a (d.rangeEquiv.symm (d.rangeEquiv x))
    (d.rangeEquiv.symm (d.rangeEquiv y)) = _
  simp only [LinearEquiv.symm_apply_apply]

theorem energy_norm (x : V) :
    ‖d.toEnergy x‖ ^ 2 = d.a x x + ‖d.j x‖ ^ 2 := by
  have h := d.energyForm.energy_norm (d.toEnergy x)
  change ‖d.toEnergy x‖ ^ 2 =
    d.denseForm.form (d.rangeEquiv x) (d.rangeEquiv x) + ‖d.j x‖ ^ 2 at h
  simpa only [d.energy_form] using h

theorem energy_bound (x : V) :
    ‖d.toEnergy x‖ ≤ Real.sqrt (‖d.a‖ + ‖d.j‖ ^ 2) * ‖x‖ := by
  have ha := d.a.le_opNorm₂ x x
  have hj := d.j.le_opNorm x
  have hnon : 0 ≤ ‖d.a‖ + ‖d.j‖ ^ 2 := by positivity
  have hs := Real.sq_sqrt hnon
  have hn := d.energy_norm x
  have haa : d.a x x ≤ ‖d.a‖ * ‖x‖ * ‖x‖ := (le_abs_self _).trans ha
  have hjj : ‖d.j x‖ ^ 2 ≤ ‖d.j‖ ^ 2 * ‖x‖ ^ 2 := by
    nlinarith [norm_nonneg (d.j x), norm_nonneg d.j, norm_nonneg x]
  have hb : ‖d.toEnergy x‖ ^ 2 ≤ (Real.sqrt (‖d.a‖ + ‖d.j‖ ^ 2) * ‖x‖) ^ 2 := by
    nlinarith
  exact le_of_sq_le_sq hb (by positivity)

theorem energy_inverse_bound :
    ∃ C : ℝ, ∀ x : d.energyForm.EnergySpace, ‖d.toEnergy.symm x‖ ≤ C * ‖x‖ := by
  obtain ⟨c, hc, hb⟩ := d.coercive
  refine ⟨(Real.sqrt c)⁻¹, fun x => ?_⟩
  let y := d.toEnergy.symm x
  have he : d.toEnergy y = x := d.toEnergy.apply_symm_apply x
  have hn := d.energy_norm y
  rw [he] at hn
  have hs := Real.sq_sqrt hc.le
  have hp : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hmul : Real.sqrt c * ‖y‖ ≤ ‖x‖ := by
    have hb' := hb y
    nlinarith [sq_nonneg ‖d.j y‖, norm_nonneg x, norm_nonneg y]
  have hh : ‖y‖ ≤ ‖x‖ / Real.sqrt c :=
    (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hmul)
  simpa only [div_eq_mul_inv, mul_comm] using hh

/-- The algebraic range transport is an isomorphism for the actual energy norm. -/
def energyEquiv : V ≃L[ℝ] d.energyForm.EnergySpace :=
  d.toEnergy.toContinuousLinearEquivOfBounds
    (Real.sqrt (‖d.a‖ + ‖d.j‖ ^ 2)) (Classical.choose d.energy_inverse_bound)
    d.energy_bound (Classical.choose_spec d.energy_inverse_bound)

theorem energy_closed [CompleteSpace V] : d.energyForm.IsClosed := by
  let e : V ≃ᵤ d.energyForm.EnergySpace :=
    ⟨d.energyEquiv.toEquiv, d.energyEquiv.toContinuousLinearMap.uniformContinuous,
      d.energyEquiv.symm.toContinuousLinearMap.uniformContinuous⟩
  exact e.completeSpace_iff.mp inferInstance

theorem energy_identification [CompleteSpace V] : FormOperatorExpected.EnergyIdentification d := by
  exact ⟨⟨d.energyEquiv, fun _ => rfl, d.toEnergy_inclusion, d.energy_norm⟩, d.energy_closed⟩

/-- The graph criterion with a vector in the original form space. -/
theorem mem_graph_at (x : V) (h : H) :
    (d.j x, h) ∈ d.operator.graph ↔ ∀ w : V, d.a x w = inner ℝ (d.j w) h := by
  change (d.j x, h) ∈ d.denseForm.associatedOperator.graph ↔ _
  rw [P201.Elliptic.DenseForm.mem_associated_graph]
  constructor
  · rintro ⟨hx, hf⟩ w
    have he : (⟨d.j x, hx⟩ : d.denseForm.domain) = d.rangeEquiv x := rfl
    simpa only [he, d.energy_form, P201.Elliptic.paperInner, d.rangeEquiv_coe] using
      hf (d.rangeEquiv w)
  · intro hf
    refine ⟨(d.rangeEquiv x).property, fun w => ?_⟩
    have he : (⟨d.j x, (d.rangeEquiv x).property⟩ : d.denseForm.domain) = d.rangeEquiv x := rfl
    rw [he, ← d.rangeEquiv.apply_symm_apply w]
    simpa only [d.energy_form, P201.Elliptic.paperInner, d.rangeEquiv_coe] using
      hf (d.rangeEquiv.symm w)

theorem mem_graph (x h : H) :
    (x, h) ∈ d.operator.graph ↔
      ∃ v : V, d.j v = x ∧ ∀ w : V, d.a v w = inner ℝ (d.j w) h := by
  constructor
  · intro hx
    obtain ⟨hdom, _⟩ := (d.denseForm.mem_associated_graph x h).mp hx
    obtain ⟨v, hv⟩ := hdom
    exact ⟨v, hv, (d.mem_graph_at v h).mp (hv.symm ▸ hx)⟩
  · rintro ⟨v, rfl, hv⟩
    exact (d.mem_graph_at v h).mpr hv

theorem exact_operator : FormOperatorExpected.ExactOperator d := by
  refine ⟨d.mem_graph, ?_, ?_, ?_⟩
  · intro x
    rw [LinearPMap.mem_domain_iff]
    constructor
    · rintro ⟨h, hx⟩
      obtain ⟨v, hv, hrep⟩ := (d.mem_graph x h).mp hx
      exact ⟨v, hv, h, hrep⟩
    · rintro ⟨v, hv, h, hrep⟩
      exact ⟨h, (d.mem_graph x h).mpr ⟨v, hv, hrep⟩⟩
  · intro v h k hh hk
    apply Dense.eq_of_inner_right (𝕜 := ℝ) d.dense
    rintro _ ⟨w, rfl⟩
    exact (hh w).symm.trans (hk w)
  · intro v h hv hh
    obtain ⟨x, hx, hval⟩ := d.operator.mem_graph_iff.mp ((d.mem_graph_at v h).mpr hh)
    have he : x = (⟨d.j v, hv⟩ : d.operator.domain) := Subtype.ext hx
    simpa only [he] using hval

/-- Closed-form representation, transported back to the given V topology. -/
theorem representation [CompleteSpace V] [CompleteSpace H] :
    FormOperatorExpected.Representation d := by
  obtain ⟨_, hd, hs, hn, S, _, hsol, hgraph, _⟩ :=
    P201.Elliptic.closed_form d.denseForm d.denseForm_hermitian
      d.denseForm_nonnegative d.energy_closed
  let K : H →L[ℝ] V := d.energyEquiv.symm.toContinuousLinearMap.comp S
  have hK (f : H) : d.toEnergy (K f) = S f := d.toEnergy.apply_symm_apply (S f)
  have hjK (f : H) : d.j (K f) = d.energyForm.inclusion (S f) := by
    rw [← d.toEnergy_inclusion, hK]
  have htest (f : H) (v : V) :
      (∀ w : d.denseForm.domain,
        d.denseForm.form (d.rangeEquiv v) w +
          P201.Elliptic.paperInner (𝕜 := ℝ) (d.j v) (w : H) =
          P201.Elliptic.paperInner (𝕜 := ℝ) f (w : H)) ↔
      (∀ w : V, d.a v w + inner ℝ (d.j w) (d.j v) = inner ℝ (d.j w) f) := by
    constructor
    · intro hv w
      simpa only [d.energy_form, P201.Elliptic.paperInner, d.rangeEquiv_coe] using
        hv (d.rangeEquiv w)
    · intro hv w
      rw [← d.rangeEquiv.apply_symm_apply w]
      simpa only [d.energy_form, P201.Elliptic.paperInner, d.rangeEquiv_coe] using
        hv (d.rangeEquiv.symm w)
  refine ⟨hd, hs, hn, K, ?_, ?_, ?_⟩
  · intro f v
    have hiff := (htest f v).symm.trans (hsol f (d.rangeEquiv v))
    apply hiff.trans
    change d.toEnergy v = S f ↔ v = K f
    rw [← hK f]
    exact d.toEnergy.injective.eq_iff
  · intro x f
    exact (hgraph x f).trans (by rw [hjK]; rfl)
  · intro hj
    exact hj.comp_clm K

end CoerciveForm
/-- Exact canonical graph, domain, representing action and uniqueness. -/
theorem form_operator_exact : FormOperatorExpected.ExactTheorem.{u, v} := by
  intro V H _ _ _ _ d
  exact d.exact_operator

/-- The image form is closed in its energy norm, equivalent to the given V norm. -/
theorem form_operator_energy : FormOperatorExpected.EnergyTheorem.{u, v} := by
  intro V H _ _ _ _ _ d
  exact d.energy_identification

/-- Nonnegative self-adjointness, shifted inverse and conditional compactness. -/
theorem form_operator_representation : FormOperatorExpected.RepresentationTheorem.{u, v} := by
  intro V H _ _ _ _ _ _ d
  exact d.representation

end P201.Heat
