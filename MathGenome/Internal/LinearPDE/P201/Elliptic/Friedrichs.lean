import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.Friedrichs
import MathGenome.Internal.LinearPDE.P201.Elliptic.ClosedForm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.FriedrichsExtension

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProductSpace ComplexConjugate
open UniformSpace
universe u v
namespace P201.Elliptic
open ExpandedFA.Unbounded
open FriedrichsExtension FriedrichsData

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Slot reversal preserves the entire canonical graph, including its domain. -/
theorem paperForm_associated (q : ClosedNonnegativeForms.NonnegativeForm 𝕜 H) :
    (paperForm q).associatedOperator = q.associatedOperator := by
  apply LinearPMap.eq_of_eq_graph
  ext ⟨x, f⟩
  rw [(paperForm q).mem_associated_graph, q.associated]
  rfl

/-- Any realization of the form completion is isometric for its energy norm. -/
def formClosureEnergyEquiv (q : ClosedNonnegativeForms.NonnegativeForm 𝕜 H)
    (F : FormClosure q) : Completion q.EnergySpace ≃ₗᵢ[𝕜] F.closedForm.EnergySpace := by
  let e : Completion q.EnergySpace ≃ₗ[𝕜] F.closedForm.EnergySpace := F.equivalence
  apply e.isometryOfInner
  intro x y
  change F.closedForm.form (F.equivalence x) (F.equivalence y) +
    inner 𝕜 (F.equivalence x : H) (F.equivalence y : H) = inner 𝕜 x y
  rw [F.inclusion, F.inclusion]
  exact F.energy_identity x y

/-- The initial domain is a dense form core, even when it is not complete. -/
theorem formClosure_dense_core (q : ClosedNonnegativeForms.NonnegativeForm 𝕜 H)
    (F : FormClosure q) :
    DenseRange (fun x : q.EnergySpace =>
      (show F.closedForm.EnergySpace from F.equivalence (x : Completion q.EnergySpace))) := by
  exact (formClosureEnergyEquiv q F).surjective.denseRange.comp
    Completion.denseRange_coe (formClosureEnergyEquiv q F).continuous

/-- The completed form agrees with the original form on its original core. -/
theorem formClosure_on_core (q : ClosedNonnegativeForms.NonnegativeForm 𝕜 H)
    (F : FormClosure q) (x y : q.EnergySpace) :
    F.closedForm.form (F.equivalence (y : Completion q.EnergySpace))
      (F.equivalence (x : Completion q.EnergySpace)) = q.form (q.toDomain y) (q.toDomain x) := by
  have he := F.energy_identity (y : Completion q.EnergySpace) (x : Completion q.EnergySpace)
  rw [F.on_core, F.on_core, Completion.inner_coe, q.energy_inner] at he
  exact add_right_cancel he

/-- Friedrichs extension from precisely density, symmetry, and a real lower
bound. The library constructs the closure; none is supplied as a hypothesis. -/
theorem semibounded_friedrichs : FriedrichsExpected.Extension.{u, v} := by
  intro 𝕜 H _ _ _ _ T m hd hs hl h q
  refine ⟨?_, ?_, closability T m h, ?_⟩
  · intro x y
    exact operatorForm_apply T m h y x
  · intro x
    rw [q.energy_norm, operatorForm_apply]
    change RCLike.re (inner 𝕜 (q.toDomain x : H) (T (q.toDomain x)) -
        (m : 𝕜) * inner 𝕜 (q.toDomain x : H) (q.toDomain x : H)) +
        ‖(q.toDomain x : H)‖ ^ 2 =
      RCLike.re (inner 𝕜 (q.toDomain x : H)
        (T (q.toDomain x) + ((1 - m : ℝ) : 𝕜) • (q.toDomain x : H)))
    rw [inner_add_right, inner_smul_right, map_sub, map_add,
      RCLike.re_ofReal_mul, RCLike.re_ofReal_mul, ← norm_sq_eq_re_inner]
    ring
  · obtain ⟨F, A, hA, _⟩ := friedrichs_extension T m h
    refine ⟨F, formClosure_dense_core q F, formClosure_on_core q F, A, ?_,
      hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2⟩
    rw [paperForm_associated]
    exact F.closedForm.associated_unique hA.1 F.closedForm.associated

/-- The complete source theorem, with independently quantified form and
operator data and the compact shifted inverse supplied by `closed_form`. -/
theorem closed_forms_and_friedrichs : FriedrichsExpected.ClosedFormsAndFriedrichs.{u, v} :=
  ⟨closed_form, semibounded_friedrichs⟩

end P201.Elliptic
