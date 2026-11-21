import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.ProximalMap
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.SubgradientBasicCalculus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Proximal.VariationalFirmness

/-! The subgradient resolvent is the canonical proximal map.
The analytic existence and variational theorem are reused from the accepted
Hilbert proximal interface. The new graph argument identifies I + μ∂φ and its
single-valued inverse, with no exclusion of the zero Hilbert space. -/
noncomputable section
open scoped InnerProductSpace
namespace ExpandedFA.Geometry.ProximalMap
open P1.ExtendedConvexFunctions
universe u

def identityPlusSubgradient : Spec.IdentityPlusSubgradientType.{u} :=
  Spec.IdentityPlusSubgradientValue

def resolvent : Spec.ResolventType.{u} := Spec.ResolventValue

theorem subgradient_riesz : Spec.RieszIdentification.{u} := by
  intro H _ _ _ φ x a
  rw [Proximal.hilbertSubdifferential_riesz_preimage H φ x]
  rfl

theorem subgradient_monotone : Spec.SubgradientMonotone.{u} := by
  intro H _ _ _ φ x y a b ha hb
  have h := BanachConvex.subdifferential_monotone H φ x y
    (InnerProductSpace.toDual ℝ H a) (InnerProductSpace.toDual ℝ H b)
    ((subgradient_riesz H φ x a).mp ha) ((subgradient_riesz H φ y b).mp hb)
  simpa only [sub_apply, InnerProductSpace.toDual_apply_apply,
    inner_sub_left] using h

theorem graph_characterization : Spec.GraphCharacterization.{u} := by
  intro H _ _ _ φ hp hc hl μ hμ f x
  have hchar := (Proximal.proximalMap_characterization H φ hp hc hl μ hμ f x).2
  change (∃ a ∈ Proximal.hilbertSubdifferential H φ x, f = x + μ • a) ↔ _
  constructor
  · rintro ⟨a, ha, heq⟩
    apply hchar.mpr
    have hres : μ⁻¹ • (f - x) = a := by
      rw [heq, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hμ.ne', one_smul]
    rwa [hres]
  · intro hx
    refine ⟨μ⁻¹ • (f - x), hchar.mp hx, ?_⟩
    rw [smul_smul, mul_inv_cancel₀ hμ.ne', one_smul, add_sub_cancel]

theorem identityPlusSubgradient_onto : Spec.Onto.{u} := by
  intro H _ _ _ φ hp hc hl μ hμ f
  exact ⟨Proximal.proximalMap H φ μ f,
    (graph_characterization H φ hp hc hl μ hμ f _).mpr rfl⟩

theorem identityPlusSubgradient_unique_preimage : Spec.UniquePreimage.{u} := by
  intro H _ _ _ φ hp hc hl μ hμ f
  refine ⟨Proximal.proximalMap H φ μ f,
    (graph_characterization H φ hp hc hl μ hμ f _).mpr rfl, ?_⟩
  intro x hx
  exact (graph_characterization H φ hp hc hl μ hμ f x).mp hx

theorem resolvent_eq_proximalMap : Spec.ResolventEqProximal.{u} := by
  intro H _ _ _ φ hp hc hl μ hμ
  funext f
  apply (graph_characterization H φ hp hc hl μ hμ f _).mp
  exact Classical.epsilon_spec (identityPlusSubgradient_onto H φ hp hc hl μ hμ f)

theorem resolvent_inverse : Spec.ResolventInverse.{u} := by
  intro H _ _ _ φ hp hc hl μ hμ f x
  rw [resolvent_eq_proximalMap H φ hp hc hl μ hμ]
  exact graph_characterization H φ hp hc hl μ hμ f x

theorem resolvent_unique_minimizer : Spec.ResolventMinimization.{u} := by
  intro H _ _ _ φ hp hc hl μ hμ f
  rw [resolvent_eq_proximalMap H φ hp hc hl μ hμ]
  exact ⟨Proximal.proximalMap_minimizes H φ hp hc hl μ hμ f,
    Proximal.minimizer_iff_eq_proximalMap H φ μ f
      (Proximal.exists_unique_proximalMinimizer H φ hp hc hl μ hμ f)⟩

theorem resolvent_residual_subgradient : Spec.ResidualSubgradient.{u} := by
  intro H _ _ _ φ hp hc hl μ hμ f
  rw [resolvent_eq_proximalMap H φ hp hc hl μ hμ]
  exact (Proximal.proximalMap_characterization H φ hp hc hl μ hμ f _).2.mp rfl

theorem resolvent_firm : Spec.FirmBound.{u} := by
  intro H _ _ _ φ hp hc hl μ hμ f g
  rw [resolvent_eq_proximalMap H φ hp hc hl μ hμ]
  exact Proximal.proximalMap_firm H φ hp hc hl μ hμ f g

end ExpandedFA.Geometry.ProximalMap
