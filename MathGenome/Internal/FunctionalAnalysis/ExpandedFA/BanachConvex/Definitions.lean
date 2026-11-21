import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06Conjugates

/-!
Canonical Banach-space subgradients, their domain, normal cones, and the
normalized duality map (paper.tex:8053–8077). All scalar functionals are
continuous and real-linear. No completeness or smoothness is required.

The primal functions use the established half-extended value space. Nothing
here changes the full `EReal` conjugates of `P1.C06Conjugates` or presumes a
proper conjugate. The finite-domain guard avoids any supporting inequality
at an infinite base value.
-/
namespace ExpandedFA.BanachConvex

open ExpandedFA.P1
open ExpandedFA.P1.ExtendedConvexFunctions

universe u

/-- ∂φ(x), empty outside the finite domain. This definition applies in
particular to every proper convex φ, without assuming lower semicontinuity. -/
def subdifferential (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X) (x : X) : Set (C04Dual.ContinuousDual ℝ X) :=
  {f | x ∈ finiteDomain X φ ∧ ∀ y : X, φ x + (f (y - x) : WithTop ℝ) ≤ φ y}

/-- D(∂φ), the points at which at least one continuous subgradient exists. -/
def subgradientDomain (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X) : Set X :=
  {x | (subdifferential X φ x).Nonempty}

/-- N_C(x), empty when x is outside C. No nonemptiness or closedness of C
is built into this definition. -/
def normalCone (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) (x : X) : Set (C04Dual.ContinuousDual ℝ X) :=
  {f | x ∈ C ∧ ∀ y ∈ C, f (y - x) ≤ 0}

/-- Jx, the normalized, set-valued duality map. In particular this does not
choose a single functional in a space with no smoothness hypothesis. -/
def dualityMap (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (x : X) : Set (C04Dual.ContinuousDual ℝ X) :=
  {f | ‖f‖ = ‖x‖ ∧ f x = ‖x‖ ^ 2}

theorem subdifferential_at_finite_value : Spec.SubdifferentialAtFiniteValue.{u} := by
  intro X _ _ φ x r hx
  ext f
  simp [Spec.SubdifferentialValue, ExtendedConvexFunctions.Spec.finiteDomainValue,
    hx, WithTop.coe_add]

theorem subdifferential_at_infinity : Spec.SubdifferentialAtInfinity.{u} := by
  intro X _ _ φ x hx
  ext f
  simp [Spec.SubdifferentialValue, ExtendedConvexFunctions.Spec.finiteDomainValue, hx]

theorem mem_subgradientDomain : Spec.SubgradientDomainIdentification.{u} := by
  intro X _ _ φ x
  rfl

theorem subgradientDomain_subset_finiteDomain : Spec.SubgradientDomainSubset.{u} := by
  intro X _ _ φ x hx
  obtain ⟨f, hf⟩ := hx
  exact hf.1

theorem normalCone_outside : Spec.NormalConeOutside.{u} := by
  intro X _ _ C x hx
  ext f
  simp [Spec.NormalConeValue, hx]

theorem normalCone_at_member : Spec.NormalConeAtMember.{u} := by
  intro X _ _ C x hx
  ext f
  simp [Spec.NormalConeValue, hx]

theorem dualityMap_zero : Spec.DualityMapAtZero.{u} := by
  intro X _ _
  ext f
  simp [Spec.DualityMapValue]

end ExpandedFA.BanachConvex
