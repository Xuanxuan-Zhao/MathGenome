import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.ContinuousSubstitution

/-! Full compact-supported Riemann substitution, paper.tex d04:07:substitution.
A diffeomorphism is represented by a homeomorphism of the actual open domains
and C¹ ambient representatives in both directions. The representatives are
constrained only on those domains. No integrability, boundedness of a Jacobian,
or regularity of the integrand is part of the diffeomorphism data. -/
noncomputable section
open Set
namespace Specs.D04.C07.RiemannSubstitution
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C06.JordanRegions.Model

def riemann_substitutionType : Prop :=
  ∀ {n : ℕ} {U V : Set (E n)} (e : U ≃ₜ V) (φ ψ : E n → E n),
    IsOpen U → IsOpen V → ContDiffOn ℝ 1 φ U → ContDiffOn ℝ 1 ψ V →
    (∀ x : U, φ x = e x) → (∀ y : V, ψ y = e.symm y) →
    ∀ f : V → ℝ, RegionBounded f → HasCompactSupport f →
      let g : U → ℝ := fun x => f (e x) * |(fderiv ℝ φ x).det|
      RegionBounded g ∧ HasCompactSupport g ∧
      HasCompactSupport (zeroExtension g) ∧ tsupport (zeroExtension g) ⊆ U ∧
      (OpenIntegrable f ↔ OpenIntegrable g) ∧
      ((OpenIntegrable f ∨ OpenIntegrable g) → openIntegral f = openIntegral g)

/-- The boundary case is evaluation, with no null-set condition on R⁰. -/
def zero_dimensionType : Prop :=
  ∀ {U V : Set (E 0)} (e : U ≃ₜ V) (φ : E 0 → E 0),
    IsOpen U → IsOpen V → ∀ f : V → ℝ,
      let g : U → ℝ := fun x => f (e x) * |(fderiv ℝ φ x).det|
      (∀ x, (fderiv ℝ φ x).det = 1) ∧ OpenIntegrable f ∧ OpenIntegrable g ∧
      openIntegral f = zeroExtension f 0 ∧
      openIntegral g = zeroExtension g 0 ∧ openIntegral f = openIntegral g

end Specs.D04.C07.RiemannSubstitution
