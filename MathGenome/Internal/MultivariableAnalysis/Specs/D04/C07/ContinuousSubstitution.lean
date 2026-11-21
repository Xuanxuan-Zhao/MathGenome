import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.Localization

/-! Independent statement of paper.tex, d04:07:continuous-substitution.
The input is a bijective C¹ map on open sets, with its actual nonzero
Jacobian. All integrals are the shared open-domain Riemann integrals.
An ambient inverse representative is only constrained on V. -/
noncomputable section
open Set Function
namespace Specs.D04.C07.ContinuousSubstitution
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C06.JordanRegions.Model

/-- Global inverse regularity follows from bijectivity and the local inverse theorem. -/
def global_inverseType : Prop :=
  ∀ {n : ℕ} {U V : Set (E n)} (φ : E n → E n),
    IsOpen U → IsOpen V → ContDiffOn ℝ 1 φ U → BijOn φ U V →
    (∀ x ∈ U, (fderiv ℝ φ x).det ≠ 0) →
    ∃ (e : U ≃ₜ V) (S : E n → E n),
      (∀ x : U, φ x = e x) ∧ (∀ y : V, S y = e.symm y) ∧
      ContDiffOn ℝ 1 S V

/-- Scalar conclusion on a homeomorphism, requiring only forward C¹ regularity.
The preceding obligation supplies the homeomorphism from the original hypotheses. -/
def scalar_substitutionType : Prop :=
  ∀ {n : ℕ} {U V : Set (E n)} (e : U ≃ₜ V) (φ : E n → E n),
    0 < n → IsOpen U → IsOpen V → ContDiffOn ℝ 1 φ U →
    (∀ x : U, φ x = e x) → (∀ x ∈ U, (fderiv ℝ φ x).det ≠ 0) →
    ∀ f : V → ℝ, Continuous f → HasCompactSupport f →
      let g : U → ℝ := fun x => f (e x) * |(fderiv ℝ φ x).det|
      Continuous (zeroExtension f) ∧ HasCompactSupport (zeroExtension f) ∧
      Continuous (zeroExtension g) ∧ HasCompactSupport (zeroExtension g) ∧
      OpenIntegrable f ∧ OpenIntegrable g ∧ openIntegral f = openIntegral g

/-- The complete theorem, including the global C¹ inverse and every finite
real vector target. The scalar case is one coordinate; zero target dimension
is allowed. Coordinate integrability and equality use the canonical scalar
Riemann integral, while continuity and support are for the vector extension. -/
def continuous_substitutionType : Prop :=
  ∀ {n : ℕ} {U V : Set (E n)} (φ : E n → E n),
    0 < n → IsOpen U → IsOpen V → ContDiffOn ℝ 1 φ U → BijOn φ U V →
    (∀ x ∈ U, (fderiv ℝ φ x).det ≠ 0) →
    ∃ (e : U ≃ₜ V) (S : E n → E n),
      (∀ x : U, φ x = e x) ∧ (∀ y : V, S y = e.symm y) ∧
      ContDiffOn ℝ 1 S V ∧
      (∀ f : V → ℝ, Continuous f → HasCompactSupport f →
        let g : U → ℝ := fun x => f (e x) * |(fderiv ℝ φ x).det|
        Continuous (zeroExtension f) ∧ HasCompactSupport (zeroExtension f) ∧
        Continuous (zeroExtension g) ∧ HasCompactSupport (zeroExtension g) ∧
        OpenIntegrable f ∧ OpenIntegrable g ∧ openIntegral f = openIntegral g) ∧
      (∀ (k : ℕ) (f : V → E k), Continuous f → HasCompactSupport f →
        let g : U → E k := fun x => |(fderiv ℝ φ x).det| • f (e x)
        Continuous (zeroExtension f) ∧ HasCompactSupport (zeroExtension f) ∧
        Continuous (zeroExtension g) ∧ HasCompactSupport (zeroExtension g) ∧
        ∀ i : Fin k, OpenIntegrable (fun y => f y i) ∧
          OpenIntegrable (fun x => g x i) ∧
          openIntegral (fun y => f y i) = openIntegral (fun x => g x i))
end Specs.D04.C07.ContinuousSubstitution
