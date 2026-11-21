import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces

/-! Independent statements of `d04:04:injective-local-diffeomorphism`.
Maps on open sets are represented by ambient functions. Injectivity is
required only on U, and the inverse is required only on the actual image.
The recursive finite classes and their intersection express the source's
finite and infinite regularity, with no nonemptiness or dimension restriction. -/
noncomputable section
open Set
namespace Specs.D04.C04.InjectiveGlobalInverse
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model

def injective_global_inverse_finiteType : Prop :=
  ∀ {n : ℕ} (r : ℕ) (U : Set (E n)) (f : E n → E n),
    1 ≤ r → IsOpen U → CrOn r U f → InjOn f U →
    (∀ x ∈ U, ∃ A : E n ≃ₗ[ℝ] E n,
      A.toContinuousLinearEquiv.toContinuousLinearMap = totalDerivative f x) →
    IsOpen (f '' U) ∧ BijOn f U (f '' U) ∧
      ∃ g : E n → E n, MapsTo g (f '' U) U ∧
        LeftInvOn g f U ∧ RightInvOn g f (f '' U) ∧ CrOn r (f '' U) g

def injective_global_inverse_smoothType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → E n),
    IsOpen U → SmoothOn U f → InjOn f U →
    (∀ x ∈ U, ∃ A : E n ≃ₗ[ℝ] E n,
      A.toContinuousLinearEquiv.toContinuousLinearMap = totalDerivative f x) →
    IsOpen (f '' U) ∧ BijOn f U (f '' U) ∧
      ∃ g : E n → E n, MapsTo g (f '' U) U ∧
        LeftInvOn g f U ∧ RightInvOn g f (f '' U) ∧ SmoothOn (f '' U) g

end Specs.D04.C04.InjectiveGlobalInverse
