import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.Localization
import Mathlib.Analysis.Calculus.ContDiff.Defs
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.MonotoneSubstitution

/-! Independent statements for paper.tex, d04:07:one-coordinate.
The maps have ambient representatives, with regularity required only on their
actual open domains. The integral is the shared Darboux integral of the zero
extension, not a measure integral. Inverse regularity is part of the original
C¹ diffeomorphism hypothesis, rather than an assumed Jacobian certificate. -/
noncomputable section
open Set
namespace Specs.D04.C07.OneCoordinate
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C06.JordanRegions.Model
namespace Model
/-- Replace just the indicated coordinate. -/
def coordinateChange {n : ℕ} (j : Fin n) (ψ : E n → ℝ) (x : E n) : E n :=
  WithLp.toLp 2 (Function.update (fun i => x i) j (ψ x))
/-- The ordinary coordinate partial, evaluated on the standard unit vector. -/
def coordinatePartial {n : ℕ} (j : Fin n) (ψ : E n → ℝ) (x : E n) : ℝ :=
  fderiv ℝ ψ x (standardBasis n j)
/-- Coordinate permutation, with (Px)_i = x_(σ i). -/
def permute {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : E n) : E n :=
  WithLp.toLp 2 (fun i => x (σ i))
end Model
open Model
abbrev coordinateChangeType := {n : ℕ} → Fin n → (E n → ℝ) → E n → E n
def coordinateChangeValue : coordinateChangeType := @Model.coordinateChange
abbrev coordinatePartialType := {n : ℕ} → Fin n → (E n → ℝ) → E n → ℝ
def coordinatePartialValue : coordinatePartialType := @Model.coordinatePartial
abbrev permuteType := {n : ℕ} → Equiv.Perm (Fin n) → E n → E n
def permuteValue : permuteType := @Model.permute

/-- The full one-coordinate substitution assertion, with both zero extensions
continuous and Riemann integrable. `j : Fin n` enforces positive dimension. -/
def substitutionType : Prop :=
  ∀ {n : ℕ} (j : Fin n) (U V : Set (E n)) (e : U ≃ₜ V)
    (ψ : E n → ℝ) (S : E n → E n),
    IsOpen U → IsOpen V → ContDiffOn ℝ 1 (coordinateChange j ψ) U → ContDiffOn ℝ 1 S V →
    (∀ x : U, coordinateChange j ψ x = e x) →
    (∀ y : V, S y = e.symm y) →
    ∀ f : V → ℝ, Continuous f → HasCompactSupport f →
      let g : U → ℝ := fun x => f (e x) * |coordinatePartial j ψ x|
      Continuous (zeroExtension f) ∧ Continuous (zeroExtension g) ∧
      OpenIntegrable f ∧ OpenIntegrable g ∧ openIntegral f = openIntegral g

/-- The integrability portion does not require any sign hypothesis. -/
def integrabilityType : Prop :=
  ∀ {n : ℕ} (j : Fin n) {U V : Set (E n)} (e : U ≃ₜ V)
    (ψ : E n → ℝ), IsOpen U → IsOpen V → ContDiffOn ℝ 1 ψ U →
    ∀ f : V → ℝ, Continuous f → HasCompactSupport f →
      let g : U → ℝ := fun x => f (e x) * |coordinatePartial j ψ x|
      Continuous (zeroExtension f) ∧ Continuous (zeroExtension g) ∧
      OpenIntegrable f ∧ OpenIntegrable g

/-- The determinant is the changed coordinate partial, with its actual sign. -/
def determinantType : Prop :=
  ∀ {n : ℕ} (j : Fin n) (ψ : E n → ℝ) (x : E n),
    DifferentiableAt ℝ ψ x →
    (fderiv ℝ (coordinateChange j ψ) x).det = coordinatePartial j ψ x

/-- Permutations on any pair of open domains identified by the permutation.
This includes all of Rⁿ and includes dimension zero. -/
def permutation_substitutionType : Prop :=
  ∀ {n : ℕ} (σ : Equiv.Perm (Fin n)) (U V : Set (E n)) (e : U ≃ₜ V),
    IsOpen U → IsOpen V → (∀ x : U, permute σ x = e x) →
    ∀ f : V → ℝ, Continuous f → HasCompactSupport f →
      Continuous (zeroExtension f) ∧ Continuous (zeroExtension (f ∘ e)) ∧
      OpenIntegrable f ∧ OpenIntegrable (f ∘ e) ∧
      openIntegral f = openIntegral (f ∘ e)

def permutation_jacobianType : Prop :=
  ∀ {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : E n),
    |(fderiv ℝ (permute σ) x).det| = 1
/-- Unsigned scalar substitution for either derivative sign. This is stated
in the same one-dimensional Darboux representation used by Riemann Fubini. -/
def scalar_substitutionType : Prop :=
  ∀ (φ dφ f : ℝ → ℝ) (a b : ℝ) (hab : a < b),
    Specs.SingleVariableAnalysis.Ch09.MonotoneSubstitution.C1OnInterval φ dφ a b →
    ((∀ t ∈ Icc a b, 0 < dφ t) ∨ (∀ t ∈ Icc a b, dφ t < 0)) →
    Continuous f →
    let A := Specs.D04.C06.DarbouxIntegral.Model.intervalBox a b hab.le
    let B := Specs.D04.C06.DarbouxIntegral.Model.intervalBox
      (min (φ a) (φ b)) (max (φ a) (φ b)) min_le_max
    let F : E 1 → ℝ := fun y => f (y 0)
    let G : E 1 → ℝ := fun y => |dφ (y 0)| * f (φ (y 0))
    Specs.D04.C06.DarbouxIntegral.Model.Integrable G A ∧
    Specs.D04.C06.DarbouxIntegral.Model.Integrable F B ∧
    Specs.D04.C06.DarbouxIntegral.Model.lowerIntegral G A =
      Specs.D04.C06.DarbouxIntegral.Model.lowerIntegral F B
/-- Inverse regularity forces the changed-coordinate partial to be nonzero. -/
def nonvanishingType : Prop :=
  ∀ {n : ℕ} (j : Fin n) {U V : Set (E n)} (e : U ≃ₜ V)
    (ψ : E n → ℝ) (S : E n → E n),
    IsOpen U → IsOpen V → ContDiffOn ℝ 1 ψ U → ContDiffOn ℝ 1 S V →
    (∀ x : U, coordinateChange j ψ x = e x) →
    (∀ y : V, S y = e.symm y) →
    ∀ x ∈ U, coordinatePartial j ψ x ≠ 0
/-- The C¹ map hypothesis is equivalent to the C¹ scalar coefficient
hypothesis, so neither representation strengthens the source statement. -/
def regularityType : Prop :=
  ∀ {n : ℕ} (j : Fin n) (ψ : E n → ℝ) (U : Set (E n)),
    ContDiffOn ℝ 1 (coordinateChange j ψ) U ↔ ContDiffOn ℝ 1 ψ U

/-- Identify the derivative coefficient with the usual coordinate partial. -/
def partial_derivativeType : Prop :=
  ∀ {n : ℕ} (j : Fin n) (ψ : E n → ℝ) (x : E n),
    DifferentiableAt ℝ ψ x →
    coordinatePartial j ψ x = deriv (fun t : ℝ => ψ (x + t • standardBasis n j)) 0
end Specs.D04.C07.OneCoordinate
