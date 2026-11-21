import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.OneCoordinate

/-! Independent obligations for `paper.tex`, d04:07:affine. The integral is
exactly the shared open-domain Darboux integral. All dimensions include zero.
Ambient representatives are constrained only on the indicated open domains. -/
noncomputable section
open Set
namespace Specs.D04.C07.AffineComposition
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C06.JordanRegions.Model
namespace Model
/-- The continuous compact-support substitution identity on the actual domains. -/
def Substitution {n : ℕ} {U V : Set (E n)} (e : U ≃ₜ V)
    (φ : E n → E n) : Prop :=
  ∀ f : V → ℝ, Continuous f → HasCompactSupport f →
    openIntegral f = openIntegral (fun x : U => f (e x) * |(fderiv ℝ φ x).det|)
end Model
open Model

/-- Composition, including continuity, compact support, zero-extension
continuity and integrability of the transformed test function. Forward C¹
regularity and a homeomorphism suffice, so this includes C¹ diffeomorphisms. -/
def compositionType : Prop :=
  ∀ {n : ℕ} {U V W : Set (E n)} (s : U ≃ₜ V) (t : V ≃ₜ W)
    (S T : E n → E n), IsOpen U → IsOpen V → IsOpen W →
    ContDiffOn ℝ 1 S U → ContDiffOn ℝ 1 T V →
    (∀ x : U, S x = s x) → (∀ y : V, T y = t y) →
    Substitution s S → Substitution t T →
    (∀ x : U, |(fderiv ℝ (T ∘ S) x).det| =
      |(fderiv ℝ T (S x)).det| * |(fderiv ℝ S x).det|) ∧
    ∀ f : W → ℝ, Continuous f → HasCompactSupport f →
      let g : V → ℝ := fun y => f (t y) * |(fderiv ℝ T y).det|
      let h : U → ℝ := fun x => f ((s.trans t) x) * |(fderiv ℝ (T ∘ S) x).det|
      Continuous g ∧ HasCompactSupport g ∧ Continuous (zeroExtension g) ∧
      OpenIntegrable g ∧ Continuous (zeroExtension f) ∧ OpenIntegrable f ∧
      Continuous (zeroExtension h) ∧ OpenIntegrable h ∧
      openIntegral f = openIntegral h

/-- The derivative of every affine map is its linear part, in the actual
standard-coordinate representation. No volume assertion is assumed. -/
def affine_jacobianType : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n),
    (fderiv ℝ (fun y => matrixLinearEquiv n n A y + b) x).det = A.det

/-- All invertible affine maps, on arbitrary open domains identified by the
map. Includes translations, shears and dimension zero. -/
def affine_substitutionType : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : E n), A.det ≠ 0 →
    ∀ {U V : Set (E n)} (e : U ≃ₜ V), IsOpen U → IsOpen V →
    (∀ x : U, matrixLinearEquiv n n A x + b = e x) →
    ∀ f : V → ℝ, Continuous f → HasCompactSupport f →
      let g : U → ℝ := fun x => f (e x) * |A.det|
      Continuous (zeroExtension f) ∧ Continuous (zeroExtension g) ∧
      OpenIntegrable f ∧ OpenIntegrable g ∧ openIntegral f = openIntegral g
end Specs.D04.C07.AffineComposition
