import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.RegionSubstitution
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.PullbackCalculus
import Mathlib.Basic.Real.Sign
import Mathlib.Topology.Connected.LocallyConnected

/-! Signs and oriented top forms, paper.tex d04:07:orientation.
The diffeomorphism is on its actual open source and target. Integration uses
exactly the shared normalized volume covector, its pullback, and the Riemann
integrals of zero extensions. A sign is selected only on the domain where it
is proved constant; no connectedness of the whole source is implicit. -/
noncomputable section
open Set
namespace Specs.D04.C07.Orientation
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C13.PullbackCalculus.Model

def determinant_regularType : Prop :=
  ∀ {n : ℕ} (e : OpenPartialHomeomorph (E n) (E n)),
    ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
    ContinuousOn (fun x => (fderiv ℝ e x).det) e.source ∧
      ∀ x ∈ e.source, (fderiv ℝ e x).det ≠ 0

def component_signType : Prop :=
  ∀ {n : ℕ} (e : OpenPartialHomeomorph (E n) (E n)),
    ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
    ∀ a ∈ e.source,
      (Real.sign ((fderiv ℝ e a).det) = 1 ∨ Real.sign ((fderiv ℝ e a).det) = -1) ∧
      (∀ x ∈ connectedComponentIn e.source a,
        Real.sign ((fderiv ℝ e x).det) = Real.sign ((fderiv ℝ e a).det)) ∧
      ((∀ x ∈ connectedComponentIn e.source a, 0 < (fderiv ℝ e x).det) ∨
       (∀ x ∈ connectedComponentIn e.source a, (fderiv ℝ e x).det < 0))

def pullback_topType : Prop :=
  ∀ {n : ℕ} (φ : E n → E n) (f : E n → ℝ) (x : E n),
    pullback φ (fun y => f y • volumeForm n) x =
      (f (φ x) * (fderiv ℝ φ x).det) • volumeForm n

/-- σ = +1 is preservation, σ = -1 reversal. The integrand g is the
coefficient of the actual shared pullback, evaluated on the ordered basis. -/
def signed_open_substitutionType : Prop :=
  ∀ {n : ℕ} (e : OpenPartialHomeomorph (E n) (E n)),
    ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
    ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
    (∀ x ∈ e.source, Real.sign ((fderiv ℝ e x).det) = σ) →
    ∀ f : e.target → ℝ, RegionBounded f → HasCompactSupport f →
      let g : e.source → ℝ := fun x =>
        pullback e (fun y => zeroExtension f y • volumeForm n) x (standardBasis n)
      RegionBounded g ∧ HasCompactSupport g ∧
        (OpenIntegrable f ↔ OpenIntegrable g) ∧
        ((OpenIntegrable f ∨ OpenIntegrable g) → openIntegral g = σ * openIntegral f)

/-- On a disconnected source, integrate on each actual component and its
image, with the sign derived at any point of that component. -/
def component_open_substitutionType : Prop :=
  ∀ {n : ℕ} (e : OpenPartialHomeomorph (E n) (E n)),
    ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
    ∀ a ∈ e.source,
      let C := connectedComponentIn e.source a
      ∀ f : (e '' C) → ℝ, RegionBounded f → HasCompactSupport f →
        let g : C → ℝ := fun x =>
          pullback e (fun y => zeroExtension f y • volumeForm n) x (standardBasis n)
        RegionBounded g ∧ HasCompactSupport g ∧
          (OpenIntegrable f ↔ OpenIntegrable g) ∧
          ((OpenIntegrable f ∨ OpenIntegrable g) →
            openIntegral g = Real.sign ((fderiv ℝ e a).det) * openIntegral f)

def signed_region_substitutionType : Prop :=
  ∀ {n : ℕ} (e : OpenPartialHomeomorph (E n) (E n)),
    ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
    ∀ S : Set (E n), Jordan S → IsCompact (closure S) → closure S ⊆ e.source →
    ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
    (∀ x ∈ S, Real.sign ((fderiv ℝ e x).det) = σ) →
    ∀ f : (e '' S) → ℝ, RegionBounded f →
      let g : S → ℝ := fun x =>
        pullback e (fun y => zeroExtension f y • volumeForm n) x (standardBasis n)
      RegionBounded g ∧ (RegionIntegrable f ↔ RegionIntegrable g) ∧
        ((RegionIntegrable f ∨ RegionIntegrable g) → regionIntegral g = σ * regionIntegral f)

def component_region_substitutionType : Prop :=
  ∀ {n : ℕ} (e : OpenPartialHomeomorph (E n) (E n)),
    ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
    ∀ a ∈ e.source, ∀ S : Set (E n),
    Jordan S → IsCompact (closure S) → closure S ⊆ e.source →
    S ⊆ connectedComponentIn e.source a →
    ∀ f : (e '' S) → ℝ, RegionBounded f →
      let g : S → ℝ := fun x =>
        pullback e (fun y => zeroExtension f y • volumeForm n) x (standardBasis n)
      RegionBounded g ∧ (RegionIntegrable f ↔ RegionIntegrable g) ∧
        ((RegionIntegrable f ∨ RegionIntegrable g) →
          regionIntegral g = Real.sign ((fderiv ℝ e a).det) * regionIntegral f)

/-- The positive density theorem retains the absolute determinant. -/
def positive_densityType : Prop :=
  ∀ {n : ℕ} (e : OpenPartialHomeomorph (E n) (E n)),
    ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
    ∀ S : Set (E n), Jordan S → IsCompact (closure S) → closure S ⊆ e.source →
      RegionIntegrable (fun x : S => |(fderiv ℝ e x).det|) ∧
        volume (e '' S) = regionIntegral (fun x : S => |(fderiv ℝ e x).det|)

def zero_dimensionType : Prop :=
  ∀ (φ : E 0 → E 0) (x : E 0), (fderiv ℝ φ x).det = 1 ∧
    ∀ f : E 0 → ℝ,
      pullback φ (fun y => f y • volumeForm 0) x (standardBasis 0) = f (φ x)

end Specs.D04.C07.Orientation
