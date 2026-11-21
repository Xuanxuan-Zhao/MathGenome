import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.RiemannSubstitution
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.NullPreservation

/-! Bounded-region substitution, paper.tex `d04:07:regions`.
A C¹ diffeomorphism is an open partial homeomorphism with C¹ forward and
inverse maps on its actual source and target. The bounded region has compact
ambient closure contained in the source. All integrals below are the shared
Riemann integrals of actual zero extensions, including the evaluation
convention in dimension zero. No regularity of the bounded integrand is assumed.
-/
noncomputable section
open Set
namespace Specs.D04.C07.RegionSubstitution
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C06.JordanRegions.Model

/-- Compact containment is retained even though the input region is Jordan. -/
def jordan_imageType : Prop :=
  ∀ {n : ℕ} (e : OpenPartialHomeomorph (E n) (E n)),
    ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
    ∀ S : Set (E n), Jordan S → IsCompact (closure S) → closure S ⊆ e.source →
      Bornology.IsBounded (e '' S) ∧ Jordan (e '' S)

/-- Existence in either direction and the equality, with no assumed integral. -/
def region_substitutionType : Prop :=
  ∀ {n : ℕ} (e : OpenPartialHomeomorph (E n) (E n)),
    ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
    ∀ S : Set (E n), Jordan S → IsCompact (closure S) → closure S ⊆ e.source →
    ∀ f : (e '' S) → ℝ, RegionBounded f →
      let g : S → ℝ := fun x =>
        f ⟨e x, mem_image_of_mem e x.property⟩ * |(fderiv ℝ e x).det|
      RegionBounded g ∧ (RegionIntegrable f ↔ RegionIntegrable g) ∧
        ((RegionIntegrable f ∨ RegionIntegrable g) → regionIntegral f = regionIntegral g)

def volume_substitutionType : Prop :=
  ∀ {n : ℕ} (e : OpenPartialHomeomorph (E n) (E n)),
    ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
    ∀ S : Set (E n), Jordan S → IsCompact (closure S) → closure S ⊆ e.source →
      RegionIntegrable (fun x : S => |(fderiv ℝ e x).det|) ∧
        volume (e '' S) = regionIntegral (fun x : S => |(fderiv ℝ e x).det|)

/-- Coordinatewise finite-dimensional extension, with zero target dimension allowed. -/
def vector_region_substitutionType : Prop :=
  ∀ {n : ℕ} (e : OpenPartialHomeomorph (E n) (E n)),
    ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
    ∀ S : Set (E n), Jordan S → IsCompact (closure S) → closure S ⊆ e.source →
    ∀ (k : ℕ) (f : (e '' S) → E k), RegionBounded f →
      let g : S → E k := fun x =>
        |(fderiv ℝ e x).det| • f ⟨e x, mem_image_of_mem e x.property⟩
      RegionBounded g ∧ (VectorRegionIntegrable f ↔ VectorRegionIntegrable g) ∧
        ((VectorRegionIntegrable f ∨ VectorRegionIntegrable g) →
          vectorRegionIntegral f = vectorRegionIntegral g)

end Specs.D04.C07.RegionSubstitution
