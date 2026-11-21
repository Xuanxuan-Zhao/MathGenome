import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Space
import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.LipschitzGeometry

/-! Independent specification of the extension clause of paper.tex:2322–2358.
Positive dimensions are indexed by `n + 1`, including dimension one (`n = 0`).
The geometric upstream uses the Euclidean L² product of tangential space and ℝ;
`geometryCoordinates` identifies it isometrically with the canonical coordinate
space used for the Gagliardo spaces. No connectedness hypothesis is imposed.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal Topology

namespace P102.Fractional

/-- A fixed orthonormal coordinate identification, independent of the domain,
exponents and function. Both sides carry their Euclidean norms. -/
def geometryCoordinates (n : ℕ) :
    P102.U4.GraphPieces.Ambient n ≃ₗᵢ[ℝ] Domain (n + 1) :=
  (stdOrthonormalBasis ℝ (P102.U4.GraphPieces.Ambient n)).repr.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (by
      rw [(WithLp.linearEquiv 2 ℝ (P102.U4.Space n × ℝ)).finrank_eq]
      simp [P102.U4.Space, Module.finrank_prod])))

/-- The source's bounded, locally one-sided Lipschitz graph condition in the
canonical coordinate model. The isometric coordinate change is fixed, rather
than an extra regularity or analytic hypothesis on the open set. -/
def IsBoundedLipschitzOpen {n : ℕ} (G : Set (Domain (n + 1))) : Prop :=
  P102.Sobolev.Geometry.IsLipschitzOpen (geometryCoordinates n ⁻¹' G)

end P102.Fractional

namespace Specs.P102.Fractional.Extension
open _root_.P102.Fractional
universe u

/-- A continuous scalar-linear extension, restricting to the original a.e.
class, bounded by the full source norm. A single compact set contains the
essential supports of all outputs; it is chosen before the input function.
The compact formulation implies the manuscript's fixed bounded support set.
The statement covers real and complex scalars, finite p including p = 1,
disconnected sets, the empty set, and every positive coordinate dimension. -/
def extension : Prop :=
  ∀ (n : ℕ) (G : Set (Domain (n + 1))), IsBoundedLipschitzOpen G →
  ∀ (s : ℝ), 0 < s → s < 1 →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  ∀ (𝕜 : Type u) [RCLike 𝕜],
  ∃ (K : Set (Domain (n + 1))), IsCompact K ∧
  ∃ (C : ℝ≥0) (E : Space 𝕜 G s p →L[𝕜] Space 𝕜 Set.univ s p),
    (∀ u, (firstProjection (E u) : Domain (n + 1) → 𝕜)
      =ᵐ[domainMeasure G] firstProjection u) ∧
    (∀ u, ∀ᵐ x ∂volume, x ∉ K → firstProjection (E u) x = 0) ∧
    (∀ u, ‖E u‖ ≤ (C : ℝ) *
      (‖firstProjection u‖ + (seminorm G s p (firstProjection u)).toReal))

end Specs.P102.Fractional.Extension
