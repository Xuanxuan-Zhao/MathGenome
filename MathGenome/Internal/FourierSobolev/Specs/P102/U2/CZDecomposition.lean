import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.CalderonZygmundDecomposition

/-! Theorem p102:U2-02, paper.tex:935–951.

We reuse the library's concrete Euclidean dyadic cubes, their averages and
bad pieces. `DyadicCube d = ℤ × (Fin d → ℤ)` encodes
`∏ i, [2^k mᵢ, 2^k (mᵢ+1))`. There is no abstract grid or selection
certificate in the hypotheses of the decomposition theorem.

Here `volume` is native Euclidean Lebesgue measure. `Integrable` and `MemLp`
use a.e. strong measurability, so the input includes arbitrary Lebesgue
measurable representatives, not just Borel measurable functions. Conclusions
about Lp use the usual a.e. quotient; `BadSeries` means `HasSum` in that Lp
space, with sum the class of `f - g`. The family is a subset of a countable
cube type, so empty and finite families need no padding or repeated cubes. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Specs.P102.U2.CZDecomposition
open ExpandedFA.SingularIntegrals.CZ

/-- All conclusions for the *same* cube family and good representative.
The pointwise identity is stronger than the source's a.e. identity. -/
def Conclusion {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : Point d → 𝕜) (t : ℝ) (Q : Set (DyadicCube d))
    (g : Point d → 𝕜) : Prop :=
  Q.Countable ∧
  Q.PairwiseDisjoint cube ∧
  (∀ q ∈ Q, t < (volume.real (cube q))⁻¹ * (∫ x in cube q, ‖f x‖) ∧
    (volume.real (cube q))⁻¹ * (∫ x in cube q, ‖f x‖) ≤ (2 : ℝ)^d * t) ∧
  ((∑' q : Q, volume (cube q.1)) ≤ eLpNorm f 1 volume / ENNReal.ofReal t) ∧
  (∀ x, x ∉ badRegion Q → g x = f x) ∧
  (∀ q ∈ Q, ∀ x ∈ cube q, g x = cubeAverage f q) ∧
  (∀ x, f x = g x + ∑' q : Q, badPiece f q.1 x) ∧
  Integrable g volume ∧
  (eLpNorm g ∞ volume ≤ ENNReal.ofReal ((2 : ℝ)^d * t)) ∧
  (eLpNorm g 1 volume ≤ eLpNorm f 1 volume) ∧
  (∀ q : Q, Integrable (badPiece f q.1) volume ∧
    (∫ x, badPiece f q.1 x) = 0 ∧
    Function.support (badPiece f q.1) ⊆ cube q.1) ∧
  ((∑' q : Q, eLpNorm (badPiece f q.1) 1 volume) ≤ 2 * eLpNorm f 1 volume) ∧
  BadSeries f g Q 1 ∧
  (MemLp f 2 volume → BadSeries f g Q 2)

/-- No global L² hypothesis is imposed on the L¹ decomposition. -/
def decomposition : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ {𝕜 : Type} [RCLike 𝕜]
    (f : Point d → 𝕜), Integrable f volume → ∀ t : ℝ, 0 < t →
      ∃ (Q : Set (DyadicCube d)) (g : Point d → 𝕜), Conclusion f t Q g

/-- Actual half-open grid geometry: volume, parent, nesting and grid cover. -/
def cube_geometry : Prop :=
  ExpandedFA.SingularIntegrals.CalderonZygmundDecompositionSpec.CubeGeometry ∧
  ExpandedFA.SingularIntegrals.CalderonZygmundDecompositionSpec.CubeGrid

/-- The canonical average is the source's normalized Bochner integral. -/
def average_formula : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (f : Point d → 𝕜) (q : DyadicCube d),
    cubeAverage f q = (volume.real (cube q))⁻¹ • ∫ x in cube q, f x

/-- If no bad set is needed, the empty family and the original representative
satisfy the full conclusion. In particular this includes the zero function. -/
def empty_family : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ {𝕜 : Type} [RCLike 𝕜]
    (f : Point d → 𝕜), Integrable f volume → ∀ t : ℝ, 0 < t →
      (∀ᵐ x ∂volume, ‖f x‖ ≤ t) → Conclusion f t ∅ f

end Specs.P102.U2.CZDecomposition
