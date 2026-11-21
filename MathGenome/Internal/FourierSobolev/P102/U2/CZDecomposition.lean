import MathGenome.Internal.FourierSobolev.Specs.P102.U2.CZDecomposition
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SingularIntegrals.CalderonZygmundDecomposition

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace P102.U2.CZDecomposition
open ExpandedFA.SingularIntegrals
open ExpandedFA.SingularIntegrals.CZ

/-- The concrete dyadic geometry is proved in the pinned library. -/
theorem cube_geometry : Specs.P102.U2.CZDecomposition.cube_geometry :=
  ⟨calderonZygmund_cube_geometry, calderonZygmund_cube_grid⟩

theorem average_formula : Specs.P102.U2.CZDecomposition.average_formula := by
  intro d 𝕜 _ f q
  exact setAverage_eq volume f (cube q)

/-- Transfer the constructed selection and analytical conclusions to the full
source statement, retaining normalized bounds and the pointwise identity. -/
lemma conclusion_of_selection {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : Point d → 𝕜) (t : ℝ) (Q : Set (DyadicCube d)) (g : Point d → 𝕜)
    (hs : Selection f t Q) (hg : Decomposition f t Q g) :
    Specs.P102.U2.CZDecomposition.Conclusion f t Q g := by
  have hgood : g = goodPart f Q := by
    funext x
    by_cases hx : x ∈ badRegion Q
    · obtain ⟨q, hq⟩ := mem_iUnion.mp hx
      exact (hg.good_inside q.1 q.2 x hq).trans
        (goodPart_inside f Q hs.disjoint q x hq).symm
    · exact (hg.good_outside x hx).trans (goodPart_outside f Q x hx).symm
  refine ⟨Set.to_countable Q, hg.disjoint, ?_, hg.measure_bound,
    hg.good_outside, hg.good_inside, ?_, hg.good_integrable,
    hg.good_infinity, hg.good_one, ?_, hg.bad_one_bound, hg.series_one, hg.series_two⟩
  · intro q hq
    have hv : 0 < volume.real (cube q) :=
      ENNReal.toReal_pos (hs.positive q hq).ne' (hs.finite q hq).ne
    constructor
    · exact (lt_inv_mul_iff₀ hv).mpr (by simpa [mul_comm] using hs.lower q hq)
    · exact (inv_mul_le_iff₀ hv).mpr (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using (hs.upper q hq))
  · intro x
    rw [hgood]
    simp only [goodPart]
    exact (sub_add_cancel (f x) _).symm
  · intro q
    exact ⟨hg.bad_integrable q, hg.bad_mean q, hg.bad_support q⟩

/-- Maximal selection is constructed from integrability; it is not an input
certificate. Its exterior estimate uses proved differentiation of averages. -/
theorem decomposition : Specs.P102.U2.CZDecomposition.decomposition := by
  intro d hd 𝕜 _ f hf t ht
  obtain ⟨Q, hs⟩ := calderonZygmund_maximal_selection d hd f hf t ht
  obtain ⟨g, hg⟩ := calderonZygmund_assemble_selection d f hf t ht Q hs
  exact ⟨Q, g, conclusion_of_selection f t Q g hs hg⟩

theorem empty_family : Specs.P102.U2.CZDecomposition.empty_family := by
  intro d hd 𝕜 _ f hf t ht hbound
  have hs : Selection f t ∅ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · filter_upwards [hbound] with x hx using fun _ => hx
  obtain ⟨g, hg⟩ := calderonZygmund_assemble_selection d f hf t ht ∅ hs
  have hgf : g = f := by
    funext x
    exact hg.good_outside x (by simp [badRegion])
  subst g
  exact conclusion_of_selection f t ∅ f hs hg

end P102.U2.CZDecomposition
