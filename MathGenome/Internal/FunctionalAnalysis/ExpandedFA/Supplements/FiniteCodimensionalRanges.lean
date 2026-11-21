import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.FiniteCodimensionalRanges
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Supplements.NonmeagreImage
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C08OpenMapping
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.DiscontinuousAlgebraicFunctional
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Isomorphisms

/-!
The finite-codimension argument uses an algebraic complement `Y` of `T.range`.
It is finite dimensional, hence complete in the inherited norm. The map
`A : E × Y → F`, `(x,y) ↦ T x + y`, is a continuous linear surjection between
Banach spaces and therefore a quotient map. Its preimage of `T.range` is
exactly `E × {0}`, a closed set. This proves closedness without assuming any
topological property of the original algebraic quotient.

For the qualification, the accepted Hamel-basis construction gives an
unbounded algebraic functional. A scalar-linear functional with closed
kernel is continuous; its nonzero range is the scalar field, so its
algebraic kernel quotient has dimension one.
-/

namespace ExpandedFA.Supplements.FiniteCodimensionalRanges

open Function Set

theorem nonmeagre_range : Spec.NonmeagreRange := by
  exact NonmeagreImage.nonmeagre_image

theorem finite_codimensional_range_closed : Spec.FiniteCodimensionalRangeClosed := by
  intro 𝕜 E F _ _ _ _ _ _ _ T hfinite
  classical
  let _ := hfinite
  obtain ⟨Y, hY⟩ := T.range.exists_isCompl
  let _ : FiniteDimensional 𝕜 Y := (T.range.quotientEquivOfIsCompl Y hY).finiteDimensional
  let _ : CompleteSpace Y := FiniteDimensional.complete 𝕜 Y
  let A : E × Y →L[𝕜] F := T.coprod Y.subtypeL
  have hsurj : Surjective A := by
    intro z
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp
      (show z ∈ T.range ⊔ Y from hY.sup_eq_top.symm ▸ Submodule.mem_top)
    obtain ⟨x, hx⟩ := ha
    change T x = a at hx
    exact ⟨(x, ⟨b, hb⟩), by change T x + b = z; rw [hx, hab]⟩
  have hopen : IsOpenMap A := P1.C08OpenMapping.open_mapping 𝕜 (E × Y) F A hsurj
  have hquot := hopen.isQuotientMap A.continuous hsurj
  have hpre : A ⁻¹' (T.range : Set F) = {p : E × Y | p.2 = 0} := by
    ext p
    change T p.1 + (p.2 : F) ∈ T.range ↔ p.2 = 0
    have ht : T p.1 ∈ T.range := ⟨p.1, rfl⟩
    constructor
    · intro hp
      have hb : (p.2 : F) ∈ T.range := by
        have := T.range.sub_mem hp ht
        simpa only [add_sub_cancel_left] using this
      apply Subtype.ext
      exact Submodule.disjoint_def.mp hY.disjoint _ hb p.2.property
    · intro hp
      simpa only [hp, Submodule.coe_zero, add_zero] using ht
  apply hquot.isCoinducing.isClosed_preimage.mp
  rw [hpre]
  exact isClosed_singleton.preimage continuous_snd

theorem nonclosed_hyperplane : Spec.NonclosedHyperplane := by
  intro 𝕜 E _ _ _ _ hE
  obtain ⟨u, B, b, f, _, _, _, _, hf, _, _, hunbounded, hdisc, _⟩ :=
    P1.DiscontinuousAlgebraicFunctional.discontinuous_algebraic_functional 𝕜 E hE
  have hsurj : Surjective f := by
    intro a
    refine ⟨a • u 1, ?_⟩
    simp [hf]
  let e : (E ⧸ f.ker) ≃ₗ[𝕜] 𝕜 := f.quotKerEquivOfSurjective hsurj
  have hfinite : FiniteDimensional 𝕜 (E ⧸ f.ker) := e.symm.finiteDimensional
  refine ⟨f, hunbounded, hdisc, hfinite, ?_, ?_⟩
  · exact e.finrank_eq.trans (Module.finrank_self 𝕜)
  · exact fun hclosed => hdisc (f.continuous_of_isClosed_ker hclosed)

end ExpandedFA.Supplements.FiniteCodimensionalRanges
