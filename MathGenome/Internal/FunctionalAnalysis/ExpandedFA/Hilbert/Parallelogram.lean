import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Parallelogram
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Conventions

/-!
The parallelogram characterization on arbitrary real or complex normed spaces.
Mathlib's Jordan–von Neumann construction uses polarization and continuity of
the norm, not completeness of the space. Its native norm compatibility and
the equality of normed scalar actions keep the original normed vector space.
-/

noncomputable section
open scoped InnerProductSpace ComplexConjugate

namespace ExpandedFA.Hilbert.Parallelogram
universe u v

/-- The polarization construction, valid over ℝ and ℂ and on incomplete spaces. -/
def innerProductSpaceOfParallelogram :
    Spec.InnerProductSpaceOfParallelogramType.{u, v} :=
  fun 𝕜 E _ _ _ h =>
    ⟨InnerProductSpace.ofNorm (𝕜 := 𝕜) (E := E)
      (fun x y => by simpa only [pow_two, mul_add] using h x y), rfl⟩

theorem parallelogram_characterization : Spec.Characterization.{u, v} := by
  intro 𝕜 E _ _ _
  constructor
  · rintro ⟨p, _⟩
    letI := p
    intro x y
    simpa only [mul_add] using parallelogram_law_with_norm 𝕜 x y
  · intro h
    exact ⟨(innerProductSpaceOfParallelogram 𝕜 E h).val,
      (innerProductSpaceOfParallelogram 𝕜 E h).property⟩

theorem constructed_inner_properties : Spec.ConstructedInnerProperties.{u, v} := by
  intro 𝕜 E _ _ _ h
  letI := (Spec.InnerProductSpaceOfParallelogramValue 𝕜 E h).val
  exact ⟨norm_sq_eq_re_inner, Conventions.inner_convention 𝕜 E⟩

end ExpandedFA.Hilbert.Parallelogram
