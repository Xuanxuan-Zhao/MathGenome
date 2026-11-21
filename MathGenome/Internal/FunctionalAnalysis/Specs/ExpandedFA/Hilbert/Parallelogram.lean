import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Conventions
import Mathlib.Analysis.InnerProductSpace.OfNorm

/-!
Independent specification of `fa2:p2:parallelogram`, paper.tex 7606–7622.
The normed space is not assumed complete or nonzero. `RCLike` includes both
the real and complex fields. Compatibility below preserves the entire given
normed scalar action; the normed additive group is a fixed parameter throughout.
-/

noncomputable section
open scoped InnerProductSpace ComplexConjugate

namespace ExpandedFA.Hilbert.Parallelogram
universe u v

/-- The identity in the manuscript, for every pair of vectors. -/
def ParallelogramLaw (E : Type v) [NormedAddCommGroup E] : Prop :=
  ∀ x y : E, ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2

namespace Spec

/-- Construct an inner product on the original normed vector space, with no
completeness hypothesis and no change of scalar multiplication. -/
def InnerProductSpaceOfParallelogramType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [n : NormedSpace 𝕜 E],
    ParallelogramLaw E → {p : InnerProductSpace 𝕜 E // p.toNormedSpace = n}

/-- The native Jordan–von Neumann polarization construction. Its formula is
conjugate linear in the first slot and linear in the second, over both fields. -/
def InnerProductSpaceOfParallelogramValue :
    InnerProductSpaceOfParallelogramType.{u, v} :=
  fun 𝕜 E _ _ _ h =>
    ⟨InnerProductSpace.ofNorm (𝕜 := 𝕜) (E := E)
      (fun x y => by simpa only [pow_two, mul_add] using h x y), rfl⟩

/-- Having an inner product inducing this norm and respecting the original
scalar action is equivalent to the parallelogram identity. -/
def Characterization : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [n : NormedSpace 𝕜 E],
    (∃ p : InnerProductSpace 𝕜 E, p.toNormedSpace = n) ↔ ParallelogramLaw E

/-- The constructed product induces the given norm and has exactly the
manuscript's conjugate-first convention. All operations here belong to the
constructed structure, whose normed scalar action is certified above. -/
def ConstructedInnerProperties : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (h : ParallelogramLaw E),
    letI := (InnerProductSpaceOfParallelogramValue 𝕜 E h).val
    (∀ x : E, ‖x‖ ^ 2 = RCLike.re ⟪x, x⟫_𝕜) ∧
    (∀ (c : 𝕜) (x y : E),
      ⟪c • x, y⟫_𝕜 = conj c * ⟪x, y⟫_𝕜 ∧
      ⟪x, c • y⟫_𝕜 = c * ⟪x, y⟫_𝕜 ∧
      conj ⟪y, x⟫_𝕜 = ⟪x, y⟫_𝕜)

end Spec
end ExpandedFA.Hilbert.Parallelogram
