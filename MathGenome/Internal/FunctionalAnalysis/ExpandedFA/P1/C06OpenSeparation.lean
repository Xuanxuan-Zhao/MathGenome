import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06OpenSeparation
import Mathlib.Analysis.LocallyConvex.Separation

/-! Open convex separation (`fa2:p1:c06:open-separation`, paper.tex:1083–1127).

Mathlib's `geometric_hahn_banach_open` uses precisely convexity, disjointness,
and openness of the first set in a real topological vector space. In particular,
it needs neither Hausdorffness, completeness, nor local convexity. Its conclusion
has the required strictness on the open side. Nonemptiness of both sets forces
the separating functional to be nonzero. The complex extension below uses
`h(x) - i h(i x)` and retains its real part at every point.
-/
namespace ExpandedFA.P1.C06
universe u

/-- Separation with strict inequality on the open side. This holds even without
local convexity, and so includes the locally convex spaces of the manuscript. -/
theorem real_open_convex_separation
    {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (A B : Set E) (hA : A.Nonempty) (hB : B.Nonempty)
    (hcA : Convex ℝ A) (hcB : Convex ℝ B) (hd : Disjoint A B) (ho : IsOpen A) :
    ∃ (h : E →L[ℝ] ℝ) (α : ℝ), h ≠ 0 ∧
      (∀ a ∈ A, h a < α) ∧ (∀ b ∈ B, α ≤ h b) := by
  obtain ⟨h, α, ha, hb⟩ := geometric_hahn_banach_open hcA ho hcB hd
  refine ⟨h, α, ?_, ha, hb⟩
  intro hz
  obtain ⟨a, haA⟩ := hA
  obtain ⟨b, hbB⟩ := hB
  have hab := (ha a haA).trans_le (hb b hbB)
  simp only [hz, zero_apply, lt_self_iff_false] at hab

/-- A complex separator together with the nonzero real separator equal to its
real part; the topology need not be Hausdorff or locally convex. -/
theorem complex_open_convex_separation
    {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (A B : Set E) (hA : A.Nonempty) (hB : B.Nonempty)
    (hcA : Convex ℝ A) (hcB : Convex ℝ B) (hd : Disjoint A B) (ho : IsOpen A) :
    ∃ (h : E →L[ℝ] ℝ) (f : E →L[ℂ] ℂ) (α : ℝ),
      h ≠ 0 ∧ f ≠ 0 ∧ (∀ x, h x = (f x).re) ∧
      (∀ a ∈ A, h a < α) ∧ (∀ b ∈ B, α ≤ h b) := by
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  obtain ⟨h, α, hn, ha, hb⟩ := real_open_convex_separation A B hA hB hcA hcB hd ho
  let f : E →L[ℂ] ℂ := StrongDual.extendRCLike h
  have hre : ∀ x, h x = (f x).re := by
    intro x
    exact (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) h x).symm
  refine ⟨h, f, α, hn, ?_, hre, ha, hb⟩
  intro hz
  apply hn
  ext x
  simpa only [hz, zero_apply, Complex.zero_re] using hre x

/-- Real normed spaces need not be complete. -/
theorem real_normed_open_convex_separation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : Set E) (hA : A.Nonempty) (hB : B.Nonempty)
    (hcA : Convex ℝ A) (hcB : Convex ℝ B) (hd : Disjoint A B) (ho : IsOpen A) :
    ∃ (h : E →L[ℝ] ℝ) (α : ℝ), h ≠ 0 ∧
      (∀ a ∈ A, h a < α) ∧ (∀ b ∈ B, α ≤ h b) :=
  real_open_convex_separation A B hA hB hcA hcB hd ho

/-- Complex normed spaces need not be complete. -/
theorem complex_normed_open_convex_separation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : Set E) (hA : A.Nonempty) (hB : B.Nonempty)
    (hcA : Convex ℝ A) (hcB : Convex ℝ B) (hd : Disjoint A B) (ho : IsOpen A) :
    ∃ (h : E →L[ℝ] ℝ) (f : E →L[ℂ] ℂ) (α : ℝ),
      h ≠ 0 ∧ f ≠ 0 ∧ (∀ x, h x = (f x).re) ∧
      (∀ a ∈ A, h a < α) ∧ (∀ b ∈ B, α ≤ h b) :=
  complex_open_convex_separation A B hA hB hcA hcB hd ho

end ExpandedFA.P1.C06
