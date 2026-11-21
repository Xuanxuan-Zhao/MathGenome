import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.RotundDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14UniformConvexity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12DualPair
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Rotundity, local uniform convexity, the convexity modulus, and the
Radon–Riesz property, paper.tex:4613–4628. -/
namespace ExpandedFA.P1.RotundDefinitions
universe u v
noncomputable section

def Rotund : Spec.PredicateType.{u,v} := Spec.RotundValue

def LocallyUniformlyConvexAt : Spec.PointPredicateType.{u,v} := Spec.LocallyUniformlyConvexAtValue

def LocallyUniformlyConvex : Spec.PredicateType.{u,v} := Spec.LocallyUniformlyConvexValue

def convexityDeficits : Spec.DeficitsType.{u,v} := Spec.DeficitsValue

def modulusConvexity : Spec.ModulusType.{u,v} := Spec.ModulusValue

def RadonRiesz : Spec.PredicateType.{u,v} := Spec.RadonRieszValue

variable (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Every deficit is nonnegative by the triangle inequality. -/
lemma convexityDeficits_bddBelow (ε : ℝ) : BddBelow (convexityDeficits 𝕜 E ε) := by
  refine ⟨0, ?_⟩
  rintro d ⟨x, y, hx, hy, _, rfl⟩
  have h := norm_add_le x y
  rw [C14UniformConvexity.norm_midpoint_eq_half]
  linarith

/-- Antipodal unit vectors give an admissible pair for every ε ≤ 2. -/
lemma convexityDeficits_nonempty [Nontrivial E] {ε : ℝ} (hε : ε ≤ 2) :
    (convexityDeficits 𝕜 E ε).Nonempty := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  obtain ⟨x, hx⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
  refine ⟨1 - ‖(2 : 𝕜)⁻¹ • (x + -x)‖, x, -x, hx.le, ?_, ?_, rfl⟩
  · simpa using hx.le
  · have heq : x - -x = (2 : ℝ) • x := by simp [two_smul]
    rw [heq, norm_smul, hx]
    norm_num
    exact hε

@[simp] theorem modulusConvexity_zero : modulusConvexity 𝕜 E 0 = 0 := by
  simp [modulusConvexity, Spec.ModulusValue]

theorem modulusConvexity_of_subsingleton [Subsingleton E] (ε : ℝ) (hε : 0 < ε) :
    modulusConvexity 𝕜 E ε = 1 := by
  have hempty : ¬ (convexityDeficits 𝕜 E ε).Nonempty := by
    rintro ⟨d, x, y, _, _, hxy, _⟩
    have heq : x = y := Subsingleton.elim _ _
    simp [heq] at hxy
    linarith
  simp only [modulusConvexity, Spec.ModulusValue, ne_of_gt hε, ↓reduceIte]
  exact ite_eq_right hempty

theorem modulusConvexity_eq_inf [Nontrivial E] (ε : ℝ) (hε : 0 < ε) (hε₂ : ε ≤ 2) :
    modulusConvexity 𝕜 E ε = sInf (convexityDeficits 𝕜 E ε) := by
  simp only [modulusConvexity, Spec.ModulusValue, ne_of_gt hε, ↓reduceIte]
  exact ite_eq_left (convexityDeficits_nonempty 𝕜 E hε₂)

/-- The infimum formulation and the previously accepted predicate agree,
including when the separated pairs do not exist. -/
theorem uniformlyConvex_iff_modulus_pos :
    C14UniformConvexity.UniformlyConvex 𝕜 E ↔
      ∀ ε : ℝ, 0 < ε → ε ≤ 2 → 0 < modulusConvexity 𝕜 E ε := by
  constructor
  · intro h ε hε hε₂
    obtain ⟨δ, hδ, hxy⟩ := h ε hε hε₂
    by_cases hn : (convexityDeficits 𝕜 E ε).Nonempty
    · have hle : δ ≤ sInf (convexityDeficits 𝕜 E ε) := by
        apply le_csInf hn
        rintro d ⟨x, y, hx, hy, hsep, rfl⟩
        have := hxy x y hx hy hsep
        linarith
      have heq : modulusConvexity 𝕜 E ε = sInf (convexityDeficits 𝕜 E ε) := by
        simp only [modulusConvexity, Spec.ModulusValue, ne_of_gt hε, ↓reduceIte]
        exact ite_eq_left hn
      rw [heq]
      exact hδ.trans_le hle
    · have heq : modulusConvexity 𝕜 E ε = 1 := by
        simp only [modulusConvexity, Spec.ModulusValue, ne_of_gt hε, ↓reduceIte]
        exact ite_eq_right hn
      rw [heq]
      norm_num
  · intro h ε hε hε₂
    refine ⟨modulusConvexity 𝕜 E ε, h ε hε hε₂, ?_⟩
    intro x y hx hy hsep
    have hmem : 1 - ‖(2 : 𝕜)⁻¹ • (x + y)‖ ∈ convexityDeficits 𝕜 E ε :=
      ⟨x, y, hx, hy, hsep, rfl⟩
    have hn : (convexityDeficits 𝕜 E ε).Nonempty := ⟨_, hmem⟩
    have heq : modulusConvexity 𝕜 E ε = sInf (convexityDeficits 𝕜 E ε) := by
      simp only [modulusConvexity, Spec.ModulusValue, ne_of_gt hε, ↓reduceIte]
      exact ite_eq_left hn
    have hle := csInf_le (convexityDeficits_bddBelow 𝕜 E ε) hmem
    rw [← heq] at hle
    linarith

theorem rotund_iff_strictConvexSpace :
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    Rotund 𝕜 E ↔ StrictConvexSpace ℝ E := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  constructor
  · intro h
    apply StrictConvexSpace.of_norm_add_ne_two
    intro x y hx hy hne heq
    have hm := h x y hx hy hne
    rw [C14UniformConvexity.norm_midpoint_eq_half, heq] at hm
    norm_num at hm
  · intro h
    let : StrictConvexSpace ℝ E := h
    intro x y hx hy hne
    have hlt : ‖x + y‖ < 2 := by
      have hle : ‖x + y‖ ≤ 2 := by have := norm_add_le x y; linarith
      refine lt_of_le_of_ne hle ?_
      intro heq
      exact hne (eq_of_norm_eq_of_norm_add_eq (hx.trans hy.symm) (by linarith))
    rw [C14UniformConvexity.norm_midpoint_eq_half]
    linarith

end
end ExpandedFA.P1.RotundDefinitions
