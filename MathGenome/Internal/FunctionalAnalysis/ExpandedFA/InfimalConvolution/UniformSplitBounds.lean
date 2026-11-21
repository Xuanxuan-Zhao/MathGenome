import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.InfimalConvolution.UniformSplitBounds
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.InfimalConvolution.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07UniformBoundedness

namespace ExpandedFA.InfimalConvolution.UniformSplitBounds

open ExpandedFA.P1
open ExtendedConvexFunctions
open Definitions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Add the two finite-point tests in the defining conjugate suprema. -/
lemma split_evaluation_le (φ ψ : ExtendedFunction E) (f g : E →L[ℝ] ℝ)
    (x y : E) (r s α : ℝ) (hx : φ x = (r : WithTop ℝ))
    (hy : ψ y = (s : WithTop ℝ))
    (hcost : conjugateSplitCost E φ ψ f g ≤ (α : EReal)) :
    g (y - x) ≤ α + r + s - f x := by
  have hφ : (((f - g) x - r : ℝ) : EReal) ≤
      C06Conjugates.convexConjugate E φ (f - g) := by
    calc
      (((f - g) x - r : ℝ) : EReal) = (((f - g) x : ℝ) : EReal) -
          C06Conjugates.extendedRealValue (φ x) := by rw [hx]; rfl
      _ ≤ C06Conjugates.convexConjugate E φ (f - g) :=
        le_iSup (fun z : E => (((f - g) z : ℝ) : EReal) -
          C06Conjugates.extendedRealValue (φ z)) x
  have hψ : ((g y - s : ℝ) : EReal) ≤
      C06Conjugates.convexConjugate E ψ g := by
    calc
      ((g y - s : ℝ) : EReal) = ((g y : ℝ) : EReal) -
          C06Conjugates.extendedRealValue (ψ y) := by rw [hy]; rfl
      _ ≤ C06Conjugates.convexConjugate E ψ g :=
        le_iSup (fun z : E => ((g z : ℝ) : EReal) -
          C06Conjugates.extendedRealValue (ψ z)) y
  have hadd := (add_le_add hφ hψ).trans hcost
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hadd
  simp only [sub_apply] at hadd
  rw [map_sub]
  linarith

/-- The full cone converts finite-domain tests into a uniform one-sided
bound at each vector, without completeness or any regularity of the functions. -/
lemma split_pointwise_upper_bound (φ ψ : ExtendedFunction E)
    (hcone : domainDifferenceCone E φ ψ = Set.univ)
    (B : Set (E →L[ℝ] ℝ)) (hB : Bornology.IsBounded B) (α : ℝ) (v : E) :
    ∃ C : ℝ, ∀ g : E →L[ℝ] ℝ,
      (∃ f ∈ B, conjugateSplitCost E φ ψ f g ≤ (α : EReal)) → g v ≤ C := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hB
  have hv : -v ∈ domainDifferenceCone E φ ψ := by rw [hcone]; trivial
  obtain ⟨a, ha, x, y, hx, hy, hxy⟩ :=
    (mem_domainDifferenceCone E φ ψ (-v)).mp hv
  obtain ⟨r, hr⟩ := (mem_finiteDomain E φ x).mp hx
  obtain ⟨s, hs⟩ := (mem_finiteDomain E ψ y).mp hy
  have hv' : v = a • (y - x) := by
    calc
      v = -(-v) := (neg_neg v).symm
      _ = -(a • (x - y)) := congrArg Neg.neg hxy
      _ = a • (y - x) := by rw [← smul_neg, neg_sub]
  refine ⟨a * (α + r + s + M * ‖x‖), ?_⟩
  intro g hg
  obtain ⟨f, hf, hcost⟩ := hg
  have hfx : -f x ≤ M * ‖x‖ :=
    (neg_le_abs (f x)).trans ((f.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hM f hf) (norm_nonneg x)))
  have htest := split_evaluation_le φ ψ f g x y r s α hr hs hcost
  rw [hv', map_smul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (by linarith) ha

/-- The uniform bounded-split assertion needs only the full cone and Banach
completeness. In particular, it does not need reflexivity. -/
theorem bounded_split_sublevel [CompleteSpace E] (φ ψ : ExtendedFunction E)
    (hcone : domainDifferenceCone E φ ψ = Set.univ)
    (B : Set (E →L[ℝ] ℝ)) (hB : Bornology.IsBounded B) (α : ℝ) :
    Bornology.IsBounded {g : E →L[ℝ] ℝ | ∃ f ∈ B,
      conjugateSplitCost E φ ψ f g ≤ (α : EReal)} := by
  let S : Set (E →L[ℝ] ℝ) := {g | ∃ f ∈ B,
    conjugateSplitCost E φ ψ f g ≤ (α : EReal)}
  have hpoint : ∀ v : E, ∃ C : ℝ, ∀ g : S, ‖(g : E →L[ℝ] ℝ) v‖ ≤ C := by
    intro v
    obtain ⟨U, hU⟩ := split_pointwise_upper_bound φ ψ hcone B hB α v
    obtain ⟨L, hL⟩ := split_pointwise_upper_bound φ ψ hcone B hB α (-v)
    refine ⟨max U L, ?_⟩
    intro g
    rw [Real.norm_eq_abs, abs_le]
    have hu := hU g.val g.property
    have hl := hL g.val g.property
    rw [map_neg] at hl
    constructor <;> linarith [le_max_left U L, le_max_right U L]
  obtain ⟨C, _, hC⟩ := C07UniformBoundedness.uniform_boundedness
    ℝ E ℝ S (fun g => g.val) hpoint
  exact isBounded_iff_forall_norm_le.mpr ⟨C, fun g hg => hC ⟨g, hg⟩⟩

/-- The manuscript statement with all its original hypotheses. -/
theorem uniform_split_bounds : Spec.BoundedSplitSublevels := by
  intro E _ _ _ φ ψ _ _ _ _ _ _ _ hcone B hB α
  exact bounded_split_sublevel φ ψ hcone B hB α

end ExpandedFA.InfimalConvolution.UniformSplitBounds
