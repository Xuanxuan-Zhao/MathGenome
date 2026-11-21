import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Monotone.PositiveGraphQuadratic
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! The graph-domain equivalence for a closed positive real operator.
We apply uniform boundedness to evaluations indexed by the quadratic unit ball.
The closed graph is complete with the product norm, and its norm is bounded
above by the sum graph norm appearing in the conclusion. No domain density,
symmetry, or full-domain assumption enters the argument. -/

noncomputable section
namespace ExpandedFA.Monotone

open ExpandedFA.Unbounded

/-- A lower bound for a quadratic along every real multiple controls its
linear coefficient, including when its quadratic coefficient is zero. -/
lemma square_le_of_quadratic_lower_bound {a b m : ℝ}
    (h : ∀ t : ℝ, m ≤ t ^ 2 * a - t * b) : b ^ 2 ≤ 4 * (-m) * a := by
  have hd := discrim_le_zero (a := a) (b := -b) (c := -m) (fun t => by
    have ht := h t
    nlinarith)
  dsimp [discrim] at hd
  nlinarith

/-- Completing the square gives the precise lower bound. -/
lemma quadratic_lower_bound_of_square_le {a b K : ℝ} (hK : 0 ≤ K)
    (ha : 0 ≤ a) (h : b ^ 2 ≤ K * a) : -K / 4 ≤ a - b := by
  rcases hK.eq_or_lt with hzero | hpos
  · have hb : b = 0 := by nlinarith [sq_nonneg b]
    rw [← hzero, hb] at h ⊢
    simpa using ha
  · by_contra hn
    have hn' : a - b + K / 4 < 0 := by linarith
    have hm := mul_neg_of_pos_of_neg hpos hn'
    nlinarith [sq_nonneg (b - K / 2)]

/-- The closed positive operator estimate on its exact graph domain. -/
theorem positive_graph_quadratic : PositiveGraphSpec.QuadraticEstimate := by
  intro X _ _ _ A hclosed hpositive
  constructor
  · intro hbelow
    let : NormedAddCommGroup A.graph := A.graph.normedAddCommGroup
    let : NormedSpace ℝ A.graph := A.graph.normedSpace
    let I := {y : A.domain // A y (y : X) ≤ (1 : ℝ)}
    let F : I → A.graph →L[ℝ] ℝ := fun y =>
      (A y.val).comp ((ContinuousLinearMap.fst ℝ X (X →L[ℝ] ℝ)).comp A.graph.subtypeL)
    let : CompleteSpace A.graph := hclosed.completeSpace_coe
    -- Lower bounds at y and -y bound every evaluation on the quadratic unit ball.
    have hpoint : ∀ z : A.graph, ∃ C : ℝ, ∀ y : I, ‖F y z‖ ≤ C := by
      intro z
      obtain ⟨x, hx, hAx⟩ := A.mem_graph_iff.mp z.property
      obtain ⟨m, hm⟩ := hbelow x
      refine ⟨1 - m, ?_⟩
      intro y
      have hp := hm (Set.mem_range_self y.val)
      have hn := hm (Set.mem_range_self (-y.val))
      have hq := y.property
      change m ≤ A y.val (y.val : X) - A y.val (x : X) at hp
      change m ≤ A (-y.val) ((-y.val : A.domain) : X) -
        A (-y.val) (x : X) at hn
      simp only [A.map_neg, Submodule.coe_neg, neg_apply,
        map_neg, neg_neg] at hn
      change |A y.val z.val.1| ≤ 1 - m
      rw [← hx]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hnorms : ∃ C : ℝ, ∀ y : I, ‖F y‖ ≤ C := by
      exact banach_steinhaus (E := A.graph) (F := ℝ) (𝕜 := ℝ) (𝕜₂ := ℝ)
        (σ₁₂ := RingHom.id ℝ) (g := F) hpoint
    obtain ⟨C, hC⟩ := hnorms
    let B : ℝ := max C 0
    have hB : 0 ≤ B := le_max_right _ _
    have hunit (x : A.domain) (y : I) :
        |A y.val (x : X)| ≤ B * (‖(x : X)‖ + ‖A x‖) := by
      let z : A.graph := ⟨((x : X), A x), A.mem_graph x⟩
      have h := (F y).le_opNorm z
      have hCB : ‖F y‖ ≤ B := (hC y).trans (le_max_left _ _)
      have hnorm : ‖z‖ ≤ ‖(x : X)‖ + ‖A x‖ := by
        change max ‖(x : X)‖ ‖A x‖ ≤ _
        exact max_le (le_add_of_nonneg_right (norm_nonneg _))
          (le_add_of_nonneg_left (norm_nonneg _))
      calc
        |A y.val (x : X)| = ‖F y z‖ := rfl
        _ ≤ ‖F y‖ * ‖z‖ := h
        _ ≤ B * (‖(x : X)‖ + ‖A x‖) := mul_le_mul hCB hnorm (norm_nonneg _) hB
    refine ⟨B ^ 2, sq_nonneg _, ?_⟩
    intro x y
    obtain ⟨m, hm⟩ := hbelow x
    have hscalar (t : ℝ) :
        m ≤ t ^ 2 * A y (y : X) - t * A y (x : X) := by
      have h := hm (Set.mem_range_self (t • y))
      change m ≤ A (t • y) ((t • y : A.domain) : X) - A (t • y) (x : X) at h
      simpa only [A.map_smul, Submodule.coe_smul, smul_apply,
        map_smul, smul_eq_mul, pow_two, mul_assoc, mul_left_comm] using h
    -- The degenerate quadratic directions vanish by the scalar discriminant test.
    by_cases hq : A y (y : X) = 0
    · have hs := square_le_of_quadratic_lower_bound hscalar
      rw [hq] at hs ⊢
      simpa only [mul_zero, sq_abs] using hs
    · have hqpos : 0 < A y (y : X) := lt_of_le_of_ne (hpositive y) (Ne.symm hq)
      -- Normalize a direction with positive quadratic value to the quadratic unit ball.
      let s : ℝ := Real.sqrt (A y (y : X))
      have hspos : 0 < s := Real.sqrt_pos.mpr hqpos
      have hsne : s ≠ 0 := ne_of_gt hspos
      have hsq : s ^ 2 = A y (y : X) := Real.sq_sqrt (hpositive y)
      have hnormalized : A (s⁻¹ • y) ((s⁻¹ • y : A.domain) : X) ≤ 1 := by
        simp only [A.map_smul, Submodule.coe_smul, smul_apply,
          map_smul, smul_eq_mul]
        rw [← hsq]
        field_simp
        rfl
      have hu := hunit x ⟨s⁻¹ • y, hnormalized⟩
      change |A (s⁻¹ • y) (x : X)| ≤ _ at hu
      simp only [A.map_smul, smul_apply, smul_eq_mul, abs_mul,
        abs_inv, abs_of_pos hspos] at hu
      have hb : |A y (x : X)| ≤ (B * (‖(x : X)‖ + ‖A x‖)) * s := by
        have := (mul_le_mul_of_nonneg_left hu (le_of_lt hspos))
        field_simp at this
        nlinarith
      have hsquare := sq_le_sq₀ (abs_nonneg (A y (x : X)))
        (mul_nonneg (mul_nonneg hB
          (add_nonneg (norm_nonneg (x : X)) (norm_nonneg (A x)))) hspos.le)
      have hout := hsquare.mpr hb
      simpa only [mul_pow, hsq, mul_assoc] using hout
  · rintro ⟨k, hk, hestimate⟩ x
    refine ⟨- (k * (‖(x : X)‖ + ‖A x‖) ^ 2) / 4, ?_⟩
    rintro _ ⟨y, rfl⟩
    have hs := hestimate x y
    rw [sq_abs] at hs
    exact quadratic_lower_bound_of_square_le
      (mul_nonneg hk (sq_nonneg _)) (hpositive y) hs

end ExpandedFA.Monotone
