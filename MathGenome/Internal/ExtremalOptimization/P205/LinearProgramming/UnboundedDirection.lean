import MathGenome.Internal.ExtremalOptimization.Specs.P205.LinearProgramming.UnboundedDirection
import MathGenome.Internal.ExtremalOptimization.P205.LinearProgramming.Certificates
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
open Matrix
universe u v
namespace P205.LinearProgramming.UnboundedDirection
open VariationalNotes.Ch05.LinearProgramModels

/-- The split free variables and slack of the dual produce a standard-form
system. Farkas for this system forces both signs of Ad and nonnegativity of d. -/
theorem unbounded_iff_direction : Specs.unbounded_iff_direction.{u,v} := by
  intro m n _ _ A b c hfeas
  classical
  constructor
  · intro hunb
    have hdual : ¬ ∃ y, dualFeasible A c y := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, hlt⟩ := hunb (dualObjective b y)
      exact (not_lt_of_ge (Certificates.weak_duality A b c x y hx hy)) hlt
    let B : Matrix n (m ⊕ (m ⊕ n)) ℝ :=
      fromCols Aᵀ (fromCols (-Aᵀ) 1)
    have hB : ¬ ∃ z, primalFeasible B c z := by
      rintro ⟨z, hz, hzpos⟩
      apply hdual
      refine ⟨(z ∘ Sum.inl) - (z ∘ Sum.inr ∘ Sum.inl), ?_⟩
      intro i
      have heq := congrFun hz i
      simp only [B, fromCols_mulVec, one_mulVec, Pi.add_apply,
        neg_mulVec, Pi.neg_apply, Function.comp_apply, Function.comp_assoc] at heq
      rw [mulVec_sub]
      change (Aᵀ *ᵥ (z ∘ Sum.inl)) i -
        (Aᵀ *ᵥ (z ∘ Sum.inr ∘ Sum.inl)) i ≤ c i
      have hs := hzpos (Sum.inr (Sum.inr i))
      linarith
    obtain ⟨d, hd, hcost⟩ := (Certificates.infeasible_iff_certificate B c).mp hB
    have htranspose : Bᵀ *ᵥ d = Sum.elim (A *ᵥ d) (Sum.elim (-(A *ᵥ d)) d) := by
      simp [B, transpose_fromCols, fromRows_mulVec, neg_mulVec]
    rw [htranspose] at hd
    refine ⟨d, (fun i => hd (Sum.inr (Sum.inr i))), ?_, hcost⟩
    ext i
    have hp := hd (Sum.inl i)
    have hn := hd (Sum.inr (Sum.inl i))
    change 0 ≤ (A *ᵥ d) i at hp
    change 0 ≤ -(A *ᵥ d) i at hn
    change (A *ᵥ d) i = 0
    linarith
  · rintro ⟨d, hd, hAd, hcost⟩ K
    obtain ⟨x₀, hx₀⟩ := hfeas
    let t : ℝ := (|K| + |c ⬝ᵥ x₀| + 1) / (-(c ⬝ᵥ d))
    have hden : 0 < -(c ⬝ᵥ d) := neg_pos.mpr hcost
    have ht : 0 ≤ t := div_nonneg (by positivity) hden.le
    have hmul : t * (-(c ⬝ᵥ d)) = |K| + |c ⬝ᵥ x₀| + 1 :=
      div_mul_cancel₀ _ (ne_of_gt hden)
    refine ⟨x₀ + t • d, ⟨?_, ?_⟩, ?_⟩
    · rw [mulVec_add, mulVec_smul, hx₀.1, hAd, smul_zero, add_zero]
    · intro i
      exact add_nonneg (hx₀.2 i) (mul_nonneg ht (hd i))
    · change c ⬝ᵥ (x₀ + t • d) < K
      rw [dotProduct_add, dotProduct_smul]
      change c ⬝ᵥ x₀ + t * (c ⬝ᵥ d) < K
      have hK := neg_abs_le K
      have hxabs := le_abs_self (c ⬝ᵥ x₀)
      nlinarith

theorem value_eq_bot_iff_direction : Specs.value_eq_bot_iff_direction.{u,v} := by
  intro m n _ _ A b c hfeas
  exact (primalUnbounded_iff_value_eq_bot A b c).symm.trans
    (unbounded_iff_direction A b c hfeas)

end P205.LinearProgramming.UnboundedDirection
