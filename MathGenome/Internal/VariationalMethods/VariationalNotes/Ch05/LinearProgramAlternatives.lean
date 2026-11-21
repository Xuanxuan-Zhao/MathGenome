import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.LinearProgramAlternatives
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch05.LinearProgramDuality
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.FiniteConesFarkas

noncomputable section
open Matrix
universe u v
namespace VariationalNotes.Ch05.LinearProgramAlternatives
open VariationalNotes.Ch05.LinearProgramModels

theorem both_feasible : Specs.both_feasible.{u,v} := by
  intro m n _ _ A b c hp hd
  obtain ⟨y, hy⟩ := hd
  have htop : primalValue A b c ≠ ⊤ := by
    intro h
    exact (primalValue_eq_top_iff A b c).mp h hp
  have hbot : primalValue A b c ≠ ⊥ := by
    intro h
    have hle := (le_dualValue A b c y hy).trans (weakDuality_values A b c)
    change (dualObjective b y : EReal) ≤ primalValue A b c at hle
    rw [h] at hle
    exact (EReal.bot_lt_coe _).not_ge hle
  let p := (primalValue A b c).toReal
  have heq : primalValue A b c = (p : EReal) := (EReal.coe_toReal htop hbot).symm
  obtain ⟨hpa, hda, _, hdv⟩ := LinearProgramDuality.strong_duality A b c p hp heq
  exact ⟨p, hpa, hda, heq, hdv⟩

theorem primal_only_unbounded : Specs.primal_only_unbounded.{u,v} := by
  intro m n _ _ A b c hp hd
  apply (primalUnbounded_iff_value_eq_bot A b c).mpr
  by_contra hbot
  have htop : primalValue A b c ≠ ⊤ := by
    intro h
    exact (primalValue_eq_top_iff A b c).mp h hp
  have heq := (EReal.coe_toReal htop hbot).symm
  obtain ⟨_, ⟨y, hy, _⟩, _, _⟩ :=
    LinearProgramDuality.strong_duality A b c _ hp heq
  exact hd ⟨y, hy.1⟩

theorem dual_only_unbounded : Specs.dual_only_unbounded.{u,v} := by
  intro m n _ _ A b c hp hd
  have hno : ¬ ∃ x : n → ℝ, 0 ≤ x ∧ A *ᵥ x = b := by
    rintro ⟨x, hx, hAx⟩
    exact hp ⟨x, hAx, hx⟩
  have hcert : ∃ z : m → ℝ, 0 ≤ Aᵀ *ᵥ z ∧ b ⬝ᵥ z < 0 := by
    rcases VariationalNotes.ConvexGeometry.farkas_alternative A b with h | h
    · exact (hno h.1).elim
    · exact h.1
  obtain ⟨z, hz, hbz⟩ := hcert
  obtain ⟨y, hy⟩ := hd
  intro r
  let t : ℝ := (|r| + |b ⬝ᵥ y| + 1) / (-(b ⬝ᵥ z))
  have hden : 0 < -(b ⬝ᵥ z) := neg_pos.mpr hbz
  have ht : 0 ≤ t := div_nonneg (by positivity) hden.le
  have hmul : t * (-(b ⬝ᵥ z)) = |r| + |b ⬝ᵥ y| + 1 :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  refine ⟨y - t • z, ?_, ?_⟩
  · intro i
    rw [mulVec_sub, mulVec_smul]
    change (Aᵀ *ᵥ y) i - t * (Aᵀ *ᵥ z) i ≤ c i
    exact (sub_le_self _ (mul_nonneg ht (hz i))).trans (hy i)
  · change r < b ⬝ᵥ (y - t • z)
    rw [dotProduct_sub, dotProduct_smul]
    change r < b ⬝ᵥ y - t * (b ⬝ᵥ z)
    have hr := le_abs_self r
    have hyabs := neg_abs_le (b ⬝ᵥ y)
    nlinarith

theorem both_infeasible_example : Specs.both_infeasible_example := by
  constructor
  · rintro ⟨x, hx, _⟩
    have h := congrFun hx 0
    norm_num at h
  · rintro ⟨y, hy⟩
    have h := hy 0
    norm_num at h

end VariationalNotes.Ch05.LinearProgramAlternatives
