import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Uniform
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Cauchy

/-!
# Uniform Cauchy criterion

Implements `K03.12.cauchy` (paper.tex:1212–1219) for both scalar fields.
Scalar completeness comes from the proved upstream Cauchy criteria. Choose
the scalar limit at each point. For a given positive error, keep the common
Cauchy threshold for half that error; at each point choose a later term
within half the error of its scalar limit. The triangle inequality gives
the required uniform estimate. This also proves the empty-domain case,
without any nonemptiness or boundedness assumption.
-/

namespace SingleVariableAnalysis

universe u v

private theorem uniform_cauchy_of_scalar_cauchy
    {E : Type u} {K : Type v} [NormedAddCommGroup K]
    (scalar_complete : ∀ a : ℕ → K,
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖a n - a m‖ < ε) →
        ∃ L : K, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ‖a n - L‖ < ε)
    (F : ℕ → E → K) :
    (∃ f : E → K, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n ≥ N, ∀ x, ‖F n x - f x‖ < ε) ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
        ∀ m ≥ N, ∀ n ≥ N, ∀ x, ‖F n x - F m x‖ < ε := by
  constructor
  · rintro ⟨f, hf⟩ ε hε
    obtain ⟨N, hN⟩ := hf (ε / 2) (half_pos hε)
    refine ⟨N, ?_⟩
    intro m hm n hn x
    calc
      ‖F n x - F m x‖ ≤ ‖F n x - f x‖ + ‖F m x - f x‖ := by
        simpa only [sub_add_sub_cancel, norm_sub_rev] using
          norm_add_le (F n x - f x) (f x - F m x)
      _ < ε / 2 + ε / 2 := add_lt_add (hN n hn x) (hN m hm x)
      _ = ε := add_halves ε
  · intro hc
    have hp : ∀ x : E, ∃ L : K, ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n ≥ N, ‖F n x - L‖ < ε := by
      intro x
      apply scalar_complete (fun n => F n x)
      intro ε hε
      obtain ⟨N, hN⟩ := hc ε hε
      exact ⟨N, fun m hm n hn => hN m hm n hn x⟩
    choose f hf using hp
    refine ⟨f, ?_⟩
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε / 2) (half_pos hε)
    refine ⟨N, ?_⟩
    intro n hn x
    obtain ⟨M, hM⟩ := hf x (ε / 2) (half_pos hε)
    let m := max N M
    calc
      ‖F n x - f x‖ ≤ ‖F n x - F m x‖ + ‖F m x - f x‖ := by
        simpa only [sub_add_sub_cancel] using
          norm_add_le (F n x - F m x) (F m x - f x)
      _ < ε / 2 + ε / 2 :=
        add_lt_add (hN m (le_max_left _ _) n hn x) (hM m (le_max_right _ _))
      _ = ε := add_halves ε

theorem real_uniform_cauchy_criterion {E : Type u} (F : ℕ → E → ℝ) :
    (∃ f : E → ℝ, RealUniformConverges F f) ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
        ∀ m ≥ N, ∀ n ≥ N, ∀ x, |F n x - F m x| < ε := by
  have scalar_complete : ∀ a : ℕ → ℝ,
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖a n - a m‖ < ε) →
        ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ‖a n - L‖ < ε := by
    intro a ha
    have ha' := (real_cauchy_criterion a).mpr
      (by simpa only [Real.norm_eq_abs] using ha)
    simpa only [RealSequenceConverges, SequenceEventually, Real.norm_eq_abs] using ha'
  simpa only [RealUniformConverges, Real.norm_eq_abs] using
    uniform_cauchy_of_scalar_cauchy scalar_complete F

theorem complex_uniform_cauchy_criterion {E : Type u} (F : ℕ → E → ℂ) :
    (∃ f : E → ℂ, ComplexUniformConverges F f) ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
        ∀ m ≥ N, ∀ n ≥ N, ∀ x, ‖F n x - F m x‖ < ε := by
  have scalar_complete : ∀ a : ℕ → ℂ,
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖a n - a m‖ < ε) →
        ∃ L : ℂ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ‖a n - L‖ < ε := by
    intro a ha
    exact (complex_cauchy_criterion a).mpr ha
  exact uniform_cauchy_of_scalar_cauchy scalar_complete F

theorem real_uniform_limit_exists_empty {E : Type u} [IsEmpty E]
    (F : ℕ → E → ℝ) : ∃ f : E → ℝ, RealUniformConverges F f := by
  exact ⟨fun _ => 0, realUniformConverges_empty F (fun _ => 0)⟩

theorem complex_uniform_limit_exists_empty {E : Type u} [IsEmpty E]
    (F : ℕ → E → ℂ) : ∃ f : E → ℂ, ComplexUniformConverges F f := by
  exact ⟨fun _ => 0, complexUniformConverges_empty F (fun _ => 0)⟩

end SingleVariableAnalysis
