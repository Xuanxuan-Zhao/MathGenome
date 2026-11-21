import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Analyticity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.IsolatedZeros
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# The local isolated-zero argument

K03.13.identity, paper.tex:1447–1449. The scalar field for analytic calculus
is ℝ in both cases. Iterated difference quotients provide the shifted series
and the factor; its constant coefficient is the original first nonzero one.
-/
noncomputable section
namespace SingleVariableAnalysis
open Set Filter
open scoped Topology

namespace IsolatedZeros

/-- Coordinate coefficients detect the zero formal series in one dimension. -/
theorem series_zero_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : FormalMultilinearSeries ℝ ℝ F) :
    p = 0 ↔ ∀ n, p.coeff n = 0 := by
  constructor
  · rintro rfl n
    rfl
  · intro h
    funext n
    exact FormalMultilinearSeries.coeff_eq_zero.mp (h n)

/-- Metric form of an unpunctured zero neighborhood. -/
theorem locally_zero_iff {F : Type*} [Zero F] (f : ℝ → F) (c : ℝ) :
    (∀ᶠ x in 𝓝 c, f x = 0) ↔
      ∃ δ : ℝ, 0 < δ ∧ ∀ x, |x-c| < δ → f x = 0 := by
  simpa only [Real.dist_eq] using (Metric.eventually_nhds_iff :
    (∀ᶠ x in 𝓝 c, f x = 0) ↔ ∃ δ > 0, ∀ x, dist x c < δ → f x = 0)

/-- The factor retains exactly the tail of the given coefficient series. -/
theorem formal_factor {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {c : ℝ} {p : FormalMultilinearSeries ℝ ℝ F}
    (hp : HasFPowerSeriesAt f p c) (hn : p ≠ 0) :
    ∃ (m : ℕ) (g : ℝ → F),
      (∀ n < m, p.coeff n = 0) ∧ p.coeff m ≠ 0 ∧
      HasFPowerSeriesAt g (FormalMultilinearSeries.fslope^[m] p) c ∧
      g c = p.coeff m ∧ ∀ x, f x = (x-c)^m • g x := by
  let g := (Function.swap dslope c)^[p.order] f
  have hg : HasFPowerSeriesAt g (FormalMultilinearSeries.fslope^[p.order] p) c :=
    hp.has_fpower_series_iterate_dslope_fslope p.order
  refine ⟨p.order, g, ?_, ?_, hg, ?_, hp.eq_pow_order_mul_iterate_dslope⟩
  · intro n hlt
    exact FormalMultilinearSeries.coeff_eq_zero.mpr (p.apply_eq_zero_of_lt_order hlt)
  · exact fun h => p.apply_order_ne_zero hn (FormalMultilinearSeries.coeff_eq_zero.mp h)
  · have he := hg.coeff_zero 1
    change (FormalMultilinearSeries.fslope^[p.order] p).coeff 0 = g c at he
    simpa only [FormalMultilinearSeries.coeff_iterate_fslope, zero_add] using he.symm

/-- A continuous nonzero factor stays nonzero on a neighborhood on which it
is continuous at every point. -/
theorem factor_neighborhood {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ → F} {c : ℝ} (hg : AnalyticAt ℝ g c) (hn : g c ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ContinuousOn g {x | |x-c| < δ} ∧
      ∀ x, |x-c| < δ → g x ≠ 0 := by
  have he := hg.eventually_continuousAt.and (hg.continuousAt.eventually_ne hn)
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro x hx
    exact (hd (by simpa only [Real.dist_eq, Set.mem_ofPred_eq] using hx)).1.continuousWithinAt
  · intro x hx
    exact (hd (by simpa only [Real.dist_eq] using hx)).2


theorem real_shift (a : ℕ → ℝ) (m : ℕ) :
    FormalMultilinearSeries.fslope^[m] (realCoefficientSeries a) =
      realCoefficientSeries (fun n => a (n+m)) := by
  funext n
  rw [← FormalMultilinearSeries.mkPiRing_coeff_eq
    (FormalMultilinearSeries.fslope^[m] (realCoefficientSeries a)) n]
  simp only [FormalMultilinearSeries.coeff_iterate_fslope, RealAnalyticity.real_coefficient]
  rfl

theorem complex_shift (a : ℕ → ℂ) (m : ℕ) :
    FormalMultilinearSeries.fslope^[m] (complexRealCoefficientSeries a) =
      complexRealCoefficientSeries (fun n => a (n+m)) := by
  funext n
  rw [← FormalMultilinearSeries.mkPiRing_coeff_eq
    (FormalMultilinearSeries.fslope^[m] (complexRealCoefficientSeries a)) n]
  simp only [FormalMultilinearSeries.coeff_iterate_fslope, RealAnalyticity.complex_coefficient]
  rfl

end IsolatedZeros

theorem real_powerSeries_local_dichotomy :
  ∀ (a : ℕ → ℝ) (f : ℝ → ℝ) (c : ℝ), RealPowerSeriesRepresentsAt a f c →
    ((∀ n, a n = 0) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ x, |x-c| < δ → f x = 0) ∨
    ∃ m : ℕ, (∀ n < m, a n = 0) ∧ a m ≠ 0 ∧ ∃ g : ℝ → ℝ,
      RealPowerSeriesRepresentsAt (fun n => a (n+m)) g c ∧ g c = a m ∧
      ∃ δ : ℝ, 0 < δ ∧ ContinuousOn g {x | |x-c| < δ} ∧
        ∀ x, |x-c| < δ → f x = (x-c)^m * g x ∧ g x ≠ 0 := by
  intro a f c hf
  have hp := (real_powerSeries_representsAt_iff a f c).mp hf
  by_cases hz : realCoefficientSeries a = 0
  · exact Or.inl ⟨by simpa using (IsolatedZeros.series_zero_iff _).mp hz,
      (IsolatedZeros.locally_zero_iff f c).mp (hp.locally_zero_iff.mpr hz)⟩
  · obtain ⟨m, g, hlow, hne, hg, hgc, hfact⟩ := IsolatedZeros.formal_factor hp hz
    have hgc' : g c = a m := by simpa using hgc
    have hne' : a m ≠ 0 := by simpa using hne
    have hg' : g c ≠ 0 := by rwa [hgc']
    obtain ⟨δ, hδ, hcont, hnon⟩ := IsolatedZeros.factor_neighborhood ⟨_, hg⟩ hg'
    refine Or.inr ⟨m, by simpa using hlow, hne', g, ?_, hgc', δ, hδ, hcont, ?_⟩
    · apply (real_powerSeries_representsAt_iff _ g c).mpr
      simpa only [IsolatedZeros.real_shift] using hg
    · intro x hx
      exact ⟨by simpa only [smul_eq_mul] using hfact x,
        hnon x hx⟩

theorem complex_real_powerSeries_local_dichotomy :
  ∀ (a : ℕ → ℂ) (f : ℝ → ℂ) (c : ℝ), ComplexRealPowerSeriesRepresentsAt a f c →
    ((∀ n, a n = 0) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ x, |x-c| < δ → f x = 0) ∨
    ∃ m : ℕ, (∀ n < m, a n = 0) ∧ a m ≠ 0 ∧ ∃ g : ℝ → ℂ,
      ComplexRealPowerSeriesRepresentsAt (fun n => a (n+m)) g c ∧ g c = a m ∧
      ∃ δ : ℝ, 0 < δ ∧ ContinuousOn g {x | |x-c| < δ} ∧
        ∀ x, |x-c| < δ → f x = ((x-c : ℝ) : ℂ)^m * g x ∧ g x ≠ 0 := by
  intro a f c hf
  have hp := (complex_real_powerSeries_representsAt_iff a f c).mp hf
  by_cases hz : complexRealCoefficientSeries a = 0
  · exact Or.inl ⟨by simpa using (IsolatedZeros.series_zero_iff _).mp hz,
      (IsolatedZeros.locally_zero_iff f c).mp (hp.locally_zero_iff.mpr hz)⟩
  · obtain ⟨m, g, hlow, hne, hg, hgc, hfact⟩ := IsolatedZeros.formal_factor hp hz
    have hgc' : g c = a m := by simpa using hgc
    have hne' : a m ≠ 0 := by simpa using hne
    have hg' : g c ≠ 0 := by rwa [hgc']
    obtain ⟨δ, hδ, hcont, hnon⟩ := IsolatedZeros.factor_neighborhood ⟨_, hg⟩ hg'
    refine Or.inr ⟨m, by simpa using hlow, hne', g, ?_, hgc', δ, hδ, hcont, ?_⟩
    · apply (complex_real_powerSeries_representsAt_iff _ g c).mpr
      simpa only [IsolatedZeros.complex_shift] using hg
    · intro x hx
      exact ⟨by simpa only [Complex.real_smul, Complex.ofReal_pow] using hfact x,
        hnon x hx⟩

theorem real_powerSeries_locally_zero_iff :
  ∀ (a : ℕ → ℝ) (f : ℝ → ℝ) (c : ℝ), RealPowerSeriesRepresentsAt a f c →
    ((∃ δ : ℝ, 0 < δ ∧ ∀ x, |x-c| < δ → f x = 0) ↔ ∀ n, a n = 0) := by
  intro a f c hf
  have hp := (real_powerSeries_representsAt_iff a f c).mp hf
  rw [← IsolatedZeros.locally_zero_iff, hp.locally_zero_iff, IsolatedZeros.series_zero_iff]
  simp only [RealAnalyticity.real_coefficient]

theorem complex_real_powerSeries_locally_zero_iff :
  ∀ (a : ℕ → ℂ) (f : ℝ → ℂ) (c : ℝ), ComplexRealPowerSeriesRepresentsAt a f c →
    ((∃ δ : ℝ, 0 < δ ∧ ∀ x, |x-c| < δ → f x = 0) ↔ ∀ n, a n = 0) := by
  intro a f c hf
  have hp := (complex_real_powerSeries_representsAt_iff a f c).mp hf
  rw [← IsolatedZeros.locally_zero_iff, hp.locally_zero_iff, IsolatedZeros.series_zero_iff]
  simp only [RealAnalyticity.complex_coefficient]

theorem real_powerSeries_isolated_zero :
  ∀ (a : ℕ → ℝ) (f : ℝ → ℝ) (c : ℝ), RealPowerSeriesRepresentsAt a f c →
    f c = 0 → (∃ n, a n ≠ 0) →
    ∃ m : ℕ, 0 < m ∧ (∀ n < m, a n = 0) ∧ a m ≠ 0 ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ x, 0 < |x-c| → |x-c| < δ → f x ≠ 0 := by
  intro a f c hf hfc hnon
  rcases real_powerSeries_local_dichotomy a f c hf with h | h
  · obtain ⟨n, hn⟩ := hnon
    exact False.elim (hn (h.1 n))
  · obtain ⟨m, hlow, hne, g, _, _, δ, hδ, _, hfact⟩ := h
    have hc : |c-c| < δ := by simpa using hδ
    have hm : 0 < m := Nat.pos_of_ne_zero (by
      intro hm
      have he := (hfact c hc).1
      rw [hm, pow_zero, one_mul] at he
      exact (hfact c hc).2 (he.symm.trans hfc))
    refine ⟨m, hm, hlow, hne, δ, hδ, fun x hx hxδ => ?_⟩
    rw [(hfact x hxδ).1]
    apply mul_ne_zero (pow_ne_zero _ ?_) ((hfact x hxδ).2)
    exact abs_pos.mp hx

theorem complex_real_powerSeries_isolated_zero :
  ∀ (a : ℕ → ℂ) (f : ℝ → ℂ) (c : ℝ), ComplexRealPowerSeriesRepresentsAt a f c →
    f c = 0 → (∃ n, a n ≠ 0) →
    ∃ m : ℕ, 0 < m ∧ (∀ n < m, a n = 0) ∧ a m ≠ 0 ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ x, 0 < |x-c| → |x-c| < δ → f x ≠ 0 := by
  intro a f c hf hfc hnon
  rcases complex_real_powerSeries_local_dichotomy a f c hf with h | h
  · obtain ⟨n, hn⟩ := hnon
    exact False.elim (hn (h.1 n))
  · obtain ⟨m, hlow, hne, g, _, _, δ, hδ, _, hfact⟩ := h
    have hc : |c-c| < δ := by simpa using hδ
    have hm : 0 < m := Nat.pos_of_ne_zero (by
      intro hm
      have he := (hfact c hc).1
      rw [hm, pow_zero, one_mul] at he
      exact (hfact c hc).2 (he.symm.trans hfc))
    refine ⟨m, hm, hlow, hne, δ, hδ, fun x hx hxδ => ?_⟩
    rw [(hfact x hxδ).1]
    apply mul_ne_zero (pow_ne_zero _ ?_) ((hfact x hxδ).2)
    exact_mod_cast (abs_pos.mp hx)

theorem real_powerSeries_zero_of_accumulation :
  ∀ (a : ℕ → ℝ) (f : ℝ → ℝ) (c : ℝ), RealPowerSeriesRepresentsAt a f c →
    (∀ ε : ℝ, 0 < ε → ∃ x : ℝ, 0 < |x-c| ∧ |x-c| < ε ∧ f x = 0) →
    (∀ n, a n = 0) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ x, |x-c| < δ → f x = 0 := by
  intro a f c hf hacc
  rcases real_powerSeries_local_dichotomy a f c hf with h | h
  · exact h
  · obtain ⟨m, _, _, g, _, _, δ, hδ, _, hfact⟩ := h
    obtain ⟨x, hx, hxδ, hzero⟩ := hacc δ hδ
    have hne : f x ≠ 0 := by
      rw [(hfact x hxδ).1]
      apply mul_ne_zero (pow_ne_zero _ ?_) ((hfact x hxδ).2)
      exact abs_pos.mp hx
    exact False.elim (hne hzero)

theorem complex_real_powerSeries_zero_of_accumulation :
  ∀ (a : ℕ → ℂ) (f : ℝ → ℂ) (c : ℝ), ComplexRealPowerSeriesRepresentsAt a f c →
    (∀ ε : ℝ, 0 < ε → ∃ x : ℝ, 0 < |x-c| ∧ |x-c| < ε ∧ f x = 0) →
    (∀ n, a n = 0) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ x, |x-c| < δ → f x = 0 := by
  intro a f c hf hacc
  rcases complex_real_powerSeries_local_dichotomy a f c hf with h | h
  · exact h
  · obtain ⟨m, _, _, g, _, _, δ, hδ, _, hfact⟩ := h
    obtain ⟨x, hx, hxδ, hzero⟩ := hacc δ hδ
    have hne : f x ≠ 0 := by
      rw [(hfact x hxδ).1]
      apply mul_ne_zero (pow_ne_zero _ ?_) ((hfact x hxδ).2)
      exact_mod_cast (abs_pos.mp hx)
    exact False.elim (hne hzero)

end SingleVariableAnalysis
