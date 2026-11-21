import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.TaggedEquivalence
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Cauchy

/-!
The Cauchy criterion for all fine tagged Riemann sums (K03.08.cauchy).
We choose one tagged partition below each reciprocal mesh bound. Pairwise
control makes the selected sums a scalar Cauchy sequence. The previously
proved sequence criterion supplies its limit, and comparison with one late
sum proves the unrestricted all-tagged limit. No boundedness or completeness
of a space of integrands is assumed. The final real and complex results retain
the paper's boundedness hypothesis and identify the value with its proper
Darboux integral. Singleton intervals are included throughout.
-/

namespace SingleVariableAnalysis.Riemann

abbrev FineTaggedCauchy := @Specs.SingleVariableAnalysis.Ch08.Cauchy.taggedCauchyValue

/-- A common fine-mesh limit controls two independent tagged sums. -/
theorem FineTaggedLimit.cauchy {E : Type} [NormedAddCommGroup E] [Module ℝ E]
    {f : ℝ → E} {a b : ℝ} {I : E} (h : FineTaggedLimit f a b I) :
    FineTaggedCauchy f a b := by
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := h (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro P ξ Q ζ hP hQ
  have h₁ := hc P ξ hP
  have h₂ := hc Q ζ hQ
  have ht := norm_sub_le_norm_sub_add_norm_sub (taggedSum P ξ f) I (taggedSum Q ζ f)
  rw [norm_sub_rev I (taggedSum Q ζ f)] at ht
  linarith

/-- A concrete cofinal sequence of tagged partitions suffices to transfer
scalar sequence completeness to the fine-mesh family. The completeness premise
is discharged below using the proved real and complex sequence criteria. -/
private theorem fineTaggedLimit_of_cauchy
    {E : Type} [NormedAddCommGroup E] [Module ℝ E]
    (complete : ∀ u : ℕ → E,
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖u n - u m‖ < ε) →
      ∃ I : E, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ‖u n - I‖ < ε)
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hc : FineTaggedCauchy f a b) :
    ∃ I : E, FineTaggedLimit f a b I := by
  classical
  have hex (n : ℕ) : ∃ P : Partition a b, mesh P < 1 / ((n : ℝ) + 1) :=
    exists_fine_partition hab _ (by positivity)
  choose P hP using hex
  let ξ (n : ℕ) : Tagging (P n) := Classical.choice (tags_exist (P n))
  let u (n : ℕ) : E := taggedSum (P n) (ξ n) f
  have hmesh (δ : ℝ) (hδ : 0 < δ) :
      ∃ N : ℕ, ∀ n ≥ N, mesh (P n) < δ := by
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
    refine ⟨N, ?_⟩
    intro n hn
    apply (hP n).trans
    apply (one_div_lt (by positivity : 0 < (n : ℝ) + 1) hδ).mpr
    exact (hN.trans_le (Nat.cast_le.mpr hn)).trans (lt_add_one _)
  have hu : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m ≥ N, ∀ n ≥ N, ‖u n - u m‖ < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hpairs⟩ := hc ε hε
    obtain ⟨N, hN⟩ := hmesh δ hδ
    exact ⟨N, fun m hm n hn => hpairs (P n) (ξ n) (P m) (ξ m) (hN n hn) (hN m hm)⟩
  obtain ⟨I, hI⟩ := complete u hu
  refine ⟨I, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hpairs⟩ := hc (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := hmesh δ hδ
  obtain ⟨M, hM⟩ := hI (ε / 2) (half_pos hε)
  let n := max N M
  have hnear := hM n (le_max_right N M)
  refine ⟨δ, hδ, ?_⟩
  intro Q ζ hQ
  have hpair := hpairs Q ζ (P n) (ξ n) hQ (hN n (le_max_left N M))
  have ht := norm_sub_le_norm_sub_add_norm_sub (taggedSum Q ζ f) (u n) I
  change ‖taggedSum Q ζ f - u n‖ < ε / 2 at hpair
  linarith

theorem real_tagged_cauchy_criterion :
    Specs.SingleVariableAnalysis.Ch08.Cauchy.realCauchyCriterion := by
  intro f a b hab _hf
  constructor
  · rintro ⟨I, hI⟩
    exact hI.cauchy
  · intro hc
    apply fineTaggedLimit_of_cauchy (E := ℝ) ?_ hab hc
    intro u hu
    have hu' : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
        ∀ m ≥ N, ∀ n ≥ N, |u n - u m| < ε := by
      simpa only [Real.norm_eq_abs] using hu
    obtain ⟨I, hI⟩ := (SingleVariableAnalysis.real_cauchy_criterion u).mpr hu'
    exact ⟨I, by simpa only [RealSequenceConverges, SequenceEventually,
      Real.norm_eq_abs] using hI⟩

theorem complex_tagged_cauchy_criterion :
    Specs.SingleVariableAnalysis.Ch08.Cauchy.complexCauchyCriterion := by
  intro f a b hab _hf
  constructor
  · rintro ⟨I, hI⟩
    exact hI.cauchy
  · intro hc
    apply fineTaggedLimit_of_cauchy (E := ℂ) ?_ hab hc
    intro u hu
    exact (SingleVariableAnalysis.complex_cauchy_criterion u).mpr hu

theorem real_tagged_cauchy_integral :
    Specs.SingleVariableAnalysis.Ch08.Cauchy.realCauchyIntegral := by
  intro f a b hab hf hc
  obtain ⟨I, hI⟩ := (real_tagged_cauchy_criterion f hab hf).mpr hc
  obtain ⟨hi, hvalue⟩ := (real_tagged_equivalence f hab hf I).mpr hI
  refine ⟨hi, ?_, ?_⟩
  · simpa only [hvalue] using hI
  · intro J hJ
    exact hvalue.trans (fineTaggedLimit_unique hab hI hJ)

theorem complex_tagged_cauchy_integral :
    Specs.SingleVariableAnalysis.Ch08.Cauchy.complexCauchyIntegral := by
  intro f a b hab hf hc
  obtain ⟨I, hI⟩ := (complex_tagged_cauchy_criterion f hab hf).mpr hc
  obtain ⟨hi, hvalue⟩ := (complex_tagged_equivalence f hab hf I).mpr hI
  refine ⟨hi, ?_, ?_⟩
  · simpa only [hvalue] using hI
  · intro J hJ
    exact hvalue.trans (fineTaggedLimit_unique hab hI hJ)

end SingleVariableAnalysis.Riemann
