import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsOrdinary
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.RsDarboux
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.TaggedEquivalence

namespace SingleVariableAnalysis.Stieltjes
open Riemann

/-- For the identity integrator, Δα is exactly the ordinary cell length. -/
theorem ordinary_darboux_sums : Specs.SingleVariableAnalysis.Ch15.RsOrdinary.darbouxSums := by
  intro f a b P hf
  exact ⟨rfl, rfl⟩

theorem ordinary_real_value : Specs.SingleVariableAnalysis.Ch15.RsOrdinary.realValue := by
  intro f a b hab hf I
  have hα : MonotoneOn (id : ℝ → ℝ) (Set.Icc a b) := fun _ _ _ _ h => h
  have hv := Darboux.integral_value a b hab f id hf hα I
  change HasIntegral a b f id I ↔ ∃ hi : RealIntegrable f a b, realIntegral f hi = I
  constructor
  · intro hI
    obtain ⟨heq, hval⟩ := hv.mp hI
    have hi : RealIntegrable f a b := ⟨hab, hf, heq.symm⟩
    exact ⟨hi, hval.symm⟩
  · rintro ⟨hi, hI⟩
    apply hv.mpr
    have hc := realIntegral_common_value f hi hab hf
    exact ⟨hc.2.symm.trans hc.1, hI.symm.trans hc.1⟩

/-- Norm boundedness supplies ordinary upper and lower real bounds. -/
theorem boundedOnInterval_of_boundedOn {a b : ℝ} {f : ℝ → ℝ}
    (hf : BoundedOn a b f) : BoundedOnInterval f a b := by
  obtain ⟨M, hM⟩ := hf
  have hx (x : ℝ) (h : x ∈ Set.Icc a b) : -M ≤ f x ∧ f x ≤ M :=
    abs_le.mp (by simpa only [Real.norm_eq_abs] using hM x h)
  exact ⟨⟨-M, by rintro _ ⟨x, h, rfl⟩; exact (hx x h).1⟩,
    ⟨M, by rintro _ ⟨x, h, rfl⟩; exact (hx x h).2⟩⟩

/-- Real and imaginary parts commute with the actual weighted finite sums. -/
theorem taggedSum_re {a b : ℝ} (P : Partition a b) (t : Tagging P)
    (f : ℝ → ℂ) (α : ℝ → ℝ) :
    (taggedSum P t f α).re = taggedSum P t (fun x => (f x).re) α := by
  simp [taggedSum, S.sumValue]

theorem taggedSum_im {a b : ℝ} (P : Partition a b) (t : Tagging P)
    (f : ℝ → ℂ) (α : ℝ → ℝ) :
    (taggedSum P t f α).im = taggedSum P t (fun x => (f x).im) α := by
  simp [taggedSum, S.sumValue]

/-- Combining the two controlling partitions is essential in the reverse
implication; neither component is assumed to use the other's partition. -/
theorem refinementLimit_complex_iff (a b : ℝ) (f : ℝ → ℂ) (α : ℝ → ℝ) (I : ℂ) :
    RefinementLimit a b f α I ↔
      RefinementLimit a b (fun x => (f x).re) α I.re ∧
      RefinementLimit a b (fun x => (f x).im) α I.im := by
  constructor
  · intro h
    constructor
    · intro ε hε
      obtain ⟨P₀, hP₀⟩ := h ε hε
      refine ⟨P₀, fun P hP t => ?_⟩
      have ht := (Complex.abs_re_le_norm (taggedSum P t f α - I)).trans_lt (hP₀ P hP t)
      simpa only [Real.norm_eq_abs, Complex.sub_re, taggedSum_re] using ht
    · intro ε hε
      obtain ⟨P₀, hP₀⟩ := h ε hε
      refine ⟨P₀, fun P hP t => ?_⟩
      have ht := (Complex.abs_im_le_norm (taggedSum P t f α - I)).trans_lt (hP₀ P hP t)
      simpa only [Real.norm_eq_abs, Complex.sub_im, taggedSum_im] using ht
  · rintro ⟨hr, hi⟩ ε hε
    obtain ⟨Pr, hPr⟩ := hr (ε/2) (half_pos hε)
    obtain ⟨Pi, hPi⟩ := hi (ε/2) (half_pos hε)
    obtain ⟨P₀, _, hP₀r, hP₀i⟩ := common_refinement Pr Pi
    refine ⟨P₀, ?_⟩
    intro P hP t
    have hr' := hPr P (Finset.Subset.trans hP₀r hP) t
    have hi' := hPi P (Finset.Subset.trans hP₀i hP) t
    have ht := Complex.norm_le_abs_re_add_abs_im (taggedSum P t f α - I)
    simp only [Real.norm_eq_abs] at hr' hi'
    simp only [Complex.sub_re, Complex.sub_im, taggedSum_re, taggedSum_im] at ht
    linarith

theorem boundedOn_complex_iff (a b : ℝ) (f : ℝ → ℂ) :
    BoundedOn a b f ↔
      BoundedOn a b (fun x => (f x).re) ∧ BoundedOn a b (fun x => (f x).im) := by
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨⟨M, fun x hx => by
      simpa only [Real.norm_eq_abs] using (Complex.abs_re_le_norm (f x)).trans (hM x hx)⟩,
      ⟨M, fun x hx => by
      simpa only [Real.norm_eq_abs] using (Complex.abs_im_le_norm (f x)).trans (hM x hx)⟩⟩
  · rintro ⟨⟨Mr, hr⟩, ⟨Mi, hi⟩⟩
    exact ⟨Mr + Mi, fun x hx => (Complex.norm_le_abs_re_add_abs_im (f x)).trans
      (add_le_add (by simpa only [Real.norm_eq_abs] using hr x hx)
        (by simpa only [Real.norm_eq_abs] using hi x hx))⟩

theorem integral_complex_componentwise :
    Specs.SingleVariableAnalysis.Ch15.RsOrdinary.complexComponentwise := by
  intro a b f α I
  unfold Specs.SingleVariableAnalysis.Ch15.RsSums.integralValue
  have hb := boundedOn_complex_iff (min a b) (max a b) f
  change (Specs.SingleVariableAnalysis.Ch15.RsSums.boundedOnValue _ _ _ ↔ _) at hb
  rw [hb]
  by_cases hab : a ≤ b
  · simp only [ite_eq_left hab, refinementLimit_complex_iff]
    tauto
  · simp only [ite_eq_right hab, refinementLimit_complex_iff, Complex.neg_re, Complex.neg_im]
    tauto

theorem ordinary_complex_value : Specs.SingleVariableAnalysis.Ch15.RsOrdinary.complexValue := by
  intro f a b hab hf I
  obtain ⟨hfr, hfi⟩ := complex_components_bounded f hf
  rw [integral_complex_componentwise,
    ordinary_real_value _ hab hfr, ordinary_real_value _ hab hfi]
  constructor
  · rintro ⟨⟨hr, hIr⟩, ⟨hi, hIi⟩⟩
    refine ⟨⟨hr, hi⟩, ?_⟩
    apply Complex.ext
    · exact (complexIntegral_components f ⟨hr, hi⟩).1.trans hIr
    · exact (complexIntegral_components f ⟨hr, hi⟩).2.trans hIi
  · rintro ⟨h, hI⟩
    have hc := complexIntegral_components f h
    rw [hI] at hc
    exact ⟨⟨h.1, hc.1.symm⟩, ⟨h.2, hc.2.symm⟩⟩

theorem ordinary_real_oriented_value :
    Specs.SingleVariableAnalysis.Ch15.RsOrdinary.realOrientedValue := by
  intro f a b hf I
  by_cases hab : a ≤ b
  · simp only [min_eq_left hab, max_eq_right hab, ite_eq_left hab] at hf ⊢
    exact ordinary_real_value f hab (boundedOnInterval_of_boundedOn hf) I
  · have hba : b ≤ a := le_of_not_ge hab
    rw [reverse_orientation]
    simp only [min_eq_right hba, max_eq_left hba, ite_eq_right hab] at hf ⊢
    rw [ordinary_real_value f hba (boundedOnInterval_of_boundedOn hf)]
    constructor
    · rintro ⟨h, hv⟩
      exact ⟨h, by rw [hv, neg_neg]⟩
    · rintro ⟨h, hv⟩
      exact ⟨h, by rw [← hv, neg_neg]⟩

theorem ordinary_complex_oriented_value :
    Specs.SingleVariableAnalysis.Ch15.RsOrdinary.complexOrientedValue := by
  intro f a b hf I
  by_cases hab : a ≤ b
  · simp only [min_eq_left hab, max_eq_right hab, ite_eq_left hab] at hf ⊢
    exact ordinary_complex_value f hab hf I
  · have hba : b ≤ a := le_of_not_ge hab
    rw [reverse_orientation]
    simp only [min_eq_right hba, max_eq_left hba, ite_eq_right hab] at hf ⊢
    rw [ordinary_complex_value f hba hf]
    constructor
    · rintro ⟨h, hv⟩
      exact ⟨h, by rw [hv, neg_neg]⟩
    · rintro ⟨h, hv⟩
      exact ⟨h, by rw [← hv, neg_neg]⟩

theorem ordinary_real_integrability :
    Specs.SingleVariableAnalysis.Ch15.RsOrdinary.realIntegrability := by
  intro f a b hf
  constructor
  · rintro ⟨I, hI⟩
    exact ((ordinary_real_oriented_value f a b hf I).mp hI).choose
  · intro h
    exact ⟨_, (ordinary_real_oriented_value f a b hf _).mpr ⟨h, rfl⟩⟩

theorem ordinary_complex_integrability :
    Specs.SingleVariableAnalysis.Ch15.RsOrdinary.complexIntegrability := by
  intro f a b hf
  constructor
  · rintro ⟨I, hI⟩
    exact ((ordinary_complex_oriented_value f a b hf I).mp hI).choose
  · intro h
    exact ⟨_, (ordinary_complex_oriented_value f a b hf _).mpr ⟨h, rfl⟩⟩

theorem ordinary_real_mesh : Specs.SingleVariableAnalysis.Ch15.RsOrdinary.realMesh := by
  intro f a b hab hf I
  exact (ordinary_real_value f hab hf I).trans (real_tagged_equivalence f hab hf I)

theorem ordinary_complex_mesh : Specs.SingleVariableAnalysis.Ch15.RsOrdinary.complexMesh := by
  intro f a b hab hf I
  exact (ordinary_complex_value f hab hf I).trans (complex_tagged_equivalence f hab hf I)

end SingleVariableAnalysis.Stieltjes
