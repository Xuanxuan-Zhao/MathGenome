import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.TaggedEquivalence
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.TaggedForward

namespace SingleVariableAnalysis.Riemann
open scoped BigOperators

/-- The cell lengths telescope, including the empty partition. -/
theorem sum_cellLength {a b : ℝ} (P : Partition a b) :
    (∑ i : Fin P.n, cellLength P i) = b - a := by
  simpa only [cellLength, S.lengthValue, P.first, P.last] using sum_cell_differences P.point

/-- Tags can approximate a cell supremum even when it is not attained. -/
theorem exists_tag_near_supremum (f : ℝ → ℝ) {a b : ℝ} (P : Partition a b)
    (hf : BoundedOnInterval f a b) (η : ℝ) (hη : 0 < η) :
    ∃ ξ : Tagging P, ∀ i, cellSupremum f P hf i - η < f (ξ i) := by
  classical
  have hex (i : Fin P.n) : ∃ x : {x // x ∈ cell P i},
      cellSupremum f P hf i - η < f x := by
    obtain ⟨y, ⟨x, hx, rfl⟩, hy, _⟩ :=
      (cell_bounds f P hf i).2.exists_between (sub_lt_self _ hη)
    exact ⟨⟨x, hx⟩, hy⟩
  exact ⟨fun i => (hex i).choose, fun i => (hex i).choose_spec⟩

/-- Independent tags likewise approximate cell infima. -/
theorem exists_tag_near_infimum (f : ℝ → ℝ) {a b : ℝ} (P : Partition a b)
    (hf : BoundedOnInterval f a b) (η : ℝ) (hη : 0 < η) :
    ∃ ξ : Tagging P, ∀ i, f (ξ i) < cellInfimum f P hf i + η := by
  classical
  have hex (i : Fin P.n) : ∃ x : {x // x ∈ cell P i},
      f x < cellInfimum f P hf i + η := by
    obtain ⟨y, ⟨x, hx, rfl⟩, _, hy⟩ :=
      (cell_bounds f P hf i).1.exists_between (lt_add_of_pos_right _ hη)
    exact ⟨⟨x, hx⟩, hy⟩
  exact ⟨fun i => (hex i).choose, fun i => (hex i).choose_spec⟩

/-- Upper sums are approximated by tagged sums with error at most η(b-a). -/
theorem exists_tag_upper_error (f : ℝ → ℝ) {a b : ℝ} (P : Partition a b)
    (hf : BoundedOnInterval f a b) (η : ℝ) (hη : 0 < η) :
    ∃ ξ : Tagging P, upperSum f P hf - taggedSum P ξ f ≤ η * (b - a) := by
  obtain ⟨ξ, hξ⟩ := exists_tag_near_supremum f P hf η hη
  refine ⟨ξ, ?_⟩
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_right (show cellSupremum f P hf i - f (ξ i) ≤ η by
      linarith [hξ i]) (cell_positive P i).le)
  simpa only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_cellLength,
    upperSum, D.upperSumValue, taggedSum, S.sumValue, smul_eq_mul, mul_comm] using hs

theorem exists_tag_lower_error (f : ℝ → ℝ) {a b : ℝ} (P : Partition a b)
    (hf : BoundedOnInterval f a b) (η : ℝ) (hη : 0 < η) :
    ∃ ξ : Tagging P, taggedSum P ξ f - lowerSum f P hf ≤ η * (b - a) := by
  obtain ⟨ξ, hξ⟩ := exists_tag_near_infimum f P hf η hη
  refine ⟨ξ, ?_⟩
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_right (show f (ξ i) - cellInfimum f P hf i ≤ η by
      linarith [hξ i]) (cell_positive P i).le)
  simpa only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_cellLength,
    lowerSum, D.lowerSumValue, taggedSum, S.sumValue, smul_eq_mul, mul_comm] using hs

/-- The converse uses two separate taggings of one fine partition. -/
theorem realIntegrable_of_fineTaggedLimit (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : BoundedOnInterval f a b) (I : ℝ) (h : FineTaggedLimit f a b I) :
    RealIntegrable f a b := by
  apply (darboux_criterion f hab hf).mpr
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := h (ε / 4) (by positivity)
  obtain ⟨P, _, hP⟩ := arbitrarily_fine hab δ hδ
  let η := ε / (8 * (b - a))
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) (sub_pos.mpr hab))
  obtain ⟨ξ, hξ⟩ := exists_tag_upper_error f P hf η hη
  obtain ⟨ζ, hζ⟩ := exists_tag_lower_error f P hf η hη
  have hu := hclose P ξ hP
  have hl := hclose P ζ hP
  rw [Real.norm_eq_abs] at hu hl
  have he : η * (b - a) = ε / 8 := by dsimp [η]; field_simp
  refine ⟨P, ?_⟩
  rw [he] at hξ hζ
  have hu' := (abs_lt.mp hu).2
  have hl' := (abs_lt.mp hl).1
  linarith

/-- There are tagged partitions below every positive mesh threshold. -/
theorem exists_fine_partition {a b : ℝ} (hab : a ≤ b) (δ : ℝ) (hδ : 0 < δ) :
    ∃ P : Partition a b, mesh P < δ := by
  rcases lt_or_eq_of_le hab with hab | rfl
  · obtain ⟨P, _, hP⟩ := arbitrarily_fine hab δ hδ
    exact ⟨P, hP⟩
  · exact ⟨emptyPartition a, lt_of_eq_of_lt (degenerate_all a (emptyPartition a)).2 hδ⟩

/-- A common fine-mesh limit is unique because fine partitions actually exist. -/
theorem fineTaggedLimit_unique {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) {I J : E}
    (hI : FineTaggedLimit f a b I) (hJ : FineTaggedLimit f a b J) : I = J := by
  by_contra hne
  have hpos : 0 < ‖I - J‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨δI, hδI, hcI⟩ := hI (‖I - J‖ / 2) (half_pos hpos)
  obtain ⟨δJ, hδJ, hcJ⟩ := hJ (‖I - J‖ / 2) (half_pos hpos)
  obtain ⟨P, hP⟩ := exists_fine_partition hab (min δI δJ) (lt_min hδI hδJ)
  obtain ⟨ξ⟩ := tags_exist P
  have hi := hcI P ξ (hP.trans_le (min_le_left _ _))
  have hj := hcJ P ξ (hP.trans_le (min_le_right _ _))
  have ht := norm_sub_le_norm_sub_add_norm_sub I (taggedSum P ξ f) J
  rw [norm_sub_rev I (taggedSum P ξ f)] at ht
  linarith

theorem degenerate_tagged_limit :
    Specs.SingleVariableAnalysis.Ch08.TaggedEquivalence.degenerateTaggedLimit := by
  intro E _ _ f a I
  constructor
  · intro h
    by_contra hne
    have hp : 0 < ‖I‖ := norm_pos_iff.mpr hne
    obtain ⟨δ, hδ, hc⟩ := h ‖I‖ hp
    obtain ⟨ξ⟩ := tags_exist (emptyPartition a)
    have ht := hc (emptyPartition a) ξ
      (by rw [(degenerate_all a _).2]; exact hδ)
    rw [degenerate_sum a _ ξ f, zero_sub, norm_neg] at ht
    exact (lt_irrefl _ ht)
  · rintro rfl ε hε
    refine ⟨1, zero_lt_one, ?_⟩
    intro P ξ _
    rw [degenerate_sum a P ξ f, sub_self, norm_zero]
    exact hε

theorem real_tagged_equivalence :
    Specs.SingleVariableAnalysis.Ch08.TaggedEquivalence.realTaggedEquivalence := by
  intro f a b hab hf I
  rcases lt_or_eq_of_le hab with hab | rfl
  · constructor
    · rintro ⟨hi, hI⟩ ε hε
      simpa only [Real.norm_eq_abs] using tagged_forward f hab hf hi I hI ε hε
    · intro h
      have hi := realIntegrable_of_fineTaggedLimit f hab hf I h
      refine ⟨hi, fineTaggedLimit_unique hab.le ?_ h⟩
      intro ε hε
      simpa only [Real.norm_eq_abs] using
        tagged_forward f hab hf hi (realIntegral f hi) rfl ε hε
  · rw [degenerate_tagged_limit f a I]
    constructor
    · rintro ⟨hi, hI⟩
      exact hI.symm.trans (realIntegral_degenerate f a hi)
    · rintro rfl
      exact ⟨realIntegrable_degenerate f a, realIntegral_degenerate f a _⟩

/-- Taking a component commutes with each finite tagged sum. -/
theorem taggedSum_re (f : ℝ → ℂ) {a b : ℝ} (P : Partition a b) (ξ : Tagging P) :
    (taggedSum P ξ f).re = taggedSum P ξ (fun x => (f x).re) := by
  simp [taggedSum, S.sumValue]

theorem taggedSum_im (f : ℝ → ℂ) {a b : ℝ} (P : Partition a b) (ξ : Tagging P) :
    (taggedSum P ξ f).im = taggedSum P ξ (fun x => (f x).im) := by
  simp [taggedSum, S.sumValue]

theorem complex_tagged_componentwise :
    Specs.SingleVariableAnalysis.Ch08.TaggedEquivalence.complexTaggedComponentwise := by
  intro f a b I
  constructor
  · intro h
    constructor
    · intro ε hε
      obtain ⟨δ, hδ, hc⟩ := h ε hε
      refine ⟨δ, hδ, fun P ξ hP => ?_⟩
      have ht := (Complex.abs_re_le_norm (taggedSum P ξ f - I)).trans_lt (hc P ξ hP)
      simpa only [Real.norm_eq_abs, Complex.sub_re, taggedSum_re] using ht
    · intro ε hε
      obtain ⟨δ, hδ, hc⟩ := h ε hε
      refine ⟨δ, hδ, fun P ξ hP => ?_⟩
      have ht := (Complex.abs_im_le_norm (taggedSum P ξ f - I)).trans_lt (hc P ξ hP)
      simpa only [Real.norm_eq_abs, Complex.sub_im, taggedSum_im] using ht
  · rintro ⟨hr, hi⟩ ε hε
    obtain ⟨δr, hδr, hcr⟩ := hr (ε / 2) (half_pos hε)
    obtain ⟨δi, hδi, hci⟩ := hi (ε / 2) (half_pos hε)
    refine ⟨min δr δi, lt_min hδr hδi, ?_⟩
    intro P ξ hP
    have hr' := hcr P ξ (hP.trans_le (min_le_left _ _))
    have hi' := hci P ξ (hP.trans_le (min_le_right _ _))
    have ht := Complex.norm_le_abs_re_add_abs_im (taggedSum P ξ f - I)
    simp only [Real.norm_eq_abs] at hr' hi'
    simp only [Complex.sub_re, Complex.sub_im, taggedSum_re, taggedSum_im] at ht
    linarith

/-- A modulus bound bounds both real components above and below. -/
theorem complex_components_bounded (f : ℝ → ℂ) {a b : ℝ}
    (hf : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M) :
    BoundedOnInterval (fun x => (f x).re) a b ∧
    BoundedOnInterval (fun x => (f x).im) a b := by
  obtain ⟨M, hM⟩ := hf
  have hr (x : ℝ) (hx : x ∈ Set.Icc a b) : |(f x).re| ≤ M :=
    (Complex.abs_re_le_norm _).trans (hM x hx)
  have hi (x : ℝ) (hx : x ∈ Set.Icc a b) : |(f x).im| ≤ M :=
    (Complex.abs_im_le_norm _).trans (hM x hx)
  constructor
  · exact ⟨⟨-M, by rintro _ ⟨x, hx, rfl⟩; exact (abs_le.mp (hr x hx)).1⟩,
      ⟨M, by rintro _ ⟨x, hx, rfl⟩; exact (abs_le.mp (hr x hx)).2⟩⟩
  · exact ⟨⟨-M, by rintro _ ⟨x, hx, rfl⟩; exact (abs_le.mp (hi x hx)).1⟩,
      ⟨M, by rintro _ ⟨x, hx, rfl⟩; exact (abs_le.mp (hi x hx)).2⟩⟩

theorem complex_tagged_equivalence :
    Specs.SingleVariableAnalysis.Ch08.TaggedEquivalence.complexTaggedEquivalence := by
  intro f a b hab hf I
  obtain ⟨hfr, hfi⟩ := complex_components_bounded f hf
  rw [complex_tagged_componentwise]
  constructor
  · rintro ⟨hi, hI⟩
    have hv := complexIntegral_components f hi
    rw [hI] at hv
    exact ⟨(real_tagged_equivalence _ hab hfr I.re).mp ⟨hi.1, hv.1.symm⟩,
      (real_tagged_equivalence _ hab hfi I.im).mp ⟨hi.2, hv.2.symm⟩⟩
  · rintro ⟨hr, hi⟩
    obtain ⟨hir, hIr⟩ := (real_tagged_equivalence _ hab hfr I.re).mpr hr
    obtain ⟨hii, hIi⟩ := (real_tagged_equivalence _ hab hfi I.im).mpr hi
    refine ⟨⟨hir, hii⟩, ?_⟩
    apply Complex.ext
    · exact (complexIntegral_components f ⟨hir, hii⟩).1.trans hIr
    · exact (complexIntegral_components f ⟨hir, hii⟩).2.trans hIi

end SingleVariableAnalysis.Riemann
