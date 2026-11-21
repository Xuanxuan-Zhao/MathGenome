import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.RadixModel

/-! The finite real radix model of paper.tex, Definition W01. -/
namespace NumAnalysis206.Rounding

noncomputable def F : RadixFormat → Set ℝ := Specs.FValue
noncomputable def fl : RadixFormat → ℝ → ℝ := Specs.flValue
noncomputable def u : RadixFormat → ℝ := Specs.uValue
noncomputable def amin : RadixFormat → ℝ := Specs.aminValue
noncomputable def amax : RadixFormat → ℝ := Specs.amaxValue
def normalSafeDomain : RadixFormat → Set ℝ := Specs.safeDomainValue

theorem mem_positiveNormals (P : RadixFormat) (x : ℝ) :
    x ∈ P.positiveNormals ↔ ∃ m e : ℤ,
      P.β ^ (P.p - 1) ≤ m ∧ m < P.β ^ P.p ∧ P.emin ≤ e ∧ e ≤ P.emax ∧
      x = (m : ℝ) * (P.β : ℝ) ^ e := by
  classical
  simp [RadixFormat.positiveNormals, Finset.mem_product, Prod.exists, and_assoc, eq_comm]

theorem mem_positiveSubnormals (P : RadixFormat) (x : ℝ) :
    x ∈ P.positiveSubnormals ↔ ∃ m : ℤ,
      1 ≤ m ∧ m < P.β ^ (P.p - 1) ∧ x = (m : ℝ) * (P.β : ℝ) ^ P.emin := by
  classical
  simp [RadixFormat.positiveSubnormals, and_assoc, eq_comm]

theorem mem_positiveValues (P : RadixFormat) (x : ℝ) :
    x ∈ P.positiveValues ↔ x ∈ P.positiveNormals ∨
      (P.gradual = true ∧ x ∈ P.positiveSubnormals) := by
  classical
  cases h : P.gradual <;> simp [RadixFormat.positiveValues, h]

theorem mem_F (P : RadixFormat) (x : ℝ) :
    x ∈ F P ↔ x = 0 ∨
      (∃ m e : ℤ, P.β ^ (P.p - 1) ≤ m ∧ m < P.β ^ P.p ∧
        P.emin ≤ e ∧ e ≤ P.emax ∧
        (x = (m : ℝ) * (P.β : ℝ) ^ e ∨ x = -((m : ℝ) * (P.β : ℝ) ^ e))) ∨
      (P.gradual = true ∧ ∃ m : ℤ, 1 ≤ m ∧ m < P.β ^ (P.p - 1) ∧
        (x = (m : ℝ) * (P.β : ℝ) ^ P.emin ∨
         x = -((m : ℝ) * (P.β : ℝ) ^ P.emin))) := by
  classical
  have hsign : x ∈ F P ↔ x = 0 ∨ x ∈ P.positiveValues ∨ -x ∈ P.positiveValues := by
    simp [F, Specs.FValue, RadixFormat.numbers, neg_eq_iff_eq_neg]
  rw [hsign]
  simp only [mem_positiveValues, mem_positiveNormals, mem_positiveSubnormals]
  constructor
  · rintro (hzero | (hn | ⟨hg, hs⟩) | (hn | ⟨hg, hs⟩))
    · exact Or.inl hzero
    · obtain ⟨m, e, hm, hm', he, he', hx⟩ := hn
      exact Or.inr (Or.inl ⟨m, e, hm, hm', he, he', Or.inl hx⟩)
    · obtain ⟨m, hm, hm', hx⟩ := hs
      exact Or.inr (Or.inr ⟨hg, m, hm, hm', Or.inl hx⟩)
    · obtain ⟨m, e, hm, hm', he, he', hx⟩ := hn
      exact Or.inr (Or.inl ⟨m, e, hm, hm', he, he', Or.inr (neg_eq_iff_eq_neg.mp hx)⟩)
    · obtain ⟨m, hm, hm', hx⟩ := hs
      exact Or.inr (Or.inr ⟨hg, m, hm, hm', Or.inr (neg_eq_iff_eq_neg.mp hx)⟩)
  · rintro (hzero | hn | ⟨hg, hs⟩)
    · exact Or.inl hzero
    · obtain ⟨m, e, hm, hm', he, he', hx | hx⟩ := hn
      · exact Or.inr (Or.inl (Or.inl ⟨m, e, hm, hm', he, he', hx⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨m, e, hm, hm', he, he', neg_eq_iff_eq_neg.mpr hx⟩))
    · obtain ⟨m, hm, hm', hx | hx⟩ := hs
      · exact Or.inr (Or.inl (Or.inr ⟨hg, m, hm, hm', hx⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hg, m, hm, hm', neg_eq_iff_eq_neg.mpr hx⟩))

/-- Finite minimization, with the least minimizer resolving every tie. -/
theorem finiteNearest_spec (s : Finset ℝ) (hs : s.Nonempty) (x : ℝ) :
    finiteNearest s hs x ∈ s ∧
    (∀ y ∈ s, |x - finiteNearest s hs x| ≤ |x - y|) ∧
    (∀ y ∈ s, |x - y| = |x - finiteNearest s hs x| → finiteNearest s hs x ≤ y) := by
  classical
  let ds := s.image (fun y => |x - y|)
  let d := ds.min' (hs.image _)
  let t := s.filter (fun y => |x - y| = d)
  have ht : t.Nonempty := by
    obtain ⟨y, hy, hdy⟩ := Finset.mem_image.mp (Finset.min'_mem ds (hs.image _))
    exact ⟨y, Finset.mem_filter.mpr ⟨hy, hdy⟩⟩
  have hmem := Finset.mem_filter.mp (Finset.min'_mem t ht)
  change t.min' ht ∈ s ∧ _
  refine ⟨hmem.1, ?_, ?_⟩
  · intro y hy
    change |x - t.min' ht| ≤ |x - y|
    rw [hmem.2]
    exact Finset.min'_le ds _ (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  · intro y hy heq
    apply Finset.min'_le t y
    exact Finset.mem_filter.mpr ⟨hy, heq.trans hmem.2⟩

theorem F_finite (P : RadixFormat) : (F P).Finite :=
  Finset.finite_toSet P.numbers

@[simp] theorem zero_mem_F (P : RadixFormat) : (0 : ℝ) ∈ F P := by
  classical
  simp [F, Specs.FValue, RadixFormat.numbers]

theorem fl_mem_F (P : RadixFormat) (x : ℝ) : fl P x ∈ F P :=
  (finiteNearest_spec P.numbers ⟨0, zero_mem_F P⟩ x).1

theorem fl_minimizes (P : RadixFormat) (x y : ℝ) (hy : y ∈ F P) :
    |fl P x - x| ≤ |y - x| := by
  have h : |x - fl P x| ≤ |x - y| :=
    (finiteNearest_spec P.numbers ⟨0, zero_mem_F P⟩ x).2.1 y hy
  simpa only [abs_sub_comm] using h

theorem fl_tie (P : RadixFormat) (x y : ℝ) (hy : y ∈ F P)
    (heq : |y - x| = |fl P x - x|) : fl P x ≤ y := by
  apply (finiteNearest_spec P.numbers ⟨0, zero_mem_F P⟩ x).2.2 y hy
  change |x - y| = |x - fl P x|
  simpa only [abs_sub_comm] using heq

@[simp] theorem fl_fixes (P : RadixFormat) (x : ℝ) (hx : x ∈ F P) : fl P x = x := by
  have h := fl_minimizes P x x hx
  simpa only [sub_self, abs_zero, abs_nonpos_iff, sub_eq_zero] using h

/-- The same total rounding operation with its representable codomain explicit. -/
noncomputable def roundToFormat (P : RadixFormat) (x : ℝ) : {y : ℝ // y ∈ F P} :=
  ⟨fl P x, fl_mem_F P x⟩

end NumAnalysis206.Rounding
