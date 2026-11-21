import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Rounding.Operations
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.Enclosures
import Mathlib.Tactic.Linarith

/-! One-round enclosures, paper.tex W03. -/
namespace NumAnalysis206.Rounding

/-- The endpoint order automatically handles positive, negative, and zero values. -/
theorem relative_enclosure (x z u δ : ℝ) (hu : 0 ≤ u) (hu1 : u < 1)
    (hδ : |δ| ≤ u) (hz : z = x * (1 + δ)) :
    min (z / (1 - u)) (z / (1 + u)) ≤ x ∧
      x ≤ max (z / (1 - u)) (z / (1 + u)) := by
  have hm : 0 < 1 - u := by linarith
  have hp : 0 < 1 + u := by linarith
  obtain ⟨hδl, hδr⟩ := abs_le.mp hδ
  rcases le_total 0 x with hx | hx
  · have hl : z / (1 + u) ≤ x := (div_le_iff₀ hp).mpr (by nlinarith)
    have hr : x ≤ z / (1 - u) := (le_div_iff₀ hm).mpr (by nlinarith)
    exact ⟨(min_le_right _ _).trans hl, hr.trans (le_max_left _ _)⟩
  · have hl : z / (1 - u) ≤ x := (div_le_iff₀ hm).mpr (by nlinarith)
    have hr : x ≤ z / (1 + u) := (le_div_iff₀ hp).mpr (by nlinarith)
    exact ⟨(min_le_left _ _).trans hl, hr.trans (le_max_right _ _)⟩

theorem relative_zero_exact (x z u δ : ℝ) (_hu : 0 ≤ u) (hu1 : u < 1)
    (hδ : |δ| ≤ u) (hz : z = x * (1 + δ)) (hz0 : z = 0) : x = 0 := by
  have hpos : 0 < 1 + δ := by
    have := (abs_le.mp hδ).1
    linarith
  exact (mul_eq_zero.mp (hz.symm.trans hz0)).resolve_right (ne_of_gt hpos)

theorem absolute_enclosure (x z η : ℝ) (_hη : 0 ≤ η) (h : |z - x| ≤ η) :
    x ∈ Set.Icc (z - η) (z + η) := by
  obtain ⟨hl, hr⟩ := abs_le.mp h
  constructor <;> linarith

theorem directed_enclosure (x zdown zup : ℝ) (hl : zdown ≤ x) (hr : x ≤ zup) :
    x ∈ Set.Icc zdown zup := ⟨hl, hr⟩

/-- Construct the lower directed point by a maximum of the filtered finite format. -/
theorem finite_directed_lower (P : RadixFormat) (x : ℝ)
    (h : {y : ℝ | y ∈ F P ∧ y ≤ x}.Nonempty) :
    ∃ zdown : ℝ, IsGreatest {y : ℝ | y ∈ F P ∧ y ≤ x} zdown := by
  classical
  let s := P.numbers.filter (fun y => y ≤ x)
  have hs : s.Nonempty := by
    obtain ⟨y, hy, hyx⟩ := h
    exact ⟨y, Finset.mem_filter.mpr ⟨hy, hyx⟩⟩
  refine ⟨s.max' hs, ?_, ?_⟩
  · exact Finset.mem_filter.mp (Finset.max'_mem s hs)
  · intro y hy
    exact Finset.le_max' s y (Finset.mem_filter.mpr hy)

/-- Construct the upper directed point by a minimum of the filtered finite format. -/
theorem finite_directed_upper (P : RadixFormat) (x : ℝ)
    (h : {y : ℝ | y ∈ F P ∧ x ≤ y}.Nonempty) :
    ∃ zup : ℝ, IsLeast {y : ℝ | y ∈ F P ∧ x ≤ y} zup := by
  classical
  let s := P.numbers.filter (fun y => x ≤ y)
  have hs : s.Nonempty := by
    obtain ⟨y, hy, hxy⟩ := h
    exact ⟨y, Finset.mem_filter.mpr ⟨hy, hxy⟩⟩
  refine ⟨s.min' hs, ?_, ?_⟩
  · exact Finset.mem_filter.mp (Finset.min'_mem s hs)
  · intro y hy
    exact Finset.min'_le s y (Finset.mem_filter.mpr hy)

theorem finite_directed_enclosure (P : RadixFormat) (x : ℝ)
    (hl : {y : ℝ | y ∈ F P ∧ y ≤ x}.Nonempty)
    (hr : {y : ℝ | y ∈ F P ∧ x ≤ y}.Nonempty) :
    ∃ zdown zup : ℝ,
      IsGreatest {y : ℝ | y ∈ F P ∧ y ≤ x} zdown ∧
      IsLeast {y : ℝ | y ∈ F P ∧ x ≤ y} zup ∧ x ∈ Set.Icc zdown zup := by
  obtain ⟨zdown, hd⟩ := finite_directed_lower P x hl
  obtain ⟨zup, hu⟩ := finite_directed_upper P x hr
  exact ⟨zdown, zup, hd, hu, directed_enclosure x zdown zup hd.1.2 hu.1.2⟩

theorem relativeModel_enclosure (round : ℝ → ℝ) (u : ℝ) (D : Set ℝ)
    (h : RelativeModel round u D) (x : ℝ) (hx : x ∈ D) :
    (min (round x / (1 - u)) (round x / (1 + u)) ≤ x ∧
      x ≤ max (round x / (1 - u)) (round x / (1 + u))) ∧
      (round x = 0 → x = 0) := by
  obtain ⟨δ, hz, hδ⟩ := relativeModel_error round u D h x hx
  exact ⟨relative_enclosure x (round x) u δ h.1 h.2.1 hδ hz,
    relative_zero_exact x (round x) u δ h.1 h.2.1 hδ hz⟩

end NumAnalysis206.Rounding
