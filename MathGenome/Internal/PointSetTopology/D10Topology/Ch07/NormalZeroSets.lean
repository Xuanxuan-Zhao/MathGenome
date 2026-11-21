import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.NormalZeroSets
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.UrysohnSeparation
import Mathlib.Topology.Separation.GDelta
import Mathlib.Tactic.Positivity

/-! Exact zero sets and exact Urysohn fibers (paper.tex, d10:07:zero-sets). -/

open Set
universe u

namespace D10Topology.Ch07

variable (X : Type u) [TopologicalSpace X]

/-- A summable positive combination of Urysohn functions detects the complement
of a closed G_delta set. The geometric majorant also keeps its range in [0,1]. -/
private theorem exists_real_zero_fiber_of_closed_gdelta (hN : Normal X)
    (A : Set X) (hA : IsClosed A) (hG : GDelta A) :
    ∃ g : C(X, ℝ), g ⁻¹' {0} = A ∧ ∀ x, g x ∈ Icc (0 : ℝ) 1 := by
  let : NormalSpace X := hN
  obtain ⟨U, ho, hu⟩ := isGδ_iff_eq_iInter_nat.mp hG
  have hd (n : ℕ) : Disjoint A (U n)ᶜ := by
    apply LE.le.disjoint_compl_right
    rw [hu]
    exact iInter_subset U n
  choose f hfA hfU hfr using fun n =>
    exists_continuous_zero_one_of_isClosed hA (ho n).isClosed_compl (hd n)
  have hbound (x : X) (n : ℕ) : ‖f n x * (1 / 2 / 2 ^ n)‖ ≤ (1 / 2 / 2 ^ n : ℝ) := by
    simp [abs_of_nonneg (hfr n x).1, (hfr n x).2]
  have hsum (x : X) : Summable fun n => f n x * (1 / 2 / 2 ^ n) :=
    (summable_geometric_two' 1).of_norm_bounded fun n => hbound x n
  let g : C(X, ℝ) :=
    { toFun x := ∑' n, f n x * (1 / 2 / 2 ^ n)
      continuous_toFun := continuous_tsum
        (fun n => (f n).continuous.mul continuous_const)
        (summable_geometric_two' 1) fun n x => hbound x n }
  have hnonneg (x : X) (n : ℕ) : 0 ≤ f n x * (1 / 2 / 2 ^ n) := by
    positivity [(hfr n x).1]
  refine ⟨g, ?_, fun x => ⟨tsum_nonneg (hnonneg x), ?_⟩⟩
  · ext x
    constructor
    · intro hx
      change g x = 0 at hx
      by_contra hxA
      obtain ⟨n, hn⟩ : ∃ n, x ∉ U n := by
        by_contra h
        apply hxA
        rw [hu]
        exact mem_iInter.mpr fun n => by simpa using not_exists.mp h n
      have hpos : 0 < g x := calc
        0 < (1 / 2 / 2 ^ n : ℝ) := by positivity
        _ = f n x * (1 / 2 / 2 ^ n) := by simp [hfU n hn]
        _ ≤ g x := (hsum x).le_tsum n (fun j _ => hnonneg x j)
      exact (ne_of_gt hpos) hx
    · intro hx
      change (∑' n, f n x * (1 / 2 / 2 ^ n)) = 0
      simp [fun n => hfA n hx]
  · calc
      g x = ∑' n, f n x * (1 / 2 / 2 ^ n) := rfl
      _ ≤ ∑' n, (1 / 2 / 2 ^ n : ℝ) :=
        (hsum x).tsum_le_tsum (fun n => by simp [(hfr n x).2]) (summable_geometric_two' 1)
      _ = 1 := tsum_geometric_two' 1

/-- Normality has no T1 assumption. No nonemptiness is required of X or A. -/
theorem closed_gdelta_iff_zero_fiber (hN : Normal X) (A : Set X) (hA : IsClosed A) :
    GDelta A ↔ ∃ g : X → unitInterval, Continuous g ∧ g ⁻¹' {0} = A := by
  constructor
  · intro hG
    obtain ⟨g, hgA, hgI⟩ := exists_real_zero_fiber_of_closed_gdelta X hN A hA hG
    refine ⟨fun x => ⟨g x, hgI x⟩, g.continuous.subtype_mk _, ?_⟩
    ext x
    simpa only [mem_preimage, mem_singleton_iff, Subtype.ext_iff, Set.Icc.coe_zero] using
      Set.ext_iff.mp hgA x
  · rintro ⟨g, hg, rfl⟩
    exact (IsGδ.singleton (0 : unitInterval)).preimage hg

/-- Positive denominator normalization gives both exact fibers, also when either
closed set is empty. Disjointness excludes simultaneous zeros pointwise. -/
theorem normal_exact_zero_one_fibers (hN : Normal X)
    (hG : ∀ F : Set X, IsClosed F → GDelta F)
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (hd : Disjoint A B) :
    ∃ f : X → unitInterval, Continuous f ∧ f ⁻¹' {0} = A ∧ f ⁻¹' {1} = B := by
  obtain ⟨a, ha, haA⟩ := (closed_gdelta_iff_zero_fiber X hN A hA).mp (hG A hA)
  obtain ⟨b, hb, hbB⟩ := (closed_gdelta_iff_zero_fiber X hN B hB).mp (hG B hB)
  have ha0 (x : X) : (a x : ℝ) = 0 ↔ x ∈ A := by
    simpa only [mem_preimage, mem_singleton_iff, Subtype.ext_iff, Set.Icc.coe_zero] using Set.ext_iff.mp haA x
  have hb0 (x : X) : (b x : ℝ) = 0 ↔ x ∈ B := by
    simpa only [mem_preimage, mem_singleton_iff, Subtype.ext_iff, Set.Icc.coe_zero] using Set.ext_iff.mp hbB x
  have hden (x : X) : 0 < (a x : ℝ) + (b x : ℝ) := by
    have hna := (a x).property.1
    have hnb := (b x).property.1
    have hn : (a x : ℝ) ≠ 0 ∨ (b x : ℝ) ≠ 0 := by
      by_contra h
      push Not at h
      exact Set.disjoint_left.mp hd ((ha0 x).mp h.1) ((hb0 x).mp h.2)
    rcases hn with hn | hn
    · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hna (Ne.symm hn)) hnb
    · exact add_pos_of_nonneg_of_pos hna (lt_of_le_of_ne hnb (Ne.symm hn))
  let f : X → ℝ := fun x => (a x : ℝ) / ((a x : ℝ) + (b x : ℝ))
  have hf : Continuous f :=
    (continuous_subtype_val.comp ha).div₀
      ((continuous_subtype_val.comp ha).add (continuous_subtype_val.comp hb))
      (fun x => ne_of_gt (hden x))
  have hfI (x : X) : f x ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (a x).property.1 (hden x).le, ?_⟩
    exact (div_le_one (hden x)).mpr (le_add_of_nonneg_right (b x).property.1)
  refine ⟨fun x => ⟨f x, hfI x⟩, hf.subtype_mk _, ?_, ?_⟩
  · ext x
    change (⟨f x, hfI x⟩ : unitInterval) = 0 ↔ x ∈ A
    rw [Subtype.ext_iff]
    change f x = 0 ↔ x ∈ A
    simp only [f, div_eq_zero_iff, ne_of_gt (hden x), or_false, ha0 x]
  · ext x
    change (⟨f x, hfI x⟩ : unitInterval) = 1 ↔ x ∈ B
    rw [Subtype.ext_iff]
    change f x = 1 ↔ x ∈ B
    rw [show f x = 1 ↔ (a x : ℝ) = (a x : ℝ) + (b x : ℝ) from
      div_eq_one_iff_eq (ne_of_gt (hden x))]
    simpa using hb0 x

end D10Topology.Ch07
