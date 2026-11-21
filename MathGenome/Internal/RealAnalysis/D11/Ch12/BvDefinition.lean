import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.BvDefinition
import Mathlib.Analysis.Normed.Group.Uniform

namespace D11.Ch12
open Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E]

/-- The classical supremum over strict endpoint partitions. -/
noncomputable def variation (F : ℝ → E) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ p : IntervalPartition a b, partitionSum F p

/-- The variation function based at the left endpoint. -/
noncomputable def variationFunction (F : ℝ → E) (a : ℝ) : ℝ → ℝ≥0∞ :=
  fun x => variation F a x

/-- Bounded variation means finiteness of the classical variation. -/
def BV (F : ℝ → E) (a b : ℝ) : Prop := variation F a b < ⊤

private lemma append_endpoint (F : ℝ → E) {n : ℕ} {u : ℕ → ℝ} {b : ℝ}
    (hu : StrictMonoOn u (Iic n)) (hb : u n ≤ b) :
    ∃ (m : ℕ) (v : ℕ → ℝ), StrictMonoOn v (Iic m) ∧ v 0 = u 0 ∧ v m = b ∧
      (∑ i ∈ Finset.range n, edist (F (u (i + 1))) (F (u i))) ≤
        ∑ i ∈ Finset.range m, edist (F (v (i + 1))) (F (v i)) := by
  rcases hb.eq_or_lt with hb | hb
  · exact ⟨n, u, hu, rfl, hb, le_rfl⟩
  · let v : ℕ → ℝ := fun i => if i ≤ n then u i else b
    refine ⟨n + 1, v, ?_, by simp [v], by simp [v], ?_⟩
    · intro i hi j hj hij
      dsimp [v]
      split_ifs with h₁ h₂
      · exact hu (by simpa using h₁) (by simpa using h₂) hij
      · have h : u i ≤ u n := hu.monotoneOn (by simpa using h₁) (by simp) h₁
        exact h.trans_lt hb
      · omega
      · simp only [mem_Iic] at hi hj
        omega
    · rw [Finset.sum_range_succ]
      have hsum : (∑ i ∈ Finset.range n, edist (F (u (i + 1))) (F (u i))) =
          ∑ i ∈ Finset.range n, edist (F (v (i + 1))) (F (v i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_range] at hi
        simp [v, show i ≤ n by omega, show i + 1 ≤ n by omega]
      rw [hsum]
      exact le_self_add

private lemma prepend_endpoint (F : ℝ → E) {n : ℕ} {u : ℕ → ℝ} {a : ℝ}
    (hu : StrictMonoOn u (Iic n)) (ha : a ≤ u 0) :
    ∃ (m : ℕ) (v : ℕ → ℝ), StrictMonoOn v (Iic m) ∧ v 0 = a ∧ v m = u n ∧
      (∑ i ∈ Finset.range n, edist (F (u (i + 1))) (F (u i))) ≤
        ∑ i ∈ Finset.range m, edist (F (v (i + 1))) (F (v i)) := by
  rcases ha.eq_or_lt with ha | ha
  · exact ⟨n, u, hu, ha.symm, rfl, le_rfl⟩
  · let v : ℕ → ℝ := fun i => if i = 0 then a else u (i - 1)
    refine ⟨n + 1, v, ?_, by simp [v], by simp [v], ?_⟩
    · intro i hi j hj hij
      simp only [mem_Iic] at hi hj
      dsimp [v]
      split_ifs with h₁ h₂
      · omega
      · exact ha.trans_le (hu.monotoneOn (by simp) (by simp; omega) (by omega))
      · omega
      · apply hu (by simp; omega) (by simp; omega)
        omega
    · rw [Finset.sum_range_succ']
      have hsum : (∑ i ∈ Finset.range n, edist (F (u (i + 1))) (F (u i))) =
          ∑ i ∈ Finset.range n, edist (F (v (i + 1 + 1))) (F (v (i + 1))) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [v]
      rw [hsum]
      exact le_self_add

/-- The definition agrees with Mathlib without a finiteness assumption. -/
theorem variation_eq_eVariationOn (F : ℝ → E) (a b : ℝ) :
    variation F a b = eVariationOn F (Icc a b) := by
  apply le_antisymm
  · apply iSup_le
    intro p
    simp only [partitionSum, ← edist_eq_enorm_sub]
    apply eVariationOn.sum_le_of_monotoneOn_Iic p.strictMono.monotoneOn
    intro i hi
    constructor
    · simpa only [p.start] using
        p.strictMono.monotoneOn (by simp) (by simpa using hi) (Nat.zero_le _)
    · simpa only [p.finish] using
        p.strictMono.monotoneOn (by simpa using hi) (by simp) hi
  · rw [eVariationOn.eVariationOn_eq_strictMonoOn]
    apply iSup_le
    rintro ⟨n, u, hu, hus⟩
    obtain ⟨m, v, hv, hv₀, hvm, hsum₁⟩ := append_endpoint F hu (hus n (by simp)).2
    obtain ⟨k, w, hw, hw₀, hwk, hsum₂⟩ := prepend_endpoint F (a := a) hv
      (by rw [hv₀]; exact (hus 0 (by simp)).1)
    let p : IntervalPartition a b := ⟨k, w, hw, hw₀, hwk.trans hvm⟩
    exact (hsum₁.trans hsum₂).trans (le_iSup_of_le p (by simp [partitionSum, p, edist_eq_enorm_sub]))

theorem variation_self (F : ℝ → E) (a : ℝ) : variation F a a = 0 := by
  rw [variation_eq_eVariationOn]
  simp

theorem variation_additive (F : ℝ → E) {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    variation F a b = variation F a c + variation F c b := by
  simp only [variation_eq_eVariationOn]
  simpa using (eVariationOn.Icc_add_Icc F (s := univ) hac hcb (mem_univ c)).symm

theorem variation_add_le (F G : ℝ → E) (a b : ℝ) :
    variation (fun x => F x + G x) a b ≤ variation F a b + variation G a b := by
  apply iSup_le
  intro p
  calc
    partitionSum (fun x => F x + G x) p ≤ partitionSum F p + partitionSum G p := by
      simp only [partitionSum, ← edist_eq_enorm_sub, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i hi => edist_add_add_le _ _ _ _
    _ ≤ variation F a b + variation G a b :=
      add_le_add (le_iSup (partitionSum F) p) (le_iSup (partitionSum G) p)

theorem variation_sub_le (F G : ℝ → E) (a b : ℝ) :
    variation (fun x => F x - G x) a b ≤ variation F a b + variation G a b := by
  apply iSup_le
  intro p
  calc
    partitionSum (fun x => F x - G x) p ≤ partitionSum F p + partitionSum G p := by
      simp only [partitionSum, ← edist_eq_enorm_sub, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i hi
      simpa only [sub_eq_add_neg, edist_neg_neg] using
        edist_add_add_le (F (p.point (i + 1))) (-G (p.point (i + 1)))
          (F (p.point i)) (-G (p.point i))
    _ ≤ variation F a b + variation G a b :=
      add_le_add (le_iSup (partitionSum F) p) (le_iSup (partitionSum G) p)

theorem enorm_sub_le_variation (F : ℝ → E) {x y : ℝ} (hxy : x ≤ y) :
    ‖F y - F x‖ₑ ≤ variation F x y := by
  rw [variation_eq_eVariationOn, ← edist_eq_enorm_sub]
  exact eVariationOn.edist_le F ⟨hxy, le_rfl⟩ ⟨le_rfl, hxy⟩

theorem bv_iff_boundedVariationOn (F : ℝ → E) (a b : ℝ) :
    BV F a b ↔ BoundedVariationOn F (Icc a b) := by
  simp [BV, variation_eq_eVariationOn, BoundedVariationOn, lt_top_iff_ne_top]

theorem norm_sub_le_variation (F : ℝ → E) {x y : ℝ} (hxy : x ≤ y) (hf : BV F x y) :
    ‖F y - F x‖ ≤ (variation F x y).toReal := by
  rw [variation_eq_eVariationOn, ← dist_eq_norm]
  exact ((bv_iff_boundedVariationOn F x y).mp hf).dist_le ⟨hxy, le_rfl⟩ ⟨le_rfl, hxy⟩

theorem variation_congr {F G : ℝ → E} {a b : ℝ} (h : EqOn F G (Icc a b)) :
    variation F a b = variation G a b := by
  simp only [variation_eq_eVariationOn]
  exact eVariationOn.congr h

theorem variation_restrict (F : ℝ → E) (a b : ℝ) :
    eVariationOn (fun x : Icc a b => F x) univ = variation F a b := by
  rw [variation_eq_eVariationOn]
  convert eVariationOn.comp_eq_of_monotoneOn F
    (fun x : Icc a b => (x : ℝ)) (t := univ) (by intro x hx y hy h; exact h) using 2
  · rfl
  · ext x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, mem_univ _, rfl⟩
    · rintro ⟨y, _, rfl⟩
      exact y.property

/-- Interval-domain functions have an ambient representative with the same
variation. This also works for a degenerate or empty interval. -/
theorem interval_domain_extension (a b : ℝ) (F : Icc a b → E) :
    ∃ G : ℝ → E, (∀ x : Icc a b, G x = F x) ∧
      variation G a b = eVariationOn F univ := by
  let G : ℝ → E := fun x => if hx : x ∈ Icc a b then F ⟨x, hx⟩ else 0
  have heq (x : Icc a b) : G x = F x := by simp only [G, dite_eq_left x.property]
  refine ⟨G, heq, ?_⟩
  rw [← variation_restrict]
  exact eVariationOn.congr (fun x _ => heq x)

end D11.Ch12
