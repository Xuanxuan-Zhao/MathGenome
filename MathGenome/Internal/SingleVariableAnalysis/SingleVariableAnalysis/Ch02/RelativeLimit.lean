import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.SequenceLimit
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.RelativeLimit

/-!
# Limits relative to a domain

Implements K03.02.relative_limit (paper.tex:361–376). The metric formulation
applies in particular to every real/complex domain and scalar target; the four
explicit scalar bridges below give exactly the manuscript's absolute-value
and modulus formulas. Functions are represented on the ambient space, but only
their restriction to E away from a is ever used (see the congruence theorem).

The neighborhood filter is restricted to E minus {a}, not merely to E. A limit
is allowed to be vacuous. Accumulation is precisely the extra nontriviality
condition that makes its value unique.
-/

namespace SingleVariableAnalysis

open scoped Topology
universe u v

/-- Every positive-radius punctured ball about a meets E. -/
def DomainAccumulation {X : Type u} [MetricSpace X] (E : Set X) (a : X) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ x ∈ E, 0 < dist x a ∧ dist x a < δ

/-- The approach to a within E excludes a itself, whether or not a belongs to E. -/
def PuncturedDomainFilter {X : Type u} [MetricSpace X] (E : Set X) (a : X) : Filter X :=
  nhdsWithin a (E \ {a})

/-- Finite epsilon–delta limit, without an implicit accumulation assumption. -/
def RelativePuncturedLimit {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : X) (L : Y) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ E, 0 < dist x a → dist x a < δ → dist (f x) L < ε

theorem domainAccumulation_filter_iff {X : Type u} [MetricSpace X] (E : Set X) (a : X) :
    DomainAccumulation E a ↔ (PuncturedDomainFilter E a).NeBot := by
  change DomainAccumulation E a ↔ (nhdsWithin a (E \ {a})).NeBot
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  constructor
  · intro h δ hδ
    obtain ⟨x, hx, hp, hd⟩ := h δ hδ
    exact ⟨x, ⟨hx, by simpa using (dist_pos.mp hp)⟩, by simpa [dist_comm] using hd⟩
  · intro h δ hδ
    obtain ⟨x, ⟨hx, hxa⟩, hd⟩ := h δ hδ
    exact ⟨x, hx, dist_pos.mpr (by simpa using hxa), by simpa [dist_comm] using hd⟩

theorem relativePuncturedLimit_filter_iff {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] (f : X → Y) (E : Set X) (a : X) (L : Y) :
    RelativePuncturedLimit f E a L ↔
      Filter.Tendsto f (PuncturedDomainFilter E a) (𝓝 L) := by
  change RelativePuncturedLimit f E a L ↔ Filter.Tendsto f (nhdsWithin a (E \ {a})) (𝓝 L)
  rw [Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hball⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx hd => hball x hx.1
      (dist_pos.mpr (by simpa using hx.2)) hd⟩
  · intro h ε hε
    obtain ⟨δ, hδ, hball⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx hp hd => hball
      ⟨hx, by simpa using (dist_pos.mp hp)⟩ hd⟩

/-- Two errors strictly smaller than half the distance contradict the triangle inequality. -/
theorem relativePuncturedLimit_unique {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] (f : X → Y) (E : Set X) (a : X) (L M : Y)
    (ha : DomainAccumulation E a) (hL : RelativePuncturedLimit f E a L)
    (hM : RelativePuncturedLimit f E a M) : L = M := by
  by_contra hne
  have hp : 0 < dist L M / 2 := half_pos (dist_pos.mpr hne)
  obtain ⟨δL, hδL, hbL⟩ := hL _ hp
  obtain ⟨δM, hδM, hbM⟩ := hM _ hp
  obtain ⟨x, hx, hxa, hδx⟩ := ha (min δL δM) (lt_min hδL hδM)
  have h1 := hbL x hx hxa (lt_of_lt_of_le hδx (min_le_left _ _))
  have h2 := hbM x hx hxa (lt_of_lt_of_le hδx (min_le_right _ _))
  have hlt : dist L M < dist L M := calc
    dist L M ≤ dist L (f x) + dist (f x) M := dist_triangle _ _ _
    _ < dist L M / 2 + dist L M / 2 := add_lt_add (by simpa [dist_comm] using h1) h2
    _ = dist L M := add_halves _
  exact (lt_irrefl _ hlt)

/-- A punctured neighborhood with no approach point makes every candidate a limit. -/
theorem relativePuncturedLimit_of_not_accumulation {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] (f : X → Y) (E : Set X) (a : X) (L : Y)
    (ha : ¬ DomainAccumulation E a) : RelativePuncturedLimit f E a L := by
  classical
  obtain ⟨δ, hδ⟩ := not_forall.mp ha
  obtain ⟨hδpos, hnone⟩ := not_imp.mp hδ
  exact fun ε _ => ⟨δ, hδpos, fun x hx hp hd => (hnone ⟨x, hx, hp, hd⟩).elim⟩

theorem relativePuncturedLimit_congr {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] (f g : X → Y) (E : Set X) (a : X) (L : Y)
    (hfg : ∀ x ∈ E, x ≠ a → f x = g x) :
    RelativePuncturedLimit f E a L ↔ RelativePuncturedLimit g E a L := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hb⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx hp hd => by
      rw [← hfg x hx (dist_pos.mp hp)]
      exact hb x hx hp hd⟩
  · intro h ε hε
    obtain ⟨δ, hδ, hb⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx hp hd => by
      rw [hfg x hx (dist_pos.mp hp)]
      exact hb x hx hp hd⟩

theorem real_domainAccumulation_iff (E : Set ℝ) (a : ℝ) :
    DomainAccumulation E a ↔
      ∀ δ : ℝ, 0 < δ → ∃ x ∈ E, 0 < |x - a| ∧ |x - a| < δ := by
  simp only [DomainAccumulation, Real.dist_eq]

theorem complex_domainAccumulation_iff (E : Set ℂ) (a : ℂ) :
    DomainAccumulation E a ↔
      ∀ δ : ℝ, 0 < δ → ∃ x ∈ E, 0 < ‖x - a‖ ∧ ‖x - a‖ < δ := by
  simp only [DomainAccumulation, dist_eq_norm]

theorem real_real_relativeLimit_iff (f : ℝ → ℝ) (E : Set ℝ) (a L : ℝ) :
    RelativePuncturedLimit f E a L ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, 0 < |x - a| → |x - a| < δ → |f x - L| < ε := by
  simp only [RelativePuncturedLimit, Real.dist_eq]

theorem real_complex_relativeLimit_iff (f : ℝ → ℂ) (E : Set ℝ) (a : ℝ) (L : ℂ) :
    RelativePuncturedLimit f E a L ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, 0 < |x - a| → |x - a| < δ → ‖f x - L‖ < ε := by
  simp only [RelativePuncturedLimit, dist_eq_norm, Real.norm_eq_abs]

theorem complex_real_relativeLimit_iff (f : ℂ → ℝ) (E : Set ℂ) (a : ℂ) (L : ℝ) :
    RelativePuncturedLimit f E a L ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, 0 < ‖x - a‖ → ‖x - a‖ < δ → |f x - L| < ε := by
  simp only [RelativePuncturedLimit, dist_eq_norm, Real.norm_eq_abs]

theorem complex_complex_relativeLimit_iff (f : ℂ → ℂ) (E : Set ℂ) (a L : ℂ) :
    RelativePuncturedLimit f E a L ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, 0 < ‖x - a‖ → ‖x - a‖ < δ → ‖f x - L‖ < ε := by
  simp only [RelativePuncturedLimit, dist_eq_norm]

private theorem singleton_not_accumulation {X : Type u} [MetricSpace X] (a : X) :
    ¬ DomainAccumulation ({a} : Set X) a := by
  intro h
  obtain ⟨x, hx, hp, _⟩ := h 1 zero_lt_one
  have heq : x = a := Set.mem_singleton_iff.mp hx
  subst x
  simp at hp

theorem real_vacuous_nonuniqueness :
    ¬ DomainAccumulation ({0} : Set ℝ) 0 ∧
      RelativePuncturedLimit (fun x : ℝ => x) {0} 0 0 ∧
      RelativePuncturedLimit (fun x : ℝ => x) {0} 0 1 ∧ (0 : ℝ) ≠ 1 := by
  have ha := singleton_not_accumulation (0 : ℝ)
  exact ⟨ha, relativePuncturedLimit_of_not_accumulation _ _ _ _ ha,
    relativePuncturedLimit_of_not_accumulation _ _ _ _ ha, zero_ne_one⟩

theorem complex_vacuous_nonuniqueness :
    ¬ DomainAccumulation ({0} : Set ℂ) 0 ∧
      RelativePuncturedLimit (fun z : ℂ => z) {0} 0 0 ∧
      RelativePuncturedLimit (fun z : ℂ => z) {0} 0 1 ∧ (0 : ℂ) ≠ 1 := by
  have ha := singleton_not_accumulation (0 : ℂ)
  exact ⟨ha, relativePuncturedLimit_of_not_accumulation _ _ _ _ ha,
    relativePuncturedLimit_of_not_accumulation _ _ _ _ ha, zero_ne_one⟩

end SingleVariableAnalysis
