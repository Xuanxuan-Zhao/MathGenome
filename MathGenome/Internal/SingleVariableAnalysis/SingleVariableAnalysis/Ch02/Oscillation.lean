import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.Oscillation

/-! # Oscillation on sets and at a point
K03.02.oscillation. The extended nonnegative codomain retains infinite
oscillations. The finite-limit assertions below explicitly include all four
real/complex domain and target choices.
-/
namespace SingleVariableAnalysis

open scoped ENNReal
universe u v

noncomputable def Oscillation {X : Type u} {Y : Type v} [MetricSpace Y]
    (f : X → Y) (A : Set X) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ | ∃ x ∈ A, ∃ y ∈ A, r = ENNReal.ofReal (dist (f x) (f y))}

noncomputable def PuncturedOscillation {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] (f : X → Y) (E : Set X) (a : X) : ℝ≥0∞ :=
  ⨅ δ : {r : ℝ // 0 < r},
    Oscillation f {x | x ∈ E ∧ 0 < dist x a ∧ dist x a < δ.val}

noncomputable def LocalOscillation {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] (f : X → Y) (E : Set X) (a : X) : ℝ≥0∞ :=
  ⨅ δ : {r : ℝ // 0 < r}, Oscillation f {x | x ∈ E ∧ dist x a < δ.val}

theorem oscillation_empty {X : Type u} {Y : Type v} [MetricSpace Y] (f : X → Y) :
    Oscillation f ∅ = 0 := by
  simp [Oscillation]

theorem oscillation_real_formula {X : Type u} (f : X → ℝ) (A : Set X) :
    Oscillation f A = sSup {r : ℝ≥0∞ | ∃ x ∈ A, ∃ y ∈ A,
      r = ENNReal.ofReal |f x - f y|} := by
  simp only [Oscillation, Real.dist_eq]

theorem oscillation_complex_formula {X : Type u} (f : X → ℂ) (A : Set X) :
    Oscillation f A = sSup {r : ℝ≥0∞ | ∃ x ∈ A, ∃ y ∈ A,
      r = ENNReal.ofReal ‖f x - f y‖} := by
  simp only [Oscillation, dist_eq_norm]

theorem distance_le_oscillation {X : Type u} {Y : Type v} [MetricSpace Y]
    (f : X → Y) (A : Set X) {x y : X} (hx : x ∈ A) (hy : y ∈ A) :
    ENNReal.ofReal (dist (f x) (f y)) ≤ Oscillation f A :=
  le_sSup ⟨x, hx, y, hy, rfl⟩

theorem oscillation_le {X : Type u} {Y : Type v} [MetricSpace Y]
    (f : X → Y) (A : Set X) (b : ℝ≥0∞)
    (h : ∀ x ∈ A, ∀ y ∈ A, ENNReal.ofReal (dist (f x) (f y)) ≤ b) :
    Oscillation f A ≤ b := by
  apply sSup_le
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact h x hx y hy

/-- Extended nonnegative infima vanish exactly when they are arbitrarily small.
No finiteness of the individual terms is assumed. -/
private theorem ennreal_iInf_eq_zero_iff {ι : Sort*} (b : ι → ℝ≥0∞) :
    (⨅ i, b i) = 0 ↔ ∀ ε : ℝ, 0 < ε → ∃ i, b i < ENNReal.ofReal ε := by
  constructor
  · intro h ε hε
    apply iInf_lt_iff.mp
    rw [h]
    exact ENNReal.ofReal_pos.mpr hε
  · intro h
    apply le_antisymm ?_ bot_le
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨i, hi⟩ := h ε hε
    simpa using (iInf_le b i).trans hi.le

/-- The half-tolerance in the reverse direction accounts for a supremum
of strict pointwise inequalities possibly attaining their upper bound. -/
theorem iInf_oscillation_eq_zero_iff {ι : Sort*} {X : Type u} {Y : Type v}
    [MetricSpace Y] (f : X → Y) (A : ι → Set X) :
    (⨅ i, Oscillation f (A i)) = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ i, ∀ x ∈ A i, ∀ y ∈ A i, dist (f x) (f y) < ε := by
  rw [ennreal_iInf_eq_zero_iff]
  constructor
  · intro h ε hε
    obtain ⟨i, hi⟩ := h ε hε
    exact ⟨i, fun x hx y hy => (ENNReal.ofReal_lt_ofReal_iff hε).mp
      ((distance_le_oscillation f (A i) hx hy).trans_lt hi)⟩
  · intro h ε hε
    obtain ⟨i, hi⟩ := h (ε / 2) (half_pos hε)
    refine ⟨i, (oscillation_le f (A i) _ ?_).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (half_lt_self hε))⟩
    intro x hx y hy
    exact ENNReal.ofReal_le_ofReal (hi x hx y hy).le

theorem puncturedOscillation_zero_iff_cauchy {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] (f : X → Y) (E : Set X) (a : X) :
    PuncturedOscillation f E a = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, 0 < dist x a → dist x a < δ →
          0 < dist y a → dist y a < δ → dist (f x) (f y) < ε := by
  unfold PuncturedOscillation
  rw [iInf_oscillation_eq_zero_iff]
  constructor
  · intro h ε hε
    obtain ⟨⟨δ, hδ⟩, hb⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx y hy hxp hxd hyp hyd =>
      hb x ⟨hx, hxp, hxd⟩ y ⟨hy, hyp, hyd⟩⟩
  · intro h ε hε
    obtain ⟨δ, hδ, hb⟩ := h ε hε
    exact ⟨⟨δ, hδ⟩, fun x hx y hy => hb x hx.1 y hy.1 hx.2.1 hx.2.2 hy.2.1 hy.2.2⟩

theorem real_real_puncturedOscillation_zero_iff_limit (f : ℝ → ℝ) (E : Set ℝ)
    (a : ℝ) (ha : DomainAccumulation E a) :
    PuncturedOscillation f E a = 0 ↔ ∃ L : ℝ, RelativePuncturedLimit f E a L := by
  rw [puncturedOscillation_zero_iff_cauchy]
  simpa only [Real.dist_eq] using (real_real_relativeLimit_cauchy_criterion f E a ha).symm

theorem real_complex_puncturedOscillation_zero_iff_limit (f : ℝ → ℂ) (E : Set ℝ)
    (a : ℝ) (ha : DomainAccumulation E a) :
    PuncturedOscillation f E a = 0 ↔ ∃ L : ℂ, RelativePuncturedLimit f E a L := by
  rw [puncturedOscillation_zero_iff_cauchy]
  simpa only [dist_eq_norm, Real.norm_eq_abs] using
    (real_complex_relativeLimit_cauchy_criterion f E a ha).symm

theorem complex_real_puncturedOscillation_zero_iff_limit (f : ℂ → ℝ) (E : Set ℂ)
    (a : ℂ) (ha : DomainAccumulation E a) :
    PuncturedOscillation f E a = 0 ↔ ∃ L : ℝ, RelativePuncturedLimit f E a L := by
  rw [puncturedOscillation_zero_iff_cauchy]
  simpa only [dist_eq_norm, Real.norm_eq_abs] using
    (complex_real_relativeLimit_cauchy_criterion f E a ha).symm

theorem complex_complex_puncturedOscillation_zero_iff_limit (f : ℂ → ℂ) (E : Set ℂ)
    (a : ℂ) (ha : DomainAccumulation E a) :
    PuncturedOscillation f E a = 0 ↔ ∃ L : ℂ, RelativePuncturedLimit f E a L := by
  rw [puncturedOscillation_zero_iff_cauchy]
  simpa only [dist_eq_norm] using
    (complex_complex_relativeLimit_cauchy_criterion f E a ha).symm

/-- Including the base point in the neighborhood makes small pairwise distances
control the difference from the actual value f(a), including isolated points. -/
theorem localOscillation_zero_iff_continuousWithinAt {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] (f : X → Y) (E : Set X) (a : X) (ha : a ∈ E) :
    LocalOscillation f E a = 0 ↔ ContinuousWithinAt f E a := by
  unfold LocalOscillation
  rw [iInf_oscillation_eq_zero_iff, Metric.continuousWithinAt_iff]
  constructor
  · intro h ε hε
    obtain ⟨⟨δ, hδ⟩, hb⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx hd => hb x ⟨hx, hd⟩ a ⟨ha, by simpa using hδ⟩⟩
  · intro h ε hε
    obtain ⟨δ, hδ, hb⟩ := h (ε / 2) (half_pos hε)
    refine ⟨⟨δ, hδ⟩, fun x hx y hy => ?_⟩
    calc
      dist (f x) (f y) ≤ dist (f x) (f a) + dist (f a) (f y) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hb hx.1 hx.2) (by
        simpa only [dist_comm] using hb hy.1 hy.2)
      _ = ε := add_halves ε

noncomputable def oscillationSpike (x : ℝ) : ℝ := if x = 0 then 1 else 0

theorem oscillationSpike_values : oscillationSpike 0 = 1 ∧
    ∀ x : ℝ, x ≠ 0 → oscillationSpike x = 0 := by
  simp [oscillationSpike]

theorem oscillationSpike_punctured :
    PuncturedOscillation oscillationSpike Set.univ 0 = 0 := by
  rw [puncturedOscillation_zero_iff_cauchy]
  intro ε hε
  refine ⟨1, zero_lt_one, fun x _ y _ hxp _ hyp _ => ?_⟩
  have hx : x ≠ 0 := dist_pos.mp hxp
  have hy : y ≠ 0 := dist_pos.mp hyp
  simpa [oscillationSpike, hx, hy] using hε

private theorem spike_distance_le_one (x y : ℝ) :
    ENNReal.ofReal (dist (oscillationSpike x) (oscillationSpike y)) ≤ 1 := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
    simp [oscillationSpike, hx, hy, Real.dist_eq]

/-- Every positive unpunctured ball contains both 0 and δ/2. These two
values differ by 1, and no two values differ by more than 1. -/
theorem oscillationSpike_local : LocalOscillation oscillationSpike Set.univ 0 = 1 := by
  apply le_antisymm
  · exact (iInf_le _ (⟨1, zero_lt_one⟩ : {r : ℝ // 0 < r})).trans
      (oscillation_le _ _ _ (fun x _ y _ => spike_distance_le_one x y))
  · apply le_iInf
    intro δ
    have hx : δ.val / 2 ≠ 0 := ne_of_gt (half_pos δ.property)
    have hmem : δ.val / 2 ∈ {x : ℝ | x ∈ Set.univ ∧ dist x 0 < δ.val} := by
      refine ⟨Set.mem_univ _, ?_⟩
      simpa [Real.dist_eq, abs_of_pos (half_pos δ.property)] using half_lt_self δ.property
    have hzero : (0 : ℝ) ∈ {x : ℝ | x ∈ Set.univ ∧ dist x 0 < δ.val} := by
      simpa using δ.property
    simpa [oscillationSpike, hx, Real.dist_eq] using
      distance_le_oscillation oscillationSpike _ hzero hmem

end SingleVariableAnalysis
