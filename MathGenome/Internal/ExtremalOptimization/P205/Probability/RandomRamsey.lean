import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.RandomRamsey
import MathGenome.Internal.ExtremalOptimization.P205.Probability.FiniteModels
import MathGenome.Internal.ExtremalOptimization.P205.Probability.UnionBound
import MathGenome.Internal.ExtremalOptimization.P205.Ramsey.GraphNumbers
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The random-coloring lower bound, paper.tex 799–824 (W16).
The experiment reuses the canonical finite product and the chapter-3 Ramsey number.
The signed integer exponent in the criterion is kept distinct from the real
exponent in its quantitative corollary. -/

open MeasureTheory
open scoped BigOperators Classical

namespace P205.Probability.RandomRamsey
open P205.Ramsey

-- The finite bit spaces and coloring spaces use their full powerset sigma algebras.
local instance bitMeasurableSpace : MeasurableSpace (Fin 2) := ⊤
local instance bitMeasurableSingleton : MeasurableSingletonClass (Fin 2) := ⟨fun _ => trivial⟩

theorem independent_edges : Specs.IndependentEdges := by
  intro n
  exact FiniteModel.independent_coordinates (fun _ : Edge n => fairBit)

theorem fair_edge : Specs.FairEdge := by
  intro n e d
  change (FiniteModel.pi (fun _ : Edge n => fairBit)).eventMass
    {c | c e ∈ ({d} : Set (Fin 2))} = 1 / 2
  rw [FiniteModel.coordinate_eventMass]
  rw [FiniteModel.eventMass_eq_sum]
  simp [fairBit]

/-- The unordered edges internal to a given vertex set. -/
noncomputable def internalEdges {n : ℕ} (t : Finset (Fin n)) : Finset (Edge n) :=
  Finset.univ.filter (fun e => e.val ⊆ t)

theorem card_internalEdges {n : ℕ} (t : Finset (Fin n)) :
    (internalEdges t).card = Nat.choose t.card 2 := by
  classical
  have heq : (internalEdges t).map (Function.Embedding.subtype _) = t.powersetCard 2 := by
    ext s
    simp only [Finset.mem_map, internalEdges, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_powersetCard]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨he, e.property⟩
    · rintro ⟨hs, hc⟩
      exact ⟨⟨s, hc⟩, hs, rfl⟩
  rw [← Finset.card_map (Function.Embedding.subtype _), heq, Finset.card_powersetCard]

theorem pattern_probability : Specs.PatternProbability := by
  intro n k t ht d
  have heq : pattern t d = (internalEdges t : Set (Edge n)).pi (fun _ => {d}) := by
    ext c
    simp [pattern, ColoredClique, internalEdges, Set.mem_pi]
  rw [heq, ← FiniteModel.measureReal_eventMass, experiment, FiniteModel.measure_pi]
  change (Measure.pi (fun _ : Edge n => fairBit.measure)
    ((internalEdges t : Set (Edge n)).pi (fun _ => {d}))).toReal = _
  rw [Measure.pi_pi_finset, ENNReal.toReal_prod]
  simp_rw [FiniteModel.measureReal_eventMass]
  have hbit : fairBit.eventMass ({d} : Set (Fin 2)) = 1 / 2 := by
    rw [FiniteModel.eventMass_eq_sum]
    simp [fairBit]
  simp only [hbit, Finset.prod_const, card_internalEdges, ht]

theorem monochromatic_probability : Specs.MonochromaticProbability := by
  intro n k hk t ht
  have hne : (internalEdges t).Nonempty := by
    rw [← Finset.card_pos, card_internalEdges, ht]
    exact Nat.choose_pos hk
  obtain ⟨e, he⟩ := hne
  have het : e.val ⊆ t := (Finset.mem_filter.mp he).2
  have hd : Disjoint (pattern t 0) (pattern t 1) := by
    rw [Set.disjoint_left]
    intro c h0 h1
    have h := (h0 e het).symm.trans (h1 e het)
    norm_num at h
  have hu : monochromatic t = pattern t 0 ∪ pattern t 1 := by
    ext c
    constructor
    · rintro ⟨d, hd⟩
      fin_cases d
      · exact Or.inl hd
      · exact Or.inr hd
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  rw [hu, ← FiniteModel.measureReal_eventMass]
  change (experiment n).measure.real (pattern t 0 ∪ pattern t 1) = _
  rw [measureReal_union hd (FiniteModel.all_measurable _)]
  simp only [Measure.real]
  rw [FiniteModel.measureReal_eventMass, FiniteModel.measureReal_eventMass,
    pattern_probability n k t ht 0, pattern_probability n k t ht 1]
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [zpow_one, zpow_natCast, div_pow, one_pow]
  ring

theorem lower_bound : Specs.LowerBound := by
  intro n k hk hcrit
  let A : KSubsets (Fin n) k → Set (Coloring n) := fun t => monochromatic t.val
  have hsum : (∑ t, (experiment n).measure.real (A t)) < 1 := by
    simp_rw [Measure.real, FiniteModel.measureReal_eventMass,
      show ∀ t : KSubsets (Fin n) k,
        (experiment n).eventMass (A t) = (2 : ℝ) ^ ((1 : ℤ) - (Nat.choose k 2 : ℤ))
        from fun t => monochromatic_probability n k hk t.val t.property]
    simpa only [Finset.sum_const, Finset.card_univ, KSubsets,
      Fintype.card_finset_len, Fintype.card_fin, nsmul_eq_mul] using hcrit
  obtain ⟨c, hc⟩ := exists_avoiding (experiment n).measure A
    (fun _ => FiniteModel.all_measurable _) hsum
  by_contra h
  have hr : P205.Ramsey.Specs.ramseyNumberValue k k ≤
      (Finset.univ : Finset (Fin n)).card := by simpa using le_of_not_gt h
  rcases ramsey_number_on k k (by omega) (by omega) (Fin n) Finset.univ hr c with
      ⟨t, _, ht, hcl⟩ | ⟨t, _, ht, hcl⟩
  · exact hc ⟨t, ht⟩ ⟨0, hcl⟩
  · exact hc ⟨t, ht⟩ ⟨1, hcl⟩

/-- The factorial beats the exponential estimate already at three. -/
theorem exponential_lt_factorial (k : ℕ) (hk : 3 ≤ k) :
    (2 : ℝ) ^ (1 + (k : ℝ) / 2) < (k.factorial : ℝ) := by
  induction k, hk using Nat.le_induction with
  | base =>
    have hs : ((2 : ℝ) ^ (1 + (3 : ℝ) / 2)) ^ 2 = 32 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    norm_num [Nat.factorial] at ⊢
    nlinarith
  | succ k hk ih =>
    have hhalf : (2 : ℝ) ^ (1 / 2 : ℝ) < 2 := by
      calc
        _ < (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one _
    have hfac : 0 < (k.factorial : ℝ) := by positivity
    have hexp : 1 + ((k + 1 : ℕ) : ℝ) / 2 = (1 + (k : ℝ) / 2) + 1 / 2 := by
      push_cast
      ring
    rw [hexp, Real.rpow_add (by norm_num), Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    calc
      _ < (k.factorial : ℝ) * 2 := mul_lt_mul ih hhalf.le (by positivity) hfac.le
      _ ≤ ((k : ℝ) + 1) * (k.factorial : ℝ) := by
        have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
        nlinarith

/-- The source's criterion holds at the natural floor of the real exponential. -/
theorem criterion_at_floor (k : ℕ) (hk : 3 ≤ k) :
    (Nat.choose ⌊(2 : ℝ) ^ ((k : ℝ) / 2)⌋₊ k : ℝ) *
      (2 : ℝ) ^ ((1 : ℤ) - (Nat.choose k 2 : ℤ)) < 1 := by
  let x : ℝ := (2 : ℝ) ^ ((k : ℝ) / 2)
  let n : ℕ := ⌊x⌋₊
  have hx : 0 < x := Real.rpow_pos_of_pos (by norm_num) _
  have hn : (n : ℝ) ≤ x := Nat.floor_le hx.le
  have hfac : 0 < (k.factorial : ℝ) := by positivity
  have hb : (Nat.choose n k : ℝ) ≤ x ^ k / (k.factorial : ℝ) := by
    calc
      _ ≤ (n : ℝ) ^ k / (k.factorial : ℝ) := Nat.choose_le_pow_div k n
      _ ≤ x ^ k / (k.factorial : ℝ) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hn _) hfac.le
  have hc : (Nat.choose k 2 : ℝ) * 2 = (k : ℝ) * ((k : ℝ) - 1) := by
    have h := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_succ_right_eq k 1)
    norm_num [Nat.choose_one_right, Nat.cast_sub (by omega : 1 ≤ k)] at h
    exact h
  have hp : x ^ k * (2 : ℝ) ^ ((1 : ℤ) - (Nat.choose k 2 : ℤ)) =
      (2 : ℝ) ^ (1 + (k : ℝ) / 2) := by
    change ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ k * _ = _
    rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_intCast,
      Int.cast_sub, Int.cast_one, Int.cast_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    nlinarith
  calc
    _ ≤ (x ^ k / (k.factorial : ℝ)) *
        (2 : ℝ) ^ ((1 : ℤ) - (Nat.choose k 2 : ℤ)) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (2 : ℝ) ^ (1 + (k : ℝ) / 2) / (k.factorial : ℝ) := by
      rw [div_mul_eq_mul_div, hp]
    _ < 1 := (div_lt_one hfac).mpr (exponential_lt_factorial k hk)

theorem exponential_lower_bound : Specs.ExponentialLowerBound := by
  intro k hk
  have hn := lower_bound ⌊(2 : ℝ) ^ ((k : ℝ) / 2)⌋₊ k (by omega)
    (criterion_at_floor k hk)
  have hcast : (⌊(2 : ℝ) ^ ((k : ℝ) / 2)⌋₊ : ℝ) + 1 ≤
      (P205.Ramsey.Specs.ramseyNumberValue k k : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hn)
  exact (Nat.lt_floor_add_one _).trans_le hcast

end P205.Probability.RandomRamsey
