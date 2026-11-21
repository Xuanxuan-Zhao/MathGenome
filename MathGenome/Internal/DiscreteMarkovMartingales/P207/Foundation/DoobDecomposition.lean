import MathGenome.Internal.DiscreteMarkovMartingales.P207.Foundation.TwoTimeAndExamples
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.DoobDecomposition

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207

variable {Ω : Type u} [m : MeasurableSpace Ω]

/-- The library compensator respects equality almost surely at each time. -/
lemma predictablePart_congr_ae (μ : Measure Ω) (ℱ : Filtration ℕ m)
    {X Y : ℕ → Ω → ℝ} (h : ∀ n, X n =ᵐ[μ] Y n) (n : ℕ) :
    predictablePart X ℱ μ n =ᵐ[μ] predictablePart Y ℱ μ n := by
  unfold predictablePart
  exact eventuallyEq_sum fun k _ => condExp_congr_ae ((h (k + 1)).sub (h k))

theorem doob_decomposition_canonical (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (ha : Adapted ℱ X) (hi : ∀ n, Integrable (X n) μ) :
    IsDoobDecomposition X ℱ μ (martingalePart X ℱ μ) (predictablePart X ℱ μ) ∧
      (∀ n ω, X n ω = martingalePart X ℱ μ n ω + predictablePart X ℱ μ n ω) := by
  have hsum : ∀ n ω, X n ω =
      martingalePart X ℱ μ n ω + predictablePart X ℱ μ n ω := by
    intro n ω
    simp [martingalePart]
  refine ⟨⟨fun n => Filter.Eventually.of_forall (hsum n),
    (martingale_iff_library μ ℱ _).mpr (martingale_martingalePart ha.stronglyAdapted hi),
    ?_, predictablePart_zero.eventuallyEq, fun n => (stronglyAdapted_predictablePart (f := X) (ℱ := ℱ) (μ := μ) n).measurable⟩,
    hsum⟩
  intro n
  unfold predictablePart
  exact integrable_finsetSum' _ fun k _ => integrable_condExp

theorem doob_decomposition_exists (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (ha : Adapted ℱ X) (hi : ∀ n, Integrable (X n) μ) :
    ∃ M A, IsDoobDecomposition X ℱ μ M A ∧ A 0 = 0 ∧
      ∀ n ω, X n ω = M n ω + A n ω :=
  ⟨_, _, (doob_decomposition_canonical μ ℱ X ha hi).1, predictablePart_zero,
    (doob_decomposition_canonical μ ℱ X ha hi).2⟩

/-- Every normalized predictable component equals the canonical compensator. -/
lemma doob_compensator_eq (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) {X M A : ℕ → Ω → ℝ}
    (h : IsDoobDecomposition X ℱ μ M A) (n : ℕ) :
    predictablePart X ℱ μ n =ᵐ[μ] A n := by
  rcases h with ⟨hs, hm, hi, hz, hp⟩
  -- Replace the initial value on its null exceptional set, so that the
  -- library's exact normalization hypothesis applies without completing ℱ₀.
  let B : ℕ → Ω → ℝ := fun k => if k = 0 then 0 else A k
  have hB : ∀ k, B k =ᵐ[μ] A k := by
    intro k
    cases k with
    | zero => exact hz.symm
    | succ k => exact Filter.EventuallyEq.rfl
  have hsum : ∀ k, X k =ᵐ[μ] M k + B k := fun k =>
    (hs k).trans (Filter.EventuallyEq.rfl.add (hB k).symm)
  have hcanon : predictablePart (M + B) ℱ μ n =ᵐ[μ] B n := by
    apply predictablePart_add_ae_eq ((martingale_iff_library μ ℱ M).mp hm)
    · intro k
      simpa only [B, Nat.add_one_ne_zero, ↓reduceIte] using (hp k).stronglyMeasurable
    · simp [B]
    · intro k
      exact (hi k).congr (hB k).symm
  exact (predictablePart_congr_ae μ ℱ hsum n).trans (hcanon.trans (hB n))

theorem doob_decomposition_unique (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X M A M' A' : ℕ → Ω → ℝ)
    (h : IsDoobDecomposition X ℱ μ M A)
    (h' : IsDoobDecomposition X ℱ μ M' A') :
    ∀ᵐ ω ∂μ, ∀ n, M n ω = M' n ω ∧ A n ω = A' n ω := by
  apply ae_all_iff.mpr
  intro n
  have hA := (doob_compensator_eq μ ℱ h n).symm.trans (doob_compensator_eq μ ℱ h' n)
  filter_upwards [hA, h.1 n, h'.1 n] with ω ha hs hs'
  constructor
  · change X n ω = M n ω + A n ω at hs
    change X n ω = M' n ω + A' n ω at hs'
    linarith
  · exact ha

theorem doob_submartingale_iff (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X M A : ℕ → Ω → ℝ)
    (ha : Adapted ℱ X) (hi : ∀ n, Integrable (X n) μ)
    (h : IsDoobDecomposition X ℱ μ M A) :
    IsSubmartingale X ℱ μ ↔ ∀ᵐ ω ∂μ, Monotone (fun n => A n ω) := by
  constructor
  · intro hx
    have hmono := ((submartingale_iff_library μ ℱ X).mp hx).monotone_predictablePart
    have heq := ae_all_iff.mpr (doob_compensator_eq μ ℱ h)
    filter_upwards [hmono, heq] with ω hm he
    intro i j hij
    change A i ω ≤ A j ω
    rw [← he i, ← he j]
    exact hm hij
  · intro hmono
    rcases h with ⟨hs, hm, hAi, hz, hp⟩
    refine ⟨ha, hi, fun n => ?_⟩
    have hce : μ[X (n + 1) | ℱ n] =ᵐ[μ] M n + A (n + 1) := by
      refine (condExp_congr_ae (hs (n + 1))).trans ?_
      refine (condExp_add (hm.2.1 (n + 1)) (hAi (n + 1)) (ℱ n)).trans ?_
      exact (hm.2.2 n).add
        (condExp_of_stronglyMeasurable (ℱ.le n) (hp n).stronglyMeasurable
          (hAi (n + 1))).eventuallyEq
    filter_upwards [hmono, hs n, hce] with ω hmon hsum hcond
    change X n ω = M n ω + A n ω at hsum
    change μ[X (n + 1) | ℱ n] ω = M n ω + A (n + 1) ω at hcond
    rw [hsum, hcond]
    exact add_le_add_right (hmon n.le_succ) _

end P207
