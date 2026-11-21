import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.FixedFutureLaw
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.CanonicalPathLaw
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal MeasureTheory

set_option linter.unusedSectionVars false

universe u v
namespace P207.Markov
noncomputable section

variable {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
  [DiscreteMeasurableSpace S]

local instance statePathLaw_probability (P : StochasticMatrix S) (i : S) :
    IsProbabilityMeasure (statePathLaw P i) := pathLaw_probability P (PMF.pure i)

local instance pathKernel_isMarkov (P : StochasticMatrix S) :
    IsMarkovKernel (pathKernel P) := pathKernel_markov P

theorem measurable_stateExpectation (P : StochasticMatrix S) (g : (ℕ → S) → ℝ) :
    Measurable (fun i => stateExpectation P i g) := measurable_of_countable _

theorem stateExpectation_bound (P : StochasticMatrix S) (g : (ℕ → S) → ℝ)
    (C : ℝ) (hg : ∀ x, ‖g x‖ ≤ C) (i : S) : ‖stateExpectation P i g‖ ≤ C := by
  simpa [stateExpectation] using
    (norm_integral_le_of_norm_le_const (μ := statePathLaw P i) (Eventually.of_forall hg))

namespace FixedFutureLaw
variable {Ω : Type v} [m : MeasurableSpace Ω]
  {P : StochasticMatrix S} {ν : ProbabilityLaw S} {X : ℕ → Ω → S}
  {ℱ : Filtration ℕ m} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- One-step recursion tested against an arbitrary event of the given filtration. -/
theorem event_step (h : IsMarkovChain P ν X ℱ μ) (t : ℕ) (B : Set Ω)
    (hB : MeasurableSet[ℱ t] B) (i j : S) (hi : ∀ ω ∈ B, X t ω = i) :
    μ (B ∩ {ω | X (t + 1) ω = j}) = μ B * P i j := by
  let D : Set Ω := {ω | X (t + 1) ω = j}
  have hBm : MeasurableSet B := (ℱ.le t) B hB
  have hD : MeasurableSet D := measurableSet_eq_fun h.1.measurable measurable_const
  have hint : Integrable (D.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const _).indicator hD
  have he : (μ (B ∩ D)).toReal = (μ B).toReal * (P i j).toReal := by
    calc
      (μ (B ∩ D)).toReal = ∫ ω in B, D.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
        rw [setIntegral_indicator hD, setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
      _ = ∫ ω in B, μ[D.indicator (fun _ => (1 : ℝ)) | ℱ t] ω ∂μ :=
        (setIntegral_condExp (ℱ.le t) hint hB).symm
      _ = ∫ ω in B, realMatrix P (X t ω) j ∂μ :=
        setIntegral_congr_ae hBm ((h.2.2 t j).mono fun ω hω _ => hω)
      _ = ∫ _ in B, (P i j).toReal ∂μ :=
        setIntegral_congr_fun hBm fun ω hω => by simp [realMatrix, hi ω hω]
      _ = (μ B).toReal * (P i j).toReal := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (entry_ne_top P _ _))).mp
  simpa only [ENNReal.toReal_mul] using he

theorem futurePrefix_measurable (h : IsMarkovChain P ν X ℱ μ)
    (n r : ℕ) (x : ℕ → S) :
    MeasurableSet[ℱ (n + r)] {ω | ∀ k ≤ r, X (n + k) ω = x k} := by
  have heq : {ω | ∀ k ≤ r, X (n + k) ω = x k} =
      ⋂ k : Finset.Iic r, {ω | X (n + k) ω = x k} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h k => h k (Finset.mem_Iic.mp k.2),
      fun h k hk => h ⟨k, Finset.mem_Iic.mpr hk⟩⟩
  rw [heq]
  let : MeasurableSpace Ω := ℱ (n + r)
  exact MeasurableSet.iInter fun k => measurableSet_eq_fun
    ((h.1 (n + k)).mono (ℱ.mono (Nat.add_le_add_left (Finset.mem_Iic.mp k.2) n))
      le_rfl) measurable_const

/-- The conditional prefix formula with an arbitrary test event at the starting time. -/
theorem futurePrefix (h : IsMarkovChain P ν X ℱ μ) (n : ℕ) (A : Set Ω)
    (hA : MeasurableSet[ℱ n] A) (r : ℕ) (x : ℕ → S) :
    μ (A ∩ {ω | ∀ k ≤ r, X (n + k) ω = x k}) =
      μ (A ∩ {ω | X n ω = x 0}) * ∏ k ∈ Finset.range r, P (x k) (x (k + 1)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    let B := A ∩ {ω | ∀ k ≤ r, X (n + k) ω = x k}
    have hB : MeasurableSet[ℱ (n + r)] B :=
      ((ℱ.mono (Nat.le_add_right n r)) A hA).inter (futurePrefix_measurable h n r x)
    have heq : A ∩ {ω | ∀ k ≤ r + 1, X (n + k) ω = x k} =
        B ∩ {ω | X ((n + r) + 1) ω = x (r + 1)} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, B]
      constructor
      · intro hh
        exact ⟨⟨hh.1, fun k hk => hh.2 k (Nat.le_succ_of_le hk)⟩,
          by simpa [Nat.add_assoc] using hh.2 (r + 1) le_rfl⟩
      · intro hh
        refine ⟨hh.1.1, fun k hk => ?_⟩
        rcases Nat.le_succ_iff_eq_or_le.mp hk with he | he
        · subst k; simpa [Nat.add_assoc] using hh.2
        · exact hh.1.2 k he
    rw [heq, event_step h (n + r) B hB (x r) (x (r + 1))
      (fun ω hω => hω.2 r le_rfl)]
    change μ (A ∩ {ω | ∀ k ≤ r, X (n + k) ω = x k}) * _ = _
    rw [ih, Finset.prod_range_succ, mul_assoc]

/-- Equality of finite measures extends the prefix formula to the whole product sigma algebra. -/
theorem future_measure (h : IsMarkovChain P ν X ℱ μ) (n : ℕ) (A : Set Ω)
    (hA : MeasurableSet[ℱ n] A) :
    (μ.restrict A).map (fun ω k => X (n + k) ω) =
      (pathKernel P).comap (X n) h.1.measurable ∘ₘ μ.restrict A := by
  let Y : Ω → (ℕ → S) := fun ω k => X (n + k) ω
  have hY : Measurable Y := measurable_pi_iff.mpr fun k => h.1.measurable
  let K := (pathKernel P).comap (X n) h.1.measurable
  apply pathMeasure_ext
  intro r x
  rw [Measure.map_apply hY (measurableSet_prefixCylinder r x),
    Measure.restrict_apply (hY (measurableSet_prefixCylinder r x)),
    Measure.bind_apply (measurableSet_prefixCylinder r x) K.aemeasurable]
  change μ ({ω | ∀ k ≤ r, X (n + k) ω = x k} ∩ A) = _
  rw [Set.inter_comm, futurePrefix h n A hA r x]
  have heq : (fun ω => K ω (prefixCylinder r x)) =
      {ω | X n ω = x 0}.indicator
        (fun _ => ∏ k ∈ Finset.range r, P (x k) (x (k + 1))) := by
    funext ω
    change statePathLaw P (X n ω) (prefixCylinder r x) = _
    by_cases hi : X n ω = x 0 <;>
      simp [statePathLaw, pathLaw_prefix, PMF.pure_apply, hi, eq_comm]
  rw [heq, lintegral_indicator
    (measurableSet_eq_fun h.1.measurable measurable_const), lintegral_const,
    Measure.restrict_apply_univ,
    Measure.restrict_apply (measurableSet_eq_fun h.1.measurable measurable_const),
    Set.inter_comm, mul_comm]

end FixedFutureLaw

/-- The conditional canonical future law, including all bounded measurable path functions. -/
theorem fixed_future_integral {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (ν : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : IsMarkovChain P ν X ℱ μ) (g : (ℕ → S) → ℝ) (hg : Measurable g)
    (hb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) (n : ℕ) (A : Set Ω)
    (hA : MeasurableSet[ℱ n] A) :
    (∫ ω in A, g (fun k => X (n + k) ω) ∂μ) =
      ∫ ω in A, stateExpectation P (X n ω) g ∂μ := by
  obtain ⟨C, hC⟩ := hb
  let K := (pathKernel P).comap (X n) h.1.measurable
  have hY : Measurable (fun ω k => X (n + k) ω) :=
    measurable_pi_iff.mpr fun _ => h.1.measurable
  have hint : Integrable g (K ∘ₘ μ.restrict A) :=
    Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall hC)
  calc
    (∫ ω in A, g (fun k => X (n + k) ω) ∂μ) =
        ∫ p, g p ∂(μ.restrict A).map (fun ω k => X (n + k) ω) :=
      (integral_map hY.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ p, g p ∂(K ∘ₘ μ.restrict A) := by
      rw [FixedFutureLaw.future_measure h n A hA]
    _ = ∫ ω in A, ∫ p, g p ∂K ω ∂μ := by
      rw [Measure.comp_eq_comp_const_apply]
      exact ProbabilityTheory.Kernel.integral_comp hint
    _ = ∫ ω in A, stateExpectation P (X n ω) g ∂μ := rfl

end
end P207.Markov
