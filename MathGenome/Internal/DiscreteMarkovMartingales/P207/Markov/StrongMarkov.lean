import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.StrongMarkov
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.FixedFutureLaw
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Foundation.Stopping

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal MeasureTheory

set_option linter.unusedSectionVars false
universe u v
namespace P207.Markov
noncomputable section

namespace StrongMarkovInterfaces
abbrev stoppedState := @P207.Markov.stoppedState
abbrev shiftedPath := @P207.Markov.shiftedPath
end StrongMarkovInterfaces

theorem shiftedPath_at_finite {S : Type u} {Ω : Type v} (X : ℕ → Ω → S)
    (τ : Ω → WithTop ℕ) (pInf : ℕ → S) (n : ℕ) (ω : Ω) (h : τ ω = n) :
    shiftedPath X τ pInf ω = fun k => X (n + k) ω := by
  simp only [shiftedPath, h]
  rfl

theorem stoppedState_at_finite {S : Type u} {Ω : Type v} (X : ℕ → Ω → S)
    (τ : Ω → WithTop ℕ) (iInf : S) (n : ℕ) (ω : Ω) (h : τ ω = n) :
    stoppedState X τ iInf ω = X n ω := by
  simp only [stoppedState, h]
  rfl

theorem shiftedPath_eq_on_finite {S : Type u} {Ω : Type v} (X : ℕ → Ω → S)
    (τ : Ω → WithTop ℕ) (p q : ℕ → S) :
    Set.EqOn (shiftedPath X τ p) (shiftedPath X τ q) {ω | τ ω < ⊤} := by
  intro ω hω
  simp [shiftedPath, ne_of_lt (show τ ω < ⊤ from hω)]

theorem stoppedState_eq_on_finite {S : Type u} {Ω : Type v} (X : ℕ → Ω → S)
    (τ : Ω → WithTop ℕ) (i j : S) :
    Set.EqOn (stoppedState X τ i) (stoppedState X τ j) {ω | τ ω < ⊤} := by
  intro ω hω
  simp [stoppedState, ne_of_lt (show τ ω < ⊤ from hω)]

variable {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
  [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω]

/-- A stopped state is measurable for the past at the stopping time, with any
fixed assignment on the infinite layer. -/
theorem measurable_stoppedState (X : ℕ → Ω → S) (ℱ : Filtration ℕ m)
    (hX : Adapted ℱ X) (τ : Ω → WithTop ℕ) (hτ : P207.IsDiscreteStoppingTime ℱ τ)
    (iInf : S) : Measurable[P207.stoppedSigma hτ] (stoppedState X τ iInf) := by
  intro B hB
  apply (P207.stoppedSigma_layers hτ _).mpr
  constructor
  · have heq : stoppedState X τ iInf ⁻¹' B =
        (⋃ n : ℕ, X n ⁻¹' B ∩ {ω | τ ω = n}) ∪
        ((fun _ : Ω => iInf) ⁻¹' B ∩ {ω | τ ω = ⊤}) := by
      ext ω
      cases ht : τ ω with
      | top => simp [stoppedState, ht]
      | coe n => simp [stoppedState, ht]; rfl
    rw [heq]
    exact (MeasurableSet.iUnion fun n => le_iSup ℱ n _
      ((hB.preimage (hX n)).inter (P207.stopping_layer_measurable hτ n))).union
      ((hB.preimage measurable_const).inter
        (MeasureTheory.IsStoppingTime.measurableSet_eq_top' hτ))
  · intro n
    have heq : stoppedState X τ iInf ⁻¹' B ∩ {ω | τ ω = n} =
        X n ⁻¹' B ∩ {ω | τ ω = n} := by
      ext ω
      by_cases ht : τ ω = n
      · simp [ht, stoppedState_at_finite X τ iInf n ω ht]
      · simp [ht]
    rw [heq]
    exact (hB.preimage (hX n)).inter (P207.stopping_layer_measurable hτ n)

/-- The shifted future is measurable for the terminal sigma algebra. It is
not asserted to be measurable for the past at the stopping time. -/
theorem measurable_shiftedPath (X : ℕ → Ω → S) (ℱ : Filtration ℕ m)
    (hX : Adapted ℱ X) (τ : Ω → WithTop ℕ) (hτ : P207.IsDiscreteStoppingTime ℱ τ)
    (pInf : ℕ → S) : Measurable[P207.terminalSigma ℱ] (shiftedPath X τ pInf) := by
  have hX' (n : ℕ) : Measurable[P207.terminalSigma ℱ] (X n) :=
    (hX n).mono (le_iSup ℱ n) le_rfl
  have ht : Measurable[P207.terminalSigma ℱ] (fun ω => (τ ω).untopA) :=
    (measurable_of_countable (fun t : WithTop ℕ => t.untopA)).comp
      (MeasureTheory.IsStoppingTime.measurable_iSup hτ)
  let mTerm := P207.terminalSigma ℱ
  have h_eval (k : ℕ) : Measurable[mTerm]
      (fun ω => X ((τ ω).untopA + k) ω) := by
    let : MeasurableSpace Ω := mTerm
    have hf : Measurable (fun a : ℕ × Ω => X (a.1 + k) a.2) :=
      measurable_from_prod_countable_right fun n => hX' (n + k)
    exact hf.comp (ht.prodMk measurable_id)
  have hpath : Measurable[mTerm]
      (fun ω k => X ((τ ω).untopA + k) ω) := by
    let : MeasurableSpace Ω := mTerm
    exact measurable_pi_iff.mpr h_eval
  have htop : MeasurableSet[mTerm] {ω | τ ω = ⊤} :=
    MeasureTheory.IsStoppingTime.measurableSet_eq_top' hτ
  change Measurable[mTerm] _
  let : MeasurableSpace Ω := mTerm
  exact measurable_const.ite htop hpath

namespace StrongMarkov

/-- The finite stopping event is the disjoint union of the finite layers. -/
theorem finite_layers (τ : Ω → WithTop ℕ) (A : Set Ω) :
    A ∩ {ω | τ ω < ⊤} = ⋃ n : ℕ, A ∩ {ω | τ ω = n} := by
  ext ω
  cases ht : τ ω with
  | top => simp [ht]
  | coe n => simp [ht]

theorem layers_disjoint (τ : Ω → WithTop ℕ) (A : Set Ω) :
    Pairwise (fun n k : ℕ => Disjoint (A ∩ {ω | τ ω = n}) (A ∩ {ω | τ ω = k})) := by
  intro n k hnk
  apply Set.disjoint_left.mpr
  intro ω hn hk
  exact hnk (WithTop.coe_injective (hn.2.symm.trans hk.2))

theorem layer_measurable {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : P207.IsDiscreteStoppingTime ℱ τ) (A : Set Ω)
    (hA : MeasurableSet[P207.stoppedSigma hτ] A) (n : ℕ) :
    MeasurableSet[ℱ n] (A ∩ {ω | τ ω = n}) :=
  ((P207.stoppedSigma_layers hτ A).mp hA).2 n

variable {P : StochasticMatrix S} {ν : ProbabilityLaw S} {X : ℕ → Ω → S}
  {ℱ : Filtration ℕ m} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The upstream fixed-time measure identity also integrates arbitrary
nonnegative functions, with no finiteness assumption on their integrals. -/
theorem fixed_future_lintegral (h : IsMarkovChain P ν X ℱ μ)
    (g : (ℕ → S) → ℝ≥0∞) (hg : Measurable g) (n : ℕ) (A : Set Ω)
    (hA : MeasurableSet[ℱ n] A) :
    (∫⁻ ω in A, g (fun k => X (n + k) ω) ∂μ) =
      ∫⁻ ω in A, ∫⁻ p, g p ∂statePathLaw P (X n ω) ∂μ := by
  let K := (pathKernel P).comap (X n) h.1.measurable
  have hY : Measurable (fun ω k => X (n + k) ω) :=
    measurable_pi_iff.mpr fun _ => h.1.measurable
  calc
    (∫⁻ ω in A, g (fun k => X (n + k) ω) ∂μ) =
        ∫⁻ p, g p ∂(μ.restrict A).map (fun ω k => X (n + k) ω) :=
      (lintegral_map hg hY).symm
    _ = ∫⁻ p, g p ∂(K ∘ₘ μ.restrict A) := by
      rw [FixedFutureLaw.future_measure h n A hA]
    _ = ∫⁻ ω in A, ∫⁻ p, g p ∂K ω ∂μ :=
      Measure.lintegral_bind K.aemeasurable hg.aemeasurable
    _ = ∫⁻ ω in A, ∫⁻ p, g p ∂statePathLaw P (X n ω) ∂μ := rfl

end StrongMarkov

/-- Strong Markov identity on the finite stopping event for bounded real
functions of the entire future. Both fallback values are arbitrary. -/
theorem strong_future_integral (P : StochasticMatrix S) (ν : ProbabilityLaw S)
    (X : ℕ → Ω → S) (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : IsMarkovChain P ν X ℱ μ) (τ : Ω → WithTop ℕ)
    (hτ : P207.IsDiscreteStoppingTime ℱ τ) (pInf : ℕ → S) (iInf : S)
    (g : (ℕ → S) → ℝ) (hg : Measurable g) (hb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C)
    (A : Set Ω) (hA : MeasurableSet[P207.stoppedSigma hτ] A) :
    (∫ ω in A ∩ {ω | τ ω < ⊤}, g (shiftedPath X τ pInf ω) ∂μ) =
      ∫ ω in A ∩ {ω | τ ω < ⊤}, stateExpectation P (stoppedState X τ iInf ω) g ∂μ := by
  obtain ⟨C, hC⟩ := hb
  have hY := (measurable_shiftedPath X ℱ h.1 τ hτ pInf).mono
    (iSup_le ℱ.le) le_rfl
  have hZ := (measurable_stoppedState X ℱ h.1 τ hτ iInf).mono
    (MeasureTheory.IsStoppingTime.measurableSpace_le hτ) le_rfl
  have hgi : Integrable (fun ω => g (shiftedPath X τ pInf ω)) μ :=
    Integrable.of_bound (hg.comp hY).aestronglyMeasurable C
      (Eventually.of_forall fun ω => hC _)
  have hGi : Integrable (fun ω => stateExpectation P (stoppedState X τ iInf ω) g) μ :=
    Integrable.of_bound ((measurable_stateExpectation P g).comp hZ).aestronglyMeasurable C
      (Eventually.of_forall fun ω => stateExpectation_bound P g C hC _)
  have hm (n : ℕ) : MeasurableSet (A ∩ {ω | τ ω = n}) :=
    ℱ.le n _ (StrongMarkov.layer_measurable hτ A hA n)
  rw [StrongMarkov.finite_layers, integral_iUnion hm (StrongMarkov.layers_disjoint τ A)
    hgi.integrableOn, integral_iUnion hm (StrongMarkov.layers_disjoint τ A) hGi.integrableOn]
  apply tsum_congr
  intro n
  calc
    (∫ ω in A ∩ {ω | τ ω = n}, g (shiftedPath X τ pInf ω) ∂μ) =
        ∫ ω in A ∩ {ω | τ ω = n}, g (fun k => X (n + k) ω) ∂μ :=
      setIntegral_congr_fun (hm n) fun ω hω =>
        congrArg g (shiftedPath_at_finite X τ pInf n ω hω.2)
    _ = ∫ ω in A ∩ {ω | τ ω = n}, stateExpectation P (X n ω) g ∂μ :=
      fixed_future_integral P ν X ℱ μ h g hg ⟨C, hC⟩ n _
        (StrongMarkov.layer_measurable hτ A hA n)
    _ = ∫ ω in A ∩ {ω | τ ω = n}, stateExpectation P (stoppedState X τ iInf ω) g ∂μ :=
      setIntegral_congr_fun (hm n) fun ω hω => by
        rw [stoppedState_at_finite X τ iInf n ω hω.2]

/-- The nonnegative extension allows infinite expectations and follows from
the same disjoint-layer proof using extended nonnegative integrals. -/
theorem strong_future_lintegral (P : StochasticMatrix S) (ν : ProbabilityLaw S)
    (X : ℕ → Ω → S) (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : IsMarkovChain P ν X ℱ μ) (τ : Ω → WithTop ℕ)
    (hτ : P207.IsDiscreteStoppingTime ℱ τ) (pInf : ℕ → S) (iInf : S)
    (g : (ℕ → S) → ℝ≥0∞) (hg : Measurable g)
    (A : Set Ω) (hA : MeasurableSet[P207.stoppedSigma hτ] A) :
    (∫⁻ ω in A ∩ {ω | τ ω < ⊤}, g (shiftedPath X τ pInf ω) ∂μ) =
      ∫⁻ ω in A ∩ {ω | τ ω < ⊤},
        ∫⁻ p, g p ∂statePathLaw P (stoppedState X τ iInf ω) ∂μ := by
  have hm (n : ℕ) : MeasurableSet (A ∩ {ω | τ ω = n}) :=
    ℱ.le n _ (StrongMarkov.layer_measurable hτ A hA n)
  rw [StrongMarkov.finite_layers, lintegral_iUnion hm (StrongMarkov.layers_disjoint τ A),
    lintegral_iUnion hm (StrongMarkov.layers_disjoint τ A)]
  apply tsum_congr
  intro n
  calc
    (∫⁻ ω in A ∩ {ω | τ ω = n}, g (shiftedPath X τ pInf ω) ∂μ) =
        ∫⁻ ω in A ∩ {ω | τ ω = n}, g (fun k => X (n + k) ω) ∂μ :=
      setLIntegral_congr_fun (hm n) fun ω hω =>
        congrArg g (shiftedPath_at_finite X τ pInf n ω hω.2)
    _ = ∫⁻ ω in A ∩ {ω | τ ω = n}, ∫⁻ p, g p ∂statePathLaw P (X n ω) ∂μ :=
      StrongMarkov.fixed_future_lintegral h g hg n _ (StrongMarkov.layer_measurable hτ A hA n)
    _ = ∫⁻ ω in A ∩ {ω | τ ω = n},
        ∫⁻ p, g p ∂statePathLaw P (stoppedState X τ iInf ω) ∂μ :=
      setLIntegral_congr_fun (hm n) fun ω hω => by
        rw [stoppedState_at_finite X τ iInf n ω hω.2]

/-- When the stopping time is finite almost surely, the stopped kernel gives
the conditional expectation of every bounded measurable future function. -/
theorem strong_future_condExp (P : StochasticMatrix S) (ν : ProbabilityLaw S)
    (X : ℕ → Ω → S) (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : IsMarkovChain P ν X ℱ μ) (τ : Ω → WithTop ℕ)
    (hτ : P207.IsDiscreteStoppingTime ℱ τ) (pInf : ℕ → S) (iInf : S)
    (hfinite : ∀ᵐ ω ∂μ, τ ω < ⊤)
    (g : (ℕ → S) → ℝ) (hg : Measurable g) (hb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) :
    μ[(fun ω => g (shiftedPath X τ pInf ω)) | P207.stoppedSigma hτ] =ᵐ[μ]
      fun ω => stateExpectation P (stoppedState X τ iInf ω) g := by
  obtain ⟨C, hC⟩ := hb
  have hle : P207.stoppedSigma hτ ≤ m :=
    MeasureTheory.IsStoppingTime.measurableSpace_le hτ
  have hY := (measurable_shiftedPath X ℱ h.1 τ hτ pInf).mono (iSup_le ℱ.le) le_rfl
  have hG : Measurable[P207.stoppedSigma hτ]
      (fun ω => stateExpectation P (stoppedState X τ iInf ω) g) :=
    (measurable_stateExpectation P g).comp (measurable_stoppedState X ℱ h.1 τ hτ iInf)
  have hgi : Integrable (fun ω => g (shiftedPath X τ pInf ω)) μ :=
    Integrable.of_bound (hg.comp hY).aestronglyMeasurable C
      (Eventually.of_forall fun ω => hC _)
  have hGi : Integrable (fun ω => stateExpectation P (stoppedState X τ iInf ω) g) μ :=
    Integrable.of_bound (hG.mono hle le_rfl).aestronglyMeasurable C
      (Eventually.of_forall fun ω => stateExpectation_bound P g C hC _)
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hle hgi
    (fun _ _ _ => hGi.integrableOn) _ hG.stronglyMeasurable.aestronglyMeasurable
  intro A hA _
  have heq : A ∩ {ω | τ ω < ⊤} =ᵐ[μ] A :=
    hfinite.mono fun ω hω => by simp [hω]
  calc
    (∫ ω in A, stateExpectation P (stoppedState X τ iInf ω) g ∂μ) =
        ∫ ω in A ∩ {ω | τ ω < ⊤}, stateExpectation P (stoppedState X τ iInf ω) g ∂μ :=
      (setIntegral_congr_set heq).symm
    _ = ∫ ω in A ∩ {ω | τ ω < ⊤}, g (shiftedPath X τ pInf ω) ∂μ :=
      (strong_future_integral P ν X ℱ μ h τ hτ pInf iInf g hg ⟨C, hC⟩ A hA).symm
    _ = ∫ ω in A, g (shiftedPath X τ pInf ω) ∂μ := setIntegral_congr_set heq

/-- Eventwise formulation of the conditional future law: the conditional
probability of every product-measurable path event is its canonical probability
started at the stopped state. -/
theorem strong_future_event_condExp (P : StochasticMatrix S) (ν : ProbabilityLaw S)
    (X : ℕ → Ω → S) (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : IsMarkovChain P ν X ℱ μ) (τ : Ω → WithTop ℕ)
    (hτ : P207.IsDiscreteStoppingTime ℱ τ) (pInf : ℕ → S) (iInf : S)
    (hfinite : ∀ᵐ ω ∂μ, τ ω < ⊤) (B : Set (ℕ → S)) (hB : MeasurableSet B) :
    μ[(fun ω => B.indicator (fun _ => (1 : ℝ)) (shiftedPath X τ pInf ω)) |
      P207.stoppedSigma hτ] =ᵐ[μ]
      fun ω => (statePathLaw P (stoppedState X τ iInf ω) B).toReal := by
  have hb : ∀ p : ℕ → S, ‖B.indicator (fun _ => (1 : ℝ)) p‖ ≤ 1 := by
    intro p
    by_cases hp : p ∈ B <;> simp [hp]
  have he := strong_future_condExp P ν X ℱ μ h τ hτ pInf iInf hfinite
    (B.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hB) ⟨1, hb⟩
  convert he using 1
  funext ω
  simp [stateExpectation, integral_indicator hB, measureReal_def]

end
end P207.Markov
