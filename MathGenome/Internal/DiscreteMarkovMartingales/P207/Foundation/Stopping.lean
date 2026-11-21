import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.Stopping

open MeasureTheory
open scoped MeasureTheory
universe u
namespace P207
variable {Ω : Type u} [m : MeasurableSpace Ω]
private theorem untopA_nat_coe (n : ℕ) : (n : WithTop ℕ).untopA = n := rfl
attribute [local simp] untopA_nat_coe

namespace StoppingInterfaces
noncomputable abbrev IsDiscreteStoppingTime : StoppingSpec.IsDiscreteStoppingTimeType.{u} :=
  @P207.IsDiscreteStoppingTime.{u}

noncomputable abbrev stoppedSigma : StoppingSpec.stoppedSigmaType.{u} :=
  @P207.stoppedSigma.{u}

noncomputable abbrev stoppedProcess : StoppingSpec.stoppedProcessType.{u} :=
  @P207.stoppedProcess.{u}

noncomputable abbrev fullStoppedValue : StoppingSpec.fullStoppedValueType.{u} :=
  @P207.fullStoppedValue.{u}

end StoppingInterfaces

theorem isDiscreteStoppingTime_iff (ℱ : Filtration ℕ m) (τ : Ω → WithTop ℕ) :
    IsDiscreteStoppingTime ℱ τ ↔ ∀ n : ℕ, MeasurableSet[ℱ n] {ω | τ ω ≤ n} := Iff.rfl

theorem stoppedSigma_membership {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) (A : Set Ω) :
    MeasurableSet[stoppedSigma hτ] A ↔
      MeasurableSet[terminalSigma ℱ] A ∧
        ∀ n : ℕ, MeasurableSet[ℱ n] (A ∩ {ω | τ ω ≤ n}) := Iff.rfl

theorem stopping_layer_measurable {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) (n : ℕ) :
    MeasurableSet[ℱ n] {ω | τ ω = n} := MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable hτ n

theorem stopping_layer_stopped_measurable {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) (n : ℕ) :
    MeasurableSet[stoppedSigma hτ] {ω | τ ω = n} := MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable' hτ n

theorem stoppedSigma_layers {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) (A : Set Ω) :
    MeasurableSet[stoppedSigma hτ] A ↔
      MeasurableSet[terminalSigma ℱ] A ∧
        ∀ n : ℕ, MeasurableSet[ℱ n] (A ∩ {ω | τ ω = n}) := by
  constructor
  · intro hA
    refine ⟨hA.1, fun n => ?_⟩
    exact (MeasureTheory.IsStoppingTime.measurableSet_inter_eq_iff hτ A n).mp
      (hA.inter (stopping_layer_stopped_measurable hτ n))
  · rintro ⟨hA, hlayers⟩
    refine ⟨hA, fun n => ?_⟩
    have heq : A ∩ {ω | τ ω ≤ n} = ⋃ k : ℕ, ⋃ (_ : k ≤ n),
        A ∩ {ω | τ ω = k} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨hω, hle⟩
        cases ht : τ ω with
        | top => simp [ht] at hle
        | coe k => exact ⟨k, WithTop.coe_le_coe.mp (ht ▸ hle), hω, rfl⟩
      · rintro ⟨k, hkn, hω, hk⟩
        exact ⟨hω, hk ▸ WithTop.coe_le_coe.mpr hkn⟩
    have hmeas : MeasurableSet[ℱ n] (⋃ k : ℕ, ⋃ (_ : k ≤ n),
        A ∩ {ω | τ ω = k}) :=
      MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun hkn =>
        ℱ.mono hkn _ (hlayers k)
    exact heq ▸ hmeas

theorem stopping_finite_measurable {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) :
    MeasurableSet[stoppedSigma hτ] {ω | τ ω < ⊤} := by
  exact measurableSet_lt (MeasureTheory.IsStoppingTime.measurable hτ) measurable_const

theorem stoppedSigma_mono {ℱ : Filtration ℕ m} {σ τ : Ω → WithTop ℕ}
    (hσ : IsDiscreteStoppingTime ℱ σ) (hτ : IsDiscreteStoppingTime ℱ τ)
    (hle : ∀ ω, σ ω ≤ τ ω) :
    stoppedSigma hσ ≤ stoppedSigma hτ := MeasureTheory.IsStoppingTime.measurableSpace_mono hσ hτ hle

theorem stoppedSigma_const (ℱ : Filtration ℕ m) (n : ℕ) :
    stoppedSigma (MeasureTheory.isStoppingTime_const ℱ n) = ℱ n := MeasureTheory.IsStoppingTime.measurableSpace_const ℱ n

theorem stoppedSigma_le_terminal {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) :
    stoppedSigma hτ ≤ terminalSigma ℱ := MeasureTheory.IsStoppingTime.measurableSpace_le' hτ

theorem stoppedProcess_min_finite (τ : Ω → WithTop ℕ) (n : ℕ) (ω : Ω) :
    min (n : WithTop ℕ) (τ ω) ≠ ⊤ := by
  exact ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)

theorem stoppedProcess_at_top (X : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (n : ℕ) (ω : Ω) (h : τ ω = ⊤) :
    stoppedProcess X τ n ω = X n ω := by simp [stoppedProcess, h]

theorem stoppedProcess_at_finite (X : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (n k : ℕ) (ω : Ω) (h : τ ω = k) :
    stoppedProcess X τ n ω = X (min n k) ω := by simp only [stoppedProcess, h]; rfl

theorem fullStoppedValue_at_top (X : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (Y : Ω → ℝ) (ω : Ω) (h : τ ω = ⊤) :
    fullStoppedValue X τ Y ω = Y ω := by simp [fullStoppedValue, h]

theorem fullStoppedValue_at_finite (X : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (Y : Ω → ℝ) (n : ℕ) (ω : Ω) (h : τ ω = n) :
    fullStoppedValue X τ Y ω = X n ω := by simp [fullStoppedValue, h]

theorem adapted_stoppedProcess {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) (X : ℕ → Ω → ℝ) (hX : Adapted ℱ X) :
    Adapted ℱ (stoppedProcess X τ) := (hX.stronglyAdapted.stoppedProcess_of_discrete hτ).adapted

theorem integrable_stoppedProcess {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) (X : ℕ → Ω → ℝ) (μ : Measure Ω)
    (hX : ∀ k, Integrable (X k) μ) (n : ℕ) :
    Integrable (stoppedProcess X τ n) μ := MeasureTheory.integrable_stoppedProcess hτ hX n

theorem measurable_fullStoppedValue {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) (X : ℕ → Ω → ℝ) (hX : Adapted ℱ X)
    (Y : Ω → ℝ) (hY : Measurable[terminalSigma ℱ] Y) :
    Measurable[stoppedSigma hτ] (fullStoppedValue X τ Y) := by
  intro B hB
  apply (stoppedSigma_layers hτ _).mpr
  constructor
  · have heq : fullStoppedValue X τ Y ⁻¹' B =
        (⋃ k : ℕ, X k ⁻¹' B ∩ {ω | τ ω = k}) ∪
          (Y ⁻¹' B ∩ {ω | τ ω = ⊤}) := by
      ext ω
      cases ht : τ ω with
      | top => simp [fullStoppedValue, ht]
      | coe k => simp [fullStoppedValue, ht]
    rw [heq]
    refine (MeasurableSet.iUnion fun k => ?_).union ?_
    · exact le_iSup ℱ k _ ((hB.preimage (hX k)).inter (stopping_layer_measurable hτ k))
    · exact (hB.preimage hY).inter (MeasureTheory.IsStoppingTime.measurableSet_eq_top' hτ)
  · intro n
    have heq : fullStoppedValue X τ Y ⁻¹' B ∩ {ω | τ ω = n} =
        X n ⁻¹' B ∩ {ω | τ ω = n} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hBω, hω⟩
        exact ⟨by simpa [fullStoppedValue, hω] using hBω, hω⟩
      · rintro ⟨hBω, hω⟩
        exact ⟨by simpa [fullStoppedValue, hω] using hBω, hω⟩
    rw [heq]
    exact (hB.preimage (hX n)).inter (stopping_layer_measurable hτ n)

theorem integrable_fullStoppedValue_bounded {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (μ : Measure Ω) (hX : ∀ k, Integrable (X k) μ)
    (N : ℕ) (hbound : ∀ ω, τ ω ≤ N) :
    Integrable (fullStoppedValue X τ Y) μ := by
  have heq : fullStoppedValue X τ Y = MeasureTheory.stoppedValue X τ := by
    funext ω
    have ht : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hbound ω)
    simp [fullStoppedValue, MeasureTheory.stoppedValue, ht]
  rw [heq]
  exact MeasureTheory.integrable_stoppedValue ℕ hτ hX hbound

end P207
