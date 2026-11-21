import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.Modifications

open MeasureTheory Set TopologicalSpace

universe u v w

namespace ProbabilityFoundations.Ch05

/-- `Y` is a modification of `X` if each fixed coordinate agrees with probability one. -/
def IsModification {ι : Type u} {Ω : Type v} {S : Type w} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : ι → Ω → S) : Prop :=
  ∀ t, P {ω | X t ω = Y t ω} = 1

/-- Indistinguishable processes agree at every time on one measurable probability-one event. -/
def Indistinguishable {ι : Type u} {Ω : Type v} {S : Type w} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : ι → Ω → S) : Prop :=
  ∃ G, MeasurableSet G ∧ P G = 1 ∧ ∀ ω ∈ G, ∀ t, X t ω = Y t ω

/-- The continuity event is required to be measurable in the original sigma-algebra. -/
def HasAlmostSurelyContinuousPaths {ι : Type u} {Ω : Type v} {S : Type w}
    [TopologicalSpace ι] [MeasurableSpace Ω] [TopologicalSpace S]
    (P : Measure Ω) (X : ι → Ω → S) : Prop :=
  ∃ G, MeasurableSet G ∧ P G = 1 ∧ ∀ ω ∈ G, Continuous (fun t => X t ω)

theorem fixedTimeEqualityMeasurable
    {T : ℝ} {Ω : Type v} {S : Type w} [MeasurableSpace Ω]
    [MetricSpace S] [SeparableSpace S] [MeasurableSpace S] [BorelSpace S]
    (X Y : Time T → Ω → S)
    (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t)) (t : Time T) :
    MeasurableSet {ω | X t ω = Y t ω} :=
  measurableSet_eq_fun (hX t) (hY t)

/-- Agreement on a common countable dense set extends to all times by continuity.
This applies also when `T = 0`, without a positive-length hypothesis. -/
theorem continuousModificationsUnique
    {T : ℝ} {Ω : Type v} {S : Type w} [MeasurableSpace Ω]
    [MetricSpace S] [SeparableSpace S] [MeasurableSpace S] [BorelSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y Z : Time T → Ω → S)
    (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t))
    (hZ : ∀ t, Measurable (Z t))
    (hXY : IsModification P X Y) (hXZ : IsModification P X Z)
    (hcY : HasAlmostSurelyContinuousPaths P Y)
    (hcZ : HasAlmostSurelyContinuousPaths P Z) : Indistinguishable P Y Z := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense (Time T)
  obtain ⟨A, hAm, hAp, hAc⟩ := hcY
  obtain ⟨B, hBm, hBp, hBc⟩ := hcZ
  have heq (t : Time T) : ∀ᵐ ω ∂P, Y t ω = Z t ω := by
    have h1 : ∀ᵐ ω ∂P, X t ω = Y t ω :=
      (mem_ae_iff_prob_eq_one (measurableSet_eq_fun (hX t) (hY t))).2 (hXY t)
    have h2 : ∀ᵐ ω ∂P, X t ω = Z t ω :=
      (mem_ae_iff_prob_eq_one (measurableSet_eq_fun (hX t) (hZ t))).2 (hXZ t)
    filter_upwards [h1, h2] with ω h1 h2 using h1.symm.trans h2
  let E : Set Ω := {ω | ∀ t ∈ D, Y t ω = Z t ω}
  have hEm : MeasurableSet E := by
    simpa only [E, ofPred_forall] using
      MeasurableSet.biInter hDc (fun t _ => measurableSet_eq_fun (hY t) (hZ t))
  have hEa : E ∈ ae P := (ae_ball_iff hDc).2 (fun t _ => heq t)
  have hAa : A ∈ ae P := (mem_ae_iff_prob_eq_one hAm).2 hAp
  have hBa : B ∈ ae P := (mem_ae_iff_prob_eq_one hBm).2 hBp
  refine ⟨A ∩ B ∩ E, (hAm.inter hBm).inter hEm, ?_, ?_⟩
  · exact (mem_ae_iff_prob_eq_one ((hAm.inter hBm).inter hEm)).1
      (Filter.inter_mem (Filter.inter_mem hAa hBa) hEa)
  · intro ω hω t
    exact congrFun ((hAc ω hω.1.1).ext_on hDd (hBc ω hω.1.2) hω.2) t

end ProbabilityFoundations.Ch05
