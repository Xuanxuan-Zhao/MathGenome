import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.ContinuousProcessLaw
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch05.DenseEvaluationBorel
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch05.Modifications
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.LawsAndTransfer
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.DeterminingClasses
import Mathlib.MeasureTheory.Constructions.Projective

open MeasureTheory Set TopologicalSpace

namespace ProbabilityFoundations.Ch05

variable {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MetricSpace S] [Nonempty S] [SeparableSpace S] [MeasurableSpace S] [BorelSpace S]

theorem continuousProcess_measurable : ProcessLawSpec.PathMapMeasurable (Ω := Ω) (S := S) := by
  intro T hT D hDc hDd X hc hX
  apply measurable_iff_comap_le.mpr
  change (borel C(Time T, S)).comap (continuousProcessPath X hc) ≤ _
  rw [denseEvaluation_borel S T hT D hDc hDd, MeasurableSpace.comap_iSup]
  refine iSup_le fun t => ?_
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, continuousProcessPath,
    ContinuousMap.coe_mk, BorelSpace.measurable_eq] using (hX t.1).comap_le

theorem continuousProcessLaw_marginals : ProcessLawSpec.PathLawMarginals (Ω := Ω) (S := S) := by
  intro T hT D hDc hDd P _ X hc hX
  have hm := continuousProcess_measurable T hT D hDc hDd X hc hX
  refine ⟨Ch01.law_probability P _ hm, ?_⟩
  intro n τ
  exact Measure.map_map (measurable_pi_iff.mpr fun i => ContinuousMap.measurable_eval (τ i)) hm

/-- The path sigma-algebra is the pullback of the product sigma-algebra on dense times.
No measurability of the image of the restriction map is needed. -/
private theorem pathBorel_comap_dense {T : ℝ} (hT : 0 < T) (D : Set (Time T))
    (hDc : D.Countable) (hDd : Dense D) :
    borel C(Time T, S) =
      (MeasurableSpace.pi : MeasurableSpace (D → S)).comap
        (fun f : C(Time T, S) => fun t : D => f t.1) := by
  rw [denseEvaluation_borel S T hT D hDc hDd,
    MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  simp only [MeasurableSpace.comap_comp, Function.comp_def, BorelSpace.measurable_eq]

theorem continuousPathMeasure_unique : ProcessLawSpec.PathMeasureUnique (S := S) := by
  intro T hT D hDc hDd μ ν _ _ hfinite
  let R : C(Time T, S) → D → S := fun f t => f t.1
  have hR : Measurable R := measurable_pi_iff.mpr fun t => ContinuousMap.measurable_eval t.1
  have hmap : μ.map R = ν.map R := by
    let P : (I : Finset D) → Measure (I → S) := fun I =>
      ν.map (fun f : C(Time T, S) => fun i : I => f i.1.1)
    haveI (I : Finset D) : IsProbabilityMeasure (P I) :=
      Ch01.law_probability ν _ (measurable_pi_iff.mpr fun i =>
        ContinuousMap.measurable_eval i.1.1)
    have hμ : IsProjectiveLimit (μ.map R) P := by
      intro I
      rw [Measure.map_map (Finset.measurable_restrict I) hR]
      exact hfinite I
    have hν : IsProjectiveLimit (ν.map R) P := by
      intro I
      exact Measure.map_map (Finset.measurable_restrict I) hR
    exact hμ.unique hν
  apply Measure.ext
  intro A hA
  have hA' : MeasurableSet[(MeasurableSpace.pi : MeasurableSpace (D → S)).comap R] A := by
    rw [← pathBorel_comap_dense hT D hDc hDd]
    exact hA
  obtain ⟨B, hB, rfl⟩ := hA'
  rw [← Measure.map_apply hR hB, ← Measure.map_apply hR hB, hmap]

/-- Finite tuples may be enumerated in any order, including the empty tuple. -/
theorem continuousProcessLaw_unique : ProcessLawSpec.ProcessLawUnique
    (Ω := Ω) (Ω' := Ω') (S := S) := by
  classical
  intro T hT D hDc hDd P Q _ _ F H hF hH hfd
  haveI : IsProbabilityMeasure (Measure.map F P) := Ch01.law_probability P F hF
  haveI : IsProbabilityMeasure (Measure.map H Q) := Ch01.law_probability Q H hH
  apply continuousPathMeasure_unique T hT D hDc hDd
  intro I
  let e := Fintype.equivFin I
  let τ : Fin (Fintype.card I) → D := fun j => (e.symm j).1
  let r : (Fin (Fintype.card I) → S) → I → S := fun x i => x (e i)
  have hr : Measurable r := measurable_pi_iff.mpr fun i => measurable_pi_apply (e i)
  have hFt : Measurable (fun ω => fun j => F ω (τ j).1) :=
    measurable_pi_iff.mpr fun j => (ContinuousMap.measurable_eval (τ j).1).comp hF
  have hHt : Measurable (fun ω => fun j => H ω (τ j).1) :=
    measurable_pi_iff.mpr fun j => (ContinuousMap.measurable_eval (τ j).1).comp hH
  have h := congrArg (Measure.map r) (hfd (Fintype.card I) τ)
  rw [Measure.map_map hr hFt, Measure.map_map hr hHt] at h
  have hm : Measurable (fun f : C(Time T, S) => fun i : I => f i.1.1) :=
    measurable_pi_iff.mpr fun i => ContinuousMap.measurable_eval i.1.1
  rw [Measure.map_map hm hF, Measure.map_map hm hH]
  simpa [Function.comp_def, r, τ] using h

theorem constantPathExtension_properties : ProcessLawSpec.ConstantExtensionProperties
    (Ω := Ω) (S := S) := by
  classical
  intro T hT D hDc hDd P _ X G hG hP hc s₀ hX
  let F := constantPathExtension X G hc s₀
  have hcoord (t : Time T) : (fun ω => F ω t) = G.piecewise (X t) (fun _ => s₀) := by
    funext ω
    by_cases hω : ω ∈ G <;> simp [F, constantPathExtension, Set.piecewise, hω]
  have hmcoord (t : Time T) : Measurable (fun ω => F ω t) := by
    rw [hcoord]
    exact Measurable.piecewise hG (hX t) measurable_const
  have hm : Measurable F := ContinuousMap.measurable_iff_eval.mpr hmcoord
  have hon : ∀ ω ∈ G, ∀ t, F ω t = X t ω := by
    intro ω hω t
    simp [F, constantPathExtension, hω]
  have hoff : ∀ ω ∉ G, ∀ t, F ω t = s₀ := by
    intro ω hω t
    simp [F, constantPathExtension, hω]
  have hGa : G ∈ ae P := (mem_ae_iff_prob_eq_one hG).2 hP
  refine ⟨hm, Ch01.law_probability P F hm, hon, hoff, ?_, ?_⟩
  · intro t
    apply (mem_ae_iff_prob_eq_one (measurableSet_eq_fun (hX t) (hmcoord t))).1
    filter_upwards [hGa] with ω hω using (hon ω hω t).symm
  · intro n τ
    apply Measure.map_congr
    filter_upwards [hGa] with ω hω
    exact funext fun i => hon ω hω (τ i)

theorem constantPathExtension_law_unique : ProcessLawSpec.ConstantExtensionUnique
    (Ω := Ω) (Ω' := Ω') (S := S) := by
  intro T hT D hDc hDd P Q _ _ X Y G K hG hK hP hQ hc hd s₀ s₁ hX hY hfd
  have hF := constantPathExtension_properties T hT D hDc hDd P X G hG hP hc s₀ hX
  have hH := constantPathExtension_properties T hT D hDc hDd Q Y K hK hQ hd s₁ hY
  apply continuousProcessLaw_unique T hT D hDc hDd P Q _ _ hF.1 hH.1
  intro n τ
  exact (hF.2.2.2.2.2 n (fun i => (τ i).1)).trans
    ((hfd n τ).trans (hH.2.2.2.2.2 n (fun i => (τ i).1)).symm)

end ProbabilityFoundations.Ch05
