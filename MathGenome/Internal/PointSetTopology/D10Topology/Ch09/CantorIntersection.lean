import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.CantorIntersection
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricConventions

/-!
Cantor's intersection criterion (paper.tex, d10:09:cantor-intersection),
including the singleton conclusion repeated in d10:14:nested-closed.
The extended diameter is used throughout, including for unbounded early sets.
-/

open Set Filter
open scoped Topology ENNReal
universe u

namespace D10Topology.Ch09

theorem shrinking_intersection_subsingleton {X : Type u} (d : MetricSpace X)
    (F : ℕ → Set X)
    (hdiam : Tendsto (fun n => diameter d.toPseudoMetricSpace (F n)) atTop (𝓝 0)) :
    (⋂ n, F n).Subsingleton := by
  let := d
  intro x hx y hy
  apply edist_eq_zero.mp
  apply le_antisymm _ bot_le
  apply ge_of_tendsto hdiam
  exact Eventually.of_forall fun n => by
    rw [diameter_eq_mathlib]
    exact Metric.edist_le_ediam_of_mem (mem_iInter.mp hx n) (mem_iInter.mp hy n)

theorem cantor_intersection_singleton {X : Type u} (d : MetricSpace X)
    (hc : SequentiallyComplete d.toPseudoMetricSpace)
    (F : ℕ → Set X) (hanti : Antitone F) (hne : ∀ n, (F n).Nonempty)
    (hclosed : ∀ n, IsClosed[metricTopology d.toPseudoMetricSpace] (F n))
    (hdiam : Tendsto (fun n => diameter d.toPseudoMetricSpace (F n)) atTop (𝓝 0)) :
    ∃ x : X, (⋂ n, F n) = {x} := by
  classical
  let := d
  choose s hs using hne
  have hcs : CauchySeq s := EMetric.cauchySeq_iff_le_tendsto_0.mpr
    ⟨fun n => diameter d.toPseudoMetricSpace (F n), fun n m N hn hm => by
      change edist (s n) (s m) ≤ diameter d.toPseudoMetricSpace (F N)
      rw [diameter_eq_mathlib]
      exact Metric.edist_le_ediam_of_mem (hanti hn (hs n)) (hanti hm (hs m)), hdiam⟩
  obtain ⟨x, hx⟩ := hc s ((cauchySequence_iff_mathlib _ _).mpr hcs)
  have hxF : x ∈ ⋂ n, F n := mem_iInter.mpr fun N =>
    (hclosed N).mem_of_tendsto ((sequenceConverges_iff_mathlib _ _ _).mp hx)
      ((eventually_ge_atTop N).mono fun n hn => hanti hn (hs n))
  refine ⟨x, ?_⟩
  ext y
  exact ⟨fun hy => (shrinking_intersection_subsingleton d F hdiam hy hxF),
    fun hy => (mem_singleton_iff.mp hy) ▸ hxF⟩

theorem complete_iff_cantor_intersection {X : Type u} (d : MetricSpace X) :
    SequentiallyComplete d.toPseudoMetricSpace ↔
      ∀ F : ℕ → Set X, Antitone F →
        (∀ n, (F n).Nonempty) →
        (∀ n, IsClosed[metricTopology d.toPseudoMetricSpace] (F n)) →
        Tendsto (fun n => diameter d.toPseudoMetricSpace (F n)) atTop (𝓝 0) →
        (⋂ n, F n).Nonempty := by
  let := d
  constructor
  · intro hc F ha hn hcl hd
    obtain ⟨x, hx⟩ := cantor_intersection_singleton d hc F ha hn hcl hd
    exact ⟨x, hx.symm ▸ mem_singleton x⟩
  · intro h s hs
    let F : ℕ → Set X := fun n => closure (s '' Ici n)
    have hanti : Antitone F := fun _ _ hnm =>
      closure_mono (image_mono (Ici_subset_Ici.mpr hnm))
    have hmem : ∀ n, s n ∈ F n := fun n =>
      subset_closure (mem_image_of_mem s (mem_Ici.mpr le_rfl))
    have hne : ∀ n, (F n).Nonempty := fun n => ⟨s n, hmem n⟩
    obtain ⟨b, hb, hblim⟩ := EMetric.cauchySeq_iff_le_tendsto_0.mp
      ((cauchySequence_iff_mathlib _ _).mp hs)
    have hdle : ∀ n, diameter d.toPseudoMetricSpace (F n) ≤ b n := by
      intro n
      rw [diameter_eq_mathlib]
      change Metric.ediam (closure (s '' Ici n)) ≤ b n
      rw [Metric.ediam_closure]
      apply Metric.ediam_le
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      exact hb i j n hi hj
    have hd : Tendsto (fun n => diameter d.toPseudoMetricSpace (F n)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hblim
        (fun _ => bot_le) hdle
    obtain ⟨x, hx⟩ := h F hanti hne (fun _ => isClosed_closure) hd
    refine ⟨x, (sequenceConverges_iff_mathlib _ _ _).mpr ?_⟩
    apply tendsto_iff_edist_tendsto_0.mpr
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hd
      (fun _ => bot_le)
    intro n
    change edist (s n) x ≤ diameter d.toPseudoMetricSpace (F n)
    rw [diameter_eq_mathlib]
    exact Metric.edist_le_ediam_of_mem (hmem n) (mem_iInter.mp hx n)

end D10Topology.Ch09
