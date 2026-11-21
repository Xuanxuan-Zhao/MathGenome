import MathGenome.Internal.RealAnalysis.D11.Ch21.HaarDefinition
import MathGenome.Internal.RealAnalysis.D11.Ch21.HaarExistence
import MathGenome.Internal.RealAnalysis.D11.Ch21.HaarUniqueness
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.HaarFiniteIffCompact
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Finite Haar mass and compactness

For the converse, open inner regularity supplies a compact set with more
than half the finite positive total mass. It intersects every left translate:
otherwise disjoint additivity exceeds the total mass. Consequently its
product with its inverse is the whole group and is compact. This proof
uses no countable exhaustion or sigma-finiteness assumption.
-/
namespace D11.Ch21.HaarFiniteIffCompact

open Set MeasureTheory
open scoped ENNReal Pointwise
universe u
noncomputable section

local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G
local instance {G : Type u} [TopologicalSpace G] : BorelSpace G := ⟨rfl⟩

section General
variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Finite total Haar mass characterizes compactness, without countability. -/
theorem finite_iff_compact (μ : @Measure G (borel G)) (hμ : isLeftHaarMeasure μ) :
    μ univ < ⊤ ↔ CompactSpace G := by
  constructor
  · intro hfin
    let : Measure.Regular μ := (D11.Ch18.isRadon_iff_regular μ).mp hμ.2.1
    have hpos : μ univ ≠ 0 := fun hz => hμ.1 (Measure.measure_univ_eq_zero.mp hz)
    obtain ⟨K, _hsub, hK, hmass⟩ := isOpen_univ.exists_lt_isCompact
      (μ := μ) (ENNReal.half_lt_self hpos hfin.ne)
    have hlarge : μ univ < μ K + μ K := by
      simpa only [ENNReal.add_halves] using ENNReal.add_lt_add hmass hmass
    have hmeet (a : G) : ¬ Disjoint K ((fun x => a * x) '' K) := by
      intro hdisj
      have hbound := measure_mono (μ := μ) (subset_univ (K ∪ (fun x => a * x) '' K))
      rw [measure_union' hdisj hK.measurableSet, hμ.2.2 a K hK.measurableSet] at hbound
      exact hlarge.not_ge hbound
    have heq : K * K⁻¹ = (univ : Set G) := by
      apply eq_univ_of_forall
      intro a
      obtain ⟨z, hz, y, hy, he⟩ := Set.not_disjoint_iff.mp (hmeet a)
      exact ⟨z, hz, y⁻¹, by simpa using hy, by rw [← he]; simp⟩
    exact ⟨heq ▸ hK.mul hK.inv⟩
  · intro hcompact
    let := hcompact
    exact hμ.2.1.1 univ isCompact_univ

end General

section Compact
variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [T2Space G] [CompactSpace G]

/-- Division by the positive finite total mass gives Haar probability. -/
theorem normalize_probability (μ : @Measure G (borel G)) (hμ : isLeftHaarMeasure μ) :
    isLeftHaarMeasure ((μ univ)⁻¹ • μ) ∧ ((μ univ)⁻¹ • μ) univ = 1 := by
  have hpos : μ univ ≠ 0 := fun hz => hμ.1 (Measure.measure_univ_eq_zero.mp hz)
  have hfinite : μ univ ≠ ⊤ := (hμ.2.1.1 univ isCompact_univ).ne
  have hmass : ((μ univ)⁻¹ • μ) univ = 1 := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hpos hfinite
  refine ⟨⟨?_, ?_, ?_⟩, hmass⟩
  · intro he
    rw [he] at hmass
    simp at hmass
  · let : Measure.Regular μ := (D11.Ch18.isRadon_iff_regular μ).mp hμ.2.1
    exact (D11.Ch18.isRadon_iff_regular _).mpr
      (Measure.Regular.smul (ENNReal.inv_ne_top.mpr hpos))
  · intro a E hE
    simp only [Measure.smul_apply, smul_eq_mul, hμ.2.2 a E hE]

/-- The compact Hausdorff group has one and only one left Haar probability. -/
theorem unique_probability (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] :
    ∃! μ : @Measure G (borel G), isLeftHaarMeasure μ ∧ μ univ = 1 := by
  obtain ⟨μ, hμ⟩ := D11.Ch21.haar_existence G
  let ν := (μ univ)⁻¹ • μ
  obtain ⟨hν, hνmass⟩ := normalize_probability μ hμ
  change ν univ = 1 at hνmass
  refine ⟨ν, ⟨hν, hνmass⟩, ?_⟩
  intro ρ hρ
  obtain ⟨c, hc, _hunique⟩ := HaarUniqueness.left_uniqueness ν ρ hν hρ.1
  have hscale := congrArg (fun m : @Measure G (borel G) => m univ) hc.2
  have hc1 : ENNReal.ofReal c = 1 := by
    simpa only [hρ.2, Measure.smul_apply, smul_eq_mul, hνmass, mul_one] using hscale.symm
  simpa only [hc1, one_smul] using hc.2

end Compact

end
end D11.Ch21.HaarFiniteIffCompact
