import MathGenome.Internal.RealAnalysis.D11.Ch21.ModularFunction
import MathGenome.Internal.RealAnalysis.D11.Ch21.HaarFiniteIffCompact
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.UnimodularCases

namespace D11.Ch21.UnimodularCases

open Set MeasureTheory
universe u
noncomputable section

local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G

/-- Unimodularity, independent of the choice of left Haar normalization. -/
def isUnimodular (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] : Prop :=
  Specs.D11.Ch21.UnimodularCases.isUnimodular_value G

section General
variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

theorem modular_eq_one_iff_rightHaar (μ : @Measure G (borel G))
    (hμ : isLeftHaarMeasure μ) :
    (∀ a : G, ModularFunction.modularFunction μ a = 1) ↔ isRightHaarMeasure μ := by
  constructor
  · intro h
    refine ⟨hμ.1, hμ.2.1, ?_⟩
    intro a E hE
    have hf := (ModularFunction.modularFunction_spec μ hμ a).2 E hE
    simpa only [h a, ENNReal.ofReal_one, one_mul] using hf
  · intro h a
    symm
    apply ModularFunction.modularFunction_unique μ hμ a 1
    refine ⟨zero_lt_one, ?_⟩
    intro E hE
    simpa only [ENNReal.ofReal_one, one_mul] using h.2.2 a E hE

theorem isUnimodular_iff : isUnimodular G ↔
    ∀ μ : @Measure G (borel G), isLeftHaarMeasure μ → isRightHaarMeasure μ := by
  constructor
  · intro h μ hμ
    exact (modular_eq_one_iff_rightHaar μ hμ).mp (h μ hμ)
  · intro h μ hμ
    exact (modular_eq_one_iff_rightHaar μ hμ).mpr (h μ hμ)

end General

theorem abelian_unimodular (G : Type u) [TopologicalSpace G] [CommGroup G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] : isUnimodular G := by
  apply isUnimodular_iff.mpr
  intro μ hμ
  refine ⟨hμ.1, hμ.2.1, ?_⟩
  intro a E hE
  simpa only [mul_comm] using hμ.2.2 a E hE

section Compact
variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [T2Space G] [CompactSpace G]

/-- The right-set scalar fixes finite, nonzero total mass, hence is one. -/
theorem compact_unimodular (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] : isUnimodular G := by
  intro μ hμ a
  change ModularFunction.modularFunction μ a = 1
  have hzero : μ univ ≠ 0 := fun hz => hμ.1 (Measure.measure_univ_eq_zero.mp hz)
  have htop : μ univ ≠ ⊤ := (hμ.2.1.1 univ isCompact_univ).ne
  have hf := ModularFunction.modularFunction_spec μ hμ a
  have himage : (fun x : G => x * a) '' univ = univ := by
    ext x
    simp only [mem_image, mem_univ, true_and, iff_true]
    exact ⟨x * a⁻¹, by simp⟩
  have heq := hf.2 univ MeasurableSet.univ
  rw [himage] at heq
  have hscalar : ENNReal.ofReal (ModularFunction.modularFunction μ a) = 1 := by
    calc
      ENNReal.ofReal (ModularFunction.modularFunction μ a) =
          (ENNReal.ofReal (ModularFunction.modularFunction μ a) * μ univ) *
            (μ univ)⁻¹ := by rw [mul_assoc, ENNReal.mul_inv_cancel hzero htop, mul_one]
      _ = μ univ * (μ univ)⁻¹ := by rw [← heq]
      _ = 1 := ENNReal.mul_inv_cancel hzero htop
  have hr := congrArg ENNReal.toReal hscalar
  simpa only [ENNReal.toReal_ofReal hf.1.le, ENNReal.toReal_one] using hr

theorem compact_probability_biinvariant (μ : @Measure G (borel G))
    (hμ : isLeftHaarMeasure μ) (_hmass : μ univ = 1)
    (a : G) (E : Set G) (hE : MeasurableSet[borel G] E) :
    μ ((fun x => a * x) '' E) = μ E ∧ μ ((fun x => x * a) '' E) = μ E := by
  exact ⟨hμ.2.2 a E hE,
    ((isUnimodular_iff.mp (compact_unimodular G)) μ hμ).2.2 a E hE⟩

theorem unique_biinvariant_probability (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] :
    ∃! μ : @Measure G (borel G),
      isLeftHaarMeasure μ ∧ isRightHaarMeasure μ ∧ μ univ = 1 := by
  obtain ⟨μ, ⟨hμ, hmass⟩, hu⟩ := HaarFiniteIffCompact.unique_probability G
  refine ⟨μ, ⟨hμ, ?_, hmass⟩, ?_⟩
  · exact isUnimodular_iff.mp (compact_unimodular G) μ hμ
  · intro ν hν
    exact hu ν ⟨hν.1, hν.2.2⟩

end Compact
end
end D11.Ch21.UnimodularCases
