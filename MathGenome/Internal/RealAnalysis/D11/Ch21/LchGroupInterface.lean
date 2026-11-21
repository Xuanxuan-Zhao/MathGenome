import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.LchGroupInterface

/-!
# Locally compact Hausdorff groups and translations

This is the interface of paper.tex, Chapter 21, `d11:21:lch-group-interface`.
We use the native `Group`, `IsTopologicalGroup`, `T2Space`, and
`LocallyCompactSpace` structures. In particular, the group need not have any
countability or metrizability property. The maps already exist on every
topological group; the final theorem specializes their properties to the
source's locally compact Hausdorff setting.
-/

namespace D11.Ch21

universe u

/-- A locally compact group in the source is also Hausdorff. -/
def IsLocallyCompactGroup (G : Type u) [TopologicalSpace G] [Group G] : Prop :=
  IsTopologicalGroup G ∧ T2Space G ∧ LocallyCompactSpace G

/-- The topological group axiom requires joint continuity of multiplication. -/
theorem isLocallyCompactGroup_iff (G : Type u) [TopologicalSpace G] [Group G] :
    IsLocallyCompactGroup G ↔
      Continuous (fun p : G × G => p.1 * p.2) ∧
      Continuous (fun x : G => x⁻¹) ∧ T2Space G ∧ LocallyCompactSpace G := by
  constructor
  · rintro ⟨hG, hT, hL⟩
    have := hG
    exact ⟨continuous_mul, continuous_inv, hT, hL⟩
  · rintro ⟨hm, hi, hT, hL⟩
    exact ⟨{ continuous_mul := hm, continuous_inv := hi }, hT, hL⟩

/-- Left translation `x ↦ a * x`, with inverse `x ↦ a⁻¹ * x`. -/
def leftTranslation (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (a : G) : G ≃ₜ G :=
  Homeomorph.mulLeft a

/-- Right translation `x ↦ x * a`, with inverse `x ↦ x * a⁻¹`. -/
def rightTranslation (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (a : G) : G ≃ₜ G :=
  Homeomorph.mulRight a

/-- Inversion is a homeomorphism and is its own inverse. -/
def inversion (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] : G ≃ₜ G :=
  Homeomorph.inv G

theorem translation_map_formulas (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (a x : G) :
    leftTranslation G a x = a * x ∧ rightTranslation G a x = x * a ∧
      inversion G x = x⁻¹ :=
  ⟨rfl, rfl, rfl⟩

theorem translation_inverse_formulas (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (a : G) :
    (leftTranslation G a).symm = leftTranslation G a⁻¹ ∧
    (rightTranslation G a).symm = rightTranslation G a⁻¹ ∧
    (inversion G).symm = inversion G :=
  ⟨Homeomorph.mulLeft_symm a, Homeomorph.mulRight_symm a, Homeomorph.symm_inv⟩

/-- A general homeomorphism gives all the preservation properties needed here. -/
theorem homeomorph_preserves_open_borel_compact (G : Type u) [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] (h : G ≃ₜ G) :
    Specs.D11.Ch21.LchGroupInterface.PreservesOpenBorelCompact G h := by
  refine ⟨h.continuous, h.measurable, ?_, ?_, ?_⟩
  · intro s
    exact ⟨h.isOpen_image, h.isOpen_preimage⟩
  · intro s
    exact ⟨h.toMeasurableEquiv.measurableSet_image,
      h.toMeasurableEquiv.measurableSet_preimage⟩
  · intro s
    exact ⟨h.isCompact_image, h.isCompact_preimage⟩

/-- Images and inverse images under translations and inversion preserve opens,
Borel sets, and compact sets. Each map is also continuous and Borel measurable. -/
theorem translations_preserve_open_borel_compact (G : Type u) [TopologicalSpace G]
    [Group G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (a : G) :
    Specs.D11.Ch21.LchGroupInterface.PreservesOpenBorelCompact G (fun x => a * x) ∧
    Specs.D11.Ch21.LchGroupInterface.PreservesOpenBorelCompact G (fun x => x * a) ∧
    Specs.D11.Ch21.LchGroupInterface.PreservesOpenBorelCompact G (fun x => x⁻¹) :=
  ⟨homeomorph_preserves_open_borel_compact G (leftTranslation G a),
    homeomorph_preserves_open_borel_compact G (rightTranslation G a),
    homeomorph_preserves_open_borel_compact G (inversion G)⟩

end D11.Ch21
