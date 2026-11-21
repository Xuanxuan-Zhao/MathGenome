import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.ConvexFunctionExtremes
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Supplements.ConvexFunctionRepresentation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C24Faces
import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
import Mathlib.Tactic.Linarith

namespace ExpandedFA.Supplements.ConvexFunctionExtremes
open Set MeasureTheory
open ConvexFunctionRepresentationSpec ConvexFunctionExtremesSpec
open ConvexFunctionRepresentation
open scoped ENNReal Topology

lemma mixture_combination (μ ν : Measure UnitInterval) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞) (x : UnitInterval) :
    mixture (a • μ + b • ν) (x : ℝ) =
      a.toReal * mixture μ (x : ℝ) + b.toReal * mixture ν (x : ℝ) := by
  unfold mixture
  rw [integral_add_measure ((hinge_integrable μ x.property).smul_measure ha)
    ((hinge_integrable ν x.property).smul_measure hb), integral_smul_measure,
    integral_smul_measure]
  rfl

lemma combination_probability (μ ν : Measure UnitInterval)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a b : ℝ≥0∞) (hab : a + b = 1) : IsProbabilityMeasure (a • μ + b • ν) := by
  constructor
  simpa only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] using hab

lemma coefficient_ne_top {a b : ℝ≥0∞} (h : a + b = 1) : a ≠ ∞ := by
  have ha : a ≤ 1 := by rw [← h]; exact le_add_right le_rfl
  exact ne_top_of_le_ne_top ENNReal.one_ne_top ha

lemma probabilityMap_mem (μ : ProbabilityMeasure UnitInterval) : probabilityMap μ ∈ normalizedSet :=
  (subtype_converse (μ : Measure UnitInterval) μ.property).2

lemma probabilityMap_continuous : Continuous probabilityMap := by
  apply continuous_pi
  intro x
  exact ProbabilityMeasure.continuous_integral_continuousMap
    (⟨fun r => hinge r (x : ℝ), continuous_hinge_parameter x.property⟩ : C(UnitInterval, ℝ))

lemma probabilityMap_injective : Function.Injective probabilityMap := by
  intro μ ν h
  apply ProbabilityMeasure.toMeasure_injective
  apply mixture_injective
  intro x hx
  exact congrFun h ⟨x, hx⟩

lemma probabilityMap_range : Set.range probabilityMap = normalizedSet := by
  apply Set.Subset.antisymm
  · rintro f ⟨μ, rfl⟩
    exact probabilityMap_mem μ
  · intro f hf
    obtain ⟨μ, hμ, _⟩ := subtype_representation f hf
    refine ⟨⟨μ, hμ.1⟩, ?_⟩
    funext x
    exact (hμ.2.2 x).2.symm

theorem affine_representation : AffineRepresentation := by
  refine ⟨probabilityMap_continuous, probabilityMap_injective, probabilityMap_range, ?_⟩
  intro μ ν a b hμ hν hab x
  letI := hμ
  letI := hν
  exact mixture_combination μ ν a b (coefficient_ne_top hab)
    (coefficient_ne_top (add_comm a b ▸ hab)) x

theorem compact_convex : CompactConvex := by
  constructor
  · rw [← probabilityMap_range]
    exact isCompact_range probabilityMap_continuous
  · intro f hf g hg a b ha hb hab
    obtain ⟨μ, hμ, _⟩ := subtype_representation f hf
    obtain ⟨ν, hν, _⟩ := subtype_representation g hg
    letI := hμ.1
    letI := hν.1
    have hab' : ENNReal.ofReal a + ENNReal.ofReal b = 1 := by
      rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]
    let ρ := ENNReal.ofReal a • μ + ENNReal.ofReal b • ν
    letI : IsProbabilityMeasure ρ := combination_probability μ ν _ _ hab'
    have hr := (subtype_converse ρ inferInstance).2
    have heq : (a • f + b • g) = fun x : UnitInterval => mixture ρ (x : ℝ) := by
      funext x
      rw [mixture_combination μ ν _ _ ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]
      change a * f x + b * g x = _
      rw [(hμ.2.2 x).2, (hν.2.2 x).2]
    exact heq ▸ hr

theorem representation : ConvexFunctionExtremesSpec.Representation :=
  subtype_representation

/-- Concentration on one point determines a probability measure. -/
lemma eq_dirac_of_compl_singleton (μ : Measure UnitInterval) [IsProbabilityMeasure μ]
    (r : UnitInterval) (h : μ ({r}ᶜ) = 0) : μ = Measure.dirac r := by
  have hr : μ {r} = 1 := (prob_compl_eq_zero_iff (measurableSet_singleton r)).mp h
  ext s hs
  by_cases hrs : r ∈ s
  · rw [Measure.dirac_apply_of_mem hrs]
    exact le_antisymm prob_le_one (hr ▸ measure_mono (singleton_subset_iff.mpr hrs))
  · rw [Measure.dirac_apply, Set.indicator_of_notMem hrs]
    have hsub : s ⊆ ({r}ᶜ : Set UnitInterval) := by
      intro x hx
      simp only [mem_compl_iff, mem_singleton_iff]
      intro hxr
      exact hrs (hxr ▸ hx)
    exact le_antisymm ((measure_mono hsub).trans_eq h) bot_le

lemma hingeFunction_mem (r : UnitInterval) : hingeFunction r ∈ normalizedSet := by
  have h := probabilityMap_mem ⟨Measure.dirac r, inferInstance⟩
  have he : probabilityMap ⟨Measure.dirac r, inferInstance⟩ = hingeFunction r := by
    funext x
    simp [probabilityMap, mixture, hingeFunction]
  rwa [he] at h

/-- A Dirac mixture cannot have a nontrivial convex decomposition. -/
lemma hingeFunction_extreme (r : UnitInterval) :
    hingeFunction r ∈ ExpandedFA.P1.extremePoints normalizedSet := by
  refine ⟨hingeFunction_mem r, ?_⟩
  intro f hf g hg t ht0 ht1 hfg
  obtain ⟨μ, hμ, _⟩ := subtype_representation f hf
  obtain ⟨ν, hν, _⟩ := subtype_representation g hg
  letI := hμ.1
  letI := hν.1
  let a := ENNReal.ofReal t
  let b := ENNReal.ofReal (1-t)
  have hb0 : 0 < 1-t := sub_pos.mpr ht1
  have hab : a + b = 1 := by
    dsimp [a, b]
    rw [← ENNReal.ofReal_add ht0.le hb0.le]
    simp
  let ρ := a • μ + b • ν
  letI : IsProbabilityMeasure ρ := combination_probability μ ν a b hab
  have he : ρ = Measure.dirac r := by
    apply mixture_injective
    intro x hx
    rw [show mixture (Measure.dirac r) x = hinge r x by simp [mixture]]
    have hv := congrFun hfg ⟨x, hx⟩
    rw [show mixture ρ x = a.toReal * mixture μ x + b.toReal * mixture ν x from
      mixture_combination μ ν a b (coefficient_ne_top hab)
        (coefficient_ne_top (add_comm a b ▸ hab)) ⟨x, hx⟩]
    simpa [a, b, ENNReal.toReal_ofReal ht0.le, ENNReal.toReal_ofReal hb0.le,
      hingeFunction, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
      ← (hμ.2.2 ⟨x,hx⟩).2, ← (hν.2.2 ⟨x,hx⟩).2] using hv.symm
  have hz : a * μ ({r}ᶜ) + b * ν ({r}ᶜ) = 0 := by
    have hh := congrArg (fun θ : Measure UnitInterval => θ ({r}ᶜ)) he
    simpa [ρ, Measure.add_apply, Measure.smul_apply] using hh
  have hm0 : μ ({r}ᶜ) = 0 := by
    have hh := (add_eq_zero.mp hz).1
    exact (mul_eq_zero.mp hh).resolve_left (ENNReal.ofReal_pos.mpr ht0).ne'
  have hn0 : ν ({r}ᶜ) = 0 := by
    have hh := (add_eq_zero.mp hz).2
    exact (mul_eq_zero.mp hh).resolve_left (ENNReal.ofReal_pos.mpr hb0).ne'
  have hm := eq_dirac_of_compl_singleton μ r hm0
  have hn := eq_dirac_of_compl_singleton ν r hn0
  constructor
  · funext x
    rw [(hμ.2.2 x).2, hm]
    simp [mixture, hingeFunction]
  · funext x
    rw [(hν.2.2 x).2, hn]
    simp [mixture, hingeFunction]

/-- An extreme mixture's representing measure only takes the values zero and one:
otherwise its normalized restrictions give a proper convex decomposition. -/
lemma extreme_measure_zero_one (f : FunctionSpace)
    (hf : f ∈ ExpandedFA.P1.extremePoints normalizedSet)
    (μ : Measure UnitInterval) (hμ : IntervalRepresents μ f) : IsZeroOneMeasure μ := by
  letI := hμ.1
  constructor
  intro s hs
  by_cases hs0 : μ s = 0
  · exact Or.inl hs0
  by_cases hs1 : μ s = 1
  · exact Or.inr hs1
  exfalso
  have hc0 : μ sᶜ ≠ 0 := by
    intro hh
    exact hs1 ((prob_compl_eq_zero_iff hs).mp hh)
  let ν := (μ s)⁻¹ • μ.restrict s
  let η := (μ sᶜ)⁻¹ • μ.restrict sᶜ
  have hν : IsProbabilityMeasure ν := by
    constructor
    simp only [ν, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hs0 (measure_ne_top _ _)
  have hη : IsProbabilityMeasure η := by
    constructor
    simp only [η, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hc0 (measure_ne_top _ _)
  letI := hν
  letI := hη
  have hsplit : μ s • ν + μ sᶜ • η = μ := by
    dsimp [ν, η]
    rw [smul_smul, smul_smul, ENNReal.mul_inv_cancel hs0 (measure_ne_top _ _),
      ENNReal.mul_inv_cancel hc0 (measure_ne_top _ _), one_smul, one_smul,
      Measure.restrict_add_restrict_compl hs]
  have hp0 : 0 < (μ s).toReal := ENNReal.toReal_pos hs0 (measure_ne_top _ _)
  have hq0 : 0 < (μ sᶜ).toReal := ENNReal.toReal_pos hc0 (measure_ne_top _ _)
  have hpq : (μ s).toReal + (μ sᶜ).toReal = 1 := probReal_add_probReal_compl hs
  let g := probabilityMap ⟨ν, hν⟩
  let k := probabilityMap ⟨η, hη⟩
  have hcomb : f = (μ s).toReal • g + (1 - (μ s).toReal) • k := by
    funext x
    rw [(hμ.2.2 x).2]
    conv_lhs => rw [← hsplit]
    rw [mixture_combination ν η _ _ (measure_ne_top _ _) (measure_ne_top _ _) x]
    change _ = (μ s).toReal * mixture ν (x : ℝ) + (1-(μ s).toReal) * mixture η (x : ℝ)
    congr 1
    congr 1
    linarith
  have hgf : g = f := (hf.2 g (probabilityMap_mem _) k (probabilityMap_mem _)
    (μ s).toReal hp0 (by linarith) hcomb).1
  have hμν : μ = ν := by
    apply mixture_injective
    intro x hx
    exact ((hμ.2.2 ⟨x,hx⟩).2.symm.trans (congrFun hgf ⟨x,hx⟩).symm)
  apply hc0
  rw [hμν]
  simp [ν, Measure.restrict_apply, hs.compl]

theorem classification : Classification := by
  apply Set.Subset.antisymm
  · intro f hf
    obtain ⟨μ, hμ, _⟩ := subtype_representation f hf.1
    letI := hμ.1
    letI := extreme_measure_zero_one f hf μ hμ
    obtain ⟨r, hr⟩ := IsZeroOneMeasure.exists_eq_dirac (μ := μ)
    refine ⟨r, ?_⟩
    funext x
    rw [(hμ.2.2 x).2, hr]
    simp [mixture, hingeFunction]
  · rintro f ⟨r, rfl⟩
    exact hingeFunction_extreme r

end ExpandedFA.Supplements.ConvexFunctionExtremes
