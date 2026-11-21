import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonProduct
import MathGenome.Internal.RealAnalysis.D11.Ch19.RecoverOpenCompactMass
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonProductOpenRectangles

/-! Open rectangles for the Radon product, without sigma-finiteness.
Open masses are recovered from Cc tests. Tensor tests give the lower bound;
compact cutoffs on the support projections dominate any admissible test and
give the upper bound. All suprema and products are in ENNReal. -/

noncomputable section
namespace D11.Ch18.RadonProductOpenRectangles
open Set MeasureTheory
open scoped ENNReal
universe u v

local instance {Z : Type*} [TopologicalSpace Z] : MeasurableSpace Z := borel Z
local instance {Z : Type*} [TopologicalSpace Z] : BorelSpace Z := ⟨rfl⟩

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]

/-- Open-mass recovery stated directly for the integration functional. -/
lemma open_mass_integral (μ : Measure X) (hμ : isRadon μ)
    (U : Set X) (hU : IsOpen U) :
    μ U = ⨆ f : CompactlySupportedContinuousMap X ℝ,
      ⨆ (_ : ∀ x, 0 ≤ f x ∧ f x ≤ 1),
        ⨆ (_ : tsupport f ⊆ U), ENNReal.ofReal (∫ x, f x ∂μ) := by
  obtain ⟨I, hI, hrep⟩ := Ch19.PositiveRieszMarkov.radon_induces_real_functional μ hμ
  rw [Ch19.RecoverOpenCompactMass.real_open_mass I hI μ hrep U hU]
  simp only [(hrep.2 _).2]
  rfl

/-- Compactly supported separate-variable product. -/
def tensor (a : CompactlySupportedContinuousMap X ℝ)
    (b : CompactlySupportedContinuousMap Y ℝ) :
    CompactlySupportedContinuousMap (X × Y) ℝ where
  toFun p := a p.1 * b p.2
  continuous_toFun := (a.continuous.comp continuous_fst).mul
    (b.continuous.comp continuous_snd)
  hasCompactSupport' := (a.hasCompactSupport.prod b.hasCompactSupport).of_isClosed_subset
    (isClosed_tsupport _) (by
      apply closure_minimal _ ((isClosed_tsupport a).prod (isClosed_tsupport b))
      intro p hp
      exact ⟨subset_tsupport a (left_ne_zero_of_mul hp),
        subset_tsupport b (right_ne_zero_of_mul hp)⟩)

omit [T2Space X] [LocallyCompactSpace X] [T2Space Y] [LocallyCompactSpace Y] in
lemma tensor_support (a : CompactlySupportedContinuousMap X ℝ)
    (b : CompactlySupportedContinuousMap Y ℝ) :
    tsupport (tensor a b) ⊆ tsupport a ×ˢ tsupport b := by
  apply closure_minimal _ ((isClosed_tsupport a).prod (isClosed_tsupport b))
  intro p hp
  exact ⟨subset_tsupport a (left_ne_zero_of_mul hp),
    subset_tsupport b (right_ne_zero_of_mul hp)⟩

omit [T2Space X] [LocallyCompactSpace X] [T2Space Y] [LocallyCompactSpace Y] in
lemma tensor_bounds (a : CompactlySupportedContinuousMap X ℝ)
    (b : CompactlySupportedContinuousMap Y ℝ)
    (ha : ∀ x, 0 ≤ a x ∧ a x ≤ 1) (hb : ∀ y, 0 ≤ b y ∧ b y ≤ 1) :
    ∀ p, 0 ≤ tensor a b p ∧ tensor a b p ≤ 1 := by
  intro p
  exact ⟨mul_nonneg (ha p.1).1 (hb p.2).1,
    (mul_le_mul (ha p.1).2 (hb p.2).2 (hb p.2).1 zero_le_one).trans_eq (one_mul 1)⟩

/-- The defining Cc law evaluates tensor tests exactly. -/
lemma tensor_integral (μ : Measure X) (ν : Measure Y)
    (hμ : isRadon μ) (hν : isRadon ν)
    (a : CompactlySupportedContinuousMap X ℝ)
    (b : CompactlySupportedContinuousMap Y ℝ) :
    (∫ p, tensor a b p ∂(RadonProduct.radonProduct μ ν)) =
      (∫ x, a x ∂μ) * (∫ y, b y ∂ν) := by
  rw [(RadonProduct.radonProduct_law μ ν hμ hν).2 (tensor a b) |>.2]
  change (∫ x, (∫ y, a x * b y ∂ν) ∂μ) = _
  simp only [integral_const_mul, integral_mul_const]


/-- An admissible Cc integral is bounded by the mass of its supporting open. -/
lemma test_integral_le_open (μ : Measure X) (hμ : isRadon μ)
    (U : Set X) (hU : IsOpen U) (a : CompactlySupportedContinuousMap X ℝ)
    (ha : ∀ x, 0 ≤ a x ∧ a x ≤ 1) (hs : tsupport a ⊆ U) :
    ENNReal.ofReal (∫ x, a x ∂μ) ≤ μ U := by
  rw [open_mass_integral μ hμ U hU]
  exact le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le hs le_rfl))

/-- The lower bound uses tensor tests and multiplication of arbitrary suprema.
The latter is valid in ENNReal also at zero and infinity. -/
lemma rectangle_lower_bound (μ : Measure X) (ν : Measure Y)
    (hμ : isRadon μ) (hν : isRadon ν)
    (U : Set X) (V : Set Y) (hU : IsOpen U) (hV : IsOpen V) :
    μ U * ν V ≤ RadonProduct.radonProduct μ ν (U ×ˢ V) := by
  have hρ := RadonProduct.radonProduct_isRadon X Y μ ν hμ hν
  rw [open_mass_integral μ hμ U hU, open_mass_integral ν hν V hV]
  simp only [ENNReal.iSup_mul, ENNReal.mul_iSup]
  refine iSup_le fun b => iSup_le fun hb => iSup_le fun hbs =>
    iSup_le fun a => iSup_le fun ha => iSup_le fun has => ?_
  rw [← ENNReal.ofReal_mul (integral_nonneg (fun x => (ha x).1)),
    ← tensor_integral μ ν hμ hν]
  exact test_integral_le_open _ hρ _ (hU.prod hV) (tensor a b)
    (tensor_bounds a b ha hb) ((tensor_support a b).trans (Set.prod_mono has hbs))

/-- Every admissible test is dominated by a tensor of compact cutoffs. -/
lemma rectangle_upper_bound (μ : Measure X) (ν : Measure Y)
    (hμ : isRadon μ) (hν : isRadon ν)
    (U : Set X) (V : Set Y) (hU : IsOpen U) (hV : IsOpen V) :
    RadonProduct.radonProduct μ ν (U ×ˢ V) ≤ μ U * ν V := by
  let ρ := RadonProduct.radonProduct μ ν
  have hρ : isRadon ρ := RadonProduct.radonProduct_isRadon X Y μ ν hμ hν
  let : MeasurableSpace (X × Y) := borel (X × Y)
  let : BorelSpace (X × Y) := ⟨rfl⟩
  let : IsFiniteMeasureOnCompacts ρ := (compactFinite_iff ρ).mp hρ.1
  rw [open_mass_integral ρ hρ (U ×ˢ V) (hU.prod hV)]
  refine iSup_le fun f => iSup_le fun hf => iSup_le fun hs => ?_
  have hK := f.hasCompactSupport.image continuous_fst
  have hL := f.hasCompactSupport.image continuous_snd
  have hKU : Prod.fst '' tsupport f ⊆ U := by
    rintro x ⟨p, hp, rfl⟩
    exact (hs hp).1
  have hLV : Prod.snd '' tsupport f ⊆ V := by
    rintro y ⟨p, hp, rfl⟩
    exact (hs hp).2
  obtain ⟨a, ha, haK, _, has⟩ := compact_cutoff X _ U hK hU hKU
  obtain ⟨b, hb, hbL, _, hbs⟩ := compact_cutoff Y _ V hL hV hLV
  have hdom : ∀ p, f p ≤ tensor a b p := by
    intro p
    by_cases hp : f p = 0
    · rw [hp]
      exact (tensor_bounds a b ha hb p).1
    · have hpt := subset_tsupport f hp
      change f p ≤ a p.1 * b p.2
      rw [haK _ ⟨p, hpt, rfl⟩, hbL _ ⟨p, hpt, rfl⟩, one_mul]
      exact (hf p).2
  calc
    ENNReal.ofReal (∫ p, f p ∂ρ) ≤ ENNReal.ofReal (∫ p, tensor a b p ∂ρ) :=
      ENNReal.ofReal_le_ofReal (integral_mono f.integrable (tensor a b).integrable hdom)
    _ = ENNReal.ofReal (∫ x, a x ∂μ) * ENNReal.ofReal (∫ y, b y ∂ν) := by
      rw [tensor_integral μ ν hμ hν,
        ENNReal.ofReal_mul (integral_nonneg (fun x => (ha x).1))]
    _ ≤ μ U * ν V := mul_le_mul'
      (test_integral_le_open μ hμ U hU a ha has)
      (test_integral_le_open ν hν V hV b hb hbs)

/-- Open-rectangle equality for arbitrary Radon factors on arbitrary LCH
Hausdorff spaces, including zero/infinite masses and empty rectangles. -/
theorem open_rectangle : Specs.D11.Ch18.RadonProductOpenRectangles.open_rectangle.{u,v} := by
  intro X _ _ _ Y _ _ _ μ ν hμ hν U V hU hV
  exact le_antisymm (rectangle_upper_bound μ ν hμ hν U V hU hV)
    (rectangle_lower_bound μ ν hμ hν U V hU hV)

end D11.Ch18.RadonProductOpenRectangles
