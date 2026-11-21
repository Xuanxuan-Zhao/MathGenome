import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonProductOpenRectangles
import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonFiniteInner
import MathGenome.Internal.RealAnalysis.D11.Ch18.FiniteDirectedLscIntegral
import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonProductSwap
import MathGenome.Internal.RealAnalysis.D11.Ch01.PiLambda
import MathGenome.Internal.RealAnalysis.D11.Ch05.MonotoneSeries
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.FiniteRadonBorelProduct
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub


/-! Finite Radon factors on arbitrary LCH Hausdorff spaces, on exactly
`borel (X × Y)`. For an open set, its section mass is the pointwise
supremum of the continuous section integrals of admissible Cc tests.
This family is directed under finite maxima. Finite Radon directed
monotone convergence interchanges that supremum with the integral;
the Cc product law and open-mass recovery identify it with product mass.
Coordinate interchange gives the other order. Finite complements and
disjoint countable unions then extend both formulas from opens to all
Borel sets. No equality of the two product sigma-algebras is used. -/

noncomputable section
namespace D11.Ch18.FiniteRadonBorelProduct
open Set MeasureTheory Filter
open scoped ENNReal Topology
universe u v

local instance {Z : Type*} [TopologicalSpace Z] : MeasurableSpace Z := borel Z
local instance {Z : Type*} [TopologicalSpace Z] : BorelSpace Z := ⟨rfl⟩

/-- A compact part of one open section persists in nearby sections. -/
lemma compact_section_tube {X : Type u} [TopologicalSpace X]
    {Y : Type v} [TopologicalSpace Y] {W : Set (X × Y)} (hW : IsOpen W)
    (x : X) {K : Set Y} (hK : IsCompact K) (hKW : K ⊆ {y | (x,y) ∈ W}) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ z ∈ U, K ⊆ {y | (z,y) ∈ W} := by
  have hsub : ({x} : Set X) ×ˢ K ⊆ W := by
    rintro ⟨z,y⟩ ⟨hz, hy⟩
    have hz' : z = x := mem_singleton_iff.mp hz
    subst z
    exact hKW hy
  obtain ⟨U,V,hU,_,hx,hKV,hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hK hW hsub
  exact ⟨U, hU, hx (mem_singleton x), fun z hz y hy => hUV ⟨hz, hKV hy⟩⟩

theorem open_sections_lowerSemicontinuous :
    Specs.D11.Ch18.FiniteRadonBorelProduct.open_sections_lowerSemicontinuous.{u,v} := by
  intro X _ Y _ _ _ ν hν W hW
  let : Measure.Regular ν := (isRadon_iff_regular ν).mp hν
  intro x a ha
  change a < ν {y | (x,y) ∈ W} at ha
  have hsec : IsOpen {y | (x,y) ∈ W} :=
    hW.preimage (continuous_const.prodMk continuous_id)
  rw [hsec.measure_eq_iSup_isCompact ν] at ha
  obtain ⟨K, hKW, hK, haK⟩ :
      ∃ K ⊆ {y | (x,y) ∈ W}, IsCompact K ∧ a < ν K := by
    simpa only [lt_iSup_iff, exists_prop] using ha
  obtain ⟨U,hU,hx,hUK⟩ := compact_section_tube hW x hK hKW
  exact Filter.mem_of_superset (hU.mem_nhds hx) (fun z hz =>
    haK.trans_le (measure_mono (hUK z hz)))

theorem borel_sections :
    Specs.D11.Ch18.FiniteRadonBorelProduct.borel_sections.{u,v} := by
  intro X _ Y _ E hE
  let : MeasurableSpace (X × Y) := borel (X × Y)
  let : BorelSpace (X × Y) := ⟨rfl⟩
  constructor
  · intro x
    exact hE.preimage (continuous_const.prodMk continuous_id).measurable
  · intro y
    exact hE.preimage (continuous_id.prodMk continuous_const).measurable

theorem finite_product_mass :
    Specs.D11.Ch18.FiniteRadonBorelProduct.finite_product_mass.{u,v} := by
  intro X _ _ _ Y _ _ _ μ ν hμ hν hμf hνf
  have he := RadonProductOpenRectangles.open_rectangle X Y μ ν hμ hν
    univ univ isOpen_univ isOpen_univ
  simp only [univ_prod_univ] at he
  exact ⟨he, he.trans_lt (ENNReal.mul_lt_top hμf hνf)⟩

theorem open_section_regularity :
    Specs.D11.Ch18.FiniteRadonBorelProduct.open_section_regularity.{u,v} := by
  intro X _ _ _ Y _ _ _ μ ν hμ hν W hW
  have hx := open_sections_lowerSemicontinuous X Y ν hν W hW
  have hy : LowerSemicontinuous (fun y => μ {x | (x,y) ∈ W}) :=
    open_sections_lowerSemicontinuous Y X μ hμ (Prod.swap ⁻¹' W)
      (hW.preimage continuous_swap)
  exact ⟨hx, hy, hx.measurable, hy.measurable⟩

/-- Measurability alone extends from opens without an integral identity. -/
lemma section_mass_measurable_of_open
    {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
    {Z : Type*} [TopologicalSpace Z]
    (k : X → Y → Z) (hk : ∀ x, Continuous (k x))
    (ν : Measure Y) (hνf : ν univ < ∞)
    (hopen : ∀ W : Set Z, IsOpen W → Measurable (fun x => ν {y | k x y ∈ W})) :
    ∀ E : Set Z, MeasurableSet[borel Z] E → Measurable (fun x => ν {y | k x y ∈ E}) := by
  apply MeasurableSpace.induction_on_inter
    (C := fun E _ => Measurable (fun x => ν {y | k x y ∈ E}))
    (s := {W | IsOpen W}) rfl (fun s hs t ht _ => hs.inter ht)
  · simp
  · exact hopen
  · intro E hE ih
    have hfun : (fun x => ν {y | k x y ∈ Eᶜ}) =
        (fun x => ν univ - ν {y | k x y ∈ E}) := by
      funext x
      exact measure_compl (hE.preimage (hk x).measurable)
        (ne_top_of_lt ((measure_mono (subset_univ _)).trans_lt hνf))
    rw [hfun]
    exact measurable_const.sub ih
  · intro E hd hm ih
    have hfun : (fun x => ν {y | k x y ∈ ⋃ n, E n}) =
        (fun x => ∑' n, ν {y | k x y ∈ E n}) := by
      funext x
      have heq : {y | k x y ∈ ⋃ n, E n} = ⋃ n, {y | k x y ∈ E n} := by
        ext y
        simp
      rw [heq]
      apply measure_iUnion
      · intro i j hij
        exact Set.disjoint_left.mpr (fun y hi hj => Set.disjoint_left.mp (hd hij) hi hj)
      · exact fun n => (hm n).preimage (hk x).measurable
    rw [hfun]
    exact Measurable.tsum ih

theorem borel_section_masses_measurable :
    Specs.D11.Ch18.FiniteRadonBorelProduct.borel_section_masses_measurable.{u,v} := by
  intro X _ _ _ Y _ _ _ μ ν hμ hν hμf hνf E hE
  let : MeasurableSpace (X × Y) := borel (X × Y)
  let : BorelSpace (X × Y) := ⟨rfl⟩
  constructor
  · exact section_mass_measurable_of_open (fun x y => (x,y))
      (fun _ => continuous_const.prodMk continuous_id) ν hνf
      (fun W hW => (open_section_regularity X Y μ ν hμ hν W hW).2.2.1) E hE
  · exact section_mass_measurable_of_open (fun y x => (x,y))
      (fun _ => continuous_id.prodMk continuous_const) μ hμf
      (fun W hW => (open_section_regularity X Y μ ν hμ hν W hW).2.2.2) E hE

/-- The finite Dynkin-class step. The open-set integral identity is the
analytic premise here; no product-measurability premise is imposed on E. -/
lemma borel_identity_of_open
    {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
    {Z : Type*} [TopologicalSpace Z]
    (k : X → Y → Z) (hk : ∀ x, Continuous (k x))
    (μ : Measure X) (ν : Measure Y) (ρ : @Measure Z (borel Z))
    (hμf : μ univ < ∞) (hνf : ν univ < ∞)
    (hmass : ρ univ = μ univ * ν univ)
    (hopen : ∀ W : Set Z, IsOpen W →
      Measurable (fun x => ν {y | k x y ∈ W}) ∧
      ρ W = ∫⁻ x, ν {y | k x y ∈ W} ∂μ) :
    ∀ E : Set Z, MeasurableSet[borel Z] E →
      Measurable (fun x => ν {y | k x y ∈ E}) ∧
      ρ E = ∫⁻ x, ν {y | k x y ∈ E} ∂μ := by
  have hρf : ρ univ < ∞ := hmass.trans_lt (ENNReal.mul_lt_top hμf hνf)
  have hbound (E : Set Z) :
      (∫⁻ x, ν {y | k x y ∈ E} ∂μ) < ∞ := by
    calc
      _ ≤ ∫⁻ _ : X, ν univ ∂μ := lintegral_mono fun _ => measure_mono (subset_univ _)
      _ = ν univ * μ univ := by simp
      _ < ∞ := ENNReal.mul_lt_top hνf hμf
  apply MeasurableSpace.induction_on_inter
    (C := fun E _ => Measurable (fun x => ν {y | k x y ∈ E}) ∧
      ρ E = ∫⁻ x, ν {y | k x y ∈ E} ∂μ)
    (s := {W | IsOpen W}) rfl
    (fun s hs t ht _ => hs.inter ht)
  · simp
  · exact hopen
  · intro E hE ih
    have hfun : (fun x => ν {y | k x y ∈ Eᶜ}) =
        (fun x => ν univ - ν {y | k x y ∈ E}) := by
      funext x
      exact measure_compl (hE.preimage (hk x).measurable)
        (ne_top_of_lt ((measure_mono (subset_univ _)).trans_lt hνf))
    rw [hfun]
    refine ⟨measurable_const.sub ih.1, ?_⟩
    rw [measure_compl hE (ne_top_of_lt ((measure_mono (subset_univ _)).trans_lt hρf)),
      lintegral_sub ih.1 (hbound E).ne
        (ae_of_all _ (fun _ => measure_mono (subset_univ _))),
      lintegral_const, ← ih.2, hmass, mul_comm (ν univ)]
  · intro E hd hm ih
    have hfun : (fun x => ν {y | k x y ∈ ⋃ n, E n}) =
        (fun x => ∑' n, ν {y | k x y ∈ E n}) := by
      funext x
      have heq : {y | k x y ∈ ⋃ n, E n} = ⋃ n, {y | k x y ∈ E n} := by
        ext y
        simp
      rw [heq]
      apply measure_iUnion
      · intro i j hij
        exact Set.disjoint_left.mpr (fun y hi hj =>
          Set.disjoint_left.mp (hd hij) hi hj)
      · exact fun n => (hm n).preimage (hk x).measurable
    rw [hfun]
    refine ⟨Measurable.tsum (fun n => (ih n).1), ?_⟩
    rw [measure_iUnion hd hm, lintegral_tsum (fun n => (ih n).1.aemeasurable)]
    exact tsum_congr (fun n => (ih n).2)

/-- Both Borel identities follow from the open identities by finite
complements and disjoint countable unions. -/
theorem borel_integral_identity_of_open
    (hopen : Specs.D11.Ch18.FiniteRadonBorelProduct.open_integral_identity.{u,v}) :
    Specs.D11.Ch18.FiniteRadonBorelProduct.borel_integral_identity.{u,v} := by
  intro X _ _ _ Y _ _ _ μ ν hμ hν hμf hνf E hE
  let : MeasurableSpace (X × Y) := borel (X × Y)
  let : BorelSpace (X × Y) := ⟨rfl⟩
  have hmass := (finite_product_mass X Y μ ν hμ hν hμf hνf).1
  have hleft := borel_identity_of_open (fun x y => (x,y))
    (fun _ => continuous_const.prodMk continuous_id) μ ν
    (RadonProduct.radonProduct μ ν) hμf hνf hmass
    (fun W hW => ⟨(hopen X Y μ ν hμ hν hμf hνf W hW).2.2.1,
      (hopen X Y μ ν hμ hν hμf hνf W hW).2.2.2.2.1⟩) E hE
  have hright := borel_identity_of_open (fun y x => (x,y))
    (fun _ => continuous_id.prodMk continuous_const) ν μ
    (RadonProduct.radonProduct μ ν) hνf hμf (hmass.trans (mul_comm _ _))
    (fun W hW => ⟨(hopen X Y μ ν hμ hν hμf hνf W hW).2.2.2.1,
      (hopen X Y μ ν hμ hν hμf hνf W hW).2.2.2.2.2⟩) E hE
  exact ⟨hleft.1, hright.1, hleft.2, hright.2⟩

/-- The easy half of the open-set identity, from the defining Cc law.
It holds even for factors of infinite total mass. -/
lemma open_mass_le_section_integral
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y) (hμ : isRadon μ) (hν : isRadon ν)
    (W : Set (X × Y)) (hW : IsOpen W) :
    RadonProduct.radonProduct μ ν W ≤ ∫⁻ x, ν {y | (x,y) ∈ W} ∂μ := by
  let : MeasurableSpace (X × Y) := borel (X × Y)
  let : BorelSpace (X × Y) := ⟨rfl⟩
  let ρ := RadonProduct.radonProduct μ ν
  have hρ : isRadon ρ := RadonProduct.radonProduct_isRadon X Y μ ν hμ hν
  change ρ W ≤ _
  rw [RadonProductOpenRectangles.open_mass_integral ρ hρ W hW]
  refine iSup_le fun f => iSup_le fun hf => iSup_le fun hs => ?_
  obtain ⟨g, _, eg, _, _, _, _, _, hg, _⟩ :=
    CcIteratedIntegrals.section_integrals_cc X Y ℝ μ ν hμ hν f
  have hg' : Integrable (fun x => ∫ y, f (x,y) ∂ν) μ := by
    simpa only [show (g : X → ℝ) = (fun x => ∫ y, f (x,y) ∂ν) from funext eg] using hg
  rw [(RadonProduct.radonProduct_law μ ν hμ hν).2 f |>.2,
    ofReal_integral_eq_lintegral_ofReal hg'
      (ae_of_all _ (fun x => integral_nonneg (fun y => (hf (x,y)).1)))]
  apply lintegral_mono
  intro x
  apply integral_le_measure
  · exact fun y _ => (hf (x,y)).2
  · intro y hy
    have hzero : f (x,y) = 0 := by
      by_contra hn
      exact hy (hs (subset_tsupport f hn))
    exact hzero.le

/-- Compact-mass recovery for the actual integral. -/
lemma compact_mass_integral
    {Z : Type*} [TopologicalSpace Z] [T2Space Z] [LocallyCompactSpace Z]
    (ρ : Measure Z) (hρ : isRadon ρ) (K : Set Z) (hK : IsCompact K) :
    ρ K = ⨅ f : CompactlySupportedContinuousMap Z ℝ,
      ⨅ (_ : ∀ z, 0 ≤ f z), ⨅ (_ : ∀ z ∈ K, 1 ≤ f z),
        ENNReal.ofReal (∫ z, f z ∂ρ) := by
  obtain ⟨I, hI, hrep⟩ := Ch19.PositiveRieszMarkov.radon_induces_real_functional ρ hρ
  rw [Ch19.RecoverOpenCompactMass.real_compact_mass I hI ρ hrep K hK]
  simp only [(hrep.2 _).2]
  rfl

/-- Compact sets satisfy the opposite inequality, by Cc majorants. -/
lemma compact_section_integral_le_mass
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y) (hμ : isRadon μ) (hν : isRadon ν)
    (K : Set (X × Y)) (hK : IsCompact K) :
    (∫⁻ x, ν {y | (x,y) ∈ K} ∂μ) ≤ RadonProduct.radonProduct μ ν K := by
  let : MeasurableSpace (X × Y) := borel (X × Y)
  let : BorelSpace (X × Y) := ⟨rfl⟩
  let ρ := RadonProduct.radonProduct μ ν
  have hρ : isRadon ρ := RadonProduct.radonProduct_isRadon X Y μ ν hμ hν
  change _ ≤ ρ K
  rw [compact_mass_integral ρ hρ K hK]
  refine le_iInf fun f => le_iInf fun hf => le_iInf fun hfK => ?_
  obtain ⟨g, _, eg, _, _, _, _, _, hg, _⟩ :=
    CcIteratedIntegrals.section_integrals_cc X Y ℝ μ ν hμ hν f
  have hg' : Integrable (fun x => ∫ y, f (x,y) ∂ν) μ := by
    simpa only [show (g : X → ℝ) = (fun x => ∫ y, f (x,y) ∂ν) from funext eg] using hg
  rw [(RadonProduct.radonProduct_law μ ν hμ hν).2 f |>.2,
    ofReal_integral_eq_lintegral_ofReal hg'
      (ae_of_all _ (fun x => integral_nonneg (fun y => hf (x,y))))]
  apply lintegral_mono
  intro x
  exact ((CcIteratedIntegrals.sections_integrable X Y ℝ μ ν hμ hν f).1 x).2.measure_le_integral
    (ae_of_all _ (fun y => hf (x,y))) (fun y hy => hfK (x,y) hy)

/-- An increasing compact exhaustion modulo a null set, for a finite Radon
measure. The ambient space itself need not be sigma-compact. -/
lemma exists_compact_ae_exhaustion
    {Z : Type*} [TopologicalSpace Z] [T2Space Z] [LocallyCompactSpace Z]
    (μ : Measure Z) (hμ : isRadon μ) (hμf : μ univ < ∞) :
    ∃ A : ℕ → Set Z, (∀ n, IsCompact (A n)) ∧ Monotone A ∧
      μ (⋃ n, A n)ᶜ = 0 := by
  classical
  obtain ⟨ε, _, hε, he⟩ := exists_seq_strictAnti_tendsto' (α := ℝ≥0∞) zero_lt_one
  have hex (n : ℕ) : ∃ K : Set Z, K ⊆ univ ∧ IsCompact K ∧ μ (univ \ K) < ε n :=
    RadonFiniteInner.exists_compact_sdiff_lt μ hμ univ MeasurableSet.univ hμf (ε n) (hε n).1
  choose K _ hK hsmall using hex
  let A : ℕ → Set Z := fun n => ⋃ i ∈ Finset.range (n+1), K i
  have hKA (n : ℕ) : K n ⊆ A n := by
    intro z hz
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self n), hz⟩⟩
  refine ⟨A, fun n => ?_, ?_, ?_⟩
  · exact (Finset.range (n+1)).finite_toSet.isCompact_biUnion (fun i _ => hK i)
  · intro i j hij
    exact iUnion₂_mono' (fun k hk => ⟨k, Finset.range_mono (Nat.add_le_add_right hij 1) hk,
      Subset.rfl⟩)
  · apply le_antisymm _ bot_le
    apply le_of_tendsto_of_tendsto' tendsto_const_nhds he
    intro n
    calc
      μ (⋃ n, A n)ᶜ ≤ μ (univ \ K n) := measure_mono (by
        intro z hz
        exact ⟨mem_univ z, fun hzK => hz (mem_iUnion.mpr ⟨n, hKA n hzK⟩)⟩)
      _ ≤ ε n := (hsmall n).le

/-- Nonnegative compactly supported tests with values at most one and
support in the specified open set. -/
def OpenTest {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
    (W : Set (X × Y)) :=
  {f : CompactlySupportedContinuousMap (X × Y) ℝ //
    (∀ p, 0 ≤ f p ∧ f p ≤ 1) ∧ tsupport f ⊆ W}

instance {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
    (W : Set (X × Y)) : Nonempty (OpenTest W) :=
  ⟨⟨0, by simp⟩⟩

lemma openTest_sup {X : Type u} [TopologicalSpace X]
    {Y : Type v} [TopologicalSpace Y] {W : Set (X × Y)} (f g : OpenTest W) :
    ∃ h : OpenTest W, f.val ≤ h.val ∧ g.val ≤ h.val := by
  refine ⟨⟨f.val ⊔ g.val, ?_, ?_⟩, le_sup_left, le_sup_right⟩
  · intro p
    exact ⟨(f.property.1 p).1.trans (le_max_left _ _),
      max_le (f.property.1 p).2 (g.property.1 p).2⟩
  · apply (closure_minimal ?_ ((isClosed_tsupport _).union (isClosed_tsupport _))).trans
      (union_subset f.property.2 g.property.2)
    intro p hp
    by_cases hf : f.val p = 0
    · have hg : g.val p ≠ 0 := by
        intro hg
        exact hp (by simp [hf, hg])
      exact Or.inr (subset_tsupport _ hg)
    · exact Or.inl (subset_tsupport _ hf)

/-- Pointwise open-section masses are suprema of the continuous section
integrals of admissible Cc tests. No countability of X or Y is used. -/
lemma open_section_mass_eq_iSup_tests
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (ν : Measure Y) (hν : isRadon ν) (W : Set (X × Y)) (hW : IsOpen W) (x : X) :
    ν {y | (x,y) ∈ W} =
      ⨆ f : OpenTest W, ENNReal.ofReal (∫ y, f.val (x,y) ∂ν) := by
  apply le_antisymm
  · have hsec : IsOpen {y | (x,y) ∈ W} :=
      hW.preimage (continuous_const.prodMk continuous_id)
    rw [RadonProductOpenRectangles.open_mass_integral ν hν _ hsec]
    refine iSup_le fun b => iSup_le fun hb => iSup_le fun hbs => ?_
    obtain ⟨U,hU,hx,hUK⟩ := compact_section_tube hW x b.hasCompactSupport hbs
    obtain ⟨a,ha,hax,_,has⟩ := compact_cutoff X {x} U isCompact_singleton hU
      (singleton_subset_iff.mpr hx)
    let t := RadonProductOpenRectangles.tensor a b
    have ht : tsupport t ⊆ W := by
      intro p hp
      obtain ⟨hp1,hp2⟩ := RadonProductOpenRectangles.tensor_support a b hp
      exact hUK p.1 (has hp1) hp2
    let f : OpenTest W := ⟨t, RadonProductOpenRectangles.tensor_bounds a b ha hb, ht⟩
    apply le_iSup_of_le f
    change ENNReal.ofReal (∫ y, b y ∂ν) ≤ ENNReal.ofReal (∫ y, a x * b y ∂ν)
    rw [hax x (mem_singleton x)]
    simp
  · refine iSup_le fun f => ?_
    apply integral_le_measure
    · exact fun y _ => (f.property.1 (x,y)).2
    · intro y hy
      have hz : f.val (x,y) = 0 := by
        by_contra hn
        exact hy (f.property.2 (subset_tsupport _ hn))
      exact hz.le

/-- The test-section family is directed under pointwise order. -/
lemma directed_test_sections
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (ν : Measure Y) (hν : isRadon ν) (W : Set (X × Y)) :
    Directed (· ≤ ·) (fun f : OpenTest W =>
      fun x => ENNReal.ofReal (∫ y, f.val (x,y) ∂ν)) := by
  intro f g
  obtain ⟨h,hfh,hgh⟩ := openTest_sup f g
  have hint (f : OpenTest W) (x : X) : Integrable (fun y => f.val (x,y)) ν := by
    let : IsFiniteMeasureOnCompacts ν := (compactFinite_iff ν).mp hν.1
    exact (f.val.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (CcIteratedIntegrals.section_hasCompactSupport f.val x)
  refine ⟨h, fun x => ?_, fun x => ?_⟩
  · exact ENNReal.ofReal_le_ofReal (integral_mono (hint f x) (hint h x) (fun y => hfh (x,y)))
  · exact ENNReal.ofReal_le_ofReal (integral_mono (hint g x) (hint h x) (fun y => hgh (x,y)))

lemma continuous_test_section
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (ν : Measure Y) (hν : isRadon ν) {W : Set (X × Y)} (f : OpenTest W) :
    Continuous (fun x => ENNReal.ofReal (∫ y, f.val (x,y) ∂ν)) := by
  let : IsFiniteMeasureOnCompacts ν := (compactFinite_iff ν).mp hν.1
  exact ENNReal.continuous_ofReal.comp (CcIteratedIntegrals.continuous_section_integral ν f.val)

lemma test_section_le_total
    {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
    (ν : Measure Y) {W : Set (X × Y)} (f : OpenTest W) (x : X) :
    ENNReal.ofReal (∫ y, f.val (x,y) ∂ν) ≤ ν univ := by
  exact integral_le_measure (fun y _ => (f.property.1 (x,y)).2) (by simp)

lemma test_section_lintegral
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y) (hμ : isRadon μ) (hν : isRadon ν)
    {W : Set (X × Y)} (f : OpenTest W) :
    (∫⁻ x, ENNReal.ofReal (∫ y, f.val (x,y) ∂ν) ∂μ) =
      ENNReal.ofReal (∫ p, f.val p ∂(RadonProduct.radonProduct μ ν)) := by
  obtain ⟨g, _, eg, _, _, _, _, _, hg, _⟩ :=
    CcIteratedIntegrals.section_integrals_cc X Y ℝ μ ν hμ hν f.val
  have hg' : Integrable (fun x => ∫ y, f.val (x,y) ∂ν) μ := by
    simpa only [show (g : X → ℝ) = (fun x => ∫ y, f.val (x,y) ∂ν) from funext eg] using hg
  rw [(RadonProduct.radonProduct_law μ ν hμ hν).2 f.val |>.2]
  exact (ofReal_integral_eq_lintegral_ofReal hg'
    (ae_of_all _ (fun x => integral_nonneg (fun y => (f.property.1 (x,y)).1)))).symm

/-- Open-mass recovery and directed integral interchange identify the
left section integral. The next lemma supplies the interchange premise. -/
lemma open_identity_left_of_directed_integral
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y) (hμ : isRadon μ) (hν : isRadon ν)
    (H : ∀ {ι : Type (max u v)} [Nonempty ι] (g : ι → X → ℝ≥0∞),
      (∀ i, LowerSemicontinuous (g i)) → Directed (· ≤ ·) g →
      (∀ i x, g i x ≤ ν univ) →
      (∫⁻ x, ⨆ i, g i x ∂μ) = ⨆ i, ∫⁻ x, g i x ∂μ)
    (W : Set (X × Y)) (hW : IsOpen W) :
    RadonProduct.radonProduct μ ν W = ∫⁻ x, ν {y | (x,y) ∈ W} ∂μ := by
  let : MeasurableSpace (X × Y) := borel (X × Y)
  let : BorelSpace (X × Y) := ⟨rfl⟩
  let ρ := RadonProduct.radonProduct μ ν
  have hρ : isRadon ρ := RadonProduct.radonProduct_isRadon X Y μ ν hμ hν
  let g : OpenTest W → X → ℝ≥0∞ := fun f x => ENNReal.ofReal (∫ y, f.val (x,y) ∂ν)
  have heq (x : X) : ν {y | (x,y) ∈ W} = ⨆ f, g f x :=
    open_section_mass_eq_iSup_tests ν hν W hW x
  rw [show (fun x => ν {y | (x,y) ∈ W}) = (fun x => ⨆ f, g f x) from funext heq]
  rw [H g (fun f => (continuous_test_section ν hν f).lowerSemicontinuous)
    (directed_test_sections ν hν W) (fun f x => test_section_le_total ν f x)]
  simp_rw [show ∀ f : OpenTest W, (∫⁻ x, g f x ∂μ) = ENNReal.ofReal (∫ p, f.val p ∂ρ)
    from fun f => test_section_lintegral μ ν hμ hν f]
  change ρ W = _
  rw [RadonProductOpenRectangles.open_mass_integral ρ hρ W hW]
  apply le_antisymm
  · refine iSup_le fun f => iSup_le fun hf => iSup_le fun hs => ?_
    exact le_iSup (fun f : OpenTest W => ENNReal.ofReal (∫ p, f.val p ∂ρ)) ⟨f,hf,hs⟩
  · refine iSup_le fun f => ?_
    exact le_iSup_of_le f.val (le_iSup_of_le f.property.1 (le_iSup_of_le f.property.2 le_rfl))

/-- The left open-set identity uses a directed family of all admissible
Cc tests, with no countability assumption on that family or on the spaces. -/
lemma open_integral_identity_left
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y) (hμ : isRadon μ) (hν : isRadon ν)
    (hμf : μ univ < ∞) (hνf : ν univ < ∞)
    (W : Set (X × Y)) (hW : IsOpen W) :
    RadonProduct.radonProduct μ ν W = ∫⁻ x, ν {y | (x,y) ∈ W} ∂μ := by
  apply open_identity_left_of_directed_integral μ ν hμ hν ?_ W hW
  intro ι _ g hg hd hb
  exact FiniteDirectedLscIntegral.lintegral_iSup_directed μ hμ hμf g hg hd
    (ν univ) hνf hb

/-- The complete open-set stage, on the product topology's Borel domain. -/
theorem open_integral_identity :
    Specs.D11.Ch18.FiniteRadonBorelProduct.open_integral_identity.{u,v} := by
  intro X _ _ _ Y _ _ _ μ ν hμ hν hμf hνf W hW
  obtain ⟨hx, hy, hmx, hmy⟩ := open_section_regularity X Y μ ν hμ hν W hW
  refine ⟨hx, hy, hmx, hmy,
    open_integral_identity_left μ ν hμ hν hμf hνf W hW, ?_⟩
  calc
    RadonProduct.radonProduct μ ν W =
        RadonProduct.radonProduct ν μ (Prod.swap ⁻¹' W) :=
      RadonProductSwap.open_swap X Y μ ν hμ hν W hW
    _ = ∫⁻ y, μ {x | (x,y) ∈ W} ∂ν :=
      open_integral_identity_left ν μ hν hμ hνf hμf (Prod.swap ⁻¹' W)
        (hW.preimage continuous_swap)

/-- Full finite-factor section formulas for every topological-product
Borel set, without identifying the two product sigma-algebras. -/
theorem borel_integral_identity :
    Specs.D11.Ch18.FiniteRadonBorelProduct.borel_integral_identity.{u,v} :=
  borel_integral_identity_of_open open_integral_identity

end D11.Ch18.FiniteRadonBorelProduct
