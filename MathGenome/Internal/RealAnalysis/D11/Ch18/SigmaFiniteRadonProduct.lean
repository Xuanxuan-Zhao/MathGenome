import MathGenome.Internal.RealAnalysis.D11.Ch18.FiniteRadonBorelProduct
import MathGenome.Internal.RealAnalysis.D11.Ch18.SigmaFiniteRadonOrdinaryProduct
import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonSigmaFiniteInner
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.SigmaFiniteRadonProduct

noncomputable section
namespace D11.Ch18.SigmaFiniteRadonProduct
open Set MeasureTheory
open scoped ENNReal
universe u v
local instance {Z : Type*} [TopologicalSpace Z] : MeasurableSpace Z := borel Z
local instance {Z : Type*} [TopologicalSpace Z] : BorelSpace Z := ⟨rfl⟩

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]

theorem finite_borel_restriction :
    Specs.D11.Ch18.SigmaFiniteRadonProduct.finite_borel_restriction.{u} := by
  intro X _ _ _ μ hμ A _hA hfin
  let : Measure.Regular μ := (isRadon_iff_regular μ).mp hμ
  exact ⟨(isRadon_iff_regular (μ.restrict A)).mpr
    (Measure.Regular.restrict_of_measure_ne_top hfin.ne), by simpa using hfin⟩

theorem increasing_finite_open_exhaustion :
    Specs.D11.Ch18.SigmaFiniteRadonProduct.increasing_finite_open_exhaustion.{u} := by
  intro X _ _ _ μ hμ hsf
  obtain ⟨U,hU,hcov⟩ := SigmaFiniteRadonOrdinaryProduct.finite_open_cover X μ hμ hsf
  refine ⟨accumulate U, fun n => ⟨?_, ?_⟩, monotone_accumulate, ?_⟩
  · exact isOpen_iUnion fun i => isOpen_iUnion fun _ => (hU i).1
  · exact measure_biUnion_lt_top (finite_Iic n) (fun i _ => (hU i).2)
  · rwa [iUnion_accumulate]

theorem finite_rectangle_restriction :
    Specs.D11.Ch18.SigmaFiniteRadonProduct.finite_rectangle_restriction.{u,v} := by
  intro X _ _ _ Y _ _ _ μ ν hμ hν hsfμ hsfν A B hA hB hμA hνB
  let : SigmaFinite μ := hsfμ
  let : SigmaFinite ν := hsfν
  let : MeasurableSpace (X × Y) := borel (X × Y)
  let : BorelSpace (X × Y) := ⟨rfl⟩
  let ρ := RadonProduct.radonProduct μ ν
  have hρ : isRadon ρ := RadonProduct.radonProduct_isRadon X Y μ ν hμ hν
  have hAB : MeasurableSet[(borel X).prod (borel Y)] (A ×ˢ B) := hA.prod hB
  have hAB' : MeasurableSet[borel (X × Y)] (A ×ˢ B) := prod_le_borel_prod _ hAB
  have ht : ρ.trim prod_le_borel_prod = μ.prod ν :=
    SigmaFiniteRadonOrdinaryProduct.ordinary_product_restriction X Y μ ν hμ hν hsfμ hsfν
  have hρAB : ρ (A ×ˢ B) < ∞ := by
    rw [← trim_measurableSet_eq prod_le_borel_prod hAB, ht, Measure.prod_prod]
    exact ENNReal.mul_lt_top hμA hνB
  have hr := (finite_borel_restriction (X × Y) ρ hρ (A ×ˢ B) hAB' hρAB).1
  have hrμ := (finite_borel_restriction X μ hμ A hA hμA).1
  have hrν := (finite_borel_restriction Y ν hν B hB hνB).1
  apply RadonProduct.unique X Y (μ.restrict A) (ν.restrict B) hrμ hrν (ρ.restrict (A ×ˢ B)) hr
  intro f
  have hm := (RadonProduct.measurable_finite_rectangle X Y ℝ μ ν hμ hν f).1
  have hsm : StronglyMeasurable[(borel X).prod (borel Y)] f := hm.stronglyMeasurable
  have hip := (SigmaFiniteRadonOrdinaryProduct.cc_fubini X Y ℝ μ ν hμ hν hsfμ hsfν f).2.2.1
  calc
    (∫ p, f p ∂(ρ.restrict (A ×ˢ B))) = ∫ p in A ×ˢ B, f p ∂(μ.prod ν) := by
      rw [setIntegral_trim prod_le_borel_prod hsm hAB, ht]
    _ = ∫ p, f p ∂((μ.restrict A).prod (ν.restrict B)) := by
      rw [Measure.prod_restrict]
    _ = ∫ x, (∫ y, f (x,y) ∂(ν.restrict B)) ∂(μ.restrict A) := by
      apply integral_prod f
      rw [Measure.prod_restrict]
      exact hip.restrict

/-- Continuity from below along a covering, evaluated on a fixed measurable set. -/
lemma measure_eq_iSup_restrict {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (A : ℕ → Set Z) (hA : Monotone A) (hcov : ⋃ n, A n = univ)
    (E : Set Z) (hE : MeasurableSet E) :
    μ E = ⨆ n, (μ.restrict (A n)) E := by
  simp_rw [Measure.restrict_apply hE]
  calc
    μ E = μ (⋃ n, E ∩ A n) := by rw [← inter_iUnion, hcov, inter_univ]
    _ = _ := (show Monotone (fun n => E ∩ A n) from fun i j hij =>
      inter_subset_inter_right E (hA hij)).measure_iUnion

omit [T2Space X] [LocallyCompactSpace X] [T2Space Y] [LocallyCompactSpace Y] in
/-- The finite rectangle restrictions exhaust every Borel mass. -/
lemma measure_eq_iSup_rectangles
    (ρ : @Measure (X × Y) (borel (X × Y)))
    (A : ℕ → Set X) (B : ℕ → Set Y)
    (hA : Monotone A) (hB : Monotone B)
    (hcA : ⋃ n, A n = univ) (hcB : ⋃ n, B n = univ)
    (E : Set (X × Y)) (hE : MeasurableSet[borel (X × Y)] E) :
    ρ E = ⨆ n, ⨆ m, (ρ.restrict (A n ×ˢ B m)) E := by
  have hcov : (⋃ p : ℕ × ℕ, A p.1 ×ˢ B p.2) = univ := by
    rw [iUnion_prod, hcA, hcB, univ_prod_univ]
  have hmono : Monotone (fun p : ℕ × ℕ => E ∩ (A p.1 ×ˢ B p.2)) :=
    fun p q hpq => inter_subset_inter_right E (prod_mono (hA hpq.1) (hB hpq.2))
  calc
    ρ E = ρ (⋃ p : ℕ × ℕ, E ∩ (A p.1 ×ˢ B p.2)) := by
      rw [← inter_iUnion, hcov, inter_univ]
    _ = ⨆ p : ℕ × ℕ, ρ (E ∩ (A p.1 ×ˢ B p.2)) := hmono.measure_iUnion
    _ = _ := by rw [iSup_prod]; simp_rw [Measure.restrict_apply hE]

theorem borel_integral_identity :
    Specs.D11.Ch18.SigmaFiniteRadonProduct.borel_integral_identity.{u,v} := by
  intro X _ _ _ Y _ _ _ μ ν hμ hν hsfμ hsfν E hE
  let : MeasurableSpace (X × Y) := borel (X × Y)
  let : BorelSpace (X × Y) := ⟨rfl⟩
  obtain ⟨A,hA,hmA,hcA⟩ := increasing_finite_open_exhaustion X μ hμ hsfμ
  obtain ⟨B,hB,hmB,hcB⟩ := increasing_finite_open_exhaustion Y ν hν hsfν
  have hrA (n : ℕ) := finite_borel_restriction X μ hμ (A n) (hA n).1.measurableSet (hA n).2
  have hrB (m : ℕ) := finite_borel_restriction Y ν hν (B m) (hB m).1.measurableSet (hB m).2
  have hfin (n m : ℕ) := FiniteRadonBorelProduct.borel_integral_identity X Y
    (μ.restrict (A n)) (ν.restrict (B m)) (hrA n).1 (hrB m).1
    (hrA n).2 (hrB m).2 E hE
  have hsec := FiniteRadonBorelProduct.borel_sections X Y E hE
  have hx (x : X) : ν {y | (x,y) ∈ E} = ⨆ m, (ν.restrict (B m)) {y | (x,y) ∈ E} :=
    measure_eq_iSup_restrict ν B hmB hcB _ (hsec.1 x)
  have hy (y : Y) : μ {x | (x,y) ∈ E} = ⨆ n, (μ.restrict (A n)) {x | (x,y) ∈ E} :=
    measure_eq_iSup_restrict μ A hmA hcA _ (hsec.2 y)
  have hmx : Measurable (fun x => ν {y | (x,y) ∈ E}) := by
    simp_rw [hx]
    exact Measurable.iSup (fun m => (hfin 0 m).1)
  have hmy : Measurable (fun y => μ {x | (x,y) ∈ E}) := by
    simp_rw [hy]
    exact Measurable.iSup (fun n => (hfin n 0).2.1)
  have hrestr (n m : ℕ) := finite_rectangle_restriction X Y μ ν hμ hν hsfμ hsfν
    (A n) (B m) (hA n).1.measurableSet (hB m).1.measurableSet (hA n).2 (hB m).2
  have hmass := measure_eq_iSup_rectangles (RadonProduct.radonProduct μ ν)
    A B hmA hmB hcA hcB E hE
  have hleft (n m : ℕ) : (RadonProduct.radonProduct μ ν).restrict (A n ×ˢ B m) E =
      ∫⁻ x, (ν.restrict (B m)) {y | (x,y) ∈ E} ∂(μ.restrict (A n)) := by
    exact (congrArg (fun ρ : @Measure (X × Y) (borel (X × Y)) => ρ E)
      (hrestr n m)).trans (hfin n m).2.2.1
  have hright (n m : ℕ) : (RadonProduct.radonProduct μ ν).restrict (A n ×ˢ B m) E =
      ∫⁻ y, (μ.restrict (A n)) {x | (x,y) ∈ E} ∂(ν.restrict (B m)) := by
    exact (congrArg (fun ρ : @Measure (X × Y) (borel (X × Y)) => ρ E)
      (hrestr n m)).trans (hfin n m).2.2.2
  refine ⟨hmx, hmy, ?_, ?_⟩
  · apply hmass.trans
    simp_rw [hleft]
    rw [iSup_comm]
    have hilim (m : ℕ) :
        (⨆ n, ∫⁻ x, (ν.restrict (B m)) {y | (x,y) ∈ E} ∂(μ.restrict (A n))) =
          ∫⁻ x, (ν.restrict (B m)) {y | (x,y) ∈ E} ∂μ := by
      rw [← setLIntegral_iUnion_of_directed _ hmA.directed_le, hcA, Measure.restrict_univ]
    simp_rw [hilim]
    rw [← lintegral_iSup (fun m => (hfin 0 m).1)]
    · simp_rw [← hx]
    · intro i j hij x
      exact Measure.le_iff'.mp (Measure.restrict_mono (hmB hij) le_rfl) _
  · apply hmass.trans
    simp_rw [hright]
    have hilim (n : ℕ) :
        (⨆ m, ∫⁻ y, (μ.restrict (A n)) {x | (x,y) ∈ E} ∂(ν.restrict (B m))) =
          ∫⁻ y, (μ.restrict (A n)) {x | (x,y) ∈ E} ∂ν := by
      rw [← setLIntegral_iUnion_of_directed _ hmB.directed_le, hcB, Measure.restrict_univ]
    simp_rw [hilim]
    rw [← lintegral_iSup (fun n => (hfin n 0).2.1)]
    · simp_rw [← hy]
    · intro i j hij y
      exact Measure.le_iff'.mp (Measure.restrict_mono (hmA hij) le_rfl) _

theorem ordinary_product_restriction :
    Specs.D11.Ch18.SigmaFiniteRadonProduct.ordinary_product_restriction.{u,v} :=
  SigmaFiniteRadonOrdinaryProduct.ordinary_product_restriction

theorem ordinary_product_apply :
    Specs.D11.Ch18.SigmaFiniteRadonProduct.ordinary_product_apply.{u,v} :=
  SigmaFiniteRadonOrdinaryProduct.ordinary_product_apply

end D11.Ch18.SigmaFiniteRadonProduct
