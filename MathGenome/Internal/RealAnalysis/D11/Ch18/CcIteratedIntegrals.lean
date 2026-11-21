import MathGenome.Internal.RealAnalysis.D11.Ch18.CcTensorApproximation
import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonPredicates
import MathGenome.Internal.RealAnalysis.D11.Ch08.Fubini
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.CcIteratedIntegrals

/-! Compact-support Fubini without global sigma-finiteness.
The compact support projections control both section supports and finite
measure restrictions. Continuity of parameter integrals uses uniform compact
support, with no first-countability assumption on the parameter space.
The native compact-support Fubini theorem restricts to these finite factor
measures internally. No product Borel measure is constructed in this module. -/

noncomputable section
namespace D11.Ch18.CcIteratedIntegrals

open Set MeasureTheory
open scoped ENNReal
universe u v

local instance {Z : Type*} [TopologicalSpace Z] : MeasurableSpace Z := borel Z
local instance {Z : Type*} [TopologicalSpace Z] : BorelSpace Z := ⟨rfl⟩

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  {Y : Type v} [TopologicalSpace Y] [T2Space Y]
  {𝕜 : Type} [RCLike 𝕜]

omit [T2Space X] [T2Space Y] in
/-- A section vanishes outside the second compact support projection. -/
theorem section_eq_zero (f : D11.Ch19.Cc (X × Y) 𝕜) (x : X) (y : Y)
    (hy : y ∉ Prod.snd '' tsupport f) : f (x,y) = 0 := by
  by_contra h
  exact hy ⟨(x,y), subset_tsupport f h, rfl⟩

omit [T2Space X] in
/-- Sections have compact support in the original second factor. -/
theorem section_hasCompactSupport (f : D11.Ch19.Cc (X × Y) 𝕜) (x : X) :
    HasCompactSupport (fun y => f (x,y)) := by
  apply (f.hasCompactSupport.image continuous_snd).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal
  · intro y hy
    exact ⟨(x,y), subset_tsupport f hy, rfl⟩
  · exact (f.hasCompactSupport.image continuous_snd).isClosed

omit [T2Space X] [T2Space Y] in
/-- Uniform compact support makes integration continuous in the parameter,
even when neither factor is first or second countable. -/
theorem continuous_section_integral (ν : Measure Y) [IsFiniteMeasureOnCompacts ν]
    (f : D11.Ch19.Cc (X × Y) 𝕜) :
    Continuous (fun x => ∫ y, f (x,y) ∂ν) := by
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (f := fun x y => f (x,y))
    (f.hasCompactSupport.image continuous_snd) f.continuous.continuousOn
  intro x y _ hy
  exact section_eq_zero f x y hy

omit [T2Space Y] in
/-- The support of the parameter integral lies in the first projection. -/
theorem section_integral_support (ν : Measure Y) (f : D11.Ch19.Cc (X × Y) 𝕜) :
    tsupport (fun x => ∫ y, f (x,y) ∂ν) ⊆ Prod.fst '' tsupport f := by
  apply closure_minimal _ (f.hasCompactSupport.image continuous_fst).isClosed
  intro x hx
  by_contra h
  have hz (y : Y) : f (x,y) = 0 := by
    by_contra hn
    exact h ⟨(x,y), subset_tsupport f hn, rfl⟩
  exact hx (by simp only [hz, integral_zero])

/-- The actual section integral, bundled as a compact-support continuous map. -/
def integralSection (ν : Measure Y) [IsFiniteMeasureOnCompacts ν]
    (f : D11.Ch19.Cc (X × Y) 𝕜) : D11.Ch19.Cc X 𝕜 where
  toFun x := ∫ y, f (x,y) ∂ν
  continuous_toFun := continuous_section_integral ν f
  hasCompactSupport' := (f.hasCompactSupport.image continuous_fst).of_isClosed_subset
    (isClosed_tsupport _) (section_integral_support ν f)

/-- Exchange the coordinates without changing the canonical Cc object. -/
def swap (f : D11.Ch19.Cc (X × Y) 𝕜) : D11.Ch19.Cc (Y × X) 𝕜 where
  toFun p := f (p.2,p.1)
  continuous_toFun := f.continuous.comp continuous_swap
  hasCompactSupport' := f.hasCompactSupport.comp_homeomorph (Homeomorph.prodComm Y X)

theorem measurable_finite_rectangle :
    Specs.D11.Ch18.CcIteratedIntegrals.measurable_finite_rectangle.{u, v} := by
  intro X _ _ _ Y _ _ _ 𝕜 _ μ ν hμ hν f
  have hK := f.hasCompactSupport.image continuous_fst
  have hL := f.hasCompactSupport.image continuous_snd
  refine ⟨CcTensorApproximation.product_borel_measurable X Y 𝕜 f,
    Prod.fst '' tsupport f, Prod.snd '' tsupport f,
    hK, hL, hK.measurableSet, hL.measurableSet,
    hμ.1 _ hK, hν.1 _ hL, ?_⟩
  intro p hp
  exact ⟨⟨p,hp,rfl⟩, ⟨p,hp,rfl⟩⟩

theorem sections_integrable :
    Specs.D11.Ch18.CcIteratedIntegrals.sections_integrable.{u, v} := by
  intro X _ _ _ Y _ _ _ 𝕜 _ μ ν hμ hν f
  let : IsFiniteMeasureOnCompacts μ := (compactFinite_iff μ).mp hμ.1
  let : IsFiniteMeasureOnCompacts ν := (compactFinite_iff ν).mp hν.1
  constructor
  · intro x
    have hc : Continuous (fun y => f (x,y)) :=
      f.continuous.comp (continuous_const.prodMk continuous_id)
    exact ⟨hc.measurable, hc.integrable_of_hasCompactSupport (section_hasCompactSupport f x)⟩
  · intro y
    have hc : Continuous (fun x => f (x,y)) :=
      f.continuous.comp (continuous_id.prodMk continuous_const)
    exact ⟨hc.measurable,
      hc.integrable_of_hasCompactSupport (section_hasCompactSupport (swap f) y)⟩

theorem section_integrals_cc :
    Specs.D11.Ch18.CcIteratedIntegrals.section_integrals_cc.{u, v} := by
  intro X _ _ _ Y _ _ _ 𝕜 _ μ ν hμ hν f
  let : IsFiniteMeasureOnCompacts μ := (compactFinite_iff μ).mp hμ.1
  let : IsFiniteMeasureOnCompacts ν := (compactFinite_iff ν).mp hν.1
  let g := integralSection ν f
  let h := integralSection μ (swap f)
  refine ⟨g,h,fun _ => rfl,fun _ => rfl,section_integral_support ν f, ?_,
    g.continuous.measurable,h.continuous.measurable,g.integrable,h.integrable⟩
  apply closure_minimal _ (f.hasCompactSupport.image continuous_snd).isClosed
  intro y hy
  by_contra hn
  have hz (x : X) := section_eq_zero f x y hn
  apply hy
  change (∫ x, f (x,y) ∂μ) = 0
  simp only [hz, integral_zero]

theorem iterated_integrals :
    Specs.D11.Ch18.CcIteratedIntegrals.iterated_integrals.{u, v} := by
  intro X _ _ _ Y _ _ _ 𝕜 _ μ ν hμ hν f
  let : IsFiniteMeasureOnCompacts μ := (compactFinite_iff μ).mp hμ.1
  let : IsFiniteMeasureOnCompacts ν := (compactFinite_iff ν).mp hν.1
  let fn : D11.Ch19.Cc (X × Y) ℝ :=
    ⟨⟨fun p => ‖f p‖, f.continuous.norm⟩, f.hasCompactSupport.norm⟩
  exact ⟨(integralSection ν fn).integrable,
    (integralSection μ (swap fn)).integrable,
    integral_integral_swap_of_hasCompactSupport (f := fun x y => f (x,y))
      f.continuous f.hasCompactSupport⟩

theorem positive_linear_functional :
    Specs.D11.Ch18.CcIteratedIntegrals.positive_linear_functional.{u, v} := by
  intro X _ _ _ Y _ _ _ μ ν hμ hν
  let : IsFiniteMeasureOnCompacts μ := (compactFinite_iff μ).mp hμ.1
  let : IsFiniteMeasureOnCompacts ν := (compactFinite_iff ν).mp hν.1
  let J : D11.Ch19.Cc (X × Y) ℝ →ₗ[ℝ] ℝ :=
    { toFun f := ∫ x, (∫ y, f (x,y) ∂ν) ∂μ
      map_add' f g := by
        have hinner : (fun x => ∫ y, (f + g) (x,y) ∂ν) =
            fun x => (∫ y, f (x,y) ∂ν) + ∫ y, g (x,y) ∂ν := by
          funext x
          exact integral_add ((sections_integrable X Y ℝ μ ν hμ hν f).1 x).2
            ((sections_integrable X Y ℝ μ ν hμ hν g).1 x).2
        change (∫ x, (∫ y, (f+g) (x,y) ∂ν) ∂μ) = _
        rw [hinner]
        exact integral_add (integralSection ν f).integrable (integralSection ν g).integrable
      map_smul' c f := by
        simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul,
          integral_const_mul, RingHom.id_apply] }
  refine ⟨PositiveLinearMap.mk₀ J ?_, fun _ => rfl⟩
  intro f hf
  exact integral_nonneg (fun x => integral_nonneg (fun y => hf (x,y)))

end D11.Ch18.CcIteratedIntegrals
