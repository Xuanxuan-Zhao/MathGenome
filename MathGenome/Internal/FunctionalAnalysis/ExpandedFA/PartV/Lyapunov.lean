import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.Lyapunov
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.LyapunovPurification
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-! Lyapunov's finite-dimensional range theorem, assembled from purification.
The weak-star compact order interval is mapped continuously by its L¹ tests.
Signed Radon–Nikodym coordinates connect that image to native vector measures.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v

namespace ExpandedFA.PartV.Lyapunov

variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

/-- Forgetting all moments gives precisely the closed order interval. -/
theorem densityInterval_eq_zero_fiber :
    Spec.densityInterval μ = LyapunovPurification.Spec.densityFiber μ
      (fun j : Fin 0 => Fin.elim0 j) (fun j : Fin 0 => Fin.elim0 j) := by
  ext g
  simp [Spec.densityInterval, LyapunovPurification.Spec.densityFiber]

theorem densityInterval_isCompact [IsFiniteMeasure μ] :
    @IsCompact (Lp ℝ ∞ μ) (LyapunovPurification.Spec.densityWeakStarTopology μ)
      (Spec.densityInterval μ) := by
  rw [densityInterval_eq_zero_fiber]
  exact LyapunovPurification.compact_fiber μ _ (fun j => Fin.elim0 j) _

theorem densityInterval_convex : Convex ℝ (Spec.densityInterval μ) := by
  rw [densityInterval_eq_zero_fiber]
  exact LyapunovPurification.densityFiber_convex _ (fun j => Fin.elim0 j) _

/-- The topology used here is exactly σ(L∞, L¹). -/
theorem momentMap_continuous {n : ℕ} (h : Fin n → X → ℝ)
    (hh : ∀ j, Integrable (h j) μ) :
    @Continuous (Lp ℝ ∞ μ) (Fin n → ℝ)
      (LyapunovPurification.Spec.densityWeakStarTopology μ) inferInstance
      (Spec.momentMap μ h) := by
  let : TopologicalSpace (Lp ℝ ∞ μ) :=
    LyapunovPurification.Spec.densityWeakStarTopology μ
  apply continuous_pi
  intro j
  let f : Lp ℝ 1 μ := (memLp_one_iff_integrable.mpr (hh j)).toLp (h j)
  have hc : Continuous (fun g : Lp ℝ ∞ μ => ∫ x, g x * f x ∂μ) :=
    continuous_iInf_dom (i := f) continuous_induced_dom
  convert hc using 1
  funext g
  apply integral_congr_ae
  filter_upwards [(memLp_one_iff_integrable.mpr (hh j)).coeFn_toLp] with x hx
  rw [hx]

theorem moment_image_compact_convex : Spec.MomentImageCompactConvex.{u} := by
  intro X _ μ _ n h hh
  let : TopologicalSpace (Lp ℝ ∞ μ) :=
    LyapunovPurification.Spec.densityWeakStarTopology μ
  refine ⟨densityInterval_isCompact.image (momentMap_continuous h hh), ?_⟩
  exact densityInterval_convex.linear_image (LyapunovPurification.momentLinear h hh)

theorem range_eq_moment_image : Spec.RangeEqualsMomentImage.{u} := by
  intro X _ μ _ hatom n h hh
  apply Set.Subset.antisymm
  · rintro b ⟨s, hs, rfl⟩
    let g : Lp ℝ ∞ μ := indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℝ)
    have hg : g =ᵐ[μ] s.indicator (fun _ => (1 : ℝ)) := indicatorConstLp_coeFn
    refine ⟨g, ?_, ?_⟩
    · filter_upwards [hg] with x hx
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [hxs]
    · funext j
      exact LyapunovPurification.moment_eq_setIntegral h g hs hg j
  · rintro b ⟨g, hg, rfl⟩
    obtain ⟨s, hs, he⟩ := LyapunovPurification.purification μ hatom h hh g
      (Lp.aestronglyMeasurable g) hg
    exact ⟨s, hs, funext he⟩

/-- Signed RN gives actual integrable representatives for all coordinates. -/
theorem coordinate_lyapunov : Spec.CoordinateLyapunov.{u} := by
  intro X _ μ _ hatom n m hm
  let h : Fin n → X → ℝ := fun j => (m j).rnDeriv μ
  have hh : ∀ j, Integrable (h j) μ := fun j => (m j).integrable_rnDeriv μ
  have hr (s : Set X) (hs : MeasurableSet s) (j : Fin n) :
      m j s = ∫ x in s, h j x ∂μ := by
    have hac : m j ≪ᵥ μ.toENNRealVectorMeasure := by
      apply ((m j).absolutelyContinuous_ennreal_iff _).mpr
      simpa using hm j
    rw [← (m j).withDensityᵥ_rnDeriv_eq μ hac, withDensityᵥ_apply (hh j) hs]
  have he : Spec.measurableRange (fun s => fun j => m j s) =
      Spec.momentMap μ h '' Spec.densityInterval μ := by
    rw [← range_eq_moment_image μ hatom h hh]
    ext b
    constructor <;> rintro ⟨s, hs, he⟩ <;> refine ⟨s, hs, ?_⟩
    · exact (funext (hr s hs)).symm.trans he
    · exact (funext (hr s hs)).trans he
  have hc := moment_image_compact_convex μ h hh
  exact ⟨h, hh, hr, he, he ▸ hc.1, he ▸ hc.2⟩

/-- Transport the finite list of signed coordinates back through a real basis.
The control measure is not required to have a countably generated sigma algebra. -/
theorem dominated_lyapunov : Spec.DominatedLyapunov.{u, v} := by
  intro X _ E _ _ _ μ _ hatom m hm
  let e : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    (Module.finBasis ℝ E).equivFunL
  let c : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ :=
    fun j => (ContinuousLinearMap.proj j).comp e.toContinuousLinearMap
  let a : Fin (Module.finrank ℝ E) → SignedMeasure X :=
    fun j => m.mapRange (c j).toAddMonoidHom (c j).continuous
  have ha (j : Fin (Module.finrank ℝ E)) : (a j).totalVariation ≪ μ := by
    have hac : a j ≪ᵥ μ.toENNRealVectorMeasure := by
      intro s hs
      change c j (m s) = 0
      rw [hm hs, map_zero]
    have hh := ((a j).absolutelyContinuous_ennreal_iff _).mp hac
    simpa using hh
  obtain ⟨h, hh, hr, he, hk, hv⟩ := coordinate_lyapunov μ hatom a ha
  have him : Spec.measurableRange m =
      e.symm '' Spec.measurableRange (fun s => fun j => a j s) := by
    apply Set.Subset.antisymm
    · rintro b ⟨s, hs, rfl⟩
      refine ⟨e (m s), ⟨s, hs, ?_⟩, e.symm_apply_apply _⟩
      rfl
    · rintro b ⟨z, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨s, hs, ?_⟩
      change m s = e.symm (e (m s))
      exact (e.symm_apply_apply _).symm
  rw [him]
  exact ⟨hk.image e.symm.continuous, hv.linear_image e.symm.toLinearMap⟩

/-- Lyapunov convexity for a finite-dimensional finite nonatomic real vector
measure, with atomlessness imposed on its actual total variation. -/
theorem lyapunov : Spec.FiniteDimensionalLyapunov.{u, v} := by
  intro X _ E _ _ _ m _ hatom
  exact dominated_lyapunov m.variation hatom m m.absolutelyContinuous

/-- A complex n-dimensional vector measure is a real finite-dimensional one.
Convexity remains real convexity. -/
theorem complex_lyapunov : Spec.ComplexLyapunov.{u} := by
  intro X _ n m _ hatom
  exact lyapunov m hatom

end ExpandedFA.PartV.Lyapunov
