import MathGenome.Internal.RealAnalysis.D11.Ch19.PositiveContentOuterMeasure
import MathGenome.Internal.RealAnalysis.D11.Ch19.PositiveFunctionalBound
import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonPredicates
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.PositiveContentRadon

/-!
# Radon regularity and exact compact-support estimates

The preceding construction has already identified the literal open-content
infimum on every subset with the canonical Riesz outer measure. Its regularity
formulas are exactly the shared Chapter 18 Radon predicate.

For an arbitrary set A with h ≥ 1 on A, the compact superlevel set K = {h ≥ 1}
contains A. Clipping h at one gives a nonnegative Cc function equal to one on K
and bounded above by h. The compact Riesz estimate and positivity therefore give
μ*(A) ≤ μ(K) ≤ I(min(h,1)) ≤ I(h). This also covers the empty set and zero h.
The other estimate is the native compact-support estimate, with the same measure.
-/

open Set MeasureTheory
open scoped ENNReal

namespace D11.Ch19.PositiveContentRadon
universe u

open D11.Ch19.PositiveContentOuterMeasure

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
variable (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ)
variable (hI : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ I f)

/-- The constructed Borel restriction is Radon in exactly the Chapter 18 sense. -/
theorem radon : D11.Ch18.isRadon (borelMeasure I hI) :=
  D11.Ch19.PositiveContentOuterMeasure.radon I hI

/-- A nonnegative Cc majorant of one bounds the outer mass of any subset. -/
theorem outerMeasure_le_functional (A : Set X) (h : CompactlySupportedContinuousMap X ℝ)
    (hh : ∀ x, 0 ≤ h x) (hA : ∀ x ∈ A, 1 ≤ h x) :
    outerMeasure I hI A ≤ ENNReal.ofReal (I h) := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let K : Set X := {x | 1 ≤ h x}
  have hK : IsCompact K := by
    apply h.hasCompactSupport.of_isClosed_subset (isClosed_le continuous_const h.continuous)
    intro x hx
    apply subset_closure
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx)
  let g : CompactlySupportedContinuousMap X ℝ :=
    ⟨⟨fun x => min (h x) 1, h.continuous.min continuous_const⟩,
      h.hasCompactSupport.comp_left (g := fun t : ℝ => min t 1) (by simp)⟩
  have hg : ∀ x, 0 ≤ g x := fun x => le_min (hh x) zero_le_one
  have hgK : ∀ x ∈ K, g x = 1 := fun x hx => min_eq_right hx
  have hgh : I g ≤ I h :=
    D11.Ch19.positive_functional_mono I hI (fun x => min_le_left (h x) 1)
  change RealRMK.rieszMeasure (positiveFunctional I hI) A ≤ ENNReal.ofReal (I h)
  calc
    RealRMK.rieszMeasure (positiveFunctional I hI) A ≤
        RealRMK.rieszMeasure (positiveFunctional I hI) K := measure_mono hA
    _ ≤ ENNReal.ofReal (I g) :=
      RealRMK.rieszMeasure_le_of_eq_one (positiveFunctional I hI) hg hK hgK
    _ ≤ ENNReal.ofReal (I h) := ENNReal.ofReal_le_ofReal hgh

/-- Tests bounded between zero and one and supported in K give lower bounds on μ(K). -/
theorem functional_le_compact_measure (K : Set X) (_hK : IsCompact K)
    (f : CompactlySupportedContinuousMap X ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hs : closure {x | f x ≠ 0} ⊆ K) :
    ENNReal.ofReal (I f) ≤ borelMeasure I hI K := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  exact RealRMK.le_rieszMeasure_tsupport_subset (positiveFunctional I hI) hf hs

end D11.Ch19.PositiveContentRadon
