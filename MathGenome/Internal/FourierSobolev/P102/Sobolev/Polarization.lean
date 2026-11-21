import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.Polarization
import MathGenome.Internal.FourierSobolev.P102.U4.BiLipschitzPullback
import MathGenome.Internal.FourierSobolev.P102.U4.Truncations
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.HalfSpaceExtension
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Classical
namespace P102.U4
namespace PolarizationBridge

def coordinateLp {d : ℕ} (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : DomainLp ℝ Ω p) : ExpandedFA.Sobolev.DomainLp ℝ (ACL.coordinateDomain Ω) p :=
  Lp.compMeasurePreserving (ACL.coordinates d).symm
    ((PiLp.volume_preserving_toLp (Fin d)).restrict_preimage Ω.isOpen.measurableSet) f

theorem coordinateLp_coe {d : ℕ} (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : DomainLp ℝ Ω p) :
    coordinateLp Ω p f =ᵐ[volume.restrict (ACL.coordinateDomain Ω : Set (Fin d → ℝ))]
      f ∘ (ACL.coordinates d).symm :=
  Lp.coeFn_compMeasurePreserving _ _

theorem coordinate_graph {d : ℕ} (Ω : Opens (Space d)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (u : Sobolev ℝ Ω 1 p) :
    ExpandedFA.Sobolev.Lines.HasWeakCoordinateDerivatives
      (coordinateLp Ω p (sobolevUnderlying u))
      (fun j => coordinateLp Ω p (firstWeakDerivative u j)) := by
  intro j
  ext φ
  simp only [ExpandedFA.Sobolev.lpDistribution_apply, neg_apply,
    ContinuousLinearMap.comp_apply]
  have h (φ : ExpandedFA.Distributions.Tests ℝ (ACL.coordinateDomain Ω))
      (f : DomainLp ℝ Ω p) :
      (∫ x in (ACL.coordinateDomain Ω : Set (Fin d → ℝ)),
        φ x * coordinateLp Ω p f x) =
      ∫ x, φ x * f ((ACL.coordinates d).symm x) := by
    calc
      _ = ∫ x in (ACL.coordinateDomain Ω : Set (Fin d → ℝ)),
          φ x * f ((ACL.coordinates d).symm x) := by
        apply integral_congr_ae
        filter_upwards [coordinateLp_coe Ω p f] with x hx
        exact congrArg (φ x * ·) hx
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp [φ.zero_on_compl hx]
  rw [h φ, h (ExpandedFA.Distributions.testPartialCLM [j] φ)]
  exact ACL.weak_identity_coordinates j (domainLp_locallyIntegrable Ω p _)
    (domainLp_locallyIntegrable Ω p _)
    (sobolev_derivative_distribution Ω 1 p u (firstSobolevIndex j)) φ

def fromProductLp {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : ExpandedFA.Sobolev.DomainLp ℝ (⊤ : Opens (Fin d → ℝ)) p) :
    DomainLp ℝ (⊤ : Opens (Space d)) p :=
  Lp.compMeasurePreserving (ACL.coordinates d)
    (by
      simp only [Opens.coe_top, Measure.restrict_univ]
      convert! PiLp.volume_preserving_ofLp (Fin d) using 1) f

theorem fromProductLp_coe {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : ExpandedFA.Sobolev.DomainLp ℝ (⊤ : Opens (Fin d → ℝ)) p) :
    fromProductLp p f =ᵐ[volume] f ∘ ACL.coordinates d := by
  have h := Lp.coeFn_compMeasurePreserving f
    (show MeasurePreserving (ACL.coordinates d)
      (volume.restrict (⊤ : Opens (Space d)))
      (volume.restrict (⊤ : Opens (Fin d → ℝ))) from
      by
        simp only [Opens.coe_top, Measure.restrict_univ]
        convert! PiLp.volume_preserving_ofLp (Fin d) using 1)
  convert! h using 1
  simp only [Opens.coe_top, Measure.restrict_univ]

theorem sobolev_of_product {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (v : ExpandedFA.Sobolev.DomainLp ℝ (⊤ : Opens (Fin d → ℝ)) p)
    (g : Fin d → ExpandedFA.Sobolev.DomainLp ℝ (⊤ : Opens (Fin d → ℝ)) p)
    (hw : ExpandedFA.Sobolev.Lines.HasWeakCoordinateDerivatives v g) :
    ∃ w : Sobolev ℝ (⊤ : Opens (Space d)) 1 p,
      sobolevUnderlying w =ᵐ[volume] v ∘ ACL.coordinates d := by
  obtain ⟨f, hrep, hacl⟩ := ExpandedFA.Sobolev.Lines.weak_to_acl v g hw
  have hpres : MeasurePreserving (ACL.coordinates d) volume volume := by
    convert! PiLp.volume_preserving_ofLp (Fin d) using 1
  have hcoord := hpres.quasiMeasurePreserving.ae
    (show v =ᵐ[volume] f from by simpa only [Opens.coe_top, Measure.restrict_univ] using hrep)
  have heq (j : Fin d) : distributionPartial {j}
      (regularDistribution ⊤ (fromProductLp p v)) =
      regularDistribution ⊤ (fromProductLp p (g j)) := by
    apply ACL.representative_to_weak j
      (domainLp_locallyIntegrable ⊤ p _) (domainLp_locallyIntegrable ⊤ p _)
    refine ⟨f ∘ ACL.coordinates d, ?_, ?_⟩
    · convert! (fromProductLp_coe p v).trans hcoord using 1
      simp only [Opens.coe_top, Measure.restrict_univ]
    · filter_upwards [hacl j, ACL.ae_on_fibers j
        (show fromProductLp p (g j) =ᵐ[volume.restrict (⊤ : Opens (Space d))]
          g j ∘ ACL.coordinates d from
          by simpa only [Opens.coe_top, Measure.restrict_univ] using fromProductLp_coe p (g j))]
        with z hz hgz
      refine ⟨?_, ?_⟩
      · change ExpandedFA.Sobolev.Lines.LocallyAbsolutelyContinuousOn
          (fun t => f (ExpandedFA.Sobolev.Lines.coordinateLine j z t)) Set.univ
        simpa only [ExpandedFA.Sobolev.Lines.fiber, Opens.coe_top, Set.preimage_univ, Opens.coe_mk] using hz.1
      · filter_upwards [hz.2, hgz] with t hzt hgt
        rw [hgt]
        exact hzt
  obtain ⟨w, hw, _⟩ := firstOrder_graph ⊤ p (fromProductLp p v)
    (fun j => fromProductLp p (g j)) heq
  refine ⟨w, ?_⟩
  rw [hw]
  exact fromProductLp_coe p v
end PolarizationBridge
end P102.U4

namespace P102.U4.PolarizationBridge
open P102.U4

def productUpperLp {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (i : Fin d)
    (f : DomainLp ℝ (⊤ : Opens (Space d)) p) :
    ExpandedFA.Sobolev.DomainLp ℝ (ExpandedFA.Sobolev.HalfSpace.upper i) p :=
  (show MemLp (fun x : (Fin d → ℝ) => f (WithLp.toLp 2 x)) p
    (volume.restrict (ExpandedFA.Sobolev.HalfSpace.upper i : Set ((Fin d → ℝ)))) from
    ((show MemLp f p volume by simpa using Lp.memLp f).comp_measurePreserving
      (PiLp.volume_preserving_toLp (Fin d))).mono_measure Measure.restrict_le_self).toLp _

theorem productUpperLp_ae {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (i : Fin d)
    (f : DomainLp ℝ (⊤ : Opens (Space d)) p) :
    productUpperLp i f =ᵐ[volume.restrict (ExpandedFA.Sobolev.HalfSpace.upper i : Set ((Fin d → ℝ)))]
      (fun x => f (WithLp.toLp 2 x)) := MemLp.coeFn_toLp _

theorem upper_pairing {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (i : Fin d)
    (f : DomainLp ℝ (⊤ : Opens (Space d)) p)
    (φ : ExpandedFA.Distributions.Tests ℝ (ExpandedFA.Sobolev.HalfSpace.upper i)) :
    (∫ x in (ExpandedFA.Sobolev.HalfSpace.upper i : Set ((Fin d → ℝ))), φ x * productUpperLp i f x) =
      ∫ x, φ x * f (WithLp.toLp 2 x) := by
  calc
    _ = ∫ x in (ExpandedFA.Sobolev.HalfSpace.upper i : Set ((Fin d → ℝ))), φ x * f (WithLp.toLp 2 x) :=
      integral_congr_ae ((productUpperLp_ae i f).mono fun x hx => by rw [hx])
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      simp [φ.zero_on_compl hx]

theorem productUpper_weak {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (i : Fin d)
    (u : Sobolev ℝ (⊤ : Opens (Space d)) 1 p) :
    ExpandedFA.Sobolev.Lines.HasWeakCoordinateDerivatives
      (productUpperLp i (sobolevUnderlying u))
      (fun j => productUpperLp i (Truncations.sobolevFirstDerivative u j)) := by
  intro j
  let U : Opens (Space d) := ⟨{x | 0 < x i},
    isOpen_lt continuous_const ((EuclideanSpace.proj i).continuous)⟩
  have hu := domainLp_locallyIntegrable (⊤ : Opens (Space d)) p (sobolevUnderlying u)
  have hg := domainLp_locallyIntegrable (⊤ : Opens (Space d)) p
    (Truncations.sobolevFirstDerivative u j)
  have hw : distributionPartial {j} (regularDistribution U (sobolevUnderlying u)) =
      regularDistribution U (Truncations.sobolevFirstDerivative u j) := by
    apply weakDerivative_restrict (show U ≤ ⊤ from le_top) _ _ hu hg j
    exact sobolev_derivative_distribution ⊤ 1 p u (Truncations.firstSobolevIndex j)
  ext φ
  simp only [ExpandedFA.Sobolev.lpDistribution_apply, _root_.neg_apply,
    ContinuousLinearMap.comp_apply]
  rw [upper_pairing, upper_pairing]
  exact ACL.weak_identity_coordinates j (hu.mono_set (subset_univ _))
    (hg.mono_set (subset_univ _)) hw φ



theorem exists_coordinate_even_extension {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (i : Fin d) (u : Sobolev ℝ (⊤ : Opens (Space d)) 1 p) :
    ∃ w : Sobolev ℝ (⊤ : Opens (Space d)) 1 p,
      sobolevUnderlying w =ᵐ[volume] fun x =>
        if 0 < x i then sobolevUnderlying u x else
          sobolevUnderlying u (WithLp.toLp 2
            (ExpandedFA.Sobolev.HalfSpace.reflect i (WithLp.ofLp x))) := by
  let a := productUpperLp i (sobolevUnderlying u)
  let b := fun j => productUpperLp i (firstWeakDerivative u j)
  let v := ExpandedFA.Sobolev.HalfSpace.reflectLp i false a
  let h := fun j => ExpandedFA.Sobolev.HalfSpace.reflectLp i (decide (j = i)) (b j)
  have hw := ExpandedFA.Sobolev.HalfSpace.weak_reflection ℝ d i p a b
    (productUpper_weak i u) v h
    (ExpandedFA.Sobolev.HalfSpace.reflectLp_coe i false a)
    (fun j => ExpandedFA.Sobolev.HalfSpace.reflectLp_coe i (decide (j = i)) (b j))
  obtain ⟨w, hw⟩ := sobolev_of_product p v h hw
  refine ⟨w, hw.trans ?_⟩
  let raw : (Fin d → ℝ) → ℝ := fun y => sobolevUnderlying u (WithLp.toLp 2 y)
  have hr : v =ᵐ[volume] ExpandedFA.Sobolev.HalfSpace.reflection i false raw :=
    (ExpandedFA.Sobolev.HalfSpace.reflectLp_coe i false a).trans
      (ExpandedFA.Sobolev.HalfSpace.reflection_congr i false
        (productUpperLp_ae i (sobolevUnderlying u)))
  have he : ExpandedFA.Sobolev.HalfSpace.reflection i false raw =ᵐ[volume]
      (fun y => if 0 < y i then raw y else raw (ExpandedFA.Sobolev.HalfSpace.reflect i y)) := by
    filter_upwards [Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i 0] with y hy
    by_cases hp : 0 < y i
    · simp [hp]
    · have hn : y i < 0 := lt_of_le_of_ne (le_of_not_gt hp) hy
      simp [ExpandedFA.Sobolev.HalfSpace.reflection_of_neg i false raw hn, hp]
  have hpres : MeasurePreserving (ACL.coordinates d) volume volume := by
    convert! PiLp.volume_preserving_ofLp (Fin d) using 1
  have hc := hpres.quasiMeasurePreserving.ae_eq_comp (hr.trans he)
  exact hc
end P102.U4.PolarizationBridge

namespace P102.Sobolev
open P102.U4
namespace Polarization

/-- The Euclidean gradient assembled from the canonical Lp derivatives is measurable. -/
theorem measurable_gradient {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (g : WholeSobolev d p) :
    Measurable (gradient g) := by
  exact (PiLp.continuous_toLp 2 _).measurable.comp
    (Measurable.of_eval (fun j => (Lp.stronglyMeasurable (firstWeakDerivative g j)).measurable))

/-- Finite-coordinate Lp membership uses the Euclidean norm. -/
theorem memLp_gradient {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (g : WholeSobolev d p) :
    MemLp (gradient g) p volume := by
  apply memLp_piLp_iff.mpr
  intro j
  simpa only [gradient, WithLp.ofLp_toLp, Opens.coe_top, Measure.restrict_univ] using
    Lp.memLp (firstWeakDerivative g j)

/-- Addition and subtraction commute with the chosen representatives a.e. -/
theorem underlying_sub_ae {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u v : WholeSobolev d p) :
    sobolevUnderlying (u - v) =ᵐ[volume]
      (fun x => sobolevUnderlying u x - sobolevUnderlying v x) := by
  have he : sobolevUnderlying (u - v) = sobolevUnderlying u - sobolevUnderlying v := rfl
  rw [he]
  have h := Lp.coeFn_sub (sobolevUnderlying u) (sobolevUnderlying v)
  simp only [Opens.coe_top, Measure.restrict_univ] at h
  convert! h using 1

theorem underlying_add_ae {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u v : WholeSobolev d p) :
    sobolevUnderlying (u + v) =ᵐ[volume]
      (fun x => sobolevUnderlying u x + sobolevUnderlying v x) := by
  have he : sobolevUnderlying (u + v) = sobolevUnderlying u + sobolevUnderlying v := rfl
  rw [he]
  have h := Lp.coeFn_add (sobolevUnderlying u) (sobolevUnderlying v)
  simp only [Opens.coe_top, Measure.restrict_univ] at h
  convert! h using 1

theorem derivative_sub_ae {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u v : WholeSobolev d p) (j : Fin d) :
    firstWeakDerivative (u - v) j =ᵐ[volume]
      (fun x => firstWeakDerivative u j x - firstWeakDerivative v j x) := by
  have he : firstWeakDerivative (u - v) j = firstWeakDerivative u j - firstWeakDerivative v j := rfl
  rw [he]
  have h := Lp.coeFn_sub (firstWeakDerivative u j) (firstWeakDerivative v j)
  simp only [Opens.coe_top, Measure.restrict_univ] at h
  convert! h using 1

theorem derivative_add_ae {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u v : WholeSobolev d p) (j : Fin d) :
    firstWeakDerivative (u + v) j =ᵐ[volume]
      (fun x => firstWeakDerivative u j x + firstWeakDerivative v j x) := by
  have he : firstWeakDerivative (u + v) j = firstWeakDerivative u j + firstWeakDerivative v j := rfl
  rw [he]
  have h := Lp.coeFn_add (firstWeakDerivative u j) (firstWeakDerivative v j)
  simp only [Opens.coe_top, Measure.restrict_univ] at h
  convert! h using 1

/-- Max and min belong to the actual weak Sobolev graph. The formulas retain
the original derivative at ties, justified by the zero-level derivative rule. -/
theorem sobolev_max_min {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u v : WholeSobolev d p) :
    ∃ a b : WholeSobolev d p,
      (sobolevUnderlying a =ᵐ[volume]
        (fun x => max (sobolevUnderlying u x) (sobolevUnderlying v x))) ∧
      (sobolevUnderlying b =ᵐ[volume]
        (fun x => min (sobolevUnderlying u x) (sobolevUnderlying v x))) ∧
      (∀ j, firstWeakDerivative a j =ᵐ[volume]
        (fun x => if sobolevUnderlying v x ≤ sobolevUnderlying u x
          then firstWeakDerivative u j x else firstWeakDerivative v j x)) ∧
      (∀ j, firstWeakDerivative b j =ᵐ[volume]
        (fun x => if sobolevUnderlying u x ≤ sobolevUnderlying v x
          then firstWeakDerivative u j x else firstWeakDerivative v j x)) := by
  obtain ⟨q, hq, hDq⟩ := lower_truncation_rule ⊤ p (u - v) 0 (Or.inl le_rfl)
  simp only [Opens.coe_top, Measure.restrict_univ] at hq hDq
  change ∀ j, firstWeakDerivative q j =ᵐ[volume]
    (fun x => if 0 < sobolevUnderlying (u - v) x then firstWeakDerivative (u - v) j x else 0)
      at hDq
  refine ⟨v + q, u - q, ?_, ?_, ?_, ?_⟩
  · filter_upwards [underlying_add_ae v q, hq, underlying_sub_ae u v] with x ha hq hs
    rw [ha, hq, hs]
    rcases le_total (sobolevUnderlying u x) (sobolevUnderlying v x) with h | h
    · rw [max_eq_right h, max_eq_left (sub_nonpos.mpr h), add_zero]
    · rw [max_eq_left h, max_eq_right (sub_nonneg.mpr h)]
      ring
  · filter_upwards [underlying_sub_ae u q, hq, underlying_sub_ae u v] with x ha hq hs
    rw [ha, hq, hs]
    rcases le_total (sobolevUnderlying u x) (sobolevUnderlying v x) with h | h
    · rw [min_eq_left h, max_eq_left (sub_nonpos.mpr h), sub_zero]
    · rw [min_eq_right h, max_eq_right (sub_nonneg.mpr h)]
      ring
  · intro j
    have hl := truncation_level_set ⊤ p (u - v) 0 j
    simp only [Opens.coe_top, Measure.restrict_univ] at hl
    filter_upwards [derivative_add_ae v q j, hDq j, underlying_sub_ae u v,
      derivative_sub_ae u v j, hl] with x ha hq hs hds hl
    change firstWeakDerivative (v + q) j x = _ at ha ⊢
    rw [ha, hq, hs]
    change firstWeakDerivative (u - v) j x = _ at hds
    rw [hds]
    by_cases he : sobolevUnderlying u x = sobolevUnderlying v x
    · have hz := hl (by rw [hs, he, sub_self])
      change firstWeakDerivative (u - v) j x = 0 at hz
      rw [hds] at hz
      simp only [he, sub_self, lt_self_iff_false, ite_false, le_refl, ite_true, add_zero]
      exact (sub_eq_zero.mp hz).symm
    · by_cases hlt : sobolevUnderlying v x < sobolevUnderlying u x
      · simp [sub_pos.mpr hlt, hlt.le]
      · have hgt : sobolevUnderlying u x < sobolevUnderlying v x :=
          lt_of_le_of_ne (le_of_not_gt hlt) he
        simp [not_lt.mpr (sub_nonpos.mpr hgt.le), not_le.mpr hgt]
  · intro j
    filter_upwards [derivative_sub_ae u q j, hDq j, underlying_sub_ae u v,
      derivative_sub_ae u v j] with x ha hq hs hds
    rw [ha, hq, hs]
    rw [hds]
    by_cases hle : sobolevUnderlying u x ≤ sobolevUnderlying v x
    · simp [hle, not_lt.mpr (sub_nonpos.mpr hle)]
    · simp [hle, sub_pos.mpr (lt_of_not_ge hle)]

/-- Local equality of Sobolev functions gives local equality of their weak
coordinate derivatives. No boundary gluing is asserted here. -/
theorem derivative_locality {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u v : WholeSobolev d p) (U : Opens (Space d))
    (huv : sobolevUnderlying u =ᵐ[volume.restrict (U : Set (Space d))] sobolevUnderlying v)
    (j : Fin d) :
    firstWeakDerivative u j =ᵐ[volume.restrict (U : Set (Space d))] firstWeakDerivative v j := by
  have hsub : (U : Set (Space d)) ⊆ (⊤ : Opens (Space d)) := subset_univ _
  have hL (f : DomainLp ℝ (⊤ : Opens (Space d)) p) :=
    (domainLp_locallyIntegrable ⊤ p f).mono_set hsub
  have he := (regular_injectivity d ℝ U _ _
    (hL (sobolevUnderlying u)) (hL (sobolevUnderlying v))).mpr huv
  have hD (w : WholeSobolev d p) :
      distributionPartial {j} (regularDistribution U (sobolevUnderlying w)) =
        regularDistribution U (firstWeakDerivative w j) := by
    apply weakDerivative_restrict (show U ≤ ⊤ from le_top) _ _
      (domainLp_locallyIntegrable ⊤ p _) (domainLp_locallyIntegrable ⊤ p _) j
    convert! sobolev_derivative_distribution ⊤ 1 p w (firstSobolevIndex j) using 1
  apply (regular_injectivity d ℝ U _ _
    (hL (firstWeakDerivative u j)) (hL (firstWeakDerivative v j))).mp
  rw [← hD u, ← hD v, he]

/-- Locality in the actual Euclidean vector of weak derivatives. -/
theorem gradient_locality {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u v : WholeSobolev d p) (U : Opens (Space d))
    (huv : sobolevUnderlying u =ᵐ[volume.restrict (U : Set (Space d))] sobolevUnderlying v) :
    gradient u =ᵐ[volume.restrict (U : Set (Space d))] gradient v := by
  filter_upwards [ae_all_iff.mpr (fun j => derivative_locality u v U huv j)] with x hx
  ext j
  exact hx j

/-- Vector form of max/min weak calculus, with Euclidean gradient representatives. -/
theorem sobolev_max_min_gradient {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u v : WholeSobolev d p) :
    ∃ a b : WholeSobolev d p,
      (sobolevUnderlying a =ᵐ[volume]
        (fun x => max (sobolevUnderlying u x) (sobolevUnderlying v x))) ∧
      (sobolevUnderlying b =ᵐ[volume]
        (fun x => min (sobolevUnderlying u x) (sobolevUnderlying v x))) ∧
      (gradient a =ᵐ[volume] (fun x => if sobolevUnderlying v x ≤ sobolevUnderlying u x
          then gradient u x else gradient v x)) ∧
      (gradient b =ᵐ[volume] (fun x => if sobolevUnderlying u x ≤ sobolevUnderlying v x
          then gradient u x else gradient v x)) := by
  obtain ⟨a, b, ha, hb, hDa, hDb⟩ := sobolev_max_min u v
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · filter_upwards [ae_all_iff.mpr hDa] with x hx
    by_cases h : sobolevUnderlying v x ≤ sobolevUnderlying u x
    all_goals
      simp only [h, ite_true, ite_false]
      ext j
      simpa only [gradient, WithLp.ofLp_toLp, h, ite_true, ite_false] using hx j
  · filter_upwards [ae_all_iff.mpr hDb] with x hx
    by_cases h : sobolevUnderlying u x ≤ sobolevUnderlying v x
    all_goals
      simp only [h, ite_true, ite_false]
      ext j
      simpa only [gradient, WithLp.ofLp_toLp, h, ite_true, ite_false] using hx j

namespace Halfspace

variable {d : ℕ} (H : Halfspace d)

/-- The specified isometry has the usual rank-one reflection formula. -/
theorem linearReflection_apply (x : Space d) :
    H.linearReflection x = x - (2 * inner ℝ H.normal x) • H.normal := by
  simp [linearReflection, Submodule.reflection_singleton_apply, H.normal_unit,
    neg_sub, mul_smul, two_smul]

/-- Explicit affine reflection formula. -/
theorem reflection_apply (x : Space d) :
    H.reflection x = x + (2 * (H.offset - inner ℝ H.normal x)) • H.normal := by
  rw [reflection, linearReflection_apply]
  rw [sub_eq_add_neg, ← neg_smul, add_assoc, ← add_smul]
  congr 2
  ring

@[simp] theorem inner_reflection (x : Space d) :
    inner ℝ H.normal (H.reflection x) = 2 * H.offset - inner ℝ H.normal x := by
  rw [reflection_apply, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    H.normal_unit]
  ring

@[simp] theorem reflection_reflection (x : Space d) :
    H.reflection (H.reflection x) = x := by
  rw [reflection_apply, inner_reflection, reflection_apply, add_assoc, ← add_smul]
  have he : 2 * (H.offset - inner ℝ H.normal x) +
      2 * (H.offset - (2 * H.offset - inner ℝ H.normal x)) = 0 := by ring
  rw [he, zero_smul, add_zero]

theorem reflection_eq_self {x : Space d} (hx : inner ℝ H.normal x = H.offset) :
    H.reflection x = x := by
  simp [reflection_apply, hx]

theorem reflection_continuous : Continuous H.reflection :=
  H.linearReflection.continuous.add continuous_const

/-- Orthogonal maps followed by translation preserve Euclidean Lebesgue measure. -/
theorem reflection_measurePreserving : MeasurePreserving H.reflection volume volume := by
  exact (measurePreserving_add_right volume ((2 * H.offset) • H.normal)).comp
    H.linearReflection.measurePreserving

/-- The reflecting plane is a proper affine hyperplane, hence Lebesgue null. -/
theorem boundary_null : volume {x : Space d | inner ℝ H.normal x = H.offset} = 0 := by
  let A : AffineSubspace ℝ (Space d) :=
    AffineSubspace.mk' (H.offset • H.normal) (innerSL ℝ H.normal).ker
  have hA : (A : Set (Space d)) = {x | inner ℝ H.normal x = H.offset} := by
    ext x
    change (inner ℝ H.normal (x - H.offset • H.normal) = 0) ↔ _
    simp only [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
      H.normal_unit, one_pow, mul_one, mem_ofPred_eq, sub_eq_zero]
  rw [← hA]
  apply Measure.addHaar_affineSubspace volume A
  intro he
  have hz : (0 : Space d) ∈ A := he ▸ (by simp)
  rw [← SetLike.mem_coe, hA] at hz
  simp only [mem_ofPred_eq, inner_zero_right] at hz
  exact H.offset_pos.ne' hz.symm

/-- The affine reflection is an isometry, independently of its offset. -/
theorem reflection_isometry : Isometry H.reflection := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  simp only [reflection, dist_add_right, H.linearReflection.dist_map]

theorem reflection_dist_sq (x y : Space d) :
    dist x (H.reflection y) ^ 2 - dist x y ^ 2 =
      4 * (H.offset - inner ℝ H.normal x) * (H.offset - inner ℝ H.normal y) := by
  rw [H.reflection_apply, dist_eq_norm, dist_eq_norm]
  rw [show x - (y + (2 * (H.offset - inner ℝ H.normal y)) • H.normal) =
    (x - y) + (- (2 * (H.offset - inner ℝ H.normal y))) • H.normal by simp [sub_eq_add_neg, neg_smul, add_assoc, add_comm ]]
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, H.normal_unit, mul_one,
    Real.norm_eq_abs, sq_abs, inner_sub_left, real_inner_comm x H.normal,
    real_inner_comm y H.normal]
  ring

theorem dist_reflection_le_of_opposite {x y : Space d}
    (hxy : (H.offset - inner ℝ H.normal x) * (H.offset - inner ℝ H.normal y) ≤ 0) :
    dist x (H.reflection y) ≤ dist x y := by
  have he := H.reflection_dist_sq x y
  have hp : 4 * ((H.offset - inner ℝ H.normal x) *
    (H.offset - inner ℝ H.normal y)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num) hxy
  nlinarith [show 0 ≤ dist x (H.reflection y) from dist_nonneg,
    show 0 ≤ dist x y from dist_nonneg]

/-- Polarization preserves the global Lipschitz constant. -/
theorem lipschitzWith_polarize {f : Space d → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : LipschitzWith K (H.polarize f) := by
  have hr : LipschitzWith K (f ∘ H.reflection) := by
    simpa using hf.comp H.reflection_isometry.lipschitzWith
  have hmax : LipschitzWith K (fun x => max (f x) (f (H.reflection x))) := by
    simpa using hf.max hr
  have hmin : LipschitzWith K (fun x => min (f x) (f (H.reflection x))) := by
    simpa using hf.min hr
  have hsel (x : Space d) : H.polarize f x = f x ∨
      H.polarize f x = f (H.reflection x) := by
    dsimp [polarize]
    split_ifs
    · exact max_choice _ _
    · exact min_choice _ _
  have hcross (x y : Space d)
      (hxy : (H.offset - inner ℝ H.normal x) * (H.offset - inner ℝ H.normal y) ≤ 0) :
      dist (H.polarize f x) (H.polarize f y) ≤ K * dist x y := by
    have h₁ := H.dist_reflection_le_of_opposite hxy
    have h₂ : dist (H.reflection x) y ≤ dist x y := by
      rw [dist_comm (H.reflection x), dist_comm x]
      exact H.dist_reflection_le_of_opposite (by rwa [mul_comm])
    rcases hsel x with hx | hx <;> rcases hsel y with hy | hy <;> rw [hx, hy]
    · exact hf.dist_le_mul x y
    · exact (hf.dist_le_mul x (H.reflection y)).trans
        (mul_le_mul_of_nonneg_left h₁ K.coe_nonneg)
    · exact (hf.dist_le_mul (H.reflection x) y).trans
        (mul_le_mul_of_nonneg_left h₂ K.coe_nonneg)
    · exact hr.dist_le_mul x y
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : x ∈ H.nearSide <;> by_cases hy : y ∈ H.nearSide
  · simpa only [polarize, hx, hy, ite_true] using hmax.dist_le_mul x y
  · apply hcross
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (le_of_lt hx))
      (sub_nonpos.mpr (le_of_not_gt hy))
  · apply hcross
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hx))
      (sub_nonneg.mpr (le_of_lt hy))
  · simpa only [polarize, hx, hy, ite_false] using hmin.dist_le_mul x y

/-- The genuine bi-Lipschitz chart used for Sobolev pullback; neither smoothness
nor an assumed Sobolev reflection certificate is built into the chart. -/
def reflectionChart : BiLipschitzChart (⊤ : Opens (Space d)) ⊤ 1 1 where
  toFun := H.reflection
  invFun := H.reflection
  mapsTo := fun _ _ => mem_univ _
  inv_mapsTo := fun _ _ => mem_univ _
  left_inv := fun x _ => H.reflection_reflection x
  right_inv := fun x _ => H.reflection_reflection x
  lipschitz := H.reflection_isometry.lipschitzWith.lipschitzOnWith
  inv_lipschitz := H.reflection_isometry.lipschitzWith.lipschitzOnWith

/-- A reflected Sobolev function, with its actual coordinate chain rule.
This uses the current proved whole-space pullback theorem. -/
theorem reflected_sobolev
    (hd : 0 < d) (p : ℝ≥0∞) [Fact (1 ≤ p)] (g : WholeSobolev d p) :
    ∃ v : WholeSobolev d p,
      (sobolevUnderlying v =ᵐ[volume] sobolevUnderlying g ∘ H.reflection) ∧
      ∀ j : Fin d, firstWeakDerivative v j =ᵐ[volume]
        (fun x => ∑ i : Fin d,
          (chartDerivative H.reflectionChart x (coordinateVector d j) i) *
            firstWeakDerivative g i (H.reflection x)) := by
  obtain ⟨T, hT, hDT, _⟩ := bilipschitz_sobolevPullback d hd ℝ ⊤ ⊤ 1 1 H.reflectionChart p
  refine ⟨T g, ?_, ?_⟩
  · simpa only [Opens.coe_top, Measure.restrict_univ, reflectionChart] using hT g
  · intro j
    simpa only [Opens.coe_top, Measure.restrict_univ, reflectionChart, smul_eq_mul] using hDT g j

section Flattening
variable (j : Fin d)

def normalRotation : Space d ≃ₗᵢ[ℝ] Space d :=
  Submodule.reflection (ℝ ∙ (H.normal - coordinateVector d j))ᗮ

theorem normalRotation_normal : H.normalRotation j H.normal = coordinateVector d j := by
  apply Submodule.reflection_sub
  rw [H.normal_unit]
  simp [coordinateVector, PiLp.norm_single]

@[simp] theorem normalRotation_twice (x : Space d) :
    H.normalRotation j (H.normalRotation j x) = x :=
  Submodule.reflection_reflection _ x

theorem normalRotation_coordinate (x : Space d) :
    H.normalRotation j x j = inner ℝ H.normal x := by
  have he := (H.normalRotation j).inner_map_map H.normal x
  rw [H.normalRotation_normal j] at he
  simpa [coordinateVector, EuclideanSpace.inner_single_left] using he

def flatten (x : Space d) : Space d :=
  H.normalRotation j (H.offset • H.normal - x)

def unflatten (x : Space d) : Space d :=
  H.offset • H.normal - H.normalRotation j x

@[simp] theorem unflatten_flatten (x : Space d) :
    H.unflatten j (H.flatten j x) = x := by
  simp [unflatten, flatten]

@[simp] theorem flatten_unflatten (x : Space d) :
    H.flatten j (H.unflatten j x) = x := by
  simp [unflatten, flatten]

@[simp] theorem flatten_coordinate (x : Space d) :
    H.flatten j x j = H.offset - inner ℝ H.normal x := by
  rw [flatten, H.normalRotation_coordinate]
  simp [inner_sub_right, inner_smul_right, H.normal_unit]

theorem flatten_isometry : Isometry (H.flatten j) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  simp only [flatten, (H.normalRotation j).dist_map, dist_sub_left]

theorem unflatten_isometry : Isometry (H.unflatten j) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  simp only [unflatten, dist_sub_left, (H.normalRotation j).dist_map]

def upperOpen : Opens (Space d) := ⟨{x | 0 < x j}, isOpen_lt continuous_const
  ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j))⟩

def nearOpen : Opens (Space d) := ⟨H.nearSide,
  isOpen_lt (continuous_const.inner continuous_id) continuous_const⟩

/-- The orthogonal affine chart sends the original near half-space onto the positive coordinate side. -/
def flattenChart : BiLipschitzChart (upperOpen j) H.nearOpen 1 1 where
  toFun := H.flatten j
  invFun := H.unflatten j
  mapsTo := by
    intro x hx
    change 0 < H.flatten j x j
    rw [H.flatten_coordinate]
    exact sub_pos.mpr hx
  inv_mapsTo := by
    intro x hx
    have he := H.flatten_coordinate j (H.unflatten j x)
    rw [H.flatten_unflatten] at he
    change inner ℝ H.normal (H.unflatten j x) < H.offset
    change 0 < x j at hx
    linarith
  left_inv := fun x _ => H.unflatten_flatten j x
  right_inv := fun x _ => H.flatten_unflatten j x
  lipschitz := (H.flatten_isometry j).lipschitzWith.lipschitzOnWith
  inv_lipschitz := (H.unflatten_isometry j).lipschitzWith.lipschitzOnWith

/-- The same chart on whole space. -/
def flattenWholeChart : BiLipschitzChart (⊤ : Opens (Space d)) ⊤ 1 1 where
  toFun := H.flatten j
  invFun := H.unflatten j
  mapsTo := fun _ _ => mem_univ _
  inv_mapsTo := fun _ _ => mem_univ _
  left_inv := fun x _ => H.unflatten_flatten j x
  right_inv := fun x _ => H.flatten_unflatten j x
  lipschitz := (H.flatten_isometry j).lipschitzWith.lipschitzOnWith
  inv_lipschitz := (H.unflatten_isometry j).lipschitzWith.lipschitzOnWith

/-- The inverse whole-space chart, used to first put a Sobolev function in flat coordinates. -/
def unflattenWholeChart : BiLipschitzChart (⊤ : Opens (Space d)) ⊤ 1 1 where
  toFun := H.unflatten j
  invFun := H.flatten j
  mapsTo := fun _ _ => mem_univ _
  inv_mapsTo := fun _ _ => mem_univ _
  left_inv := fun x _ => H.flatten_unflatten j x
  right_inv := fun x _ => H.unflatten_flatten j x
  lipschitz := (H.unflatten_isometry j).lipschitzWith.lipschitzOnWith
  inv_lipschitz := (H.flatten_isometry j).lipschitzWith.lipschitzOnWith

def coordinateReflection (y : Space d) : Space d :=
  y - (2 * y j) • coordinateVector d j

theorem coordinateReflection_formula (y : Space d) :
    coordinateReflection j y = WithLp.toLp 2
      (ExpandedFA.Sobolev.HalfSpace.reflect j (WithLp.ofLp y)) := by
  ext k
  by_cases hk : k = j
  · subst k
    simp [coordinateReflection, coordinateVector,
      ExpandedFA.Sobolev.HalfSpace.reflect]
    ring
  · simp [coordinateReflection, coordinateVector,
      ExpandedFA.Sobolev.HalfSpace.reflect, hk]

/-- Flattening conjugates reflection in the given affine plane to coordinate reflection. -/
theorem flatten_reflection (x : Space d) :
    H.flatten j (H.reflection x) = coordinateReflection j (H.flatten j x) := by
  rw [coordinateReflection, H.flatten_coordinate]
  rw [flatten, H.reflection_apply]
  rw [show H.offset • H.normal -
      (x + (2 * (H.offset - inner ℝ H.normal x)) • H.normal) =
      (H.offset • H.normal - x) - (2 * (H.offset - inner ℝ H.normal x)) • H.normal by abel]
  rw [map_sub, map_smul, H.normalRotation_normal]
  rfl

theorem unflatten_coordinateReflection (y : Space d) :
    H.unflatten j (coordinateReflection j y) = H.reflection (H.unflatten j y) := by
  have he := congrArg (H.unflatten j) (H.flatten_reflection j (H.unflatten j y))
  simpa only [H.unflatten_flatten, H.flatten_unflatten] using he.symm

theorem flatten_measurePreserving : MeasurePreserving (H.flatten j) volume volume := by
  have he : H.flatten j = H.normalRotation j ∘
      ((fun x : Space d => x + H.offset • H.normal) ∘ (LinearIsometryEquiv.neg ℝ)) := by
    funext x
    simp [flatten, sub_eq_add_neg, add_comm]
  rw [he]
  exact (H.normalRotation j).measurePreserving.comp
    ((measurePreserving_add_right volume (H.offset • H.normal)).comp
      (LinearIsometryEquiv.neg ℝ).measurePreserving)

theorem unflatten_measurePreserving : MeasurePreserving (H.unflatten j) volume volume := by
  have he : H.unflatten j = (fun x : Space d => x + H.offset • H.normal) ∘
      ((LinearIsometryEquiv.neg ℝ) ∘ H.normalRotation j) := by
    funext x
    simp [unflatten, sub_eq_add_neg, add_comm]
  rw [he]
  exact (measurePreserving_add_right volume (H.offset • H.normal)).comp
    ((LinearIsometryEquiv.neg ℝ).measurePreserving.comp (H.normalRotation j).measurePreserving)


end Flattening

/-- Even reflection from the near half-space belongs to the canonical Sobolev graph. -/

theorem even_extension (hd : 0 < d) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (g : WholeSobolev d p) :
    ∃ E : WholeSobolev d p, sobolevUnderlying E =ᵐ[volume]
      (fun x => if x ∈ H.nearSide then sobolevUnderlying g x
        else sobolevUnderlying g (H.reflection x)) := by
  let j : Fin d := ⟨0, hd⟩
  obtain ⟨T, hT, _, _⟩ := bilipschitz_sobolevPullback d hd ℝ ⊤ ⊤ 1 1
    (H.flattenWholeChart j).symm p
  have hu := hT g
  simp only [Opens.coe_top, Measure.restrict_univ, BiLipschitzChart.symm,
    flattenWholeChart] at hu
  obtain ⟨v, hv⟩ := P102.U4.PolarizationBridge.exists_coordinate_even_extension j (T g)
  obtain ⟨S, hS, _, _⟩ := bilipschitz_sobolevPullback d hd ℝ ⊤ ⊤ 1 1
    (H.flattenWholeChart j) p
  refine ⟨S v, ?_⟩
  have hs := hS v
  simp only [Opens.coe_top, Measure.restrict_univ, flattenWholeChart] at hs
  have huf := (H.flatten_measurePreserving j).quasiMeasurePreserving.ae hu
  have hufs := H.reflection_measurePreserving.quasiMeasurePreserving.ae huf
  have hvf := (H.flatten_measurePreserving j).quasiMeasurePreserving.ae hv
  filter_upwards [hs, huf, hufs, hvf] with x hs hu hus hv
  simp only [Function.comp_apply, H.unflatten_flatten] at hs hu hus
  rw [hs, hv]
  by_cases hx : x ∈ H.nearSide
  · have hpos : 0 < H.flatten j x j := by
      rw [H.flatten_coordinate]
      exact sub_pos.mpr hx
    simp only [hpos, ite_true, hx]
    exact hu
  · have hpos : ¬ 0 < H.flatten j x j := by
      rw [H.flatten_coordinate]
      exact fun h => hx (sub_pos.mp h)
    simp only [hpos, ite_false, hx]
    rw [← coordinateReflection_formula, ← H.flatten_reflection]
    exact hus

/-- The classical derivative of the affine reflection is its orthogonal part. -/
theorem reflection_hasFDerivAt (x : Space d) :
    HasFDerivAt H.reflection H.linearReflection.toContinuousLinearEquiv.toContinuousLinearMap x := by
  convert! H.linearReflection.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.add_const
      ((2 * H.offset) • H.normal) using 1

@[simp] theorem chartDerivative_reflection (x : Space d) :
    chartDerivative H.reflectionChart x =
      H.linearReflection.toContinuousLinearEquiv.toContinuousLinearMap :=
  (H.reflection_hasFDerivAt x).fderiv

/-- Orthogonality makes the two gradient lengths a permutation on every
reflected pair, including ties. This assertion itself needs no weak calculus. -/
theorem pair_gradient_observable (g : Space d → ℝ) (G : Space d → Space d)
    (F : ℝ → ℝ≥0∞) (x : Space d) :
    F ‖H.selectedGradient g G x‖ + F ‖H.selectedGradient g G (H.reflection x)‖ =
      F ‖G x‖ + F ‖G (H.reflection x)‖ := by
  by_cases he : inner ℝ H.normal x = H.offset
  · simp [selectedGradient, H.reflection_eq_self he]
  by_cases hx : x ∈ H.nearSide
  · have hs : H.reflection x ∉ H.nearSide := by
      change ¬ inner ℝ H.normal (H.reflection x) < H.offset
      rw [H.inner_reflection]
      change inner ℝ H.normal x < H.offset at hx
      linarith
    by_cases hv : g (H.reflection x) ≤ g x
    · simp [selectedGradient, hx, hs, hv]
    · simp [selectedGradient, hx, hs, hv, H.linearReflection.norm_map, add_comm]
  · have hs : H.reflection x ∈ H.nearSide := by
      change inner ℝ H.normal (H.reflection x) < H.offset
      rw [H.inner_reflection]
      change ¬ inner ℝ H.normal x < H.offset at hx
      have hgt := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm he)
      linarith
    by_cases hv : g x ≤ g (H.reflection x)
    · simp [selectedGradient, hx, hs, hv]
    · simp [selectedGradient, hx, hs, hv, H.linearReflection.norm_map, add_comm]

/-- The orthogonal part of a plane reflection is self-adjoint. -/
theorem linearReflection_inner (x y : Space d) :
    inner ℝ (H.linearReflection x) y = inner ℝ x (H.linearReflection y) := by
  simp only [H.linearReflection_apply, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, conj_trivial]
  rw [real_inner_comm x H.normal]
  ring

/-- The transpose coordinate chain rule equals the reflected Euclidean vector. -/
theorem reflection_gradient_coordinates (x v : Space d) (j : Fin d) :
    (∑ i : Fin d, (chartDerivative H.reflectionChart x (coordinateVector d j) i) * v i) =
      H.linearReflection v j := by
  rw [H.chartDerivative_reflection]
  have he : (∑ i : Fin d, H.linearReflection (coordinateVector d j) i * v i) =
      inner ℝ (H.linearReflection (coordinateVector d j)) v := by
    simp [PiLp.inner_apply, mul_comm]
  convert! he.trans ?_ using 1
  rw [H.linearReflection_inner]
  simp [coordinateVector, EuclideanSpace.inner_single_left]

/-- Reflection transports the actual weak gradient by the orthogonal linear
reflection. In particular this entails exact preservation of gradient length. -/
theorem reflected_sobolev_gradient (hd : 0 < d) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (g : WholeSobolev d p) :
    ∃ v : WholeSobolev d p,
      (sobolevUnderlying v =ᵐ[volume] sobolevUnderlying g ∘ H.reflection) ∧
      gradient v =ᵐ[volume] (fun x => H.linearReflection (gradient g (H.reflection x))) := by
  obtain ⟨v, hv, hDv⟩ := H.reflected_sobolev hd p g
  refine ⟨v, hv, ?_⟩
  filter_upwards [ae_all_iff.mpr hDv] with x hx
  ext j
  exact (hx j).trans (H.reflection_gradient_coordinates x (gradient g (H.reflection x)) j)

/-- Squared distances increase on the side containing the origin. -/
theorem reflection_norm_sq (x : Space d) :
    ‖H.reflection x‖ ^ 2 - ‖x‖ ^ 2 =
      4 * H.offset * (H.offset - inner ℝ H.normal x) := by
  rw [reflection_apply, norm_add_sq_real, real_inner_smul_right,
    norm_smul, H.normal_unit, mul_one, Real.norm_eq_abs, sq_abs]
  rw [real_inner_comm x H.normal]
  ring

theorem norm_le_reflection {x : Space d} (hx : x ∈ H.nearSide) :
    ‖x‖ ≤ ‖H.reflection x‖ := by
  have ht : 0 < H.offset - inner ℝ H.normal x := sub_pos.mpr hx
  have he := H.reflection_norm_sq x
  have hp := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) H.offset_pos.le) ht.le
  nlinarith [norm_nonneg x, norm_nonneg (H.reflection x)]

/-- Reflection exchanges the sides; on the fixed plane the two values coincide. -/
theorem pair_values (g : Space d → ℝ) (x : Space d) :
    (H.polarize g x = max (g x) (g (H.reflection x)) ∧
      H.polarize g (H.reflection x) = min (g x) (g (H.reflection x))) ∨
    (H.polarize g x = min (g x) (g (H.reflection x)) ∧
      H.polarize g (H.reflection x) = max (g x) (g (H.reflection x))) := by
  change ((if inner ℝ H.normal x < H.offset then _ else _) = _ ∧
      (if inner ℝ H.normal (H.reflection x) < H.offset then _ else _) = _) ∨
    ((if inner ℝ H.normal x < H.offset then _ else _) = _ ∧
      (if inner ℝ H.normal (H.reflection x) < H.offset then _ else _) = _)
  by_cases hx : inner ℝ H.normal x < H.offset
  · have hs : ¬ inner ℝ H.normal (H.reflection x) < H.offset := by
      rw [inner_reflection]; linarith
    left
    simp only [ite_eq_left hx, ite_eq_right hs, reflection_reflection, min_comm, and_self]
  · by_cases he : inner ℝ H.normal x = H.offset
    · have hs := H.reflection_eq_self he
      simp only [hs, min_self, max_self, ite_self, and_self, or_self]
    · have hgt : H.offset < inner ℝ H.normal x := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm he)
      have hs : inner ℝ H.normal (H.reflection x) < H.offset := by
        rw [inner_reflection]; linarith
      right
      simp only [ite_eq_right hx, ite_eq_left hs, reflection_reflection, max_comm, and_self]

/-- Every observable is merely permuted on each reflected pair. -/
theorem pair_observable (g : Space d → ℝ) (F : ℝ → ℝ≥0∞) (x : Space d) :
    F (H.polarize g x) + F (H.polarize g (H.reflection x)) =
      F (g x) + F (g (H.reflection x)) := by
  rcases H.pair_values g x with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂]
  all_goals
    rcases le_total (g x) (g (H.reflection x)) with h | h
    all_goals simp [h, add_comm]

theorem measurable_nearSide : MeasurableSet H.nearSide :=
  (isOpen_lt (continuous_const.inner continuous_id :
    Continuous (fun x : Space d => inner ℝ H.normal x)) continuous_const).measurableSet

theorem measurable_polarize {g : Space d → ℝ} (hg : Measurable g) :
    Measurable (H.polarize g) :=
  (hg.max (hg.comp H.reflection_continuous.measurable)).ite H.measurable_nearSide
    (hg.min (hg.comp H.reflection_continuous.measurable))

/-- The selected gradient has measurable representatives whenever its inputs do. -/
theorem measurable_selectedGradient {g : Space d → ℝ} {G : Space d → Space d}
    (hg : Measurable g) (hG : Measurable G) : Measurable (H.selectedGradient g G) := by
  have hc : MeasurableSet {x | if x ∈ H.nearSide then
      g (H.reflection x) ≤ g x else g x ≤ g (H.reflection x)} := by
    convert MeasurableSet.ite H.measurable_nearSide
      (measurableSet_le (hg.comp H.reflection_continuous.measurable) hg)
      (measurableSet_le hg (hg.comp H.reflection_continuous.measurable)) using 1
    ext x
    by_cases hx : x ∈ H.nearSide <;> simp [Set.ite, hx]
  exact hG.ite hc (H.linearReflection.continuous.measurable.comp
    (hG.comp H.reflection_continuous.measurable))

/-- Pairing proves preservation of all nonnegative measurable observables,
including ones with infinite integral. No cancellation of an infinite summand
is used: multiplication by two is injective on ENNReal. -/
theorem lintegral_observable {g : Space d → ℝ} (hg : Measurable g)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x, F (H.polarize g x) ∂volume) = ∫⁻ x, F (g x) ∂volume := by
  have hp : Measurable (fun x => F (H.polarize g x)) := hF.comp (H.measurable_polarize hg)
  have hq : Measurable (fun x => F (g x)) := hF.comp hg
  have he := congrArg (fun f : Space d → ℝ≥0∞ => ∫⁻ x, f x ∂volume)
    (funext (H.pair_observable g F))
  rw [lintegral_add_left hp, lintegral_add_left hq,
    H.reflection_measurePreserving.lintegral_comp hp,
    H.reflection_measurePreserving.lintegral_comp hq] at he
  apply (ENNReal.mul_left_inj (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mp
  simpa only [mul_two] using he

/-- Every measurable observable of gradient length is preserved by the
selected vector field, including observables with infinite integral. -/
theorem lintegral_selectedGradient {g : Space d → ℝ} {G : Space d → Space d}
    (hg : Measurable g) (hG : Measurable G) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x, F ‖H.selectedGradient g G x‖ ∂volume) = ∫⁻ x, F ‖G x‖ ∂volume := by
  have hp : Measurable (fun x => F ‖H.selectedGradient g G x‖) :=
    hF.comp (H.measurable_selectedGradient hg hG).norm
  have hq : Measurable (fun x => F ‖G x‖) := hF.comp hG.norm
  have he := congrArg (fun f : Space d → ℝ≥0∞ => ∫⁻ x, f x ∂volume)
    (funext (H.pair_gradient_observable g G F))
  rw [lintegral_add_left hp, lintegral_add_left hq,
    H.reflection_measurePreserving.lintegral_comp hp,
    H.reflection_measurePreserving.lintegral_comp hq] at he
  apply (ENNReal.mul_left_inj (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mp
  simpa only [mul_two] using he

/-- The exact Euclidean Lp energy equality for the selected gradient field. -/
theorem eLpNorm_selectedGradient {g : Space d → ℝ} {G : Space d → Space d}
    (hg : Measurable g) (hG : Measurable G) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp_top : p ≠ ∞) :
    eLpNorm (H.selectedGradient g G) p volume = eLpNorm G p volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top
      (H.measurable_selectedGradient hg hG).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hG.aestronglyMeasurable]
  congr 1
  simp_rw [← ofReal_norm]
  exact H.lintegral_selectedGradient hg hG (ENNReal.measurable_ofReal.pow_const p.toReal)

/-- Every superlevel measure is preserved, with no exception for levels having
positive-measure equality sets. -/
theorem superlevel_measure {g : Space d → ℝ} (hg : Measurable g) (s : ℝ) :
    volume {x | s < H.polarize g x} = volume {x | s < g x} := by
  let F : ℝ → ℝ≥0∞ := (Ioi s).indicator (fun _ => 1)
  have hm : Measurable F := measurable_const.indicator measurableSet_Ioi
  have he := H.lintegral_observable hg hm
  have hp : MeasurableSet {x | s < H.polarize g x} :=
    measurableSet_lt measurable_const (H.measurable_polarize hg)
  have hq : MeasurableSet {x | s < g x} := measurableSet_lt measurable_const hg
  change (∫⁻ x, {x | s < H.polarize g x}.indicator (fun _ => 1) x ∂volume) =
    ∫⁻ x, {x | s < g x}.indicator (fun _ => 1) x ∂volume at he
  simpa only [lintegral_indicator_const hp, lintegral_indicator_const hq, one_mul] using he

/-- The function norm is preserved in every nonzero finite exponent. -/
theorem eLpNorm_polarize {g : Space d → ℝ} (hg : Measurable g)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp_top : p ≠ ∞) :
    eLpNorm (H.polarize g) p volume = eLpNorm g p volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top
      (H.measurable_polarize hg).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hg.aestronglyMeasurable,
    H.lintegral_observable hg (measurable_enorm.pow_const p.toReal)]

/-- Nonnegativity is inherited on each reflected pair, also for a.e. data. -/
theorem nonnegative_ae {g : Space d → ℝ} (hg : ∀ᵐ x ∂volume, 0 ≤ g x) :
    ∀ᵐ x ∂volume, 0 ≤ H.polarize g x := by
  filter_upwards [hg, H.reflection_measurePreserving.quasiMeasurePreserving.ae hg] with x hx hs
  dsimp [polarize]
  split_ifs
  · exact le_max_of_le_left hx
  · exact le_min hx hs

/-- Moving the larger value toward the origin preserves the original ball
support. Nonnegativity is essential on the outer side. -/
theorem supported_ae {g : Space d → ℝ} {R : ℝ}
    (hg : ∀ᵐ x ∂volume, 0 ≤ g x)
    (hz : ∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : Space d) R → g x = 0) :
    ∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : Space d) R → H.polarize g x = 0 := by
  filter_upwards [hz, H.reflection_measurePreserving.quasiMeasurePreserving.ae hz,
    H.reflection_measurePreserving.quasiMeasurePreserving.ae hg] with x hx hs hpos hout
  have hx0 := hx hout
  by_cases hn : x ∈ H.nearSide
  · have hout' : H.reflection x ∉ Metric.closedBall (0 : Space d) R := by
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hout ⊢
      exact hout.trans_le (H.norm_le_reflection hn)
    simp only [polarize, ite_eq_left hn, hx0, hs hout', max_self]
  · simp only [polarize, ite_eq_right hn, hx0, min_eq_left hpos]

/-- Lp membership of the explicit polarization precedes its weak-derivative
construction; it follows from the already proved distribution of values. -/
theorem memLp_polarize {g : Space d → ℝ} (hg : Measurable g)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp_top : p ≠ ∞) (hgp : MemLp g p volume) :
    MemLp (H.polarize g) p volume := by
  rw [memLp_iff, H.eLpNorm_polarize hg hp0 hp_top]
  exact hgp.eLpNorm_lt_top

/-- Once a Sobolev representative with the specified weak gradient has been
constructed, all value, support and sharp gradient conclusions follow.
This is an assembly lemma; it does not assert that the representative exists. -/
theorem properties_of_gradient_realization {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp0 : p ≠ 0) (hp_top : p ≠ ∞) {R : ℝ} (g w : WholeSobolev d p)
    (hg : SupportedNonnegative R g)
    (hw : sobolevUnderlying w =ᵐ[volume] H.polarize (sobolevUnderlying g))
    (hDw : gradient w =ᵐ[volume] H.selectedGradient (sobolevUnderlying g) (gradient g)) :
    SupportedNonnegative R w ∧
      (∀ s : ℝ, 0 < s → volume {x | s < sobolevUnderlying w x} =
        volume {x | s < sobolevUnderlying g x}) ∧
      eLpNorm (sobolevUnderlying w) p volume = eLpNorm (sobolevUnderlying g) p volume ∧
      eLpNorm (gradient w) p volume = eLpNorm (gradient g) p volume := by
  have hm : Measurable (sobolevUnderlying g) := (Lp.stronglyMeasurable _).measurable
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · filter_upwards [hw, H.nonnegative_ae hg.1] with x hx hp
    rwa [hx]
  · filter_upwards [hw, H.supported_ae hg.1 hg.2] with x hx hp
    rwa [hx]
  · intro s _hs
    calc
      volume {x | s < sobolevUnderlying w x} =
          volume {x | s < H.polarize (sobolevUnderlying g) x} := by
        apply measure_congr
        filter_upwards [hw] with x hx
        simp only [hx]
      _ = _ := H.superlevel_measure hm s
  · exact (eLpNorm_congr_ae hw).trans (H.eLpNorm_polarize hm hp0 hp_top)
  · exact (eLpNorm_congr_ae hDw).trans
      (H.eLpNorm_selectedGradient hm (measurable_gradient g) hp0 hp_top)


/-- The actual weak gradient of any global polarization representative is the selected vector field. -/
theorem gradient_of_realization (hd : 0 < d) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (g w : WholeSobolev d p)
    (hw : sobolevUnderlying w =ᵐ[volume] H.polarize (sobolevUnderlying g)) :
    gradient w =ᵐ[volume] H.selectedGradient (sobolevUnderlying g) (gradient g) := by
  obtain ⟨v, hv, hDv⟩ := H.reflected_sobolev_gradient hd p g
  obtain ⟨a, b, ha, hb, hDa, hDb⟩ := sobolev_max_min_gradient g v
  let U : Opens (Space d) := ⟨H.nearSide,
    isOpen_lt (continuous_const.inner continuous_id) continuous_const⟩
  let V : Opens (Space d) := ⟨{x | H.offset < inner ℝ H.normal x},
    isOpen_lt continuous_const (continuous_const.inner continuous_id)⟩
  have hwa : sobolevUnderlying w =ᵐ[volume.restrict (U : Set (Space d))]
      sobolevUnderlying a := by
    filter_upwards [ae_restrict_of_ae hw, ae_restrict_of_ae ha,
      ae_restrict_of_ae hv, ae_restrict_mem U.isOpen.measurableSet] with x hw ha hv hx
    rw [hw, ha, hv]
    exact ite_eq_left hx
  have hwb : sobolevUnderlying w =ᵐ[volume.restrict (V : Set (Space d))]
      sobolevUnderlying b := by
    filter_upwards [ae_restrict_of_ae hw, ae_restrict_of_ae hb,
      ae_restrict_of_ae hv, ae_restrict_mem V.isOpen.measurableSet] with x hw hb hv hx
    rw [hw, hb, hv]
    apply ite_eq_right
    change H.offset < inner ℝ H.normal x at hx
    exact not_lt.mpr hx.le
  have hDU := (ae_restrict_iff' U.isOpen.measurableSet).mp (gradient_locality w a U hwa)
  have hDV := (ae_restrict_iff' V.isOpen.measurableSet).mp (gradient_locality w b V hwb)
  have hn : ∀ᵐ x ∂volume, inner ℝ H.normal x ≠ H.offset := by
    apply ae_iff.mpr
    simpa only [not_not] using H.boundary_null
  filter_upwards [hDU, hDV, hDa, hDb, hv, hDv, hn] with x hU hV hDa hDb hv hDv hn
  by_cases hx : x ∈ H.nearSide
  · rw [hU hx, hDa, hv, hDv]
    simp only [selectedGradient, hx, ite_true]
    rfl
  · have hxV : x ∈ V := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hn)
    rw [hV hxV, hDb, hv, hDv]
    simp only [selectedGradient, hx, ite_false]
    rfl

/-- Even extension and positive-part calculus give a genuine global polarization. -/
theorem polarization_of_even_extension (hd : 0 < d) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (g E : WholeSobolev d p)
    (hE : sobolevUnderlying E =ᵐ[volume] (fun x =>
      if x ∈ H.nearSide then sobolevUnderlying g x else sobolevUnderlying g (H.reflection x))) :
    ∃ w : WholeSobolev d p,
      sobolevUnderlying w =ᵐ[volume] H.polarize (sobolevUnderlying g) := by
  obtain ⟨q, hq, _⟩ := lower_truncation_rule ⊤ p (g - E) 0 (Or.inl le_rfl)
  simp only [Opens.coe_top, Measure.restrict_univ] at hq
  obtain ⟨qr, hqr, _⟩ := H.reflected_sobolev hd p q
  have hq' : sobolevUnderlying q =ᵐ[volume] (fun x =>
      max 0 (sobolevUnderlying g x - (if x ∈ H.nearSide then sobolevUnderlying g x
        else sobolevUnderlying g (H.reflection x)))) := by
    filter_upwards [hq, underlying_sub_ae g E, hE] with x hq hs he
    rw [hq, hs, he]
  refine ⟨(g + qr) - q, ?_⟩
  filter_upwards [underlying_sub_ae (g + qr) q, underlying_add_ae g qr, hqr,
    hq', H.reflection_measurePreserving.quasiMeasurePreserving.ae hq'] with x hw ha hr hq hs
  rw [hw, ha, hr, hq]
  simp only [Function.comp_apply]
  rw [hs, H.reflection_reflection]
  by_cases hx : x ∈ H.nearSide
  · have hs : H.reflection x ∉ H.nearSide := by
      change ¬ inner ℝ H.normal (H.reflection x) < H.offset
      rw [H.inner_reflection]
      change inner ℝ H.normal x < H.offset at hx
      linarith
    simp only [polarize, hx, hs, ite_true, ite_false, sub_self, max_self, sub_zero]
    rcases le_total (sobolevUnderlying g x) (sobolevUnderlying g (H.reflection x)) with h | h
    · rw [max_eq_right (sub_nonneg.mpr h), max_eq_right h]
      ring
    · rw [max_eq_left (sub_nonpos.mpr h), max_eq_left h, add_zero]
  · by_cases he : inner ℝ H.normal x = H.offset
    · simp [polarize, H.reflection_eq_self he]
    · have hs : H.reflection x ∈ H.nearSide := by
        change inner ℝ H.normal (H.reflection x) < H.offset
        rw [H.inner_reflection]
        change ¬ inner ℝ H.normal x < H.offset at hx
        have hgt := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm he)
        linarith
      simp only [polarize, hx, hs, ite_true, ite_false, sub_self, max_self, add_zero]
      rcases le_total (sobolevUnderlying g x) (sobolevUnderlying g (H.reflection x)) with h | h
      · rw [max_eq_left (sub_nonpos.mpr h), min_eq_left h, sub_zero]
      · rw [max_eq_right (sub_nonneg.mpr h), min_eq_right h]
        ring

/-- The max and min maps are both contractions in the maximum norm of a pair. -/
theorem abs_polarize_sub_le (g h : Space d → ℝ) (x : Space d) :
    |H.polarize g x - H.polarize h x| ≤
      max |g x - h x| |g (H.reflection x) - h (H.reflection x)| := by
  dsimp [polarize]
  split_ifs
  · exact abs_max_sub_max_le_max _ _ _ _
  · exact abs_min_sub_min_le_max _ _ _ _

/-- A pointwise p-energy estimate with the sharp factor two after integration. -/
theorem enorm_rpow_sub_le (g h : Space d → ℝ) (x : Space d) {q : ℝ} (hq : 0 ≤ q) :
    ‖H.polarize g x - H.polarize h x‖ₑ ^ q ≤
      ‖g x - h x‖ₑ ^ q + ‖g (H.reflection x) - h (H.reflection x)‖ₑ ^ q := by
  have he : ‖H.polarize g x - H.polarize h x‖ₑ ≤
      max ‖g x - h x‖ₑ ‖g (H.reflection x) - h (H.reflection x)‖ₑ := by
    simp only [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_max]
    exact ENNReal.ofReal_le_ofReal (H.abs_polarize_sub_le g h x)
  exact (ENNReal.rpow_le_rpow he hq).trans (by
    rw [ENNReal.max_rpow hq]
    exact max_le (le_self_add) (le_add_self))

/-- The p-th-power continuity estimate for arbitrary measurable real functions.
In particular it applies to the Sobolev class in the independent specification. -/
theorem continuity_power {g h : Space d → ℝ} (hg : Measurable g) (hh : Measurable h)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp_top : p ≠ ∞) :
    (eLpNorm (fun x => H.polarize g x - H.polarize h x) p volume) ^ p.toReal ≤
      2 * (eLpNorm (fun x => g x - h x) p volume) ^ p.toReal := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hm : Measurable (fun x => ‖g x - h x‖ₑ ^ p.toReal) :=
    (hg.sub hh).enorm.pow_const p.toReal
  have hn (f : Space d → ℝ) (hf : Measurable f) :
      (eLpNorm f p volume) ^ p.toReal = ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hf.aestronglyMeasurable,
      ← ENNReal.rpow_mul, div_mul_cancel₀ _ hpr.ne', ENNReal.rpow_one]
  rw [hn (fun x => H.polarize g x - H.polarize h x)
      ((H.measurable_polarize hg).sub (H.measurable_polarize hh)),
    hn (fun x => g x - h x) (hg.sub hh)]
  calc
    _ ≤ ∫⁻ x, ‖g x - h x‖ₑ ^ p.toReal +
        ‖g (H.reflection x) - h (H.reflection x)‖ₑ ^ p.toReal ∂volume :=
      lintegral_mono (fun x => H.enorm_rpow_sub_le g h x hpr.le)
    _ = _ := by
      rw [lintegral_add_left hm,
        H.reflection_measurePreserving.lintegral_comp hm,
        two_mul]

end Halfspace
end Polarization
/-- Polarization has all the stated Sobolev, distributional, support, and norm properties. -/
theorem polarization_properties : PolarizationExpected.Properties := by
  intro d hd p _hp hp hp_top H R _hR g hg
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp)
  obtain ⟨E, hE⟩ := H.even_extension hd p g
  obtain ⟨w, hw⟩ := H.polarization_of_even_extension hd g E hE
  have hDw := H.gradient_of_realization hd g w hw
  obtain ⟨hsupp, hsuper, hnorm, hgrad⟩ :=
    H.properties_of_gradient_realization hp0 hp_top g w hg hw hDw
  exact ⟨w, hw, hsupp, hsuper, hnorm, hgrad.le⟩

/-- The original closed continuity target. -/
theorem polarization_continuity :
    PolarizationExpected.Continuity := by
  intro d _hd p _hp hp hp_top H R _hR g h _hg _hh
  exact H.continuity_power (Lp.stronglyMeasurable (sobolevUnderlying g)).measurable
    (Lp.stronglyMeasurable (sobolevUnderlying h)).measurable
    (ne_of_gt (lt_trans (by norm_num) hp)) hp_top

end P102.Sobolev
