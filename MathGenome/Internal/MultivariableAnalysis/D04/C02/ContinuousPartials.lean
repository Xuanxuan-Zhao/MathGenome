import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeBridge
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.ContinuousPartials
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Filter Topology Asymptotics
open scoped BigOperators
open private isLittleO_sub_sub_fderiv from Mathlib.Analysis.Calculus.FDeriv.Partial
namespace D04

/-- The linear map whose columns are the first coordinate partials.
Existence of those partials is asserted separately in the theorem. -/
def partialDerivativeMap : Specs.D04.C02.ContinuousPartials.partialDerivativeMapType :=
  @Specs.D04.C02.ContinuousPartials.partialDerivativeMapValue

theorem partialDerivativeMap_apply {n m : ℕ} (f : E n → E m) (a h : E n) :
    partialDerivativeMap f a h = ∑ j : Fin n, h j • partialDerivative f a j := by
  change (standardBasis n).constr ℝ (partialDerivative f a) h = _
  simp [Module.Basis.constr_apply_fintype, standardBasis, EuclideanSpace.basisFun_repr]

theorem partialDerivativeMap_column {n m : ℕ} (f : E n → E m) (a : E n) (j : Fin n) :
    partialDerivativeMap f a (standardBasis n j) = partialDerivative f a j := by
  change (standardBasis n).constr ℝ (partialDerivative f a) (standardBasis n j) = _
  exact (standardBasis n).constr_basis ℝ _ j

/-- Prefixes of the coordinate increment used in the telescoping argument. -/
private def coordinatePrefix {n : ℕ} (k : ℕ) (h : E n) : E n :=
  ∑ i : Fin n, if i.val < k then h i • standardBasis n i else 0

private theorem coordinatePrefix_zero {n : ℕ} (h : E n) : coordinatePrefix 0 h = 0 := by
  simp [coordinatePrefix]

private theorem coordinatePrefix_all {n : ℕ} (h : E n) : coordinatePrefix n h = h := by
  simp only [coordinatePrefix, Fin.is_lt, ite_true]
  simpa [standardBasis, EuclideanSpace.basisFun_repr] using (standardBasis n).sum_repr h

private theorem coordinatePrefix_succ {n : ℕ} (j : Fin n) (h : E n) :
    coordinatePrefix (j.val + 1) h = coordinatePrefix j.val h + h j • standardBasis n j := by
  classical
  have he (i : Fin n) :
      (if i.val < j.val + 1 then h i • standardBasis n i else 0) =
        (if i.val < j.val then h i • standardBasis n i else 0) +
        (if i = j then h j • standardBasis n j else 0) := by
    by_cases hij : i = j
    · subst i; simp
    · have hv : i.val ≠ j.val := fun he => hij (Fin.ext he)
      by_cases hi : i.val < j.val <;> simp [hij, hi, show (i.val < j.val + 1) ↔ i.val < j.val by omega]
  simp_rw [coordinatePrefix, he, Finset.sum_add_distrib]
  simp

private theorem coordinatePrefix_continuous {n : ℕ} (k : ℕ) :
    Continuous (coordinatePrefix (n := n) k) := by
  classical
  apply continuous_finsetSum
  intro i _
  split_ifs
  · exact (PiLp.continuous_apply 2 _ i).smul continuous_const
  · exact continuous_const

/-- Move the basepoint of a directional quotient to a parameter on its affine line. -/
private theorem hasDerivAt_coordinateLine {n m : ℕ} (f : E n → E m)
    (b : E n) (j : Fin n) (t : ℝ) (d : E m)
    (hd : HasPartialDerivative f (b + t • standardBasis n j) j d) :
    HasDerivAt (fun s : ℝ => f (b + s • standardBasis n j)) d t := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  change Tendsto (fun s : ℝ => s⁻¹ •
    (f (b + (t + s) • standardBasis n j) - f (b + t • standardBasis n j))) _ _
  change Tendsto (fun s : ℝ => s⁻¹ •
    (f ((b + t • standardBasis n j) + s • standardBasis n j) -
      f (b + t • standardBasis n j))) _ _ at hd
  simpa only [add_smul, add_assoc] using hd

/-- Each coordinate error is small compared to the full increment. The only
continuity used is the continuity of this partial at a. -/
private theorem coordinate_error_isLittleO {n m : ℕ} (f : E n → E m) (a : E n)
    (hd : ∀ᶠ x in 𝓝 a, ∀ j : Fin n, ∃ d, HasPartialDerivative f x j d)
    (hc : ∀ j : Fin n, ContinuousAt (fun x => partialDerivative f x j) a)
    (j : Fin n) :
    (fun x => f (a + coordinatePrefix (j.val + 1) (x - a)) -
      f (a + coordinatePrefix j.val (x - a)) - (x - a) j • partialDerivative f a j)
      =o[𝓝 a] (fun x => x - a) := by
  let p : E n × ℝ → E n := fun q =>
    a + coordinatePrefix j.val (q.1 - a) + q.2 • standardBasis n j
  have hp : Continuous p :=
    (continuous_const.add ((coordinatePrefix_continuous j.val).comp
      (continuous_fst.sub continuous_const))).add (continuous_snd.smul continuous_const)
  have hpa : p (a, 0) = a := by simp [p, coordinatePrefix]
  have ht : Tendsto p (𝓝 a ×ˢ 𝓝 (0 : ℝ)) (𝓝 a) := by
    have h := hp.tendsto (a, 0)
    rwa [hpa, nhds_prod_eq] at h
  have hder : ∀ᶠ q : E n × ℝ in 𝓝 a ×ˢ 𝓝[Set.univ] (0 : ℝ),
      HasFDerivWithinAt
        (fun t : ℝ => f (a + coordinatePrefix j.val (q.1 - a) + t • standardBasis n j))
        (ContinuousLinearMap.toSpanSingleton ℝ (partialDerivative f (p q) j)) Set.univ q.2 := by
    simp only [nhdsWithin_univ]
    filter_upwards [ht.eventually hd] with q hq
    obtain ⟨d, hq⟩ := hq j
    have he : partialDerivative f (p q) j = d :=
      directionalDerivative_eq f (p q) (standardBasis n j) d hq
    rw [he]
    exact (hasDerivAt_coordinateLine f _ j q.2 d hq).hasFDerivAt.hasFDerivWithinAt
  have hcont : Tendsto
      (fun q : E n × ℝ => ContinuousLinearMap.toSpanSingleton ℝ (partialDerivative f (p q) j))
      (𝓝 a ×ˢ 𝓝[Set.univ] (0 : ℝ))
      (𝓝 (ContinuousLinearMap.toSpanSingleton ℝ (partialDerivative f a j))) := by
    simp only [nhdsWithin_univ]
    exact (ContinuousLinearMap.toSpanSingletonLIE ℝ (E m)).continuous.continuousAt.tendsto.comp
      ((hc j).tendsto.comp ht)
  have hv : Tendsto (fun x : E n => (x - a) j) (𝓝 a) (𝓝 (0 : ℝ)) := by
    have hv' : Continuous (fun x : E n => (x - a) j) :=
      (PiLp.continuous_apply 2 _ j).comp (continuous_id.sub continuous_const)
    simpa using hv'.tendsto a
  have h := isLittleO_sub_sub_fderiv (𝕜 := ℝ)
    (f := fun x t => f (a + coordinatePrefix j.val (x - a) + t • standardBasis n j))
    (f' := fun x t => ContinuousLinearMap.toSpanSingleton ℝ
      (partialDerivative f (a + coordinatePrefix j.val (x - a) + t • standardBasis n j) j))
    hv tendsto_const_nhds Set.univ (by simp) hder hcont
  have hbig : (fun x : E n => (x - a) j - (0 : ℝ)) =O[𝓝 a] (fun x => x - a) := by
    apply isBigO_of_le
    intro x
    simpa only [sub_zero] using PiLp.norm_apply_le (x - a) j
  convert h.trans_isBigO hbig using 1
  ext x
  simp only [coordinatePrefix_succ, add_assoc, zero_smul, add_zero, sub_zero,
    ContinuousLinearMap.toSpanSingleton_apply]

/-- The coordinate telescope also works for the empty family of coordinates. -/
private theorem coordinate_telescope {n m : ℕ} (f : E n → E m) (a x : E n) :
    (∑ j : Fin n, (f (a + coordinatePrefix (j.val + 1) (x - a)) -
      f (a + coordinatePrefix j.val (x - a)))) = f x - f a := by
  have h := Finset.sum_range_sub (fun k => f (a + coordinatePrefix k (x - a))) n
  rw [Finset.sum_range] at h
  simpa only [coordinatePrefix_all, coordinatePrefix_zero, add_sub_cancel, add_zero] using h

theorem continuous_partials_hasTotalDerivative {n m : ℕ}
    (U : Set (E n)) (f : E n → E m) (a : E n) (hU : IsOpen U) (ha : a ∈ U)
    (hd : ∀ᶠ x in 𝓝 a, ∀ j : Fin n, ∃ d, HasPartialDerivative f x j d)
    (hc : ∀ j : Fin n, ContinuousWithinAt (fun x => partialDerivative f x j) U a) :
    HasTotalDerivative U f (partialDerivativeMap f a) a := by
  apply (hasTotalDerivative_iff_hasFDerivAt U f _ a hU ha).mpr
  rw [hasFDerivAt_iff_isLittleO]
  have h := IsLittleO.sum (s := Finset.univ) (fun j _ =>
    coordinate_error_isLittleO f a hd (fun i => (hc i).continuousAt (hU.mem_nhds ha)) j)
  have he : (fun x => ∑ j : Fin n,
      (f (a + coordinatePrefix (j.val + 1) (x - a)) -
        f (a + coordinatePrefix j.val (x - a)) - (x - a) j • partialDerivative f a j)) =
      (fun x => f x - f a - partialDerivativeMap f a (x - a)) := by
    funext x
    rw [Finset.sum_sub_distrib, coordinate_telescope, partialDerivativeMap_apply]
  simpa only [Finset.sum_fn, he] using h

/-- The global conclusion uses the operator-norm/coordinate bridge, so it
asserts continuity of the total derivative in its actual operator norm. -/
theorem continuous_partials_continuous_totalDerivative {n m : ℕ}
    (U : Set (E n)) (f : E n → E m) (hU : IsOpen U)
    (hd : ∀ x ∈ U, ∀ j : Fin n, ∃ d, HasPartialDerivative f x j d)
    (hc : ∀ j : Fin n, ContinuousOn (fun x => partialDerivative f x j) U) :
    TotalDifferentiableOn U f ∧ ContinuousOn (totalDerivative f) U := by
  have hder (a : E n) (ha : a ∈ U) :
      HasTotalDerivative U f (partialDerivativeMap f a) a :=
    continuous_partials_hasTotalDerivative U f a hU ha
      (Filter.eventually_of_mem (hU.mem_nhds ha) hd) (fun j => hc j a ha)
  refine ⟨fun a ha => ⟨partialDerivativeMap f a, hder a ha⟩, ?_⟩
  have hmap : ContinuousOn (partialDerivativeMap f) U := by
    intro a ha
    change Tendsto (partialDerivativeMap f) (𝓝[U] a) (𝓝 (partialDerivativeMap f a))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have ht := (linear_operator_tendsto (𝓝[U] a)
      (fun x => (partialDerivativeMap f x).toLinearMap)
      (partialDerivativeMap f a).toLinearMap).mpr (fun i j => by
        simp only [matrixOfLinearMap_apply]
        change Tendsto (fun x => partialDerivativeMap f x (standardBasis n j) i)
          (𝓝[U] a) (𝓝 (partialDerivativeMap f a (standardBasis n j) i))
        simp only [partialDerivativeMap_column]
        exact (PiLp.continuous_apply 2 _ i).continuousAt.tendsto.comp (hc j a ha))
    have he (x : E n) :
        linearOperatorNorm ((partialDerivativeMap f x).toLinearMap -
          (partialDerivativeMap f a).toLinearMap) = ‖partialDerivativeMap f x - partialDerivativeMap f a‖ :=
      linearOperatorNorm_eq_standard (partialDerivativeMap f x - partialDerivativeMap f a)
    simpa only [he] using ht
  exact hmap.congr (fun a ha => totalDerivative_eq U f _ a (hder a ha))

end D04
