import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.ConditionalOrder
import MathGenome.Internal.MultivariableAnalysis.D04.C06.DarbouxFubini
import MathGenome.Internal.MultivariableAnalysis.D04.C06.SlicingAndMoments
import MathGenome.Internal.MultivariableAnalysis.D04.C06.AbsoluteConvergence
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.FtcSecond
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter Topology
open scoped Classical
namespace D04.ConditionalOrder
open Darboux JordanRegions ImproperExhaustions
open Specs.D04.C06.ConditionalOrder.Model

lemma kernel_antisymm (x y : ℝ) : kernel y x = -kernel x y := by
  unfold kernel
  rw [add_comm (y^2), ← neg_div]
  congr 1
  ring

lemma denominator_pos {x y : ℝ} (hx : 0 < x) : 0 < x^2+y^2 := by
  nlinarith [sq_nonneg y, sq_pos_of_pos hx]

lemma continuousOn_integrand {S : Set (E 2)} (hS : ∀ z ∈ S, 0 < z 0) :
    ContinuousOn integrand S := by
  apply ContinuousOn.div
  · exact ((PiLp.continuous_apply 2 _ (0 : Fin 2)).pow 2).continuousOn.sub
      (((PiLp.continuous_apply 2 _ (1 : Fin 2)).pow 2).continuousOn)
  · exact (((PiLp.continuous_apply 2 _ (0 : Fin 2)).pow 2).add
      ((PiLp.continuous_apply 2 _ (1 : Fin 2)).pow 2)).continuousOn.pow 2
  · intro z hz
    exact pow_ne_zero 2 (denominator_pos (hS z hz)).ne'

lemma local_integrability : Specs.D04.C06.ConditionalOrder.local_integrabilityType := by
  intro Q hQ
  apply ExceptionalSets.integrable_continuous (by decide) Q integrand
  exact continuousOn_integrand (fun z hz => (hQ hz 0).1)

lemma quantitative_bound : Specs.D04.C06.ConditionalOrder.quantitative_boundType := by
  intro x y hx hy hxy
  have hx2 : 0 < x^2 := sq_pos_of_pos hx
  have hq := denominator_pos (y := y) hx
  have hy2 : 4*y^2 ≤ x^2 := by nlinarith [sq_nonneg (x-2*y)]
  unfold kernel
  apply (div_le_div_iff₀ (by positivity : 0 < 25*x^2) (sq_pos_of_pos hq)).mpr
  have hh : 0 ≤ (x^2-4*y^2)*(13*x^2+3*y^2) := mul_nonneg (by linarith) (by positivity)
  nlinarith

/-- Scalar FTC applied to the actual one-dimensional Darboux integral. -/
lemma properIntegral_ftc (g F : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) (hF : ContinuousOn F (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt F (g t) t) :
    Integrable (fun z : E 1 => g (z 0)) (intervalBox a b hab) ∧
    properIntegral g a b = F b - F a := by
  have hc : ContinuousOn (fun z : E 1 => g (z 0)) (carrier (intervalBox a b hab)) := by
    apply hg.comp (PiLp.continuous_apply 2 _ (0 : Fin 1)).continuousOn
    intro z hz
    exact hz 0
  have hi := ExceptionalSets.integrable_continuous (by decide) _ _ hc
  refine ⟨hi, ?_⟩
  obtain ⟨hs, hsval⟩ := (scalar_integral _ a b hab).2 hi
  have hv := SingleVariableAnalysis.Riemann.real_ftc_second F g a b hab hF hd hs
  change lowerIntegral _ (intervalBox a b hab) = _ at hsval
  simpa only [properIntegral, min_eq_left hab, max_eq_right hab] using hsval.trans hv

lemma primitive_deriv {x : ℝ} (hx : 0 < x) (t : ℝ) :
    HasDerivAt (fun t => t/(x^2+t^2)) (kernel x t) t := by
  have hq := (denominator_pos (y := t) hx).ne'
  have h := (hasDerivAt_id t).div
    ((hasDerivAt_const t (x^2)).add (hasDerivAt_pow 2 t)) hq
  convert h using 1
  · rfl
  · norm_num [kernel]
    ring

lemma kernel_continuous_right {x : ℝ} (hx : 0 < x) : Continuous (kernel x) := by
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro y
  exact pow_ne_zero 2 (denominator_pos hx).ne'

lemma primitive_continuous {x : ℝ} (hx : 0 < x) :
    Continuous (fun t : ℝ => t/(x^2+t^2)) := by
  exact continuous_id.div (by fun_prop) (fun t => (denominator_pos hx).ne')

lemma proper_kernel {x a b : ℝ} (hx : 0 < x) (hab : a ≤ b) :
    Integrable (fun z : E 1 => kernel x (z 0)) (intervalBox a b hab) ∧
    properIntegral (kernel x) a b = b/(x^2+b^2)-a/(x^2+a^2) :=
  properIntegral_ftc _ _ hab (kernel_continuous_right hx).continuousOn
    (primitive_continuous hx).continuousOn (fun t _ => primitive_deriv hx t)

lemma proper_kernel_reverse {x a b : ℝ} (hx : 0 < x) (hab : a ≤ b) :
    Integrable (fun z : E 1 => kernel (z 0) x) (intervalBox a b hab) ∧
    properIntegral (fun t => kernel t x) a b = -(b/(x^2+b^2)-a/(x^2+a^2)) := by
  have he : (fun t => kernel t x) = fun t => -kernel x t :=
    funext (fun t => kernel_antisymm x t)
  have hz : (fun z : E 1 => kernel (z 0) x) = fun z => -kernel x (z 0) :=
    funext (fun z => kernel_antisymm x (z 0))
  rw [hz, he]
  convert properIntegral_ftc (fun t => -kernel x t)
    (fun t => -(t/(x^2+t^2))) hab (kernel_continuous_right hx).neg.continuousOn
    (primitive_continuous hx).neg.continuousOn (fun t _ => (primitive_deriv hx t).neg) using 1
  ring


lemma eventually_small_positive : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < 1/2 := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1/2 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with δ hδ hδ'
  exact ⟨hδ, hδ'⟩

lemma unit_improper_ftc (g F : ℝ → ℝ) (hg : Continuous g) (hF : Continuous F)
    (hd : ∀ t, HasDerivAt F (g t) t) :
    HasUnitImproperIntegral g (F 1-F 0) := by
  refine ⟨fun a b _ hab _ => (properIntegral_ftc g F hab hg.continuousOn hF.continuousOn
    (fun t _ => hd t)).1, ?_⟩
  have h1 : Tendsto (fun δ : ℝ => 1-δ) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub ((show Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 0) from nhdsWithin_le_nhds))
  have h0 : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    nhdsWithin_le_nhds
  refine ⟨?_, F (1/2)-F 0, F 1-F (1/2), ?_, ?_, by ring⟩
  · apply ((hF.continuousAt.tendsto.comp h1).sub (hF.continuousAt.tendsto.comp h0)).congr'
    filter_upwards [eventually_small_positive] with δ hδ
    exact (properIntegral_ftc g F (by linarith [hδ.2]) hg.continuousOn hF.continuousOn
      (fun t _ => hd t)).2.symm
  · apply (tendsto_const_nhds.sub (hF.continuousAt.tendsto.comp h0)).congr'
    filter_upwards [eventually_small_positive] with δ hδ
    exact (properIntegral_ftc g F hδ.2.le hg.continuousOn hF.continuousOn
      (fun t _ => hd t)).2.symm
  · apply ((hF.continuousAt.tendsto.comp h1).sub tendsto_const_nhds).congr'
    filter_upwards [eventually_small_positive] with δ hδ
    exact (properIntegral_ftc g F (by linarith [hδ.2]) hg.continuousOn hF.continuousOn
      (fun t _ => hd t)).2.symm


lemma inner_integrals : Specs.D04.C06.ConditionalOrder.inner_integralsType := by
  intro x hx
  have hi := proper_kernel (a := 0) (b := 1) hx (by norm_num)
  have hr := proper_kernel_reverse (a := 0) (b := 1) hx (by norm_num)
  have hu := unit_improper_ftc _ _ (kernel_continuous_right hx) (primitive_continuous hx)
    (primitive_deriv hx)
  have he : (fun t => kernel t x) = fun t => -kernel x t :=
    funext (fun t => kernel_antisymm x t)
  have hur := unit_improper_ftc (fun t => -kernel x t) (fun t => -(t/(x^2+t^2))) (kernel_continuous_right hx).neg
    (primitive_continuous hx).neg (fun t => (primitive_deriv hx t).neg)
  refine ⟨hi.1, ?_, ?_, hr.1, ?_, ?_⟩
  · simpa [add_comm, neg_div, Pi.neg_apply] using hi.2
  · simpa [add_comm, neg_div, Pi.neg_apply] using hu
  · simpa [add_comm, neg_div, Pi.neg_apply] using hr.2
  · rw [he]
    simpa [add_comm, neg_div, Pi.neg_apply] using hur

lemma properIntegral_congr {g h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (he : EqOn g h (Icc a b)) : properIntegral g a b = properIntegral h a b := by
  unfold properIntegral
  simp only [min_eq_left hab, max_eq_right hab]
  exact lowerIntegral_congr (fun z hz => he (hz 0))

lemma unit_improper_congr {g h : ℝ → ℝ} {I : ℝ}
    (he : EqOn g h (Ioo 0 1)) (hg : HasUnitImproperIntegral g I) :
    HasUnitImproperIntegral h I := by
  refine ⟨?_, ?_⟩
  · intro a b ha hab hb
    exact (integrable_congr (fun z hz => he ⟨ha.trans_le (hz 0).1, (hz 0).2.trans_lt hb⟩)).mp
      (hg.1 a b ha hab hb)
  · refine ⟨?_, ?_⟩
    · apply hg.2.1.congr'
      filter_upwards [eventually_small_positive] with δ hδ
      apply properIntegral_congr (by linarith [hδ.2])
      intro t ht
      exact he ⟨hδ.1.trans_le ht.1, by linarith [ht.2, hδ.1]⟩
    · obtain ⟨L, R, hL, hR, hI⟩ := hg.2.2
      refine ⟨L, R, ?_, ?_, hI⟩
      · apply hL.congr'
        filter_upwards [eventually_small_positive] with δ hδ
        apply properIntegral_congr hδ.2.le
        intro t ht
        exact he ⟨hδ.1.trans_le ht.1, by linarith [ht.2]⟩
      · apply hR.congr'
        filter_upwards [eventually_small_positive] with δ hδ
        apply properIntegral_congr (by linarith [hδ.2])
        intro t ht
        exact he ⟨by linarith [ht.1], by linarith [ht.2, hδ.1]⟩


lemma iterated_integrals : Specs.D04.C06.ConditionalOrder.iterated_integralsType := by
  have hc : Continuous (fun t : ℝ => 1/(1+t^2)) :=
    continuous_const.div (by fun_prop) (fun t => by positivity)
  have hd (t : ℝ) : HasDerivAt Real.arctan (1/(1+t^2)) t := by
    simpa [one_div] using Real.hasDerivAt_arctan t
  have h := unit_improper_ftc _ _ hc Real.continuous_arctan hd
  have hn := unit_improper_ftc (fun t => -(1/(1+t^2))) (fun t => -Real.arctan t) hc.neg Real.continuous_arctan.neg (fun t => (hd t).neg)
  constructor
  · apply unit_improper_congr (g := fun t => 1/(1+t^2))
    · intro t ht
      exact ((inner_integrals t ht.1).2.1).symm
    · simpa using h
  · apply unit_improper_congr (g := fun t => -(1/(1+t^2)))
    · intro t ht
      simpa only [neg_div] using ((inner_integrals t ht.1).2.2.2.2.1).symm
    · simpa [Pi.neg_apply, neg_div] using hn

lemma mem_interval_carrier {a b : ℝ} (hab : a ≤ b) (z : E 1) :
    z ∈ carrier (intervalBox a b hab) ↔ z 0 ∈ Icc a b := by
  constructor
  · exact fun hz => hz 0
  · intro hz i
    fin_cases i
    exact hz

/-- Exact agreement of interval-region integrals and the shared box integral,
proved by the proper cutoff lemma, including arbitrary endpoint values. -/
lemma region_interval {a b : ℝ} (hab : a ≤ b) (v : E 1 → ℝ)
    (hv : Integrable v (intervalBox a b hab)) :
    RegionIntegrable (fun z : carrier (intervalBox a b hab) => v z) ∧
    regionIntegral (fun z : carrier (intervalBox a b hab) => v z) =
      lowerIntegral v (intervalBox a b hab) := by
  let A := intervalBox a b hab
  let B := intervalBox (a-1) (b+1) (show a-1 ≤ b+1 by linarith)
  have hB : Encloses (carrier A) B := by
    change closure (carrier A) ⊆ interior (carrier B)
    rw [(NullCovers.isClosed_carrier A).closure_eq]
    intro z hz
    rw [interior_carrier]
    intro i
    change a-1 < z i ∧ z i < b+1
    have hzi := hz i
    change a ≤ z i ∧ z i ≤ b at hzi
    constructor <;> linarith [hzi.1, hzi.2]
  have he : zeroExtension (fun z : carrier A => v z) =
      fun z : E 1 => if z 0 ∈ Icc a b then v z else 0 := by
    funext z
    by_cases hz : z ∈ carrier A
    · rw [zeroExtension_apply _ ⟨z, hz⟩, ite_eq_left ((mem_interval_carrier hab z).mp hz)]
    · rw [zeroExtension_of_not_mem _ hz,
        ite_eq_right (fun h => hz ((mem_interval_carrier hab z).mpr h))]
  obtain ⟨hg, hgval⟩ := SlicingAndMoments.interval_cutoff v (a-1) a b (b+1)
    (by linarith) hab (by linarith) hv
  have hi : Integrable (zeroExtension (fun z : carrier A => v z)) B := by
    rw [he]
    exact hg
  have hri := (region_integrable_iff_box _ hB).mpr hi
  refine ⟨hri, ?_⟩
  rw [integral_eq_on_enclosing_box _ hri hB hi]
  change lowerIntegral _ B = _
  rw [he]
  exact hgval

@[simp] lemma integrand_product (x y : E 1) :
    integrand (productPoint x y) = kernel (x 0) (y 0) := rfl

lemma square_box_zero {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    let A := intervalBox a b hab
    Integrable integrand (productBox A A) ∧
    lowerIntegral integrand (productBox A A) = 0 := by
  dsimp only
  let A := intervalBox a b hab
  have hf : Integrable integrand (productBox A A) := by
    apply ExceptionalSets.integrable_continuous (by decide)
    apply continuousOn_integrand
    intro z hz
    have h := hz 0
    change a ≤ z 0 ∧ z 0 ≤ b at h
    exact ha.trans_le h.1
  obtain ⟨hl, _, hval, _⟩ := fubini_lower_upper A A integrand hf
  obtain ⟨hr, _, hrval, _⟩ := fubini_reverse A A integrand hf
  have he : EqOn (lowerSliceReverse integrand A)
      (fun y => (-1 : ℝ)*lowerSlice integrand A y) (carrier A) := by
    intro y hy
    have hypos : 0 < y 0 := ha.trans_le (hy 0).1
    have hi := (proper_kernel (a := a) (b := b) hypos hab).1
    have hneg := integrable_smul (-1) hi
    have hs := integral_smul (-1) hi hneg
    change lowerIntegral (fun x => integrand (productPoint x y)) A =
      (-1)*lowerIntegral (fun x => integrand (productPoint y x)) A
    calc
      _ = lowerIntegral (fun x : E 1 => (-1)*kernel (y 0) (x 0)) A := by
        apply lowerIntegral_congr
        intro x _
        simp only [integrand_product, kernel_antisymm (y 0), neg_one_mul]
      _ = (-1)*lowerIntegral (fun x : E 1 => kernel (y 0) (x 0)) A := hs
      _ = _ := rfl
  have hneg := integrable_smul (-1) hl
  have hs := integral_smul (-1) hl hneg
  have hlr := lowerIntegral_congr he
  change lowerIntegral _ A = lowerIntegral integrand _ at hval hrval
  change lowerIntegral _ A = (-1)*lowerIntegral _ A at hs
  refine ⟨hf, ?_⟩
  linarith [hlr.trans hs]

lemma square_region_zero {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    let A := intervalBox a b hab
    RegionIntegrable (fun z : carrier (productBox A A) => integrand z) ∧
    regionIntegral (fun z : carrier (productBox A A) => integrand z) = 0 := by
  dsimp only
  let A := intervalBox a b hab
  let S := SlicingAndMoments.between (carrier A) (fun _ => a) (fun _ => b)
  have he : S = carrier (productBox A A) := by
    ext z
    exact (SlicingAndMoments.productBox_mem_iff z A a b hab).symm
  have hc : ContinuousOn integrand (closure S) := by
    rw [he, (NullCovers.isClosed_carrier _).closure_eq]
    apply continuousOn_integrand
    intro z hz
    have h := hz 0
    change a ≤ z 0 ∧ z 0 ≤ b at h
    exact ha.trans_le h.1
  obtain ⟨hi, _, hout, hv⟩ := (SlicingAndMoments.slicing (carrier A)
    (fun _ => a) (fun _ => b) (jordan_box A) continuousOn_const continuousOn_const
    (fun _ _ => hab)).2.2 integrand hc
  have hs : SlicingAndMoments.sliceIntegral (fun _ : E 1 => a) (fun _ => b) integrand =
      lowerSlice integrand A := by
    funext x
    simp only [SlicingAndMoments.sliceIntegral, Specs.D04.C06.SlicingAndMoments.Model.sliceIntegral,
      Specs.D04.C06.SlicingAndMoments.Model.sliceBox,
      min_eq_left hab, max_eq_right hab]
    rfl
  simp only [hs] at hv hout
  have hf := (square_box_zero ha hab).1
  obtain ⟨hl, _, hlval, _⟩ := fubini_lower_upper A A integrand hf
  have houter := (@region_interval a b hab (@lowerSlice 1 1 integrand A) hl).2
  have hz : regionIntegral (fun z : S => integrand z) = 0 := by
    exact hv.trans (houter.trans (hlval.trans (square_box_zero ha hab).2))
  exact he ▸ (show RegionIntegrable (fun z : S => integrand z) ∧
    regionIntegral (fun z : S => integrand z) = 0 from ⟨hi, hz⟩)

lemma square_integrals : Specs.D04.C06.ConditionalOrder.square_integralsType := by
  intro δ hδ hδhalf
  have hab : δ ≤ 1-δ := by linarith
  have he : truncationBox δ = productBox (intervalBox δ (1-δ) hab)
      (intervalBox δ (1-δ) hab) := by
    simp only [truncationBox, max_eq_right hab]
  change Integrable integrand _ ∧ lowerIntegral integrand _ = 0 ∧
    RegionIntegrable (fun z : carrier (truncationBox δ) => integrand z) ∧
    regionIntegral (fun z : carrier (truncationBox δ) => integrand z) = 0
  rw [he]
  exact ⟨(square_box_zero hδ hab).1, (square_box_zero hδ hab).2, square_region_zero hδ hab⟩

lemma truncation_lower (δ : ℝ) (i : Fin 2) : (truncationBox δ).lower i = δ := by
  fin_cases i <;> rfl
lemma truncation_upper (δ : ℝ) (i : Fin 2) :
    (truncationBox δ).upper i = max δ (1-δ) := by
  fin_cases i <;> rfl

lemma mem_truncation {δ : ℝ} (hδ : δ < 1/2) (z : E 2) :
    z ∈ truncation δ ↔ ∀ i, δ ≤ z i ∧ z i ≤ 1-δ := by
  change (∀ i, _ ≤ z i ∧ z i ≤ _) ↔ _
  simp only [truncation_lower, truncation_upper, max_eq_right (show δ ≤ 1-δ by linarith)]

lemma mem_interior_truncation {δ : ℝ} (hδ : δ < 1/2) (z : E 2) :
    z ∈ interior (truncation δ) ↔ ∀ i, δ < z i ∧ z i < 1-δ := by
  change z ∈ interior (carrier (truncationBox δ)) ↔ _
  rw [interior_carrier]
  change (∀ i, _ < z i ∧ z i < _) ↔ _
  simp only [truncation_lower, truncation_upper, max_eq_right (show δ ≤ 1-δ by linarith)]

lemma truncation_compact_jordan {δ : ℝ} (hδ : 0 < δ) (hh : δ < 1/2) :
    CompactJordanSubset domain (truncation δ) := by
  refine ⟨DiscontinuityCriterion.carrier_compact _, jordan_box _, ?_⟩
  intro z hz i
  have h := (mem_truncation hh z).mp hz i
  constructor <;> linarith [h.1, h.2]

lemma regular_exhaustion : Specs.D04.C06.ConditionalOrder.regular_exhaustionType := by
  intro δ hδ hanti hlim
  refine ⟨fun j => truncation_compact_jordan (hδ j).1 (hδ j).2, ?_, ?_⟩
  · intro j z hz
    apply (mem_interior_truncation (hδ (j+1)).2 z).mpr
    intro i
    have hi := (mem_truncation (hδ j).2 z).mp hz i
    have hstep := hanti (Nat.lt_succ_self j)
    constructor <;> linarith [hi.1, hi.2]
  · apply Subset.antisymm
    · intro z hz
      obtain ⟨j, hj⟩ := mem_iUnion.mp hz
      exact (truncation_compact_jordan (hδ j).1 (hδ j).2).2.2 (interior_subset hj)
    · intro z hz
      have hev : ∀ᶠ j in atTop, ∀ i : Fin 2, δ j < z i ∧ δ j < 1-z i := by
        apply Filter.eventually_all.mpr
        intro i
        exact (hlim.eventually (eventually_lt_nhds (hz i).1)).and
          (hlim.eventually (eventually_lt_nhds (show 0 < 1-z i by linarith [(hz i).2])))
      obtain ⟨j, hj⟩ := hev.exists
      apply mem_iUnion.mpr
      refine ⟨j, (mem_interior_truncation (hδ j).2 z).mpr ?_⟩
      intro i
      exact ⟨(hj i).1, by linarith [(hj i).2]⟩

lemma square_limit (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j ∧ δ j < 1/2) :
    HasIntegralAlong integrand (fun j => truncation (δ j)) 0 := by
  have he : (fun j => regionIntegral (fun z : truncation (δ j) => integrand z)) =
      fun _ : ℕ => (0 : ℝ) := by
    funext j
    exact (square_integrals (δ j) (hδ j).1 (hδ j).2).2.2.2
  change Tendsto _ atTop (𝓝 0)
  rw [he]
  exact tendsto_const_nhds

lemma mem_triangle {δ : ℝ} (hδ : δ < 1/2) (z : E 2) :
    z ∈ triangle δ ↔ δ ≤ z 0 ∧ z 0 ≤ 1/2 ∧ δ/4 ≤ z 1 ∧ z 1 ≤ z 0/2 := by
  change (SlicingAndMoments.basePoint z ∈ carrier _ ∧ _ ∧ _) ↔ _
  rw [mem_interval_carrier]
  change (δ ≤ z 0 ∧ z 0 ≤ max δ (1/2)) ∧ δ/4 ≤ z 1 ∧ z 1 ≤ z 0/2 ↔ _
  simp only [max_eq_right hδ.le, and_assoc]

lemma triangle_compact_jordan {δ : ℝ} (hδ : 0 < δ) (hh : δ < 1/2) :
    CompactJordanSubset domain (triangle δ) := by
  let A := intervalBox δ (max δ (1/2)) (le_max_left _ _)
  have hab : ∀ x ∈ closure (carrier A), δ/4 ≤ x 0/2 := by
    rw [(NullCovers.isClosed_carrier A).closure_eq]
    intro x hx
    have h := (hx 0).1
    change δ ≤ x 0 at h
    linarith
  have hs := SlicingAndMoments.slicing (carrier A) (fun _ => δ/4) (fun x => x 0/2)
    (jordan_box A) continuousOn_const ((PiLp.continuous_apply 2 _ (0 : Fin 1)).div_const 2).continuousOn hab
  have hc : IsClosed (triangle δ) := by
    have he : triangle δ = {z : E 2 | δ ≤ z 0 ∧ z 0 ≤ 1/2 ∧ δ/4 ≤ z 1 ∧ z 1 ≤ z 0/2} :=
      Set.ext (mem_triangle hh)
    rw [he]
    exact (isClosed_le continuous_const (PiLp.continuous_apply 2 _ (0 : Fin 2))).inter
      ((isClosed_le (PiLp.continuous_apply 2 _ (0 : Fin 2)) continuous_const).inter
        ((isClosed_le continuous_const (PiLp.continuous_apply 2 _ (1 : Fin 2))).inter
          (isClosed_le (PiLp.continuous_apply 2 _ (1 : Fin 2))
            ((PiLp.continuous_apply 2 _ (0 : Fin 2)).div_const 2))))
  refine ⟨Metric.isCompact_iff_isClosed_bounded.mpr ⟨hc, hs.1⟩, hs.2.1, ?_⟩
  intro z hz i
  have hm := (mem_triangle hh z).mp hz
  fin_cases i
  · change 0 < z 0 ∧ z 0 < 1
    exact ⟨hδ.trans_le hm.1, by linarith [hm.2.1]⟩
  · change 0 < z 1 ∧ z 1 < 1
    exact ⟨by linarith [hm.2.2.1], by linarith [hm.2.1, hm.2.2.2]⟩

lemma continuousOn_triangle {δ : ℝ} (hδ : 0 < δ) (hh : δ < 1/2) :
    ContinuousOn integrand (closure (triangle δ)) := by
  rw [(triangle_compact_jordan hδ hh).1.isClosed.closure_eq]
  apply continuousOn_integrand
  intro z hz
  exact hδ.trans_le ((mem_triangle hh z).mp hz).1

lemma triangle_slicing {δ : ℝ} (hδ : 0 < δ) (hh : δ < 1/2) :
    RegionIntegrable (fun z : triangle δ => triangleMinorant z) ∧
    regionIntegral (fun z : triangle δ => triangleMinorant z) =
      regionIntegral (fun x : carrier (intervalBox δ (max δ (1/2)) (le_max_left _ _)) =>
        (12/(25*(x.val 0)^2)) * (x.val 0/2-δ/4)) := by
  let A := intervalBox δ (max δ (1/2)) (le_max_left _ _)
  have hab : ∀ x ∈ closure (carrier A), δ/4 ≤ x 0/2 := by
    rw [(NullCovers.isClosed_carrier A).closure_eq]
    intro x hx
    have h := (hx 0).1
    change δ ≤ x 0 at h
    linarith
  have hc : ContinuousOn triangleMinorant (closure (triangle δ)) := by
    apply ContinuousOn.div continuousOn_const
    · exact continuousOn_const.mul (((PiLp.continuous_apply 2 _ (0 : Fin 2)).pow 2).continuousOn)
    · intro z hz
      have hm := (triangle_compact_jordan hδ hh).1.isClosed.closure_eq ▸ hz
      have hp := hδ.trans_le ((mem_triangle hh z).mp hm).1
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hp.ne')
  obtain ⟨hi, _, _, hv⟩ := (SlicingAndMoments.slicing (carrier A) (fun _ => δ/4) (fun x => x 0/2)
    (jordan_box A) continuousOn_const ((PiLp.continuous_apply 2 _ (0 : Fin 1)).div_const 2).continuousOn hab).2.2
      triangleMinorant hc
  refine ⟨hi, hv.trans ?_⟩
  congr 1
  funext x
  have ho := hab x (subset_closure x.property)
  change lowerIntegral (fun _ : E 1 => 12/(25*(x.val 0)^2))
    (SlicingAndMoments.sliceBox (fun _ => δ/4) (fun x : E 1 => x 0/2) x.val) = _
  rw [SlicingAndMoments.sliceBox_eq_interval _ _ _ ho, (constant_integrals _ _).1,
    SlicingAndMoments.intervalBox_content]

lemma logarithmic_minorant {δ : ℝ} (hδ : 0 < δ) (hh : δ < 1/2) :
    RegionIntegrable (fun x : carrier (intervalBox δ (max δ (1/2)) (le_max_left _ _)) =>
      3/(25*(x.val 0))) ∧
    regionIntegral (fun x : carrier (intervalBox δ (max δ (1/2)) (le_max_left _ _)) =>
      3/(25*(x.val 0))) = (3/25)*(Real.log (1/2)-Real.log δ) := by
  let g : ℝ → ℝ := fun t => 3/(25*t)
  let F : ℝ → ℝ := fun t => (3/25)*Real.log t
  have hg : ContinuousOn g (Icc δ (1/2)) := by
    apply ContinuousOn.div continuousOn_const (continuousOn_const.mul continuousOn_id)
    intro t ht
    exact mul_ne_zero (by norm_num) (hδ.trans_le ht.1).ne'
  have hF : ContinuousOn F (Icc δ (1/2)) := by
    apply continuousOn_const.mul
    exact Real.continuousOn_log.mono (fun t ht => (hδ.trans_le ht.1).ne')
  have hd : ∀ t ∈ Ioo δ (1/2), HasDerivAt F (g t) t := by
    intro t ht
    have h := (Real.hasDerivAt_log (hδ.trans ht.1).ne').const_mul (3/25 : ℝ)
    convert h using 1
    dsimp [g]
    ring
  obtain ⟨hi, hv⟩ := properIntegral_ftc g F hh.le hg hF hd
  have hr := region_interval hh.le (fun z : E 1 => g (z 0)) hi
  have hv' : lowerIntegral (fun z : E 1 => g (z 0)) (intervalBox δ (1/2) hh.le) =
      (3/25)*(Real.log (1/2)-Real.log δ) := by
    have hv'' : properIntegral g δ (1/2) =
        lowerIntegral (fun z : E 1 => g (z 0)) (intervalBox δ (1/2) hh.le) := by
      simp only [properIntegral, min_eq_left hh.le, max_eq_right hh.le]
    rw [hv''] at hv
    exact hv.trans (by dsimp [F]; ring)
  have he : intervalBox δ (max δ (1/2)) (le_max_left _ _) = intervalBox δ (1/2) hh.le := by
    simp only [max_eq_right hh.le]
  exact Eq.ndrec (motive := fun B : Box 1 =>
    RegionIntegrable (fun x : carrier B => 3/(25*(x.val 0))) ∧
    regionIntegral (fun x : carrier B => 3/(25*(x.val 0))) =
      (3/25)*(Real.log (1/2)-Real.log δ))
    ⟨hr.1, hr.2.trans hv'⟩ he.symm

lemma triangles : Specs.D04.C06.ConditionalOrder.trianglesType := by
  intro δ hδ hh
  have hT := triangle_compact_jordan hδ hh
  have hif := locally_integrable_on_compact_jordan (by
    change IsOpen {z : E 2 | ∀ i, z i ∈ Ioo 0 1}
    have ho := isOpen_iInter_of_finite (fun i : Fin 2 => (isOpen_Ioo : IsOpen (Ioo (0 : ℝ) 1)).preimage
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i))
    convert ho using 1
    ext z
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage])
      local_integrability hT
  have hiabs := (scalar_abs_bound _ hif).1
  have hmi := triangle_slicing hδ hh
  have hlog := logarithmic_minorant hδ hh
  have houter : RegionIntegrable (fun x : carrier (intervalBox δ (max δ (1/2)) (le_max_left _ _)) =>
      (12/(25*(x.val 0)^2))*(x.val 0/2-δ/4)) := by
    let A := intervalBox δ (max δ (1/2)) (le_max_left _ _)
    apply (region_interval (le_max_left δ (1/2))
      (fun x : E 1 => (12/(25*(x 0)^2))*(x 0/2-δ/4)) ?_).1
    apply ExceptionalSets.integrable_continuous (by decide)
    apply ContinuousOn.mul
    · apply ContinuousOn.div continuousOn_const
      · exact continuousOn_const.mul (((PiLp.continuous_apply 2 _ (0 : Fin 1)).pow 2).continuousOn)
      · intro x hx
        exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (hδ.trans_le (hx 0).1).ne')
    · exact (((PiLp.continuous_apply 2 _ (0 : Fin 1)).div_const 2).sub continuous_const).continuousOn
  have houter_bound := AbsoluteConvergence.region_mono hlog.1 houter (by
    intro x
    have hx : 0 < x.val 0 := hδ.trans_le (x.property 0).1
    apply (div_le_iff₀ (show 0 < 25*x.val 0 by positivity)).mpr
    have hid : (12/(25*(x.val 0)^2))*(x.val 0/2-δ/4)*(25*x.val 0) =
        6-3*δ/(x.val 0) := by field_simp; ring
    rw [hid]
    have hdle : δ/(x.val 0) ≤ 1 := (div_le_one hx).mpr (x.property 0).1
    have hh3 : 3*δ/(x.val 0) ≤ 3 := by
      calc
        3*δ/(x.val 0) = 3*(δ/(x.val 0)) := by ring
        _ ≤ 3*1 := mul_le_mul_of_nonneg_left hdle (by norm_num)
        _ = 3 := by norm_num
    linarith only [hh3])
  have hpoint := AbsoluteConvergence.region_mono hmi.1 hiabs (by
    intro z
    have hm := (mem_triangle hh z).mp z.property
    have hx := hδ.trans_le hm.1
    have hy : 0 < z.val 1 := by linarith [hm.2.2.1]
    exact (quantitative_bound _ _ hx hy hm.2.2.2).trans (le_abs_self _))
  refine ⟨hT, hiabs, hmi.1, houter, hmi.2, ?_⟩
  rw [hlog.2] at houter_bound
  exact houter_bound.trans (hmi.2 ▸ hpoint)

lemma triangle_divergence : Specs.D04.C06.ConditionalOrder.triangle_divergenceType := by
  apply tendsto_atTop.mpr
  intro M
  have hl := (tendsto_atBot.mp Real.tendsto_log_nhdsGT_zero)
    (Real.log (1/2)-(25/3)*M)
  filter_upwards [hl, eventually_small_positive] with δ hlog hδ
  have hb := (triangles δ hδ.1 hδ.2).2.2.2.2.2
  nlinarith

lemma not_absolute : Specs.D04.C06.ConditionalOrder.not_absoluteType := by
  have hm : absoluteMass domain integrand = ⊤ := by
    by_contra hne
    have hfin : absoluteMass domain integrand < ⊤ := lt_top_iff_ne_top.mpr hne
    have hl := (tendsto_atTop.mp triangle_divergence) ((absoluteMass domain integrand).toReal+1)
    obtain ⟨δ, hδ, hlarge⟩ := (eventually_small_positive.and hl).exists
    have hsmall := AbsoluteConvergence.integral_abs_le_mass hfin
      (triangle_compact_jordan hδ.1 hδ.2)
    linarith
  refine ⟨hm, ?_⟩
  intro habs
  exact (ne_of_lt habs.2) hm

lemma conditional_limit : Specs.D04.C06.ConditionalOrder.conditional_limitType := by
  intro δ hδ hanti hlim
  exact ⟨local_integrability, regular_exhaustion δ hδ hanti hlim,
    not_absolute.2, square_limit δ hδ⟩

end D04.ConditionalOrder
