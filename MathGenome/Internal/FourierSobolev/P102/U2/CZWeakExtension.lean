import MathGenome.Internal.FourierSobolev.Specs.P102.U2.CZWeakExtension
import MathGenome.Internal.FourierSobolev.P102.U2.CZDecomposition
import MathGenome.Internal.FourierSobolev.P102.U2.WeakNorms
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SingularIntegrals.CalderonZygmundWeak11

/-! The imported smooth-kernel endpoint theorem is not applied here. We reuse
only its kernel-independent measure-convergence lemmas, core subspace, and
smooth density lemma. Our operator is an arbitrary bounded complex-linear map.
The rough-kernel endpoint estimate is proved directly from the integral
difference hypothesis by Tonelli and cancellation below. -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace P102.U2.CZWeakExtension
open P102.U2.CZWeak
namespace MeasureTools

/-- A weak estimate on a linear map controls differences without any support
or kernel hypothesis. The non-strict threshold is needed for convergence in
measure and is bounded using the weak estimate at half the threshold. -/
lemma difference_bound {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S : E →ₗ[ℂ] Classes d) (C : ℝ)
    (hS : ∀ (f : E) (t : ℝ), 0 < t →
      volume {x | t < ‖S f x‖} ≤ ENNReal.ofReal (C / t) * ENNReal.ofReal ‖f‖)
    (f g : E) (ε : ℝ) (hε : 0 < ε) :
    volume {x | ε ≤ ‖S f x - S g x‖} ≤
      ENNReal.ofReal (C / (ε / 2)) * ENNReal.ofReal ‖f - g‖ := by
  have he : (S (f - g) : Point d → ℂ) =ᵐ[volume] (fun x => S f x - S g x) := by
    rw [map_sub]
    exact AEEqFun.coeFn_sub _ _
  refine (measure_mono_ae (t := {x | ε / 2 < ‖S (f - g) x‖}) ?_).trans
    (hS (f - g) (ε / 2) (by positivity))
  filter_upwards [he] with x hx hh
  rw [hx]
  change ε ≤ ‖S f x - S g x‖ at hh
  linarith

/-- Weak estimates imply global convergence in measure on L¹ limits. -/
lemma continuous_in_measure {d : ℕ} (S : Extension d) (C : ℝ)
    (hS : WeakBound S C) : MeasureContinuous S := by
  intro u f hu
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hn : Tendsto (fun n => ‖u n - f‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hu
  have hb : Tendsto (fun n => ENNReal.ofReal (C / (ε / 2)) * ENNReal.ofReal ‖u n - f‖)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal hn)
      (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ => bot_le) (fun n => difference_bound S C hS (u n) f ε hε)

/-- Descend a linear map through a surjection once its kernel ambiguity
has been annihilated. Keeping this algebra abstract avoids expanding quotient
representatives of concrete Lp spaces during elaboration. -/
lemma descend {E F G : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
    [Module ℂ E] [Module ℂ F] [Module ℂ G]
    (j : E →ₗ[ℂ] F) (L : E →ₗ[ℂ] G) (hj : Function.Surjective j)
    (hker : LinearMap.ker j ≤ LinearMap.ker L) :
    ∃ U : F →ₗ[ℂ] G, ∀ x, U (j x) = L x := by
  let U := (LinearMap.liftOfSurjective (f := j) hj) ⟨L, hker⟩
  exact ⟨U, fun x => LinearMap.equivOfSurjective_apply (f := j) (g := L) hj hker⟩

end MeasureTools

namespace Library
abbrev Core (d : ℕ) :=
  ExpandedFA.SingularIntegrals.CZWeak.coreSpace (𝕜 := ℂ) (d := d)
abbrev coreToL2 {d : ℕ} : Core d →ₗ[ℂ] L2 d :=
  ExpandedFA.SingularIntegrals.CZWeak.coreToL2

/-- The original action, restricted to the dense intersection. -/
def coreAction {d : ℕ} (T : Operator d) : Core d →ₗ[ℂ] Classes d :=
  (lpEmbed 2).comp (T.toLinearMap.comp coreToL2)

lemma compatible_core {d : ℕ} (T : Operator d) (S : Extension d)
    (hS : Compatible T S) (f : Core d) : S f.val = coreAction T f := by
  simpa [Lp.toLp_coeFn, coreAction, coreToL2,
    ExpandedFA.SingularIntegrals.CZWeak.coreToL2] using
    hS f.val (Lp.memLp f.val) f.property

lemma coreAction_weak {d : ℕ} (T : Operator d) {C : ℝ} (hT : CoreBound T C)
    (f : Core d) (t : ℝ) (ht : 0 < t) :
    volume {x | t < ‖coreAction T f x‖} ≤
      ENNReal.ofReal (C / t) * ENNReal.ofReal ‖f‖ := by
  have h := hT f.val (Lp.memLp f.val) f.property t ht
  change volume {x | t < ‖T (f.property.toLp f.val) x‖} ≤ _
  convert h using 1
  rw [← Lp.enorm_def, ofReal_norm]
  rfl

end Library
open Library

/-- Equality on the dense intersection and weak estimates suffice for
uniqueness; the operator need not have any kernel at all. -/
theorem extension_unique {d : ℕ} (T : Operator d) (S : Extension d)
    (hS : Compatible T S) (hweak : ∃ C : ℝ, 0 ≤ C ∧ WeakBound S C) :
    UniqueWeakExtension T S := by
  intro S' hS' hweak'
  obtain ⟨C, _, hC⟩ := hweak
  obtain ⟨D, _, hD⟩ := hweak'
  apply LinearMap.ext
  intro f
  obtain ⟨u, hu⟩ := ExpandedFA.SingularIntegrals.CZWeak.core_dense_sequence f
  have he (n : ℕ) : (S' (u n).val : Point d → ℂ) =ᵐ[volume] S (u n).val := by
    rw [compatible_core T S' hS' (u n), compatible_core T S hS (u n)]
  exact AEEqFun.ext (tendstoInMeasure_ae_unique
    ((MeasureTools.continuous_in_measure S' D hD (fun n => (u n).val) f hu).congr_left he)
    (MeasureTools.continuous_in_measure S C hC (fun n => (u n).val) f hu))

lemma approximates_of_compatible {d : ℕ} (T : Operator d) (S : Extension d)
    (hS : Compatible T S) (hc : MeasureContinuous S) : Approximates T S := by
  intro u h2 f hu
  apply (hc u f hu).congr_left
  intro n
  have he := hS (u n) (Lp.memLp (u n)) (h2 n)
  rw [Lp.toLp_coeFn] at he
  rw [he]
  exact Filter.EventuallyEq.rfl

namespace Completion
open ExpandedFA.SingularIntegrals.CZWeak (exists_tendstoInMeasure_of_cauchy
  tendstoInMeasure_add tendstoInMeasure_const_smul weak_bound_of_tendstoInMeasure)

variable {d : ℕ} (T : Operator d) {C : ℝ}

/-- Image sequences are Cauchy globally in measure when their inputs are
Cauchy in L¹. No finite-measure assumption is used. -/
lemma images_cauchy (hC : 0 ≤ C) (hT : CoreBound T C) (u : ℕ → Core d) (f : L1 d)
    (hu : Tendsto (fun n => (u n).val) atTop (𝓝 f)) :
    ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ,
      ∀ m n : ℕ, N ≤ m → N ≤ n →
        volume {x | ε ≤ ‖coreAction T (u m) x - coreAction T (u n) x‖} ≤ ENNReal.ofReal δ := by
  intro ε hε δ hδ
  let a := C / (ε / 2)
  have ha : 0 ≤ a := div_nonneg hC (by positivity)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu.cauchySeq (δ / (a + 1)) (by positivity)
  refine ⟨N, fun m n hm hn =>
    (MeasureTools.difference_bound (coreAction T) C (coreAction_weak T hT)
      (u m) (u n) ε hε).trans ?_⟩
  rw [← ENNReal.ofReal_mul ha]
  apply ENNReal.ofReal_le_ofReal
  have hb : ‖(u m).val - (u n).val‖ ≤ δ / (a + 1) := by
    exact (show ‖(u m).val - (u n).val‖ < δ / (a + 1) by
      simpa only [dist_eq_norm] using hN m hm n hn).le
  change a * ‖(u m).val - (u n).val‖ ≤ δ
  refine (mul_le_mul_of_nonneg_left hb ha).trans ?_
  rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < a + 1)]
  nlinarith

lemma images_zero (hT : CoreBound T C) (u : ℕ → Core d)
    (hu : Tendsto (fun n => (u n).val) atTop (𝓝 0)) :
    TendstoInMeasure volume (fun n => (coreAction T (u n) : Point d → ℂ))
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hn : Tendsto (fun n => ‖(u n).val‖) atTop (𝓝 0) := by simpa using hu.norm
  have hb : Tendsto (fun n => ENNReal.ofReal (C / (ε / 2)) * ENNReal.ofReal ‖(u n).val‖)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal hn)
      (Or.inr ENNReal.ofReal_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => bot_le)
  intro n
  refine (measure_mono (t := {x | ε / 2 < ‖coreAction T (u n) x‖}) ?_).trans
    (coreAction_weak T hT (u n) (ε / 2) (by positivity))
  intro x hx
  change ε ≤ ‖coreAction T (u n) x - 0‖ at hx
  simp only [sub_zero] at hx
  change ε / 2 < ‖coreAction T (u n) x‖
  linarith

/-- Graph of the operator obtained by completing its dense original domain. -/
def Limit (f : L1 d) (g : Classes d) : Prop :=
  ∃ u : ℕ → Core d, Tendsto (fun n => (u n).val) atTop (𝓝 f) ∧
    TendstoInMeasure volume (fun n => (coreAction T (u n) : Point d → ℂ)) atTop g

lemma limit_exists (hC : 0 ≤ C) (hT : CoreBound T C) (f : L1 d) : ∃ g : Classes d, Limit T f g := by
  obtain ⟨u, hu⟩ := ExpandedFA.SingularIntegrals.CZWeak.core_dense_sequence f
  obtain ⟨g, hg, hlim⟩ := exists_tendstoInMeasure_of_cauchy volume
    (fun n => (coreAction T (u n) : Point d → ℂ))
    (fun n => (coreAction T (u n)).aestronglyMeasurable)
    (images_cauchy T hC hT u f hu)
  exact ⟨AEEqFun.mk g hg, u, hu, hlim.congr_right (AEEqFun.coeFn_mk g hg).symm⟩

lemma limit_unique (hT : CoreBound T C) {f : L1 d} {g h : Classes d}
    (hg : Limit T f g) (hh : Limit T f h) : g = h := by
  obtain ⟨u, hu, hug⟩ := hg
  obtain ⟨v, hv, hvh⟩ := hh
  let w : ℕ → Core d := fun n => v n - u n
  have hw : Tendsto (fun n => (w n).val) atTop (𝓝 0) := by simpa [w] using hv.sub hu
  have hz := images_zero T hT w hw
  have hsum := tendstoInMeasure_add hz hug
  have heq (n : ℕ) :
      (fun x => coreAction T (w n) x + coreAction T (u n) x) =ᵐ[volume]
        (coreAction T (v n) : Point d → ℂ) := by
    have he : coreAction T (w n) + coreAction T (u n) = coreAction T (v n) := by
      rw [← map_add]
      simp [w]
    have he' := (AEEqFun.coeFn_add (coreAction T (w n)) (coreAction T (u n))).symm
    rw [he] at he'
    exact he'
  have hl := hsum.congr heq (Eventually.of_forall (fun x => zero_add (g x)))
  exact AEEqFun.ext (tendstoInMeasure_ae_unique hl hvh)

lemma limit_add {f f' : L1 d} {g g' : Classes d}
    (hg : Limit T f g) (hg' : Limit T f' g') : Limit T (f + f') (g + g') := by
  obtain ⟨u, hu, hug⟩ := hg
  obtain ⟨v, hv, hvg⟩ := hg'
  refine ⟨fun n => u n + v n, hu.add hv, ?_⟩
  apply (tendstoInMeasure_add hug hvg).congr
  · intro n
    rw [map_add]
    exact (AEEqFun.coeFn_add _ _).symm
  · exact (AEEqFun.coeFn_add _ _).symm

lemma limit_smul {f : L1 d} {g : Classes d} (hg : Limit T f g) (a : ℂ) :
    Limit T (a • f) (a • g) := by
  obtain ⟨u, hu, hug⟩ := hg
  refine ⟨fun n => a • u n, hu.const_smul a, ?_⟩
  apply (tendstoInMeasure_const_smul hug a).congr
  · intro n
    rw [map_smul]
    exact (AEEqFun.coeFn_smul a _).symm
  · exact (AEEqFun.coeFn_smul a _).symm

lemma limit_weak (hT : CoreBound T C) {f : L1 d} {g : Classes d} (hg : Limit T f g) :
    ∀ t : ℝ, 0 < t → volume {x | t < ‖g x‖} ≤
      ENNReal.ofReal (2 * C / t) * ENNReal.ofReal ‖f‖ := by
  obtain ⟨u, hu, hug⟩ := hg
  exact weak_bound_of_tendstoInMeasure hug hu.norm
    (fun n t ht => coreAction_weak T hT (u n) t ht)

lemma extension_exists (hC : 0 ≤ C) (hT : CoreBound T C) : ∃ S : Extension d, Compatible T S ∧ WeakBound S (2 * C) := by
  classical
  choose F hF using limit_exists T hC hT
  let S : Extension d :=
    { toFun := F
      map_add' := fun f g => limit_unique T hT (hF (f + g)) (limit_add T (hF f) (hF g))
      map_smul' := fun a f => limit_unique T hT (hF (a • f)) (limit_smul T (hF f) a) }
  refine ⟨S, ?_, ?_⟩
  · intro f h1 h2
    have h2' : MemLp (h1.toLp f : Point d → ℂ) 2 volume :=
      (memLp_congr_ae h1.coeFn_toLp).mpr h2
    let a : Core d := ⟨h1.toLp f, h2'⟩
    have ha : Limit T a.val (coreAction T a) := by
      refine ⟨fun _ => a, tendsto_const_nhds, ?_⟩
      intro ε hε
      simp only [edist_self, not_le.mpr hε, Set.ofPred_false, measure_empty]
      exact tendsto_const_nhds
    have he : S (h1.toLp f) = coreAction T a := limit_unique T hT (hF a.val) ha
    rw [he]
    have hL2 : coreToL2 a = h2.toLp f := h2'.toLp_congr h2 h1.coeFn_toLp
    change lpEmbed 2 (T (coreToL2 a)) = lpEmbed 2 (T (h2.toLp f))
    rw [hL2]
  · intro f t ht
    exact limit_weak T hT (hF f) t ht

end Completion

/-- Construct the action on the actual sum space by descending the product
map; agreement on the intersection annihilates exactly its ambiguity. -/
theorem compatible_sum {d : ℕ} (T : Operator d) (S : Extension d)
    (hS : Compatible T S) : CompatibleSum T S := by
  classical
  let j : L1 d × L2 d →ₗ[ℂ] SumSpace d := (sumMap d).rangeRestrict
  let F : L1 d × L2 d →ₗ[ℂ] Classes d := S.coprod ((lpEmbed 2).comp T.toLinearMap)
  have hker : LinearMap.ker j ≤ LinearMap.ker F := by
    rintro ⟨f, g⟩ hfg
    have hz : lpEmbed 1 f + lpEmbed 2 g = 0 := by
      exact congrArg Subtype.val (LinearMap.mem_ker.mp hfg)
    have he : (f : Classes d) = ((-g : L2 d) : Classes d) :=
      eq_neg_of_add_eq_zero_left hz
    have hf2 : MemLp (f : Point d → ℂ) 2 volume :=
      (memLp_congr_ae (AEEqFun.ext_iff.mp he)).mpr (Lp.memLp (-g))
    have hlp : hf2.toLp f = -g := by
      apply Lp.ext
      exact hf2.coeFn_toLp.trans (AEEqFun.ext_iff.mp he)
    have hSf : S f = lpEmbed 2 (T (-g)) := by
      simpa [Lp.toLp_coeFn, hlp] using hS f (Lp.memLp f) hf2
    change F (f, g) = 0
    change S f + lpEmbed 2 (T g) = 0
    rw [hSf, map_neg, map_neg, neg_add_cancel]
  have hj : Function.Surjective j := by
    rintro ⟨z, ⟨u, rfl⟩⟩
    exact ⟨u, rfl⟩
  obtain ⟨U, hu⟩ := MeasureTools.descend
    (E := L1 d × L2 d) (F := SumSpace d) (G := Classes d) j F hj hker
  have hU (f : L1 d) (g : L2 d) : U (sumInput f g) = S f + lpEmbed 2 (T g) :=
    hu (f, g)
  refine ⟨U, hU, ?_⟩
  intro V hV
  apply LinearMap.ext
  rintro ⟨z, ⟨⟨f, g⟩, rfl⟩⟩
  exact (hV f g).trans (hU f g).symm

/-- Complete the abstract extension, including all compatibility conclusions. -/
theorem abstract_extension : Specs.P102.U2.CZWeakExtension.abstract_extension := by
  intro d T C hC hT
  obtain ⟨S, hS, hw⟩ := Completion.extension_exists T hC hT
  have hc := MeasureTools.continuous_in_measure S (2 * C) hw
  exact ⟨S, hS, hw, hc, approximates_of_compatible T S hS hc,
    extension_unique T S hS ⟨2 * C, by positivity, hw⟩, compatible_sum T S hS⟩

lemma coreBound_mono {d : ℕ} {T : Operator d} {C D : ℝ}
    (hCD : C ≤ D) (hT : CoreBound T C) : CoreBound T D := by
  intro f h1 h2 t ht
  exact (hT f h1 h2 t ht).trans (mul_le_mul'
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hCD ht.le)) le_rfl)

/-- The integral difference hypothesis controls every shifted exterior used
in cancellation. This requires no pointwise regularity or size estimate. -/
lemma shifted_difference_bound {d : ℕ} (K : Point d → ℂ) (A : ℝ≥0)
    (hdiff : ∀ h : Point d, h ≠ 0 →
      (∫⁻ z in {z : Point d | 2 * ‖h‖ < ‖z‖}, ‖K (z - h) - K z‖ₑ) ≤ (A : ℝ≥0∞))
    (c y : Point d) (R : ℝ) (hy : ‖y - c‖ ≤ R) :
    (∫⁻ x in (Metric.closedBall c (2 * R))ᶜ, ‖K (x - y) - K (x - c)‖ₑ) ≤ (A : ℝ≥0∞) := by
  by_cases he : y = c
  · simp [he]
  have hne : y - c ≠ 0 := sub_ne_zero.mpr he
  let E : Set (Point d) := {z | 2 * R < ‖z‖}
  have hE : MeasurableSet E := measurableSet_lt measurable_const measurable_norm
  let F : Point d → ℝ≥0∞ := E.indicator (fun z => ‖K (z - (y - c)) - K z‖ₑ)
  have hshift : (∫⁻ x in (Metric.closedBall c (2 * R))ᶜ,
      ‖K (x - y) - K (x - c)‖ₑ) = ∫⁻ z in E, ‖K (z - (y - c)) - K z‖ₑ := by
    rw [← lintegral_indicator Metric.isClosed_closedBall.measurableSet.compl,
      ← lintegral_indicator hE]
    change (∫⁻ x, (Metric.closedBall c (2 * R))ᶜ.indicator
      (fun x => ‖K (x - y) - K (x - c)‖ₑ) x) = ∫⁻ z, F z
    have heq : (fun x => (Metric.closedBall c (2 * R))ᶜ.indicator
        (fun x => ‖K (x - y) - K (x - c)‖ₑ) x) = fun x => F (x - c) := by
      funext x
      have hmem : x ∈ (Metric.closedBall c (2 * R))ᶜ ↔ x - c ∈ E := by
        simp [E, Metric.mem_closedBall, dist_eq_norm]
      have halg : x - c - (y - c) = x - y := by abel
      by_cases hx : x ∈ (Metric.closedBall c (2 * R))ᶜ
      · simp [F, hx, hmem.mp hx, halg]
      · simp [F, hx, show x - c ∉ E from fun h => hx (hmem.mpr h)]
    rw [heq]
    exact lintegral_sub_right_eq_self F c
  rw [hshift]
  exact (lintegral_mono_set (show E ⊆ {z : Point d | 2 * ‖y - c‖ < ‖z‖} from
    fun z hz => by dsimp [E] at hz ⊢; linarith)).trans (hdiff (y - c) hne)

lemma kernel_aestronglyMeasurable {d : ℕ} (hd : 0 < d) {K : Point d → ℂ}
    (hK : LocallyIntegrableOn K ({0}ᶜ : Set (Point d)) volume) :
    AEStronglyMeasurable K volume := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have he : (volume : Measure (Point d)).restrict ({0}ᶜ : Set (Point d)) = volume := by
    apply Measure.restrict_eq_self_of_ae_mem
    simp only [ae_iff, mem_compl_iff, not_not, Set.ofPred_mem_eq]
    exact measure_singleton 0
  rw [← he]
  exact hK.aestronglyMeasurable

/-- Tonelli turns the integral difference condition into cancellation control
for every mean-zero integrable L² input essentially supported in a ball. -/
lemma rough_cancellation_ball {d : ℕ} (hd : 0 < d)
    (T : Operator d) (K : Point d → ℂ) (A : ℝ≥0) (hK : KernelHypotheses T K A)
    (c : Point d) (R : ℝ) (hR : 0 < R)
    (b : Point d → ℂ) (hb : Integrable b volume) (h2 : MemLp b 2 volume)
    (hs : ∀ᵐ y ∂volume, y ∉ Metric.closedBall c R → b y = 0)
    (hm : (∫ y, b y) = 0) :
    eLpNorm (T (h2.toLp b) : Point d → ℂ) 1
      (volume.restrict (Metric.closedBall c (2 * R))ᶜ) ≤
      (A : ℝ≥0∞) * eLpNorm b 1 volume := by
  let E := (Metric.closedBall c (2 * R))ᶜ
  let μ : Measure (Point d) := volume.restrict E
  let H : Point d × Point d → ℂ := fun p => (K (p.1 - p.2) - K (p.1 - c)) * b p.2
  have hKm := kernel_aestronglyMeasurable hd hK.locallyIntegrable
  have hH : AEStronglyMeasurable H (μ.prod volume) := by
    have h1 := hKm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume volume)
    have h2 := (hKm.comp_quasiMeasurePreserving
      (measurePreserving_sub_right volume c).quasiMeasurePreserving).comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := (volume : Measure (Point d))))
    have h3 := hb.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Point d))) (ν := volume))
    exact (h1.sub h2 |>.mul h3).mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have htotal : (∫⁻ x, ∫⁻ y, ‖H (x, y)‖ₑ ∂volume ∂μ) ≤
      (A : ℝ≥0∞) * eLpNorm b 1 volume := by
    rw [lintegral_lintegral_swap hH.enorm,
      eLpNorm_one_eq_lintegral_enorm hb.aestronglyMeasurable,
      ← lintegral_const_mul'' _ hb.aestronglyMeasurable.enorm]
    apply lintegral_mono_ae
    filter_upwards [hs] with y hy
    by_cases hyS : y ∈ Metric.closedBall c R
    · simp only [H, enorm_mul]
      rw [lintegral_mul_const' _ _ (by simp)]
      exact mul_le_mul' (shifted_difference_bound K A hK.difference c y R (by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hyS)) le_rfl
    · simp [H, hy hyS]
  have hiH : Integrable H (μ.prod volume) := by
    refine ⟨hH, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hH.enorm]
    exact htotal.trans_lt (ENNReal.mul_lt_top (by simp) (memLp_one_iff_integrable.mpr hb).eLpNorm_lt_top)
  have hrep := hK.offSupport b h2 (Metric.closedBall c R) (isCompact_closedBall c R) hs
  have heq : ∀ᵐ x ∂μ, T (h2.toLp b) x = ∫ y, H (x, y) := by
    filter_upwards [hiH.prod_right_ae, ae_restrict_of_ae hrep,
      ae_restrict_mem (Metric.isClosed_closedBall.measurableSet.compl)] with x hx hrep hxE
    have hxS : x ∉ Metric.closedBall c R := by
      intro hxS
      apply hxE
      exact Metric.closedBall_subset_closedBall (by linarith) hxS
    rw [hrep hxS]
    have hc : Integrable (fun y => K (x - c) * b y) := hb.const_mul _
    have hf : Integrable (fun y => K (x - y) * b y) := by
      have he : (fun y => K (x - y) * b y) =
          (fun y => H (x,y) + K (x - c) * b y) := by funext y; dsimp [H]; ring
      rw [he]
      exact hx.add hc
    simp only [H, sub_mul]
    rw [integral_sub hf hc, integral_const_mul, hm, mul_zero, sub_zero]
  rw [eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable _).restrict]
  apply le_trans _ htotal
  apply lintegral_mono_ae
  filter_upwards [heq] with x hx
  rw [hx]
  exact enorm_integral_le_lintegral_enorm _


open ExpandedFA.SingularIntegrals
open ExpandedFA.SingularIntegrals.CZWeak

lemma rough_cancellation_cube {d : ℕ} (hd : 0 < d)
    (T : Operator d) (K : Point d → ℂ) (A : ℝ≥0) (hK : KernelHypotheses T K A)
    (q : CZ.DyadicCube d) (b : Point d → ℂ) (hb : Integrable b volume)
    (h2 : MemLp b 2 volume) (hs : ∀ᵐ y ∂volume, y ∉ CZ.cube q → b y = 0)
    (hm : (∫ y, b y) = 0) :
    eLpNorm (T (h2.toLp b) : Point d → ℂ) 1 (volume.restrict (enlargedCube q)ᶜ) ≤
      (A : ℝ≥0∞) * eLpNorm b 1 volume := by
  have hs' : ∀ᵐ y ∂volume, y ∉ Metric.closedBall (cubeCenter q) (cubeRadius q) → b y = 0 := by
    filter_upwards [hs] with y hy hys
    exact hy (fun hyq => hys (cube_subset_closedBall q hyq))
  exact (eLpNorm_mono_measure _ (Measure.restrict_mono
    (Set.compl_subset_compl.mpr (closedBall_subset_enlargedCube q)) le_rfl)).trans
      (rough_cancellation_ball hd T K A hK (cubeCenter q) (cubeRadius q)
        (cubeRadius_pos q) b hb h2 hs' hm)

/-- Pass cancellation bounds for the actual bad pieces through their L² sum. -/
lemma rough_bad_sum_bound {d : ℕ} (hd : 0 < d)
    (T : Operator d) (K : Point d → ℂ) (A : ℝ≥0) (hK : KernelHypotheses T K A)
    (f : Point d → ℂ) (t : ℝ) (Q : Set (CZ.DyadicCube d)) (g : Point d → ℂ)
    (hD : CZ.Decomposition f t Q g) (h2 : MemLp f 2 volume) :
    ∃ hg2 : MemLp g 2 volume,
      eLpNorm (T (h2.toLp f - hg2.toLp g) : Point d → ℂ) 1
        (volume.restrict (⋃ q : Q, enlargedCube q.1)ᶜ) ≤
          (2 * (A : ℝ≥0∞)) * eLpNorm f 1 volume := by
  classical
  obtain ⟨hg2, hb2, hs2, hsum⟩ := hD.series_two h2
  let E := (⋃ q : Q, enlargedCube q.1)ᶜ
  let u : Q → L2 d := fun q => T ((hb2 q).toLp (CZ.badPiece f q.1))
  have heq : hs2.toLp (f - g) = h2.toLp f - hg2.toLp g := by
    apply Lp.ext
    filter_upwards [hs2.coeFn_toLp, Lp.coeFn_sub (h2.toLp f) (hg2.toLp g),
      h2.coeFn_toLp, hg2.coeFn_toLp] with x hx hsub hf hg
    simp only [hx, hsub, Pi.sub_apply, hf, hg]
  have hu : HasSum u (T (h2.toLp f - hg2.toLp g)) := by
    simpa only [heq] using T.hasSum hsum
  refine ⟨hg2, eLpNorm_one_le_of_hasSum_L2 u _ hu E _ (fun s => ?_)⟩
  have hpiece (q : Q) : eLpNorm (u q : Point d → ℂ) 1 (volume.restrict E) ≤
      (A : ℝ≥0∞) * eLpNorm (CZ.badPiece f q.1) 1 volume := by
    have hs : ∀ᵐ x ∂volume, x ∉ CZ.cube q.1 → CZ.badPiece f q.1 x = 0 := by
      exact ae_of_all _ fun x hx => by
        by_contra hn
        exact hx (hD.bad_support q hn)
    have hsub : E ⊆ (enlargedCube q.1)ᶜ := by
      intro x hx hxs
      exact hx (mem_iUnion.mpr ⟨q, hxs⟩)
    exact (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)).trans
      (rough_cancellation_cube hd T K A hK q.1 (CZ.badPiece f q.1)
        (hD.bad_integrable q) (hb2 q) hs (hD.bad_mean q))
  calc
    eLpNorm (∑ i ∈ s, (u i : Point d → ℂ)) 1 (volume.restrict E) ≤
        ∑ q ∈ s, eLpNorm (u q : Point d → ℂ) 1 (volume.restrict E) := eLpNorm_sum_le le_rfl
    _ ≤ ∑ q ∈ s, (A : ℝ≥0∞) * eLpNorm (CZ.badPiece f q.1) 1 volume :=
      Finset.sum_le_sum fun q _ => hpiece q
    _ = (A : ℝ≥0∞) * ∑ q ∈ s, eLpNorm (CZ.badPiece f q.1) 1 volume :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (A : ℝ≥0∞) * (2 * eLpNorm f 1 volume) :=
      mul_le_mul le_rfl ((ENNReal.sum_le_tsum s).trans hD.bad_one_bound) bot_le bot_le
    _ = _ := by ring



/-- The uniform constant depends only on the dimension, integral difference
bound and L² operator norm. -/
theorem weak_core : Specs.P102.U2.CZWeakExtension.weak_core := by
  refine ⟨fun d A N => ⟨4 * (N : ℝ) ^ 2 * 2 ^ d +
    (6 * Real.sqrt (d + 1 : ℝ)) ^ d + 4 * (A : ℝ), by positivity⟩, ?_⟩
  intro d hd T K A hK
  classical
  let D : ℝ := (6 * Real.sqrt (d + 1 : ℝ)) ^ d
  let Gc : ℝ := 4 * ‖T‖ ^ 2 * 2 ^ d
  change CoreBound T (Gc + D + 4 * (A : ℝ))
  intro f h1 h2 t ht
  have hf := memLp_one_iff_integrable.mp h1
  obtain ⟨Q, g, hcon⟩ := P102.U2.CZDecomposition.decomposition d hd f hf t ht
  rcases hcon with ⟨_, hdisjoint, _, hmeasure, hout, hin, _, hgi, hginf, hg1, hpieces,
    hbad1, hs1, hs2⟩
  have hdec : CZ.Decomposition f t Q g :=
    { disjoint := hdisjoint
      good_outside := hout
      good_inside := hin
      measure_bound := hmeasure
      good_integrable := hgi
      good_infinity := hginf
      good_one := hg1
      bad_integrable := fun q => (hpieces q).1
      bad_mean := fun q => (hpieces q).2.1
      bad_support := fun q => (hpieces q).2.2
      bad_one_bound := hbad1
      series_one := hs1
      series_two := hs2 }
  obtain ⟨hg2, hbad⟩ := rough_bad_sum_bound hd T K A hK f t Q g hdec h2
  let G : L2 d := T (hg2.toLp g)
  let B : L2 d := T (h2.toLp f - hg2.toLp g)
  let F : Set (Point d) := ⋃ q : Q, enlargedCube q.1
  have henergy : ‖hg2.toLp g‖ ^ 2 ≤ (2 : ℝ) ^ d * t * ∫ x, ‖f x‖ := by
    rw [norm_L2_sq]
    have he : (fun x => ‖hg2.toLp g x‖ ^ 2) =ᵐ[volume] (fun x => ‖g x‖ ^ 2) :=
      hg2.coeFn_toLp.mono fun x hx => by simp only [hx]
    rw [integral_congr_ae he]
    exact (good_energy_bound f hf t ht Q g hdec).2
  have hTG : ‖G‖ ^ 2 ≤ ‖T‖ ^ 2 * ((2 : ℝ) ^ d * t * ∫ x, ‖f x‖) := by
    calc
      ‖G‖ ^ 2 ≤ (‖T‖ * ‖hg2.toLp g‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) _
      _ = ‖T‖ ^ 2 * ‖hg2.toLp g‖ ^ 2 := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left henergy (sq_nonneg _)
  have hgood : volume {x | t / 2 < ‖G x‖} ≤ ENNReal.ofReal (Gc / t) * eLpNorm f 1 volume := by
    apply (measure_norm_gt_le_L2 G (t / 2) (by positivity)).trans
    rw [eLpNorm_one_eq_integral_norm hf, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_div_of_nonneg_right hTG (sq_nonneg _)).trans_eq
    dsimp [Gc]
    field_simp
    ring
  have hregion : volume F ≤ ENNReal.ofReal (D / t) * eLpNorm f 1 volume := by
    calc
      volume F ≤ ∑' q : Q, volume (enlargedCube q.1) := measure_iUnion_le _
      _ ≤ ∑' q : Q, ENNReal.ofReal D * volume (CZ.cube q.1) :=
        ENNReal.tsum_le_tsum fun q => enlargedCube_volume_le q.1
      _ = ENNReal.ofReal D * ∑' q : Q, volume (CZ.cube q.1) := by rw [ENNReal.tsum_mul_left]
      _ ≤ ENNReal.ofReal D * (eLpNorm f 1 volume / ENNReal.ofReal t) :=
        mul_le_mul le_rfl hdec.measure_bound bot_le bot_le
      _ = ENNReal.ofReal (D / t) * eLpNorm f 1 volume := by
        rw [ENNReal.ofReal_div_of_pos ht]
        simp only [div_eq_mul_inv]
        ring
  have hbadlevel : (volume.restrict Fᶜ) {x | t / 2 < ‖B x‖} ≤
      ENNReal.ofReal (4 * (A : ℝ) / t) * eLpNorm f 1 volume := by
    apply (measure_norm_gt_le_one (volume.restrict Fᶜ) B (t / 2) (by positivity)).trans
    apply (mul_le_mul le_rfl hbad bot_le bot_le).trans_eq
    rw [← mul_assoc, ← ENNReal.ofReal_inv_of_pos (by positivity : 0 < t / 2)]
    rw [show 2 * (A : ℝ≥0∞) = ENNReal.ofReal (2 * (A : ℝ)) by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 2
    field_simp
    ring
  have he : T (h2.toLp f) = G + B := by
    dsimp [G, B]
    rw [← map_add]
    congr 1
    abel
  rw [he]
  apply (level_triangle G B t).trans
  apply (add_le_add hgood
    ((measure_level_le_region volume B (Lp.stronglyMeasurable B) (t / 2) F).trans
      (add_le_add hregion hbadlevel))).trans_eq
  rw [← add_assoc, ← add_mul, ← add_mul,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 2
  ring

/-- Assembly retains one uniform constant on the core and the full extension. -/
theorem weak_extension : Specs.P102.U2.CZWeakExtension.weak_extension := by
  obtain ⟨C, hC⟩ := weak_core
  refine ⟨fun d A N => 2 * C d A N, ?_⟩
  intro d hd T K A hK
  have hcore := hC d hd T K A hK
  obtain ⟨S, hS, hw, hc, ha, hu, hsum⟩ :=
    abstract_extension d T (C d A ‖T‖₊) (NNReal.coe_nonneg _) hcore
  have hcore' : CoreBound T (2 * (C d A ‖T‖₊ : ℝ)) :=
    coreBound_mono (by nlinarith [NNReal.coe_nonneg (C d A ‖T‖₊)]) hcore
  exact ⟨by simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using hcore',
    S, hS, by simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using hw, hc, ha, hu, hsum⟩

end P102.U2.CZWeakExtension
