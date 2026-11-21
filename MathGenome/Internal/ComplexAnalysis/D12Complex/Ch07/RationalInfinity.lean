import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.RationalInfinity
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.LocalQuotientsArithmetic
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.Sphere
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Tauto

noncomputable section
open Filter Set
open scoped Topology
namespace D12Complex.RationalInfinity
open D12Complex.LocalQuotientsArithmetic hiding fill
open Specs.D12Complex.Ch07.LocalQuotientsArithmetic.Objects (fill)

/-- The rational expression, whose arbitrary values at denominator zeros are filled below. -/
def rational (P Q : Polynomial ℂ) (z : ℂ) : ℂ := P.eval z / Q.eval z

/-- Fill the rational expression in the finite and reciprocal source coordinates. -/
def extension (P Q : Polynomial ℂ) : RiemannSphere → RiemannSphere :=
  fun p => OnePoint.elim p (fill (reciprocalPullback (rational P Q)) 0)
    (fill (rational P Q))

/-- A zero of exact positive order in the reciprocal coordinate, with a holomorphic unit. -/
def ZeroOfOrderAtInfinity (f : ℂ → ℂ) (m : ℕ) : Prop :=
  1 ≤ m ∧ IsolatedSingularityAtInfinity f ∧
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ, HolomorphicOn (Metric.ball 0 r) g ∧
      g 0 ≠ 0 ∧ ∀ w ∈ puncturedDisk 0 r, f w⁻¹ = w ^ m * g w

private theorem reverse_eval (P : Polynomial ℂ) {w : ℂ} (hw : w ≠ 0) :
    P.eval w⁻¹ = P.reverse.eval w / w ^ P.natDegree := by
  let : Invertible w⁻¹ := invertibleOfNonzero (inv_ne_zero hw)
  have h := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) w⁻¹ P
  simp only [invOf_eq_inv, inv_inv, Polynomial.eval₂_id] at h
  rw [← h, inv_pow, div_eq_mul_inv]

private theorem reciprocal_formula (P Q : Polynomial ℂ) :
    reciprocalPullback (rational P Q) =ᶠ[𝓝[≠] 0]
      (fun w => w ^ ((Q.natDegree : ℤ) - (P.natDegree : ℤ)) *
        (P.reverse.eval w / Q.reverse.eval w)) := by
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw : w ≠ 0 := hw
  simp only [reciprocalPullback, rational, reverse_eval P hw, reverse_eval Q hw,
    zpow_sub₀ hw, zpow_natCast]
  field_simp

private theorem reversed_unit (P Q : Polynomial ℂ) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    AnalyticAt ℂ (fun w => P.reverse.eval w / Q.reverse.eval w) 0 ∧
      P.reverse.eval 0 / Q.reverse.eval 0 ≠ 0 := by
  have hp : P.reverse.eval 0 = P.leadingCoeff := by rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse]
  have hq : Q.reverse.eval 0 = Q.leadingCoeff := by rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse]
  refine ⟨(AnalyticOnNhd.eval_polynomial P.reverse 0 (mem_univ _)).div (AnalyticOnNhd.eval_polynomial Q.reverse 0 (mem_univ _)) ?_, ?_⟩
  · simpa [hq] using Polynomial.leadingCoeff_ne_zero.mpr hQ
  · rw [hp, hq]
    exact div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP)
      (Polynomial.leadingCoeff_ne_zero.mpr hQ)

private theorem reciprocal_meromorphic (P Q : Polynomial ℂ) :
    MeromorphicAt (reciprocalPullback (rational P Q)) 0 := by
  apply MeromorphicAt.congr _ (reciprocal_formula P Q).symm
  exact (((analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) 0).meromorphicAt).zpow _).mul
    ((AnalyticOnNhd.eval_polynomial P.reverse 0 (mem_univ _)).meromorphicAt.div (AnalyticOnNhd.eval_polynomial Q.reverse 0 (mem_univ _)).meromorphicAt)

theorem order_at_infinity (P Q : Polynomial ℂ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (_hrel : IsRelPrime P Q) :
    meromorphicOrderAt (reciprocalPullback (rational P Q)) 0 =
      ((Q.natDegree : ℤ) - (P.natDegree : ℤ) : WithTop ℤ) := by
  obtain ⟨hu, hu0⟩ := reversed_unit P Q hP hQ
  apply (meromorphicOrderAt_eq_int_iff (reciprocal_meromorphic P Q)).mpr
  exact ⟨_, hu, hu0, by simpa [Filter.EventuallyEq, sub_zero, smul_eq_mul] using reciprocal_formula P Q⟩

private theorem rational_meromorphic (P Q : Polynomial ℂ) (a : ℂ) :
    MeromorphicAt (rational P Q) a :=
  (AnalyticOnNhd.eval_polynomial P a (mem_univ _)).meromorphicAt.div
    (AnalyticOnNhd.eval_polynomial Q a (mem_univ _)).meromorphicAt

private theorem reciprocal_meromorphic_all (P Q : Polynomial ℂ) (a : ℂ) :
    MeromorphicAt (reciprocalPullback (rational P Q)) a := by
  by_cases ha : a = 0
  · subst a; exact reciprocal_meromorphic P Q
  · exact (rational_meromorphic P Q a⁻¹).comp_analyticAt
      (analyticAt_id.inv ha)

private theorem fill_comp_inv (f : ℂ → ℂ) {w : ℂ} (hw : w ≠ 0)
    (hf : MeromorphicAt f w⁻¹) :
    fill (fun z => f z⁻¹) w = fill f w⁻¹ := by
  have hi : AnalyticAt ℂ (fun z : ℂ => z⁻¹) w := analyticAt_id.inv hw
  have hd : deriv (fun z : ℂ => z⁻¹) w ≠ 0 := by
    rw [(hasDerivAt_inv hw).deriv]
    exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hw))
  have ht := (hasDerivAt_inv hw).tendsto_nhdsNE
    (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hw)))
  have he := hf.eq_nhdsNE_toMeromorphicNFAt.comp_tendsto ht
  rw [fill_congr (f := fun z => f z⁻¹) (g := fun z => toMeromorphicNFAt f w⁻¹ z⁻¹) w he]
  have hnf : MeromorphicNFAt (fun z => toMeromorphicNFAt f w⁻¹ z⁻¹) w :=
    meromorphicNFAt_toMeromorphicNFAt.comp_analyticAt hi
  have ho : meromorphicOrderAt (fun z => toMeromorphicNFAt f w⁻¹ z⁻¹) w =
      meromorphicOrderAt f w⁻¹ := by
    rw [show (fun z => toMeromorphicNFAt f w⁻¹ z⁻¹) =
      (toMeromorphicNFAt f w⁻¹) ∘ (fun z : ℂ => z⁻¹) from rfl,
      meromorphicOrderAt_comp_of_deriv_ne_zero hi hd,
      hf.meromorphicOrderAt_toMeromorphicNFAt]
  simp only [fill, ho, toMeromorphicNFAt_eq_self.mpr hnf]

private theorem infinity_expression (P Q : Polynomial ℂ) :
    extension P Q ∘ infinityParametrization = fill (reciprocalPullback (rational P Q)) := by
  funext w
  by_cases hw : w = 0
  · subst w; simp [extension, _root_.D12Complex.infinityParametrization, sphereInfty]
  · simp only [Function.comp_def, infinityParametrization, hw, ↓reduceIte, extension,
      sphereFinite]
    exact (fill_comp_inv (rational P Q) hw (rational_meromorphic P Q w⁻¹)).symm

theorem meromorphic_extension (P Q : Polynomial ℂ) (_hQ : Q ≠ 0) :
    ScalarMeromorphicOnSphere univ (extension P Q) ∧
    ∀ z : ℂ, Q.eval z ≠ 0 → extension P Q (sphereFinite z) =
      sphereFinite (P.eval z / Q.eval z) := by
  constructor
  · refine ⟨isOpen_univ, ?_, ?_⟩
    · change ScalarMeromorphicOn univ (fill (rational P Q))
      exact scalarMeromorphicOn_fill univ isOpen_univ _ (fun a _ => rational_meromorphic P Q a)
    · rw [infinity_expression]
      exact scalarMeromorphicOn_fill univ isOpen_univ _
        (fun a _ => reciprocal_meromorphic_all P Q a)
  · intro z hz
    exact fill_of_analyticAt ((AnalyticOnNhd.eval_polynomial P z (mem_univ _)).div
      (AnalyticOnNhd.eval_polynomial Q z (mem_univ _)) hz)

theorem sphere_order_at_infinity (P Q : Polynomial ℂ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hrel : IsRelPrime P Q) :
    sphereScalarSignedOrder (extension P Q) sphereInfty =
      some ((Q.natDegree : ℤ) - (P.natDegree : ℤ)) := by
  rw [sphereScalarSignedOrder_infty]
  change meromorphicOrderAt (scalarFinitePart (extension P Q ∘ infinityParametrization)) 0 =
    (((Q.natDegree : ℤ) - (P.natDegree : ℤ) : ℤ) : WithTop ℤ)
  rw [infinity_expression]
  exact (meromorphicOrderAt_congr (finitePart_fill_germ (reciprocal_meromorphic P Q))).trans
    (order_at_infinity P Q hP hQ hrel)

theorem infinity_values (P Q : Polynomial ℂ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hrel : IsRelPrime P Q) :
    (Q.natDegree < P.natDegree → extension P Q sphereInfty = sphereInfty) ∧
    (P.natDegree < Q.natDegree → extension P Q sphereInfty = sphereFinite 0) := by
  have ho := order_at_infinity P Q hP hQ hrel
  change (Q.natDegree < P.natDegree → fill _ 0 = _) ∧
    (P.natDegree < Q.natDegree → fill _ 0 = _)
  constructor
  · intro hdeg
    have hn : meromorphicOrderAt (reciprocalPullback (rational P Q)) 0 < 0 := by
      rw [ho]
      exact_mod_cast (sub_neg.mpr (by exact_mod_cast hdeg : (Q.natDegree : ℤ) < P.natDegree))
    simp only [fill, ite_eq_left hn]
  · intro hdeg
    have hn : 0 < meromorphicOrderAt (reciprocalPullback (rational P Q)) 0 := by
      rw [ho]
      exact_mod_cast (sub_pos.mpr (by exact_mod_cast hdeg : (P.natDegree : ℤ) < Q.natDegree))
    simp only [fill, ite_eq_right (not_lt.mpr hn.le),
      toMeromorphicNFAt_of_meromorphicOrderAt_ne_zero hn.ne']

private theorem isolated_of_meromorphic {f : ℂ → ℂ} (hf : MeromorphicAt f 0) :
    IsolatedSingularityAt f 0 := by
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp hf.eventually_analyticAt)
  refine ⟨r, hr, ?_, fun w hw => (hb ?_ ?_).differentiableAt⟩
  · have he : puncturedDisk 0 r = Metric.ball 0 r \ {0} := by
      ext z; simp [puncturedDisk, Metric.mem_ball, norm_pos_iff, dist_eq_norm]; tauto
    rw [he]; exact Metric.isOpen_ball.sdiff isClosed_singleton
  · simpa [dist_eq_norm] using hw.2
  · simpa [mem_compl_iff, mem_singleton_iff] using norm_pos_iff.mp (by simpa using hw.1)

private theorem removable_of_extension {f g : ℂ → ℂ} (hf : MeromorphicAt f 0)
    (hg : AnalyticAt ℂ g 0) (he : f =ᶠ[𝓝[≠] 0] g) : RemovableSingularityAt f 0 := by
  have hd := hg.eventually_analyticAt.mono (fun _ h => h.differentiableAt)
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp
    (hd.and (eventually_nhdsWithin_iff.mp he))
  refine ⟨isolated_of_meromorphic hf, r, hr, g, ⟨Metric.isOpen_ball,
    fun z hz => (hb (Metric.mem_ball.mp hz)).1⟩, ?_⟩
  intro w hw
  exact (hb (by simpa [dist_eq_norm] using hw.2)).2
    (by simpa using norm_pos_iff.mp (by simpa using hw.1))

theorem pole_at_infinity (P Q : Polynomial ℂ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hrel : IsRelPrime P Q) (hdeg : Q.natDegree < P.natDegree) :
    PoleOfOrderAtInfinity (rational P Q) (P.natDegree - Q.natDegree) := by
  apply poleOfOrder_of_order (reciprocal_meromorphic P Q) _ (by omega)
  rw [order_at_infinity P Q hP hQ hrel]
  have he : -((P.natDegree - Q.natDegree : ℕ) : ℤ) =
      (Q.natDegree : ℤ) - (P.natDegree : ℤ) := by omega
  exact_mod_cast he.symm

theorem zero_at_infinity (P Q : Polynomial ℂ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (_hrel : IsRelPrime P Q) (hdeg : P.natDegree < Q.natDegree) :
    ZeroOfOrderAtInfinity (rational P Q) (Q.natDegree - P.natDegree) := by
  obtain ⟨hu, hu0⟩ := reversed_unit P Q hP hQ
  have he : reciprocalPullback (rational P Q) =ᶠ[𝓝[≠] 0]
      (fun w => w ^ (Q.natDegree - P.natDegree) * (P.reverse.eval w / Q.reverse.eval w)) := by
    simpa [← Int.ofNat_sub (by omega : P.natDegree ≤ Q.natDegree), zpow_natCast]
      using reciprocal_formula P Q
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp
    ((hu.eventually_analyticAt.mono (fun _ h => h.differentiableAt)).and
      (eventually_nhdsWithin_iff.mp he))
  refine ⟨by omega, isolated_of_meromorphic (reciprocal_meromorphic P Q),
    r, hr, _, ⟨Metric.isOpen_ball, fun z hz => (hb (Metric.mem_ball.mp hz)).1⟩, hu0, ?_⟩
  intro w hw
  exact (hb (by simpa [dist_eq_norm] using hw.2)).2
    (by simpa using norm_pos_iff.mp (by simpa using hw.1))

theorem value_at_infinity (P Q : Polynomial ℂ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (_hrel : IsRelPrime P Q) (hdeg : P.natDegree = Q.natDegree) :
    RemovableSingularityAtInfinity (rational P Q) ∧
    Tendsto (reciprocalPullback (rational P Q)) (𝓝[≠] 0)
      (𝓝 (P.leadingCoeff / Q.leadingCoeff)) ∧
    extension P Q sphereInfty = sphereFinite (P.leadingCoeff / Q.leadingCoeff) ∧
    P.leadingCoeff / Q.leadingCoeff ≠ 0 := by
  obtain ⟨hu, hu0⟩ := reversed_unit P Q hP hQ
  have he : reciprocalPullback (rational P Q) =ᶠ[𝓝[≠] 0]
      (fun w => P.reverse.eval w / Q.reverse.eval w) := by
    simpa [hdeg] using reciprocal_formula P Q
  have hval : P.reverse.eval 0 / Q.reverse.eval 0 = P.leadingCoeff / Q.leadingCoeff := by
    simp only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse]
  refine ⟨removable_of_extension (reciprocal_meromorphic P Q) hu he, ?_, ?_, ?_⟩
  · rw [← hval]; exact hu.continuousAt.continuousWithinAt.tendsto.congr' he.symm
  · change fill (reciprocalPullback (rational P Q)) 0 = _
    exact (fill_congr _ _ 0 he).trans ((fill_of_analyticAt hu).trans (congrArg sphereFinite hval))
  · rwa [← hval]

theorem zero_rational (Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    extension 0 Q = (fun _ => sphereFinite 0) ∧
    ScalarMeromorphicOnSphere univ (extension 0 Q) ∧
    RemovableSingularityAtInfinity (rational 0 Q) := by
  have hr : rational 0 Q = fun _ => 0 := by funext z; simp [rational]
  have hi : reciprocalPullback (rational 0 Q) = fun _ => 0 := by funext z; simp only [_root_.D12Complex.reciprocalPullback, hr]
  refine ⟨?_, (meromorphic_extension 0 Q hQ).1, ?_⟩
  · funext p
    induction p using OnePoint.rec with
    | infty => exact (congrArg (fun f => fill f 0) hi).trans (fill_of_analyticAt analyticAt_const)
    | coe z => exact (congrArg (fun f => fill f z) hr).trans (fill_of_analyticAt analyticAt_const)
  · exact removable_of_extension (reciprocal_meromorphic 0 Q) analyticAt_const (Filter.Eventually.of_forall (congrFun hi))

end D12Complex.RationalInfinity
