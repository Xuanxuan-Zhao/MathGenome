import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.IdealApproximateIdentities
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CStar.PositiveConeSquareRoots
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

noncomputable section
namespace ExpandedFA.CStar.IdealApproximateIdentities
universe u
open Filter Topology

/-- The star-closed part of an ideal can be used before star invariance is proved. -/
def starCore {A : Type u} [NonUnitalCStarAlgebra A]
    (I : Spec.ClosedTwoSidedIdeal A) : NonUnitalStarSubalgebra ℂ A where
  carrier := {x | x ∈ I ∧ star x ∈ I}
  zero_mem' := by simp [show (0 : A) ∈ I from I.toSubmodule.zero_mem]
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨I.toSubmodule.add_mem hx hy, by simpa using I.toSubmodule.add_mem hx' hy'⟩
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨I.mul_mem_left x y hy, by simpa using I.mul_mem_left (star y) (star x) hx'⟩
  smul_mem' := by
    rintro z x ⟨hx, hx'⟩
    exact ⟨I.toSubmodule.smul_mem z hx, by simpa using I.toSubmodule.smul_mem (star z) hx'⟩
  star_mem' := by rintro x ⟨hx, hx'⟩; exact ⟨hx', by simpa using hx⟩

instance starCore_isClosed {A : Type u} [NonUnitalCStarAlgebra A]
    (I : Spec.ClosedTwoSidedIdeal A) : IsClosed (starCore I : Set A) :=
  I.isClosed.inter (I.isClosed.preimage continuous_star)

/-- Control an adjoint error using only the positive square in the star core. -/
lemma adjoint_error_bound {A : Type u} [NonUnitalCStarAlgebra A]
    (a e : A) (he : IsSelfAdjoint e) (he1 : ‖e‖ ≤ 1) :
    ‖star a - e * star a‖ ^ 2 ≤ 2 * ‖star a * a - e * (star a * a)‖ := by
  have hid : (star a - e * star a) * star (star a - e * star a) =
      (star a * a - e * (star a * a)) - (star a * a - e * (star a * a)) * e := by
    simp only [star_sub, star_mul, star_star, he.star_eq]
    noncomm_ring
  rw [pow_two, ← CStarRing.norm_self_mul_star, hid]
  calc
    _ ≤ ‖star a * a - e * (star a * a)‖ +
        ‖(star a * a - e * (star a * a)) * e‖ := norm_sub_le _ _
    _ ≤ ‖star a * a - e * (star a * a)‖ +
        ‖star a * a - e * (star a * a)‖ * ‖e‖ :=
      add_le_add_right (norm_mul_le _ _) _
    _ ≤ _ := by nlinarith [norm_nonneg (star a * a - e * (star a * a))]

theorem star_invariant : Spec.StarInvariant.{u} := by
  intro A _ I a ha
  let S := starCore I
  let := CStarAlgebra.spectralOrder S
  let := CStarAlgebra.spectralOrderedRing S
  let b : S := ⟨star a * a, I.mul_mem_left (star a) a ha, by
    simpa only [star_mul, star_star, Spec.mem_toSubmodule] using I.mul_mem_left (star a) a ha⟩
  have hu := CStarAlgebra.increasingApproximateUnit S
  have ht : Tendsto (fun e : S => ‖b - e * b‖) (CStarAlgebra.approximateUnit S) (𝓝 0) := by
    simpa using ((hu.tendsto_mul_right b).const_sub b).norm
  change star a ∈ (I.toSubmodule : Set A)
  rw [← I.isClosed.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hδ : 0 < ε ^ 2 / 2 := by positivity
  obtain ⟨e, heδ, he1, heStar⟩ :=
    ((ht.eventually (gt_mem_nhds hδ)).and
      (hu.eventually_norm.and hu.eventually_isSelfAdjoint)).exists
  refine ⟨(e : A) * star a, I.mul_mem_right _ _ e.property.1, ?_⟩
  rw [dist_eq_norm]
  have h := adjoint_error_bound a (e : A) (by
    exact congrArg Subtype.val heStar.star_eq) he1
  change ‖star a * a - (e : A) * (star a * a)‖ < ε ^ 2 / 2 at heδ
  nlinarith [norm_nonneg (star a - (e : A) * star a)]

/-- Positivity of the star core is positivity in the original algebra. -/
lemma positive_coe_starCore {A : Type u} [NonUnitalCStarAlgebra A]
    (I : Spec.ClosedTwoSidedIdeal A) (e : starCore I)
    (he : Conventions.Spec.PositiveValue (starCore I) e) :
    Conventions.Spec.PositiveValue A (e : A) := by
  obtain ⟨x, hx⟩ := (PositiveConeSquareRoots.star_square_characterization (starCore I) e).mp he
  exact (PositiveConeSquareRoots.star_square_characterization A (e : A)).mpr
    ⟨(x : A), congrArg Subtype.val hx⟩

theorem finite_approximation : Spec.FiniteApproximation.{u} := by
  intro A _ I F ε hε
  let S := starCore I
  let := CStarAlgebra.spectralOrder S
  let := CStarAlgebra.spectralOrderedRing S
  let lift : I → S := fun a => ⟨a, a.property, star_invariant A I a a.property⟩
  have hu := CStarAlgebra.increasingApproximateUnit S
  have hF : ∀ᶠ e : S in CStarAlgebra.approximateUnit S,
      ∀ a ∈ F, ‖e * lift a - lift a‖ < ε ∧ ‖lift a * e - lift a‖ < ε := by
    apply (Filter.eventually_all_finset F).mpr
    intro a ha
    have hl := ((hu.tendsto_mul_right (lift a)).sub_const (lift a)).norm
    have hr := ((hu.tendsto_mul_left (lift a)).sub_const (lift a)).norm
    simp only [sub_self, norm_zero] at hl hr
    exact (hl.eventually (gt_mem_nhds hε)).and (hr.eventually (gt_mem_nhds hε))
  obtain ⟨e, he0, he1, heF⟩ :=
    (hu.eventually_nonneg.and (hu.eventually_norm.and hF)).exists
  refine ⟨(e : A), e.property.1, ?_, he1, ?_⟩
  · exact positive_coe_starCore I e ((PositiveConeSquareRoots.positive_iff_nonneg e).mpr he0)
  · intro a ha
    exact heF a ha

/-- A net indexed by finite sets and positive tolerances, with both error
bounds holding at every index, and both products converging in the original norm. -/
theorem approximate_identity : Spec.ApproximateIdentity.{u} := by
  classical
  intro A _ I
  have h : ∀ d : Spec.ApproximationIndex I,
      ∃ e : A, e ∈ I ∧ Conventions.Spec.PositiveValue A e ∧ ‖e‖ ≤ 1 ∧
        ∀ (a : I), a ∈ d.1 →
          ‖e * (a : A) - a‖ < ((OrderDual.ofDual d.2 : Set.Ioi (0 : ℝ)) : ℝ) ∧
          ‖(a : A) * e - a‖ < ((OrderDual.ofDual d.2 : Set.Ioi (0 : ℝ)) : ℝ) := by
    intro d
    exact finite_approximation A I d.1 _ (OrderDual.ofDual d.2).property
  choose e heI hepos he1 heF using h
  refine ⟨e, fun d => ⟨heI d, hepos d, he1 d⟩, heF, ?_⟩
  intro a
  constructor
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    let d₀ : Spec.ApproximationIndex I := ({a}, OrderDual.toDual ⟨ε, hε⟩)
    refine ⟨d₀, ?_⟩
    intro d hd
    have haF : a ∈ d.1 := hd.1 (Finset.mem_singleton_self a)
    have hεd : ((OrderDual.ofDual d.2 : Set.Ioi (0 : ℝ)) : ℝ) ≤ ε := hd.2
    simpa only [dist_eq_norm] using (heF d a haF).1.trans_le hεd
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    let d₀ : Spec.ApproximationIndex I := ({a}, OrderDual.toDual ⟨ε, hε⟩)
    refine ⟨d₀, ?_⟩
    intro d hd
    have haF : a ∈ d.1 := hd.1 (Finset.mem_singleton_self a)
    have hεd : ((OrderDual.ofDual d.2 : Set.Ioi (0 : ℝ)) : ℝ) ≤ ε := hd.2
    simpa only [dist_eq_norm] using (heF d a haF).2.trans_le hεd

end ExpandedFA.CStar.IdealApproximateIdentities
