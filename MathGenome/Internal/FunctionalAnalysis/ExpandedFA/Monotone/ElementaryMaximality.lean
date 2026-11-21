import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Monotone.ElementaryMaximality
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Monotone.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.WeakVariants.UnboundedAdjointClosures
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C08ClosedGraph
import Mathlib.Algebra.QuadraticDiscriminant

/-! The adjoint identities are assembled from the authorized adjoint-closure
module. For maximality, closed inequalities of the evaluation pairing give
graph closedness; Hahn–Banach double annihilation gives domain density.
The full-domain argument uses the discriminant of the quadratic obtained by
testing a related pair at x + t v, then applies the closed graph theorem. -/

noncomputable section
namespace ExpandedFA.Monotone.ElementaryMaximality
universe u v w
open ExpandedFA.Unbounded

theorem weakStar_range_closure : Spec.WeakStarRangeClosure.{u,v,w} :=
  ExpandedFA.WeakVariants.UnboundedAdjointClosures.weakStar_range_closure
theorem weakStar_domain_closure : Spec.WeakStarDomainClosure.{u,v,w} :=
  ExpandedFA.WeakVariants.UnboundedAdjointClosures.weakStar_domain_closure
theorem norm_range_closure : Spec.NormRangeClosure.{u,v,w} :=
  ExpandedFA.WeakVariants.UnboundedAdjointClosures.norm_range_closure
theorem norm_domain_closure : Spec.NormDomainClosure.{u,v,w} :=
  ExpandedFA.WeakVariants.UnboundedAdjointClosures.norm_domain_closure

/-- Each inequality defining the monotonically related pairs is norm closed. -/
theorem maximalMonotone_isClosed {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {G : Set (X × (X →L[ℝ] ℝ))}
    (hG : Monotone.Spec.MaximalMonotoneValue X G) : IsClosed G := by
  obtain ⟨hmono, hmax⟩ := (maximalMonotone_iff_related X G).mp hG
  apply isClosed_of_closure_subset
  rintro ⟨x, f⟩ hp
  apply hmax x f
  intro y g hyg
  have hc : IsClosed {p : X × (X →L[ℝ] ℝ) | 0 ≤ (p.2 - g) (p.1 - y)} :=
    isClosed_le continuous_const
      ((continuous_snd.sub continuous_const).clm_apply (continuous_fst.sub continuous_const))
  change (x, f) ∈ {p : X × (X →L[ℝ] ℝ) | 0 ≤ (p.2 - g) (p.1 - y)}
  apply hc.closure_subset
  exact closure_mono (fun p hp => hmono hp hyg) hp

theorem maximal_closed : Spec.MaximalClosed.{u} := by
  intro X _ _ B hB
  exact maximalMonotone_isClosed hB

theorem maximal_dense : Spec.MaximalDense.{u} := by
  intro X _ _ B hB
  obtain ⟨hmono, hmax⟩ := (maximalMonotone_iff_related X _).mp hB
  have hann (f : X →L[ℝ] ℝ) (hf : ∀ x ∈ B.domain, f x = 0) : f = 0 := by
    have hrelated : ∀ y g, (y, g) ∈ Monotone.Spec.LinearGraphValue X B →
        0 ≤ (f - g) (0 - y) := by
      intro y g hyg
      obtain ⟨hy, rfl⟩ := (mem_linearGraph X B y g).mp hyg
      have hpos := (linearMonotone_iff_positive X B).mp hmono ⟨y, hy⟩
      simpa only [zero_sub, map_neg, sub_apply, hf y hy, zero_sub, neg_neg] using hpos
    have hmem := hmax 0 f hrelated
    obtain ⟨h0, heq⟩ := (mem_linearGraph X B 0 f).mp hmem
    have hz : (⟨0, h0⟩ : B.domain) = 0 := Subtype.ext rfl
    simpa only [hz, B.map_zero] using heq.symm
  rw [dense_iff_closure_eq, ← ExpandedFA.P1.C06DoubleAnnihilator.double_annihilator_primal
    ℝ X B.domain]
  ext x
  change (∀ f : X →L[ℝ] ℝ, (∀ y ∈ B.domain, f y = 0) → f x = 0) ↔ True
  constructor
  · intro _; trivial
  · intro _ f hf
    rw [hann f hf]
    rfl

theorem everywhere_maximal : Spec.EverywhereMaximal.{u} := by
  intro X _ _ B hB
  apply (maximalMonotone_iff_related X _).mpr
  refine ⟨(monotone_graphOfMap_iff X B).mpr hB, ?_⟩
  intro x f hrel
  change f = B x
  ext v
  have hpoly (t : ℝ) :
      0 ≤ (B v v) * (t * t) + ((B x - f) v) * t + 0 := by
    have h := hrel (x + t • v) (B (x + t • v)) rfl
    simp only [map_add, map_smul, sub_apply, _root_.add_apply, _root_.smul_apply,
      smul_eq_mul, map_sub] at h
    simp only [sub_apply]
    nlinarith
  have hd := discrim_le_zero hpoly
  simp only [discrim, mul_zero, sub_zero] at hd
  have he : (B x - f) v = 0 := by nlinarith [sq_nonneg ((B x - f) v)]
  exact (sub_eq_zero.mp he).symm

theorem everywhere_bounded : Spec.EverywhereBounded.{u} := by
  intro X _ _ _ B hB
  have hc := maximalMonotone_isClosed (everywhere_maximal X B hB)
  apply (ExpandedFA.P1.C08ClosedGraph.closed_graph ℝ X (X →L[ℝ] ℝ) B).mpr
  exact (ExpandedFA.P1.C08ClosedGraph.sum_product_geometry X (X →L[ℝ] ℝ)).2 _ |>.mpr hc

end ExpandedFA.Monotone.ElementaryMaximality
