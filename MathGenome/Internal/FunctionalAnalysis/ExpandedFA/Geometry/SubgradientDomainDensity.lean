import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.SubgradientDomainDensity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Geometry.BrondstedRockafellarApproximation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06FenchelMoreau

/-! Epsilon-subgradient existence and both norm-closure identities from
`fa2:p2:brondsted-rockafellar`. The range argument approximates the defining
primal supremum directly, so it does not pass to the bidual or assume reflexivity. -/
namespace ExpandedFA.Geometry.SubgradientDomainDensity

open Set
open ExpandedFA.P1.ExtendedConvexFunctions
open ExpandedFA.P1.C06Conjugates
open ExpandedFA.P1.C06FenchelMoreau
open ExpandedFA.BanachConvex
open ExpandedFA.Geometry.EpsilonSubgradient

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- An affine minorant close to the value at x is an epsilon-support at x.
Completeness is unnecessary for this existence statement. -/
lemma epsilonSubdifferential_nonempty_of_finite (φ : ExtendedFunction X)
    (hp : Proper X φ) (hl : LowerSemicontinuous X φ) (hc : ExtendedConvex X φ)
    (x : X) (hx : x ∈ finiteDomain X φ) (ε : ℝ) (hε : 0 < ε) :
    (epsilonSubdifferential X φ ε x).Nonempty := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hx
  obtain ⟨f, c, hm, hclose⟩ := ExpandedFA.P1.AffineMinorants.continuous_affine_minorant_above
    X φ hp hc hl x (r - ε) (by rw [← hr]; exact WithTop.coe_lt_coe.mpr (by linarith))
  refine ⟨f, (epsilonSubdifferential_iff_conjugate X φ ε x r hr.symm f).mpr ?_⟩
  exact (convexConjugate_le_of_affine_minorant φ f c hm).trans
    (EReal.coe_le_coe_iff.mpr (by linarith))

/-- At a finite conjugate value, a point close to the defining supremum
makes the given functional an epsilon-subgradient. -/
lemma exists_epsilonSubgradient_base (φ : ExtendedFunction X)
    (f : X →L[ℝ] ℝ) (s : ℝ) (hs : convexConjugate X φ f = (s : EReal))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ x : X, f ∈ epsilonSubdifferential X φ ε x := by
  have hlt : ((s - ε : ℝ) : EReal) < convexConjugate X φ f := by
    rw [hs, EReal.coe_lt_coe_iff]
    linarith
  obtain ⟨x, hx⟩ := lt_iSup_iff.mp hlt
  have hfinite : φ x ≠ ⊤ := by
    intro htop
    change ((s - ε : ℝ) : EReal) < (f x : EReal) - extendedRealValue (φ x) at hx
    rw [htop] at hx
    change ((s - ε : ℝ) : EReal) < (f x : EReal) - ⊤ at hx
    rw [EReal.sub_top] at hx
    exact not_lt_bot hx
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hreal : s - ε < f x - r := by
    change ((s - ε : ℝ) : EReal) < (f x : EReal) - extendedRealValue (φ x) at hx
    rw [← hr] at hx
    exact EReal.coe_lt_coe_iff.mp hx
  refine ⟨x, (epsilonSubdifferential_iff_conjugate X φ ε x r hr.symm f).mpr ?_⟩
  change convexConjugate X φ f ≤ _
  rw [hs, EReal.coe_le_coe_iff]
  linarith

theorem epsilonSubdifferential_nonempty : Spec.EpsilonNonempty.{u} := by
  intro X _ _ _ φ hp hl hc x hx ε hε
  exact epsilonSubdifferential_nonempty_of_finite φ hp hl hc x hx ε hε

theorem subgradientDomain_closure : Spec.DomainClosure.{u} := by
  intro X _ _ _ φ hp hl hc
  change closure (subgradientDomain X φ) = closure (finiteDomain X φ)
  apply le_antisymm
  · exact closure_mono (subgradientDomain_subset_finiteDomain X φ)
  · apply closure_minimal _ isClosed_closure
    intro x hx
    apply Metric.mem_closure_iff.mpr
    intro δ hδ
    obtain ⟨f, hf⟩ := epsilonSubdifferential_nonempty_of_finite φ hp hl hc
      x hx (δ / 2) (by linarith)
    obtain ⟨y, g, hg, hdist, _⟩ :=
      BrondstedRockafellarApproximation.brondsted_rockafellar_approximation
        X φ hp hl hc x f (δ / 2) (by linarith) hf 1 zero_lt_one
    refine ⟨y, ⟨g, hg⟩, ?_⟩
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt hdist (by simpa using (show δ / 2 < δ by linarith))

theorem subgradientRange_closure : Spec.RangeClosure.{u} := by
  intro X _ _ _ φ hp hl hc
  change closure {f : X →L[ℝ] ℝ | ∃ x, f ∈ subdifferential X φ x} =
    closure {f : X →L[ℝ] ℝ | ∃ r : ℝ, convexConjugate X φ f = (r : EReal)}
  apply le_antisymm
  · apply closure_mono
    rintro f ⟨x, hf⟩
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hf.1
    exact ⟨f x - r, (mem_subdifferential_iff_conjugate φ x r hr.symm f).mp hf⟩
  · apply closure_minimal _ isClosed_closure
    rintro f ⟨s, hs⟩
    apply Metric.mem_closure_iff.mpr
    intro δ hδ
    obtain ⟨x, hx⟩ := exists_epsilonSubgradient_base φ f s hs 1 zero_lt_one
    obtain ⟨y, g, hg, _, hdist⟩ :=
      BrondstedRockafellarApproximation.brondsted_rockafellar_approximation
        X φ hp hl hc x f 1 zero_lt_one hx (δ / 2) (by linarith)
    refine ⟨g, ⟨y, hg⟩, ?_⟩
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt hdist (by linarith)

end ExpandedFA.Geometry.SubgradientDomainDensity
