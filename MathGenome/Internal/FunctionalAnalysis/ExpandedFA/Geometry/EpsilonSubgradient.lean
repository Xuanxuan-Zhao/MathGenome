import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.EpsilonSubgradient
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.SubgradientBasicCalculus

/-!
The epsilon-subgradient definition in paper.tex:12937–12943, on the shared
half-extended primal value space and continuous real-linear dual. The finite
base-value guard agrees with the canonical exact subdifferential. The norm
identity is the accepted earlier norm-subgradient theorem.
-/
namespace ExpandedFA.Geometry.EpsilonSubgradient

open ExpandedFA.P1.ExtendedConvexFunctions
open ExpandedFA.P1.C06Conjugates

universe u

/-- ∂_ε φ(x), empty outside the finite domain. This applies in particular to
proper lsc convex functions on real Banach spaces, without needing those
hypotheses merely to define the set. -/
def epsilonSubdifferential (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X) (ε : ℝ) (x : X) : Set (X →L[ℝ] ℝ) :=
  {f | x ∈ finiteDomain X φ ∧
    ∀ y : X, φ x + ((f (y - x) - ε : ℝ) : WithTop ℝ) ≤ φ y}

theorem epsilonSubdifferential_at_finite_value : Spec.AtFiniteValue.{u} := by
  intro X _ _ φ ε x r hx
  ext f
  change (φ x ≠ ⊤ ∧ ∀ y : X,
    φ x + ((f (y - x) - ε : ℝ) : WithTop ℝ) ≤ φ y) ↔
      ∀ y : X, ((r + f (y - x) - ε : ℝ) : WithTop ℝ) ≤ φ y
  rw [hx]
  simp only [← WithTop.coe_add, add_sub_assoc]
  exact and_iff_right WithTop.coe_ne_top

theorem epsilonSubdifferential_at_infinity : Spec.AtInfinity.{u} := by
  intro X _ _ φ ε x hx
  ext f
  simp [Spec.EpsilonSubdifferentialValue,
    ExpandedFA.P1.ExtendedConvexFunctions.Spec.finiteDomainValue, hx]

theorem epsilonSubdifferential_zero : Spec.AtZeroEpsilon.{u} := by
  intro X _ _ φ x
  ext f
  simp [Spec.EpsilonSubdifferentialValue, ExpandedFA.BanachConvex.Spec.SubdifferentialValue]

/-- Finite-valued competitors suffice, because all other right sides are +∞. -/
lemma mem_epsilonSubdifferential_iff_of_value
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X) (ε : ℝ) (x : X) (r : ℝ)
    (hx : φ x = (r : WithTop ℝ)) (f : X →L[ℝ] ℝ) :
    f ∈ epsilonSubdifferential X φ ε x ↔
      ∀ (y : X) (s : ℝ), φ y = (s : WithTop ℝ) → r + f (y - x) - ε ≤ s := by
  change f ∈ Spec.EpsilonSubdifferentialValue X φ ε x ↔ _
  rw [epsilonSubdifferential_at_finite_value X φ ε x r hx]
  change (∀ y : X, ((r + f (y - x) - ε : ℝ) : WithTop ℝ) ≤ φ y) ↔ _
  constructor
  · intro h y s hy
    simpa only [hy, WithTop.coe_le_coe] using h y
  · intro h y
    by_cases hy : φ y = ⊤
    · simp [hy]
    · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy
      simpa only [← hs, WithTop.coe_le_coe] using h y s hs.symm

theorem epsilonSubdifferential_iff_conjugate : Spec.ConjugateCriterion.{u} := by
  intro X _ _ φ ε x r hx f
  change f ∈ epsilonSubdifferential X φ ε x ↔
    convexConjugate X φ f ≤ ((f x - r + ε : ℝ) : EReal)
  rw [mem_epsilonSubdifferential_iff_of_value φ ε x r hx f]
  constructor
  · intro h
    apply (convexConjugate_isLUB X φ f).2
    rintro _ ⟨y, rfl⟩
    by_cases hy : φ y = ⊤
    · change (f y : EReal) - extendedRealValue (φ y) ≤ _
      rw [hy]
      change (f y : EReal) - ⊤ ≤ _
      rw [EReal.sub_top]
      exact bot_le
    · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy
      change (f y : EReal) - extendedRealValue (φ y) ≤ _
      rw [← hs]
      change (f y : EReal) - (s : EReal) ≤ _
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
      have hh := h y s hs.symm
      rw [map_sub] at hh
      linarith
  · intro h y s hy
    have hh : (f y : EReal) - extendedRealValue (φ y) ≤ convexConjugate X φ f :=
      (convexConjugate_isLUB X φ f).1 ⟨y, rfl⟩
    have hb := hh.trans h
    rw [hy] at hb
    change (f y : EReal) - (s : EReal) ≤ ((f x - r + ε : ℝ) : EReal) at hb
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at hb
    rw [map_sub]
    linarith

theorem norm_subdifferential_zero : Spec.NormAtZero.{u} :=
  ExpandedFA.BanachConvex.norm_subdifferential_zero

end ExpandedFA.Geometry.EpsilonSubgradient
