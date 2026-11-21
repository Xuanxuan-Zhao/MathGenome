import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06FenchelMoreau
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06Conjugates
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.AffineMinorants

/-! Fenchel inequality and Fenchel–Moreau, paper.tex:1287–1344.
The affine-minorant results imported above are proved prerequisites.
No completeness, interior-domain, or finite-valuedness hypothesis is used. -/
namespace ExpandedFA.P1.C06FenchelMoreau

open ExpandedFA.P1.ExtendedConvexFunctions
open ExpandedFA.P1.C06Conjugates ExpandedFA.P1.AffineMinorants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite upper bound on the supremum is a family of ordinary real
inequalities on the finite domain. Infinite input values impose no constraint. -/
theorem convexConjugate_le_real_iff (φ : ExtendedFunction E)
    (f : E →L[ℝ] ℝ) (r : ℝ) :
    convexConjugate E φ f ≤ (r : EReal) ↔
      ∀ (x : E) (s : ℝ), φ x = (s : WithTop ℝ) → f x - s ≤ r := by
  unfold convexConjugate
  rw [iSup_le_iff]
  constructor
  · intro h x s hs
    have hx := h x
    rw [hs] at hx
    exact EReal.coe_le_coe_iff.mp hx
  · intro h x
    by_cases hx : φ x = ⊤
    · rw [hx]
      change (f x : EReal) - ⊤ ≤ (r : EReal)
      rw [EReal.sub_top]
      exact bot_le
    · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hx
      rw [← hs]
      exact EReal.coe_le_coe_iff.mpr (h x s hs.symm)

theorem fenchel_inequality : Spec.FenchelInequality := by
  intro E _ _ φ hp x f
  change (f x : EReal) ≤ extendedRealValue (φ x) + convexConjugate E φ f
  have h := le_iSup (fun y => (f y : EReal) - extendedRealValue (φ y)) x
  rw [add_comm]
  exact (EReal.sub_le_iff_le_add
    (Or.inl (extendedRealValue_conventions.2.2.1 (φ x)))
    (Or.inr (convexConjugate_ne_bot E φ hp f))).mp h

/-- An affine minorant produces a finite upper bound for the conjugate. -/
theorem convexConjugate_le_of_affine_minorant (φ : ExtendedFunction E)
    (h : E →L[ℝ] ℝ) (c : ℝ) (hm : IsContinuousAffineMinorant φ h c) :
    convexConjugate E φ h ≤ ((-c : ℝ) : EReal) := by
  rw [convexConjugate_le_real_iff]
  intro y s hs
  have hh : h y + c ≤ s := WithTop.coe_le_coe.mp (by simpa [hs] using hm y)
  linarith

theorem convexConjugate_proper : Spec.ConjugateProper := by
  intro E _ _ φ hp hc hl
  refine ⟨convexConjugate_ne_bot E φ hp, ?_⟩
  obtain ⟨h, c, hm⟩ := exists_continuous_affine_minorant E φ hp hc hl
  have htop : convexConjugate E φ h ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (convexConjugate_le_of_affine_minorant φ h c hm)
  exact ⟨h, (convexConjugate E φ h).toReal,
    (EReal.coe_toReal htop (convexConjugate_ne_bot E φ hp h)).symm⟩

theorem convexConjugate_convex : Spec.ConjugateConvex := by
  intro E _ _ φ _ f g r s a b hf hg ha hb hab
  change convexConjugate E φ (a • f + b • g) ≤ _
  rw [convexConjugate_le_real_iff]
  intro x t ht
  have hfx : f x - t ≤ r := (convexConjugate_le_real_iff φ f r).mp hf.le x t ht
  have hgx : g x - t ≤ s := (convexConjugate_le_real_iff φ g s).mp hg.le x t ht
  simp only [add_apply, smul_apply, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left hfx ha, mul_le_mul_of_nonneg_left hgx hb,
    congrArg (fun z : ℝ => z * t) hab]

theorem convexConjugate_weakStar_lowerSemicontinuous :
    Spec.ConjugateWeakStarLowerSemicontinuous := by
  intro E _ _ φ _ r
  change IsClosed {f : WeakDual ℝ E |
    convexConjugate E φ (WeakDual.toStrongDual f) ≤ (r : EReal)}
  have heval (x : E) : Continuous (fun f : WeakDual ℝ E => f x) :=
    WeakDual.eval_continuous x
  have heq : {f : WeakDual ℝ E |
      convexConjugate E φ (WeakDual.toStrongDual f) ≤ (r : EReal)} =
      ⋂ (x : E) (s : ℝ) (_ : φ x = (s : WithTop ℝ)), {f | f x - s ≤ r} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, convexConjugate_le_real_iff,
      WeakDual.toStrongDual_apply]
  rw [heq]
  exact isClosed_iInter fun x => isClosed_iInter fun s =>
    isClosed_iInter fun _ => isClosed_le ((heval x).sub continuous_const) continuous_const

/-- The supremum of affine minorants gives the lower inequality even at +∞. -/
theorem fenchel_moreau : Spec.BiconjugateEquality := by
  intro E _ _ φ hp hc hl x
  change convexBiconjugate E φ x = extendedRealValue (φ x)
  apply le_antisymm
  · unfold convexBiconjugate
    apply iSup_le
    intro f
    exact EReal.sub_le_of_le_add (fenchel_inequality E φ hp x f)
  · by_contra hn
    obtain ⟨t, hbt, htf⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
    have ht : (t : WithTop ℝ) < φ x := WithBot.coe_lt_coe.mp htf
    obtain ⟨h, c, hm, htc⟩ := continuous_affine_minorant_above E φ hp hc hl x t ht
    have hbound := convexConjugate_le_of_affine_minorant φ h c hm
    have hle : ((h x + c : ℝ) : EReal) ≤ convexBiconjugate E φ x := by
      calc
        ((h x + c : ℝ) : EReal) = (h x : EReal) - ((-c : ℝ) : EReal) := by
          rw [← EReal.coe_sub]; congr 1; ring
        _ ≤ (h x : EReal) - convexConjugate E φ h := EReal.sub_le_sub le_rfl hbound
        _ ≤ convexBiconjugate E φ x :=
          le_iSup (fun f : E →L[ℝ] ℝ => (f x : EReal) - convexConjugate E φ f) h
    exact (not_lt_of_ge hle) (hbt.trans (EReal.coe_lt_coe_iff.mpr htc))

end ExpandedFA.P1.C06FenchelMoreau
