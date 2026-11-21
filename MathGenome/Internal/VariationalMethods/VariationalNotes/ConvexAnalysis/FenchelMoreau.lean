import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.Conjugates
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.FenchelMoreau
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.FenchelMoreauLcs

noncomputable section
universe u
namespace VariationalNotes.ConvexAnalysis

variable {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]

/-- The finite-domain and unrestricted conjugates agree, including their
infinite terms. Both use the continuous dual of the same topology. -/
theorem conjugate_eq_lcs (f : X → WithTop ℝ) (y : X →L[ℝ] ℝ) :
    conjugate f y = ExpandedFA.P1.FenchelMoreauLcs.convexConjugate X f y := by
  exact conjugate_eq_iSup_sub f y

theorem biconjugate_eq_lcs (f : X → WithTop ℝ) (x : X) :
    biconjugate f x = ExpandedFA.P1.FenchelMoreauLcs.convexBiconjugate X f x := by
  change (⨆ y : X →L[ℝ] ℝ, (y x : EReal) - Specs.conjugate f y) = _
  unfold ExpandedFA.P1.FenchelMoreauLcs.convexBiconjugate
  congr 1
  funext y
  rw [← conjugate_eq_lcs f y]
  rfl

omit [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] in
private theorem proper_lcs (f : X → WithTop ℝ) (h : Proper f) :
    ExpandedFA.P1.ExtendedConvexFunctions.Proper X f := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, ne_of_lt hx⟩

omit [TopologicalSpace X] in
private theorem convex_lcs (f : X → WithTop ℝ) (h : IsConvex f) :
    ExpandedFA.P1.ExtendedConvexFunctions.ExtendedConvex X f :=
  (ExpandedFA.P1.ExtendedConvexFunctions.convex_iff_convex_epigraph X f).mpr h

omit [AddCommGroup X] [Module ℝ X] in
private theorem lsc_lcs (f : X → WithTop ℝ) (h : IsLowerSemicontinuous f) :
    ExpandedFA.P1.ExtendedConvexFunctions.LowerSemicontinuous X f :=
  (lowerSemicontinuous_iff_closed_sublevels f).mp h

theorem fenchel_moreau : Specs.fenchel_moreau.{u} := by
  intro X _ _ _ _ _ _ _ f hp hc hl x
  rw [show Specs.biconjugate f x = ExpandedFA.P1.FenchelMoreauLcs.convexBiconjugate X f x from
    biconjugate_eq_lcs f x]
  exact (ExpandedFA.P1.FenchelMoreauLcs.fenchel_moreau X f
    (proper_lcs f hp) (convex_lcs f hc) (lsc_lcs f hl) x).symm

theorem exists_affine_minorant : Specs.exists_affine_minorant.{u} := by
  intro X _ _ _ _ _ _ _ f hp hc hl
  exact ExpandedFA.P1.FenchelMoreauLcs.exists_continuous_affine_minorant f
    (proper_lcs f hp) (convex_lcs f hc) (lsc_lcs f hl)

theorem affine_minorant_representation : Specs.affine_minorant_representation.{u} := by
  intro X _ _ _ _ _ _ _ f hp hc hl x
  apply le_antisymm
  · by_contra hn
    obtain ⟨t, hst, htf⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
    have ht : (t : WithTop ℝ) < f x := WithBot.coe_lt_coe.mp htf
    obtain ⟨y, b, hm, htx⟩ := ExpandedFA.P1.FenchelMoreauLcs.continuous_affine_minorant_above f
      (proper_lcs f hp) (convex_lcs f hc) (lsc_lcs f hl) x t ht
    have hle : ((y x + b : ℝ) : EReal) ≤
        ⨆ (y : X →L[ℝ] ℝ) (b : ℝ)
          (_ : ∀ z, ((y z + b : ℝ) : WithTop ℝ) ≤ f z), ((y x + b : ℝ) : EReal) :=
      le_iSup_of_le y (le_iSup_of_le b (le_iSup_of_le hm le_rfl))
    exact (not_lt_of_ge hle) (hst.trans (EReal.coe_lt_coe_iff.mpr htx))
  · apply iSup_le
    intro y
    apply iSup_le
    intro b
    apply iSup_le
    intro hm
    exact WithBot.coe_le_coe.mpr (hm x)

theorem conjugate_proper : Specs.conjugate_proper.{u} := by
  intro X _ _ _ _ _ _ _ f hp hc hl
  refine ⟨conjugate_ne_bot f hp, ?_⟩
  obtain ⟨y, b, hm⟩ := exists_affine_minorant f hp hc hl
  have hbound : ExpandedFA.P1.FenchelMoreauLcs.convexConjugate X f y ≤ ((-b : ℝ) : EReal) := by
    apply (ExpandedFA.P1.FenchelMoreauLcs.convexConjugate_le_real_iff f y (-b)).mpr
    intro z s hs
    have hz : y z + b ≤ s := WithTop.coe_le_coe.mp (by simpa [hs] using hm z)
    linarith
  rw [← conjugate_eq_lcs] at hbound
  have htop : conjugate f y ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hbound
  have hbot := conjugate_ne_bot f hp y
  lift conjugate f y to ℝ using ⟨htop, hbot⟩ with r hr
  exact ⟨y, r, hr.symm⟩

end VariationalNotes.ConvexAnalysis
