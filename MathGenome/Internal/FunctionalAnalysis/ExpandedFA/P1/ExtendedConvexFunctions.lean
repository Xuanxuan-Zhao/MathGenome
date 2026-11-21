import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.ExtendedConvexFunctions

/-! Extended-valued functions and their real epigraphs, with no completeness
or properness assumptions on the epigraph equivalences. -/
namespace ExpandedFA.P1.ExtendedConvexFunctions

open Set

def finiteDomain : Spec.finiteDomainType :=
  Spec.finiteDomainValue

def Proper : Spec.ProperType :=
  Spec.ProperValue

def LowerSemicontinuous : Spec.LowerSemicontinuousType :=
  Spec.LowerSemicontinuousValue

def realEpigraph : Spec.realEpigraphType :=
  Spec.realEpigraphValue

def ExtendedConvex : Spec.ExtendedConvexType :=
  Spec.ExtendedConvexValue

theorem proper_iff_finite_value : Spec.ProperIffFiniteValue := by
  intro E φ
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hx
    exact ⟨x, r, hr.symm⟩
  · rintro ⟨x, r, hr⟩
    exact ⟨x, by simp [Spec.finiteDomainValue, hr]⟩

/-- Closed real sublevels give a closed real epigraph by an intersection of
closed unions; this avoids introducing extended-real arithmetic at infinity. -/
theorem lowerSemicontinuous_iff_closed_epigraph :
    Spec.LowerSemicontinuousIffClosedEpigraph := by
  intro E _ φ
  constructor
  · intro h
    have heq : realEpigraph E φ = ⋂ r : ℝ,
        ({p : E × ℝ | φ p.1 ≤ (r : WithTop ℝ)} ∪ {p | r ≤ p.2}) := by
      ext p
      simp only [realEpigraph, Spec.realEpigraphValue,
        mem_ofPred_eq, mem_iInter, mem_union]
      constructor
      · intro hp r
        by_cases hr : r ≤ p.2
        · exact Or.inr hr
        · exact Or.inl (hp.trans (WithTop.coe_le_coe.mpr (le_of_not_ge hr)))
      · intro hp
        by_contra hn
        obtain ⟨r, htr, hrf⟩ := WithTop.lt_iff_exists_coe_btwn.mp (lt_of_not_ge hn)
        rcases hp r with hf | ht
        · exact (not_le_of_gt hrf) hf
        · exact (not_le_of_gt htr) (WithTop.coe_le_coe.mpr ht)
    rw [← show realEpigraph E φ = Spec.realEpigraphValue E φ from rfl,
      heq]
    exact isClosed_iInter fun r =>
      ((h r).preimage continuous_fst).union (isClosed_le continuous_const continuous_snd)
  · intro h r
    exact h.preimage (continuous_id.prodMk continuous_const :
      Continuous (fun x : E => (x, r)))

theorem convex_iff_convex_epigraph :
    Spec.ConvexIffConvexEpigraph := by
  intro E _ _ φ
  constructor
  · intro h
    rintro ⟨x, t⟩ hx ⟨y, u⟩ hy a b ha hb hab
    change φ (a • x + b • y) ≤ ((a * t + b * u : ℝ) : WithTop ℝ)
    obtain ⟨r, hr, hrt⟩ := WithTop.le_coe_iff.mp hx
    obtain ⟨s, hs, hsu⟩ := WithTop.le_coe_iff.mp hy
    exact (h x y r s a b hr hs ha hb hab).trans
      (WithTop.coe_le_coe.mpr (add_le_add (mul_le_mul_of_nonneg_left hrt ha)
        (mul_le_mul_of_nonneg_left hsu hb)))
  · intro h x y r s a b hx hy ha hb hab
    exact h (show (x, r) ∈ Spec.realEpigraphValue E φ from hx.le)
      (show (y, s) ∈ Spec.realEpigraphValue E φ from hy.le) ha hb hab

theorem convex_finiteDomain : Spec.ConvexFiniteDomain := by
  intro E _ _ φ h x hx y hy a b ha hb hab
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hx
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy
  exact ne_top_of_le_ne_top (WithTop.coe_ne_top : ((a * r + b * s : ℝ) : WithTop ℝ) ≠ ⊤)
    (h x y r s a b hr.symm hs.symm ha hb hab)

end ExpandedFA.P1.ExtendedConvexFunctions
