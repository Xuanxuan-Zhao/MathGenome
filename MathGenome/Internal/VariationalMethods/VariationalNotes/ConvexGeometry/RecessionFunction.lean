import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.RecessionFunction
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.RecessionSets
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.ExtendedFunctions
import Mathlib.Tactic.Ring

/-! Recession of extended-valued functions, with real epigraph heights.
The epigraph ray criterion identifies each real fiber with the real upper
bounds of the positive-time quotients. This also handles an empty fiber. -/

noncomputable section
open Set
universe u
namespace VariationalNotes.ConvexGeometry

abbrev recessionFunction {E : Type u} [AddCommGroup E] [Module ℝ E]
    (f : E → WithTop ℝ) (d : E) : EReal := Specs.recessionFunction f d

abbrev rayQuotient {E : Type u} [AddCommGroup E] [Module ℝ E]
    (f : E → WithTop ℝ) (x d : E) (t : ℝ) : EReal := Specs.rayQuotient f x d t

section Algebra
variable {E : Type u} [AddCommGroup E] [Module ℝ E]

lemma rayQuotient_le_real_iff (f : E → WithTop ℝ) (x d : E) (a r t : ℝ)
    (hx : f x = a) (ht : 0 < t) :
    rayQuotient f x d t ≤ (r : EReal) ↔
      f (x + t • d) ≤ ((a + t*r : ℝ) : WithTop ℝ) := by
  unfold rayQuotient Specs.rayQuotient
  rw [hx]
  generalize f (x + t • d) = z
  induction z using WithTop.recTopCoe with
  | top =>
    change ((⊤ : EReal) - (a : EReal)) / (t : EReal) ≤ (r : EReal) ↔
      (⊤ : WithTop ℝ) ≤ ((a + t*r : ℝ) : WithTop ℝ)
    rw [EReal.top_sub_coe, EReal.top_div_of_pos_ne_top (by exact_mod_cast ht)
      (EReal.coe_ne_top t)]
    exact iff_of_false (not_le.mpr (EReal.coe_lt_top r))
      (not_le.mpr (WithTop.coe_lt_top _))
  | coe b =>
    change ((b - a) / t : EReal) ≤ (r : EReal) ↔ _
    rw [← EReal.coe_sub, ← EReal.coe_div, EReal.coe_le_coe_iff, WithTop.coe_le_coe]
    rw [div_le_iff₀ ht]
    constructor <;> intro h <;> linarith

lemma rayQuotient_ne_bot (f : E → WithTop ℝ) (x d : E) (a t : ℝ)
    (hx : f x = a) (ht : 0 < t) : rayQuotient f x d t ≠ ⊥ := by
  unfold rayQuotient Specs.rayQuotient
  rw [hx]
  generalize f (x + t • d) = z
  induction z using WithTop.recTopCoe with
  | top =>
    change ((⊤ : EReal) - (a : EReal)) / (t : EReal) ≠ ⊥
    rw [EReal.top_sub_coe, EReal.top_div_of_pos_ne_top (by exact_mod_cast ht)
      (EReal.coe_ne_top t)]
    exact top_ne_bot
  | coe b => exact EReal.coe_ne_bot ((b-a)/t)

theorem recessionFunction_empty_fiber : Specs.recessionFunction_empty_fiber.{u} := by
  intro E _ _ f d h
  have hempty : {r : ℝ | (d,r) ∈ Specs.recession (ConvexAnalysis.Specs.epigraph f)} = ∅ := by
    ext r
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact fun hr => h ⟨r, hr⟩
  simp [Specs.recessionFunction, hempty]

lemma rayQuotient_of_top (f : E → WithTop ℝ) (x d : E) (a t : ℝ)
    (hx : f x = a) (ht : 0 < t) (h : f (x + t • d) = ⊤) :
    rayQuotient f x d t = ⊤ := by
  unfold rayQuotient Specs.rayQuotient
  rw [hx, h]
  change ((⊤ : EReal) - (a : EReal)) / (t : EReal) = ⊤
  rw [EReal.top_sub_coe, EReal.top_div_of_pos_ne_top (by exact_mod_cast ht)
    (EReal.coe_ne_top t)]

lemma rayQuotient_of_real (f : E → WithTop ℝ) (x d : E) (a b t : ℝ)
    (hx : f x = a) (h : f (x + t • d) = b) :
    rayQuotient f x d t = (((b-a)/t : ℝ) : EReal) := by
  unfold rayQuotient Specs.rayQuotient
  rw [hx, h]
  rfl

theorem rayQuotient_monotone : Specs.rayQuotient_monotone.{u} := by
  intro E _ _ f hc x hx d s hs t ht hst
  change rayQuotient f x d s ≤ rayQuotient f x d t
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hx)
  by_cases htop : f (x + t • d) = ⊤
  · rw [rayQuotient_of_top f x d a t ha.symm ht htop]
    exact le_top
  · obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [rayQuotient_of_real f x d a b t ha.symm hb.symm]
    apply (rayQuotient_le_real_iff f x d a ((b-a)/t) s ha.symm hs).mpr
    have hfrac : s/t ≤ 1 := (div_le_one ht).mpr hst
    have h : f ((1-s/t) • x + (s/t) • (x + t • d)) ≤
        (((1-s/t)*a + (s/t)*b : ℝ) : WithTop ℝ) :=
      hc (show (x,a) ∈ ConvexAnalysis.Specs.epigraph f from ha.symm.le)
        (show (x+t • d,b) ∈ ConvexAnalysis.Specs.epigraph f from hb.symm.le)
        (sub_nonneg.mpr hfrac) (div_nonneg hs.le ht.le) (sub_add_cancel 1 (s/t))
    have heq : (1-s/t) • x + (s/t) • (x+t • d) = x+s • d := by
      rw [smul_add, smul_smul, div_mul_cancel₀ _ ht.ne', sub_smul, one_smul]
      abel
    rw [heq] at h
    convert h using 1
    congr 1
    ring

end Algebra

/-- Every extended real is the infimum of its real upper bounds, including
both infinite endpoints. -/
lemma sInf_real_upperBounds (q : EReal) :
    sInf ((fun r : ℝ => (r : EReal)) '' {r : ℝ | q ≤ (r : EReal)}) = q := by
  apply le_antisymm
  · by_contra h
    obtain ⟨r, hqr, hri⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
    have hi : sInf ((fun r : ℝ => (r : EReal)) '' {r : ℝ | q ≤ (r : EReal)}) ≤
        (r : EReal) := sInf_le ⟨r, hqr.le, rfl⟩
    exact hri.not_ge hi
  · apply le_sInf
    rintro z ⟨r, hr, rfl⟩
    exact hr

section Topology
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

lemma mem_recession_epigraph_iff (f : E → WithTop ℝ)
    (hc : ConvexAnalysis.IsConvex f) (hl : ConvexAnalysis.IsLowerSemicontinuous f)
    (x d : E) (a r : ℝ) (hx : f x = a) :
    (d,r) ∈ recession (ConvexAnalysis.epigraph f) ↔
      ∀ t : ℝ, 0 < t → rayQuotient f x d t ≤ (r : EReal) := by
  constructor
  · intro hd t ht
    apply (rayQuotient_le_real_iff f x d a r t hx ht).mpr
    exact hd (x,a) (show (x,a) ∈ ConvexAnalysis.epigraph f from hx.le) t ht.le
  · intro h
    apply recession_of_ray ((ConvexAnalysis.lowerSemicontinuous_iff_closed_epigraph f).mp hl) hc
      (x₀ := (x,a))
    intro t ht
    rcases eq_or_lt_of_le ht with heq | hpos
    · subst t
      change f (x + (0:ℝ) • d) ≤ ((a + (0:ℝ)*r : ℝ) : WithTop ℝ)
      simpa only [zero_smul, add_zero, zero_mul] using hx.le
    · exact (rayQuotient_le_real_iff f x d a r t hx hpos).mp (h t hpos)

theorem recessionFunction_eq_sup : Specs.recessionFunction_eq_sup.{u} := by
  intro E _ _ _ _ _ f _ hc hl x hx d
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hx)
  have hset : {r : ℝ | (d,r) ∈ Specs.recession (ConvexAnalysis.Specs.epigraph f)} =
      {r : ℝ | (⨆ (t : ℝ) (_ : 0 < t), rayQuotient f x d t) ≤ (r : EReal)} := by
    ext r
    exact (mem_recession_epigraph_iff f hc hl x d a r ha.symm).trans
      (by simp only [iSup_le_iff, mem_ofPred_eq])
  change sInf _ = _
  rw [hset]
  exact sInf_real_upperBounds _

theorem raySupremum_independent : Specs.raySupremum_independent.{u} := by
  intro E _ _ _ _ _ f hp hc hl x y hx hy d
  rw [← recessionFunction_eq_sup f hp hc hl x hx d,
    ← recessionFunction_eq_sup f hp hc hl y hy d]

theorem recessionFunction_ne_bot : Specs.recessionFunction_ne_bot.{u} := by
  intro E _ _ _ _ _ f hp hc hl d
  obtain ⟨x, hx⟩ := hp
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hx)
  rw [recessionFunction_eq_sup f ⟨x,hx⟩ hc hl x hx d]
  exact ne_bot_of_le_ne_bot (rayQuotient_ne_bot f x d a 1 ha.symm zero_lt_one)
    (le_iSup_of_le 1 (le_iSup_of_le zero_lt_one le_rfl))

lemma mem_recession_epigraph_iff_le (f : E → WithTop ℝ)
    (hp : ConvexAnalysis.Proper f) (hc : ConvexAnalysis.IsConvex f)
    (hl : ConvexAnalysis.IsLowerSemicontinuous f) (d : E) (r : ℝ) :
    (d,r) ∈ recession (ConvexAnalysis.epigraph f) ↔ recessionFunction f d ≤ (r : EReal) := by
  obtain ⟨x, hx⟩ := hp
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hx)
  change (d,r) ∈ recession (ConvexAnalysis.epigraph f) ↔ Specs.recessionFunction f d ≤ _
  rw [recessionFunction_eq_sup f ⟨x,hx⟩ hc hl x hx d]
  exact (mem_recession_epigraph_iff f hc hl x d a r ha.symm).trans
    (by simp only [iSup_le_iff])

theorem recession_sublevel : Specs.recession_sublevel.{u} := by
  intro E _ _ _ _ _ f hp hc hl a hne
  ext d
  change d ∈ recession (ConvexAnalysis.sublevel f a) ↔ recessionFunction f d ≤ 0
  rw [← EReal.coe_zero, ← mem_recession_epigraph_iff_le f hp hc hl d 0]
  constructor
  · intro hd
    obtain ⟨x, hx⟩ := hne
    apply recession_of_ray ((ConvexAnalysis.lowerSemicontinuous_iff_closed_epigraph f).mp hl) hc
      (x₀ := (x,a))
    intro t ht
    change f (x + t • d) ≤ ((a + t*0 : ℝ) : WithTop ℝ)
    have h : f (x + t • d) ≤ (a : WithTop ℝ) := hd x hx t ht
    simpa only [mul_zero, add_zero] using h
  · intro hd x hx t ht
    have h := hd (x,a) hx t ht
    change f (x + t • d) ≤ ((a + t*0 : ℝ) : WithTop ℝ) at h
    change f (x + t • d) ≤ (a : WithTop ℝ)
    simpa only [mul_zero, add_zero] using h

end Topology

theorem unbounded_sublevel_iff : Specs.unbounded_sublevel_iff.{u} := by
  intro E _ _ _ _ _ _ _ _ f hp hc hl a hne
  have hcl : IsClosed (ConvexAnalysis.sublevel f a) :=
    (ConvexAnalysis.lowerSemicontinuous_iff_closed_sublevels f).mp hl a
  have hcv : Convex ℝ (ConvexAnalysis.sublevel f a) := by
    intro x hx y hy b c hb hcc hbc
    have h : f (b • x + c • y) ≤ ((b*a+c*a : ℝ) : WithTop ℝ) :=
      hc (show (x,a) ∈ ConvexAnalysis.epigraph f from hx)
        (show (y,a) ∈ ConvexAnalysis.epigraph f from hy) hb hcc hbc
    rw [← add_mul, hbc, one_mul] at h
    exact h
  have h := unbounded_iff_recession_nonzero (ConvexAnalysis.Specs.sublevel f a) hne hcl hcv
  rw [recession_sublevel f hp hc hl a hne] at h
  simpa only [mem_ofPred_eq, and_comm] using h

end VariationalNotes.ConvexGeometry
