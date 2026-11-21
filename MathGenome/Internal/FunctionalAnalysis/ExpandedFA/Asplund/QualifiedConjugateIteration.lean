import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Asplund.QualifiedConjugateIteration
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Asplund.ConjugateLimits
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.FenchelRockafellar
import Mathlib.Analysis.Convex.Continuous

namespace ExpandedFA.Asplund.QualifiedConjugateIteration

universe u

open Iteration OrderLimit ConjugateLimits Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem primal_conclusions : Spec.PrimalConclusions.{u} :=
  ⟨iterates_properties, order_chain, common_limit⟩

theorem unqualified_conjugate_conclusions : Spec.UnqualifiedConjugateConclusions.{u} :=
  ⟨phi_conjugate_limit, psi_conjugate_recurrence,
    psi_conjugate_limit, psi_conjugate_limit_fullDomain⟩

/-- A convex function dominated by a function continuous at one point is
continuous there. The local upper bound suffices even in an incomplete space. -/
theorem continuousAt_of_convex_dominated (q r : E → ℝ)
    (hq : ConvexOn ℝ univ q) (hqr : ∀ x, q x ≤ r x)
    (x₀ : E) (hr : ContinuousAt r x₀) : ContinuousAt q x₀ := by
  have hb : (𝓝 x₀).IsBoundedUnder (· ≤ ·) q := by
    refine ⟨r x₀ + 1, ?_⟩
    change ∀ᶠ x in 𝓝 x₀, q x ≤ r x₀ + 1
    filter_upwards [hr.eventually (eventually_le_nhds (by linarith : r x₀ < r x₀ + 1))]
      with x hx
    exact (hqr x).trans hx
  have hc : ContinuousOn q univ := by
    apply ((hq.continuousOn_tfae isOpen_univ univ_nonempty).out 4 2).mp
    exact ⟨x₀, mem_univ _, hb⟩
  exact hc.continuousAt (univ_mem)

theorem iterates_continuousAt : Spec.IteratesContinuousAt := by
  intro E _ _ φ₀ ψ₀ h x₀ hc n
  have hn := iterates_properties E φ₀ ψ₀ h n
  have hφ : ∀ x, phi E φ₀ ψ₀ n x ≤ φ₀ x := fun x =>
    (monotone_sequences E φ₀ ψ₀ h x).1 (Nat.zero_le n)
  exact ⟨continuousAt_of_convex_dominated _ _ hn.1 hφ x₀ hc,
    continuousAt_of_convex_dominated _ _ hn.2.1
      (fun x => (hn.2.2.2.1 x).trans (hφ x)) x₀ hc⟩

/-- Positive scaling preserves arbitrary extended infima, also when all
terms are infinite. -/
theorem half_iInf {ι : Type*} (a : ι → EReal) :
    ((1 / 2 : ℝ) : EReal) * (⨅ i, a i) =
      ⨅ i, ((1 / 2 : ℝ) : EReal) * a i := by
  apply Monotone.map_iInf_of_continuousAt
  · exact (EReal.continuousAt_mul
      (Or.inl (EReal.coe_ne_zero.mpr (by norm_num)))
      (Or.inl (EReal.coe_ne_zero.mpr (by norm_num)))
      (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).comp
        (continuousAt_const.prodMk continuousAt_id)
  · exact fun _ _ h => mul_le_mul_of_nonneg_left h (by norm_num)
  · exact EReal.coe_mul_top_of_pos (by norm_num)

/-- Weak duality for every continuous splitting; no qualification is needed. -/
theorem conjugate_arithmeticMean_le (q r : E → ℝ) (f g : E →L[ℝ] ℝ) :
    conjugate E (arithmeticMean E q r) f ≤
      ((1 / 2 : ℝ) : EReal) * (conjugate E q (f + g) + conjugate E r (f - g)) := by
  rw [conjugate_eq]
  apply iSup_le
  intro x
  calc
    ((f x - arithmeticMean E q r x : ℝ) : EReal) =
        ((1 / 2 : ℝ) : EReal) *
          ((((f + g) x - q x : ℝ) : EReal) + (((f - g) x - r x : ℝ) : EReal)) := by
      rw [← EReal.coe_add, ← EReal.coe_mul]
      congr 1
      simp only [add_apply, sub_apply, arithmeticMean]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
      (by rw [conjugate_eq]; exact le_iSup (fun y : E => (((f + g) y - q y : ℝ) : EReal)) x)
      (by rw [conjugate_eq]; exact le_iSup (fun y : E => (((f - g) y - r y : ℝ) : EReal)) x)) (by norm_num)

/-- Real convexity agrees with the accepted finite-extension interface. -/
theorem finiteExtension_convex (q : E → ℝ) (hq : ConvexOn ℝ univ q) :
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue E (finiteExtension E q) := by
  intro x y r s a b hx hy ha hb hab
  have hx' : q x = r := WithTop.coe_injective hx
  have hy' : q y = s := WithTop.coe_injective hy
  subst r; subst s
  exact WithTop.coe_le_coe.mpr (hq.2 (mem_univ _) (mem_univ _) ha hb hab)

/-- At a finite arithmetic conjugate value, the qualified separator gives
an exact continuous-dual splitting. -/
theorem exists_split_of_finite (q r : E → ℝ)
    (h : InitialData E q r) (x₀ : E) (hc : ContinuousAt q x₀)
    (f : E →L[ℝ] ℝ) (hf : conjugate E (arithmeticMean E q r) f < ⊤) :
    ∃ g : E →L[ℝ] ℝ,
      ((1 / 2 : ℝ) : EReal) * (conjugate E q (f + g) + conjugate E r (f - g)) ≤
        conjugate E (arithmeticMean E q r) f := by
  let a : ℝ := (conjugate E (arithmeticMean E q r) f).toReal
  have habot := conjugate_ne_bot E (arithmeticMean E q r) f
  have ha : (a : EReal) = conjugate E (arithmeticMean E q r) f :=
    EReal.coe_toReal hf.ne habot
  have hlower (x : E) : -2 * a ≤ (q x - f x) + (r x - f x) := by
    have hx : ((f x - arithmeticMean E q r x : ℝ) : EReal) ≤ (a : EReal) := by
      rw [ha, conjugate_eq]
      exact le_iSup (fun y : E => ((f y - arithmeticMean E q r y : ℝ) : EReal)) x
    have hr := EReal.coe_le_coe_iff.mp hx
    dsimp [arithmeticMean] at hr
    linarith
  have hqc : ConvexOn ℝ univ (fun x => q x - f x) :=
    h.1.sub (f.toLinearMap.concaveOn convex_univ)
  have hrc : ConvexOn ℝ univ (fun x => r x - f x) :=
    h.2.1.sub (f.toLinearMap.concaveOn convex_univ)
  have hcont : ContinuousAt (finiteExtension E (fun x => q x - f x)) x₀ :=
    WithTop.continuous_coe.continuousAt.comp (hc.sub f.continuous.continuousAt)
  obtain ⟨g, c, hp, hr⟩ := P1.FenchelRockafellar.affine_minorants_of_lower_bound
    (finiteExtension E (fun x => q x - f x))
    (finiteExtension E (fun x => r x - f x))
    (finiteExtension_convex _ hqc) (finiteExtension_convex _ hrc)
    x₀ (q x₀ - f x₀) (r x₀ - f x₀) rfl rfl hcont (-2 * a)
    (by
      intro x u v hu hv
      have hu' : q x - f x = u := WithTop.coe_injective hu
      have hv' : r x - f x = v := WithTop.coe_injective hv
      rw [← hu', ← hv']; exact hlower x)
  have hP : conjugate E q (f + g) ≤ ((-c : ℝ) : EReal) := by
    rw [conjugate_eq]
    apply iSup_le
    intro x
    apply EReal.coe_le_coe_iff.mpr
    have hx := WithTop.coe_le_coe.mp (hp x)
    simp only [add_apply]
    linarith
  have hR : conjugate E r (f - g) ≤ ((2 * a + c : ℝ) : EReal) := by
    rw [conjugate_eq]
    apply iSup_le
    intro x
    apply EReal.coe_le_coe_iff.mpr
    have hx := WithTop.coe_le_coe.mp (hr x)
    simp only [sub_apply]
    linarith
  refine ⟨g, ?_⟩
  calc
    _ ≤ ((1 / 2 : ℝ) : EReal) * (((-c : ℝ) : EReal) + ((2 * a + c : ℝ) : EReal)) :=
      mul_le_mul_of_nonneg_left (add_le_add hP hR) (by norm_num)
    _ = conjugate E (arithmeticMean E q r) f := by
      rw [← EReal.coe_add, ← EReal.coe_mul, ← ha]
      congr 1
      ring

/-- Qualified conjugation of one arithmetic mean, with infinite values allowed. -/
theorem conjugate_arithmeticMean (q r : E → ℝ) (h : InitialData E q r)
    (x₀ : E) (hc : ContinuousAt q x₀) (f : E →L[ℝ] ℝ) :
    conjugate E (arithmeticMean E q r) f =
      ((1 / 2 : ℝ) : EReal) * (⨅ g : E →L[ℝ] ℝ,
        conjugate E q (f + g) + conjugate E r (f - g)) := by
  have hweak : conjugate E (arithmeticMean E q r) f ≤
      ((1 / 2 : ℝ) : EReal) * (⨅ g : E →L[ℝ] ℝ,
        conjugate E q (f + g) + conjugate E r (f - g)) := by
    rw [half_iInf]
    exact le_iInf (conjugate_arithmeticMean_le q r f)
  apply le_antisymm hweak
  by_cases hf : conjugate E (arithmeticMean E q r) f = ⊤
  · rw [hf]; exact le_top
  · obtain ⟨g, hg⟩ := exists_split_of_finite q r h x₀ hc f (lt_top_iff_ne_top.mpr hf)
    exact (mul_le_mul_of_nonneg_left
      (iInf_le (fun g : E →L[ℝ] ℝ => conjugate E q (f + g) + conjugate E r (f - g)) g)
      (by norm_num : (0 : EReal) ≤ ((1 / 2 : ℝ) : EReal))).trans hg

/-- A finite value is attained by a splitting in the continuous dual. -/
theorem conjugate_arithmeticMean_attained (q r : E → ℝ) (h : InitialData E q r)
    (x₀ : E) (hc : ContinuousAt q x₀) (f : E →L[ℝ] ℝ)
    (hf : conjugate E (arithmeticMean E q r) f < ⊤) :
    ∃ g : E →L[ℝ] ℝ,
      (⨅ k : E →L[ℝ] ℝ, conjugate E q (f + k) + conjugate E r (f - k)) =
        conjugate E q (f + g) + conjugate E r (f - g) := by
  obtain ⟨g, hg⟩ := exists_split_of_finite q r h x₀ hc f hf
  refine ⟨g, ?_⟩
  have heq : ((1 / 2 : ℝ) : EReal) *
      (⨅ k : E →L[ℝ] ℝ, conjugate E q (f + k) + conjugate E r (f - k)) =
      ((1 / 2 : ℝ) : EReal) * (conjugate E q (f + g) + conjugate E r (f - g)) := by
    rw [← conjugate_arithmeticMean q r h x₀ hc f]
    exact le_antisymm (conjugate_arithmeticMean_le q r f g) hg
  have hscale (z : EReal) : (2 : EReal) * (((1 / 2 : ℝ) : EReal) * z) = z := by
    have hh : (2 : EReal) * ((1 / 2 : ℝ) : EReal) = 1 := by
      change ((2 : ℝ) : EReal) * ((1 / 2 : ℝ) : EReal) = ((1 : ℝ) : EReal)
      rw [← EReal.coe_mul]
      norm_num
    rw [← mul_assoc, hh, one_mul]
  have hs := congrArg (fun z : EReal => (2 : EReal) * z) heq
  simpa only [hscale] using hs

theorem qualified_conjugate_formula : Spec.QualifiedConjugateFormula := by
  intro E _ _ φ₀ ψ₀ h x₀ hc n f
  exact conjugate_arithmeticMean _ _ (iterates_properties E φ₀ ψ₀ h n) x₀
    (iterates_continuousAt E φ₀ ψ₀ h x₀ hc n).1 f

theorem qualified_conjugate_attainment : Spec.QualifiedConjugateAttainment := by
  intro E _ _ φ₀ ψ₀ h x₀ hc n f hf
  exact conjugate_arithmeticMean_attained _ _ (iterates_properties E φ₀ ψ₀ h n) x₀
    (iterates_continuousAt E φ₀ ψ₀ h x₀ hc n).1 f hf

end ExpandedFA.Asplund.QualifiedConjugateIteration
