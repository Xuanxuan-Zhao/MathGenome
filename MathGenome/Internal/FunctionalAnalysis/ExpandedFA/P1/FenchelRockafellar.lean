import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.FenchelRockafellar
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06Conjugates
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.ExtendedConvexFunctions
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Fenchel–Rockafellar duality by epigraph separation.

At a real lower bound `a`, separate the interior of `epi φ` from
`{(x,t) | ψ(x) ≤ a-t}`. Continuity at the common finite-domain point
makes the first interior nonempty and forces the separator's vertical
coefficient to be strictly negative. Normalizing gives complementary
continuous affine minorants, hence a dual value at least `a`.

The geometric argument is also given in R. T. Rockafellar, “Extension of
Fenchel's duality theorem for convex functions”, Duke Math. J. 33 (1966),
81–89, Theorem 1, pp. 82–83. No global lower semicontinuity is required. -/

set_option backward.isDefEq.respectTransparency false

namespace ExpandedFA.P1.FenchelRockafellar

open Set Filter ExtendedConvexFunctions
open scoped Topology

local notation "val" => C06Conjugates.Spec.ExtendedRealValueValue

@[simp] private lemma val_coe (r : ℝ) : val (r : WithTop ℝ) = (r : EReal) := rfl
@[simp] private lemma val_top : val ⊤ = (⊤ : EReal) := rfl
private lemma val_ne_bot (r : WithTop ℝ) : val r ≠ (⊥ : EReal) := WithBot.coe_ne_bot

theorem normed_conjugate_agreement : Spec.NormedConjugateAgreement := by
  intro E _ _ φ f
  change conjugate φ f = C06Conjugates.convexConjugate E φ f
  rfl

section Order
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- Weak duality needs no convexity or qualification. -/
theorem dualValue_le_sum (φ ψ : ExtendedFunction E) (f : E →L[ℝ] ℝ) (x : E) :
    dualValue φ ψ f ≤ val (φ x) + val (ψ x) := by
  by_cases hx : φ x = ⊤
  · rw [hx]
    rw [val_top, EReal.top_add_of_ne_bot (val_ne_bot (ψ x))]
    exact le_top
  by_cases hy : ψ x = ⊤
  · rw [hy]
    rw [val_top, EReal.add_top_of_ne_bot (val_ne_bot (φ x))]
    exact le_top
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hx
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy
  have hφ : ((f x - r : ℝ) : EReal) ≤ conjugate φ f := by
    simpa only [conjugate, hr.symm, val_coe, ← EReal.coe_sub] using
      (le_iSup (fun y => (f y : EReal) - val (φ y)) x)
  have hψ : (((-f) x - s : ℝ) : EReal) ≤ conjugate ψ (-f) := by
    simpa only [conjugate, hs.symm, val_coe, ← EReal.coe_sub] using
      (le_iSup (fun y => ((-f) y : EReal) - val (ψ y)) x)
  have h := add_le_add (EReal.neg_le_neg_iff.mpr hφ) (EReal.neg_le_neg_iff.mpr hψ)
  change -conjugate φ f + -conjugate ψ (-f) ≤ _
  rw [hr.symm, hs.symm]
  change -conjugate φ f + -conjugate ψ (-f) ≤ (r : EReal) + (s : EReal)
  convert h using 1
  simp only [← EReal.coe_neg, ← EReal.coe_add, neg_apply]
  congr 1
  ring

theorem weak_duality (φ ψ : ExtendedFunction E) :
    (⨆ f : E →L[ℝ] ℝ, dualValue φ ψ f) ≤ primalValue φ ψ := by
  exact iSup_le fun f => le_iInf fun x => dualValue_le_sum φ ψ f x

/-- A pair of complementary continuous affine minorants gives a dual
value at least `a`. -/
theorem dualValue_ge_of_affine_minorants (φ ψ : ExtendedFunction E)
    (a c : ℝ) (f : E →L[ℝ] ℝ)
    (hφ : ∀ x, ((f x + c : ℝ) : WithTop ℝ) ≤ φ x)
    (hψ : ∀ x, ((-f x + (a - c) : ℝ) : WithTop ℝ) ≤ ψ x) :
    (a : EReal) ≤ dualValue φ ψ f := by
  have hp : conjugate φ f ≤ ((-c : ℝ) : EReal) := by
    apply iSup_le
    intro x
    calc
      (f x : EReal) - val (φ x) ≤
          (f x : EReal) - ((f x + c : ℝ) : EReal) :=
        EReal.sub_le_sub le_rfl (WithBot.coe_le_coe.mpr (hφ x))
      _ = ((-c : ℝ) : EReal) := by rw [← EReal.coe_sub]; congr 1; ring
  have hq : conjugate ψ (-f) ≤ ((c - a : ℝ) : EReal) := by
    apply iSup_le
    intro x
    calc
      ((-f) x : EReal) - val (ψ x) ≤
          ((-f) x : EReal) - ((-f x + (a - c) : ℝ) : EReal) :=
        EReal.sub_le_sub le_rfl (WithBot.coe_le_coe.mpr (hψ x))
      _ = ((c - a : ℝ) : EReal) := by
        rw [← EReal.coe_sub]; congr 1; simp only [neg_apply]; ring
  have h := add_le_add (EReal.neg_le_neg_iff.mpr hp) (EReal.neg_le_neg_iff.mpr hq)
  change (a : EReal) ≤ -conjugate φ f + -conjugate ψ (-f)
  convert h using 1
  simp only [← EReal.coe_neg, ← EReal.coe_add]
  congr 1
  ring
end Order

section EpigraphTopology
variable {E : Type*} [TopologicalSpace E]

/-- Continuity at a finite point supplies an interior point of the real epigraph. -/
theorem epigraph_interior_of_continuousAt (φ : ExtendedFunction E) (x₀ : E)
    (r : ℝ) (hr : φ x₀ = (r : WithTop ℝ)) (hc : ContinuousAt φ x₀) :
    (x₀, r + 1) ∈ interior (realEpigraph E φ) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hx : {x | φ x < ((r + 1 / 2 : ℝ) : WithTop ℝ)} ∈ 𝓝 x₀ :=
    hc.preimage_mem_nhds (Iio_mem_nhds (by rw [hr]; exact WithTop.coe_lt_coe.mpr (by linarith)))
  have ht : Ioi (r + 1 / 2) ∈ 𝓝 (r + 1) := Ioi_mem_nhds (by linarith)
  apply mem_of_superset (prod_mem_nhds hx ht)
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  change φ x ≤ (t : WithTop ℝ)
  change φ x < ((r + 1 / 2 : ℝ) : WithTop ℝ) at hx
  change r + 1 / 2 < t at ht
  exact hx.le.trans (WithTop.coe_le_coe.mpr ht.le)

/-- An interior epigraph point lies strictly above the value of the function. -/
theorem lt_of_mem_epigraph_interior (φ : ExtendedFunction E) {p : E × ℝ}
    (hp : p ∈ interior (realEpigraph E φ)) : φ p.1 < (p.2 : WithTop ℝ) := by
  have hn : {t : ℝ | φ p.1 ≤ (t : WithTop ℝ)} ∈ 𝓝 p.2 :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (mem_interior_iff_mem_nhds.mp hp)
  obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  have hm : (l + p.2) / 2 ∈ Ioo l u := ⟨by linarith [hlu.1], by linarith [hlu.1, hlu.2]⟩
  exact (hsub hm).trans_lt (WithTop.coe_lt_coe.mpr (by linarith [hlu.1]))

end EpigraphTopology

section Separation
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Separation yields complementary affine minorants at every real primal lower
bound. This is the geometric core of the continuity qualification theorem. -/
theorem affine_minorants_of_lower_bound (φ ψ : ExtendedFunction E)
    (hφ : ExtendedConvexFunctions.Spec.ExtendedConvexValue E φ)
    (hψ : ExtendedConvexFunctions.Spec.ExtendedConvexValue E ψ)
    (x₀ : E) (r s : ℝ) (hr : φ x₀ = (r : WithTop ℝ))
    (hs : ψ x₀ = (s : WithTop ℝ)) (hc : ContinuousAt φ x₀)
    (a : ℝ) (ha : ∀ (x : E) (r' s' : ℝ), φ x = (r' : WithTop ℝ) →
      ψ x = (s' : WithTop ℝ) → a ≤ r' + s') :
    ∃ (f : E →L[ℝ] ℝ) (c : ℝ),
      (∀ x, ((f x + c : ℝ) : WithTop ℝ) ≤ φ x) ∧
      (∀ x, ((-f x + (a - c) : ℝ) : WithTop ℝ) ≤ ψ x) := by
  let A := realEpigraph E φ
  let B : Set (E × ℝ) := {p | ψ p.1 ≤ ((a - p.2 : ℝ) : WithTop ℝ)}
  have hA : Convex ℝ A := (convex_iff_convex_epigraph E φ).mp hφ
  have hB : Convex ℝ B := by
    rintro ⟨x, t⟩ hx ⟨y, u⟩ hy α β hα hβ hαβ
    have hep := (convex_iff_convex_epigraph E ψ).mp hψ
    have h := hep (show (x, a - t) ∈ realEpigraph E ψ from hx)
      (show (y, a - u) ∈ realEpigraph E ψ from hy) hα hβ hαβ
    change ψ (α • x + β • y) ≤ ((α * (a - t) + β * (a - u) : ℝ) : WithTop ℝ) at h
    change ψ (α • x + β • y) ≤ ((a - (α * t + β * u) : ℝ) : WithTop ℝ)
    convert h using 1
    congr 1
    calc
      a - (α * t + β * u) = (α + β) * a - (α * t + β * u) := by rw [hαβ, one_mul]
      _ = α * (a - t) + β * (a - u) := by ring
  have hint : (x₀, r + 1) ∈ interior A :=
    epigraph_interior_of_continuousAt φ x₀ r hr hc
  have hdisj : Disjoint (interior A) B := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    have hlt := lt_of_mem_epigraph_interior φ hp
    obtain ⟨r', hr', _⟩ := WithTop.le_coe_iff.mp hlt.le
    have hrt : r' < p.2 := by rw [hr'] at hlt; exact WithTop.coe_lt_coe.mp hlt
    obtain ⟨s', hs', hst⟩ := WithTop.le_coe_iff.mp hq
    have hmin := ha p.1 r' s' hr' hs'
    linarith
  obtain ⟨g, d, hgA, hgB⟩ :=
    geometric_hahn_banach_open hA.interior isOpen_interior hB hdisj
  have hgA' : ∀ p ∈ A, g p ≤ d := by
    intro p hp
    apply closure_minimal (fun z hz => (hgA z hz).le) (isClosed_Iic.preimage g.continuous)
    rw [hA.closure_interior_eq_closure_of_nonempty_interior ⟨_, hint⟩]
    exact subset_closure hp
  let l : E →L[ℝ] ℝ := g.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let b : ℝ := g (0, 1)
  have g_eq (x : E) (t : ℝ) : g (x, t) = l x + t * b := by
    have hp : (x, t) = (x, (0 : ℝ)) + t • ((0 : E), (1 : ℝ)) := by simp
    rw [hp, map_add, map_smul]
    rfl
  have hb : b < 0 := by
    have hu := hgA (x₀, r + 1) hint
    have hv := hgB (x₀, a - s) (by change ψ x₀ ≤ _; rw [hs]; exact WithTop.coe_le_coe.mpr (by linarith))
    rw [g_eq] at hu hv
    have hmin := ha x₀ r s hr hs
    by_contra hn
    have hn' : 0 ≤ b := le_of_not_gt hn
    have hmul := mul_le_mul_of_nonneg_right (show a - s ≤ r + 1 by linarith) hn'
    linarith
  let f : E →L[ℝ] ℝ := (-b)⁻¹ • l
  let c : ℝ := d / b
  have hf (x : E) : f x = -l x / b := by
    simp only [f, smul_apply, smul_eq_mul, inv_neg, div_eq_mul_inv]
    ring
  refine ⟨f, c, ?_, ?_⟩
  · intro x
    by_cases hx : φ x = ⊤
    · rw [hx]; exact le_top
    obtain ⟨r', hr'⟩ := WithTop.ne_top_iff_exists.mp hx
    have h := hgA' (x, r') (by change φ x ≤ _; rw [← hr'])
    rw [g_eq] at h
    rw [← hr', WithTop.coe_le_coe, hf]
    change -l x / b + d / b ≤ r'
    have heq : (-l x + d) / b = -l x / b + d / b := add_div _ _ _
    rw [← heq]
    exact (div_le_iff_of_neg hb).mpr (by linarith)
  · intro x
    by_cases hx : ψ x = ⊤
    · rw [hx]; exact le_top
    obtain ⟨s', hs'⟩ := WithTop.ne_top_iff_exists.mp hx
    have h := hgB (x, a - s') (by change ψ x ≤ _; rw [← hs']; exact WithTop.coe_le_coe.mpr (by linarith))
    rw [g_eq] at h
    rw [← hs', WithTop.coe_le_coe, hf]
    change -(-l x / b) + (a - d / b) ≤ s'
    have hdiv : a - s' ≤ (d - l x) / b := (le_div_iff_of_neg hb).mpr (by linarith)
    rw [sub_div] at hdiv
    simp only [neg_div, neg_neg]
    linarith
end Separation

section Assembly
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- At a finite primal value the separator supplies a maximizing dual functional. -/
theorem exists_dual_eq_of_primal_eq (φ ψ : ExtendedFunction E)
    (hφ : ExtendedConvexFunctions.Spec.ExtendedConvexValue E φ)
    (hψ : ExtendedConvexFunctions.Spec.ExtendedConvexValue E ψ)
    (x₀ : E) (hx : φ x₀ ≠ ⊤) (hy : ψ x₀ ≠ ⊤) (hc : ContinuousAt φ x₀)
    (a : ℝ) (hvalue : primalValue φ ψ = (a : EReal)) :
    ∃ f : E →L[ℝ] ℝ, dualValue φ ψ f = (a : EReal) := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hx
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy
  have ha : ∀ (x : E) (r' s' : ℝ), φ x = (r' : WithTop ℝ) →
      ψ x = (s' : WithTop ℝ) → a ≤ r' + s' := by
    intro x r' s' hr' hs'
    have h : primalValue φ ψ ≤ val (φ x) + val (ψ x) := iInf_le _ x
    rw [hvalue, hr', hs', val_coe, val_coe, ← EReal.coe_add] at h
    exact EReal.coe_le_coe_iff.mp h
  obtain ⟨f, c, hp, hq⟩ :=
    affine_minorants_of_lower_bound φ ψ hφ hψ x₀ r s hr.symm hs.symm hc a ha
  refine ⟨f, le_antisymm ?_ (dualValue_ge_of_affine_minorants φ ψ a c f hp hq)⟩
  rw [← hvalue]
  exact (le_iSup (fun f : E →L[ℝ] ℝ => dualValue φ ψ f) f).trans (weak_duality φ ψ)

end Assembly

/-- Fenchel–Rockafellar duality and finite-value dual attainment on the given
real Hausdorff locally convex space. The proof does not assert primal attainment. -/
theorem fenchel_rockafellar : Spec.Duality := by
  intro E _ _ _ _ hE φ ψ _ _ hφ hψ x₀ hx hy hc
  let : IsTopologicalAddGroup E := hE.1.1
  let : ContinuousSMul ℝ E := hE.1.2
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hx
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy
  have hupper : primalValue φ ψ ≤ ((r + s : ℝ) : EReal) := by
    have h : primalValue φ ψ ≤ val (φ x₀) + val (ψ x₀) := iInf_le _ x₀
    simpa only [hr.symm, hs.symm, val_coe, ← EReal.coe_add] using h
  have hnTop : primalValue φ ψ ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) hupper
  have hattain := exists_dual_eq_of_primal_eq φ ψ hφ hψ x₀ hx hy hc
  refine ⟨le_antisymm ?_ (weak_duality φ ψ), hattain⟩
  by_cases hbot : primalValue φ ψ = ⊥
  · rw [hbot]
    exact bot_le
  · let a := (primalValue φ ψ).toReal
    have ha : primalValue φ ψ = (a : EReal) := (EReal.coe_toReal hnTop hbot).symm
    obtain ⟨f, hf⟩ := hattain a ha
    rw [ha, ← hf]
    exact le_iSup (fun g : E →L[ℝ] ℝ => dualValue φ ψ g) f

end ExpandedFA.P1.FenchelRockafellar
