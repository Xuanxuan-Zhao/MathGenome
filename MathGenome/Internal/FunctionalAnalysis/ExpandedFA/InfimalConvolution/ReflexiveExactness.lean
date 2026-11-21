import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.InfimalConvolution.ReflexiveExactness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.InfimalConvolution.DomainConjugateIdentities
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.InfimalConvolution.UniformSplitBounds
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Maps.Proper.Basic

namespace ExpandedFA.InfimalConvolution.ReflexiveExactness

open ExpandedFA.P1 ExtendedConvexFunctions C06Conjugates C06FenchelMoreau
open Definitions DomainConjugateIdentities
open Filter Set
open scoped Topology Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Finite-domain tests describe the entire cost sublevel, including infinite costs. -/
lemma split_cost_le_iff (φ ψ : ExtendedFunction E) (f g : E →L[ℝ] ℝ) (α : ℝ) :
    conjugateSplitCost E φ ψ f g ≤ (α : EReal) ↔
    ∀ (x y : E) (r s : ℝ), φ x = (r : WithTop ℝ) → ψ y = (s : WithTop ℝ) →
      f x + g (y - x) - r - s ≤ α := by
  constructor
  · intro hc x y r s hx hy
    have h := UniformSplitBounds.split_evaluation_le φ ψ f g x y r s α hx hy hc
    linarith
  · intro h
    unfold conjugateSplitCost convexConjugate
    rw [ereal_iSup_add]
    apply iSup_le
    intro x
    rw [ereal_add_iSup]
    apply iSup_le
    intro y
    by_cases hx : φ x = ⊤
    · rw [hx]
      change ((↑((f - g) x) : EReal) - ⊤) + _ ≤ _
      rw [EReal.sub_top, EReal.bot_add]
      exact bot_le
    by_cases hy : ψ y = ⊤
    · rw [hy]
      change _ + ((↑(g y) : EReal) - ⊤) ≤ _
      rw [EReal.sub_top, EReal.add_bot]
      exact bot_le
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hx
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy
    rw [← hr, ← hs]
    change (((f - g) x : EReal) - (r : EReal)) + ((g y : EReal) - (s : EReal)) ≤ _
    rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have hh := h x y r s hr.symm hs.symm
    simp only [sub_apply, map_sub] at *
    linarith

/-- The total functional has its norm topology and the split variable its weak-star topology. -/
lemma split_sublevel_closed (φ ψ : ExtendedFunction E) (α : ℝ) :
    IsClosed {p : (E →L[ℝ] ℝ) × WeakDual ℝ E |
      conjugateSplitCost E φ ψ p.1 p.2.toStrongDual ≤ (α : EReal)} := by
  have heq : {p : (E →L[ℝ] ℝ) × WeakDual ℝ E |
      conjugateSplitCost E φ ψ p.1 p.2.toStrongDual ≤ (α : EReal)} =
      ⋂ (x : E) (y : E) (r : ℝ) (s : ℝ) (_ : φ x = (r : WithTop ℝ))
        (_ : ψ y = (s : WithTop ℝ)),
      {p | p.1 x + p.2 (y - x) - r - s ≤ α} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, split_cost_le_iff, WeakDual.toStrongDual_apply]
  rw [heq]
  refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun r =>
    isClosed_iInter fun s => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
  exact isClosed_le
    ((((ContinuousLinearMap.apply ℝ ℝ x).continuous.comp continuous_fst).add
      ((WeakDual.eval_continuous (y - x)).comp continuous_snd)).sub
      continuous_const |>.sub continuous_const) continuous_const

/-- Each cost is bounded below by the convolution's affine lower bound. -/
lemma split_cost_ne_bot (φ ψ : ExtendedFunction E)
    (hcommon : (Definitions.finiteDomain E φ ∩ Definitions.finiteDomain E ψ).Nonempty)
    (f g : E →L[ℝ] ℝ) : conjugateSplitCost E φ ψ f g ≠ ⊥ :=
  ne_bot_of_le_ne_bot (convolution_ne_bot φ ψ hcommon f) (iInf_le _ g)

lemma split_cost_lsc (φ ψ : ExtendedFunction E)
    (hcommon : (Definitions.finiteDomain E φ ∩ Definitions.finiteDomain E ψ).Nonempty)
    (f : E →L[ℝ] ℝ) :
    LowerSemicontinuous (fun g : WeakDual ℝ E =>
      conjugateSplitCost E φ ψ f g.toStrongDual) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro α
  induction α with
  | bot =>
    have heq : {g : WeakDual ℝ E | conjugateSplitCost E φ ψ f g.toStrongDual ≤ ⊥} = ∅ := by
      ext g
      simp [le_bot_iff, split_cost_ne_bot φ ψ hcommon]
    simpa only [preimage, mem_Iic, heq] using isClosed_empty
  | coe α =>
    exact (split_sublevel_closed φ ψ α).preimage (continuous_const.prodMk continuous_id)
  | top => simp

/-- Uniform boundedness and Banach–Alaoglu give a compact ball containing a
prescribed split sublevel, uniformly for all total functionals in B. -/
lemma compact_split_bound [CompleteSpace E] (φ ψ : ExtendedFunction E)
    (hcone : domainDifferenceCone E φ ψ = univ)
    (B : Set (E →L[ℝ] ℝ)) (hB : Bornology.IsBounded B) (α : ℝ) :
    ∃ R : ℝ, ∀ f ∈ B, ∀ g : E →L[ℝ] ℝ,
      conjugateSplitCost E φ ψ f g ≤ (α : EReal) →
      StrongDual.toWeakDual g ∈ WeakDual.toStrongDual ⁻¹'
        Metric.closedBall (0 : E →L[ℝ] ℝ) R := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp
    (UniformSplitBounds.bounded_split_sublevel φ ψ hcone B hB α)
  refine ⟨R, ?_⟩
  intro f hf g hg
  change dist g 0 ≤ R
  simpa only [dist_zero_right] using hR g ⟨f, hf, hg⟩

/-- Every finite infimum is attained. This compactness argument only needs
Banach completeness and the full cone, in addition to a common domain point. -/
lemma minimizing_split [CompleteSpace E] (φ ψ : ExtendedFunction E)
    (hcommon : (Definitions.finiteDomain E φ ∩ Definitions.finiteDomain E ψ).Nonempty)
    (hcone : domainDifferenceCone E φ ψ = univ)
    (f : E →L[ℝ] ℝ) (α : ℝ) (hα : infimalConvolution E φ ψ f < (α : EReal)) :
    ∃ g, conjugateSplitCost E φ ψ f g = infimalConvolution E φ ψ f := by
  obtain ⟨g₀, hg₀⟩ := iInf_lt_iff.mp hα
  obtain ⟨R, hR⟩ := compact_split_bound φ ψ hcone {f} Bornology.isBounded_singleton α
  let K : Set (WeakDual ℝ E) := WeakDual.toStrongDual ⁻¹'
    Metric.closedBall (0 : E →L[ℝ] ℝ) R
  have hgK : StrongDual.toWeakDual g₀ ∈ K := hR f (mem_singleton f) g₀ hg₀.le
  obtain ⟨g, hg, hmin⟩ := ((split_cost_lsc φ ψ hcommon f).lowerSemicontinuousOn K).exists_isMinOn
    ⟨_, hgK⟩ (WeakDual.isCompact_closedBall (𝕜 := ℝ) (E := E) 0 R)
  refine ⟨g.toStrongDual, le_antisymm ?_ (iInf_le _ _)⟩
  apply le_iInf
  intro u
  by_cases hu : conjugateSplitCost E φ ψ f u ≤ (α : EReal)
  · exact hmin (hR f (mem_singleton f) u hu)
  · exact (hmin hgK).trans (hg₀.le.trans (le_of_not_ge hu))

lemma split_le_iff [CompleteSpace E] (φ ψ : ExtendedFunction E)
    (hcommon : (Definitions.finiteDomain E φ ∩ Definitions.finiteDomain E ψ).Nonempty)
    (hcone : domainDifferenceCone E φ ψ = univ)
    (f : E →L[ℝ] ℝ) (α : ℝ) :
    infimalConvolution E φ ψ f ≤ (α : EReal) ↔
      ∃ g, conjugateSplitCost E φ ψ f g ≤ (α : EReal) := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := minimizing_split φ ψ hcommon hcone f (α + 1)
      (h.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith)))
    exact ⟨g, hg ▸ h⟩
  · rintro ⟨g, hg⟩
    exact (iInf_le _ g).trans hg

/-- Projection of a closed split sublevel is closed when the total functionals
are restricted to a closed bounded set. The compact factor is a dual ball. -/
lemma bounded_sublevel_closed [CompleteSpace E] (φ ψ : ExtendedFunction E)
    (hcommon : (Definitions.finiteDomain E φ ∩ Definitions.finiteDomain E ψ).Nonempty)
    (hcone : domainDifferenceCone E φ ψ = univ)
    (B : Set (E →L[ℝ] ℝ)) (hB : Bornology.IsBounded B) (hcB : IsClosed B) (α : ℝ) :
    IsClosed (B ∩ {f | infimalConvolution E φ ψ f ≤ (α : EReal)}) := by
  obtain ⟨R, hR⟩ := compact_split_bound φ ψ hcone B hB α
  let K : Set (WeakDual ℝ E) := WeakDual.toStrongDual ⁻¹'
    Metric.closedBall (0 : E →L[ℝ] ℝ) R
  have hK : IsCompact K := WeakDual.isCompact_closedBall 0 R
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let Z : Set ((E →L[ℝ] ℝ) × K) :=
    {p | p.1 ∈ B ∧ conjugateSplitCost E φ ψ p.1 p.2.val.toStrongDual ≤ (α : EReal)}
  have hZ : IsClosed Z := (hcB.preimage continuous_fst).inter
    ((split_sublevel_closed φ ψ α).preimage
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  have heq : B ∩ {f | infimalConvolution E φ ψ f ≤ (α : EReal)} = Prod.fst '' Z := by
    ext f
    constructor
    · rintro ⟨hfB, hf⟩
      obtain ⟨g, hg⟩ := (split_le_iff φ ψ hcommon hcone f α).mp hf
      exact ⟨(f, ⟨StrongDual.toWeakDual g, hR f hfB g hg⟩), ⟨hfB, hg⟩, rfl⟩
    · rintro ⟨⟨f, g⟩, ⟨hfB, hg⟩, rfl⟩
      exact ⟨hfB, (split_le_iff φ ψ hcommon hcone f α).mpr ⟨g.val.toStrongDual, hg⟩⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace Z hZ

/-- Closedness is local in the norm topology, so the bounded projection
result suffices without any weak-star boundedness assumption on a net of f's. -/
lemma convolution_sublevel_closed [CompleteSpace E] (φ ψ : ExtendedFunction E)
    (hcommon : (Definitions.finiteDomain E φ ∩ Definitions.finiteDomain E ψ).Nonempty)
    (hcone : domainDifferenceCone E φ ψ = univ) (α : ℝ) :
    IsClosed {f | infimalConvolution E φ ψ f ≤ (α : EReal)} := by
  apply isClosed_iff_nhds.mpr
  intro f hf
  let B := Metric.closedBall f 1
  have hBnhds : B ∈ 𝓝 f := Metric.closedBall_mem_nhds f (by norm_num)
  have hclosed := bounded_sublevel_closed φ ψ hcommon hcone B
    Metric.isBounded_closedBall Metric.isClosed_closedBall α
  have hmem : f ∈ closure (B ∩ {u | infimalConvolution E φ ψ u ≤ (α : EReal)}) := by
    apply mem_closure_iff_nhds.mpr
    intro U hU
    obtain ⟨u, ⟨huU, huB⟩, hu⟩ := hf (U ∩ B) (inter_mem hU hBnhds)
    exact ⟨u, huU, huB, hu⟩
  exact (hclosed.closure_subset hmem).2

theorem norm_lowerSemicontinuity : Spec.NormLowerSemicontinuity := by
  intro E _ _ _ _ φ ψ _ _ hcommon hcone α
  exact convolution_sublevel_closed φ ψ hcommon hcone α

/-- Transfer the never-bottom convolution to the shared half-extended
representation, apply Fenchel–Moreau there, and transfer back. -/
theorem exact_conjugate_formula : Spec.ExactConjugateFormula := by
  intro E _ _ _ href φ ψ hp hq hcommon hcone f
  change infimalConvolution E φ ψ f = convexConjugate E (fun x => φ x + ψ x) f
  let H : ExtendedFunction (E →L[ℝ] ℝ) :=
    fun u => (infimalConvolution E φ ψ u).unbot (convolution_ne_bot φ ψ hcommon u)
  have hH (u : E →L[ℝ] ℝ) : extendedRealValue (H u) = infimalConvolution E φ ψ u :=
    WithBot.coe_unbot _ _
  have hpH : ExtendedConvexFunctions.Spec.ProperValue (E →L[ℝ] ℝ) H := by
    obtain ⟨u, r, hr⟩ := (proper_convolution E φ ψ hp hq hcommon).2
    change infimalConvolution E φ ψ u = (r : EReal) at hr
    refine ⟨u, ?_⟩
    change H u ≠ ⊤
    intro htop
    have hh := hH u
    rw [htop] at hh
    exact EReal.coe_ne_top r (hr.symm.trans hh.symm)
  have hcH : ExtendedConvexFunctions.Spec.ExtendedConvexValue (E →L[ℝ] ℝ) H := by
    intro u v r s a b hu hv ha hb hab
    have hu' : infimalConvolution E φ ψ u = (r : EReal) := by rw [← hH u, hu]; rfl
    have hv' : infimalConvolution E φ ψ v = (s : EReal) := by rw [← hH v, hv]; rfl
    apply WithBot.coe_le_coe.mp
    change extendedRealValue (H (a • u + b • v)) ≤ ((a * r + b * s : ℝ) : EReal)
    rw [hH]
    exact convex_convolution E φ ψ hp hq hcommon u v r s a b hu' hv' ha hb hab
  have hlH : ExtendedConvexFunctions.Spec.LowerSemicontinuousValue (E →L[ℝ] ℝ) H := by
    intro r
    have heq : {u | H u ≤ (r : WithTop ℝ)} =
        {u | infimalConvolution E φ ψ u ≤ (r : EReal)} := by
      ext u
      change H u ≤ (r : WithTop ℝ) ↔ infimalConvolution E φ ψ u ≤ (r : EReal)
      rw [← hH u]
      exact WithBot.coe_le_coe.symm
    rw [heq]
    exact convolution_sublevel_closed φ ψ hcommon hcone r
  have hc (L : (E →L[ℝ] ℝ) →L[ℝ] ℝ) :
      convexConjugate (E →L[ℝ] ℝ) H L =
        DomainConjugateIdentities.Spec.fullConjugate (E →L[ℝ] ℝ)
          (infimalConvolution E φ ψ) L := by
    unfold convexConjugate DomainConjugateIdentities.Spec.fullConjugate
    simp_rw [hH]
  have hfm := fenchel_moreau (E →L[ℝ] ℝ) H hpH hcH hlH f
  change convexBiconjugate (E →L[ℝ] ℝ) H f = extendedRealValue (H f) at hfm
  rw [hH] at hfm
  rw [← hfm]
  unfold convexBiconjugate
  simp_rw [hc]
  exact biconjugate_identity E href φ ψ hp hq hcommon f

theorem finite_attainment : Spec.FiniteAttainment := by
  intro E _ _ _ href φ ψ hp hq hcommon hcone f r hr
  have hh := exact_conjugate_formula E href φ ψ hp hq hcommon hcone f
  change infimalConvolution E φ ψ f = convexConjugate E (fun x => φ x + ψ x) f at hh
  change convexConjugate E (fun x => φ x + ψ x) f = (r : EReal) at hr
  rw [hr] at hh
  obtain ⟨g, hg⟩ := minimizing_split φ ψ hcommon hcone f (r + 1)
    (by rw [hh]; exact EReal.coe_lt_coe_iff.mpr (by linarith))
  exact ⟨g, hg.trans hh⟩

theorem exact_domain_sum : Spec.ExactDomainSum := by
  intro E _ _ _ href φ ψ hp hq hcommon hcone
  have hdom := domain_identity E φ ψ hp hq hcommon
  change {f | ∃ r : ℝ, infimalConvolution E φ ψ f = (r : EReal)} = _ at hdom
  have heq (f : E →L[ℝ] ℝ) : infimalConvolution E φ ψ f =
      convexConjugate E (fun x => φ x + ψ x) f :=
    exact_conjugate_formula E href φ ψ hp hq hcommon hcone f
  simp_rw [heq] at hdom
  exact hdom

end ExpandedFA.InfimalConvolution.ReflexiveExactness
