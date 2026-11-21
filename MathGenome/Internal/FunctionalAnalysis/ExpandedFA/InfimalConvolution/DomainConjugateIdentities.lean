import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.InfimalConvolution.DomainConjugateIdentities
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.InfimalConvolution.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06FenchelMoreau
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04CanonicalMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

namespace ExpandedFA.InfimalConvolution.DomainConjugateIdentities

open scoped Pointwise

open ExpandedFA.P1 ExtendedConvexFunctions C06Conjugates C06FenchelMoreau
open Definitions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A real lower bound for each summand, obtained by testing its supremum. -/
theorem conjugate_lower_bound (φ : ExtendedFunction E) (x : E) (r : ℝ)
    (hx : φ x = (r : WithTop ℝ)) (f : E →L[ℝ] ℝ) :
    ((f x - r : ℝ) : EReal) ≤ convexConjugate E φ f := by
  calc
    _ = (f x : EReal) - extendedRealValue (φ x) := by rw [hx]; rfl
    _ ≤ _ := le_iSup (fun y => (f y : EReal) - extendedRealValue (φ y)) x

theorem affine_lower_bound : Spec.AffineLowerBound := by
  intro E _ _ φ ψ x r s hx hy f
  change ((f x - r - s : ℝ) : EReal) ≤ infimalConvolution E φ ψ f
  apply le_iInf
  intro g
  have h := add_le_add (conjugate_lower_bound φ x r hx (f - g))
    (conjugate_lower_bound ψ x s hy g)
  calc
    _ = (((f - g) x - r : ℝ) : EReal) + ((g x - s : ℝ) : EReal) := by
      rw [← EReal.coe_add]
      congr 1
      simp only [sub_apply]
      ring
    _ ≤ _ := h

theorem convolution_ne_bot (φ ψ : ExtendedFunction E)
    (hcommon : (ExtendedConvexFunctions.Spec.finiteDomainValue E φ ∩
      ExtendedConvexFunctions.Spec.finiteDomainValue E ψ).Nonempty)
    (f : E →L[ℝ] ℝ) : infimalConvolution E φ ψ f ≠ ⊥ := by
  obtain ⟨x, hx, hy⟩ := hcommon
  obtain ⟨r, hr⟩ := (mem_finiteDomain E φ x).mp hx
  obtain ⟨s, hs⟩ := (mem_finiteDomain E ψ x).mp hy
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (affine_lower_bound E φ ψ x r s hr hs f)

/-- A finite split cost forces both summands to be finite. -/
theorem finite_split_of_cost_lt (φ ψ : ExtendedFunction E)
    (hp : ExtendedConvexFunctions.Spec.ProperValue E φ)
    (hq : ExtendedConvexFunctions.Spec.ProperValue E ψ)
    (f g : E →L[ℝ] ℝ) (t : ℝ)
    (hc : conjugateSplitCost E φ ψ f g < (t : EReal)) :
    ∃ r s : ℝ, convexConjugate E φ (f - g) = (r : EReal) ∧
      convexConjugate E ψ g = (s : EReal) ∧ r + s < t := by
  have hn := convexConjugate_ne_bot E φ hp (f - g)
  have hm := convexConjugate_ne_bot E ψ hq g
  change convexConjugate E φ (f - g) ≠ ⊥ at hn
  change convexConjugate E ψ g ≠ ⊥ at hm
  have ht : convexConjugate E φ (f - g) ≠ ⊤ := by
    intro hh
    have : conjugateSplitCost E φ ψ f g = ⊤ := by
      simp only [conjugateSplitCost, hh, EReal.top_add_of_ne_bot hm]
    simp [this] at hc
  have hu : convexConjugate E ψ g ≠ ⊤ := by
    intro hh
    have : conjugateSplitCost E φ ψ f g = ⊤ := by
      simp only [conjugateSplitCost, hh, EReal.add_top_of_ne_bot hn]
    simp [this] at hc
  refine ⟨_, _, (EReal.coe_toReal ht hn).symm, (EReal.coe_toReal hu hm).symm, ?_⟩
  rw [conjugateSplitCost, ← EReal.coe_toReal ht hn, ← EReal.coe_toReal hu hm,
    ← EReal.coe_add, EReal.coe_lt_coe_iff] at hc
  exact hc

theorem near_minimizing_split (φ ψ : ExtendedFunction E)
    (hp : ExtendedConvexFunctions.Spec.ProperValue E φ)
    (hq : ExtendedConvexFunctions.Spec.ProperValue E ψ)
    (f : E →L[ℝ] ℝ) (t : ℝ) (h : infimalConvolution E φ ψ f < (t : EReal)) :
    ∃ (g : E →L[ℝ] ℝ) (r s : ℝ),
      convexConjugate E φ (f - g) = (r : EReal) ∧
      convexConjugate E ψ g = (s : EReal) ∧ r + s < t := by
  obtain ⟨g, hg⟩ := iInf_lt_iff.mp h
  obtain ⟨r, s, hr, hs, hlt⟩ := finite_split_of_cost_lt φ ψ hp hq f g t hg
  exact ⟨g, r, s, hr, hs, hlt⟩

theorem proper_convolution : Spec.ProperConvolution := by
  intro E _ _ φ ψ hp hq hcommon
  refine ⟨convolution_ne_bot φ ψ hcommon, ?_⟩
  obtain ⟨a, r, hr⟩ := (convexConjugate_proper E φ hp.1 hp.2.1 hp.2.2).2
  obtain ⟨b, s, hs⟩ := (convexConjugate_proper E ψ hq.1 hq.2.1 hq.2.2).2
  change convexConjugate E φ a = (r : EReal) at hr
  change convexConjugate E ψ b = (s : EReal) at hs
  have hle : infimalConvolution E φ ψ (a + b) ≤ ((r + s : ℝ) : EReal) := by
    calc
      _ ≤ conjugateSplitCost E φ ψ (a + b) b :=
        iInf_le (conjugateSplitCost E φ ψ (a + b)) b
      _ = _ := by rw [conjugateSplitCost, add_sub_cancel_right, hr, hs, ← EReal.coe_add]
  have ht := ne_top_of_le_ne_top (EReal.coe_ne_top _) hle
  exact ⟨a + b, _, (EReal.coe_toReal ht (convolution_ne_bot φ ψ hcommon _)).symm⟩

theorem domain_identity : Spec.DomainIdentity := by
  intro E _ _ φ ψ hp hq hcommon
  ext f
  constructor
  · rintro ⟨t, ht⟩
    change infimalConvolution E φ ψ f = (t : EReal) at ht
    obtain ⟨g, r, s, hr, hs, _⟩ := near_minimizing_split φ ψ hp.1 hq.1 f (t + 1)
      (by rw [ht]; exact EReal.coe_lt_coe_iff.mpr (by linarith))
    exact ⟨f - g, ⟨r, hr⟩, g, ⟨s, hs⟩, sub_add_cancel f g⟩
  · rintro ⟨a, ⟨r, hr⟩, b, ⟨s, hs⟩, rfl⟩
    change convexConjugate E φ a = (r : EReal) at hr
    change convexConjugate E ψ b = (s : EReal) at hs
    have hle : infimalConvolution E φ ψ (a + b) ≤ ((r + s : ℝ) : EReal) := by
      calc
        _ ≤ conjugateSplitCost E φ ψ (a + b) b :=
          iInf_le (conjugateSplitCost E φ ψ (a + b)) b
        _ = _ := by rw [conjugateSplitCost, add_sub_cancel_right, hr, hs, ← EReal.coe_add]
    exact ⟨_, (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) hle)
      (convolution_ne_bot φ ψ hcommon _)).symm⟩

/-- Addition on EReal preserves suprema, including the bottom cases.
This is used only for independent suprema, not for infima. -/
theorem ereal_add_iSup {ι : Sort*} (c : EReal) (u : ι → EReal) :
    c + (⨆ i, u i) = ⨆ i, c + u i := by
  induction c with
  | bot => simp
  | coe c =>
    apply le_antisymm
    · have hh : (⨆ i, u i) ≤ (⨆ i, (c : EReal) + u i) - (c : EReal) := by
        apply iSup_le
        intro i
        apply (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot c))
          (.inl (EReal.coe_ne_top c))).mpr
        simpa only [add_comm] using le_iSup (fun i => (c : EReal) + u i) i
      simpa only [add_comm] using EReal.add_le_of_le_sub hh
    · exact iSup_le fun i => add_le_add le_rfl (le_iSup u i)
  | top =>
    by_cases hu : (⨆ i, u i) = ⊥
    · have hi : ∀ i, u i = ⊥ := iSup_eq_bot.mp hu
      simp [hi]
    · obtain ⟨i, hi⟩ : ∃ i, u i ≠ ⊥ := by
        by_contra hh
        push Not at hh
        exact hu (by simp [hh])
      rw [EReal.top_add_of_ne_bot hu]
      apply le_antisymm ?_ le_top
      calc
        ⊤ = (⊤ : EReal) + u i := (EReal.top_add_of_ne_bot hi).symm
        _ ≤ ⨆ j, (⊤ : EReal) + u j := le_iSup (fun j => (⊤ : EReal) + u j) i

theorem ereal_iSup_add {ι : Sort*} (u : ι → EReal) (c : EReal) :
    (⨆ i, u i) + c = ⨆ i, u i + c := by
  simpa only [add_comm] using ereal_add_iSup c u

theorem convex_convolution : Spec.ConvexConvolution := by
  intro E _ _ φ ψ hp hq _ f g r s a b hf hg ha hb hab
  change infimalConvolution E φ ψ f = (r : EReal) at hf
  change infimalConvolution E φ ψ g = (s : EReal) at hg
  change infimalConvolution E φ ψ (a • f + b • g) ≤ _
  by_contra hn
  obtain ⟨t, ht, hth⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  have hrt : a * r + b * s < t := EReal.coe_lt_coe_iff.mp ht
  let δ := (t - (a * r + b * s)) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨u, r₁, r₂, hr₁, hr₂, hru⟩ := near_minimizing_split φ ψ hp.1 hq.1 f (r + δ)
    (by rw [hf]; exact EReal.coe_lt_coe_iff.mpr (by linarith))
  obtain ⟨v, s₁, s₂, hs₁, hs₂, hsv⟩ := near_minimizing_split φ ψ hp.1 hq.1 g (s + δ)
    (by rw [hg]; exact EReal.coe_lt_coe_iff.mpr (by linarith))
  have hφ := convexConjugate_convex E φ hp.1 (f - u) (g - v) r₁ s₁ a b
    hr₁ hs₁ ha hb hab
  have hψ := convexConjugate_convex E ψ hq.1 u v r₂ s₂ a b
    hr₂ hs₂ ha hb hab
  change convexConjugate E φ (a • (f - u) + b • (g - v)) ≤ _ at hφ
  change convexConjugate E ψ (a • u + b • v) ≤ _ at hψ
  have hsplit : a • f + b • g - (a • u + b • v) =
      a • (f - u) + b • (g - v) := by module
  have hbound : infimalConvolution E φ ψ (a • f + b • g) ≤
      ((a * r₁ + b * s₁ + (a * r₂ + b * s₂) : ℝ) : EReal) := by
    calc
      _ ≤ conjugateSplitCost E φ ψ (a • f + b • g) (a • u + b • v) := iInf_le _ _
      _ ≤ _ := by
        simpa only [conjugateSplitCost, hsplit, ← EReal.coe_add] using add_le_add hφ hψ
  have hreal : a * r₁ + b * s₁ + (a * r₂ + b * s₂) < t := by
    have h1 := mul_le_mul_of_nonneg_left hru.le ha
    have h2 := mul_le_mul_of_nonneg_left hsv.le hb
    have hsum : a * δ + b * δ = δ := by nlinarith [congrArg (fun x : ℝ => x * δ) hab]
    dsimp [δ] at *
    nlinarith
  exact (not_lt_of_ge hbound) ((EReal.coe_lt_coe_iff.mpr hreal).trans hth)

theorem conjugate_identity : Spec.ConjugateIdentity := by
  intro E _ _ φ ψ hp hq hcommon x
  change Spec.fullConjugate (E →L[ℝ] ℝ) (infimalConvolution E φ ψ)
    (C04CanonicalMap.canonicalEvaluation ℝ E x) =
      extendedRealValue (φ x) + extendedRealValue (ψ x)
  apply le_antisymm
  · by_cases hx : φ x = ⊤
    · rw [hx]
      change _ ≤ (⊤ : EReal) + extendedRealValue (ψ x)
      have hy' : extendedRealValue (ψ x) ≠ ⊥ := extendedRealValue_conventions.2.2.1 (ψ x)
      rw [EReal.top_add_of_ne_bot hy']
      exact le_top
    by_cases hy : ψ x = ⊤
    · rw [hy]
      change _ ≤ extendedRealValue (φ x) + (⊤ : EReal)
      have hx' : extendedRealValue (φ x) ≠ ⊥ := extendedRealValue_conventions.2.2.1 (φ x)
      rw [EReal.add_top_of_ne_bot hx']
      exact le_top
    obtain ⟨r, hr⟩ := (mem_finiteDomain E φ x).mp hx
    obtain ⟨s, hs⟩ := (mem_finiteDomain E ψ x).mp hy
    unfold Spec.fullConjugate
    apply iSup_le
    intro f
    have h := EReal.sub_le_sub (le_refl (f x : EReal))
      (affine_lower_bound E φ ψ x r s hr hs f)
    convert h using 1
    · rfl
    · rw [hr, hs]
      change (r : EReal) + (s : EReal) =
        (f x : EReal) - ((f x - r - s : ℝ) : EReal)
      rw [← EReal.coe_add, ← EReal.coe_sub]
      congr 1
      ring
  · have hsplit (a b : E →L[ℝ] ℝ) :
        ((a x : EReal) - convexConjugate E φ a) +
          ((b x : EReal) - convexConjugate E ψ b) ≤
            Spec.fullConjugate (E →L[ℝ] ℝ) (infimalConvolution E φ ψ)
              (C04CanonicalMap.canonicalEvaluation ℝ E x) := by
      calc
        _ = ((a + b) x : EReal) - conjugateSplitCost E φ ψ (a + b) b := by
          simp only [conjugateSplitCost, add_sub_cancel_right,
            add_apply, EReal.coe_add]
          exact (EReal.add_sub_add_comm
            (.inl (convexConjugate_ne_bot E φ hp.1 a))
            (.inr (convexConjugate_ne_bot E ψ hq.1 b))).symm
        _ ≤ ((a + b) x : EReal) - infimalConvolution E φ ψ (a + b) :=
          EReal.sub_le_sub le_rfl (iInf_le _ b)
        _ ≤ _ := by
          change _ ≤ ⨆ c : E →L[ℝ] ℝ, (c x : EReal) - infimalConvolution E φ ψ c
          exact le_iSup (fun c : E →L[ℝ] ℝ => (c x : EReal) -
            infimalConvolution E φ ψ c) (a + b)
    have hp' : convexBiconjugate E φ x = extendedRealValue (φ x) :=
      fenchel_moreau E φ hp.1 hp.2.1 hp.2.2 x
    have hq' : convexBiconjugate E ψ x = extendedRealValue (ψ x) :=
      fenchel_moreau E ψ hq.1 hq.2.1 hq.2.2 x
    rw [← hp', ← hq']
    change (⨆ a : E →L[ℝ] ℝ, (a x : EReal) - convexConjugate E φ a) +
      (⨆ b : E →L[ℝ] ℝ, (b x : EReal) - convexConjugate E ψ b) ≤ _
    rw [ereal_iSup_add]
    apply iSup_le
    intro a
    rw [ereal_add_iSup]
    exact iSup_le (hsplit a)

theorem biconjugate_identity : Spec.BiconjugateIdentity := by
  intro E _ _ href φ ψ hp hq hcommon f
  change (⨆ L : (E →L[ℝ] ℝ) →L[ℝ] ℝ, (L f : EReal) -
    Spec.fullConjugate (E →L[ℝ] ℝ) (infimalConvolution E φ ψ) L) =
    convexConjugate E (fun x => φ x + ψ x) f
  have href' : Function.Surjective (C04CanonicalMap.canonicalEvaluation ℝ E) := href
  have hc (x : E) :
      Spec.fullConjugate (E →L[ℝ] ℝ) (infimalConvolution E φ ψ)
        (C04CanonicalMap.canonicalEvaluation ℝ E x) =
        extendedRealValue (φ x) + extendedRealValue (ψ x) :=
    conjugate_identity E φ ψ hp hq hcommon x
  have hsum (x : E) : extendedRealValue (φ x + ψ x) =
      extendedRealValue (φ x) + extendedRealValue (ψ x) := rfl
  apply le_antisymm
  · apply iSup_le
    intro L
    obtain ⟨x, rfl⟩ := href' L
    rw [hc x]
    change (f x : EReal) - _ ≤ _
    rw [← hsum]
    exact le_iSup (fun y : E => (f y : EReal) - extendedRealValue (φ y + ψ y)) x
  · unfold convexConjugate
    apply iSup_le
    intro x
    rw [hsum, ← hc x]
    exact le_iSup (fun L : (E →L[ℝ] ℝ) →L[ℝ] ℝ => (L f : EReal) -
      Spec.fullConjugate (E →L[ℝ] ℝ) (infimalConvolution E φ ψ) L)
      (C04CanonicalMap.canonicalEvaluation ℝ E x)

end ExpandedFA.InfimalConvolution.DomainConjugateIdentities
