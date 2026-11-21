import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.InfimalConvolution.ConjugateDomainClosure
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.InfimalConvolution.DomainConjugateIdentities
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12ConvexClosure
import Mathlib.Analysis.LocallyConvex.Separation

namespace ExpandedFA.InfimalConvolution.ConjugateDomainClosure

open scoped Pointwise
open ExpandedFA.P1 ExtendedConvexFunctions C06Conjugates C06FenchelMoreau
open Definitions DomainConjugateIdentities

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A finite biconjugate value lies in the closed finite domain whenever H
has convex finite domain and a continuous affine lower bound. Separation
produces affine minorants of arbitrarily large value at any excluded point. -/
theorem biconjugate_domain_subset_closure (H : V → EReal)
    (hn : ∀ v, H v ≠ ⊥)
    (hc : Convex ℝ {v | ∃ r : ℝ, H v = (r : EReal)})
    (A : V →L[ℝ] ℝ) (c : ℝ) (ha : ∀ v, ((A v + c : ℝ) : EReal) ≤ H v)
    (x : V) (R : ℝ)
    (hx : (⨆ L : V →L[ℝ] ℝ,
      (L x : EReal) - DomainConjugateIdentities.Spec.fullConjugate V H L) = (R : EReal)) :
    x ∈ closure {v | ∃ r : ℝ, H v = (r : EReal)} := by
  by_contra hnot
  obtain ⟨L, α, hL, hα⟩ :=
    geometric_hahn_banach_closed_point hc.closure isClosed_closure hnot
  let t := max 0 ((R - A x - c + 1) / (L x - α))
  have ht : 0 ≤ t := le_max_left _ _
  have hgap : 0 < L x - α := sub_pos.mpr hα
  have hlarge : R - A x - c + 1 ≤ t * (L x - α) :=
    (div_le_iff₀ hgap).mp (le_max_right _ _)
  let M : V →L[ℝ] ℝ := A + t • L
  have hbound : DomainConjugateIdentities.Spec.fullConjugate V H M ≤
      ((t * α - c : ℝ) : EReal) := by
    apply iSup_le
    intro v
    by_cases hv : H v = ⊤
    · simp only [hv, EReal.sub_top, bot_le]
    · let r := (H v).toReal
      have hr : H v = (r : EReal) := (EReal.coe_toReal hv (hn v)).symm
      have hAv : A v + c ≤ r := by
        have hh := ha v
        rw [hr, EReal.coe_le_coe_iff] at hh
        exact hh
      have hLv : L v < α := hL v (subset_closure ⟨r, hr⟩)
      rw [hr, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      change A v + t * L v - r ≤ t * α - c
      nlinarith [mul_le_mul_of_nonneg_left hLv.le ht]
  have hle : ((M x - (t * α - c) : ℝ) : EReal) ≤ (R : EReal) := by
    calc
      _ = (M x : EReal) - ((t * α - c : ℝ) : EReal) := EReal.coe_sub _ _
      _ ≤ (M x : EReal) - DomainConjugateIdentities.Spec.fullConjugate V H M :=
        EReal.sub_le_sub le_rfl hbound
      _ ≤ _ := hx ▸ le_iSup (fun L : V →L[ℝ] ℝ =>
        (L x : EReal) - DomainConjugateIdentities.Spec.fullConjugate V H L) M
  have hreal := EReal.coe_le_coe_iff.mp hle
  change A x + t * L x - (t * α - c) ≤ R at hreal
  nlinarith

/-- Taking a biconjugate can only decrease a function at its finite points. -/
theorem biconjugate_le_at_real (H : V → EReal) (x : V) (r : ℝ)
    (hr : H x = (r : EReal)) :
    (⨆ L : V →L[ℝ] ℝ,
      (L x : EReal) - DomainConjugateIdentities.Spec.fullConjugate V H L) ≤ (r : EReal) := by
  apply iSup_le
  intro L
  have h : ((L x - r : ℝ) : EReal) ≤
      DomainConjugateIdentities.Spec.fullConjugate V H L := by
    calc
      _ = (L x : EReal) - H x := by rw [hr, EReal.coe_sub]
      _ ≤ _ := le_iSup (fun v => (L v : EReal) - H v) x
  calc
    _ ≤ (L x : EReal) - ((L x - r : ℝ) : EReal) := EReal.sub_le_sub le_rfl h
    _ = _ := by rw [← EReal.coe_sub]; congr 1; ring

/-- Convexity of the finite domain in the full extended-real representation. -/
theorem convex_real_domain (H : V → EReal) (hn : ∀ v, H v ≠ ⊥)
    (hc : ∀ (v w : V) (r s a b : ℝ), H v = (r : EReal) → H w = (s : EReal) →
      0 ≤ a → 0 ≤ b → a + b = 1 → H (a • v + b • w) ≤ ((a * r + b * s : ℝ) : EReal)) :
    Convex ℝ {v | ∃ r : ℝ, H v = (r : EReal)} := by
  rintro v ⟨r, hr⟩ w ⟨s, hs⟩ a b ha hb hab
  have ht := ne_top_of_le_ne_top (EReal.coe_ne_top _) (hc v w r s a b hr hs ha hb hab)
  exact ⟨_, (EReal.coe_toReal ht (hn _)).symm⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem sum_proper (φ ψ : ExtendedFunction E)
    (hcommon : (ExtendedConvexFunctions.Spec.finiteDomainValue E φ ∩
      ExtendedConvexFunctions.Spec.finiteDomainValue E ψ).Nonempty) :
    ExtendedConvexFunctions.Spec.ProperValue E (fun x => φ x + ψ x) := by
  obtain ⟨x, hx, hy⟩ := hcommon
  obtain ⟨r, hr⟩ := (mem_finiteDomain E φ x).mp hx
  obtain ⟨s, hs⟩ := (mem_finiteDomain E ψ x).mp hy
  refine ⟨x, ?_⟩
  change φ x + ψ x ≠ ⊤
  rw [hr, hs, ← WithTop.coe_add]
  exact WithTop.coe_ne_top

private theorem convolution_domain_convex (φ ψ : ExtendedFunction E)
    (hp : DomainConjugateIdentities.Spec.Regular E φ)
    (hq : DomainConjugateIdentities.Spec.Regular E ψ)
    (hcommon : (ExtendedConvexFunctions.Spec.finiteDomainValue E φ ∩
      ExtendedConvexFunctions.Spec.finiteDomainValue E ψ).Nonempty) :
    Convex ℝ {f | ∃ r : ℝ, infimalConvolution E φ ψ f = (r : EReal)} :=
  convex_real_domain _ (convolution_ne_bot φ ψ hcommon)
    (convex_convolution E φ ψ hp hq hcommon)

private theorem conjugate_sum_domain_convex (φ ψ : ExtendedFunction E)
    (hcommon : (ExtendedConvexFunctions.Spec.finiteDomainValue E φ ∩
      ExtendedConvexFunctions.Spec.finiteDomainValue E ψ).Nonempty) :
    Convex ℝ (Spec.conjugateSumDomain E φ ψ) :=
  convex_real_domain _ (convexConjugate_ne_bot E _ (sum_proper φ ψ hcommon))
    (convexConjugate_convex E _ (sum_proper φ ψ hcommon))

/-- Equality of norm closures, without any qualification for exact splits. -/
theorem norm_domain_closure : Spec.NormDomainClosure := by
  intro E _ _ href φ ψ hp hq hcommon
  have hdom := domain_identity E φ ψ hp hq hcommon
  change {f | ∃ r : ℝ, infimalConvolution E φ ψ f = (r : EReal)} =
    Spec.sumConjugateDomains E φ ψ at hdom
  have hbic := biconjugate_identity E href φ ψ hp hq hcommon
  change ∀ f : E →L[ℝ] ℝ, (⨆ L : (E →L[ℝ] ℝ) →L[ℝ] ℝ,
    (L f : EReal) - DomainConjugateIdentities.Spec.fullConjugate (E →L[ℝ] ℝ)
      (infimalConvolution E φ ψ) L) = convexConjugate E (fun x => φ x + ψ x) f at hbic
  apply Set.Subset.antisymm
  · apply closure_minimal ?_ isClosed_closure
    intro f hf
    obtain ⟨R, hR⟩ := hf
    change convexConjugate E (fun x => φ x + ψ x) f = (R : EReal) at hR
    rw [← hdom]
    have hn := convolution_ne_bot φ ψ hcommon
    have hc := convolution_domain_convex φ ψ hp hq hcommon
    obtain ⟨x₀, hx, hy⟩ := hcommon
    obtain ⟨r, hr⟩ := (mem_finiteDomain E φ x₀).mp hx
    obtain ⟨s, hs⟩ := (mem_finiteDomain E ψ x₀).mp hy
    apply biconjugate_domain_subset_closure (infimalConvolution E φ ψ)
      hn hc
      (C04CanonicalMap.canonicalEvaluation ℝ E x₀) (-r - s)
      (by
        intro g
        have hh := affine_lower_bound E φ ψ x₀ r s hr hs g
        change ((g x₀ - r - s : ℝ) : EReal) ≤ infimalConvolution E φ ψ g at hh
        change ((g x₀ + (-r - s) : ℝ) : EReal) ≤ infimalConvolution E φ ψ g
        simpa only [sub_eq_add_neg, add_assoc] using hh)
      f R
    exact (hbic f).trans hR
  · apply closure_mono
    rw [← hdom]
    rintro f ⟨r, hr⟩
    have hle : convexConjugate E (fun x => φ x + ψ x) f ≤ (r : EReal) := by
      rw [← hbic f]
      exact biconjugate_le_at_real _ f r hr
    exact ⟨_, (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) hle)
      (convexConjugate_ne_bot E _ (sum_proper φ ψ hcommon) f)).symm⟩

/-- Convexity identifies both norm closures with the respective weak closures. -/
theorem weak_domain_closures : Spec.WeakDomainClosures := by
  intro E _ _ href φ ψ hp hq hcommon
  dsimp only
  have hA := conjugate_sum_domain_convex φ ψ hcommon
  have hB : Convex ℝ (Spec.sumConjugateDomains E φ ψ) := by
    have hd := domain_identity E φ ψ hp hq hcommon
    change {f | ∃ r : ℝ, infimalConvolution E φ ψ f = (r : EReal)} =
      Spec.sumConjugateDomains E φ ψ at hd
    rw [← hd]
    exact convolution_domain_convex φ ψ hp hq hcommon
  have hwA := C12ConvexClosure.weak_closure_eq_norm_closure ℝ (E →L[ℝ] ℝ) _ hA
  have hwB := C12ConvexClosure.weak_closure_eq_norm_closure ℝ (E →L[ℝ] ℝ) _ hB
  exact ⟨hA, hB, hwA, hwB, hwA.trans ((norm_domain_closure E href φ ψ hp hq hcommon).trans hwB.symm)⟩

end ExpandedFA.InfimalConvolution.ConjugateDomainClosure
