import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.ConstrainedSupport
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06StrongSeparation
import Mathlib.Analysis.Normed.Module.WeakDual

namespace ExpandedFA.PartIV.ConstrainedSupport
open Set
open scoped Pointwise
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
open Spec

/-- A real linear functional bounded above on a subspace vanishes there. -/
lemma vanishes_of_bounded_above {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : E →ₗ[ℝ] ℝ) (N : Submodule ℝ E) (b : ℝ)
    (hb : ∀ x ∈ N, p x ≤ b) : ∀ x ∈ N, p x = 0 := by
  intro x hx
  by_contra hn
  have h := hb (((b + 1) / p x) • x) (N.smul_mem _ hx)
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hn] at h
  linarith

/-- A norm-closed subspace equals its continuous preannihilator. -/
lemma mem_of_annihilator {M : Submodule ℝ X} (hM : IsClosed (M : Set X))
    {u : X} (hu : ∀ p ∈ annihilator M, p u = 0) : u ∈ M := by
  by_contra hn
  obtain ⟨p, _, hb, hs⟩ := P1.C06.real_point_strong_separation
    (M : Set X) u ⟨0, M.zero_mem⟩ hM M.convex hn
  obtain ⟨b, hb'⟩ := hb
  have hp := vanishes_of_bounded_above p.toLinearMap M b
    (fun x hx => hb' ⟨x, hx, rfl⟩)
  have hpu := hu p hp
  have hz : (0 : ℝ) ≤ sSup (p '' (M : Set X)) := by
    apply le_csSup ⟨b, hb'⟩
    exact ⟨0, M.zero_mem, map_zero p⟩
  linarith

/-- The support bound is preserved by taking norm limits. -/
lemma support_of_mem_closure {M : Submodule ℝ X} {C : Set (X →L[ℝ] ℝ)}
    {f : X →L[ℝ] ℝ} (hf : f ∈ closure ((annihilator M : Set (X →L[ℝ] ℝ)) + C)) :
    ∀ u ∈ M, (f u : EReal) ≤ supportValue C u := by
  intro u hu
  have hclosed : IsClosed {p : X →L[ℝ] ℝ | (p u : EReal) ≤ supportValue C u} :=
    isClosed_le (continuous_coe_real_ereal.comp (ContinuousLinearMap.apply ℝ ℝ u).continuous)
      continuous_const
  apply closure_minimal (t := {p : X →L[ℝ] ℝ | (p u : EReal) ≤ supportValue C u}) ?_ hclosed hf
  rintro p ⟨m, hm, g, hg, rfl⟩
  have hm' : m u = 0 := hm u hu
  simp only [mem_ofPred_eq, _root_.add_apply, hm', zero_add]
  exact le_iSup (fun g : C => (g.val u : EReal)) ⟨g, hg⟩

/-- Strong separation in the dual, represented by evaluation using reflexivity. -/
theorem support_iff_mem_closure : Spec.SupportClosure.{u} := by
  intro X _ _ hX M hM C hC hvC f
  constructor
  · intro hf
    by_contra hn
    let S : Set (X →L[ℝ] ℝ) := (annihilator M : Set (X →L[ℝ] ℝ)) + C
    have hne : S.Nonempty := by
      obtain ⟨g, hg⟩ := hC
      exact ⟨0 + g, add_mem_add (annihilator M).zero_mem hg⟩
    have hv : Convex ℝ S := (annihilator M).convex.add hvC
    obtain ⟨p, _, hb, hs⟩ := P1.C06.real_point_strong_separation
      (closure S) f hne.closure isClosed_closure hv.closure hn
    obtain ⟨u, hup⟩ := hX p
    have heval : ∀ g : X →L[ℝ] ℝ, p g = g u := by
      intro g
      exact (congrArg (fun q : (X →L[ℝ] ℝ) →L[ℝ] ℝ => q g) hup).symm
    let b := sSup (p '' closure S)
    have hbound : ∀ g ∈ S, g u ≤ b := by
      intro g hg
      rw [← heval]
      exact le_csSup hb ⟨g, subset_closure hg, rfl⟩
    obtain ⟨g₀, hg₀⟩ := hC
    have hvan : ∀ m ∈ annihilator M, m u = 0 := by
      apply vanishes_of_bounded_above (ContinuousLinearMap.apply ℝ ℝ u).toLinearMap
        (annihilator M) (b - g₀ u)
      intro m hm
      have h := hbound (m + g₀) (add_mem_add hm hg₀)
      simp only [_root_.add_apply] at h
      change m u ≤ b - g₀ u
      linarith
    have hu : u ∈ M := mem_of_annihilator hM hvan
    have hsup : supportValue C u ≤ (b : EReal) := by
      apply iSup_le
      intro g
      apply EReal.coe_le_coe
      have h := hbound (0 + g.val) (add_mem_add (annihilator M).zero_mem g.property)
      simpa using h
    have hle : f u ≤ b := EReal.coe_le_coe_iff.mp ((hf u hu).trans hsup)
    rw [heval] at hs
    exact (not_lt_of_ge hle) hs
  · exact support_of_mem_closure


/-- In a reflexive space every dual separator is a weak-star continuous
    evaluation, so a norm-closed convex set in the dual is weak-star closed. -/
lemma isClosed_weakDual_preimage
    (hX : P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X)
    {C : Set (X →L[ℝ] ℝ)} (hC : C.Nonempty) (hv : Convex ℝ C) (hc : IsClosed C) :
    IsClosed (WeakDual.toStrongDual ⁻¹' C) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro f hf
  have hf' : WeakDual.toStrongDual f ∉ C := hf
  obtain ⟨p, _, hb, hs⟩ := P1.C06.real_point_strong_separation
    C (WeakDual.toStrongDual f) hC hc hv hf'
  obtain ⟨u, hup⟩ := hX p
  have heval : ∀ g : X →L[ℝ] ℝ, p g = g u := by
    intro g
    exact (congrArg (fun q : (X →L[ℝ] ℝ) →L[ℝ] ℝ => q g) hup).symm
  refine ⟨{g : WeakDual ℝ X | sSup (p '' C) < g u}, ?_,
    isOpen_lt continuous_const (WeakDual.eval_continuous u), ?_⟩
  · intro g hg hgc
    have hle := le_csSup hb ⟨WeakDual.toStrongDual g, hgc, rfl⟩
    rw [heval] at hle
    exact (not_lt_of_ge hle) hg
  · change sSup (p '' C) < (WeakDual.toStrongDual f) u
    rwa [← heval]

/-- Annihilators are intersections of weak-star closed evaluation kernels. -/
lemma isClosed_annihilator_weakDual (M : Submodule ℝ X) :
    IsClosed (WeakDual.toStrongDual ⁻¹' (annihilator M : Set (X →L[ℝ] ℝ))) := by
  change IsClosed {f : WeakDual ℝ X | ∀ u ∈ M, f u = 0}
  simp only [ofPred_forall]
  exact isClosed_iInter fun u => isClosed_iInter fun _ =>
    isClosed_eq (WeakDual.eval_continuous u) continuous_const

/-- Banach-Alaoglu and reflexive separation supply the compact summand;
    a closed set plus a compact set is closed in the weak-star topology. -/
theorem annihilator_add_closed : Spec.ClosedSum.{u} := by
  intro X _ _ hX M _ C hC hv hc hb
  have hweak : IsClosed (WeakDual.toStrongDual ⁻¹' C) :=
    isClosed_weakDual_preimage hX hC hv hc
  have hk : IsCompact (WeakDual.toStrongDual ⁻¹' C) :=
    WeakDual.isCompact_of_bounded_of_closed hb hweak
  have ha := isClosed_annihilator_weakDual M
  have hs := ha.add_right_of_isCompact hk
  change IsClosed (WeakDual.toStrongDual ⁻¹'
    ((annihilator M : Set (X →L[ℝ] ℝ)) + C)) at hs
  exact hs.preimage NormedSpace.Dual.toWeakDual_continuous

end ExpandedFA.PartIV.ConstrainedSupport
