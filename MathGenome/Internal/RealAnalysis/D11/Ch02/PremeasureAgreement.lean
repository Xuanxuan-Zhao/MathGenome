import MathGenome.Internal.RealAnalysis.D11.Ch02.Caratheodory
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.PremeasureAgreement

/-!
# Premeasures and agreement of the covering construction

Finite additivity follows by padding two disjoint algebra sets with empty
sets. Disjointifying a cover inside an algebra set then proves that every
cover costs at least its premeasure value. Splitting each covering set gives
the full Carathéodory test. In particular neither agreement nor measurability
uses sigma-finiteness or an already constructed extension measure.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace D11.Ch02.PremeasureAgreement

abbrev premeasure {α : Type u} (A : Set (Set α)) (hA : IsSetAlgebra A) :=
  Premeasure A hA

/-- Sigma-finiteness concerns a cover in the original algebra. -/
def isSigmaFinite {α : Type u} {A : Set (Set α)} {hA : IsSetAlgebra A}
    (p : Premeasure A hA) : Prop :=
  ∃ E : ℕ → A, (∀ n, p.value (E n) < ∞) ∧ (⋃ n, (E n).1) = univ

namespace Premeasure

variable {α : Type u} {A : Set (Set α)} {hA : IsSetAlgebra A} (p : Premeasure A hA)

/-- A premeasure is finitely additive, even at infinite values. -/
theorem union (s t : A) (hd : Disjoint s.1 t.1) :
    p.value ⟨s.1 ∪ t.1, hA.union_mem s.2 t.2⟩ = p.value s + p.value t := by
  let E : ℕ → A := fun n => match n with
    | 0 => s
    | 1 => t
    | _ + 2 => ⟨∅, hA.empty_mem⟩
  have hU : (⋃ n, (E n).1) = s.1 ∪ t.1 := by
    ext x
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨n, hn⟩
      cases n with
      | zero => exact Or.inl hn
      | succ n =>
        cases n with
        | zero => exact Or.inr hn
        | succ n => exact False.elim hn
    · rintro (hs | ht)
      · exact ⟨0, hs⟩
      · exact ⟨1, ht⟩
  have hE : Pairwise fun i j => Disjoint (E i).1 (E j).1 := by
    intro i j hij
    rcases i with _ | (_ | i) <;> rcases j with _ | (_ | j) <;>
      simp_all [E, hd.symm]
  have h := p.iUnion E (hU ▸ hA.union_mem s.2 t.2) hE
  have hsum : (∑' n, p.value (E n)) = p.value s + p.value t := by
    have hsupp : ∀ n ∉ ({0, 1} : Finset ℕ), p.value (E n) = 0 := by
      intro n hn
      rcases n with _ | (_ | n) <;> simp_all [E, p.empty]
    rw [tsum_eq_sum hsupp]
    simp [E]
  rw [hsum] at h
  simpa only [hU] using h

theorem mono (s t : A) (hst : s.1 ⊆ t.1) : p.value s ≤ p.value t := by
  have h := p.union s ⟨t.1 \ s.1, hA.sdiff_mem t.2 s.2⟩ disjoint_sdiff_self_right
  have heq : s.1 ∪ (t.1 \ s.1) = t.1 := union_sdiff_cancel hst
  rw [show (⟨s.1 ∪ (t.1 \ s.1), _⟩ : A) = t from Subtype.ext heq] at h
  rw [h]
  exact le_self_add

/-- Every countable algebra cover of an algebra set costs at least its value. -/
theorem le_cover (s : A) (F : ℕ → A) (hcover : s.1 ⊆ ⋃ n, (F n).1) :
    p.value s ≤ ∑' n, p.value (F n) := by
  let B : ℕ → A := fun n =>
    ⟨s.1 ∩ disjointed (fun i => (F i).1) n,
      hA.inter_mem s.2 (hA.isSetRing.disjointed_mem (fun i => (F i).2) n)⟩
  have hU : (⋃ n, (B n).1) = s.1 := by
    simp only [B, ← inter_iUnion, iUnion_disjointed]
    exact inter_eq_left.mpr hcover
  have hd : Pairwise fun i j => Disjoint (B i).1 (B j).1 :=
    fun i j hij => (disjoint_disjointed (fun n => (F n).1) hij).mono
      inter_subset_right inter_subset_right
  have h := p.iUnion B (hU ▸ s.2) hd
  have hs : p.value s = ∑' n, p.value (B n) := by simpa only [hU] using h
  rw [hs]
  exact ENNReal.tsum_le_tsum fun n =>
    p.mono (B n) (F n) (inter_subset_right.trans (disjointed_subset _ n))

end Premeasure

/-- The source's outer measure, constructed directly from algebra covering costs. -/
noncomputable def coveringOuterMeasure {α : Type u} {A : Set (Set α)}
    {hA : IsSetAlgebra A} (p : Premeasure A hA) : OuterMeasure α :=
  OuterCover.coveringOuterMeasure A hA.empty_mem hA.univ_mem p.value p.empty

theorem coveringOuterMeasure_apply {α : Type u} {A : Set (Set α)}
    {hA : IsSetAlgebra A} (p : Premeasure A hA) (E : Set α) :
    coveringOuterMeasure p E =
      ⨅ (F : ℕ → Set α) (hF : ∀ n, F n ∈ A)
        (_ : E ⊆ ⋃ n, F n), ∑' n, p.value ⟨F n, hF n⟩ :=
  OuterCover.coveringOuterMeasure_apply A hA.empty_mem hA.univ_mem p.value p.empty E

/-- Agreement with the original premeasure, without sigma-finiteness. -/
theorem coveringOuterMeasure_agrees {α : Type u} {A : Set (Set α)}
    {hA : IsSetAlgebra A} (p : Premeasure A hA) (s : A) :
    coveringOuterMeasure p s.1 = p.value s := by
  apply le_antisymm
  · have h := @OuterMeasure.ofFunction_le α
      (fun t => ⨅ ht : t ∈ A, p.value ⟨t, ht⟩)
      (by simpa only [iInf_pos hA.empty_mem] using p.empty) s.1
    exact h.trans (iInf_le (fun hs : s.1 ∈ A => p.value ⟨s.1, hs⟩) s.2)
  · rw [coveringOuterMeasure_apply]
    exact le_iInf fun F => le_iInf fun hF => le_iInf fun hc =>
      p.le_cover s (fun n => ⟨F n, hF n⟩) hc

/-- Every algebra member passes the splitting test against every subset. -/
theorem algebra_measurable {α : Type u} {A : Set (Set α)} {hA : IsSetAlgebra A}
    (p : Premeasure A hA) :
    A ⊆ {s : Set α | ∀ E : Set α,
      coveringOuterMeasure p E =
        coveringOuterMeasure p (E ∩ s) + coveringOuterMeasure p (E \ s)} := by
  intro s hs
  apply (Caratheodory.isMeasurable_iff_le (coveringOuterMeasure p) s).mpr
  intro E
  rw [coveringOuterMeasure_apply p E]
  refine le_iInf fun F => le_iInf fun hF => le_iInf fun hcover => ?_
  have hinter : E ∩ s ⊆ ⋃ n, F n ∩ s := by
    rw [← iUnion_inter]
    exact inter_subset_inter_left s hcover
  have hdiff : E \ s ⊆ ⋃ n, F n \ s := by
    rw [← iUnion_sdiff]
    exact sdiff_subset_sdiff_left hcover
  have hbound (G : ℕ → A) (T : Set α) (hT : T ⊆ ⋃ n, (G n).1) :
      coveringOuterMeasure p T ≤ ∑' n, p.value (G n) := by
    rw [coveringOuterMeasure_apply]
    exact iInf_le_of_le (fun n => (G n).1)
      (iInf_le_of_le (fun n => (G n).2) (iInf_le_of_le hT le_rfl))
  have hI := hbound (fun n => ⟨F n ∩ s, hA.inter_mem (hF n) hs⟩) (E ∩ s) hinter
  have hD := hbound (fun n => ⟨F n \ s, hA.sdiff_mem (hF n) hs⟩) (E \ s) hdiff
  apply (add_le_add hI hD).trans
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro n
  have h := p.union ⟨F n ∩ s, hA.inter_mem (hF n) hs⟩
    ⟨F n \ s, hA.sdiff_mem (hF n) hs⟩ disjoint_inf_sdiff
  rw [show (⟨(F n ∩ s) ∪ (F n \ s), _⟩ : A) = ⟨F n, hF n⟩ from
    Subtype.ext (inter_union_sdiff (F n) s)] at h
  exact h.ge

end D11.Ch02.PremeasureAgreement
