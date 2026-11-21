import MathGenome.Internal.Specs.D05.M02.BasisExtension
import MathGenome.Internal.D05.M02.Basis
import MathGenome.Internal.D05.M02.Exchange
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Fintype.EquivFin

/-! K05.02.basis_extension: finite extraction, extension, and the separate
Zorn-based unrestricted extension. -/

namespace D05.M02.BasisExtension

open Set Submodule

section FiniteSelection

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Process a finite set of candidate indices. Retain a candidate precisely
when its vector is outside the current span. The initial independent subfamily
may be infinite; only the candidates are processed by finite induction. -/
theorem extend_by_finite_indices (v : I → V) (S : Set I) (F : Finset I)
    (hS : LinearIndepOn K v S) :
    ∃ T : Finset I, T ⊆ F ∧ LinearIndepOn K v (S ∪ (T : Set I)) ∧
      v '' (F : Set I) ⊆ span K (v '' (S ∪ (T : Set I))) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    exact ⟨∅, Finset.empty_subset _, by simpa using hS, by simp⟩
  | @insert a F ha ih =>
    obtain ⟨T, hTF, hT, hspan⟩ := ih
    by_cases hv : v a ∈ span K (v '' (S ∪ (T : Set I)))
    · refine ⟨T, hTF.trans (Finset.subset_insert _ _), hT, ?_⟩
      rw [Finset.coe_insert, image_insert_eq]
      exact insert_subset hv hspan
    · refine ⟨insert a T, Finset.insert_subset_insert a hTF, ?_, ?_⟩
      · simpa only [Finset.coe_insert, union_insert] using hT.insert hv
      · rw [Finset.coe_insert, image_insert_eq]
        refine insert_subset ?_ ?_
        · exact subset_span ⟨a, Or.inr (Finset.mem_insert_self a T), rfl⟩
        · exact hspan.trans (span_mono (image_mono (union_subset_union_right _
            (by simpa only [Finset.coe_insert] using Set.subset_insert a (T : Set I)))))

end FiniteSelection

theorem finite_spanning_contains_basis :
    Specs.D05.M02.BasisExtension.finite_spanning_contains_basis := by
  intro K V _ _ _ s w hw
  classical
  obtain ⟨T, _, hT, hspan⟩ :=
    extend_by_finite_indices w ∅ Finset.univ (linearIndepOn_empty K w)
  simp only [empty_union, Finset.coe_univ, image_univ] at hT hspan
  have htop : span K (w '' (T : Set (Fin s))) = ⊤ :=
    top_unique (hw ▸ span_le.mpr hspan)
  have hrange : Set.range (fun j : T => w j) = w '' (T : Set (Fin s)) := by
    ext x
    simp
  obtain ⟨b, hb⟩ := (D05.M02.Basis.basis_iff_independent_span (fun j : T => w j)).mpr
    ⟨hT, by rw [hrange, htop]⟩
  exact ⟨T, b, hb⟩

theorem independent_family_finite :
    Specs.D05.M02.BasisExtension.independent_family_finite := by
  intro K V I _ _ _ s w v hw hv
  classical
  have hI : Finite I := by
    by_contra h
    haveI : Infinite I := not_finite_iff_infinite.mp h
    let e : Fin (s + 1) → I := fun i => Infinite.natEmbedding I i.val
    have he : Function.Injective e :=
      (Infinite.natEmbedding I).injective.comp Fin.val_injective
    have hle := (D05.M02.Exchange.exchange (s + 1) s (v ∘ e) w
      (hv.comp e he) hw).1
    exact Nat.not_succ_le_self s hle
  haveI := hI
  let _ := Fintype.ofFinite I
  let e := (Fintype.equivFin I).symm
  have hle := (D05.M02.Exchange.exchange (Fintype.card I) s (v ∘ e) w
    (hv.comp e e.injective) hw).1
  exact ⟨hI, by simpa only [Nat.card_eq_fintype_card] using hle⟩

theorem finite_basis_extension : Specs.D05.M02.BasisExtension.finite_basis_extension := by
  intro K V I _ _ _ s w v hw hv
  classical
  haveI : Finite I := (independent_family_finite s w v hw hv).1
  let _ := Fintype.ofFinite I
  let f : I ⊕ Fin s → V := Sum.elim v w
  let S : Set (I ⊕ Fin s) := range Sum.inl
  have hS : LinearIndepOn K f S := by
    rw [LinearIndepOn]
    let e : S → I := fun j => j.val.getLeft (by
      obtain ⟨i, hi⟩ := j.property
      rw [← hi]
      trivial)
    have he : Function.Injective e := by
      intro a b hab
      apply Subtype.ext
      obtain ⟨i, hi⟩ := a.property
      obtain ⟨j, hj⟩ := b.property
      simpa [e, ← hi, ← hj] using congrArg (Sum.inl : I → I ⊕ Fin s) hab
    convert hv.comp e he using 1
    funext j
    obtain ⟨i, hi⟩ := j.property
    simp [f, e, ← hi]
  obtain ⟨T, _, hT, hspan⟩ := extend_by_finite_indices f S Finset.univ hS
  let U : Set (I ⊕ Fin s) := S ∪ (T : Set (I ⊕ Fin s))
  let t : Finset (I ⊕ Fin s) := U.toFinite.toFinset
  have ht : (t : Set (I ⊕ Fin s)) = U := Set.Finite.coe_toFinset _
  have htop : span K (f '' U) = ⊤ := by
    apply top_unique
    rw [← hw]
    apply span_le.mpr
    rintro x ⟨j, rfl⟩
    exact hspan ⟨Sum.inr j, Finset.mem_univ _, rfl⟩
  have hli : LinearIndependent K (fun j : t => f j) := by
    change LinearIndepOn K f (t : Set (I ⊕ Fin s))
    rw [ht]
    exact hT
  have hrange : range (fun j : t => f j) = f '' U := by
    rw [← ht]
    ext x
    simp
  obtain ⟨b, hb⟩ := (D05.M02.Basis.basis_iff_independent_span (fun j : t => f j)).mpr
    ⟨hli, by rw [hrange, htop]⟩
  refine ⟨t, ?_, b, hb⟩
  intro i
  change Sum.inl i ∈ (t : Set (I ⊕ Fin s))
  rw [ht]
  exact Or.inl ⟨i, rfl⟩

/-- Mathlib's `Basis.extend` uses the independent-set extension theorem proved
by Zorn's lemma. This use of unrestricted choice is separate from the finite
selection proof above. -/
theorem unrestricted_basis_extension :
    Specs.D05.M02.BasisExtension.unrestricted_basis_extension := by
  intro K V _ _ _ S hS
  have hS' : LinearIndepOn K id S := hS
  refine ⟨hS'.extend (subset_univ S), hS'.subset_extend _, Module.Basis.extend hS', ?_⟩
  exact Module.Basis.extend_apply_self hS'

end D05.M02.BasisExtension
