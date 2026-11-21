import MathGenome.Internal.Specs.D05.M02.Exchange
import MathGenome.Internal.D05.M02.Independence
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! K05.02.exchange: exchange of indexed finite spanning lists. -/

namespace D05.M02.Exchange

open Set Submodule

section

variable {K V J : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- If adjoining a finite indexed family makes a vector available, at least
one of its occurrences can be exchanged for that vector without changing span.
The set `S` may be infinite. -/
theorem exchange_one (S : Set V) (w : J → V) [DecidableEq J] (F : Finset J) (x : V)
    (hx : x ∈ span K (S ∪ w '' (F : Set J))) (hn : x ∉ span K S) :
    ∃ (j : J) (T : Finset J), j ∉ T ∧ insert j T = F ∧
      span K (insert x (S ∪ w '' (T : Set J))) =
        span K (S ∪ w '' (F : Set J)) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact (hn (by simpa using hx)).elim
  | @insert a F ha ih =>
    by_cases hxF : x ∈ span K (S ∪ w '' (F : Set J))
    · obtain ⟨j, T, hj, hT, hspan⟩ := ih hxF
      have hja : j ≠ a := by
        intro h
        apply ha
        rw [← hT, ← h]
        exact Finset.mem_insert_self _ _
      refine ⟨j, insert a T, by simp [hj, hja], ?_, ?_⟩
      · rw [Finset.insert_comm, hT]
      · simp only [Finset.coe_insert, Set.image_insert_eq, union_insert]
        rw [Set.insert_comm x (w a), span_insert, hspan, ← span_insert]
    · have hx' : x ∈ span K (insert (w a) (S ∪ w '' (F : Set J))) := by
        simpa only [Finset.coe_insert, Set.image_insert_eq, union_insert] using hx
      have hw : w a ∈ span K (insert x (S ∪ w '' (F : Set J))) :=
        mem_span_insert_exchange hx' hxF
      refine ⟨a, F, ha, rfl, ?_⟩
      simp only [Finset.coe_insert, Set.image_insert_eq, union_insert]
      calc
        span K (insert x (S ∪ w '' (F : Set J))) =
            span K (insert (w a) (insert x (S ∪ w '' (F : Set J)))) :=
          (span_insert_eq_span hw).symm
        _ = span K (insert x (insert (w a) (S ∪ w '' (F : Set J)))) := by
          rw [Set.insert_comm]
        _ = span K (insert (w a) (S ∪ w '' (F : Set J))) :=
          span_insert_eq_span hx'

end

section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Choose distinct positions to remove; the inserted vectors together with
the remaining occurrences still span. This is proved by finite induction,
without choosing a basis or assuming finite dimension. -/
theorem exchange_positions (r s : ℕ) (v : Fin r → V) (w : Fin s → V)
    (hv : LinearIndependent K v) (hw : span K (range w) = ⊤) :
    ∃ e : Fin r ↪ Fin s,
      span K (range v ∪ w '' (univ \ range e)) = ⊤ := by
  classical
  induction r with
  | zero =>
    refine ⟨⟨Fin.elim0, fun i => Fin.elim0 i⟩, ?_⟩
    simpa using hw
  | succ r ih =>
    obtain ⟨htail, hnot⟩ := linearIndependent_finSucc.mp hv
    obtain ⟨e, he⟩ := ih (Fin.tail v) htail
    let F : Finset (Fin s) := Finset.univ.filter (fun j => j ∉ range e)
    have hFset : (F : Set (Fin s)) = univ \ range e := by
      ext j
      simp [F]
    have hx : v 0 ∈ span K (range (Fin.tail v) ∪ w '' (F : Set (Fin s))) := by
      rw [hFset, he]
      trivial
    obtain ⟨j, T, hjT, hTF, hspan⟩ := exchange_one (range (Fin.tail v)) w F (v 0) hx hnot
    have hjF : j ∈ F := by rw [← hTF]; exact Finset.mem_insert_self _ _
    have hj : j ∉ range e := (Finset.mem_filter.mp hjF).2
    let e' : Fin (r + 1) ↪ Fin s :=
      ⟨Fin.cons j e, Fin.cons_injective_of_injective hj e.injective⟩
    have hremaining : univ \ range e' = (T : Set (Fin s)) := by
      have hset : insert j (T : Set (Fin s)) = univ \ range e := by
        rw [← hFset, ← hTF, Finset.coe_insert]
      change univ \ range (Fin.cons j e) = (T : Set (Fin s))
      rw [Fin.range_cons]
      ext k
      have hmem := Set.ext_iff.mp hset k
      simp only [mem_insert_iff, mem_sdiff, mem_univ, true_and, Finset.mem_coe] at hmem ⊢
      constructor
      · intro hk
        exact (hmem.mpr (fun hke => hk (Or.inr hke))).resolve_left
          (fun hkj => hk (Or.inl hkj))
      · intro hk hkr
        rcases hkr with hkj | hke
        · exact hjT (hkj ▸ hk)
        · exact hmem.mp (Or.inr hk) hke
    refine ⟨e', ?_⟩
    calc
      span K (range v ∪ w '' (univ \ range e')) =
          span K (insert (v 0) (range (Fin.tail v) ∪ w '' (T : Set (Fin s)))) := by
        rw [hremaining, ← Fin.cons_self_tail v, Fin.range_cons, insert_union]
        simp only [Fin.cons_zero, Fin.tail_cons]
      _ = span K (range (Fin.tail v) ∪ w '' (F : Set (Fin s))) := hspan
      _ = ⊤ := by rw [hFset, he]

end

/-- The paper's complete exchange theorem, including the length bound and
an actual spanning list obtained by replacing distinct original positions. -/
theorem exchange : Specs.D05.M02.Exchange.exchange := by
  intro K V _ _ _ r s v w hv hw
  classical
  obtain ⟨e, he⟩ := exchange_positions r s v w hv hw
  let u : Fin s → V := Function.extend e v w
  have hvu (i : Fin r) : u (e i) = v i := e.injective.extend_apply v w i
  have hwu (j : Fin s) (hj : j ∉ range e) : u j = w j :=
    Function.extend_apply' v w j hj
  refine ⟨?_, e, u, hvu, hwu, ?_⟩
  · simpa using Fintype.card_le_of_injective e e.injective
  · apply top_unique
    rw [← he]
    apply span_le.mpr
    intro z hz
    rcases hz with ⟨i, rfl⟩ | ⟨j, hj, rfl⟩
    · exact subset_span ⟨e i, hvu i⟩
    · exact subset_span ⟨j, hwu j hj.2⟩

end D05.M02.Exchange
