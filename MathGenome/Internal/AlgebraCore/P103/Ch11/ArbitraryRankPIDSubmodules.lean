import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ArbitraryRankPIDSubmodules
import Mathlib.Data.Finset.Max
import Mathlib.SetTheory.Cardinal.Order

noncomputable section

open Module

namespace P103.Ch11.ArbitraryRankPIDSubmodules

universe u v w

variable {R : Type u} {F : Type v} {ι : Type w}
variable [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable [AddCommGroup F] [Module R F]
variable [LinearOrder ι]

/-- Vectors supported on the initial segment ending at `i`. -/
def initialSegment (b : Basis ι R F) (i : ι) : Submodule R F where
  carrier := {x | ∀ j, i < j → b.repr x j = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy j hj
    simp [hx j hj, hy j hj]
  smul_mem' := by
    intro r x hx j hj
    simp [hx j hj]

/-- The ideal of possible leading coordinates of elements of `N` at `i`. -/
def coordinateIdeal (b : Basis ι R F) (N : Submodule R F) (i : ι) : Ideal R :=
  (N ⊓ initialSegment b i).map (b.coord i)

omit [IsDomain R] in
lemma exists_leadingVector (b : Basis ι R F) (N : Submodule R F) (i : ι) :
    ∃ x : N, (∀ j, i < j → b.repr (x : F) j = 0) ∧
      b.repr (x : F) i = Submodule.IsPrincipal.generator (coordinateIdeal b N i) := by
  obtain ⟨x, hx, hcoord⟩ :=
    Submodule.IsPrincipal.generator_mem (coordinateIdeal b N i)
  exact ⟨⟨x, hx.1⟩, hx.2, hcoord⟩

/-- A lift of the generator of the leading-coordinate ideal. -/
def leadingVector (b : Basis ι R F) (N : Submodule R F) (i : ι) : N :=
  (exists_leadingVector b N i).choose

omit [IsDomain R] in
lemma leadingVector_above (b : Basis ι R F) (N : Submodule R F) (i j : ι)
    (hij : i < j) : b.repr (leadingVector b N i : F) j = 0 :=
  (exists_leadingVector b N i).choose_spec.1 j hij

omit [IsDomain R] in
lemma leadingVector_coord (b : Basis ι R F) (N : Submodule R F) (i : ι) :
    b.repr (leadingVector b N i : F) i =
      Submodule.IsPrincipal.generator (coordinateIdeal b N i) :=
  (exists_leadingVector b N i).choose_spec.2

/-- Only nonzero leading-coordinate ideals contribute basis vectors. -/
abbrev Active (b : Basis ι R F) (N : Submodule R F) :=
  {i : ι // Submodule.IsPrincipal.generator (coordinateIdeal b N i) ≠ 0}

lemma leadingVectors_independent (b : Basis ι R F) (N : Submodule R F) :
    LinearIndependent R (fun i : Active b N => leadingVector b N i.1) := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  by_contra hn
  have hs := Finsupp.support_nonempty_iff.mpr hn
  let i := l.support.max' hs
  have hi : i ∈ l.support := l.support.max'_mem hs
  have hsum : (∑ j ∈ l.support, l j * b.repr (leadingVector b N j.1 : F) i.1) = 0 := by
    have h := congrArg (fun x : N => b.repr (x : F) i.1) hl
    simpa [Finsupp.linearCombination_apply, Finsupp.sum] using h
  have hone : (∑ j ∈ l.support, l j * b.repr (leadingVector b N j.1 : F) i.1) =
      l i * b.repr (leadingVector b N i.1 : F) i.1 := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      have hle : j ≤ i := l.support.le_max' j hj
      have hlt : j.1 < i.1 := lt_of_le_of_ne hle (fun h => hji (Subtype.ext h))
      rw [leadingVector_above b N j.1 i.1 hlt, mul_zero]
    · exact fun h => (h hi).elim
  rw [hone, leadingVector_coord] at hsum
  exact (mul_ne_zero (Finsupp.mem_support_iff.mp hi) i.2) hsum

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- A nonzero vector has a last nonzero coordinate, because its support is finite. -/
lemma exists_last_coordinate (b : Basis ι R F) (x : F) (hx : x ≠ 0) :
    ∃ i, b.repr x i ≠ 0 ∧ ∀ j, i < j → b.repr x j = 0 := by
  classical
  have hs : (b.repr x).support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun h => hx (b.repr.injective (by simpa using h)))
  refine ⟨(b.repr x).support.max' hs,
    Finsupp.mem_support_iff.mp ((b.repr x).support.max'_mem hs), ?_⟩
  intro j hj
  apply Finsupp.notMem_support_iff.mp
  intro hjm
  exact (not_lt_of_ge ((b.repr x).support.le_max' j hjm)) hj

omit [IsDomain R] in
/-- Cancelling the last coordinate strictly lowers the support in the well-order. -/
lemma leadingVectors_span [WellFoundedLT ι] (b : Basis ι R F) (N : Submodule R F) :
    ⊤ ≤ Submodule.span R (Set.range (fun i : Active b N => leadingVector b N i.1)) := by
  classical
  let S := Submodule.span R (Set.range (fun i : Active b N => leadingVector b N i.1))
  have hind : ∀ i (x : N), (∀ j, i < j → b.repr (x : F) j = 0) →
      b.repr (x : F) i ≠ 0 → x ∈ S := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      intro x hx hxi
      have hmem : b.repr (x : F) i ∈ coordinateIdeal b N i :=
        ⟨(x : F), ⟨x.property, hx⟩, rfl⟩
      obtain ⟨r, hr⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator
        (coordinateIdeal b N i)).mp hmem
      have ha : Submodule.IsPrincipal.generator (coordinateIdeal b N i) ≠ 0 := by
        intro ha
        apply hxi
        simpa [ha] using hr
      let idx : Active b N := ⟨i, ha⟩
      let y : N := x - r • leadingVector b N i
      have hyi : b.repr (y : F) i = 0 := by
        simp [y, leadingVector_coord, hr]
      have hyabove : ∀ j, i < j → b.repr (y : F) j = 0 := by
        intro j hj
        simp [y, hx j hj, leadingVector_above b N i j hj]
      have hyspan : y ∈ S := by
        by_cases hy : y = 0
        · simp [hy]
        have hycoe : (y : F) ≠ 0 := fun h => hy (Subtype.ext h)
        obtain ⟨j, hj, hjmax⟩ := exists_last_coordinate b (y : F) hycoe
        have hji : j < i := by
          apply lt_of_not_ge
          intro hij
          rcases eq_or_lt_of_le hij with hij | hij
          · exact hj (hij ▸ hyi)
          · exact hj (hyabove j hij)
        exact ih j hji y hjmax hj
      have hvspan : leadingVector b N i ∈ S :=
        Submodule.subset_span ⟨idx, rfl⟩
      have heq : x = y + r • leadingVector b N i := (sub_add_cancel x _).symm
      rw [heq]
      exact S.add_mem hyspan (S.smul_mem r hvspan)
  intro x _
  by_cases hx : x = 0
  · simp [hx]
  have hxcoe : (x : F) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨i, hi, himax⟩ := exists_last_coordinate b (x : F) hxcoe
  exact hind i x himax hi

/-- The leading vectors form a basis for an arbitrary submodule. -/
def submoduleBasis [WellFoundedLT ι] (b : Basis ι R F) (N : Submodule R F) :
    Basis (Active b N) R N :=
  Basis.mk (leadingVectors_independent b N) (leadingVectors_span b N)

omit [LinearOrder ι] in
/-- No cardinality assumption is imposed on the ambient basis. -/
theorem free_of_basis (b : Basis ι R F) (N : Submodule R F) : Module.Free R N := by
  obtain ⟨order, hwf⟩ := exists_wellFoundedLT ι
  let : LinearOrder ι := order
  let : WellFoundedLT ι := hwf
  exact Module.Free.of_basis (submoduleBasis b N)

theorem free_submodule :
    Specs.P103.Ch11.ArbitraryRankPIDSubmodules.freeSubmodule.{u, v} := by
  intro R F _ _ _ _ _ _ N
  exact free_of_basis (Module.Free.chooseBasis R F) N

end P103.Ch11.ArbitraryRankPIDSubmodules
