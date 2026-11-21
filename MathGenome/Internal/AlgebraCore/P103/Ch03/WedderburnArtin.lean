import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.WedderburnArtin
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.Artinian.Module

/-!
Wedderburn–Artin classification, paper.tex, Theorem 3.4 (equivalence).

Mathlib's finite semisimple decomposition groups simple left ideals by
isomorphism type. Its regular-endomorphism equivalence uses right
multiplication, and its passage to opposites uses transpose on matrices.
The coefficient rings are the opposites of the Schur endomorphism division
rings, with no commutativity hypothesis. We retain this explicit stronger
form below, together with the representative formulas for both bridges.

For the converse Mathlib proves full matrix rings over division rings
semisimple using simple Artinian rings; finite products preserve
semisimplicity. The Artinian radical-zero characterization has no
Noetherian or nonzero-ring assumption. Thus the empty product gives the
zero-ring boundary of the same classification.
-/

universe u

namespace P103.Ch03.WedderburnArtin

open P103.Specs.Ch03.WedderburnArtin

theorem regular_endomorphisms : regular_endomorphismsType.{u} := by
  intro R _
  exact ⟨RingEquiv.moduleEndSelf R, fun _ _ => rfl⟩

theorem transpose_opposite : transpose_oppositeType.{u} := by
  intro D _ n
  exact ⟨RingEquiv.mopMatrix.symm, fun _ _ _ => rfl⟩

theorem opposite_decomposition : opposite_decompositionType.{u} := by
  intro R _ _
  obtain ⟨k, S, n, hS, hn, he⟩ :=
    IsSemisimpleRing.exists_ringEquiv_pi_matrix_end_mulOpposite R
  exact ⟨k, S, n, hS, fun i => Nat.pos_of_ne_zero (hn i).out, he⟩

theorem matrix_regular_semisimple : matrix_regular_semisimpleType.{u} := by
  intro D _ n
  infer_instance

theorem product_regular_semisimple : product_regular_semisimpleType.{u} := by
  intro k D n _
  let : ∀ i, IsSemisimpleRing (Matrix (Fin (n i)) (Fin (n i)) (D i)) :=
    fun i => matrix_regular_semisimple (D i) (n i)
  infer_instance

theorem classification : classificationType.{u} := by
  intro R _
  constructor
  · constructor
    · intro h
      let := h
      have : IsArtinianRing R := inferInstance
      exact ⟨inferInstance, IsArtinianRing.isSemisimpleRing_iff_jacobson.mp h⟩
    · rintro ⟨hA, hJ⟩
      let := hA
      exact IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr hJ
  · constructor
    · intro h
      let := h
      obtain ⟨k, D, n, instD, hn, he⟩ :=
        IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
      exact ⟨k, D, n, instD, fun i => Nat.pos_of_ne_zero (hn i).out, he⟩
    · rintro ⟨k, D, n, instD, _, ⟨e⟩⟩
      letI := instD
      let := product_regular_semisimple k D n
      exact e.symm.isSemisimpleRing

theorem nonempty_factors : nonempty_factorsType.{u} := by
  intro R _ _ k D n _ ⟨e⟩
  cases k with
  | zero =>
    exact (zero_ne_one (α := R) (e.injective (Subsingleton.elim _ _))).elim
  | succ k => exact Nat.zero_lt_succ k

theorem zero_ring : zero_ringType.{u} := by
  intro R _ _
  have hs : IsSemisimpleModule R R := inferInstance
  refine ⟨hs, (classification R).1.mp hs, ?_⟩
  let D : Fin 0 → Type u := fun i => Fin.elim0 i
  let : ∀ i, DivisionRing (D i) := fun i => Fin.elim0 i
  let : Unique R := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  exact ⟨D, inferInstance, ⟨RingEquiv.ofUnique⟩⟩

end P103.Ch03.WedderburnArtin
