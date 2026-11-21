import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sum
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.PathAlgebra
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.BoundedPaths

/-! Bounded-length paths in a finite quiver. -/

universe u v

namespace RM03.Path

/-- For each bound, a quiver with finitely many vertices and total arrows has
only finitely many paths of length strictly below that bound. -/
theorem finite_length_lt {V : Type u} [Quiver.{v} V] [Finite V] [Finite (Arrow V)]
    (m : ℕ) : Finite {p : Path V // p.length < m} := by
  induction m with
  | zero =>
    have : IsEmpty {p : Path V // p.length < 0} :=
      ⟨fun p => Nat.not_lt_zero _ p.property⟩
    infer_instance
  | succ m ih =>
    have := ih
    -- A path is either a vertex or a shorter path followed by a matching arrow.
    let extend : V ⊕ {pa : {p : Path V // p.length < m} × Arrow V //
        pa.2.1 = pa.1.val.target} → {p : Path V // p.length < m + 1} :=
      Sum.elim
        (fun i => ⟨vertex i, Nat.zero_lt_succ m⟩)
        (fun ⟨⟨p, ⟨_, _, a⟩⟩, h⟩ => by
          have endpoints : (arrow a).source = p.val.target := h
          refine ⟨(arrow a).concat p.val endpoints, ?_⟩
          rw [length_concat, length_arrow]
          exact Nat.succ_lt_succ p.property)
    apply Finite.of_surjective extend
    rintro ⟨⟨i, j, p⟩, hp⟩
    cases p with
    | nil => exact ⟨Sum.inl i, rfl⟩
    | @cons b j p a =>
      have h : (ofPath p).length < m := Nat.lt_of_succ_lt_succ hp
      exact ⟨Sum.inr ⟨(⟨ofPath p, h⟩, ⟨b, j, a⟩), rfl⟩, rfl⟩

end RM03.Path
