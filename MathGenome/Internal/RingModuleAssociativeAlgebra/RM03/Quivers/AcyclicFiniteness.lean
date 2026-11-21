import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Find
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.BoundedPaths
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.AcyclicFiniteness

/-! A finite quiver has finite-dimensional path algebra exactly when it is acyclic. -/

universe u v w

namespace RM03

section

variable {V : Type u} [Quiver.{v} V]

private theorem exists_closed_path_of_not_nodup {i j : V} (p : Quiver.Path i j)
    (h : ¬ p.vertices.Nodup) :
    ∃ (a : V) (q : Quiver.Path a a), 0 < q.length ∧ q.length ≤ p.length := by
  induction p with
  | nil => simp at h
  | @cons b c p e ih =>
    by_cases hp : p.vertices.Nodup
    · have hc : c ∈ p.vertices := by
        simpa only [Quiver.Path.vertices_cons, List.nodup_concat, hp, and_true, not_not]
          using h
      obtain ⟨p₁, p₂, rfl⟩ := p.exists_eq_comp_of_mem_vertices hc
      refine ⟨c, p₂.cons e, by simp, ?_⟩
      simp only [Quiver.Path.length_cons, Quiver.Path.length_comp]
      exact Nat.succ_le_succ (Nat.le_add_left _ _)
    · obtain ⟨a, q, hq, hle⟩ := ih hp
      exact ⟨a, q, hq, hle.trans (Nat.le_succ _)⟩

/-- Every positive-length closed path implies the existence of an oriented cycle. -/
theorem hasOrientedCycle_iff_exists_closed_path :
    HasOrientedCycle V ↔ ∃ (i : V) (p : Quiver.Path i i), 0 < p.length := by
  classical
  constructor
  · rintro ⟨i, p, hp, _⟩
    exact ⟨i, p, hp⟩
  · rintro ⟨i, p, hp⟩
    -- Choose a shortest positive-length closed path.
    have h : ∃ n : ℕ, ∃ (j : V) (q : Quiver.Path j j), 0 < q.length ∧ q.length = n :=
      ⟨p.length, i, p, hp, rfl⟩
    obtain ⟨j, q, hq, hmin⟩ := Nat.find_spec h
    obtain ⟨b, initial, e, rfl⟩ := (Quiver.Path.length_ne_zero_iff_eq_cons q).1 hq.ne'
    refine ⟨j, initial.cons e, hq, ?_⟩
    simp only [Quiver.Path.vertices_cons, List.concat_eq_append, List.dropLast_concat]
    by_contra hrepeat
    obtain ⟨a, r, hr, hle⟩ := exists_closed_path_of_not_nodup initial hrepeat
    have hshort : r.length < Nat.find h := by
      rw [← hmin, Quiver.Path.length_cons]
      exact Nat.lt_succ_of_le hle
    exact Nat.find_min h hshort ⟨a, r, hr, rfl⟩

end

namespace PathAlgebra

/-- The path algebra of a finite nonempty quiver over a field is finite-dimensional
if and only if the quiver has no oriented cycle. -/
theorem finiteDimensional_iff_no_orientedCycle {k : Type w} {V : Type u} [Field k] [Quiver.{v} V]
    [Finite V] [Nonempty V] [Finite (Arrow V)] :
    FiniteDimensional k (PathAlgebra k V) ↔ ¬ HasOrientedCycle V := by
  constructor
  · intro hfinite hcycle
    obtain ⟨i, p, hp, _⟩ := hcycle
    let repeatPath : ℕ → Quiver.Path i i := Nat.rec .nil (fun _ q => q.comp p)
    have hlength (n : ℕ) : (repeatPath n).length = n * p.length := by
      induction n with
      | zero => simp [repeatPath]
      | succ n ih => simp [repeatPath, ih, Nat.succ_mul]
    have : Finite (Path V) := Module.Finite.finite_basis (basis k V)
    have : Finite ℕ := Finite.of_injective (fun n => Path.ofPath (repeatPath n)) (by
      intro m n hmn
      have heq := congrArg Path.length hmn
      rw [Path.length_ofPath, Path.length_ofPath, hlength, hlength] at heq
      exact Nat.mul_right_cancel hp heq)
    exact not_finite ℕ
  · intro hacyclic
    let _ := Fintype.ofFinite V
    have hlength (p : Path V) : p.length < Fintype.card V := by
      have hnodup : p.2.2.vertices.Nodup := by
        by_contra hrepeat
        obtain ⟨a, q, hq, _⟩ := exists_closed_path_of_not_nodup p.2.2 hrepeat
        exact hacyclic (hasOrientedCycle_iff_exists_closed_path.mpr ⟨a, q, hq⟩)
      have hcard := hnodup.length_le_card
      rw [Quiver.Path.vertices_length] at hcard
      exact hcard
    have := Path.finite_length_lt (V := V) (Fintype.card V)
    have : Finite (Path V) := Finite.of_injective
      (fun p => (⟨p, hlength p⟩ : {q : Path V // q.length < Fintype.card V}))
      (fun _ _ h => congrArg Subtype.val h)
    exact (basis k V).finiteDimensional_of_finite

end PathAlgebra
end RM03
