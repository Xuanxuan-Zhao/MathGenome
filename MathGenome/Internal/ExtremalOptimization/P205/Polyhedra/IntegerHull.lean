import MathGenome.Internal.ExtremalOptimization.Specs.P205.Polyhedra.IntegerHull
import MathGenome.Internal.ExtremalOptimization.P205.Polyhedra.IntegralVertices
import MathGenome.Internal.ExtremalOptimization.P205.Polyhedra.BoundedHull
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section
open Matrix Set
namespace P205.Polyhedra

/-- Intersect a TU system with the integer box surrounding a given point.
The enlarged row type is reindexed by a finite ordinal so that the shared
polyhedron interface applies, without a nonempty-index assumption. -/
lemma exists_integral_box {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : A.IsTotallyUnimodular) (x : Coordinate n) :
    ∃ (k : ℕ) (B : Matrix (Fin k) (Fin n) ℤ) (d : Fin k → ℤ),
      B.IsTotallyUnimodular ∧ ∀ z,
        z ∈ polyhedron (B.map (Int.cast : ℤ → ℝ)) (fun i => (d i : ℝ)) ↔
        z ∈ polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)) ∧
          (∀ j, (⌊x j⌋ : ℝ) ≤ z j) ∧ (∀ j, z j ≤ (⌈x j⌉ : ℝ)) := by
  classical
  let R := (Fin m ⊕ Fin n) ⊕ Fin n
  let e := Fintype.equivFin R
  let D : Matrix R (Fin n) ℤ :=
    Matrix.fromRows (Matrix.fromRows A 1) (-1)
  let c : R → ℤ := Sum.elim (Sum.elim b (fun j => ⌈x j⌉)) (fun j => -⌊x j⌋)
  let B := D.submatrix e.symm id
  let d := c ∘ e.symm
  refine ⟨Fintype.card R, B, d, ?_, ?_⟩
  · exact (TotalUnimodularity.append_bounds hA).submatrix e.symm id
  · intro z
    change (∀ i, ∑ j, (D (e.symm i) j : ℝ) * z j ≤ (c (e.symm i) : ℝ)) ↔ _
    have hreindex : (∀ i, ∑ j, (D (e.symm i) j : ℝ) * z j ≤ (c (e.symm i) : ℝ)) ↔
        (∀ r : R, ∑ j, (D r j : ℝ) * z j ≤ (c r : ℝ)) :=
      (e.symm.surjective.forall (p := fun r : R =>
        ∑ j, (D r j : ℝ) * z j ≤ (c r : ℝ))).symm
    apply hreindex.trans
    simp [R, D, c, polyhedron, rowCovector, Matrix.one_apply,
      neg_le_iff_add_nonneg, and_comm, and_assoc]

/-- Every point is in the hull of integral feasible points, by the bounded
floor/ceiling box. Boundedness is required only of this local box. -/
theorem integer_hull : IntegerHullSpecs.integer_hull := by
  intro m n A b hA
  let P := polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨k, B, d, hB, hbox⟩ := exists_integral_box A b hA x
    let Q := polyhedron (B.map (Int.cast : ℤ → ℝ)) (fun i => (d i : ℝ))
    have hxQ : x ∈ Q := (hbox x).mpr ⟨hx, (fun j => Int.floor_le (x j)), (fun j => Int.le_ceil (x j))⟩
    have hbQ : Bornology.IsBounded Q := by
      apply (isCompact_Icc (a := fun j => (⌊x j⌋ : ℝ))
        (b := fun j => (⌈x j⌉ : ℝ))).isBounded.subset
      intro z hz
      exact ⟨(hbox z).mp hz |>.2.1, (hbox z).mp hz |>.2.2⟩
    have hQhull : Q = convexHull ℝ (Q.extremePoints ℝ) :=
      bounded_polyhedron_hull k n (B.map (Int.cast : ℤ → ℝ))
        (fun i => (d i : ℝ)) ⟨x, hxQ⟩ hbQ
    have hvertices : Q.extremePoints ℝ ⊆ {z | z ∈ P ∧ IsIntegralPoint z} := by
      intro z hz
      exact ⟨((hbox z).mp hz.1).1, vertex_integral B d z hB hz⟩
    exact convexHull_mono hvertices (hQhull ▸ hxQ)
  · exact convexHull_min (fun _ hx => hx.1)
      (convex_polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)))

end P205.Polyhedra
