import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SymplecticCompactKilling
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalRootsC
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.KillingCriterion
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Batteries.Tactic.OpenPrivate

/-! Compactness of the skew-Hermitian real form of the complex symplectic
algebra, and the resulting Killing criterion for the complex algebra. -/

noncomputable section

namespace LieAlgebrasAndRepresentations.SymplecticCompactKilling

open Matrix LieAlgebra
open Specs.LieAlgebrasAndRepresentations.ClassicalRootsC
open Specs.LieAlgebrasAndRepresentations.SymplecticCompactKilling
open LieAlgebrasAndRepresentations.RealForms
open Specs.LieAlgebrasAndRepresentations.PolarRealStructures (IsCompact hermitian)
open scoped ComplexOrder InnerProductSpace
attribute [local instance] LieRing.ofAssociativeRing

private theorem eq_zero_of_central {n : ℕ} (X : sp n)
    (h : ∀ Y : sp n, ⁅X, Y⁆ = 0) : X = 0 := by
  have hroot : X.val ∈ rootSpace (0 : Weight n) := by
    refine ⟨X.property, fun t => ?_⟩
    have ht := congrArg (fun Z : sp n => Z.val)
      (h ⟨Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal t,
        ClassicalRootsC.diagonal_mem n t⟩)
    change ⁅X.val, Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal t⁆ = 0 at ht
    rw [← lie_skew, ht]
    simp
  rw [ClassicalRootsC.zero_space n] at hroot
  obtain ⟨t, ht⟩ := hroot
  change Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal t = X.val at ht
  have hti (i : Fin n) : t i = 0 := by
    have hlong : bLong i ∈ rootSpace ((2 : ℂ) • eps i) := by
      rw [ClassicalRootsC.b_long_space n i]
      exact Submodule.subset_span (Set.mem_singleton _)
    have hbr := congrArg (fun Z : sp n => Z.val) (h ⟨bLong i, hlong.1⟩)
    change ⁅X.val, bLong i⁆ = 0 at hbr
    rw [← ht] at hbr
    have he := congrArg (fun Z : Mat n => Z (.inl i) (.inr i)) hbr
    rw [ClassicalRootsC.bracket_diagonal] at he
    simpa [signed, eps, bLong, sub_eq_add_neg, ← two_mul] using he
  apply Subtype.ext
  change X.val = 0
  rw [← ht, show t = 0 from funext hti]
  simp [Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.diagonal]

private theorem fixed_ad_ne_zero {n : ℕ} (ω : Conjugation (sp n)) {x : ω.fixed}
    (hx : x ≠ 0) : ad ℝ ω.fixed x ≠ 0 := by
  intro ha
  apply hx
  apply Subtype.ext
  apply eq_zero_of_central
  have hz (u : ω.fixed) : ⁅(x : sp n), (u : sp n)⁆ = 0 :=
    congrArg (fun z : ω.fixed => (z : sp n)) (LinearMap.congr_fun ha u)
  intro y
  obtain ⟨u, v, hy⟩ := fixed_decomposition ω y
  rw [← hy, lie_add, lie_smul, hz u, hz v, smul_zero, add_zero]

private abbrev matrixOf {n : ℕ} {ω : Conjugation (sp n)} (x : ω.fixed) : Mat n :=
  (x.val : Mat n)

/-- The real Hilbert–Schmidt pairing restricted to the skew-Hermitian matrices. -/
private def traceInner {n : ℕ} {ω : Conjugation (sp n)} (x y : ω.fixed) : ℝ :=
  -(Matrix.trace (matrixOf x * matrixOf y)).re

private theorem traceInner_skew {n : ℕ} {ω : Conjugation (sp n)} (x y z : ω.fixed) :
    traceInner y ⁅x, z⁆ = -traceInner ⁅x, y⁆ z := by
  unfold traceInner
  change -(Matrix.trace (matrixOf y * (matrixOf x * matrixOf z - matrixOf z * matrixOf x))).re =
    -(-(Matrix.trace ((matrixOf x * matrixOf y - matrixOf y * matrixOf x) * matrixOf z)).re)
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_sub, Matrix.mul_assoc,
    Matrix.mul_assoc, Matrix.trace_mul_cycle' (matrixOf y) (matrixOf z) (matrixOf x)]
  simp [sub_eq_add_neg]

@[instance_reducible] private def traceCore {n : ℕ} (ω : Conjugation (sp n))
    (hω : ∀ X : sp n, (ω.map X : Mat n) = -X.valᴴ) : InnerProductSpace.Core ℝ ω.fixed := by
  have hself (x : ω.fixed) :
      Matrix.trace ((matrixOf x)ᴴ * matrixOf x) = -Matrix.trace (matrixOf x * matrixOf x) := by
    have hx : -(matrixOf x)ᴴ = matrixOf x :=
      (hω x.val).symm.trans (congrArg (fun z : sp n => z.val) x.property)
    rw [neg_eq_iff_eq_neg.mp hx, Matrix.neg_mul, Matrix.trace_neg]
  have hnonneg (x : ω.fixed) := Complex.nonneg_iff.mp
    (Matrix.posSemidef_conjTranspose_mul_self (matrixOf x)).trace_nonneg
  refine
    { inner := traceInner
      conj_inner_symm := fun x y => ?_
      re_inner_nonneg := fun x => ?_
      add_left := fun x y z => ?_
      smul_left := fun x y r => ?_
      definite := fun x hx => ?_ }
  · change -(Matrix.trace (matrixOf y * matrixOf x)).re =
      -(Matrix.trace (matrixOf x * matrixOf y)).re
    rw [Matrix.trace_mul_comm]
  · change 0 ≤ traceInner x x
    simpa [hself x, traceInner] using (hnonneg x).1
  · change -(Matrix.trace ((matrixOf x + matrixOf y) * matrixOf z)).re = _
    simp [add_mul, Matrix.trace_add, traceInner, Complex.add_re, add_comm]
  · change -(Matrix.trace ((r • matrixOf x) * matrixOf y)).re = r * traceInner x y
    rw [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re]
    rw [traceInner, smul_eq_mul, mul_neg]
  · have hz : Matrix.trace ((matrixOf x)ᴴ * matrixOf x) = 0 := by
      apply Complex.ext
      · simpa [hself x, traceInner] using hx
      · exact (hnonneg x).2.symm
    exact Subtype.ext (Subtype.ext (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hz))

/-- The adjoint of a nonzero fixed element has strictly negative trace of its square. -/
theorem compact_killing : compact_killing_type := by
  intro n _ ω hω x hx
  let : FiniteDimensional ℝ (sp n) := FiniteDimensional.trans ℝ ℂ (sp n)
  let : FiniteDimensional ℝ ω.fixed :=
    FiniteDimensional.of_injective ω.fixed.toSubmodule.subtype Subtype.val_injective
  let c := traceCore ω hω
  let : NormedAddCommGroup ω.fixed := c.toNormedAddCommGroup
  let : InnerProductSpace ℝ ω.fixed := InnerProductSpace.ofCore c.toCore
  let b := stdOrthonormalBasis ℝ ω.fixed
  let A := ad ℝ ω.fixed x
  have hs (y : ω.fixed) : ⟪y, A (A y)⟫_ℝ = -⟪A y, A y⟫_ℝ :=
    traceInner_skew x y (A y)
  have hi : ∃ i, A (b i) ≠ 0 := by
    by_contra! h
    apply fixed_ad_ne_zero ω hx
    apply b.toBasis.ext
    exact h
  obtain ⟨i, hi⟩ := hi
  rw [killingForm_apply_apply, LinearMap.trace_eq_sum_inner _ b]
  calc
    _ = ∑ j, -⟪A (b j), A (b j)⟫_ℝ := Finset.sum_congr rfl fun j _ => hs (b j)
    _ < ∑ _j : Fin (Module.finrank ℝ ω.fixed), (0 : ℝ) := by
      refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
      · exact neg_nonpos.mpr real_inner_self_nonneg
      · exact neg_lt_zero.mpr (real_inner_self_pos.mpr hi)
    _ = 0 := Finset.sum_const_zero

private theorem conjugateTranspose_mem {n : ℕ} (X : sp n) : X.valᴴ ∈ sp n := by
  obtain ⟨hC, hB, hD⟩ := ClassicalRootsC.block_relations X.val X.property
  have hblocks (A B C D : Matrix (Fin n) (Fin n) ℂ) :
      (fromBlocks A B C D)ᴴ = fromBlocks Aᴴ Cᴴ Bᴴ Dᴴ := by
    ext (i | i) (j | j) <;> rfl
  rw [← Matrix.fromBlocks_toBlocks X.val, hblocks, ClassicalRootsC.block_form]
  exact ⟨by rw [← conjTranspose_transpose_eq_transpose_conjTranspose, hB],
    by rw [← conjTranspose_transpose_eq_transpose_conjTranspose, hC],
    by rw [hD, conjTranspose_neg, conjTranspose_transpose_eq_transpose_conjTranspose]⟩

private def matrixConjugation (n : ℕ) : Conjugation (sp n) where
  map :=
    { toFun := fun X => ⟨-X.valᴴ, (sp n).neg_mem (conjugateTranspose_mem X)⟩
      map_add' X Y := by
        apply Subtype.ext
        change -(X.val + Y.val)ᴴ = -X.valᴴ + -Y.valᴴ
        rw [conjTranspose_add, neg_add]
      map_smul' r X := by
        apply Subtype.ext
        change -(r • X.val)ᴴ = r • (-X.valᴴ)
        rw [conjTranspose_smul, star_trivial, smul_neg]
      map_lie' := by
        intro X Y
        apply Subtype.ext
        change -(X.val * Y.val - Y.val * X.val)ᴴ =
          (-X.valᴴ) * (-Y.valᴴ) - (-Y.valᴴ) * (-X.valᴴ)
        simp [conjTranspose_sub, conjTranspose_mul, neg_sub] }
  antilinear r X := by
    apply Subtype.ext
    change -(r • X.val)ᴴ = star r • (-X.valᴴ)
    rw [conjTranspose_smul, smul_neg]
  involutive X := by
    apply Subtype.ext
    change -(-X.valᴴ)ᴴ = X.val
    simp

open private hermitian_positive from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures

/-- The complex symplectic algebra has zero solvable radical. -/
theorem semisimple : semisimple_type := by
  intro n hn
  let ω := matrixConjugation n
  have hc : IsCompact ω := compact_killing n hn ω (fun _ => rfl)
  apply (semisimple_iff_killingForm_nondegenerate ℂ (sp n)).2
  have hright (x : sp n) (h : ∀ y, _root_.killingForm ℂ (sp n) y x = 0) : x = 0 := by
    by_contra hx
    have hp := hermitian_positive ω hc hx
    unfold hermitian at hp
    rw [h (ω.map x)] at hp
    simp at hp
  exact ⟨fun x h => hright x fun y => (killingForm_symmetric ℂ (sp n) y x).trans (h y), hright⟩

end LieAlgebrasAndRepresentations.SymplecticCompactKilling
