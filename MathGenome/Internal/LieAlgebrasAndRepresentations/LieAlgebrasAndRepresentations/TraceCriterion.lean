import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.TraceCriterion
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.LieTheorem
import Mathlib.Algebra.Lie.CartanCriterion

open LieAlgebra LieModule LinearMap
open scoped TensorProduct

universe u v w
namespace LieAlgebrasAndRepresentations

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable def killingForm (k : Type u) (G : Type v)
    [Field k] [LieRing G] [LieAlgebra k G] : LinearMap.BilinForm k G :=
  _root_.killingForm k G

theorem killingForm_apply {k : Type u} {G : Type v}
    [Field k] [LieRing G] [LieAlgebra k G] (x y : G) :
    killingForm k G x y =
      LinearMap.trace k G (LieAlgebra.ad k G x * LieAlgebra.ad k G y) := rfl

/-- Once an ideal is solvable, the corresponding derived-series tail vanishes. -/
theorem solvable_of_solvable_derived (k : Type u) (G : Type v)
    [Field k] [LieRing G] [LieAlgebra k G] (n : ℕ)
    (h : LieAlgebra.IsSolvable (LieAlgebra.derivedSeries k G n)) :
    LieAlgebra.IsSolvable G := by
  obtain ⟨m, hm⟩ := LieAlgebra.IsSolvable.solvable k (LieAlgebra.derivedSeries k G n)
  apply LieAlgebra.IsSolvable.mk (R := k) (k := m + n)
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hm
  simpa only [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_add] using hm

/-- The reverse matrix criterion uses the zero trace form on the derived ideal. -/
theorem solvable_of_trace_orthogonal {k : Type u} [Field k] [CharZero k]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (A : LieSubalgebra k (Module.End k V))
    (h : ∀ x : A, x ∈ LieAlgebra.derivedSeries k A 1 →
      ∀ y : A, LinearMap.trace k V ((x : Module.End k V) * (y : Module.End k V)) = 0) :
    LieAlgebra.IsSolvable A := by
  let D := LieAlgebra.derivedSeries k A 1
  let DD : LieIdeal k A := ⁅D, D⁆
  have hz : LieModule.traceForm k D V = 0 := by
    ext ⟨x, hx⟩ ⟨y, hy⟩
    exact h x hx y
  have hn : LieModule.IsNilpotent (LieAlgebra.derivedSeries k D 1) V :=
    LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero hz
  have hnil : LieRing.IsNilpotent DD := by
    rw [LieAlgebra.isNilpotent_iff_forall (R := k)]
    rintro ⟨x, hx⟩
    apply LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad (DD : LieSubalgebra k A)
    apply LieAlgebra.isNilpotent_ad_of_isNilpotent (L := A)
    have hxD : x ∈ D := LieSubmodule.lie_le_left D D hx
    exact (LieModule.isNilpotent_iff_forall' (R := k)).mp hn
      ⟨⟨x, hxD⟩, by
        rwa [LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap, LieIdeal.mem_comap]⟩
  have hs : LieAlgebra.IsSolvable DD := inferInstance
  apply solvable_of_solvable_derived k A 2
  exact hs

/-- Diagonal multiplication for two upper triangular matrices. -/
private theorem upper_mul_diag {k : Type u} [Field k] {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) k)
    (hM : ∀ i j, j < i → M i j = 0)
    (hN : ∀ i j, j < i → N i j = 0) (i : Fin n) :
    (M * N) i i = M i i * N i i := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · rw [hM i j hlt, zero_mul]
    · rw [hN j i hgt, mul_zero]
  · simp

/-- Lie's theorem makes the derived algebra orthogonal to the whole algebra
for the trace form of every finite-dimensional representation. -/
theorem traceForm_eq_zero_of_solvable_of_isAlgClosed
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {G : Type v} [LieRing G] [LieAlgebra k G] [FiniteDimensional k G]
    [LieAlgebra.IsSolvable G]
    {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [LieRingModule G V] [LieModule k G V]
    (x : G) (hx : x ∈ LieAlgebra.derivedSeries k G 1) (y : G) :
    LieModule.traceForm k G V x y = 0 := by
  classical
  obtain ⟨n, b, hb⟩ := common_upper_triangular_basis (k := k) (G := G) (V := V)
  let T : G →ₗ[k] Matrix (Fin n) (Fin n) k :=
    (LinearMap.toMatrix b b).toLinearMap.comp (LieModule.toEnd k G V).toLinearMap
  have hT (z : G) (i j : Fin n) (hij : j < i) : T z i j = 0 := by
    simpa [T, LinearMap.toMatrix_apply] using hb z i j hij
  have hmul (z w : G) (i : Fin n) :
      (T z * T w) i i = T z i i * T w i i :=
    upper_mul_diag _ _ (hT z) (hT w) i
  have hlie (z w : G) : T ⁅z, w⁆ = T z * T w - T w * T z := by
    dsimp [T]
    rw [LieHom.map_lie, Ring.lie_def, map_sub, LinearMap.toMatrix_mul, LinearMap.toMatrix_mul]
  have hd (i : Fin n) : T x i i = 0 := by
    replace hx : x ∈ Submodule.span k {⁅z, w⁆ | (z : G) (w : G)} := by
      rw [← LieAlgebra.coe_derivedSeries_one_eq]
      exact hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨z, w, rfl⟩ := hz
      rw [hlie, Matrix.sub_apply, hmul, hmul, mul_comm, sub_self]
    | zero => simp
    | add z w _ _ hz hw => simp [hz, hw]
    | smul c z _ hz => simp [hz]
  rw [LieModule.traceForm_apply_apply, LinearMap.trace_eq_matrix_trace k b,
    ← Module.End.mul_eq_comp, LinearMap.toMatrix_mul]
  change Matrix.trace (T x * T y) = 0
  simp only [Matrix.trace, Matrix.diag, hmul, hd, zero_mul, Finset.sum_const_zero]

/-- Descent of the trace statement from an algebraic closure. -/
theorem traceForm_eq_zero_of_solvable
    {k : Type u} [Field k] [CharZero k]
    {G : Type v} [LieRing G] [LieAlgebra k G] [FiniteDimensional k G]
    [LieAlgebra.IsSolvable G]
    {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [LieRingModule G V] [LieModule k G V]
    (x : G) (hx : x ∈ LieAlgebra.derivedSeries k G 1) (y : G) :
    LieModule.traceForm k G V x y = 0 := by
  let K := AlgebraicClosure k
  have hxK : 1 ⊗ₜ[k] x ∈ LieAlgebra.derivedSeries K (K ⊗[k] G) 1 := by
    rw [LieAlgebra.derivedSeries_baseChange]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hx
  have h := traceForm_eq_zero_of_solvable_of_isAlgClosed
    (V := K ⊗[k] V) (1 ⊗ₜ[k] x) hxK (1 ⊗ₜ[k] y)
  rw [LieModule.traceForm_baseChange] at h
  simpa only [LinearMap.BilinForm.baseChange_tmul, one_mul, Algebra.smul_def,
    mul_one, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective k K)] using h

/-- Cartan's matrix trace criterion over the original characteristic-zero field. -/
theorem trace_criterion :
    Specs.LieAlgebrasAndRepresentations.TraceCriterion.trace_criterion_type := by
  intro k _ _ V _ _ _ A
  constructor
  · intro hs x hx y
    exact traceForm_eq_zero_of_solvable (V := V) x hx y
  · exact solvable_of_trace_orthogonal A

/-- Cartan's abstract criterion for the Killing form. -/
theorem killing_criterion :
    Specs.LieAlgebrasAndRepresentations.TraceCriterion.killing_criterion_type := by
  intro k _ _ G _ _ _
  constructor
  · intro hs x hx y
    exact traceForm_eq_zero_of_solvable (V := G) x hx y
  · intro h
    apply LieAlgebra.isSolvable_of_killingForm_apply_lie_eq_zero (R := k)
    intro y x hx
    rw [LieModule.traceForm_comm]
    exact h x hx y

end LieAlgebrasAndRepresentations
