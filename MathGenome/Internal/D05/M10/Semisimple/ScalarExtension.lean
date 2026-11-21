import MathGenome.Internal.Specs.D05.M10.Semisimple.ScalarExtension
import MathGenome.Internal.D05.M05.Adjugate.RankMinors
import MathGenome.Internal.D05.M08.Minpoly

/-! Scalar extension preserves matrix minimal polynomials (K05.10.semisimple).
The rank proof uses the upstream rank–minor theorem; flattening then transfers
independence of matrix powers. The final step uses uniqueness of a monic
annihilator with independent lower powers, so it identifies every coefficient.
The characteristic-zero polynomial statements are separate from this argument. -/

noncomputable section

namespace D05.M10.Semisimple.ScalarExtension

open Polynomial

/-- Determinants of selected square minors commute with coefficient extension. -/
theorem minor_map {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    {m n k : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin n) :
    ((A.map (algebraMap K L)).submatrix rows cols).det =
      algebraMap K L (A.submatrix rows cols).det := by
  rw [Matrix.submatrix_map]
  exact ((algebraMap K L).map_det _).symm

theorem rank_preserved : Specs.D05.M10.Semisimple.ScalarExtension.rank_preserved := by
  intro K L _ _ _ m n A
  apply Nat.le_antisymm
  · obtain ⟨rows, cols, hdet⟩ := M05.Adjugate.RankMinors.exists_rank_minor
      (A.map (algebraMap K L))
    rw [M05.DetDefinition.matrix_det_bridge, minor_map] at hdet
    apply M05.Adjugate.RankMinors.minor_size_le_rank A rows cols
    rw [M05.DetDefinition.matrix_det_bridge]
    exact fun h => hdet (by rw [h, map_zero])
  · obtain ⟨rows, cols, hdet⟩ := M05.Adjugate.RankMinors.exists_rank_minor A
    apply M05.Adjugate.RankMinors.minor_size_le_rank
      (A.map (algebraMap K L)) rows cols
    rw [M05.DetDefinition.matrix_det_bridge, minor_map]
    rw [M05.DetDefinition.matrix_det_bridge] at hdet
    exact (map_ne_zero (algebraMap K L)).mpr hdet

theorem columns_independent_extension :
    Specs.D05.M10.Semisimple.ScalarExtension.columns_independent_extension := by
  intro K L _ _ _ m n A
  simp only [linearIndependent_iff_card_eq_finrank_span, Set.finrank,
    ← Matrix.rank_eq_finrank_span_cols, rank_preserved (L := L) A]

/-- Row-major flattening, with each matrix entry retained as a separate coordinate. -/
def flatten {K : Type*} [Field K] (n : ℕ) :
    Matrix (Fin n) (Fin n) K →ₗ[K] (Fin (n * n) → K) where
  toFun M i := M (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem flatten_injective {K : Type*} [Field K] (n : ℕ) :
    Function.Injective (flatten (K := K) n) := by
  intro A B h
  ext i j
  have he := congrFun h (finProdFinEquiv (i, j))
  change A (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
    (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 =
    B (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
    (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 at he
  simpa only [Equiv.symm_apply_apply] using he

/-- Columns of the coordinate matrix are exactly the flattened powers. -/
def powerColumns {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (d : ℕ) : Matrix (Fin (n * n)) (Fin d) K :=
  fun i j => flatten n (A ^ j.val) i

theorem powers_independent_iff_columns {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (d : ℕ) :
    LinearIndependent K (powerColumns A d).col ↔
      LinearIndependent K (fun i : Fin d => A ^ i.val) := by
  exact (flatten (K := K) n).linearIndependent_iff
    (LinearMap.ker_eq_bot.mpr (flatten_injective n))

theorem powerColumns_map {K : Type*} {L : Type*}
    [Field K] [Field L] [Algebra K L] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (d : ℕ) :
    powerColumns (A.map (algebraMap K L)) d =
      (powerColumns A d).map (algebraMap K L) := by
  ext i j
  exact congrFun (congrFun (A.map_pow (algebraMap K L) j.val).symm
    (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2

theorem powers_independent_extension :
    Specs.D05.M10.Semisimple.ScalarExtension.powers_independent_extension := by
  intro K L _ _ _ n A d
  rw [← powers_independent_iff_columns, powerColumns_map,
    columns_independent_extension, powers_independent_iff_columns]

/-- Matrix evaluation is compatible with extension of both coefficients and entries. -/
theorem aeval_map_matrix {K : Type*} {L : Type*} [Field K] [Field L]
    [Algebra K L] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (p : Polynomial K) :
    aeval (A.map (algebraMap K L)) (p.map (algebraMap K L)) =
      (aeval A p).map (algebraMap K L) := by
  symm
  exact map_aeval_eq_aeval_map (φ := algebraMap K L)
    (ψ := (algebraMap K L).mapMatrix) (by
      ext a i j
      by_cases h : i = j <;>
        simp [Matrix.algebraMap_eq_diagonal, h]) p A

theorem minpoly_scalar_extension :
    Specs.D05.M10.Semisimple.ScalarExtension.minpoly_scalar_extension := by
  intro K L _ _ _ n A
  have hm : (minpoly K A).Monic := minpoly.monic (IsIntegral.of_finite K A)
  apply minpoly.eq_of_linearIndependent L (A.map (algebraMap K L))
    (hm.map (algebraMap K L))
  · simp only [aeval_map_matrix, minpoly.aeval, Matrix.map_zero, map_zero]
  · rw [degree_eq_natDegree (hm.map (algebraMap K L)).ne_zero,
      hm.natDegree_map]
  · exact (powers_independent_extension A _).mpr (linearIndependent_pow A)

theorem empty_minpoly : Specs.D05.M10.Semisimple.ScalarExtension.empty_minpoly := by
  intro K L _ _ _ A
  exact ⟨minpoly.subsingleton K A,
    minpoly.subsingleton L (A.map (algebraMap K L))⟩

theorem irreducible_derivative :
    Specs.D05.M10.Semisimple.ScalarExtension.irreducible_derivative := by
  intro K _ _ p hp
  exact ⟨Polynomial.derivative_ne_zero.mpr hp.natDegree_pos.ne',
    natDegree_derivative_lt hp.natDegree_pos.ne', hp.separable⟩

theorem irreducible_extension_separable :
    Specs.D05.M10.Semisimple.ScalarExtension.irreducible_extension_separable := by
  intro K L _ _ _ _ p hp
  exact hp.separable.map

theorem irreducible_extension_roots :
    Specs.D05.M10.Semisimple.ScalarExtension.irreducible_extension_roots := by
  intro K L _ _ _ _ p hp
  have hs : (p.map (algebraMap K L)).Separable := irreducible_extension_separable p hp
  exact ⟨Polynomial.nodup_roots hs, fun a ha => hs.eval₂_derivative_ne_zero (RingHom.id L) ha⟩

end D05.M10.Semisimple.ScalarExtension
