import MathGenome

/-!
# Consumer examples for the first D05 release

Integration examples for the assembled release. Original D05 and Specs
modules remain unchanged; see verification/results for the checked snapshot.

These proofs consume bundled Mathlib objects through the D05 interfaces.
Vector spaces and duals are algebraic unless an inner product is requested.
Matrices act on columns. The manuscript's first-slot-linear `D05.firstInner`
becomes `inner F` after reversing its arguments. Empty sizes and index types
remain allowed; the final example states its characteristic guard explicitly.
-/

noncomputable section

open scoped BigOperators Matrix TensorProduct

namespace MathGenome.Examples

section Algebraic

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Descent is an actual bundled map, so its representative formula composes
with ordinary Mathlib linearity. No dimensions or complements are needed. -/
theorem descent_with_add_formula (U : Submodule K V) (T : V →ₗ[K] W)
    (hU : U ≤ LinearMap.ker T) :
    ∃ S : (V ⧸ U) →ₗ[K] W, T = S.comp U.mkQ ∧
      ∀ v w : V, S (Submodule.Quotient.mk (v + w)) = T v + T w := by
  obtain ⟨S, hS, _⟩ := (D05.M06.QuotientLift.quotient_lift U T).mpr hU
  refine ⟨S, hS, ?_⟩
  intro v w
  rw [D05.M06.QuotientLift.factorization_apply U T S hS (v + w), map_add]

/-- A functional in the annihilator descends independently of a representative,
including arbitrary scalar multiples of a vector killed in the quotient. -/
theorem quotient_dual_representative (U : Submodule K V) (f : U.dualAnnihilator)
    (x u : V) (hu : u ∈ U) (a : K) :
    (D05.M07.QuotientDual.quotientDualEquiv K V U).symm f
      (Submodule.Quotient.mk (x + a • u)) = f.val x := by
  have hfu : f.val u = 0 :=
    (Submodule.mem_dualAnnihilator f.val).mp f.property u hu
  change ((Specs.D05.M07.QuotientDual.quotientDualEquiv_value K V U).symm f)
    (Submodule.Quotient.mk (x + a • u)) = f.val x
  rw [D05.M07.QuotientDual.quotientDualEquiv_symm_apply U f]
  simp only [map_add, map_smul, hfu, smul_zero, add_zero]

end Algebraic

section Matrices

variable {K : Type*} [Field K]

/-- The transpose's Mathlib matrix rank is the dimension of the original
rectangular coordinate map's range. Both matrix dimensions may be zero. -/
theorem transpose_rank_as_range_dimension {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) :
    A.transpose.rank = Module.finrank K (LinearMap.range A.mulVecLin) := by
  calc
    A.transpose.rank = A.rank := D05.M04.RankBridge.rank_transpose A
    _ = Module.finrank K (Submodule.span K (Set.range A.col)) :=
      D05.M04.RankBridge.rank_eq_column_rank A
    _ = Module.finrank K (LinearMap.range A.mulVecLin) :=
      D05.M04.RankBridge.column_rank_eq_map_rank A

/-- Reducing the entire augmentation supplies a reduced matrix together with
the exact original solution set, even for an inconsistent system. -/
theorem reduced_augmentation_with_same_solutions {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    ∃ R : Matrix (Fin m) (Fin (n + 1)) K,
      R.IsReducedRowEchelon ∧
      ∀ x : Fin n → K,
        (fun (i : Fin m) (j : Fin n) => R i j.castSucc) *ᵥ x =
          (fun i => R i (Fin.last n)) ↔
          A *ᵥ x = b := by
  obtain ⟨ops, hR⟩ :=
    D05.M01.Elimination.exists_reduced (D05.M01.System.augmentedMatrix A b)
  refine ⟨D05.M01.Elimination.applyOps ops
    (D05.M01.System.augmentedMatrix A b), hR, ?_⟩
  intro x
  exact D05.M01.SolutionInvariance.sequence_preserves_solutions ops A b x

/-- A nonzero Mathlib determinant yields an actual unique solution through
the D05 determinant bridge and bundled coordinate-map criterion. `n = 0`
is included, consistently with the empty determinant being one. -/
theorem unique_solution_of_det_ne_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : A.det ≠ 0) (b : Fin n → K) :
    ∃! x : Fin n → K, A *ᵥ x = b := by
  have hpaper : D05.M05.determinant A ≠ 0 := by
    rwa [D05.M05.DetDefinition.matrix_det_bridge]
  have hbij : Function.Bijective A.mulVecLin :=
    (D05.M05.DetInvertible.bijective_iff_isUnit_det A).mpr
      (isUnit_iff_ne_zero.mpr hpaper)
  obtain ⟨x, hx⟩ := hbij.2 b
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hbij.1 (hy.trans hx.symm)

end Matrices

section InnerProduct

variable {F V W : Type*} [RCLike F]
  [NormedAddCommGroup V] [InnerProductSpace F V]
  [NormedAddCommGroup W] [InnerProductSpace F W]

/-- A Mathlib orthonormal algebraic basis can use the D05 Fourier theorem,
with the coefficient order translated back to Mathlib's convention. -/
theorem mathlib_fourier_expansion {I : Type*} [Fintype I]
    (b : Module.Basis I F V) (hb : Orthonormal F b) (v : V) :
    v = ∑ i, inner F (b i) v • b i := by
  have hbD : D05.orthonormalFamily (F := F) b :=
    (D05.M12.Orthonormal.orthonormal_iff_mathlib b).mpr hb
  simpa only [D05.firstInner] using
    D05.M12.FourierParseval.fourier_expansion b hbD v

/-- Kernel perturbations preserve the least-squares minimum; among them,
equality with the pseudoinverse's norm occurs precisely at zero perturbation.
The scalar can be real or complex, and neither space needs positive dimension. -/
theorem least_squares_kernel_perturbation
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) (w : W) (k : V) (hk : k ∈ T.ker) :
    (∀ u : V,
      ‖T (D05.pseudoinverse T w + k) - w‖ ≤ ‖T u - w‖) ∧
    (‖D05.pseudoinverse T w + k‖ = ‖D05.pseudoinverse T w‖ ↔ k = 0) := by
  have hmin := (D05.M14.LeastSquares.minimizer_iff_exists_kernel T w
    (D05.pseudoinverse T w + k)).mpr ⟨k, hk, rfl⟩
  refine ⟨hmin, ?_⟩
  rw [D05.M14.LeastSquares.norm_eq_iff T w _ hmin]
  constructor
  · intro h
    exact add_left_cancel (h.trans (add_zero _).symm)
  · intro h
    simp only [h, add_zero]

end InnerProduct

section Tensors

variable {K V W Z : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup Z] [Module K Z]

/-- The coordinate inverse to tensor–Hom commutes with postcomposition.
Only the source has a finite basis; `W` and `Z` may be infinite dimensional.
An empty basis is valid as well. -/
theorem tensor_hom_postcomposition {I : Type*} [Fintype I]
    (b : Module.Basis I K V) (T : V →ₗ[K] W) (g : W →ₗ[K] Z) :
    D05.M15.TensorDualHom.psi b (g.comp T) =
      TensorProduct.map (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V) g
        (D05.M15.TensorDualHom.psi b T) := by
  rw [D05.M15.TensorDualHom.psi_apply b (g.comp T),
    D05.M15.TensorDualHom.psi_apply b T, map_sum]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.comp_apply]

/-- Degree zero pairing is scalar multiplication, and remains linear in a
sum of scaled empty tensors. No finiteness of any vector-space factor is used. -/
theorem empty_tensor_pairing_add (a c d : K) :
    PiTensorProduct.dualDistrib
      (a • PiTensorProduct.tprod K (0 : Fin 0 → Module.Dual K K) +
        c • PiTensorProduct.tprod K (0 : Fin 0 → Module.Dual K K))
      (d • PiTensorProduct.tprod K (0 : Fin 0 → K)) = a * d + c * d := by
  rw [← add_smul, D05.M15.TensorPairing.nullary_pairing]
  exact add_mul a c d

section Averaging

open Specs.D05.M15.Normalization

/-- Equality of symmetric or exterior quotient classes can be tested on their
canonical averaged tensors. Characteristic zero supplies every factorial
inverse; arbitrary dimension and degree zero are retained. -/
theorem quotient_classes_detect_averages [CharZero K] (p : ℕ)
    (x y : PiTensorProduct K (fun _ : Fin p => V)) :
    (symQ (K := K) (V := V) p x = symQ (K := K) (V := V) p y ↔
      symP (K := K) (V := V) p x = symP (K := K) (V := V) p y) ∧
    (extQ (K := K) (V := V) p x = extQ (K := K) (V := V) p y ↔
      altP (K := K) (V := V) p x = altP (K := K) (V := V) p y) := by
  constructor
  · constructor
    · intro h
      have hs := D05.M15.Normalization.symmetricSection_projection (K := K) (V := V) p
      calc
        symP p x = D05.M15.Normalization.symmetricSection (K := K) (V := V) p
          (symQ (K := K) (V := V) p x) :=
          (LinearMap.congr_fun hs x).symm
        _ = D05.M15.Normalization.symmetricSection (K := K) (V := V) p
          (symQ (K := K) (V := V) p y) := congrArg _ h
        _ = symP p y := LinearMap.congr_fun hs y
    · intro h
      have hq := congrArg (symQ (K := K) (V := V) p) h
      simpa only [← LinearMap.comp_apply,
        (D05.M15.Normalization.quotient_averages p).1] using hq
  · constructor
    · intro h
      have hs := D05.M15.Normalization.exteriorSection_projection (K := K) (V := V) p
      calc
        altP p x = D05.M15.Normalization.exteriorSection (K := K) (V := V) p (extQ p x) :=
          (LinearMap.congr_fun hs x).symm
        _ = D05.M15.Normalization.exteriorSection (K := K) (V := V) p (extQ p y) := congrArg _ h
        _ = altP p y := LinearMap.congr_fun hs y
    · intro h
      have hq := congrArg (extQ (K := K) (V := V) p) h
      simpa only [← LinearMap.comp_apply,
        (D05.M15.Normalization.quotient_averages p).2] using hq

end Averaging

end Tensors

end MathGenome.Examples
