import MathGenome.Internal.Specs.D05.M15.TensorBasis.RankDecomposable
import MathGenome.Internal.D05.M15.TensorBasis
import MathGenome.Internal.D05.M15.TensorDualHom
import MathGenome.Internal.D05.M07.Biddual
import MathGenome.Internal.D05.M04.RankBridge

namespace D05.M15.TensorBasis.RankDecomposable

open scoped TensorProduct
open Specs.D05.M15.TensorBasis.RankDecomposable

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem associated_tmul : Specs.D05.M15.TensorBasis.RankDecomposable.associated_tmul := by
  intro K V W _ _ _ _ _ v w φ
  rfl

theorem associated_sum : Specs.D05.M15.TensorBasis.RankDecomposable.associated_sum := by
  intro K V W _ _ _ _ _ r v w φ
  simp only [map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => associated_tmul (v i) (w i) φ

theorem matrix_formula : Specs.D05.M15.TensorBasis.RankDecomposable.matrix_formula := by
  intro K V W _ _ _ _ _ _ _ n m e f z
  induction z using TensorProduct.inductionOn with
  | tmul v w =>
    ext j i
    simp [LinearMap.toMatrix_apply, coefficientMatrix,
      Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.coe_dualBasis, mul_comm]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    ext j i
    simp [coefficientMatrix]

theorem rank_matrix : Specs.D05.M15.TensorBasis.RankDecomposable.rank_matrix := by
  intro K V W _ _ _ _ _ _ _ n m e f z
  have h := D05.M04.RankBridge.matrixOfMap_rank e.dualBasis f (associatedMap z)
  change (LinearMap.toMatrix e.dualBasis f (associatedMap z)).rank = tensorRank z at h
  rw [matrix_formula e f z, Matrix.rank_transpose] at h
  exact h.symm

theorem range_containment : Specs.D05.M15.TensorBasis.RankDecomposable.range_containment := by
  intro K V W _ _ _ _ _ r v w
  rintro y ⟨φ, rfl⟩
  rw [associated_sum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, rfl⟩)

private theorem rank_le_span (r : ℕ) (v : Fin r → V) (w : Fin r → W) :
    tensorRank (∑ i, v i ⊗ₜ[K] w i) ≤
      Module.finrank K (Submodule.span K (Set.range w)) := by
  let : FiniteDimensional K (Submodule.span K (Set.range w)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range w)
  exact Submodule.finrank_mono (range_containment r v w)

theorem rank_bound : Specs.D05.M15.TensorBasis.RankDecomposable.rank_bound := by
  intro K V W _ _ _ _ _ _ _ z r ⟨v, w, hz⟩
  rw [hz]
  exact (rank_le_span r v w).trans (by
    simpa only [Set.finrank, Fintype.card_fin] using finrank_range_le_card (R := K) w)

/-- Flipping tensor factors transposes the actual coefficient array. -/
private theorem coefficientMatrix_comm [FiniteDimensional K V] [FiniteDimensional K W]
    {n m : ℕ} (e : Module.Basis (Fin n) K V) (f : Module.Basis (Fin m) K W)
    (z : V ⊗[K] W) :
    coefficientMatrix f e (TensorProduct.comm K V W z) =
      (coefficientMatrix e f z).transpose := by
  induction z using TensorProduct.inductionOn with
  | tmul v w =>
    ext j i
    simp [coefficientMatrix, Module.Basis.tensorProduct_repr_tmul_apply, mul_comm]
  | add x y hx hy =>
    ext j i
    have hxi := congrArg (fun A => A j i) hx
    have hyi := congrArg (fun A => A j i) hy
    simpa [coefficientMatrix, map_add] using congrArg₂ (· + ·) hxi hyi

/-- Matrix rank is unchanged by interchanging the factors. -/
private theorem rank_comm [FiniteDimensional K V] [FiniteDimensional K W]
    (z : V ⊗[K] W) : tensorRank (TensorProduct.comm K V W z) = tensorRank z := by
  let e := Module.finBasis K V
  let f := Module.finBasis K W
  rw [rank_matrix f e, coefficientMatrix_comm e f, Matrix.rank_transpose, rank_matrix e f]

theorem minimal_independent : Specs.D05.M15.TensorBasis.RankDecomposable.minimal_independent := by
  intro K V W _ _ _ _ _ _ _ z r v w hz hr
  constructor
  · apply linearIndependent_iff_card_le_finrank_span.mpr
    have h := rank_le_span (K := K) r w v
    have hflip : TensorProduct.comm K V W z = ∑ i, w i ⊗ₜ[K] v i := by
      rw [hz]
      simp
    rw [← hflip, rank_comm, ← hr] at h
    simpa only [Fintype.card_fin, Set.finrank] using h
  · apply linearIndependent_iff_card_le_finrank_span.mpr
    have h := rank_le_span (K := K) r v w
    rw [← hz, ← hr] at h
    simpa only [Fintype.card_fin, Set.finrank] using h

/-- Coefficient extraction shows that the canonical associated map detects tensors. -/
private theorem associated_injective [FiniteDimensional K V] [FiniteDimensional K W] :
    Function.Injective (associatedMap (K := K) (V := V) (W := W)) := by
  intro x y h
  let e := Module.finBasis K V
  let f := Module.finBasis K W
  apply (e.tensorProduct f).repr.injective
  ext p
  have hm := congrArg (LinearMap.toMatrix e.dualBasis f) h
  rw [matrix_formula e f x, matrix_formula e f y] at hm
  exact congrArg (fun A => A p.2 p.1) hm

/-- Choose an image basis and pull its coordinate functionals back through
finite biduality. This constructs, rather than assumes, the short expression. -/
private theorem hasLength_rank [FiniteDimensional K V] [FiniteDimensional K W]
    (z : V ⊗[K] W) : HasLength z (tensorRank z) := by
  classical
  let T := associatedMap z
  change ∃ (v : Fin (Module.finrank K T.range) → V)
    (w : Fin (Module.finrank K T.range) → W), z = ∑ i, v i ⊗ₜ[K] w i
  let b := Module.finBasis K (LinearMap.range T)
  let E := LinearEquiv.ofBijective (Module.Dual.eval K V)
    (D05.M07.Biddual.evaluation_bijective (K := K) (V := V))
  let v := fun i => E.symm ((b.coord i).comp T.rangeRestrict)
  let w := fun i => (b i : W)
  have hv (i) (φ : Module.Dual K V) :
      φ (v i) = b.repr (T.rangeRestrict φ) i := by
    have h := congrArg (fun F : Module.Dual K (Module.Dual K V) => F φ)
      (E.apply_symm_apply ((b.coord i).comp T.rangeRestrict))
    exact h
  refine ⟨v, w, associated_injective ?_⟩
  ext φ
  rw [associated_sum]
  simp only [hv]
  change T φ = ∑ i, b.repr (T.rangeRestrict φ) i • (b i : W)
  have hb := congrArg (fun x : LinearMap.range T => (x : W))
    (b.sum_repr (T.rangeRestrict φ))
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hb
  exact hb.symm

theorem exists_minimal_expression :
    Specs.D05.M15.TensorBasis.RankDecomposable.exists_minimal_expression := by
  intro K V W _ _ _ _ _ _ _ z
  obtain ⟨v, w, hz⟩ := hasLength_rank z
  obtain ⟨hv, hw⟩ := minimal_independent z (tensorRank z) v w hz rfl
  exact ⟨v, w, hz, hv, hw⟩

theorem least_length : Specs.D05.M15.TensorBasis.RankDecomposable.least_length := by
  intro K V W _ _ _ _ _ _ _ z
  exact ⟨hasLength_rank z, fun _ hr => rank_bound z _ hr⟩

theorem rank_zero_iff : Specs.D05.M15.TensorBasis.RankDecomposable.rank_zero_iff := by
  intro K V W _ _ _ _ _ _ _ z
  constructor
  · intro h
    have hz : HasLength z 0 := h ▸ hasLength_rank z
    obtain ⟨v, w, heq⟩ := hz
    simpa using heq
  · rintro rfl
    simp [tensorRank]

theorem decomposable_iff : Specs.D05.M15.TensorBasis.RankDecomposable.decomposable_iff := by
  intro K V W _ _ _ _ _ _ _ z
  constructor
  · rintro ⟨v, w, rfl⟩
    apply rank_bound _ 1
    exact ⟨fun _ => v, fun _ => w, by simp⟩
  · intro h
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with hzero | hone
    · rw [(rank_zero_iff z).mp hzero]
      exact ⟨0, 0, by simp⟩
    · have hz : HasLength z 1 := hone ▸ hasLength_rank z
      obtain ⟨v, w, heq⟩ := hz
      exact ⟨v 0, w 0, by simpa using heq⟩

end D05.M15.TensorBasis.RankDecomposable
