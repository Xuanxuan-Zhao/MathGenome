import MathGenome.Internal.Specs.D05.M04.Blocks

/-! Block components, composition, and invariant direct sums (K05.04.blocks). -/
namespace D05.M04.Blocks
open Specs.D05.M04.Blocks

/-- Blocks act by inclusion, the original map, and component projection. -/
theorem block_apply : Specs.D05.M04.Blocks.block_apply := by
  intro R V W I J _ _ _ _ _ _ _ _ _ E F _ _ _ _ e f T i j x
  rfl

theorem apply_eq_sum : Specs.D05.M04.Blocks.apply_eq_sum := by
  intro R V W I J _ _ _ _ _ _ _ _ _ E F _ _ _ _ e f T x i
  let H := (LinearMap.proj i).comp (f.symm.toLinearMap.comp (T.comp e.toLinearMap))
  have hx := LinearMap.sum_single_apply E x
  have hh := congrArg H hx
  simpa only [H, map_sum, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearEquiv.coe_coe, block, LinearMap.single_apply] using hh.symm

theorem block_comp : Specs.D05.M04.Blocks.block_comp := by
  classical
  intro R V W X I J L _ _ _ _ _ _ _ _ _ _ _ _ G _ _ E F _ _ _ _ e f g S T l j
  apply LinearMap.ext
  intro x
  have h := apply_eq_sum f g S (f.symm (T (e (Pi.single j x)))) l
  simpa only [block, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearEquiv.coe_coe, LinearMap.single_apply, LinearEquiv.apply_symm_apply,
    LinearMap.sum_apply] using h

theorem block_matrix_comp : Specs.D05.M04.Blocks.block_matrix_comp := by
  intro R V W X I J L _ _ _ _ _ _ _ _ _ _ _ _ G _ _ E F _ _ _ _ e f g S T n m p b c d l j
  rw [block_comp e f g S T l j, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact LinearMap.toMatrix_comp (b j) (c i) (d l) _ _

theorem block_matrix_entry : Specs.D05.M04.Blocks.block_matrix_entry := by
  intro R V W I J _ _ _ _ _ _ _ _ _ E F _ _ _ _ e f T i j n m b c a d
  exact LinearMap.toMatrix_apply b c _ a d

theorem matrix_mul_blocks : Specs.D05.M04.Blocks.matrix_mul_blocks := by
  intro R I J L _ _ r s t _ A B l j
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.sum_apply,
    Fintype.sum_sigma]

section Internal
variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype I] [DecidableEq I]

/-- The canonical external-to-internal map includes a single component. -/
theorem sumEquiv_single (U : I → Submodule K V)
    (h : Specs.D05.M06.DirectSum.UniqueDecomposition U) (j : I) (u : U j) :
    sumEquiv U h (Pi.single j u) = (u : V) := by
  change (∑ i, ((Pi.single j u : ∀ i, U i) i : V)) = (u : V)
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · simp

/-- Membership in a summand means that all other components vanish. -/
theorem coordinates_of_mem (U : I → Submodule K V)
    (h : Specs.D05.M06.DirectSum.UniqueDecomposition U) (j : I)
    (x : V) (hx : x ∈ U j) :
    (sumEquiv U h).symm x = Pi.single j (⟨x, hx⟩ : U j) := by
  apply (sumEquiv U h).injective
  rw [LinearEquiv.apply_symm_apply, sumEquiv_single]
end Internal

theorem internal_block_apply : Specs.D05.M04.Blocks.internal_block_apply := by
  intro K V W I J _ _ _ _ _ _ _ _ _ U Z hU hZ T i j u
  change (sumEquiv Z hZ).symm (T (sumEquiv U hU (Pi.single j u))) i = _
  rw [sumEquiv_single]

theorem invariant_iff_off_diagonal : Specs.D05.M04.Blocks.invariant_iff_off_diagonal := by
  intro K V I _ _ _ _ _ U h T j
  constructor
  · intro hT i hij
    apply LinearMap.ext
    intro u
    rw [internal_block_apply U U h h T i j u,
      coordinates_of_mem U h j (T (u : V)) (hT u u.property)]
    simp [Pi.single_eq_of_ne hij]
  · intro hz x hx
    let c := (sumEquiv U h).symm (T x)
    have hc : c = Pi.single j (c j) := by
      funext i
      by_cases hij : i = j
      · subst i
        simp
      · have hi := congrArg (fun A : U j →ₗ[K] U i => A ⟨x, hx⟩) (hz i hij)
        rw [internal_block_apply U U h h T i j ⟨x, hx⟩] at hi
        simpa only [c, Pi.single_eq_of_ne hij, LinearMap.zero_apply] using hi
    have he : T x = (c j : V) := by
      calc T x = sumEquiv U h c := (LinearEquiv.apply_symm_apply _ _).symm
           _ = sumEquiv U h (Pi.single j (c j)) := congrArg (sumEquiv U h) hc
           _ = (c j : V) := sumEquiv_single U h j (c j)
    rw [he]
    exact (c j).property

theorem invariant_iff_matrix_off_diagonal :
    Specs.D05.M04.Blocks.invariant_iff_matrix_off_diagonal := by
  intro K V I _ _ _ _ _ U h T n b j
  simp only [invariant_iff_off_diagonal U h T, LinearEquiv.map_eq_zero_iff]

theorem all_invariant_iff_block_diagonal :
    Specs.D05.M04.Blocks.all_invariant_iff_block_diagonal := by
  intro K V I _ _ _ _ _ U h T
  simp only [invariant_iff_off_diagonal U h T]
  exact forall_comm

theorem invariant_iff_lower_left_zero :
    Specs.D05.M04.Blocks.invariant_iff_lower_left_zero := by
  intro K V _ _ _ U W h T
  have H := invariant_iff_off_diagonal (fun b : Bool => if b then W else U) h T false
  simpa [Bool.forall_bool] using H

theorem both_invariant_iff_off_diagonal_zero :
    Specs.D05.M04.Blocks.both_invariant_iff_off_diagonal_zero := by
  intro K V _ _ _ U W h T
  have H := invariant_iff_off_diagonal (fun b : Bool => if b then W else U) h T true
  have HW : Specs.D05.M06.Invariant.invariant_value K V W T ↔
      block (sumEquiv _ h) (sumEquiv _ h) T false true = 0 := by
    simpa [Bool.forall_bool] using H
  exact and_congr (invariant_iff_lower_left_zero U W h T) HW

end D05.M04.Blocks
