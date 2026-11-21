import MathGenome.Internal.Specs.D05.M11.Hermitian.TriangularGram.FlagProjection
import MathGenome.Internal.D05.M11.Nondegenerate.OneSidedComplements

noncomputable section
namespace D05.M11.Hermitian.TriangularGram.FlagProjection

open Module
open Specs.D05.M11.Hermitian.TriangularGram.FlagProjection

variable {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}

/-- The restricted original basis is a basis of its actual span W_k. -/
def flagBasis (e : Basis (Fin n) K V) (k : Fin (n + 1)) : Basis (Fin k.val) K (flag e k) :=
  Basis.span (e.linearIndependent.comp (Fin.castLE (Nat.le_of_lt_succ k.isLt))
    (Fin.castLE_injective _))

@[simp] lemma flagBasis_coe (e : Basis (Fin n) K V) (k : Fin (n + 1)) (i : Fin k.val) :
    (flagBasis e k i : V) = e (Fin.castLE (Nat.le_of_lt_succ k.isLt) i) := by
  exact Basis.coe_span_apply _ _

theorem empty_flag : Specs.D05.M11.Hermitian.TriangularGram.FlagProjection.empty_flag := by
  intro K V _ _ _ n e
  constructor
  · simp [flag]
  · intro B
    letI : IsEmpty (Fin ((0 : Fin (n + 1)).val)) :=
      inferInstanceAs (IsEmpty (Fin 0))
    exact Matrix.det_isEmpty

theorem restriction_nondegenerate :
    Specs.D05.M11.Hermitian.TriangularGram.FlagProjection.restriction_nondegenerate := by
  intro K V _ _ _ n e B h k
  apply (D05.M11.Nondegenerate.OneSidedComplements.matrix_criterion
    (RingEquiv.refl K) (starRingAut : K ≃+* K) B (flag e k) (flagBasis e k)).mpr
  have hdet : (leadingMatrix e B k).det ≠ 0 := by
    by_cases hk : 0 < k.val
    · exact h k hk
    · have hk0 : k = 0 := Fin.ext (Nat.eq_zero_of_not_pos hk)
      rw [hk0, (empty_flag e).2 B]
      exact one_ne_zero
  have hm : Matrix.of (fun i j => B (flagBasis e k i) (flagBasis e k j)) =
      leadingMatrix e B k := by
    ext i j
    simp [leadingMatrix, Specs.D05.M11.Hermitian.formMatrix_value]
  exact hm.symm ▸ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))

theorem flag_direct_sum :
    Specs.D05.M11.Hermitian.TriangularGram.FlagProjection.flag_direct_sum := by
  intro K V _ _ _ n e B h k
  let := Module.Finite.of_basis (flagBasis e k)
  have hn := restriction_nondegenerate e B h k
  exact ⟨D05.M11.Nondegenerate.OneSidedComplements.right_complement
    (RingEquiv.refl K) (starRingAut : K ≃+* K) B (flag e k) hn,
    D05.M11.Nondegenerate.OneSidedComplements.right_direct_sum
    (RingEquiv.refl K) (starRingAut : K ≃+* K) B (flag e k) hn⟩

theorem projection_properties :
    Specs.D05.M11.Hermitian.TriangularGram.FlagProjection.projection_properties := by
  intro K V _ _ _ n e B k E hE
  rcases hE with ⟨hp, hr, hk⟩
  refine ⟨?_, ?_, ?_⟩
  · intro v
    rw [← hr]
    exact LinearMap.mem_range_self E v
  · intro w hw
    exact (D05.M06.Projection.range_iff_fixed E hp w).mp (hr.symm ▸ hw)
  · intro v
    rw [← hk]
    exact (D05.M06.Projection.decomposition_formula E hp v).2.1

theorem representative_unique :
    Specs.D05.M11.Hermitian.TriangularGram.FlagProjection.representative_unique := by
  intro K V _ _ _ n e B j E hE
  obtain ⟨hmem, hfix, hres⟩ := projection_properties e B j.castSucc E hE
  refine ⟨?_, hres (e j), ?_⟩
  · simpa only [sub_sub_cancel_left] using (flag e j.castSucc).neg_mem (hmem (e j))
  · intro u hu ho
    have hf := hfix (u - e j) hu
    have hz : E u = 0 := by
      apply LinearMap.mem_ker.mp
      rw [hE.2.2]
      exact ho
    rw [map_sub, hz, zero_sub] at hf
    calc
      u = (u - e j) + e j := (sub_add_cancel u (e j)).symm
      _ = -E (e j) + e j := by rw [← hf]
      _ = e j - E (e j) := by rw [sub_eq_add_neg, add_comm]

theorem flag_projections :
    Specs.D05.M11.Hermitian.TriangularGram.FlagProjection.flag_projections := by
  intro K V _ _ _ n e B h
  have hex : ∀ k : Fin (n + 1), ∃! E : Module.End K V, IsFlagProjection e B k E := by
    intro k
    exact D05.M06.Projection.projection_exists_unique (flag e k)
      ((flag e k).orthogonalBilin B) (flag_direct_sum e B h k).2
  choose E hE huniq using hex
  refine ⟨E, fun k => ⟨hE k, huniq k⟩,
    fun k => projection_properties e B k (E k) (hE k), ?_, ?_⟩
  · apply LinearMap.range_eq_bot.mp
    rw [(hE 0).2.1, (empty_flag e).1]
  · intro j
    exact representative_unique e B j (E j.castSucc) (hE j.castSucc)

end D05.M11.Hermitian.TriangularGram.FlagProjection
