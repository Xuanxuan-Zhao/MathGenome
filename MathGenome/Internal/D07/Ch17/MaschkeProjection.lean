import MathGenome.Internal.D07.Ch17.KernelsImages
import MathGenome.Internal.Specs.D07.Ch17.MaschkeProjection
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
Maschke's theorem, with the paper's explicit average of conjugate projections.
The starting projection exists by the arbitrary-dimensional basis theorem.
-/
namespace D07.Ch17.MaschkeProjection

universe u v w

theorem averaged_projection :
    Specs.D07.Ch17.MaschkeProjection.AveragedProjection.{u, v, w} := by
  classical
  intro K G V _ _ _ _ _ hm ρ U hU E hE hEU
  let P : Module.End K V := (Fintype.card G : K)⁻¹ •
    ∑ g : G, (ρ g).comp (E.comp (ρ g⁻¹))
  have hP (x : V) : P x = (Fintype.card G : K)⁻¹ •
      ∑ g : G, ρ g (E (ρ g⁻¹ x)) := by
    simp [P, LinearMap.sum_apply]
  have hmem (x : V) : P x ∈ U := by
    rw [hP]
    exact U.smul_mem _ (U.sum_mem fun g _ => hU g _ (hE _))
  have hfix (x : V) (hx : x ∈ U) : P x = x := by
    rw [hP]
    have hs (g : G) : ρ g (E (ρ g⁻¹ x)) = x := by
      rw [hEU _ (hU g⁻¹ x hx)]
      exact ρ.self_inv_apply g x
    simp only [hs, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hm, one_smul]
  have heq : ρ.IsIntertwiningMap ρ P := by
    constructor
    intro h x
    rw [hP, hP, map_smul, map_sum]
    congr 1
    symm
    apply Fintype.sum_bijective (fun g : G => h * g) (Group.mulLeft_bijective h)
    intro g
    simp [mul_inv_rev, map_mul, Module.End.mul_apply]
  have hproj : LinearMap.IsProj U P := ⟨hmem, hfix⟩
  refine ⟨hmem, hfix, ?_, heq, ?_, hproj.isCompl⟩
  · ext x
    exact hfix (P x) (hmem x)
  · exact KernelsImages.kernel_invariant K G V V ρ ρ P heq

theorem invariant_complement :
    Specs.D07.Ch17.MaschkeProjection.InvariantComplement.{u, v, w} := by
  classical
  intro K G V _ _ _ _ _ hm ρ U hU
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨W, hW⟩ := U.exists_isCompl
  let E := U.projection W hW
  have hE (x : V) : E x ∈ U := U.projection_apply_mem hW x
  have hEU (x : V) (hx : x ∈ U) : E x = x :=
    U.projection_apply_of_mem_left hW hx
  have hm' : (Fintype.card G : K) ≠ 0 := by
    rwa [Fintype.card_eq_nat_card]
  obtain ⟨_, _, _, _, hk, hc⟩ := averaged_projection K G V hm' ρ U hU E hE hEU
  exact ⟨_, hk, hc⟩

theorem char_zero_condition :
    Specs.D07.Ch17.MaschkeProjection.CharZeroCondition.{u, v} := by
  intro K G _ _ _ _
  exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'

theorem positive_char_condition :
    Specs.D07.Ch17.MaschkeProjection.PositiveCharCondition.{u, v} := by
  intro K G _ _ _ p _ _
  exact (CharP.cast_eq_zero_iff K p (Nat.card G)).not

theorem no_normalization_of_dvd :
    Specs.D07.Ch17.MaschkeProjection.NoNormalizationOfDvd.{u, v} := by
  intro K G _ _ _ p _ _ hdiv
  have hzero : (Nat.card G : K) = 0 := (CharP.cast_eq_zero_iff K p _).mpr hdiv
  simp [hzero]

end D07.Ch17.MaschkeProjection
