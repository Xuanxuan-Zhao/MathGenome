import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.FiberProductRegularInCodimensionOne
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.RegularQuotient
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.FiberProductDepthOne
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-! The depth-one fiber product in SN-12, paper.tex:4343–4351.
All coordinates, the local structure, and the dimension are those of SN-12b.
The nonzero class of `(x,0)` supplies the quotient socle; DP-01 and DP-05
then determine the depth. -/

noncomputable section
universe u
open scoped Pointwise
namespace AdvCommAlg.Normality.FiberProduct
variable (k : Type u) [Field k]

/-- The module quotient used below is precisely the principal ring quotient
as an additive module. -/
theorem principalSubmodule_eq_span : principalSubmodule k =
    (Ideal.span {diagonalVariable k} : Ideal (Ring k)) := by
  rw [principalSubmodule, Ideal.ofList_singleton]
  change (Ideal.span {diagonalVariable k} : Ideal (Ring k)) * ⊤ = _
  exact Ideal.mul_top _

@[simp] theorem first_diagonalVariable : first k (diagonalVariable k) = planeVariable k 0 := by
  simp [diagonalVariable, pairVariable, first]

@[simp] theorem second_diagonalVariable : second k (diagonalVariable k) = planeVariable k 0 := by
  simp [diagonalVariable, pairVariable, second]

@[simp] theorem first_pairVariable_zero : first k (pairVariable k 0) = planeVariable k 0 := by
  simp [pairVariable, first]

@[simp] theorem second_pairVariable_zero : second k (pairVariable k 0) = 0 := by
  simp [pairVariable, second]

@[simp] theorem planeResidue_variable (i : Fin 2) : planeResidue k (planeVariable k i) = 0 := by
  simp [planeVariable, planeResidue]

theorem planeVariable_ne_zero (i : Fin 2) : planeVariable k i ≠ 0 := by
  simpa only [planeVariable, map_zero] using
    (IsLocalization.injective (LocalPlane k) (origin k 2).primeCompl_le_nonZeroDivisors).ne
      (MvPolynomial.X_ne_zero i)

theorem diagonalVariable_regular : IsSMulRegular (Ring k) (diagonalVariable k) := by
  intro a b hab
  apply Subtype.ext
  apply Prod.ext
  · change first k a = first k b
    apply mul_left_cancel₀ (planeVariable_ne_zero k 0)
    simpa only [smul_eq_mul, map_mul, first_diagonalVariable] using congrArg (first k) hab
  · change second k a = second k b
    apply mul_left_cancel₀ (planeVariable_ne_zero k 0)
    simpa only [smul_eq_mul, map_mul, second_diagonalVariable] using congrArg (second k) hab

theorem diagonalVariable_mem_maximalIdeal :
    diagonalVariable k ∈ IsLocalRing.maximalIdeal (Ring k) := by
  rw [← IsLocalRing.ker_eq_maximalIdeal ((planeResidue k).comp (first k))
    ((planeResidue_surjective k).comp (first_surjective k))]
  change planeResidue k (first k (diagonalVariable k)) = 0
  rw [first_diagonalVariable, planeResidue_variable]

theorem socleClass_ne_zero : socleClass k ≠ 0 := by
  intro hz
  have hm : pairVariable k 0 ∈ principalSubmodule k :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  rw [principalSubmodule, Ideal.ofList_singleton, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hm
  obtain ⟨a, _, ha⟩ := hm
  have hfirst : first k a = 1 := by
    apply mul_left_cancel₀ (planeVariable_ne_zero k 0)
    simpa only [smul_eq_mul, map_mul, first_diagonalVariable, first_pairVariable_zero, mul_one] using
      congrArg (first k) ha
  have hsecond : second k a = 0 := by
    apply mul_left_cancel₀ (planeVariable_ne_zero k 0)
    simpa only [smul_eq_mul, map_mul, second_diagonalVariable, second_pairVariable_zero, mul_zero] using
      congrArg (second k) ha
  have h := a.property
  change planeResidue k (first k a) = planeResidue k (second k a) at h
  rw [hfirst, hsecond, map_one, map_zero] at h
  exact one_ne_zero h

theorem maximalIdeal_smul_socleClass (a : Ring k)
    (ha : a ∈ IsLocalRing.maximalIdeal (Ring k)) : a • socleClass k = 0 := by
  have ha0 : planeResidue k (first k a) = 0 := by
    rw [← IsLocalRing.ker_eq_maximalIdeal ((planeResidue k).comp (first k))
      ((planeResidue_surjective k).comp (first_surjective k))] at ha
    exact ha
  let b : Ring k := ⟨(first k a, 0), by simpa using ha0⟩
  have heq : a * pairVariable k 0 = diagonalVariable k * b := by
    apply Subtype.ext
    apply Prod.ext
    · change first k (a * pairVariable k 0) = first k (diagonalVariable k * b)
      rw [map_mul, map_mul, first_pairVariable_zero, first_diagonalVariable]
      change first k a * planeVariable k 0 = planeVariable k 0 * first k a
      exact mul_comm _ _
    · change second k (a * pairVariable k 0) = second k (diagonalVariable k * b)
      rw [map_mul, map_mul, second_pairVariable_zero, second_diagonalVariable]
      change second k a * 0 = planeVariable k 0 * 0
      simp
  change Submodule.Quotient.mk (a * pairVariable k 0) = (0 : PrincipalQuotient k)
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [principalSubmodule, Ideal.ofList_singleton, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨b, Submodule.mem_top, heq.symm⟩

instance principalQuotient_nontrivial : Nontrivial (PrincipalQuotient k) :=
  nontrivial_of_ne (socleClass k) 0 (socleClass_ne_zero k)

theorem quotient_depth_zero : Depth.depth (Ring k) (PrincipalQuotient k) = 0 := by
  apply (Depth.depth_zero_iff_socle_ne_bot (Ring k) (PrincipalQuotient k)).mpr
  intro hbot
  have hm : socleClass k ∈ Submodule.torsionBySet (Ring k) (PrincipalQuotient k)
      (IsLocalRing.maximalIdeal (Ring k) : Set (Ring k)) := by
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    exact maximalIdeal_smul_socleClass k a a.property
  rw [hbot, Submodule.mem_bot] at hm
  exact socleClass_ne_zero k hm

theorem singleton_regular : RingTheory.Sequence.IsRegular (Ring k) [diagonalVariable k] := by
  refine ⟨(RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mpr
    (diagonalVariable_regular k), ?_⟩
  exact (Submodule.Quotient.nontrivial_iff.mp (principalQuotient_nontrivial k)).symm

theorem depth_one : Depth.depth (Ring k) (Ring k) = 1 := by
  have hproper : IsLocalRing.maximalIdeal (Ring k) •
      (⊤ : Submodule (Ring k) (Ring k)) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson _)).symm
  have hmem : ∀ a ∈ [diagonalVariable k], a ∈ IsLocalRing.maximalIdeal (Ring k) := by
    simpa using diagonalVariable_mem_maximalIdeal k
  have hdrop := Depth.grade_quotient_regular (Ring k)
    (IsLocalRing.maximalIdeal (Ring k)) hproper [diagonalVariable k]
    (singleton_regular k) hmem
  have hzero : Depth.depth (Ring k) (Ring k) - 1 = 0 := by
    simpa [Depth.depth, principalSubmodule] using hdrop.symm.trans (quotient_depth_zero k)
  apply le_antisymm
  · exact tsub_eq_zero_iff_le.mp hzero
  · rw [Depth.depth, Depth.grade_of_smul_ne_top _ _ hproper]
    exact le_sSup ⟨[diagonalVariable k], singleton_regular k, hmem, by simp⟩

/-- The closed-point instance of a Serre condition on a local ring. -/
theorem serreCondition_local_bound {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (n : ℕ) (hs : AdvCommAlg.CohenMacaulay.RingSerreCondition R n) :
    min (n : WithBot ℕ∞) (ringKrullDim R) ≤
      (AdvCommAlg.Depth.depth R R : WithBot ℕ∞) := by
  let p := IsLocalRing.closedPoint R
  let S := Localization.AtPrime p.asIdeal
  let N := LocalizedModule.AtPrime p.asIdeal R
  let e := IsLocalization.atUnits R p.asIdeal.primeCompl (S := S)
    (fun a ha => IsLocalRing.notMem_maximalIdeal.mp ha)
  have : Module.Finite R S := Module.Finite.equiv e.toLinearEquiv
  let eN : N ≃ₗ[R] S := IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl R) (Algebra.linearMap R S)
  let eNS : N ≃ₗ[S] S := eN.extendScalarsOfIsLocalization p.asIdeal.primeCompl S
  have hp : p ∈ Module.support R R := IsLocalRing.closedPoint_mem_support R R
  have h := hs p hp
  have hdim : Module.supportDim S N = ringKrullDim R := by
    rw [Module.supportDim_eq_of_equiv eNS, Module.supportDim_self_eq_ringKrullDim]
    exact e.toRingEquiv.ringKrullDim.symm
  have hdepth : IsLocalRing.depth (ModuleCat.of S N) = AdvCommAlg.Depth.depth R R := by
    rw [IsLocalRing.depth_eq_of_linearEquiv eNS]
    rw [← AdvCommAlg.Depth.depth_eq_libraryDepth]
    change AdvCommAlg.Depth.grade (IsLocalRing.maximalIdeal S) S = _
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (algebraMap R S) e.surjective]
    rw [AdvCommAlg.Depth.grade_map_of_surjective S e.surjective]
    rw [AdvCommAlg.Depth.grade_eq_idealDepth _ (ModuleCat.of R S)]
    rw [Ideal.depth_eq_of_linearEquiv (IsLocalRing.maximalIdeal R) e.toLinearEquiv.symm]
    exact (AdvCommAlg.Depth.depth_eq_libraryDepth (ModuleCat.of R R)).symm
  change min (n : WithBot ℕ∞) (Module.supportDim S N) ≤
    (IsLocalRing.depth (ModuleCat.of S N) : WithBot ℕ∞) at h
  rwa [hdim, hdepth] at h

/-- Dimension two and depth one violate the closed-point `(S₂)` inequality. -/
theorem not_serreCondition_two [IsNoetherianRing (Ring k)] :
    ¬ CohenMacaulay.RingSerreCondition (Ring k) 2 := by
  intro hs
  have h := serreCondition_local_bound 2 hs
  rw [dimension k, depth_one k] at h
  norm_num at h

/-- The concrete Noetherian local example has dimension two and depth one,
satisfies `(R₁)`, and fails `(S₂)`. No extra hypotheses on the field are needed. -/
theorem counterexample :
    ∃ hN : IsNoetherianRing (Ring k),
      ringKrullDim (Ring k) = 2 ∧ Depth.depth (Ring k) (Ring k) = 1 ∧
      @RegularInCodimension (Ring k) _ hN 1 ∧
        ¬ @CohenMacaulay.RingSerreCondition (Ring k) _ hN 2 := by
  exact ⟨ring_isNoetherianRing k, dimension k, depth_one k,
    regularInCodimensionOne k, not_serreCondition_two k⟩

end AdvCommAlg.Normality.FiberProduct
