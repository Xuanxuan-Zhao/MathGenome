import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Exterior.BaseChange
import Mathlib.LinearAlgebra.ExteriorAlgebra.BaseChange
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.GradedAlgebra.TensorProduct

open scoped TensorProduct

namespace Alg01SymmetricWitt.Exterior

universe u v w

open Specs.Alg01SymmetricWitt.Exterior

noncomputable section

theorem alternatingQuotient : AlternatingQuotient.{u, w} := by
  intro R _ M _ _ q
  let P := repeatedTensors R M q
  let p : (⨂[R] _ : Fin q, M) →ₗ[R] ⋀[R]^q M :=
    PiTensorProduct.lift (exteriorPower.ιMulti R q).toMultilinearMap
  have hp (x : Fin q → M) : p (PiTensorProduct.tprod R x) = exteriorPower.ιMulti R q x :=
    PiTensorProduct.lift.tprod _
  refine ⟨p, ?_, ?_, hp⟩
  · apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← exteriorPower.ιMulti_span R q M]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact ⟨_, hp x⟩
  · change LinearMap.ker p = P
    have hrel : P ≤ LinearMap.ker p := by
      apply Submodule.span_le.mpr
      rintro _ ⟨x, ⟨i, j, hij, heq⟩, rfl⟩
      change p (PiTensorProduct.tprod R x) = 0
      rw [hp]
      exact (exteriorPower.ιMulti R q).map_eq_zero_of_eq x heq hij
    let a : M [⋀^Fin q]→ₗ[R] ((⨂[R] _ : Fin q, M) ⧸ P) :=
      { P.mkQ.compMultilinearMap (PiTensorProduct.tprod R) with
        map_eq_zero_of_eq' := by
          intro x i j heq hij
          change P.mkQ (PiTensorProduct.tprod R x) = 0
          rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
          exact Submodule.subset_span ⟨x, ⟨i, j, hij, heq⟩, rfl⟩ }
    let f := exteriorPower.alternatingMapLinearEquiv a
    have hcomp : f.comp p = P.mkQ := by
      apply PiTensorProduct.ext
      ext x
      change f (p (PiTensorProduct.tprod R x)) = P.mkQ (PiTensorProduct.tprod R x)
      rw [hp, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
      rfl
    apply le_antisymm _ hrel
    intro t ht
    change t ∈ P
    rw [← Submodule.ker_mkQ P, ← hcomp, LinearMap.mem_ker, LinearMap.comp_apply,
      LinearMap.mem_ker.mp ht, map_zero]

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

private def includeExterior : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra S (S ⊗[R] M) :=
  ((ExteriorAlgebra.baseChangeEquiv R M S).toAlgHom.restrictScalars R).comp
    Algebra.TensorProduct.includeRight

private theorem includeExterior_wedge (q : ℕ) (x : Fin q → M) :
    includeExterior (S := S) (ExteriorAlgebra.ιMulti R q x) =
      ExteriorAlgebra.ιMulti S q (fun i => (1 : S) ⊗ₜ[R] x i) := by
  induction q with
  | zero => simp only [ExteriorAlgebra.ιMulti_zero_apply, map_one]
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul, ExteriorAlgebra.ιMulti_succ_apply, ih]
    have h (m : M) : includeExterior (S := S) (ExteriorAlgebra.ι R m) =
        ExteriorAlgebra.ι S ((1 : S) ⊗ₜ[R] m) :=
      ExteriorAlgebra.baseChangeEquiv_apply R M S 1 m
    rw [h]
    rfl

private theorem algebraComparison_wedge (q : ℕ) (s : S) (x : Fin q → M) :
    ExteriorAlgebra.baseChangeEquiv R M S (s ⊗ₜ[R] ExteriorAlgebra.ιMulti R q x) =
      s • ExteriorAlgebra.ιMulti S q (fun i => (1 : S) ⊗ₜ[R] x i) := by
  rw [← includeExterior_wedge]
  change ExteriorAlgebra.baseChangeEquiv R M S (s ⊗ₜ[R] ExteriorAlgebra.ιMulti R q x) =
    s • ExteriorAlgebra.baseChangeEquiv R M S ((1 : S) ⊗ₜ[R] ExteriorAlgebra.ιMulti R q x)
  rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem inverse_generator_mem (z : S ⊗[R] M) :
    (ExteriorAlgebra.baseChangeEquiv R M S).symm (ExteriorAlgebra.ι S z) ∈
      (⋀[R]^1 M).baseChange S := by
  induction z using TensorProduct.inductionOn with
  | tmul s m =>
    rw [ExteriorAlgebra.baseChangeEquiv_symm_apply]
    exact Submodule.tmul_mem_baseChange_of_mem s (by
      simpa only [ExteriorAlgebra.exteriorPower, pow_one] using
        LinearMap.mem_range_self (ExteriorAlgebra.ι R) m)
  | add a b ha hb =>
    simpa only [map_add] using Submodule.add_mem _ ha hb

private theorem inverse_mem (q : ℕ) {z : ExteriorAlgebra S (S ⊗[R] M)}
    (hz : z ∈ ⋀[S]^q (S ⊗[R] M)) :
    (ExteriorAlgebra.baseChangeEquiv R M S).symm z ∈ (⋀[R]^q M).baseChange S := by
  induction hz using Submodule.pow_induction_on_left' with
  | algebraMap s =>
    rw [AlgEquiv.commutes]
    exact SetLike.algebraMap_mem_graded (fun q => (⋀[R]^q M).baseChange S) s
  | add a b q ha hb iha ihb =>
    simpa only [map_add] using Submodule.add_mem _ iha ihb
  | mem_mul a ha q b hb ih =>
    obtain ⟨z, rfl⟩ := ha
    rw [map_mul]
    simpa only [Nat.add_comm 1 q] using
      SetLike.mul_mem_graded (A := fun q => (⋀[R]^q M).baseChange S)
        (inverse_generator_mem z) ih

private theorem map_degree (q : ℕ) :
    ((⋀[R]^q M).baseChange S).map (ExteriorAlgebra.baseChangeEquiv R M S).toLinearMap =
      ⋀[S]^q (S ⊗[R] M) := by
  apply le_antisymm
  · rw [← exteriorPower.ιMulti_span_fixedDegree R q M, Submodule.baseChange_span,
      LinearMap.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩
    change ExteriorAlgebra.baseChangeEquiv R M S
      ((1 : S) ⊗ₜ[R] ExteriorAlgebra.ιMulti R q x) ∈ _
    rw [algebraComparison_wedge, one_smul]
    exact ExteriorAlgebra.ιMulti_range S q (Set.mem_range_self _)
  · intro z hz
    exact ⟨_, inverse_mem q hz, (ExteriorAlgebra.baseChangeEquiv R M S).apply_symm_apply z⟩

/-- Restrict the exterior algebra comparison to degree q using the split grading. -/
def baseChangePower (q : ℕ) : S ⊗[R] (⋀[R]^q M) ≃ₗ[S] ⋀[S]^q (S ⊗[R] M) :=
  (LinearEquiv.ofBijective _ (DirectSum.toBaseChange_bijective (fun q => ⋀[R]^q M) q)).trans
    ((ExteriorAlgebra.baseChangeEquiv R M S).toLinearEquiv.ofSubmodules _ _ (map_degree q))

theorem baseChangePower_isComparison (q : ℕ) : IsComparison (baseChangePower (R := R) (S := S) (M := M) q) := by
  intro s x
  apply Subtype.ext
  rw [baseChangePower, LinearEquiv.trans_apply, LinearEquiv.ofSubmodules_apply,
    LinearEquiv.ofBijective_apply, Submodule.coe_toBaseChange_tmul]
  exact algebraComparison_wedge q s x

private theorem comparison_unique {q : ℕ}
    (e f : S ⊗[R] (⋀[R]^q M) ≃ₗ[S] ⋀[S]^q (S ⊗[R] M))
    (he : IsComparison e) (hf : IsComparison f) : e = f := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.restrictScalars_injective R
  apply TensorProduct.ext
  apply LinearMap.ext
  intro s
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  exact (he s x).trans (hf s x).symm

private theorem baseChangePower_zero (s : S) (x : ⋀[R]^0 M) :
    exteriorPower.zeroEquiv S (S ⊗[R] M) (baseChangePower 0 (s ⊗ₜ[R] x)) =
      s * algebraMap R S (exteriorPower.zeroEquiv R M x) := by
  let x₀ : Fin 0 → M := fun i => Fin.elim0 i
  let r := exteriorPower.zeroEquiv R M x
  have hx : x = r • exteriorPower.ιMulti R 0 x₀ := by
    apply (exteriorPower.zeroEquiv R M).injective
    rw [map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]
  change _ = s * algebraMap R S r
  have h := baseChangePower_isComparison (R := R) (S := S) (M := M) 0 (r • s) x₀
  rw [hx, TensorProduct.tmul_smul, TensorProduct.smul_tmul', h, map_smul, exteriorPower.zeroEquiv_ιMulti,
    smul_eq_mul, mul_one, Algebra.smul_def, mul_comm]

theorem exteriorPowerComparison : ExteriorPowerComparison.{u, v, w} := by
  intro R _ S _ φ M _ _
  let : Algebra R S := φ.toAlgebra
  refine ⟨baseChangePower, ⟨baseChangePower_isComparison, baseChangePower_zero⟩, ?_⟩
  intro e he
  funext q
  exact comparison_unique _ _ (he.1 q) (baseChangePower_isComparison q)

theorem koszulTermComparison : KoszulTermComparison.{u, v, w} := by
  intro R _ S _ φ E _ _ u
  let : Algebra R S := φ.toAlgebra
  refine ⟨?_, baseChangePower, baseChangePower_isComparison⟩
  intro s x
  change extendForm u (s ⊗ₜ[R] x) = s * algebraMap R S (u x)
  rw [extendForm, LinearMap.comp_apply, LinearMap.baseChange_tmul]
  change TensorProduct.AlgebraTensorModule.rid R S S (s ⊗ₜ[R] u x) = _
  rw [TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_comm]

end
end Alg01SymmetricWitt.Exterior
