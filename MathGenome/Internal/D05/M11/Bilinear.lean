import MathGenome.Internal.D05.M03.LinearMap
import MathGenome.Internal.Specs.D05.M11.Bilinear

/-! K05.11.bilinear: canonical pairings, pointwise operations and coordinates. -/

namespace D05.M11.Bilinear

open Module
open scoped BigOperators

/-- A scalar pairing is a linear map into the canonical space of linear functionals. -/
abbrev bilinearPairing (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] := V →ₗ[K] W →ₗ[K] K

/-- Bilinear forms are pairings with equal domains. -/
abbrev bilinearForm (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  LinearMap.BilinForm K V

theorem pairing_iff_axioms : Specs.D05.M11.Bilinear.pairing_iff_axioms := by
  intro K V W _ _ _ _ _ b
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x x' y
      simpa only [hB] using B.map_add₂ x x' y
    · intro a x y
      simpa only [hB, smul_eq_mul] using B.map_smul₂ a x y
    · intro x y y'
      simpa only [hB] using (B x).map_add y y'
    · intro a x y
      simpa only [hB, smul_eq_mul] using (B x).map_smul a y
  · rintro ⟨hadd₁, hsmul₁, hadd₂, hsmul₂⟩
    exact ⟨LinearMap.mk₂ K b hadd₁ hsmul₁ hadd₂ hsmul₂, fun _ _ => rfl⟩

theorem pointwise_operations : Specs.D05.M11.Bilinear.pointwise_operations := by
  intro K V W _ _ _ _ _ B C a x y
  exact ⟨rfl, rfl, rfl⟩

theorem finite_expansion : Specs.D05.M11.Bilinear.finite_expansion := by
  intro K V W I J _ _ _ _ _ B s t x y e f
  rw [B.map_sum₂]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [B.map_smul₂]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem basis_expansion : Specs.D05.M11.Bilinear.basis_expansion := by
  intro K V W I J _ _ _ _ _ _ _ e f B x y
  calc
    B x y = B (∑ a, e.repr x a • e a) (∑ b, f.repr y b • f b) := by
      rw [e.sum_repr, f.sum_repr]
    _ = ∑ a, ∑ b, e.repr x a * f.repr y b * B (e a) (f b) :=
      finite_expansion B Finset.univ Finset.univ (e.repr x) (f.repr y) e f

theorem basis_ext : Specs.D05.M11.Bilinear.basis_ext := by
  intro K V W I J _ _ _ _ _ _ _ e f B C h
  exact LinearMap.ext_basis e f h

/-- Two successive basis extensions construct the pairing for any array.
Each extension is linear by construction, not by a dimension argument. -/
noncomputable def coordinatePairing {K V W I J : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : Basis I K V) (f : Basis J K W) (A : Matrix I J K) :
    V →ₗ[K] W →ₗ[K] K :=
  e.constr K (fun a => f.constr K (fun b => A a b))

theorem coordinatePairing_basis : Specs.D05.M11.Bilinear.coordinatePairing_basis := by
  intro K V W I J _ _ _ _ _ _ _ e f A a b
  change (e.constr K (fun a => f.constr K (fun b => A a b))) (e a) (f b) = A a b
  rw [Basis.constr_basis, Basis.constr_basis]

theorem coordinatePairing_apply : Specs.D05.M11.Bilinear.coordinatePairing_apply := by
  intro K V W I J _ _ _ _ _ _ _ e f A x y
  change coordinatePairing e f A x y = _
  rw [basis_expansion e f (coordinatePairing e f A) x y]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  rw [show coordinatePairing e f A (e a) (f b) = A a b from
    coordinatePairing_basis e f A a b]

theorem exists_unique_pairing : Specs.D05.M11.Bilinear.exists_unique_pairing := by
  intro K V W I J _ _ _ _ _ _ _ e f A
  refine ⟨coordinatePairing e f A, ?_, ?_⟩
  · exact coordinatePairing_basis e f A
  · intro B hB
    apply basis_ext e f
    intro a b
    rw [hB]
    exact (coordinatePairing_basis e f A a b).symm

end D05.M11.Bilinear
