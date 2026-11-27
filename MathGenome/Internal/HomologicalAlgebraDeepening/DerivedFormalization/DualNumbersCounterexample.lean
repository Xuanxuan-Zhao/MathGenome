import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainModels
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DualNumbersCounterexample

/-! A bi-infinite acyclic complex of free modules over the dual numbers. -/

namespace DerivedFormalization

open CategoryTheory
open HomologicalComplex (ιTensorObj)
open scoped TensorProduct
open TrivSqZeroExt (fst snd inl)

universe u

variable (k : Type u) [Field k]

local notation "R" => DualNumber k
local notation "ε" => (DualNumber.eps : R)

/-- The complex with a copy of the dual numbers in every degree and differential
multiplication by the square-zero generator. -/
abbrev dualNumbersComplex : Comp.{u} R :=
  Specs.DerivedFormalization.DualNumbersCounterexample.complexValue k

local notation "A" => dualNumbersComplex k

private theorem d_apply {i j : ℤ} (h : i + 1 = j) (x : R) :
    (A).d i j x = ε * x := by
  change (if i + 1 = j then ModuleCat.ofHom (LinearMap.mulLeft R ε) else 0) x = _
  rw [ite_eq_left h]
  rfl

private theorem exactAt_iff_exists (C : Comp.{u} R) (n : ℤ) :
    C.ExactAt n ↔ ∀ x : C.X n, C.d n (n + 1) x = 0 →
      ∃ y : C.X (n - 1), C.d (n - 1) n y = x := by
  have hp : (ComplexShape.up ℤ).Rel (n - 1) n := by change n - 1 + 1 = n; omega
  rw [C.exactAt_iff' (n - 1) n (n + 1) ((ComplexShape.up ℤ).prev_eq' hp)
    ((ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)),
    ShortComplex.moduleCat_exact_iff]
  rfl

theorem dualNumbersComplex_acyclic : (A).Acyclic := by
  intro n
  apply (exactAt_iff_exists k A n).2
  intro x hx
  rw [d_apply k rfl] at hx
  have hfst : fst x = 0 := by
    simpa using congrArg snd hx
  refine ⟨inl (snd x), ?_⟩
  rw [d_apply k (by omega : n - 1 + 1 = n)]
  apply TrivSqZeroExt.ext
  · simp [hfst]
  · simp

theorem dualNumbersComplex_termwiseFree (n : ℤ) : Module.Free R ((A).X n) :=
  inferInstanceAs (Module.Free R R)

theorem dualNumbersComplex_not_kProjective : ¬ IsKProjective A := by
  intro h
  let : IsKProjective A := h
  obtain ⟨H⟩ := CochainComplex.IsKProjective.nonempty_homotopy_zero
    (𝟙 A) (dualNumbersComplex_acyclic k)
  have eq := H.comm (0 : ℤ)
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 from rfl),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by decide)] at eq
  have hx := ConcreteCategory.congr_hom eq (1 : R)
  change (1 : R) = H.hom 1 0 ((A).d 0 1 1) + (A).d (-1) 0 (H.hom 0 (-1) 1) + 0 at hx
  rw [d_apply k (by decide : (0 : ℤ) + 1 = 1), mul_one,
    d_apply k (by decide : (-1 : ℤ) + 1 = 0)] at hx
  have hh : H.hom 1 0 ε = ε * H.hom 1 0 1 := by
    simpa using (H.hom 1 0).hom.map_smul ε (1 : R)
  rw [hh] at hx
  simpa using congrArg fst hx


open MonoidalCategory
open HomologicalComplex (mapBifunctorDesc ι_mapBifunctorDesc)

local notation "T" => tensorComplex A A

private def weight (i : ℤ) : ℤˣ := ((i + 1) / 2).negOnePow

private theorem weight_succ (i : ℤ) : weight (i + 1) = -(i.negOnePow * weight i) := by
  by_cases h : Even i
  · obtain ⟨j, hj⟩ := h
    have h₁ : (i + 1) / 2 = j := by omega
    have h₂ : (i + 1 + 1) / 2 = j + 1 := by omega
    simp only [weight, h₁, h₂, Int.negOnePow_succ, Int.negOnePow_even i ⟨j, hj⟩, one_mul]
  · have h' : Odd i := Int.not_even_iff_odd.mp h
    obtain ⟨j, hj⟩ := h'
    have h₁ : (i + 1) / 2 = j + 1 := by omega
    have h₂ : (i + 1 + 1) / 2 = j + 1 := by omega
    simp only [weight, h₁, h₂, Int.negOnePow_odd i ⟨j, hj⟩, neg_mul, one_mul, neg_neg]

/-- Multiplication on each summand with signs chosen to cancel the two parts
of the total tensor differential. -/
private noncomputable def weightedSum (n : ℤ) : (T).X n ⟶ ModuleCat.of R R :=
  mapBifunctorDesc (K₁ := A) (K₂ := A) (F := curriedTensor (ModuleCat R))
    (c := ComplexShape.up ℤ) (j := n) fun i _ _ =>
      weight i • ModuleCat.ofHom (TensorProduct.lid R R).toLinearMap

private theorem weightedSum_ι {i j n : ℤ} (h : i + j = n) (x y : R) :
    weightedSum k n (ιTensorObj A A i j n h (x ⊗ₜ[R] y)) = weight i • (x * y) := by
  have eq := ι_mapBifunctorDesc (K₁ := A) (K₂ := A) (F := curriedTensor (ModuleCat R))
    (c := ComplexShape.up ℤ) (j := n)
    (fun a _ _ => weight a • ModuleCat.ofHom (TensorProduct.lid R R).toLinearMap) i j h
  exact ConcreteCategory.congr_hom eq (x ⊗ₜ[R] y)

private theorem weightedSum_d (n : ℤ) : (T).d n (n + 1) ≫ weightedSum k (n + 1) = 0 := by
  apply HomologicalComplex.mapBifunctor.hom_ext (K₁ := A) (K₂ := A)
    (F := curriedTensor (ModuleCat R)) (c := ComplexShape.up ℤ)
  intro i j hij
  change i + j = n at hij
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  change weightedSum k (n + 1)
    ((T).d n (n + 1) (ιTensorObj A A i j n hij (x ⊗ₜ[R] y))) = 0
  rw [tensor_d_apply i j n (n + 1) hij rfl]
  change (weightedSum k (n + 1)).hom (_ + i.negOnePow • _) = 0
  rw [map_add, Units.smul_def, map_zsmul, ← Units.smul_def]
  change weightedSum k (n + 1) _ + i.negOnePow • weightedSum k (n + 1) _ = 0
  rw [weightedSum_ι, weightedSum_ι, d_apply k rfl, d_apply k rfl,
    weight_succ, Units.neg_smul, smul_smul]
  have hmul : (ε * x) * y = x * (ε * y) := by rw [mul_comm ε x, mul_assoc]
  rw [hmul, neg_add_cancel]

private theorem eps_ne_zero : ε ≠ 0 := by
  intro h
  simpa using congrArg snd h

theorem dualNumbersTensor_not_exactAt (n : ℤ) : ¬ (T).ExactAt n := by
  intro hex
  let z : (T).X n := ιTensorObj A A 0 n n (zero_add n) (ε ⊗ₜ[R] (1 : R))
  have hzz : ε ⊗ₜ[R] ε = 0 := by
    have h := TensorProduct.smul_tmul_smul ε ε (1 : R) (1 : R)
    simpa only [smul_eq_mul, mul_one, DualNumber.eps_mul_eps, TensorProduct.zero_smul] using h
  have hz : (T).d n (n + 1) z = 0 := by
    dsimp only [z]
    rw [tensor_d_apply 0 n n (n + 1) (zero_add n) rfl, d_apply k rfl, d_apply k rfl,
      DualNumber.eps_mul_eps, mul_one, hzz]
    simp
  obtain ⟨y, hy⟩ := (exactAt_iff_exists k T n).1 hex z hz
  have eq := weightedSum_d k (n - 1)
  rw [show n - 1 + 1 = n by omega] at eq
  have h := ConcreteCategory.congr_hom eq y
  change weightedSum k n ((T).d (n - 1) n y) = 0 at h
  rw [hy] at h
  apply eps_ne_zero k
  dsimp only [z] at h
  rw [weightedSum_ι] at h
  simpa [weight] using h

theorem dualNumbersComplex_not_kFlat : ¬ IsKFlat A := by
  intro h
  exact dualNumbersTensor_not_exactAt k 0 (h A (dualNumbersComplex_acyclic k) 0)

end DerivedFormalization
