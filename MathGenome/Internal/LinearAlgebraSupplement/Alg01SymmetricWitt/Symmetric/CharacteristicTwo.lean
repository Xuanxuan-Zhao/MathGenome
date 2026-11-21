import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Symmetric.MonomialBasis
import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.CharacteristicTwo
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

noncomputable section

namespace Alg01SymmetricWitt.Symmetric.CharacteristicTwo

open Module
open Alg01SymmetricWitt.Symmetric.Algebra (degree pureProductCoe)
open Alg01SymmetricWitt.Symmetric.Grading (degreeQuotientMap)

local notation "F₂" => ZMod 2

abbrev tensor := @Specs.Alg01SymmetricWitt.Symmetric.CharacteristicTwo.tensor
abbrev swapFactors := Specs.Alg01SymmetricWitt.Symmetric.CharacteristicTwo.swapFactors
abbrev fixedTensors := Specs.Alg01SymmetricWitt.Symmetric.CharacteristicTwo.fixedTensors
abbrev fixedQuotient := Specs.Alg01SymmetricWitt.Symmetric.CharacteristicTwo.fixedQuotient
abbrev fixedGenerators := @Specs.Alg01SymmetricWitt.Symmetric.CharacteristicTwo.fixedGenerators
abbrev symmetricPair := @Specs.Alg01SymmetricWitt.Symmetric.CharacteristicTwo.symmetricPair

variable {M : Type*} [AddCommGroup M] [Module F₂ M]

private theorem mem_fixedTensors (x : TensorPower F₂ 2 M) :
    x ∈ fixedTensors M ↔ swapFactors M x = x := by
  change (swapFactors M x - x = 0) ↔ _
  exact sub_eq_zero

private theorem swapFactors_tensor (b : Basis (Fin 2) F₂ M) (i j : Fin 2) :
    swapFactors M (tensor b i j) = tensor b j i := by
  unfold swapFactors tensor Specs.Alg01SymmetricWitt.Symmetric.CharacteristicTwo.swapFactors
    Specs.Alg01SymmetricWitt.Symmetric.CharacteristicTwo.tensor
  rw [PiTensorProduct.reindex_tprod]
  congr 1
  funext k
  fin_cases k <;> simp

private theorem fixedGenerators_mem (b : Basis (Fin 2) F₂ M) (i : Fin 3) :
    fixedGenerators b i ∈ fixedTensors M := by
  rw [mem_fixedTensors]
  fin_cases i <;>
    simp [fixedGenerators, Specs.Alg01SymmetricWitt.Symmetric.CharacteristicTwo.fixedGenerators,
      swapFactors_tensor, add_comm]

private def tensorBasis (b : Basis (Fin 2) F₂ M) :
    Basis (Fin 2 × Fin 2) F₂ (TensorPower F₂ 2 M) :=
  (Basis.piTensorProduct (fun _ : Fin 2 => b)).reindex (finTwoArrowEquiv (Fin 2))

private theorem tensorBasis_apply (b : Basis (Fin 2) F₂ M) (i j : Fin 2) :
    tensorBasis b (i, j) = tensor b i j := by
  rw [tensorBasis, Basis.reindex_apply, Basis.piTensorProduct_apply]
  congr 1
  funext k
  fin_cases k <;> rfl

private theorem coord_tensor (b : Basis (Fin 2) F₂ M) (i j a d : Fin 2) :
    (tensorBasis b).coord (i, j) (tensor b a d) = if (a, d) = (i, j) then 1 else 0 := by
  classical
  rw [← tensorBasis_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]

private theorem coord_swap (b : Basis (Fin 2) F₂ M) (i j : Fin 2) (x : TensorPower F₂ 2 M) :
    (tensorBasis b).coord (i, j) (swapFactors M x) = (tensorBasis b).coord (j, i) x := by
  change (((tensorBasis b).coord (i, j)).comp (swapFactors M).toLinearMap) x = _
  congr 1
  apply (tensorBasis b).ext
  rintro ⟨a, d⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, tensorBasis_apply, swapFactors_tensor,
    coord_tensor, Prod.mk.injEq, and_comm]

private def fixedVector (b : Basis (Fin 2) F₂ M) (i : Fin 3) : fixedTensors M :=
  ⟨fixedGenerators b i, fixedGenerators_mem b i⟩

private theorem fixedVector_independent (b : Basis (Fin 2) F₂ M) :
    LinearIndependent F₂ (fixedVector b) := by
  apply LinearIndependent.of_comp (fixedTensors M).subtype
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rw [Fin.sum_univ_three] at hc
  change c 0 • tensor b 0 0 + c 1 • tensor b 1 1 +
    c 2 • (tensor b 0 1 + tensor b 1 0) = 0 at hc
  have h₀ := congrArg ((tensorBasis b).coord (0, 0)) hc
  have h₁ := congrArg ((tensorBasis b).coord (1, 1)) hc
  have h₂ := congrArg ((tensorBasis b).coord (0, 1)) hc
  simp [-Basis.coord_apply, coord_tensor] at h₀ h₁ h₂
  intro i
  fin_cases i <;> assumption

private theorem fixedVector_spans (b : Basis (Fin 2) F₂ M) :
    ⊤ ≤ Submodule.span F₂ (Set.range (fixedVector b)) := by
  intro x _
  let c := (tensorBasis b).coord
  have hfix := (mem_fixedTensors (x : TensorPower F₂ 2 M)).mp x.property
  have hmixed : c (1, 0) x = c (0, 1) x := by
    rw [← coord_swap b 0 1, hfix]
  have hx : x = c (0, 0) x • fixedVector b 0 + c (1, 1) x • fixedVector b 1 +
      c (0, 1) x • fixedVector b 2 := by
    apply Subtype.ext
    apply (tensorBasis b).ext_elem
    rintro ⟨i, j⟩
    change c (i, j) (x : TensorPower F₂ 2 M) =
      c (i, j) (c (0, 0) x • tensor b 0 0 + c (1, 1) x • tensor b 1 1 +
        c (0, 1) x • (tensor b 0 1 + tensor b 1 0))
    fin_cases i <;> fin_cases j <;> simp [-Basis.coord_apply, c, coord_tensor, hmixed]
  rw [hx]
  exact add_mem (add_mem
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩))

/-- The two squares and the mixed-tensor sum form a basis of the fixed space. -/
theorem fixedBasis (b : Basis (Fin 2) F₂ M) :
    ∃ c : Basis (Fin 3) F₂ (fixedTensors M),
      ∀ i, (c i : TensorPower F₂ 2 M) = fixedGenerators b i := by
  refine ⟨Basis.mk (fixedVector_independent b) (fixedVector_spans b), fun i => ?_⟩
  rw [Basis.mk_apply]
  rfl

/-- The canonical quotient sends elementary tensors to products of their factors. -/
theorem quotientOnPairs (b : Basis (Fin 2) F₂ M) (i j : Fin 2) :
    degreeQuotientMap F₂ M 2 (tensor b i j) = symmetricPair b i j ∧
      (symmetricPair b i j : SymmetricAlgebra F₂ M) =
        SymmetricAlgebra.ι F₂ M (b i) * SymmetricAlgebra.ι F₂ M (b j) := by
  refine ⟨rfl, ?_⟩
  change (Algebra.pureProduct F₂ M 2 ![b i, b j] : SymmetricAlgebra F₂ M) = _
  simpa [Fin.prod_univ_two] using pureProductCoe F₂ M 2 (![b i, b j])

private theorem symmetricPair_comm (b : Basis (Fin 2) F₂ M) (i j : Fin 2) :
    symmetricPair b i j = symmetricPair b j i := by
  apply Subtype.ext
  rw [(quotientOnPairs b i j).2, (quotientOnPairs b j i).2, mul_comm]

private theorem quotient_mixed (b : Basis (Fin 2) F₂ M) :
    degreeQuotientMap F₂ M 2 (tensor b 0 1 + tensor b 1 0) =
      (2 : F₂) • symmetricPair b 0 1 := by
  rw [map_add, (quotientOnPairs b 0 1).1, (quotientOnPairs b 1 0).1, symmetricPair_comm b 1 0,
    two_smul]

private theorem two_eq_zero : (2 : F₂) = 0 := by decide

/-- The nonzero mixed-tensor sum maps to twice the mixed class, which vanishes. -/
theorem quotientOnMixedTensor (b : Basis (Fin 2) F₂ M) :
    ∃ t : fixedTensors M,
      (t : TensorPower F₂ 2 M) = tensor b 0 1 + tensor b 1 0 ∧
      t ≠ 0 ∧ fixedQuotient M t = (2 : F₂) • symmetricPair b 0 1 ∧ fixedQuotient M t = 0 := by
  let t := fixedVector b 2
  have hq : fixedQuotient M t = (2 : F₂) • symmetricPair b 0 1 := quotient_mixed b
  refine ⟨t, rfl, ?_, hq, by rw [hq, two_eq_zero, zero_smul]⟩
  intro h
  have hcoord := congrArg (fun x : fixedTensors M => (tensorBasis b).coord (0, 1) x) h
  change (tensorBasis b).coord (0, 1) (tensor b 0 1 + tensor b 1 0) =
    (tensorBasis b).coord (0, 1) 0 at hcoord
  simp [-Basis.coord_apply, coord_tensor] at hcoord

/-- The image of the fixed subspace is the span of the two square monomials. -/
theorem quotientRange (b : Basis (Fin 2) F₂ M) :
    LinearMap.range (fixedQuotient M) =
      Submodule.span F₂ {symmetricPair b 0 0, symmetricPair b 1 1} := by
  obtain ⟨c, hc⟩ := fixedBasis b
  have h (i : Fin 3) :
      fixedQuotient M (c i) = ![symmetricPair b 0 0, symmetricPair b 1 1, 0] i := by
    change degreeQuotientMap F₂ M 2 (c i : TensorPower F₂ 2 M) = _
    rw [hc]
    fin_cases i
    · exact (quotientOnPairs b 0 0).1
    · exact (quotientOnPairs b 1 1).1
    · change degreeQuotientMap F₂ M 2 (tensor b 0 1 + tensor b 1 0) = 0
      rw [quotient_mixed, two_eq_zero, zero_smul]
  rw [LinearMap.range_eq_map, ← c.span_eq, Submodule.map_span, ← Set.range_comp]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change fixedQuotient M (c i) ∈ _
    rw [h]
    fin_cases i
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
    · exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Submodule.subset_span ⟨0, h 0⟩
    · exact Submodule.subset_span ⟨1, h 1⟩

private def pairExponent (i j : Fin 2) : MonomialBasis.Exponent 2 2 :=
  ⟨Finsupp.single i 1 + Finsupp.single j 1, by
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two, Finsupp.single_apply]⟩

/-- The mixed monomial is nonzero and is missing from the image of fixed tensors. -/
theorem mixedClass (b : Basis (Fin 2) F₂ M) :
    symmetricPair b 0 1 ≠ 0 ∧ symmetricPair b 0 1 ∉ LinearMap.range (fixedQuotient M) ∧
      ∃ c : Basis (MonomialBasis.Exponent 2 2) F₂ (degree F₂ M 2),
        (∀ a : MonomialBasis.Exponent 2 2,
          (c a : SymmetricAlgebra F₂ M) = ∏ i, SymmetricAlgebra.ι F₂ M (b i) ^ a.val i) ∧
          ∃ a : MonomialBasis.Exponent 2 2, a.val 0 = 1 ∧ a.val 1 = 1 ∧ c a = symmetricPair b 0 1 := by
  obtain ⟨c, hc⟩ := MonomialBasis.exists_monomialBasis b 2
  have hpair (i j : Fin 2) : c (pairExponent i j) = symmetricPair b i j := by
    apply Subtype.ext
    rw [(hc (pairExponent i j)).1, (quotientOnPairs b i j).2]
    fin_cases i <;> fin_cases j <;>
      simp [Fin.prod_univ_two, pairExponent, Finsupp.single_apply, pow_two, mul_comm]
  let a := pairExponent 0 1
  have ha : a.val 0 = 1 ∧ a.val 1 = 1 := by simp [a, pairExponent]
  refine ⟨hpair 0 1 ▸ c.ne_zero _, ?_, c, fun d => (hc d).1, a, ha.1, ha.2, hpair 0 1⟩
  have h₀ : pairExponent 0 0 ≠ a := by
    intro h
    have h₀ := congrArg (fun x : MonomialBasis.Exponent 2 2 => x.val 0) h
    simp [a, pairExponent] at h₀
  have h₁ : pairExponent 1 1 ≠ a := by
    intro h
    have h₁ := congrArg (fun x : MonomialBasis.Exponent 2 2 => x.val 0) h
    simp [a, pairExponent] at h₁
  have hspan : Submodule.span F₂ {symmetricPair b 0 0, symmetricPair b 1 1} ≤
      LinearMap.ker (c.coord a) := by
    apply Submodule.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · simp [← hpair 0 0, h₀]
    · simp [← hpair 1 1, h₁]
  rw [quotientRange b]
  intro h
  have hzero : c.coord a (symmetricPair b 0 1) = 0 := hspan h
  simp [← hpair 0 1, a] at hzero

/-- The canonical map from fixed tensors is neither injective nor surjective. -/
theorem quotientFailures (b : Basis (Fin 2) F₂ M) :
    ¬ Function.Injective (fixedQuotient M) ∧ ¬ Function.Surjective (fixedQuotient M) := by
  obtain ⟨t, _, ht, _, hq⟩ := quotientOnMixedTensor b
  refine ⟨fun hinj => ht (hinj (hq.trans (map_zero _).symm)), fun hsurj => ?_⟩
  exact (mixedClass b).2.1 (hsurj (symmetricPair b 0 1))

end Alg01SymmetricWitt.Symmetric.CharacteristicTwo
