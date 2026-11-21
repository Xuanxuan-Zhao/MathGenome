import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Degree
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.RingTheory.Polynomial.Resultant.Basic

namespace RM03.CSA

open scoped TensorProduct Polynomial
open Polynomial

universe u v w

section GenericMatrix

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
variable {n : ℕ}

private theorem resultant_derivative_ne_zero_iff (p : L[X]) (hp : p.Monic) :
    p.resultant p.derivative p.natDegree (p.natDegree - 1) ≠ 0 ↔ p.Separable := by
  have hle : p.derivative.natDegree ≤ p.natDegree - 1 :=
    natDegree_derivative_le p
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hle
  conv_lhs => rw [hm]
  rw [resultant_add_right_deg _ _ _ _ _ le_rfl, ← leadingCoeff, hp.leadingCoeff,
    one_pow, one_mul, ← isUnit_iff_ne_zero, isUnit_resultant_iff_isCoprime hp, separable_def]

/-- A basis of matrices over `L` has a `K`-linear combination with separable characteristic
polynomial when `K` is infinite. -/
private theorem exists_separable_charpoly [Infinite K] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι L (Matrix (Fin n) (Fin n) L)) :
    ∃ c : ι → K, (∑ i, algebraMap K L (c i) • b i).charpoly.Separable := by
  classical
  let M : Matrix (Fin n) (Fin n) (MvPolynomial ι L) :=
    ∑ i, (MvPolynomial.X i : MvPolynomial ι L) • (b i).map MvPolynomial.C
  let p := M.charpoly
  let r := p.resultant p.derivative n (n - 1)
  have specialize (c : ι → L) :
      MvPolynomial.eval c r ≠ 0 ↔ (∑ i, c i • b i).charpoly.Separable := by
    let f := MvPolynomial.eval c
    have hM : M.map f = ∑ i, c i • b i := by
      ext a b'
      simp [M, f, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply]
    have hp : p.map f = (∑ i, c i • b i).charpoly := by
      rw [← hM, Matrix.charpoly_map]
    have hdeg : (∑ i, c i • b i).charpoly.natDegree = n := by simp
    rw [show MvPolynomial.eval c r = f (p.resultant p.derivative n (n - 1)) from rfl,
      ← resultant_map_map, ← derivative_map, hp]
    simpa only [hdeg] using
      (resultant_derivative_ne_zero_iff _ (Matrix.charpoly_monic (∑ i, c i • b i)))
  let : Infinite L := Infinite.of_injective (algebraMap K L) (RingHom.injective _)
  let d := Infinite.natEmbedding L
  let diag : Matrix (Fin n) (Fin n) L := Matrix.diagonal (fun i => d (i : ℕ))
  have hdiag : diag.charpoly.Separable := by
    rw [Matrix.charpoly_diagonal, separable_prod_X_sub_C_iff]
    exact d.injective.comp Fin.val_injective
  have hdEval : MvPolynomial.eval (fun i => b.repr diag i) r ≠ 0 := by
    apply (specialize _).2
    simpa only [b.sum_repr] using hdiag
  have hr : r ≠ 0 := by
    intro h
    exact hdEval (by rw [h, map_zero])
  obtain ⟨c, hc⟩ : ∃ c : ι → K, MvPolynomial.eval (fun i => algebraMap K L (c i)) r ≠ 0 := by
    by_contra! h
    apply hr
    refine MvPolynomial.funext_set (fun _ => Set.range (algebraMap K L))
      (fun _ => Set.infinite_range_of_injective (RingHom.injective (algebraMap K L))) ?_
    intro a ha
    have : ∀ i, ∃ x, algebraMap K L x = a i := fun i => ha i (Set.mem_univ i)
    choose c hc using this
    simpa only [hc, map_zero] using h c
  exact ⟨c, (specialize _).1 hc⟩

end GenericMatrix

section Minpoly

variable {k : Type u} [Field k] {L : Type w} [Field L] [Algebra k L]
variable {A : Type v} [Ring A] [Algebra k A]

private theorem minpoly_includeRight (x : A) (hx : IsIntegral k x) :
    minpoly L (Algebra.TensorProduct.includeRight (R := k) (A := L) x) =
      (minpoly k x).map (algebraMap k L) := by
  let j : A →ₐ[k] BaseChange k L A := Algebra.TensorProduct.includeRight
  change minpoly L (j x) = _
  refine minpoly.eq_of_linearIndependent L (j x) ((minpoly.monic hx).map _) ?_
    (minpoly k x).natDegree ?_ ?_
  · rw [aeval_map_algebraMap, aeval_algHom_apply j, minpoly.aeval, map_zero]
  · rw [degree_map_eq_of_injective (RingHom.injective _),
      degree_eq_natDegree (minpoly.ne_zero hx)]
  · convert Module.Flat.linearIndependent_one_tmul (S := L)
      (linearIndependent_pow (K := k) x) using 1
    funext i
    exact (map_pow j x (i : ℕ)).symm

private theorem minpoly_eq_charpoly_of_separable [IsAlgClosed L] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) L) (hM : M.charpoly.Separable) :
    minpoly L M = M.charpoly := by
  have hp : (minpoly L M).Monic := minpoly.monic (IsIntegral.of_finite L M)
  symm
  refine eq_of_monic_of_dvd_of_natDegree_le hp (Matrix.charpoly_monic M)
    (Matrix.minpoly_dvd_charpoly M) ?_
  have hdvd : M.charpoly ∣ minpoly L M := by
    apply (IsAlgClosed.dvd_iff_roots_le_roots hM.ne_zero hp.ne_zero).2
    apply (Multiset.le_iff_subset (nodup_roots hM)).2
    intro a ha
    rw [mem_roots hM.ne_zero] at ha
    rw [mem_roots hp.ne_zero]
    have he : Module.End.HasEigenvalue M.toLin' a :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (by rwa [Matrix.charpoly_toLin'])
    have hr := Module.End.isRoot_of_hasEigenvalue he
    change (minpoly L (Matrix.toLinAlgEquiv' M)).IsRoot a at hr
    rwa [minpoly.algEquiv_eq] at hr
  exact natDegree_le_of_dvd hdvd hp.ne_zero

end Minpoly

variable {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D]

private theorem exists_element_degree_separable [Infinite k] (hD : IsCentralDivision k D) :
    ∃ x : D, (minpoly k x).natDegree = degree k D ∧ IsSeparable k x := by
  let : FiniteDimensional k D := hD.2
  let L := AlgebraicClosure k
  obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure (isCentralSimple_of_isCentralDivision k D hD)
  let b := Module.finBasis k D
  let B := (b.baseChange L).map e.toLinearEquiv
  obtain ⟨c, hc⟩ := exists_separable_charpoly (K := k) B
  let x : D := ∑ i, c i • b i
  let j : D →ₐ[k] BaseChange k L D := Algebra.TensorProduct.includeRight
  have he : e (j x) = ∑ i, algebraMap k L (c i) • B i := by
    simp only [x, map_sum, map_smul, j, Algebra.TensorProduct.includeRight_apply, B,
      Module.Basis.map_apply, Module.Basis.baseChange_apply, AlgEquiv.toLinearEquiv_apply]
    congr 1
    funext i
    rw [← algebraMap_smul L (c i), map_smul]
  have hsep : (e (j x)).charpoly.Separable := by rwa [he]
  have hm : (minpoly k x).map (algebraMap k L) = (e (j x)).charpoly := by
    rw [← minpoly_includeRight x (IsIntegral.of_finite k x),
      ← minpoly.algEquiv_eq e (j x), minpoly_eq_charpoly_of_separable _ hsep]
  refine ⟨x, ?_, (separable_map (algebraMap k L)).mp (hm.symm ▸ hsep)⟩
  rw [← natDegree_map_eq_of_injective (RingHom.injective (algebraMap k L)), hm]
  simp

private theorem exists_separable_subfield_of_finite [Finite k] (hD : IsCentralDivision k D) :
    ∃ E : Subalgebra k D, IsField E ∧ Algebra.IsSeparable k E ∧
      Module.finrank k E = degree k D := by
  let : FiniteDimensional k D := hD.2
  let b := Module.finBasis k D
  let : Finite D := Finite.of_injective b.equivFun b.equivFun.injective
  let : Field D := littleWedderburn D
  have hs : Function.Surjective (algebraMap k D) := by
    intro x
    have hx : x ∈ Subalgebra.center k D := by
      change x ∈ Subring.center D
      exact Subring.mem_center_iff.mpr fun y => mul_comm y x
    change x ∈ Set.range (algebraMap k D)
    rwa [← ((isCentralDivision_iff k D).mp hD).2]
  let e : k ≃ₐ[k] D := AlgEquiv.ofBijective (Algebra.ofId k D)
    ⟨RingHom.injective (algebraMap k D), hs⟩
  have hdeg : degree k D = 1 := by
    rw [degree, ← e.toLinearEquiv.finrank_eq, Module.finrank_self]
    decide
  let f := Algebra.botEquiv k D
  exact ⟨⊥, f.toRingEquiv.toMulEquiv.isField (Field.toIsField k),
    AlgEquiv.Algebra.isSeparable f.symm,
    by rw [hdeg, f.toLinearEquiv.finrank_eq, Module.finrank_self]⟩

private theorem separable_adjoin_singleton (x : D) (h : IsSeparable k x)
    [FiniteDimensional k D] :
    IsField (Algebra.adjoin k ({x} : Set D)) ∧
      Algebra.IsSeparable k (Algebra.adjoin k ({x} : Set D)) ∧
      Module.finrank k (Algebra.adjoin k ({x} : Set D)) = (minpoly k x).natDegree := by
  let E := Algebra.adjoin k ({x} : Set D)
  let : CommRing E := Algebra.instCommRingAdjoinSingleton x
  let : IsDomain E := Function.Injective.isDomain E.val Subtype.val_injective
  let : Field E := fieldOfFiniteDimensional k E
  let y : E := ⟨x, Algebra.self_mem_adjoin_singleton k x⟩
  have hmin : minpoly k y = minpoly k x :=
    (minpoly.algHom_eq E.val Subtype.val_injective y).symm
  have hgen : IsSeparable k y := by
    change (minpoly k y).Separable
    rwa [hmin]
  have htop : Algebra.adjoin k ({y} : Set E) = ⊤ := by
    have hy : (((↑) : E → D) ⁻¹' ({x} : Set D)) = {y} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hz => Subtype.val_injective hz, fun hz => congrArg Subtype.val hz⟩
    rw [← hy]
    exact Algebra.adjoin_adjoin_coe_preimage
  let pb := PowerBasis.ofAdjoinEqTop hgen.isIntegral htop
  have ht : (⊤ : Subalgebra k E) ≤ (separableClosure k E).toSubalgebra := by
    rw [← htop, Algebra.adjoin_le_iff]
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact hgen
  refine ⟨Field.toIsField E, ⟨fun z => ?_⟩, ?_⟩
  · exact ht (show z ∈ (⊤ : Subalgebra k E) from trivial)
  · exact pb.finrank.trans (congrArg natDegree hmin)

/-- A central division algebra contains a separable subfield of degree equal to its degree. -/
theorem exists_separable_subfield (hD : IsCentralDivision k D) :
    ∃ E : Subalgebra k D, IsField E ∧ Algebra.IsSeparable k E ∧
      Module.finrank k E = degree k D := by
  rcases finite_or_infinite k with h | h
  · exact exists_separable_subfield_of_finite hD
  · let : FiniteDimensional k D := hD.2
    obtain ⟨x, hdeg, hsep⟩ := exists_element_degree_separable hD
    obtain ⟨hfield, hseparable, hdim⟩ := separable_adjoin_singleton x hsep
    exact ⟨_, hfield, hseparable, hdim.trans hdeg⟩

end RM03.CSA
