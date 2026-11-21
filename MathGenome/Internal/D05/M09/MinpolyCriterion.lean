import MathGenome.Internal.Specs.D05.M09.MinpolyCriterion
import MathGenome.Internal.D05.M08.Minpoly
import MathGenome.Internal.D05.M08.Primary
import MathGenome.Internal.D05.M09.Diagonalizable
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite

/-! K05.09.minpoly_criterion: distinct linear factors over the original field. -/

noncomputable section

namespace D05.M09.MinpolyCriterion

open Polynomial

theorem annihilates_iff_vanishes_on_eigenbasis :
    Specs.D05.M09.MinpolyCriterion.annihilates_iff_vanishes_on_eigenbasis := by
  intro K V _ _ _ n b T μ h p
  constructor
  · intro hp i
    have hz : p.eval (μ i) • b i = 0 := by
      rw [← Module.End.aeval_apply_of_mem_apply_eq_smul (h i), hp]
      rfl
    exact (smul_eq_zero.mp hz).resolve_right (b.ne_zero i)
  · intro hp
    apply b.ext
    intro i
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul (h i), hp i, zero_smul]
    rfl

/-- Deduplicate the eigenvalue list. Its product annihilates `T`, while each
of its relatively prime factors divides every annihilator. Monicity then
identifies that product with the minimal polynomial. -/
theorem minpoly_eq_product_of_eigenbasis {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V)
    (μ : Fin n → K) (h : ∀ i, T (b i) = μ i • b i) :
    ∃ s : Finset K, minpoly K T = ∏ a ∈ s, (X - C a) := by
  classical
  let s := Finset.univ.image μ
  let q : Polynomial K := ∏ a ∈ s, (X - C a)
  have hq : aeval T q = 0 := by
    apply (annihilates_iff_vanishes_on_eigenbasis b T μ h q).mpr
    intro i
    apply (dvd_iff_isRoot.mp ?_)
    exact Finset.dvd_prod_of_mem (fun a => X - C a)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hmq : minpoly K T ∣ q := minpoly.dvd K T hq
  have hqm : q ∣ minpoly K T := by
    apply Finset.prod_dvd_of_coprime
      (fun a _ c _ hac => pairwise_coprime_X_sub_C Function.injective_id hac)
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    apply dvd_iff_isRoot.mpr
    exact (annihilates_iff_vanishes_on_eigenbasis b T μ h (minpoly K T)).mp
      (minpoly.aeval K T) i
  exact ⟨s, eq_of_monic_of_associated (M08.Minpoly.monic T)
    (monic_prod_X_sub_C id s) (associated_of_dvd_dvd hmq hqm)⟩

/-- Kernel expansions for the distinct linear factors span a set of
eigenvectors. Extract a basis from that set and reindex it by `Fin n`. -/
theorem eigenbasis_of_minpoly_eq_product {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : Module.End K V) (s : Finset K)
    (hm : minpoly K T = ∏ a ∈ s, (X - C a)) :
    Diagonalizable.diagonalizable K V T := by
  classical
  let f : s → Polynomial K := fun a => X - C (a : K)
  have hc : Pairwise (fun i j => IsCoprime (f i) (f j)) :=
    pairwise_coprime_X_sub_C Subtype.coe_injective
  have hz : aeval T (∏ i, f i) = 0 := by
    rw [show (∏ i, f i) = ∏ a ∈ s, (X - C a) by
      exact Finset.prod_coe_sort s (fun a => X - C a)]
    rw [← hm]
    exact minpoly.aeval K T
  obtain ⟨_, hU, _⟩ := M08.Primary.coprime_kernel_decomposition T f hc hz
  let S : Set V := {v | ∃ a ∈ s, T v = a • v}
  have hspan : ⊤ ≤ Submodule.span K S := by
    intro v _
    obtain ⟨c, hc, _⟩ := hU v
    rw [← hc]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.subset_span
    refine ⟨i.val, i.property, ?_⟩
    have hi := LinearMap.mem_ker.mp (c i).property
    simpa [f, sub_eq_zero, Module.algebraMap_end_apply] using hi
  let b := Module.Basis.ofSpan hspan
  let I := (LinearIndepOn.extend (linearIndepOn_empty K id) (Set.empty_subset S))
  have : Finite I := b.linearIndependent.finite
  let _ : Fintype I := Fintype.ofFinite I
  have hb : ∀ i, ∃ a : K, T (b i) = a • b i := by
    intro i
    obtain ⟨a, _, ha⟩ := Module.Basis.ofSpan_subset hspan ⟨i, rfl⟩
    exact ⟨a, ha⟩
  choose μ hμ using hb
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, b.reindex e, μ ∘ e.symm, ?_⟩
  intro i
  simpa using hμ (e.symm i)

theorem diagonalizable_iff_distinct_linear_factors :
    Specs.D05.M09.MinpolyCriterion.diagonalizable_iff_distinct_linear_factors := by
  intro K V _ _ _ _ T
  constructor
  · rintro ⟨n, b, μ, h⟩
    exact minpoly_eq_product_of_eigenbasis b T μ h
  · rintro ⟨s, hs⟩
    exact eigenbasis_of_minpoly_eq_product T s hs

theorem empty_product_iff_zero_space :
    Specs.D05.M09.MinpolyCriterion.empty_product_iff_zero_space := by
  intro K V _ _ _ _ T
  simpa using M08.Primary.minimalPolynomial_eq_one_iff_zero T

end D05.M09.MinpolyCriterion
