import MathGenome.Internal.Specs.D05.M10.AdditiveDecomposition
import MathGenome.Internal.D05.M08.Evaluation
import MathGenome.Internal.D05.M09.Diagonalizable
import MathGenome.Internal.D05.M10.GeneralizedDecomposition
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.FieldTheory.Separable

noncomputable section
namespace D05.M10.AdditiveDecomposition

open Polynomial Algebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Removing repeated linear factors of a split monic polynomial gives a
separable polynomial with a power divisible by the original polynomial. -/
theorem split_separable_power (m : Polynomial K) (hm : m.Monic) (hs : m.Splits) :
    ∃ (P : Polynomial K) (k : ℕ), P.Separable ∧ m ∣ P ^ k := by
  classical
  let s := m.roots.toFinset
  let P : Polynomial K := ∏ μ ∈ s, (X - C μ)
  refine ⟨P, m.natDegree, ?_, ?_⟩
  · exact separable_prod_X_sub_C_iff'.mpr (fun _ _ _ _ h => h)
  · have hfac : m = ∏ μ ∈ s, (X - C μ) ^ m.rootMultiplicity μ := by
      rw [Polynomial.prod_multiset_root_eq_finset_root.symm]
      exact hs.eq_prod_roots_of_monic hm
    calc
      m = ∏ μ ∈ s, (X - C μ) ^ m.rootMultiplicity μ := hfac
      _ ∣ ∏ μ ∈ s, (X - C μ) ^ m.natDegree := by
        apply Finset.prod_dvd_prod_of_dvd
        intro μ _
        apply pow_dvd_pow _
        simpa using (Polynomial.natDegree_le_of_dvd
          (Polynomial.pow_rootMultiplicity_dvd m μ) hm.ne_zero)
      _ = P ^ m.natDegree := Finset.prod_pow s _ _


/-- A scalar action on all generalized summands supplies a finite eigenbasis. -/
theorem diagonalizable_of_scalar_on_generalized (T D : Module.End K V)
    (hspan : (⨆ μ : K, T.genEigenspace μ (Module.finrank K V)) = ⊤)
    (hact : ∀ μ x, x ∈ T.genEigenspace μ (Module.finrank K V) → D x = μ • x) :
    Specs.D05.M09.Diagonalizable.diagonalizable_value K V D := by
  classical
  let U := fun μ : K => T.genEigenspace μ (Module.finrank K V)
  have hU : DirectSum.IsInternal U :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (T.independent_genEigenspace (Module.finrank K V)) hspan
  let ι := (μ : K) × Module.Free.ChooseBasisIndex K (U μ)
  let b : Module.Basis ι K V := hU.collectedBasis (fun μ => Module.Free.chooseBasis K (U μ))
  have := Module.Finite.finite_basis b
  let := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, b.reindex e, fun i => (e.symm i).1, ?_⟩
  intro i
  rw [Module.Basis.reindex_apply]
  exact hact _ _ (hU.collectedBasis_mem _ _)

/-- In a commuting diagonalizable–nilpotent pair, every eigenvector of the
first part lies in the corresponding generalized eigenspace of their sum. -/
theorem eigenvector_mem_generalized (T D N : Module.End K V)
    (hT : T = D + N) (hc : Commute D N) (hN : IsNilpotent N)
    (μ : K) (x : V) (hx : D x = μ • x) :
    x ∈ T.genEigenspace μ (Module.finrank K V) := by
  have heig (k : ℕ) : D ((N ^ k) x) = μ • ((N ^ k) x) := by
    calc
      _ = (N ^ k) (D x) := congrArg (fun A : Module.End K V => A x) (hc.pow_right k).eq
      _ = _ := by rw [hx, map_smul]
  have hpow (k : ℕ) : ((T - μ • 1) ^ k) x = (N ^ k) x := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
      simp only [hT, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.smul_apply, Module.End.one_apply, heig, add_sub_cancel_left]
  obtain ⟨r, hr⟩ := hN
  apply Module.End.mem_genEigenspace_nat.mpr
  apply Module.End.ker_pow_le_ker_pow_finrank (T - μ • 1) r
  change ((T - μ • 1) ^ r) x = 0
  rw [hpow, hr, LinearMap.zero_apply]

/-- The split-minimal-polynomial additive decomposition over the original
field, with polynomial formulas and uniqueness among all admissible pairs. -/
theorem decomposition : Specs.D05.M10.AdditiveDecomposition.decomposition := by
  intro K V _ _ _ _ T hs
  classical
  change (minpoly K T).Splits at hs
  obtain ⟨P, k, hsep, hdvd⟩ := split_separable_power (minpoly K T)
    (minpoly.monic (IsIntegral.isIntegral T)) hs
  obtain ⟨N, hNT, D, hDT, hN, hD, hT⟩ :=
    Module.End.exists_isNilpotent_isSemisimple_of_separable_of_dvd_pow hsep hdvd
  obtain ⟨p, hp⟩ := (Algebra.adjoin_singleton_eq_range_aeval K T ▸ hDT)
  obtain ⟨q, hq⟩ := (Algebra.adjoin_singleton_eq_range_aeval K T ▸ hNT)
  have hTD : Commute T D := Algebra.commute_of_mem_adjoin_self hDT
  have hact (μ : K) (x : V)
      (hx : x ∈ T.genEigenspace μ (Module.finrank K V)) : D x = μ • x := by
    apply Module.End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
      hx hTD hD.isFinitelySemisimple
    simpa only [hT, add_sub_cancel_right] using hN
  have hdiag := diagonalizable_of_scalar_on_generalized T D
    (GeneralizedDecomposition.iSup_generalized_eq_top T (minpoly K T)
      (minpoly.monic (IsIntegral.isIntegral T)) hs (minpoly.aeval K T)) hact
  have hDN : Commute D N := by
    rw [← hp, ← hq]
    exact D05.M08.Evaluation.polynomials_commute T p q
  refine ⟨D, N, ?_, hdiag, hN, hDN, ⟨p, hp⟩, ⟨q, hq⟩, ?_⟩
  · rw [add_comm]; exact hT
  · intro D' N' hT' hD' hN' hc'
    obtain ⟨n, b, μ, hb⟩ := hD'
    have heq : D' = D := by
      apply b.ext
      intro i
      exact (hb i).trans (hact (μ i) (b i)
        (eigenvector_mem_generalized T D' N' hT' hc' hN' (μ i) (b i) (hb i))).symm
    refine ⟨heq, ?_⟩
    apply add_left_cancel (a := D)
    rw [← heq, ← hT', hT, add_comm N D, heq]

end D05.M10.AdditiveDecomposition
