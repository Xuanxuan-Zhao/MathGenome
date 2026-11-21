import MathGenome.Internal.Specs.D05.M10.GeneralizedDecomposition
import MathGenome.Internal.D05.M08.Primary
import MathGenome.Internal.D05.M08.CayleyHamilton
import MathGenome.Internal.D05.M10.Generalized
import Mathlib.Algebra.Polynomial.Splits

/-! Generalized eigenspace decomposition over the original field, assuming only
splitting of the characteristic polynomial. -/

noncomputable section
namespace D05.M10.GeneralizedDecomposition

open Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- The primary summands obtained from any split monic annihilator span V.
Kernel stabilization puts each of them inside the corresponding G_μ. -/
theorem iSup_generalized_eq_top (T : Module.End K V) (p : Polynomial K)
    (hm : p.Monic) (hs : p.Splits) (hz : Polynomial.aeval T p = 0) :
    (⨆ μ : K, T.genEigenspace μ (Module.finrank K V)) = ⊤ := by
  classical
  let ι := {μ // μ ∈ p.roots.toFinset}
  let f : ι → Polynomial K := fun μ => (X - C μ.val) ^ p.rootMultiplicity μ.val
  have hprod : (∏ μ : ι, f μ) = p := by
    calc
      (∏ μ : ι, f μ) = ∏ μ ∈ p.roots.toFinset,
          (X - C μ) ^ p.rootMultiplicity μ := by
            simpa only [f, ι] using
              (Finset.prod_coe_sort p.roots.toFinset
                (fun μ => ((X : Polynomial K) - C μ) ^ p.rootMultiplicity μ))
      _ = (p.roots.map (fun μ => X - C μ)).prod :=
        Polynomial.prod_multiset_root_eq_finset_root.symm
      _ = p := (hs.eq_prod_roots_of_monic hm).symm
  have hc : Pairwise (fun μ ν : ι => IsCoprime (f μ) (f ν)) := by
    intro μ ν hne
    exact (Polynomial.pairwise_coprime_X_sub_C (s := fun μ : ι => μ.val)
      Subtype.val_injective hne).pow
  obtain ⟨_, hU, _⟩ := D05.M08.Primary.coprime_kernel_decomposition T f hc (by rw [hprod]; exact hz)
  have hspan := ((D05.M06.DirectSum.internal_iff_spanning_zero_sum _).mp hU).1
  apply top_unique
  rw [← hspan]
  apply iSup_le
  intro μ
  apply le_trans _ (le_iSup (fun ν : K => T.genEigenspace ν (Module.finrank K V)) μ.val)
  intro x hx
  apply (Generalized.mem_iff T μ.val x).mpr
  apply Module.End.ker_pow_le_ker_pow_finrank (T - μ.val • 1) (p.rootMultiplicity μ.val)
  simpa only [f, map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] using hx

theorem outside_spectrum : Specs.D05.M10.GeneralizedDecomposition.outside_spectrum := by
  intro K V _ _ _ _ T μ hμ
  by_contra hne
  have hgen : T.HasUnifEigenvalue μ (Module.finrank K V) := hne
  exact hμ ((hgen.lt (by simp : (0 : ℕ∞) < 1)).mem_spectrum)

theorem decomposition : Specs.D05.M10.GeneralizedDecomposition.decomposition := by
  intro K V _ _ _ _ T hs
  classical
  change _root_.DirectSum.IsInternal
    (fun μ : spectrum K T => T.genEigenspace μ.val (Module.finrank K V))
  apply _root_.DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (T.independent_genEigenspace (Module.finrank K V)).comp Subtype.val_injective
  · have htop := iSup_generalized_eq_top T T.charpoly (LinearMap.charpoly_monic T) hs
      (D05.M08.CayleyHamilton.annihilates T)
    apply top_unique
    rw [← htop]
    apply iSup_le
    intro μ
    by_cases hμ : μ ∈ spectrum K T
    · exact le_iSup_of_le ⟨μ, hμ⟩ le_rfl
    · have hz : T.genEigenspace μ (Module.finrank K V) = ⊥ := outside_spectrum T μ hμ
      rw [hz]
      exact bot_le

theorem summand_structure : Specs.D05.M10.GeneralizedDecomposition.summand_structure := by
  intro K V _ _ _ _ T μ
  exact Generalized.restriction_structure T μ.val

theorem zero_dimension : Specs.D05.M10.GeneralizedDecomposition.zero_dimension := by
  intro K V _ _ _ _ T hn
  have : Subsingleton V := Module.finrank_zero_iff.mp hn
  have he : IsEmpty (spectrum K T) := ⟨by
    intro μ
    have h := (Module.End.hasEigenvalue_iff_mem_spectrum).mpr μ.property
    exact (D05.M09.Eigenspace.no_eigenvalues_on_zero_space T μ.val) h⟩
  refine ⟨he, decomposition T ?_⟩
  change T.charpoly.Splits
  rw [show T.charpoly = 1 from D05.M08.Charpoly.zero_dimensional T hn]
  exact Polynomial.Splits.one

end D05.M10.GeneralizedDecomposition
