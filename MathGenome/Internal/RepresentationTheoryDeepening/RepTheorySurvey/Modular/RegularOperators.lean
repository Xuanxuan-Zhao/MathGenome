import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.ResidualRoots
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.RegularOperators
import Mathlib.Algebra.DirectSum.Module
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-! Eigenbases for prime-to-`p` group elements over the two splitting fields. -/

namespace RepTheorySurvey.Modular

open Module Polynomial

private theorem rootEigenbasis_of_pow_eq_one
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {n : ℕ} (hn : (n : F) ≠ 0) {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    {T : Module.End F V} (hT : T ^ n = 1) : MR02Spec.HasRootEigenbasis n T := by
  classical
  have hn' : n ≠ 0 := fun h => hn (by simp [h])
  let : NeZero n := ⟨hn'⟩
  let f : F[X] := X ^ n - C 1
  have hmonic : f.Monic := monic_X_pow_sub_C 1 hn'
  have hsplit : f.Splits := X_pow_sub_one_splits hζ
  have hsep : f.Separable := separable_X_pow_sub_C 1 hn one_ne_zero
  let s := f.roots.toFinset
  let factor : F → Module.End F V := fun μ => aeval T (X - C μ)
  have hfactor (μ : F) : factor μ = T - μ • 1 := by
    simp [factor, Algebra.algebraMap_eq_smul_one]
  have hker (μ : F) : LinearMap.ker (factor μ) = T.eigenspace μ := by
    rw [hfactor, Module.End.eigenspace_def]
  have hprod : f = s.noncommProd (fun μ => X - C μ) (fun _ _ _ _ _ => Commute.all _ _) := by
    rw [Finset.noncommProd_eq_prod, hsplit.eq_prod_roots_of_monic hmonic]
    change (f.roots.map (X - C ·)).prod = (s.val.map (X - C ·)).prod
    rw [Multiset.toFinset_val, (nodup_roots hsep).dedup]
  have hcomm : (↑s : Set F).Pairwise (Function.onFun Commute factor) :=
    fun μ _ ν _ _ => (Commute.all (X - C μ) (X - C ν)).map (aeval T)
  have hzero : s.noncommProd factor hcomm = 0 := by
    rw [← Finset.map_noncommProd s (fun μ => X - C μ) (fun _ _ _ _ _ => Commute.all _ _)
      (aeval T), ← hprod]
    simp [f, hT]
  have hspan : (⨆ μ : s, T.eigenspace (μ : F)) = ⊤ := by
    have hi : s.SupIndep fun μ => LinearMap.ker (factor μ) := by
      simpa only [hker] using T.eigenspaces_iSupIndep.supIndep' s
    rw [iSup_subtype]
    simp_rw [← hker]
    rw [← LinearMap.ker_noncommProd_eq_of_supIndep_ker s hcomm hi, hzero, LinearMap.ker_zero]
  let E : s → Submodule F V := fun μ => T.eigenspace (μ : F)
  have hInternal : DirectSum.IsInternal E :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (T.eigenspaces_iSupIndep.comp Subtype.val_injective) hspan
  let bases (μ : s) := Module.finBasis F (E μ)
  let b := hInternal.collectedBasis bases
  let reindex := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  have hroot (μ : F) (hμ : T.HasEigenvalue μ) : μ ^ n = 1 := by
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    apply smul_left_injective F hv.2
    simpa [hT] using (hv.pow_apply n).symm
  refine ⟨fun μ hμ => ⟨rootsOfUnity.mkOfPowEq μ (hroot μ hμ), rfl⟩, b.reindex reindex, ?_⟩
  have hEigenvector (i : Fin (Module.finrank F V)) :
      T.HasEigenvector (reindex.symm i).1.val (b (reindex.symm i)) :=
    ⟨hInternal.collectedBasis_mem bases _, b.ne_zero _⟩
  refine ⟨fun i => rootsOfUnity.mkOfPowEq _
    (hroot _ (Module.End.hasEigenvalue_of_hasEigenvector (hEigenvector i))), ?_⟩
  intro i
  simpa only [Module.Basis.reindex_apply, rootsOfUnity.coe_mkOfPowEq] using
    (hEigenvector i).apply_eq_smul

universe uG uO uK uV

variable {G : Type uG} [Group G] [Finite G] {p : ℕ}
  {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type uK} [Field K] [Algebra O K]

local notation "k" => IsLocalRing.ResidueField O
local notation "m" => primeToPart G p

omit [Finite G] in
private theorem regularAction_pow {F : Type*} [Field F] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V) (hp : p.Prime)
    (g : PRegular G p) : ρ g.val ^ m = 1 := by
  rw [← map_pow, orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_primeToPart hp g), map_one]

set_option backward.isDefEq.respectTransparency false in
/-- A `p`-regular element acts on a finite-dimensional `k[G]`-module with
an eigenbasis, and its eigenvalues are `m`-th roots of unity in `k`. -/
theorem residueRegularEigenbasis (S : SplittingSystem G p O K)
    (g : PRegular G p) (M : Type uV) [AddCommGroup M] [Module (MonoidAlgebra k G) M]
    [FiniteDimensional k (RestrictScalars k (MonoidAlgebra k G) M)] :
    MR02Spec.HasRootEigenbasis m (moduleRepresentation k G M g.val) := by
  obtain ⟨ζ, hζ⟩ := exists_residue_isPrimitiveRoot S
  exact rootEigenbasis_of_pow_eq_one (primeToPart_residue_ne_zero S) hζ
    (regularAction_pow (moduleRepresentation k G M) S.prime g)

set_option backward.isDefEq.respectTransparency false in
/-- A `p`-regular element acts on a finite-dimensional `K[G]`-module with
an eigenbasis, and its eigenvalues are `m`-th roots of unity in `K`. -/
theorem fractionRegularEigenbasis (S : SplittingSystem G p O K)
    (g : PRegular G p) (M : Type uV) [AddCommGroup M] [Module (MonoidAlgebra K G) M]
    [FiniteDimensional K (RestrictScalars K (MonoidAlgebra K G) M)] :
    MR02Spec.HasRootEigenbasis m (moduleRepresentation K G M g.val) := by
  let : CharZero K := S.charZero
  obtain ⟨ζ, hζ⟩ := S.primitiveRoot
  exact rootEigenbasis_of_pow_eq_one (Nat.cast_ne_zero.mpr (primeToPart_pos G p).ne') hζ
    (regularAction_pow (moduleRepresentation K G M) S.prime g)

end RepTheorySurvey.Modular
