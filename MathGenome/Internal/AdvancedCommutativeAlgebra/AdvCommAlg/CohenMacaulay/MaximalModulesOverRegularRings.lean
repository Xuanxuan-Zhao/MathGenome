import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.MaximalModulesOverRegularRings
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularLocalStructure
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularParameters
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Homological.MinimalFreeResolution

/-! CM-12: maximal Cohen–Macaulay modules over regular local rings.
The forward direction uses exactness of reduction by a regular sequence
and a minimal finite free cover. Thus no finite projective dimension is
assumed. The argument includes the empty list of generators.
-/

universe u
open RingTheory.Sequence
open scoped Pointwise TensorProduct
namespace AdvCommAlg.CohenMacaulay

section FreeCriterion
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- If a generating list of the maximal ideal is weakly regular on a finite
module, a minimal finite free cover has zero kernel. -/
theorem free_of_weaklyRegular_generators (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (x : List R)
    (hgen : Ideal.ofList x = IsLocalRing.maximalIdeal R)
    (hreg : IsWeaklyRegular M x) : Module.Free R M := by
  obtain ⟨F, hfin, hfree, f, hsurj, hmin⟩ :=
    AdvCommAlg.exists_minimalFreeCover (ModuleCat.of R M)
  let K := LinearMap.ker f.hom
  let i : K →ₗ[R] F := K.subtype
  have hex : Function.Exact (0 : K →ₗ[R] K) i := by
    rw [LinearMap.exact_iff]
    simp [i]
  have hex' : Function.Exact i f.hom := by
    rw [LinearMap.exact_iff]
    simp [i, K]
  have hred := map_first_exact_on_four_term_right_exact_of_isSMulRegular_last
    hex hex' hsurj hreg
  let J := Ideal.ofList x
  let q := Submodule.mapQ (J • (⊤ : Submodule R K))
    (J • (⊤ : Submodule R F)) i (Submodule.smul_top_le_comap_smul_top J i)
  have hqzero : ∀ z, q z = 0 := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | _ z =>
      change (J • (⊤ : Submodule R F)).mkQ (i z) = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      simpa [J, hgen, i] using hmin z.property
  have htop : (⊤ : Submodule R K) ≤ J • ⊤ := by
    intro z _
    have hz := (hred ((J • (⊤ : Submodule R K)).mkQ z)).mp
      (hqzero ((J • (⊤ : Submodule R K)).mkQ z))
    obtain ⟨w, hw⟩ := hz
    have hz0 : (J • (⊤ : Submodule R K)).mkQ z = 0 := by
      simpa using hw.symm
    exact (Submodule.Quotient.mk_eq_zero _).mp hz0
  have hbot : (⊤ : Submodule R K) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot J ⊤ Module.Finite.fg_top htop
      (by simpa [J, hgen] using IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
  have hinj : Function.Injective f.hom := by
    rw [← LinearMap.ker_eq_bot]
    apply eq_bot_iff.mpr
    intro z hz
    have h : (⟨z, hz⟩ : K) ∈ (⊥ : Submodule R K) := hbot ▸ Submodule.mem_top
    exact congrArg Subtype.val h
  exact Module.Free.of_equiv (LinearEquiv.ofBijective f.hom ⟨hinj, hsurj⟩)
end FreeCriterion

section RegularLocal
variable (R : Type u) [CommRing R] [IsRegularLocalRing R]
variable (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M]

/-- Every nonzero finite free module is maximal Cohen–Macaulay over a
regular local ring. No restriction on its rank is imposed. -/
theorem maximalCohenMacaulay_of_free [Module.Free R M] :
    MaximalCohenMacaulay R M := by
  obtain ⟨x, hgen, hdim, hx⟩ := exists_regular_generators R
  have hxm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R :=
    fun a ha => hgen ▸ Ideal.subset_span ha
  have hweak : IsWeaklyRegular M x :=
    ((TensorProduct.lid R M).isWeaklyRegular_congr x).mp
      hx.toIsWeaklyRegular.isWeaklyRegular_rTensor
  have hreg : IsRegular M x :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hxm).mpr hweak
  apply (maximalCohenMacaulay_iff_sourceDepth R M).mpr
  apply le_antisymm
  · exact (Depth.depth_le_supportDim (R := R) M).trans (Module.supportDim_le_ringKrullDim R M)
  · rw [hdim]
    apply WithBot.coe_le_coe.mpr
    rw [Depth.depth_eq_grade, Depth.grade_of_smul_ne_top _ _
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (IsLocalRing.maximalIdeal_le_jacobson _)).symm]
    exact le_sSup ⟨x, hreg, hxm, rfl⟩

/-- A maximal Cohen–Macaulay module is free, with no assumption on its
projective dimension. -/
theorem free_of_maximalCohenMacaulay (hM : MaximalCohenMacaulay R M) :
    Module.Free R M := by
  have hdepth := (maximalCohenMacaulay_iff_sourceDepth R M).mp hM
  have hbound := Depth.depth_le_supportDim (R := R) M
  rw [hdepth] at hbound
  have hdimM : dimension R M = ringKrullDim R :=
    le_antisymm (Module.supportDim_le_ringKrullDim R M) hbound
  have hCM : LocalCohenMacaulay R M :=
    (localCohenMacaulay_iff_sourceDepth R M).mpr (hdepth.trans hdimM.symm)
  obtain ⟨x, hgen, hdim, _⟩ := exists_regular_generators R
  have hxm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R :=
    fun a ha => hgen ▸ Ideal.subset_span ha
  have hlength : (x.length : WithBot ℕ∞) = dimension R M :=
    hdim.symm.trans hdimM.symm
  have hfinite : IsFiniteLength R
      (M ⧸ (Ideal.ofList x • (⊤ : Submodule R M))) := by
    apply (finiteLength_quotient_iff_support_singleton R M (Ideal.ofList x)
      (by rw [hgen])).mpr
    rw [support_quotient, hgen]
    change Module.support R M ∩
      PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R : Set R) =
        {⟨IsLocalRing.maximalIdeal R, inferInstance⟩}
    rw [PrimeSpectrum.zeroLocus_eq_singleton]
    exact Set.inter_singleton_of_mem (IsLocalRing.closedPoint_mem_support R M)
  have hreg : IsRegular M x :=
    (localCohenMacaulay_iff_every_systemOfParameters_regular M).mp hCM x
      ⟨hxm, hlength, hfinite⟩
  exact free_of_weaklyRegular_generators M x hgen hreg.toIsWeaklyRegular

/-- CM-12, including rank one and dimension zero. Finiteness is a hypothesis,
so the right hand side is precisely finite freeness. -/
theorem maximalCohenMacaulay_iff_free :
    MaximalCohenMacaulay R M ↔ Module.Free R M :=
  ⟨free_of_maximalCohenMacaulay R M, fun _ => maximalCohenMacaulay_of_free R M⟩
end RegularLocal

end AdvCommAlg.CohenMacaulay
