import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.DimensionBounds
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.SupportAndParameters
import MathGenome.Internal.AlgebraCore.P103.Ch06.SystemsParameters
import Mathlib.Data.List.OfFn

/-! Support, finite colength, and systems of parameters (CM-02).
The tuple parameter-count theorem is transported to lists, with the
annihilator-quotient dimension identified with CM-01's support dimension.
-/

universe u
namespace AdvCommAlg.CohenMacaulay

noncomputable def IsSystemOfParameters (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] (x : List R) : Prop :=
  (∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) ∧
  (x.length : WithBot ℕ∞) = dimension R M ∧
  IsFiniteLength R (M ⧸ (Ideal.ofList x • (⊤ : Submodule R M)))

theorem support_quotient (R : Type u) [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (J : Ideal R) :
    Module.support R (M ⧸ (J • (⊤ : Submodule R M))) =
      Module.support R M ∩ PrimeSpectrum.zeroLocus (J : Set R) :=
  Module.support_quotient J

section Local
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]

theorem quotient_nontrivial (J : Ideal R) (hJ : J ≤ IsLocalRing.maximalIdeal R) :
    Nontrivial (M ⧸ (J • (⊤ : Submodule R M))) :=
  P103.Ch06.FiniteColength.quotient_nontrivial R M J hJ

theorem finiteLength_quotient_iff_support_singleton
    (J : Ideal R) (hJ : J ≤ IsLocalRing.maximalIdeal R) :
    IsFiniteLength R (M ⧸ (J • (⊤ : Submodule R M))) ↔
      Module.support R (M ⧸ (J • (⊤ : Submodule R M))) = {IsLocalRing.closedPoint R} := by
  have := quotient_nontrivial R M J hJ
  exact (P103.Ch06.FiniteColength.support_singleton_iff_finite_length R
    (M ⧸ (J • (⊤ : Submodule R M)))).symm

omit [IsNoetherianRing R] [IsLocalRing R] in
private lemma ofList_ofFn_eq_span_range {n : ℕ} (x : Fin n → R) :
    Ideal.ofList (List.ofFn x) = Ideal.span (Set.range x) := by
  change Ideal.span {a | a ∈ List.ofFn x} = _
  congr 1
  ext a
  exact List.mem_ofFn' x a

theorem exists_systemOfParameters : ∃ x : List R, IsSystemOfParameters R M x := by
  obtain ⟨d, hd, ⟨x, hxm, hlen⟩, _⟩ := P103.Ch06.SystemsParameters.parameter_count R M
  refine ⟨List.ofFn x, ?_, ?_, ?_⟩
  · exact List.forall_mem_ofFn_iff.mpr hxm
  · simpa only [List.length_ofFn] using
      ((dimension_eq_quotient_annihilator R M).trans hd).symm
  · exact (Submodule.quotEquivOfEq _ _
      (congrArg (fun I : Ideal R => I • (⊤ : Submodule R M))
        (ofList_ofFn_eq_span_range R x))).symm.isFiniteLength hlen

theorem dimension_le_length_of_finiteLength_quotient (x : List R)
    (hxm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R)
    (hlen : IsFiniteLength R (M ⧸ (Ideal.ofList x • (⊤ : Submodule R M)))) :
    dimension R M ≤ (x.length : WithBot ℕ∞) := by
  obtain ⟨d, hd, _, hbound⟩ := P103.Ch06.SystemsParameters.parameter_count R M
  have hspan : Ideal.span (Set.range x.get) = Ideal.ofList x := by
    rw [← ofList_ofFn_eq_span_range, List.ofFn_get]
  have hle : d ≤ x.length := hbound x.length x.get
    (fun i => hxm _ (List.get_mem ..))
    ((Submodule.quotEquivOfEq _ _
      (congrArg (fun I : Ideal R => I • (⊤ : Submodule R M)) hspan)).symm.isFiniteLength hlen)
  rw [(dimension_eq_quotient_annihilator R M).trans hd]
  exact_mod_cast hle

theorem isLeast_parameter_length :
    ∃ d : ℕ, dimension R M = (d : WithBot ℕ∞) ∧
      IsLeast {n : ℕ | ∃ x : List R, x.length = n ∧
        (∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) ∧
        IsFiniteLength R (M ⧸ (Ideal.ofList x • (⊤ : Submodule R M)))} d := by
  obtain ⟨x, hxm, hdim, hlen⟩ := exists_systemOfParameters R M
  refine ⟨x.length, hdim.symm, ⟨⟨x, rfl, hxm, hlen⟩, ?_⟩⟩
  rintro n ⟨y, rfl, hym, hylen⟩
  have h := dimension_le_length_of_finiteLength_quotient R M y hym hylen
  rw [← hdim] at h
  exact_mod_cast h

theorem dimension_zero_iff_finiteLength : dimension R M = 0 ↔ IsFiniteLength R M := by
  rw [dimension_eq_quotient_annihilator]
  exact P103.Ch06.SystemsParameters.dimension_zero_iff R M

theorem systemOfParameters_nil_iff : IsSystemOfParameters R M [] ↔ dimension R M = 0 := by
  constructor
  · intro h
    simpa only [List.length_nil, Nat.cast_zero] using h.2.1.symm
  · intro h
    refine ⟨by simp, by simpa using h.symm, ?_⟩
    have hlen := (dimension_zero_iff_finiteLength R M).mp h
    exact hlen.of_surjective (Submodule.mkQ_surjective _)

theorem dimension_quotient_regular (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hreg : Function.Injective (fun m : M => x • m)) :
    Nontrivial (QuotSMulTop x M) ∧
      dimension R (QuotSMulTop x M) + 1 = dimension R M := by
  refine ⟨?_, Depth.supportDim_quotSMulTop_add_one M x hx hreg⟩
  apply Submodule.Quotient.nontrivial_iff.mpr
  exact (Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator
    ((IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M)) hx)).symm

end Local
end AdvCommAlg.CohenMacaulay
