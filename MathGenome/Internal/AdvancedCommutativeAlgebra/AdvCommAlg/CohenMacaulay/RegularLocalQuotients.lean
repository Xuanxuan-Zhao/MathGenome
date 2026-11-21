import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularLocalStructure
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularParameters
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.QuotientsAndScalars
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.RegularLocalQuotients

/-! CM-08b: prefix quotients, regular quotients, and the DVR counterexample. -/

universe u
namespace AdvCommAlg.CohenMacaulay

theorem regularLocal_prefix_quotient (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (d : ℕ) (x : List R) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (hlen : x.length = d) (hgen : Ideal.ofList x = IsLocalRing.maximalIdeal R)
    (c : ℕ) (hc : c ≤ d) :
    IsRegularLocalRing (R ⧸ Ideal.ofList (x.take c)) ∧
      ringKrullDim (R ⧸ Ideal.ofList (x.take c)) = ((d - c : ℕ) : WithBot ℕ∞) :=
  P103.Ch07.RegularSequence.prefix_regular d x hd hlen hgen c hc

theorem regularLocal_regular_quotient_cohenMacaulay
    (R : Type u) [CommRing R] [IsRegularLocalRing R] (x : List R)
    (hx : RingTheory.Sequence.IsRegular R x)
    (hmem : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) :
    letI := Depth.regularQuotientLocalRing x hmem
    LocalCohenMacaulay (R ⧸ Ideal.ofList x) (R ⧸ Ideal.ofList x) := by
  letI := Depth.regularQuotientLocalRing x hmem
  have h := cohenMacaulay_quotient_of_regular R (regularLocal_cohenMacaulay R) x hmem hx
  have hsmul : Ideal.ofList x • (⊤ : Submodule R R) = Ideal.ofList x := by
    change Ideal.ofList x * ⊤ = _
    exact Ideal.mul_top _
  rw [hsmul] at h
  exact (localCohenMacaulay_of_surjective_iff (R := R) (S := R ⧸ Ideal.ofList x)
    (R ⧸ Ideal.ofList x) Ideal.Quotient.mk_surjective).mp h

theorem dvr_uniformizer_square_quotient
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (t : R) (ht : IsLocalRing.maximalIdeal R = Ideal.span {t}) :
    RingTheory.Sequence.IsRegular R [t ^ 2] ∧
    ∃ hlocal : IsLocalRing (R ⧸ Ideal.ofList [t ^ 2]),
      ringKrullDim (R ⧸ Ideal.ofList [t ^ 2]) = 0 ∧
      @IsLocalRing.maximalIdeal (R ⧸ Ideal.ofList [t ^ 2]) _ hlocal ≠ ⊥ ∧
      ¬ IsRegularLocalRing (R ⧸ Ideal.ofList [t ^ 2]) := by
  have hirr : Irreducible t := (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr ht
  have htm : t ∈ IsLocalRing.maximalIdeal R := by
    rw [ht]
    exact Ideal.subset_span (by simp)
  have hmem : ∀ a ∈ [t ^ 2], a ∈ IsLocalRing.maximalIdeal R := by
    simpa using (IsLocalRing.maximalIdeal R).pow_mem_of_mem htm 2 (by decide)
  have hreg : RingTheory.Sequence.IsRegular R [t ^ 2] := by
    refine ⟨(RingTheory.Sequence.isWeaklyRegular_singleton_iff R (t ^ 2)).mpr ?_, ?_⟩
    · intro a b hab
      exact mul_left_cancel₀ (pow_ne_zero 2 hirr.ne_zero) hab
    · have hle : Ideal.ofList [t ^ 2] ≤ IsLocalRing.maximalIdeal R := Ideal.span_le.mpr hmem
      have hproper := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hle
      simpa only [show Ideal.ofList [t ^ 2] • (⊤ : Submodule R R) = Ideal.ofList [t ^ 2] from
        Ideal.mul_top _ , ne_comm] using hproper
  letI := Depth.regularQuotientLocalRing [t ^ 2] hmem
  have hdim : ringKrullDim (R ⧸ Ideal.ofList [t ^ 2]) = 0 := by
    have h := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular [t ^ 2] hreg
    rw [IsPrincipalIdealRing.ringKrullDim_eq_one R (IsDiscreteValuationRing.not_isField R)] at h
    simpa using (ENat.WithBot.add_one_cancel.mp (by simpa using h :
      ringKrullDim (R ⧸ Ideal.ofList [t ^ 2]) + 1 = (0 : WithBot ℕ∞) + 1))
  have htnot : t ∉ Ideal.ofList [t ^ 2] := by
    rw [Ideal.ofList_singleton, Ideal.mem_span_singleton]
    rintro ⟨a, ha⟩
    have ha' : t * 1 = t * (t * a) := by simpa [pow_two, mul_assoc] using ha
    have hu : IsUnit t := isUnit_of_dvd_one ⟨a, mul_left_cancel₀ hirr.ne_zero ha'⟩
    exact hirr.not_isUnit hu
  have hmax : IsLocalRing.maximalIdeal (R ⧸ Ideal.ofList [t ^ 2]) ≠ ⊥ := by
    intro hz
    have hm : Ideal.Quotient.mk (Ideal.ofList [t ^ 2]) t ∈
        IsLocalRing.maximalIdeal (R ⧸ Ideal.ofList [t ^ 2]) := by
      rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (Ideal.ofList [t ^ 2]))
        Ideal.Quotient.mk_surjective]
      exact Ideal.mem_map_of_mem _ htm
    rw [hz, Ideal.mem_bot] at hm
    exact htnot (Ideal.Quotient.eq_zero_iff_mem.mp hm)
  refine ⟨hreg, inferInstance, hdim, hmax, ?_⟩
  intro hregular
  letI := hregular
  have hf := regularLocal_dimension_zero_isField (R ⧸ Ideal.ofList [t ^ 2]) hdim
  exact hmax (IsLocalRing.isField_iff_maximalIdeal_eq.mp hf)

end AdvCommAlg.CohenMacaulay
