import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.SupportAndParameters
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.RegularQuotient
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.QuotientsAndScalars

/-! CM-05: regular quotients and restriction of scalars along surjections.
The scalar comparison theorems retain the zero-module conventions and do
not require Cohen–Macaulayness. The regular quotient equivalences use the
same quotient module with its canonical R and R/(x) actions. -/

universe u
namespace AdvCommAlg.CohenMacaulay

section Scalars
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (L : Type u) [AddCommGroup L] [Module R L] [Module S L]
variable [IsScalarTower R S L] [Module.Finite S L]

theorem finite_restrictScalars_of_surjective
    (hf : Function.Surjective (algebraMap R S)) : Module.Finite R L := by
  constructor
  simpa only [Submodule.restrictScalars_top] using
    (Module.Finite.fg_top (R := S) (M := L)).restrictScalars_of_surjective hf

theorem dimension_of_surjective (hf : Function.Surjective (algebraMap R S)) :
    dimension R L = dimension S L := by
  haveI := finite_restrictScalars_of_surjective L hf
  rw [dimension_eq_quotient_annihilator, dimension_eq_quotient_annihilator,
    ← Module.comap_annihilator (R := S) (R₀ := R) (M := L)]
  exact (RingEquiv.ofBijective
    (Ideal.quotientMap (Module.annihilator S L) (algebraMap R S) le_rfl)
    ⟨Ideal.quotientMap_injective, Ideal.quotientMap_surjective hf⟩).ringKrullDim

variable [IsLocalRing R] [IsLocalRing S]

theorem depth_of_surjective (hf : Function.Surjective (algebraMap R S)) :
    Depth.depth R L = Depth.depth S L := by
  unfold Depth.depth
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (algebraMap R S) hf]
  exact (Depth.grade_map_of_surjective L hf _).symm

variable [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite R L]

theorem localCohenMacaulay_of_surjective_iff
    (hf : Function.Surjective (algebraMap R S)) :
    LocalCohenMacaulay R L ↔ LocalCohenMacaulay S L := by
  simp only [LocalCohenMacaulay,
    ← Depth.depth_eq_libraryDepth (ModuleCat.of R L),
    ← Depth.depth_eq_libraryDepth (ModuleCat.of S L),
    depth_of_surjective L hf, dimension_of_surjective L hf]

end Scalars

section RegularQuotient
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]

/-- The two numerical drops have the same increment, so equality of depth
and dimension is equivalent before and after quotienting. -/
theorem localCohenMacaulay_quotient_regular (x : R)
    (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hreg : Function.Injective (fun m : M => x • m)) :
    LocalCohenMacaulay R M ↔ LocalCohenMacaulay R (QuotSMulTop x M) := by
  obtain ⟨hQ, hdim⟩ := dimension_quotient_regular R M x hx hreg
  haveI := hQ
  have hI : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M))).symm
  have hmem : ∀ a ∈ [x], a ∈ IsLocalRing.maximalIdeal R := by simpa using hx
  have hs : RingTheory.Sequence.IsRegular M [x] := by
    refine ⟨(RingTheory.Sequence.isWeaklyRegular_singleton_iff M x).mpr hreg, ?_⟩
    exact (ne_top_of_le_ne_top hI (Submodule.smul_mono_left
      (Ideal.span_le.mpr hmem))).symm
  have hle : (1 : ℕ∞) ≤ Depth.depth R M := by
    rw [Depth.depth_eq_grade, Depth.grade_of_smul_ne_top _ _ hI]
    exact le_sSup ⟨[x], hs, hmem, rfl⟩
  have hd : Depth.depth R (QuotSMulTop x M) = Depth.depth R M - 1 := by
    have h := Depth.grade_quotient_regular M (IsLocalRing.maximalIdeal R) hI [x] hs hmem
    rw [Ideal.ofList_singleton, Submodule.ideal_span_singleton_smul] at h
    exact h
  have hdrop : (Depth.depth R (QuotSMulTop x M) : WithBot ℕ∞) + 1 =
      (Depth.depth R M : WithBot ℕ∞) := by
    exact_mod_cast (hd ▸ tsub_add_cancel_of_le hle :
      Depth.depth R (QuotSMulTop x M) + 1 = Depth.depth R M)
  rw [localCohenMacaulay_iff_sourceDepth, localCohenMacaulay_iff_sourceDepth,
    ← hdrop, ← hdim, ENat.WithBot.add_one_cancel]

theorem localCohenMacaulay_quotient_regular_scalars (x : R)
    (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hreg : Function.Injective (fun m : M => x • m)) :
    letI := Depth.regularQuotientLocalRing [x] (by simpa using hx)
    LocalCohenMacaulay R M ↔
      LocalCohenMacaulay (R ⧸ Ideal.ofList [x])
        (M ⧸ (Ideal.ofList [x] • (⊤ : Submodule R M))) := by
  letI := Depth.regularQuotientLocalRing [x] (by simpa using hx)
  have h := localCohenMacaulay_quotient_regular R M x hx hreg
  have h' : LocalCohenMacaulay R M ↔
      LocalCohenMacaulay R (M ⧸ (Ideal.ofList [x] • (⊤ : Submodule R M))) := by
    rw [Ideal.ofList_singleton, Submodule.ideal_span_singleton_smul]
    exact h
  exact h'.trans (localCohenMacaulay_of_surjective_iff _ Ideal.Quotient.mk_surjective)

end RegularQuotient
end AdvCommAlg.CohenMacaulay
