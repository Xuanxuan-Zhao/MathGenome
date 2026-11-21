import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.MaximalCohenMacaulayExt
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.CanonicalReduction
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.RegularQuotientExt
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.DepthZeroInjectivity
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularParameters
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.QuotientsAndScalars

import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.CanonicalReduction
/-! GC-11: vanishing of positive Ext from a finite maximal Cohen–Macaulay
module to an arbitrary canonical module. The canonical reduction theorem
is an explicit premise of the conditional helper. -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise
namespace AdvCommAlg.Gorenstein
open CohenMacaulay

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma maximalCohenMacaulay_dimension (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (hM : MaximalCohenMacaulay R M) :
    dimension R M = ringKrullDim R := by
  have hd := (maximalCohenMacaulay_iff_sourceDepth R M).mp hM
  exact le_antisymm (Module.supportDim_le_ringKrullDim R M)
    (hd ▸ Depth.depth_le_supportDim M)

lemma maximalCohenMacaulay_local (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (hM : MaximalCohenMacaulay R M) :
    LocalCohenMacaulay R M := by
  apply (localCohenMacaulay_iff_sourceDepth R M).mpr
  rw [maximalCohenMacaulay_dimension M hM]
  exact (maximalCohenMacaulay_iff_sourceDepth R M).mp hM

lemma systemOfParameters_of_maximalCohenMacaulay (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hM : MaximalCohenMacaulay R M) (xs : List R)
    (hs : IsSystemOfParameters R R xs) : IsSystemOfParameters R M xs := by
  let Q := M ⧸ (Ideal.ofList xs • (⊤ : Submodule R M))
  let T := R ⧸ (Ideal.ofList xs • (⊤ : Submodule R R))
  letI : Nontrivial Q := quotient_list_nontrivial M xs hs.1
  letI : Nontrivial T := quotient_list_nontrivial R xs hs.1
  have hT : dimension R T = 0 := (dimension_zero_iff_finiteLength R T).mpr hs.2.2
  have hsub : Module.support R Q ⊆ Module.support R T := by
    rw [support_quotient, support_quotient]
    intro p hp
    refine ⟨?_, hp.2⟩
    apply Module.mem_support_iff'.mpr
    refine ⟨1, ?_⟩
    intro a ha hz
    have haz : a = 0 := by simpa using hz
    exact ha (haz ▸ p.asIdeal.zero_mem)
  have hle : dimension R Q ≤ dimension R T :=
    Order.krullDim_le_of_strictMono (fun p => ⟨p.1, hsub p.2⟩)
      (fun _ _ h => h)
  have hz : dimension R Q = 0 := by
    apply le_antisymm (hT ▸ hle)
    letI : Nonempty (Module.support R Q) :=
      Module.nonempty_support_of_nontrivial.to_subtype
    exact Order.krullDim_nonneg
  refine ⟨hs.1, ?_, (dimension_zero_iff_finiteLength R Q).mp hz⟩
  rw [maximalCohenMacaulay_dimension M hM]
  exact hs.2.1.trans (Module.supportDim_self_eq_ringKrullDim R)

lemma regular_first_parameter (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (hM : MaximalCohenMacaulay R M)
    (x : R) (xs : List R) (hs : IsSystemOfParameters R R (x :: xs)) :
    IsSMulRegular M x := by
  have hreg := (localCohenMacaulay_iff_every_systemOfParameters_regular M).mp
    (maximalCohenMacaulay_local M hM) (x :: xs)
    (systemOfParameters_of_maximalCohenMacaulay M hM (x :: xs) hs)
  exact ((RingTheory.Sequence.isRegular_cons_iff M x xs).mp hreg).1

lemma regular_singleton_of_mem (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (x : R)
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) :
    RingTheory.Sequence.IsRegular M [x] := by
  refine ⟨(RingTheory.Sequence.isWeaklyRegular_singleton_iff M x).mpr hreg, ?_⟩
  exact (Submodule.Quotient.nontrivial_iff.mp
    (quotient_list_nontrivial M [x] (by simpa using hx))).symm

/-- The numerical maximal CM condition survives the actual quotient action. -/
lemma maximalCohenMacaulay_principal_quotient (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hM : MaximalCohenMacaulay R M) (x : R)
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x)
    (d : ℕ) (hd : ringKrullDim R = (d + 1 : ℕ))
    (hqd : ringKrullDim (R ⧸ Ideal.span {x}) = d) :
    letI := principalQuotientLocalRing x hx
    MaximalCohenMacaulay (R ⧸ Ideal.span {x})
      (M ⧸ (Ideal.span {x} • (⊤ : Submodule R M))) := by
  letI := principalQuotientLocalRing x hx
  let Q := M ⧸ (Ideal.span {x} • (⊤ : Submodule R M))
  letI : Nontrivial Q := quotient_nontrivial R M _
    (Ideal.span_le.mpr (by simpa using hx))
  apply (maximalCohenMacaulay_iff_sourceDepth (R ⧸ Ideal.span {x}) Q).mpr
  have hproper : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson _)).symm
  have hdrop := Depth.grade_quotient_regular M (IsLocalRing.maximalIdeal R)
    hproper [x] (regular_singleton_of_mem M x hx hreg) (by simpa using hx)
  change Depth.depth R (M ⧸ (Ideal.ofList [x] • (⊤ : Submodule R M))) =
    Depth.depth R M - [x].length at hdrop
  rw [Ideal.ofList_singleton, List.length_singleton] at hdrop
  have hdep : Depth.depth R M = (d + 1 : ℕ) := by
    apply WithBot.coe_injective
    exact ((maximalCohenMacaulay_iff_sourceDepth R M).mp hM).trans hd
  have hdrop' : Depth.depth (R ⧸ Ideal.span {x}) Q = d := by
    rw [← depth_of_surjective Q Ideal.Quotient.mk_surjective]
    change Depth.depth R Q = (d : ℕ∞)
    rw [hdrop, hdep]
    norm_cast
  rw [hdrop', hqd]
  rfl

private theorem ext_vanishing_of_dimension
    (hred : Specs.canonical_reductionType.{u}) (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R],
    ringKrullDim R = d →
    ∀ (W : Type u) [AddCommGroup W] [Module R W] [Module.Finite R W],
    Specs.IsCanonicalModuleValue R W →
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    MaximalCohenMacaulay R M →
    ∀ i : ℕ, 0 < i → Subsingleton (Ext (ModuleCat.of R M) (ModuleCat.of R W) i) := by
  induction d with
  | zero =>
    intro R _ _ _ _ hd W _ _ _ hW M _ _ _ hM i hi
    have hCM : LocalCohenMacaulay R R := hW.1
    have hdepth : Depth.depth R R = 0 := by
      apply WithBot.coe_injective
      exact ((localCohenMacaulay_iff_sourceDepth R R).mp hCM).trans
        ((Module.supportDim_self_eq_ringKrullDim R).trans hd)
    haveI : Injective (ModuleCat.of R W) :=
      DepthZeroInjectivity.injective_of_depth_zero_of_finite_injectiveDimension R
        hdepth (ModuleCat.of R W) hW.2.2.2.2
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    exact Ext.subsingleton_of_injective _ _ j
  | succ d ih =>
    intro R _ _ _ _ hd W _ _ _ hW M _ _ _ hM i hi
    classical
    by_cases hzero : Subsingleton M
    · letI := hzero
      exact FiniteExtDetection.subsingleton_ext_of_subsingleton _ _ i
    letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hzero
    letI : Nontrivial W := hW.2.1
    have hRCM : LocalCohenMacaulay R R := hW.1
    have hRMCM : MaximalCohenMacaulay R R := by
      apply (maximalCohenMacaulay_iff_sourceDepth R R).mpr
      exact ((localCohenMacaulay_iff_sourceDepth R R).mp hRCM).trans
        (Module.supportDim_self_eq_ringKrullDim R)
    obtain ⟨xs, hs⟩ := exists_systemOfParameters R R
    cases xs with
    | nil =>
      have hz := (systemOfParameters_nil_iff R R).mp hs
      rw [dimension, Module.supportDim_self_eq_ringKrullDim, hd] at hz
      norm_cast at hz
    | cons x xs =>
      have hx := hs.1 x (by simp)
      have hR := regular_first_parameter R hRMCM x xs hs
      have hMreg := regular_first_parameter M hM x xs hs
      have hWreg := regular_first_parameter W hW.2.2.1 x xs hs
      letI := principalQuotientLocalRing x hx
      have hqdim : ringKrullDim (R ⧸ Ideal.span {x}) = d := by
        have he := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hR hx
        rw [hd] at he
        apply ENat.WithBot.add_one_cancel.mp
        simpa only [Nat.cast_add, Nat.cast_one] using he
      let QM := M ⧸ (Ideal.span {x} • (⊤ : Submodule R M))
      let QW := W ⧸ (Ideal.span {x} • (⊤ : Submodule R W))
      have hQW : Specs.IsCanonicalModuleValue (R ⧸ Ideal.span {x}) QW :=
        hred R W hW x xs hs
      have hQM := maximalCohenMacaulay_principal_quotient M hM x hx hMreg d hd hqdim
      have hvan := ih (R ⧸ Ideal.span {x}) hqdim QW hQW QM hQM i hi
      letI : Subsingleton (Ext (ModuleCat.of (R ⧸ Ideal.span {x}) QM)
          (ModuleCat.of (R ⧸ Ideal.span {x}) QW) i) := hvan
      obtain ⟨e⟩ := RegularQuotientExt.comparison R x (ModuleCat.of R W) hR hWreg i
      letI : Subsingleton ↑((RegularQuotientExt.quotientExtFunctor x
          (ModuleCat.of R W) i).obj (Opposite.op (ModuleCat.of _ QM))) := hvan
      haveI : Subsingleton (Ext
          (((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj
            (ModuleCat.of (R ⧸ Ideal.span {x}) QM))) (ModuleCat.of R W) (i + 1)) := by
        exact (ModuleCat.mono_iff_injective (e.inv.app
          (Opposite.op (ModuleCat.of (R ⧸ Ideal.span {x}) QM)))).mp inferInstance |>.subsingleton
      haveI : Subsingleton (Ext (ModuleCat.of R (QuotSMulTop x M))
          (ModuleCat.of R W) (1 + i)) := by
        rw [Nat.add_comm 1 i]
        exact FiniteExtDetection.subsingleton_ext_of_linearEquiv
          (B := ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj
            (ModuleCat.of (R ⧸ Ideal.span {x}) QM)))
          (Depth.principalQuotientEquiv (ModuleCat.of R M) x) (i + 1)
      exact FiniteExtDetection.subsingleton_ext_of_smul_cokernel
        (ModuleCat.of R M) (ModuleCat.of R W) x hx hMreg i

/-- Conditional GC-11 derivation with the full canonical reduction premise. -/
theorem maximalCohenMacaulay_ext_vanishing_conditional
    (hred : Specs.canonical_reductionType.{u}) :
    Specs.maximalCohenMacaulay_ext_vanishingType.{u} := by
  intro R _ _ _ _ W _ _ _ hW M _ _ _ hM i hi
  obtain ⟨d, hd⟩ := exists_nat_dimension (R := R) R
  have hdR : ringKrullDim R = d :=
    (Module.supportDim_self_eq_ringKrullDim R).symm.trans hd
  exact ext_vanishing_of_dimension hred d R hdR W hW M hM i hi

end AdvCommAlg.Gorenstein

universe v8_closure_7b1818ee1b39b225_u0
theorem _root_.«AdvCommAlg».«Gorenstein».«maximalCohenMacaulay_ext_vanishing» : _root_.«AdvCommAlg».«Gorenstein».«Specs».«maximalCohenMacaulay_ext_vanishingType».{v8_closure_7b1818ee1b39b225_u0} :=
  @_root_.«AdvCommAlg».«Gorenstein».«maximalCohenMacaulay_ext_vanishing_conditional».{v8_closure_7b1818ee1b39b225_u0} (@_root_.«AdvCommAlg».«Gorenstein».«canonical_reduction».{v8_closure_7b1818ee1b39b225_u0})
