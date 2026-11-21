import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.CanonicalReduction
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.RegularQuotientExt
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.InjectiveDimensionTest
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularParameters
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.QuotientsAndScalars
import Mathlib.RingTheory.Length

/-! GC-11: canonical reduction, paper.tex:4742–4760.
The parameter acts regularly on every nonzero finite MCM module. The regular
quotient has maximal CM depth; the residue-field Ext shift preserves type and
eventual vanishing. All quotient actions are the canonical ones. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise ModuleCat.Algebra
universe u

namespace AdvCommAlg.Gorenstein
open CohenMacaulay

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- A nonzero maximal CM module has full support dimension, hence is CM. -/
lemma maximalCM_dimension (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (hM : MaximalCohenMacaulay R M) :
    dimension R M = ringKrullDim R ∧ LocalCohenMacaulay R M := by
  have hd := (maximalCohenMacaulay_iff_sourceDepth R M).mp hM
  have he : dimension R M = ringKrullDim R := le_antisymm
    (Module.supportDim_le_ringKrullDim R M)
    (by rw [← hd]; exact Depth.depth_le_supportDim M)
  exact ⟨he, (localCohenMacaulay_iff_sourceDepth R M).mpr (hd.trans he.symm)⟩

/-- Every ring system of parameters is a system of parameters on a nonzero MCM module. -/
lemma systemOfParameters_maximalCM (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (hM : MaximalCohenMacaulay R M)
    (xs : List R) (hsop : IsSystemOfParameters R R xs) :
    IsSystemOfParameters R M xs := by
  have hdim := (maximalCM_dimension M hM).1
  refine ⟨hsop.1, ?_, ?_⟩
  · rw [hdim, ← Module.supportDim_self_eq_ringKrullDim R]
    exact hsop.2.1
  · let J := Ideal.ofList xs
    have hJ : J ≤ IsLocalRing.maximalIdeal R := Ideal.span_le.mpr hsop.1
    have hR := (finiteLength_quotient_iff_support_singleton R R J hJ).mp hsop.2.2
    haveI := quotient_nontrivial R M J hJ
    apply (finiteLength_quotient_iff_support_singleton R M J hJ).mpr
    apply Set.Subset.antisymm
    · intro p hp
      apply hR.subset
      rw [Module.support_quotient] at hp ⊢
      refine ⟨?_, hp.2⟩
      rw [Module.support_of_algebra]
      change (⊥ : Ideal R) ≤ p.asIdeal
      exact bot_le
    · intro p hp
      obtain rfl := Set.mem_singleton_iff.mp hp
      exact IsLocalRing.closedPoint_mem_support R _

/-- The first element of a ring system of parameters is regular on every nonzero MCM module. -/
lemma firstParameter_regular_maximalCM (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (hM : MaximalCohenMacaulay R M)
    (x : R) (xs : List R) (hsop : IsSystemOfParameters R R (x :: xs)) :
    IsSMulRegular M x := by
  have hreg := (localCohenMacaulay_iff_every_systemOfParameters_regular M).mp
    (maximalCM_dimension M hM).2 (x :: xs) (systemOfParameters_maximalCM M hM _ hsop)
  exact (RingTheory.Sequence.isRegular_cons_iff M x xs).mp hreg |>.1

omit [IsNoetherianRing R] in
/-- Surjective local scalar change identifies the actual residue fields R-linearly. -/
noncomputable def residueFieldEquivOfSurjective {S : Type u} [CommRing S] [IsLocalRing S]
    [Algebra R S] (hf : Function.Surjective (algebraMap R S)) :
    IsLocalRing.ResidueField R ≃ₗ[R] IsLocalRing.ResidueField S := by
  letI := IsLocalHom.of_surjective (algebraMap R S) hf
  let f : IsLocalRing.ResidueField R →ₐ[R] IsLocalRing.ResidueField S :=
    { IsLocalRing.ResidueField.map (algebraMap R S) with
      commutes' := fun r => IsLocalRing.ResidueField.map_residue (algebraMap R S) r }
  apply (AlgEquiv.ofBijective f ⟨f.injective, ?_⟩).toLinearEquiv
  intro a
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective (R := S) a
  obtain ⟨r, rfl⟩ := hf s
  exact ⟨IsLocalRing.residue R r, IsLocalRing.ResidueField.map_residue _ r⟩

/-- The residue-field instance of the regular-quotient Ext comparison. -/
noncomputable def residueExtQuotientEquiv (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hR : IsSMulRegular R x) (M : ModuleCat.{u} R) (hM : IsSMulRegular M x) (i : ℕ) :
    letI := principalQuotientLocalRing x hx
    Depth.ResidueExt M (i + 1) ≃ₗ[R]
      Depth.ResidueExt (Depth.Rees.quotientModule (Ideal.span {x}) M) i := by
  letI := principalQuotientLocalRing x hx
  let K := ModuleCat.of (R ⧸ Ideal.span {x})
    (IsLocalRing.ResidueField (R ⧸ Ideal.span {x}))
  let e := residueFieldEquivOfSurjective (R := R) (S := R ⧸ Ideal.span {x})
    Ideal.Quotient.mk_surjective
  let e' : ModuleCat.of R (IsLocalRing.ResidueField R) ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj K :=
    e.toModuleIso
  exact (Depth.Iterate.extIsoCongr e' (Iso.refl M) (i + 1)).trans
    ((Depth.reesSingleComparison x hR).equiv M hM K i)

/-- Express type as R-module length; this avoids choosing an identification of residue fields. -/
lemma residueExt_length (M : ModuleCat.{u} R) [Module.Finite R M] (i : ℕ) :
    Module.length R (Depth.ResidueExt M i) =
      (Module.finrank (IsLocalRing.ResidueField R) (Depth.ResidueExt M i) : ℕ∞) := by
  haveI : Module.Finite (IsLocalRing.ResidueField R) (Depth.ResidueExt M i) :=
    Module.Finite.of_restrictScalars_finite R _ _
  rw [Module.length_eq_of_surjective (IsLocalRing.residue_surjective (R := R)),
    Module.length_eq_finrank]

/-- Reduction by a common regular element preserves maximal CM modules. -/
lemma maximalCM_quotient (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (hM : MaximalCohenMacaulay R M)
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hR : IsSMulRegular R x) (hreg : IsSMulRegular M x) :
    letI := principalQuotientLocalRing x hx
    Nontrivial (M ⧸ (Ideal.span {x} • (⊤ : Submodule R M))) ∧
      MaximalCohenMacaulay (R ⧸ Ideal.span {x})
        (M ⧸ (Ideal.span {x} • (⊤ : Submodule R M))) := by
  letI := principalQuotientLocalRing x hx
  let Q := R ⧸ Ideal.span {x}
  let U := M ⧸ (Ideal.span {x} • (⊤ : Submodule R M))
  haveI : Nontrivial U := quotient_nontrivial R M (Ideal.span {x})
    (Ideal.span_le.mpr (by simpa using hx))
  haveI : Nontrivial (QuotSMulTop x M) := (dimension_quotient_regular R M x hx hreg).1
  let e : QuotSMulTop x M ≃ₗ[R] U :=
    Depth.principalQuotientEquiv (ModuleCat.of R M) x
  have hloc : LocalCohenMacaulay R U :=
    (localCohenMacaulay_congr e).mp
      ((localCohenMacaulay_quotient_regular R M x hx hreg).mp (maximalCM_dimension M hM).2)
  have hlocQ : LocalCohenMacaulay Q U :=
    (localCohenMacaulay_of_surjective_iff U Ideal.Quotient.mk_surjective).mp hloc
  have hd : dimension R U + 1 = ringKrullDim R := by
    rw [dimension, ← Module.supportDim_eq_of_equiv e]
    exact (dimension_quotient_regular R M x hx hreg).2.trans (maximalCM_dimension M hM).1
  rw [dimension_of_surjective U (S := Q) Ideal.Quotient.mk_surjective] at hd
  have hfull : dimension Q U = ringKrullDim Q :=
    ENat.WithBot.add_one_cancel.mp
      (hd.trans (ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hR hx).symm)
  refine ⟨inferInstance, (maximalCohenMacaulay_iff_depth_eq Q U).mpr ?_⟩
  exact ((localCohenMacaulay_iff_depth_eq Q U).mp hlocQ).trans hfull

/-- Type is unchanged by a common regular element on a nonzero MCM module. -/
lemma moduleType_quotient_maximalCM (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (hM : MaximalCohenMacaulay R M)
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hR : IsSMulRegular R x) (hreg : IsSMulRegular M x) :
    letI := principalQuotientLocalRing x hx
    Depth.moduleType (R ⧸ Ideal.span {x}) (Depth.Rees.quotientModule (Ideal.span {x})
      (ModuleCat.of R M)) = Depth.moduleType R (ModuleCat.of R M) := by
  letI := principalQuotientLocalRing x hx
  let Q := R ⧸ Ideal.span {x}
  let U := Depth.Rees.quotientModule (Ideal.span {x}) (ModuleCat.of R M)
  have ht := maximalCM_quotient M hM x hx hR hreg
  haveI : Nontrivial U := ht.1
  have hdR := (maximalCohenMacaulay_iff_sourceDepth R M).mp hM
  have hdQ := (maximalCohenMacaulay_iff_sourceDepth Q U).mp ht.2
  have hd : Depth.depthDegree R (ModuleCat.of R M) = Depth.depthDegree Q U + 1 := by
    have he := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hR hx
    rw [← hdR, ← hdQ, ← (Depth.depth_finite R (ModuleCat.of R M)).2,
      ← (Depth.depth_finite Q U).2] at he
    exact_mod_cast he.symm
  have e := residueExtQuotientEquiv x hx hR (ModuleCat.of R M) hreg (Depth.depthDegree Q U)
  have hl := e.length_eq
  have hchange : Module.length R (Depth.ResidueExt U (Depth.depthDegree Q U)) =
      Module.length Q (Depth.ResidueExt U (Depth.depthDegree Q U)) :=
    Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
  rw [residueExt_length, hchange, residueExt_length] at hl
  unfold Depth.moduleType
  rw [hd]
  exact_mod_cast hl.symm

/-- Eventual residue-field Ext vanishing descends to the actual quotient module. -/
lemma finiteInjectiveDimension_quotient (M : ModuleCat.{u} R) [Module.Finite R M]
    (hfinite : FiniteInjectiveDimension R M)
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hR : IsSMulRegular R x) (hM : IsSMulRegular M x) :
    letI := principalQuotientLocalRing x hx
    FiniteInjectiveDimension (R ⧸ Ideal.span {x})
      (Depth.Rees.quotientModule (Ideal.span {x}) M) := by
  letI := principalQuotientLocalRing x hx
  let Q := R ⧸ Ideal.span {x}
  let U := Depth.Rees.quotientModule (Ideal.span {x}) M
  obtain ⟨n, hn⟩ := (finiteInjectiveDimension_iff_exists_bound R M).mp hfinite
  have hvan := (InjectiveDimensionTest.injectiveDimension_le_iff_residue_ext R M n).mp
    ((injectiveDimension_le_iff M n).mpr hn)
  have hbound : injectiveDimension U ≤ (n : WithBot ℕ∞) :=
    (InjectiveDimensionTest.injectiveDimension_le_iff_residue_ext Q U n).mpr (by
      intro i hi
      haveI := hvan (i + 1) (by omega)
      exact (residueExtQuotientEquiv x hx hR M hM i).symm.injective.subsingleton)
  exact ne_top_of_le_ne_top
    (ne_of_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top n))) hbound

/-- A common regular element in the maximal ideal reduces every canonical module. -/
theorem canonical_quotient_of_regular (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (hM : IsCanonicalModule R M)
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hR : IsSMulRegular R x) (hreg : IsSMulRegular M x) :
    letI := principalQuotientLocalRing x hx
    IsCanonicalModule (R ⧸ Ideal.span {x})
      (M ⧸ (Ideal.span {x} • (⊤ : Submodule R M))) := by
  letI := principalQuotientLocalRing x hx
  haveI : Nontrivial M := hM.2.1
  have hCM : LocalCohenMacaulay (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x}) := by
    have heq : x • (⊤ : Submodule R R) = (Ideal.span {x} : Submodule R R) := by
      rw [← Submodule.ideal_span_singleton_smul]
      exact Ideal.mul_top _
    have e : QuotSMulTop x R ≃ₗ[R] (R ⧸ Ideal.span {x}) :=
      Submodule.quotEquivOfEq _ _ heq
    have hloc := (localCohenMacaulay_quotient_regular R R x hx hR).mp hM.1
    have hn := (dimension_quotient_regular R R x hx hR).1
    haveI := hn
    have hloc' := (localCohenMacaulay_congr e).mp hloc
    exact (localCohenMacaulay_of_surjective_iff _ Ideal.Quotient.mk_surjective).mp hloc'
  have hU := maximalCM_quotient M hM.2.2.1 x hx hR hreg
  refine ⟨hCM, hU.1, hU.2, ?_, ?_⟩
  · exact (moduleType_quotient_maximalCM M hM.2.2.1 x hx hR hreg).trans hM.2.2.2.1
  · exact finiteInjectiveDimension_quotient (ModuleCat.of R M) hM.2.2.2.2 x hx hR hreg

/-- GC-11: the first element of any nonempty system of parameters reduces a canonical module. -/
theorem canonical_reduction : Specs.canonical_reductionType.{u} := by
  intro R _ _ _ _ M _ _ _ hM x xs hsop
  haveI : Nontrivial M := hM.2.1
  have hR : IsSMulRegular R x := by
    have hreg := (localCohenMacaulay_iff_every_systemOfParameters_regular R).mp hM.1
      (x :: xs) hsop
    exact (RingTheory.Sequence.isRegular_cons_iff R x xs).mp hreg |>.1
  have hreg := firstParameter_regular_maximalCM M hM.2.2.1 x xs hsop
  exact canonical_quotient_of_regular M hM x (hsop.1 x (by simp)) hR hreg

end AdvCommAlg.Gorenstein
