import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.SplittingSystem
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.StableLattices
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-! Stable lattices and the two scalar changes used in modular reduction. -/

namespace RepTheorySurvey.Modular

open Module
open scoped Pointwise TensorProduct nonZeroDivisors

abbrev StableLattice := @MR04LatticeSpec.LatticeData
abbrev NativeStableLattice := MR04LatticeSpec.NativeLatticeData
abbrev ResidueQuotient := MR04LatticeSpec.ResidueQuotient
abbrev integralLatticeAction := @MR04LatticeSpec.integralAction
abbrev reduce := @MR04LatticeSpec.reduce
noncomputable abbrev reduceMap := @MR04LatticeSpec.reduceMap
noncomputable abbrev residueRepresentation := @MR04LatticeSpec.residueAction
noncomputable abbrev residueModule := @MR04LatticeSpec.residueModule
noncomputable abbrev NativeStableLattice.reduction := @MR04LatticeSpec.nativeReduction
abbrev toFractionSpan := @MR04LatticeSpec.toFractionSpan

theorem exists_stableLattice : MR04LatticeSpec.existsLattice := by
  intro O _ _ _ K _ _ _ G _ _ V _ _ _ _ _ ρ
  classical
  let b := Module.finBasis K V
  let L₀ : Submodule O V := Submodule.span O (Set.range b)
  let A : G → V →ₗ[O] V := fun g => (ρ g).restrictScalars O
  let L : Submodule O V := ⨆ g, L₀.map (A g)
  have hfg : L.FG :=
    Submodule.fg_iSup _ fun g => (Submodule.fg_span (Set.finite_range b)).map (A g)
  have h₀ : L₀ ≤ L := by
    have h := le_iSup (fun g => L₀.map (A g)) (1 : G)
    have h1 : A 1 = LinearMap.id := by ext x; simp [A]
    simpa [h1, L] using h
  have hspan : Submodule.span K (L : Set V) = ⊤ := by
    apply top_le_iff.mp
    rw [← b.span_eq]
    exact Submodule.span_le.mpr fun x hx => Submodule.subset_span (h₀ (Submodule.subset_span hx))
  have hstable (g : G) : L.map (A g) ≤ L := by
    rw [Submodule.map_iSup]
    refine iSup_le fun h => ?_
    rw [← Submodule.map_comp]
    have hcomp : (A g).comp (A h) = A (g * h) := by ext v; simp [A]
    rw [hcomp]
    exact le_iSup (fun t => L₀.map (A t)) (g * h)
  have : Module.Finite O L := Module.Finite.iff_fg.mpr hfg
  have : FaithfulSMul O K :=
    (faithfulSMul_iff_algebraMap_injective O K).mpr (IsFractionRing.injective O K)
  have : Module.IsTorsionFree O V := .trans_faithfulSMul O K V
  exact ⟨⟨L, inferInstance, Module.free_iff_isTorsionFree.mpr inferInstance, hspan,
    fun g _ hx => hstable g (Submodule.mem_map_of_mem hx)⟩⟩

theorem exists_nativeStableLattice : MR04LatticeSpec.existsNativeLattice := by
  intro O _ _ _ K _ _ G _ _ p S V _ _ _
  let W := RestrictScalars K (MonoidAlgebra K G) V
  let kModule : Module K W := RestrictScalars.module K (MonoidAlgebra K G) V
  let oModule := Module.restrictScalars O K W
  have tower := IsScalarTower.restrictScalars O K W
  exact @exists_stableLattice O _ _ _ K _ _ S.fractionRing G _ _ W _
    kModule oModule tower ‹Module.Finite K W› (moduleRepresentation K G V)

theorem residue_is_uniformizerQuotient : MR04LatticeSpec.residueIsUniformizerQuotient := by
  intro O _ _ _ K _ _ G _ _ p S M _ _
  rw [S.maximalIdeal_eq_span, Submodule.ideal_span_singleton_smul]

@[simp]
theorem residueRepresentation_reduce : MR04LatticeSpec.residueActionOnClasses := by
  intro O _ _ G _ M _ _ σ g x
  rfl

theorem residue_baseChange : MR04LatticeSpec.residueBaseChange := by
  intro O _ _ M _ _
  let I := IsLocalRing.maximalIdeal O
  let e : ((O ⧸ I) ⊗[O] M) ≃ₗ[O ⧸ I] (M ⧸ (I • (⊤ : Submodule O M))) :=
    (TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
      (Ideal.Quotient.mk_surjective (I := I))
  let ek : (IsLocalRing.ResidueField O ⊗[O] M) ≃ₗ[IsLocalRing.ResidueField O]
      ResidueQuotient O M := e
  exact IsBaseChange.of_equiv ek fun x => TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul I x

theorem fractionSpan_baseChange : MR04LatticeSpec.fractionSpanBaseChange := by
  intro O _ _ K _ _ _ V _ _ _ _ L
  let f : V →ₗ[O] V := LinearMap.id
  have : IsLocalizedModule O⁰ f := isLocalizedModule_id O⁰ V K
  have hspan : L.localized' K O⁰ f = Submodule.span K (L : Set V) := by
    rw [Submodule.localized'_eq_span]
    simp [f]
  let e := (IsLocalizedModule.isBaseChange O⁰ K (L.toLocalized' K O⁰ f)).equiv
  let e' := LinearEquiv.ofEq _ _ hspan
  refine IsBaseChange.of_equiv (e.trans e') fun x => ?_
  change e' (e (1 ⊗ₜ[O] x)) = toFractionSpan (K := K) L x
  simp only [e, IsBaseChange.equiv_tmul, one_smul]
  apply Subtype.ext
  rfl

theorem finrank_residueQuotient : MR04LatticeSpec.finrankResidue := by
  intro O _ _ _ M _ _ _ _
  rw [← (residue_baseChange M).equiv.finrank_eq, Module.finrank_baseChange]

theorem finrank_fractionSpan : MR04LatticeSpec.finrankFractionSpan := by
  intro O _ _ K _ _ _ V _ _ _ _ L
  exact (fractionSpan_baseChange L).finrank_eq

theorem StableLattice.baseChange : MR04LatticeSpec.latticeBaseChange := by
  intro O _ _ K _ _ _ G _ V _ _ _ _ ρ L
  let e := (fractionSpan_baseChange (K := K) L.carrier).equiv
  let e' := (LinearEquiv.ofEq _ _ L.spans).trans Submodule.topEquiv
  refine IsBaseChange.of_equiv (e.trans e') fun x => ?_
  change e' (e (1 ⊗ₜ[O] x)) = (x : V)
  simp only [e, IsBaseChange.equiv_tmul, one_smul]
  rfl

theorem StableLattice.finrank_eq : MR04LatticeSpec.latticeFinrank := by
  intro O _ _ _ K _ _ _ G _ V _ _ _ _ ρ L
  have := L.finite
  have := L.free
  exact ⟨(StableLattice.baseChange L).finrank_eq, finrank_residueQuotient L.carrier⟩

@[simp]
theorem reduceMap_reduce : MR04LatticeSpec.reduceMapOnClasses := by
  intro O _ _ M _ _ N _ _ f x
  rfl

theorem residueRepresentation_algebra_reduce : MR04LatticeSpec.residueActionOnAlgebra := by
  intro O _ _ G _ M _ _ σ a x
  change (residueRepresentation σ).asAlgebraHom (groupAlgebraReduction O G a)
    (reduce (O := O) x) = reduce (O := O) (σ.asAlgebraHom a x)
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    rw [show groupAlgebraReduction O G (MonoidAlgebra.of O G g) =
        MonoidAlgebra.of (IsLocalRing.ResidueField O) G g by
          simp [MonoidAlgebra.of_apply, groupAlgebraReduction]]
    rw [Representation.asAlgebraHom_of, Representation.asAlgebraHom_of]
    exact residueRepresentation_reduce σ g x
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb]
  | smul r a ha =>
    have hd : groupAlgebraReduction O G (r • a) =
        IsLocalRing.residue O r • groupAlgebraReduction O G a := by
      simp [Algebra.smul_def, groupAlgebraReduction, MonoidAlgebra.coe_algebraMap]
    rw [hd, map_smul, LinearMap.smul_apply, ha, map_smul, LinearMap.smul_apply, map_smul]
    rfl

end RepTheorySurvey.Modular
