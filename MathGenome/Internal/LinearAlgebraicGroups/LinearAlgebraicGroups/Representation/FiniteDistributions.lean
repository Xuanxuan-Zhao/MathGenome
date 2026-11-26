import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FiniteDistributions
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RelativeFrobenius
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dual.Basis
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Coalgebra WithConv LinearMap
open scoped TensorProduct

universe u v w z

namespace LinearAlgebraicGroups.FiniteDistributions

noncomputable section

variable {k : Type u} [Field k]
variable {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable {W : Type z} [AddCommGroup W] [Module k W]

private def tensorEvaluation : V ⊗[k] C →ₗ[k] Dist k C →ₗ[k] V :=
  (WithConv.linearEquiv k (Module.Dual k C)).toLinearMap.lcomp k V ∘ₗ
    dualTensorHom k (Module.Dual k C) V ∘ₗ
    (Module.Dual.eval k C).rTensor V ∘ₗ (TensorProduct.comm k V C).toLinearMap

omit [Coalgebra k C] in
private theorem tensorEvaluation_apply (t : V ⊗[k] C) (a : Dist k C) :
    tensorEvaluation t a = pair a t := by
  induction t using TensorProduct.inductionOn with
  | tmul x c => simp [tensorEvaluation, dualTensorHom_apply]
  | add s t hs ht => simp [hs, ht]

private def tensorEvaluationEquiv [Module.Finite k C] :
    V ⊗[k] C ≃ₗ[k] (Dist k C →ₗ[k] V) :=
  TensorProduct.comm k V C ≪≫ₗ
    TensorProduct.congr (Module.evalEquiv k C) (LinearEquiv.refl k V) ≪≫ₗ
    dualTensorHomEquiv k (Module.Dual k C) V ≪≫ₗ
    LinearEquiv.arrowCongr (WithConv.linearEquiv k (Module.Dual k C)).symm
      (LinearEquiv.refl k V)

omit [Coalgebra k C] in
private theorem tensorEvaluationEquiv_apply [Module.Finite k C] (t : V ⊗[k] C) (a : Dist k C) :
    tensorEvaluationEquiv t a = pair a t := by
  induction t using TensorProduct.inductionOn with
  | tmul x c => simp [tensorEvaluationEquiv]
  | add s t hs ht => simp [hs, ht]

omit [Coalgebra k C] in
private theorem tensor_ext [Module.Finite k C] {s t : V ⊗[k] C}
    (h : ∀ a : Dist k C, pair a s = pair a t) : s = t :=
  tensorEvaluationEquiv.injective (LinearMap.ext fun a => by
    simpa only [tensorEvaluationEquiv_apply] using h a)

omit [Coalgebra k C] in
private theorem pair_rTensor {W : Type z} [AddCommGroup W] [Module k W]
    (a : Dist k C) (f : V →ₗ[k] W) (t : V ⊗[k] C) :
    pair a (f.rTensor C t) = f (pair a t) := by
  induction t using TensorProduct.inductionOn with
  | tmul x c => simp
  | add s t hs ht => simp [hs, ht]

private def pairThree (a b : Dist k C) : V ⊗[k] (C ⊗[k] C) →ₗ[k] V :=
  pair a ∘ₗ pair b ∘ₗ (TensorProduct.assoc k V C C).symm.toLinearMap

omit [Coalgebra k C] in
private theorem pairThree_assoc (δ : V →ₗ[k] V ⊗[k] C) (a b : Dist k C) (t : V ⊗[k] C) :
    pairThree a b (TensorProduct.assoc k V C C (δ.rTensor C t)) =
      pair a (δ (pair b t)) := by
  simp [pairThree, pair_rTensor]

private theorem pairThree_comul (a b : Dist k C) (t : V ⊗[k] C) :
    pairThree a b ((Coalgebra.comul (R := k) (A := C)).lTensor V t) = pair (a * b) t := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul x c =>
    simp only [lTensor_tmul, pair_tmul, convMul_apply]
    generalize Coalgebra.comul (R := k) c = y
    induction y using TensorProduct.inductionOn with
    | tmul c d => simp [pairThree, smul_smul, mul_comm]
    | add s t hs ht => simp only [TensorProduct.tmul_add, map_add, add_smul, hs, ht]

private theorem pair_one (t : V ⊗[k] C) :
    pair (1 : Dist k C) t =
      TensorProduct.rid k V ((Coalgebra.counit (R := k) (A := C)).lTensor V t) := by
  have h : (1 : Dist k C).ofConv = Coalgebra.counit := by
    ext c
    simp [convOne_apply]
  rw [pair, h]
  rfl

/-- A right coaction gives a left action of the convolution algebra, even before
imposing a finiteness hypothesis on the coalgebra. -/
def toAction (ρ : RightComodule k C V) : LeftAction k C V :=
  AlgHom.ofLinearMap (tensorEvaluation.comp ρ.coaction).flip
    (by
      ext x
      change tensorEvaluation (ρ.coaction x) 1 = x
      rw [tensorEvaluation_apply, pair_one, ρ.counit])
    (by
      intro a b
      ext x
      change tensorEvaluation (ρ.coaction x) (a * b) =
        tensorEvaluation (ρ.coaction (tensorEvaluation (ρ.coaction x) b)) a
      simp only [tensorEvaluation_apply]
      rw [← pairThree_comul, ← ρ.coassoc, pairThree_assoc])

theorem toAction_pairs (ρ : RightComodule k C V) : PairsWith ρ (toAction ρ) :=
  fun a x => tensorEvaluation_apply (ρ.coaction x) a

/-- Reconstruct the coaction by finite-dimensional duality on the coalgebra. -/
def toComodule [Module.Finite k C] (μ : LeftAction k C V) : RightComodule k C V := by
  let δ : V →ₗ[k] V ⊗[k] C :=
    tensorEvaluationEquiv.symm.toLinearMap.comp μ.toLinearMap.flip
  have hδ (a : Dist k C) (x : V) : pair a (δ x) = μ a x := by
    rw [← tensorEvaluationEquiv_apply]
    change tensorEvaluationEquiv (tensorEvaluationEquiv.symm (μ.toLinearMap.flip x)) a = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  refine ⟨δ, ?_, ?_⟩
  · intro x
    apply (TensorProduct.assoc k V C C).symm.injective
    apply tensor_ext
    intro b
    apply tensor_ext
    intro a
    change pairThree a b (TensorProduct.assoc k V C C (δ.rTensor C (δ x))) =
      pairThree a b ((Coalgebra.comul (R := k) (A := C)).lTensor V (δ x))
    rw [pairThree_assoc, pairThree_comul, hδ, hδ, hδ, map_mul]
    rfl
  · intro x
    rw [← pair_one, hδ, map_one]
    rfl

theorem toComodule_pairs [Module.Finite k C] (μ : LeftAction k C V) :
    PairsWith (toComodule μ) μ := by
  intro a x
  rw [← tensorEvaluationEquiv_apply]
  change μ a x = tensorEvaluationEquiv (tensorEvaluationEquiv.symm (μ.toLinearMap.flip x)) a
  rw [LinearEquiv.apply_symm_apply]
  rfl

private theorem eq_action_of_pairs {ρ : RightComodule k C V} {μ ν : LeftAction k C V}
    (hμ : PairsWith ρ μ) (hν : PairsWith ρ ν) : μ = ν := by
  ext a x
  exact (hμ a x).trans (hν a x).symm

private theorem eq_comodule_of_pairs [Module.Finite k C] {ρ σ : RightComodule k C V}
    {μ : LeftAction k C V} (hρ : PairsWith ρ μ) (hσ : PairsWith σ μ) : ρ = σ := by
  have h : ρ.coaction = σ.coaction :=
    LinearMap.ext fun x => tensor_ext fun a => (hρ a x).symm.trans (hσ a x)
  cases ρ
  cases σ
  cases h
  rfl

/-- The comparison fixes the underlying vector space and is inverse in both directions. -/
def comoduleActionEquiv [Module.Finite k C] : RightComodule k C V ≃ LeftAction k C V where
  toFun := toAction
  invFun := toComodule
  left_inv ρ := eq_comodule_of_pairs (toComodule_pairs _) (toAction_pairs ρ)
  right_inv μ := eq_action_of_pairs (toAction_pairs _) (toComodule_pairs μ)

theorem comoduleModuleComparison : Specs.FiniteDistributions.ComoduleModuleComparison.{u,v,w} := by
  intro k _ C _ _ _ _ V _ _
  refine ⟨comoduleActionEquiv, fun ρ μ => ⟨?_, ?_⟩⟩
  · rintro rfl
    exact toAction_pairs ρ
  · exact eq_action_of_pairs (toAction_pairs ρ)

/-- The algebra action induces a left module structure with the given field scalars. -/
def moduleStructure (μ : LeftAction k C V) : CompatibleModule k C V where
  module := Module.compHom V μ.toRingHom
  tower := by
    let := Module.compHom V μ.toRingHom
    apply IsScalarTower.of_algebraMap_smul
    intro r x
    change μ (algebraMap k (Dist k C) r) x = r • x
    rw [AlgHom.commutes]
    rfl

/-- Scalar multiplication in a compatible left module gives its linear action. -/
def linearAction (M : CompatibleModule k C V) : LeftAction k C V := by
  letI := M.module
  letI := M.tower
  letI : SMulCommClass (Dist k C) k V :=
    ⟨fun a r x => by
      calc
        a • (r • x) = a • ((algebraMap k (Dist k C) r) • x) := by
          rw [IsScalarTower.algebraMap_smul]
        _ = ((algebraMap k (Dist k C) r) * a) • x := by
          rw [← mul_smul, Algebra.commutes r a]
        _ = r • (a • x) := by rw [mul_smul, IsScalarTower.algebraMap_smul]⟩
  exact Algebra.lsmul k k V

/-- Compatible modules and actions by linear endomorphisms are the same structures. -/
def actionModuleEquiv : LeftAction k C V ≃ CompatibleModule k C V where
  toFun := moduleStructure
  invFun := linearAction
  left_inv μ := AlgHom.ext fun a => LinearMap.ext fun x => rfl
  right_inv M := by
    have h := Module.ext' (moduleStructure (linearAction M)).module M.module (fun _ _ => rfl)
    cases M
    cases h
    rfl

theorem moduleStructureComparison : Specs.FiniteDistributions.ModuleStructureComparison.{u,v,w} := by
  intro k _ C _ _ _ V _ _
  exact ⟨actionModuleEquiv, fun _ _ _ => rfl⟩

/-- An equivalence with actual left module structures on the fixed vector space. -/
def comoduleModuleEquiv [Module.Finite k C] : RightComodule k C V ≃ CompatibleModule k C V :=
  comoduleActionEquiv.trans actionModuleEquiv

theorem morphismComparison : Specs.FiniteDistributions.MorphismComparison.{u,v,w,z} := by
  intro k _ C _ _ _ _ V _ _ W _ _ ρ σ μ ν hμ hν f
  constructor
  · intro h a x
    rw [hμ, hν, ← pair_rTensor, h x]
  · intro h x
    apply tensor_ext
    intro a
    rw [pair_rTensor, ← hμ, ← hν, h]

section FiniteCategories

variable [Module.Finite k C]

/-- The comparison functor sends a coaction to its left distribution action
and keeps the underlying linear maps. -/
def finiteComoduleFunctor :
    FiniteRightComodule.{u,v,w} k C ⥤ FiniteLeftModule.{u,v,w} k C where
  obj X := ⟨X.space, X.finite, comoduleModuleEquiv X.comodule⟩
  map {X Y} f :=
    ⟨f.1, (morphismComparison X.comodule Y.comodule _ _
      (toAction_pairs _) (toAction_pairs _) f.1).mp f.2⟩

theorem finiteComoduleFunctor_isEquivalence :
    (finiteComoduleFunctor.{u,v,w} (k := k) (C := C)).IsEquivalence := by
  let F : FiniteRightComodule.{u,v,w} k C ⥤ FiniteLeftModule.{u,v,w} k C :=
    finiteComoduleFunctor
  let ff : F.FullyFaithful :=
    { preimage := fun {X Y} f =>
        ⟨f.1, (morphismComparison X.comodule Y.comodule _ _
          (toAction_pairs _) (toAction_pairs _) f.1).mpr f.2⟩
      map_preimage := fun _ => rfl
      preimage_map := fun _ => rfl }
  refine ⟨ff.faithful, ff.full, ⟨fun Y => ?_⟩⟩
  obtain ⟨ρ, hρ⟩ := comoduleModuleEquiv.surjective Y.action
  let X : FiniteRightComodule k C := ⟨Y.space, Y.finite, ρ⟩
  have h : F.obj X = Y :=
    congrArg (fun action => FiniteLeftModule.mk Y.space Y.finite action) hρ
  exact ⟨X, ⟨eqToIso h⟩⟩

theorem finiteCategoriesComparison : Specs.FiniteDistributions.FiniteCategoriesComparison.{u,v,w} := by
  intro k _ C _ _ _ _
  exact ⟨finiteComoduleFunctor, finiteComoduleFunctor_isEquivalence, rfl⟩

end FiniteCategories

theorem subobjectComparison : Specs.FiniteDistributions.SubobjectComparison.{u,v,w} := by
  intro k _ C _ _ _ _ V _ _ ρ μ hμ U
  constructor
  · intro h a x
    obtain ⟨t, ht⟩ := h x
    rw [hμ, ← ht, pair_rTensor]
    exact (pair a t).property
  · intro h x
    let b := Module.finBasis k C
    let t : U ⊗[k] C := ∑ j, (⟨μ (toConv (b.coord j)) x, h _ x⟩ : U) ⊗ₜ[k] b j
    refine ⟨t, ?_⟩
    apply tensor_ext
    intro a
    have his : ∑ j, a.ofConv (b j) • toConv (b.coord j) = a := by
      apply WithConv.ofConv_injective
      simpa only [ofConv_sum, ofConv_smul, ofConv_toConv, Module.Basis.coe_dualBasis, Module.Basis.dualBasis_repr] using
        b.dualBasis.sum_repr a.ofConv
    rw [← hμ a x, ← his]
    simp [t]

theorem distributionMultiplication : Specs.FiniteDistributions.DistributionMultiplication.{u} := by
  intro k _ A _
  exact ⟨Module.Finite.equiv (WithConv.linearEquiv k (Module.Dual k A)).symm,
    fun f g a => rfl, fun a => by simp [convOne_apply]⟩


section Restriction

variable {D : Type z} [AddCommGroup D] [Module k D] [Coalgebra k D]

/-- Corestrict a coaction along a coalgebra homomorphism. For coordinate maps
this is restriction of group scheme representations. -/
def restrict (g : C →ₗc[k] D) (ρ : RightComodule k C V) : RightComodule k D V where
  coaction := g.toLinearMap.lTensor V ∘ₗ ρ.coaction
  coassoc x := by
    have h₁ (t : V ⊗[k] C) :
        TensorProduct.assoc k V D D
          ((g.toLinearMap.lTensor V ∘ₗ ρ.coaction).rTensor D (g.toLinearMap.lTensor V t)) =
        (TensorProduct.map g.toLinearMap g.toLinearMap).lTensor V
          (TensorProduct.assoc k V C C (ρ.coaction.rTensor C t)) := by
      induction t using TensorProduct.inductionOn with
      | add s t hs ht => simp only [map_add, hs, ht]
      | tmul x c =>
        simp only [lTensor_tmul, rTensor_tmul, coe_comp, Function.comp_apply]
        generalize ρ.coaction x = t
        induction t using TensorProduct.inductionOn with
        | add s t hs ht => simp only [map_add, TensorProduct.add_tmul, hs, ht]
        | tmul y d => simp
    have h₂ (t : V ⊗[k] C) :
        (Coalgebra.comul (R := k) (A := D)).lTensor V (g.toLinearMap.lTensor V t) =
          (TensorProduct.map g.toLinearMap g.toLinearMap).lTensor V
            ((Coalgebra.comul (R := k) (A := C)).lTensor V t) := by
      induction t using TensorProduct.inductionOn with
      | add s t hs ht => simp only [map_add, hs, ht]
      | tmul x c => simp [CoalgHomClass.map_comp_comul_apply g c]
    change _ = (Coalgebra.comul (R := k) (A := D)).lTensor V
      (g.toLinearMap.lTensor V (ρ.coaction x))
    exact (h₁ _).trans (by rw [ρ.coassoc, ← h₂])
  counit x := by
    have h (t : V ⊗[k] C) :
        TensorProduct.rid k V ((Coalgebra.counit (R := k) (A := D)).lTensor V
          (g.toLinearMap.lTensor V t)) =
        TensorProduct.rid k V ((Coalgebra.counit (R := k) (A := C)).lTensor V t) := by
      induction t using TensorProduct.inductionOn with
      | add s t hs ht => simp only [map_add, hs, ht]
      | tmul x c => simp [CoalgHomClass.counit_comp_apply g c]
    exact (h _).trans (ρ.counit x)

theorem restrictionComparison : Specs.FiniteDistributions.RestrictionComparison.{u,v,w,z} := by
  intro k _ C _ _ _ D _ _ _ V _ _ g ρ μ hμ
  refine ⟨restrict g ρ, rfl, fun a x => ?_⟩
  change μ (distributionMap g a) x = pair a (g.toLinearMap.lTensor V (ρ.coaction x))
  rw [hμ]
  generalize ρ.coaction x = t
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul x c => rfl

end Restriction

section Frobenius

open Specs.RelativeFrobenius

open private liftSemilinear extAlong counit_tmul
  comulTensorMap comulTensorMap_tmul comul_tmul
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RelativeFrobenius

variable (p r : ℕ) [Fact p.Prime] [CharP k p]

private def frobeniusAlgHom (A : HopfAlgebraCategory k) :
    twistCoordinates k p r A →ₐ[k] A := by
  letI : Nontrivial A := (Bialgebra.counitAlgHom k A).toRingHom.domain_nontrivial
  letI : CharP A p := CharP.of_ringHom_of_ne_zero (algebraMap k A) p (Fact.out : p.Prime).ne_zero
  exact liftSemilinear (iterateFrobenius k p r) A A (iterateFrobenius A p r)
    (fun c => ((algebraMap k A).map_iterateFrobenius p c r).symm)

private theorem frobeniusAlgHom_tmul (A : HopfAlgebraCategory k) (c : k) (a : A) :
    frobeniusAlgHom p r A (scalarTensor (iterateFrobenius k p r) A c a) =
      c • a ^ (p ^ r) := rfl

/-- Pullback of the iterated relative Frobenius. The twist and the power both
use the same iterate of Frobenius. -/
def frobeniusPullback (A : HopfAlgebraCategory k) : twistCoordinates k p r A ⟶ A :=
  ⟨BialgHom.ofAlgHom (A := ↑(twistCoordinates k p r A)) (B := ↑A) (frobeniusAlgHom p r A)
    (by
      apply extAlong (iterateFrobenius k p r) A
      intro a
      rw [AlgHom.comp_apply, frobeniusAlgHom_tmul, one_smul, counit_tmul, map_pow,
        _root_.iterateFrobenius_def])
    (by
      apply extAlong (iterateFrobenius k p r) A
      intro a
      rw [AlgHom.comp_apply, AlgHom.comp_apply, frobeniusAlgHom_tmul, one_smul, comul_tmul, map_pow]
      generalize Bialgebra.comulAlgHom k A a = t
      let : Nontrivial (A ⊗[k] A) :=
        (Bialgebra.counitAlgHom k (A ⊗[k] A)).toRingHom.domain_nontrivial
      let : CharP (A ⊗[k] A) p :=
        CharP.of_ringHom_of_ne_zero (algebraMap k (A ⊗[k] A)) p (Fact.out : p.Prime).ne_zero
      change Algebra.TensorProduct.map (frobeniusAlgHom p r A) (frobeniusAlgHom p r A)
        (comulTensorMap (iterateFrobenius k p r) A t) = iterateFrobenius (A ⊗[k] A) p r t
      induction t using TensorProduct.inductionOn with
      | tmul a b =>
        rw [comulTensorMap_tmul, Algebra.TensorProduct.map_tmul, frobeniusAlgHom_tmul,
          frobeniusAlgHom_tmul, one_smul, one_smul, _root_.iterateFrobenius_def, Algebra.TensorProduct.tmul_pow]
      | add s t hs ht => simp only [map_add, hs, ht])⟩

theorem frobeniusPullback_formula (A : HopfAlgebraCategory k) :
    FrobeniusFormula k p r A (frobeniusPullback p r A) :=
  frobeniusAlgHom_tmul p r A

theorem relativeFrobenius : Specs.FiniteDistributions.RelativeFrobenius.{u} := by
  intro k _ p r _ _ A
  refine ⟨frobeniusPullback p r A, frobeniusPullback_formula p r A, fun f hf => ?_⟩
  apply CommHopfAlgCat.hom_ext
  have h : f.hom.toAlgHom = (frobeniusPullback p r A).hom.toAlgHom :=
    extAlong (iterateFrobenius k p r) A fun a =>
      (hf 1 a).trans ((frobeniusPullback_formula p r A) 1 a).symm
  exact BialgHom.ext (fun x => congrArg (fun g : twistCoordinates k p r A →ₐ[k] A => g x) h)

private theorem finite_kernel_of_formula (A : HopfAlgebraCategory k)
    (f : twistCoordinates k p r A ⟶ A) (hf : FrobeniusFormula k p r A f)
    (hA : Algebra.FiniteType k A) : Module.Finite k (A ⧸ Specs.kernelIdeal f) := by
  let B := twistCoordinates k p r A
  let σ := iterateFrobenius k p r
  let I := Specs.kernelIdeal f
  let π := Ideal.Quotient.mkₐ k I
  let ε := Bialgebra.counitAlgHom k B
  apply (Algebra.finite_iff_isIntegral_and_finiteType).mpr
  refine ⟨⟨?_⟩, Algebra.FiniteType.of_surjective π Ideal.Quotient.mk_surjective⟩
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) x
  let t := scalarTensor σ A 1 a
  have hz : t - algebraMap k B (ε t) ∈ Specs.augmentationIdeal B := by
    change ε (t - algebraMap k B (ε t)) = 0
    simp
  have hm : f.hom (t - algebraMap k B (ε t)) ∈ I :=
    Ideal.mem_map_of_mem f.hom.toAlgHom hz
  have hzero : π (f.hom (t - algebraMap k B (ε t))) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hm
  have hp : f.hom t = a ^ (p ^ r) := by simpa [t, σ] using hf 1 a
  have he : (π a) ^ (p ^ r) = algebraMap k (A ⧸ I) (ε t) := by
    have he' : π (f.hom t) - algebraMap k (A ⧸ I) (ε t) = 0 := by
      change π (f.hom.toAlgHom (t - algebraMap k B (ε t))) = 0 at hzero
      rw [map_sub, AlgHom.commutes, map_sub, AlgHom.commutes] at hzero
      exact hzero
    rw [hp, map_pow] at he'
    exact sub_eq_zero.mp he'
  apply IsIntegral.of_pow (Nat.pow_pos (Fact.out : p.Prime).pos)
  change IsIntegral k ((π a) ^ (p ^ r))
  rw [he]
  exact isIntegral_algebraMap

theorem frobeniusKernelComparison : Specs.FiniteDistributions.FrobeniusKernel.{u} := by
  intro k _ p r _ _ A f hf
  let h := hopfKernelIdeal k f
  exact ⟨h, (schemeKernel k f).1, (schemeKernel k f).2, finite_kernel_of_formula p r A f hf⟩

/-- Coordinate Hopf algebra of the scheme kernel of the iterated relative Frobenius. -/
def frobeniusKernelHopf (A : HopfAlgebraCategory k) : HopfAlgebraCategory k :=
  letI := hopfKernelIdeal k (frobeniusPullback p r A)
  hopfQuotient A (Specs.kernelIdeal (frobeniusPullback p r A))

/-- The group scheme `Gᵣ`, with its Hopf quotient model. -/
def frobeniusKernel (A : HopfAlgebraCategory k) : Specs.GroupScheme k :=
  specGroup (frobeniusKernelHopf p r A)

/-- Closed inclusion of the Frobenius kernel. -/
def frobeniusKernelInclusion (A : HopfAlgebraCategory k) :
    frobeniusKernel p r A ⟶ specGroup A :=
  letI := hopfKernelIdeal k (frobeniusPullback p r A)
  specGroupMap (hopfQuotientMap A (Specs.kernelIdeal (frobeniusPullback p r A)))

/-- The defining pullback of the Frobenius kernel in the category of group schemes. -/
theorem frobeniusKernel_isPullback (A : HopfAlgebraCategory k) :
    IsPullback (frobeniusKernelInclusion p r A)
      (specGroupMap (hopfUnit (frobeniusKernelHopf p r A)))
      (specGroupMap (frobeniusPullback p r A)) (specGroupMap (hopfCounit (twistCoordinates k p r A))) := by
  let h := hopfKernelIdeal k (frobeniusPullback p r A)
  exact (schemeKernel k (frobeniusPullback p r A)).1

instance (A : HopfAlgebraCategory k) [hA : Algebra.FiniteType k A] :
    Module.Finite k (frobeniusKernelHopf p r A) :=
  finite_kernel_of_formula p r A _ (frobeniusPullback_formula p r A) hA

end Frobenius

theorem finiteSpectrum : Specs.FiniteDistributions.FiniteSpectrum.{u} := by
  intro k _ A
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k A))) ↔ Module.Finite k A
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap

private theorem finite_of_groupIso {G K : Specs.GroupScheme k}
    (e : G ≅ K) (h : IsFinite K.X.hom) : IsFinite G.X.hom := by
  let F := Grp.forget (SchemeOver k)
  let i := F.mapIso e
  change IsFinite (F.obj G).hom
  rw [← Over.w i.hom]
  let : IsIso i.hom.left := (Over.forget _).map_isIso i.hom
  let : IsFinite (F.obj K).hom := h
  infer_instance

theorem finiteGroupPresentation : Specs.FiniteDistributions.FiniteGroupPresentation.{u} := by
  intro k _ K
  constructor
  · intro h
    let := h
    have hAff : IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom
    obtain ⟨A, ⟨e⟩⟩ := essImage_hopfSpec.mpr hAff
    exact ⟨A.unop, (finiteSpectrum k A.unop).mp (finite_of_groupIso e h), ⟨e⟩⟩
  · rintro ⟨A, hA, ⟨e⟩⟩
    exact finite_of_groupIso e.symm ((finiteSpectrum k A).mpr hA)

end
end LinearAlgebraicGroups.FiniteDistributions
