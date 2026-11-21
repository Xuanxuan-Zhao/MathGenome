import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FormalCharacters
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FormalCharacterDefinitions
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaWeightsUniversal
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeightStringsConvexity
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Data.Finsupp.Multiset

noncomputable section

namespace LieAlgebrasAndRepresentations.FormalCharacters

open Specs.LieAlgebrasAndRepresentations.FormalCharacters
open Specs.LieAlgebrasAndRepresentations
open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
open Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
open Module SerreRelations HighestWeightData RootForm
open SolvableRadical (IsSemisimple_value)
open scoped BigOperators Classical Pointwise TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w z
variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Direction H)

private theorem simple_mem_cone (i : simple H φ) : i.val ∈ cone H φ :=
  Submodule.subset_span ⟨i, rfl⟩

private theorem upperCone_isPWO [Fintype (simple H φ)] (a : Exponent H φ) :
    (Set.Ici a).IsPWO := by
  let f : (simple H φ → ℕ) → Exponent H φ :=
    fun n => exponent H φ (((exponent H φ).symm a) - ∑ i, n i • i.val)
  have hf : Monotone f := by
    intro n m h
    change (((exponent H φ).symm a) - ∑ i, n i • i.val) -
      (((exponent H φ).symm a) - ∑ i, m i • i.val) ∈ cone H φ
    have hs : (∑ i : simple H φ, m i • i.val) =
        (∑ i : simple H φ, n i • i.val) + ∑ i : simple H φ, (m i - n i) • i.val := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [← add_nsmul, Nat.add_sub_of_le (h i)]
    rw [hs]
    rw [show (((exponent H φ).symm a) - ∑ i : simple H φ, n i • i.val) -
      ((exponent H φ).symm a - ((∑ i : simple H φ, n i • i.val) + ∑ i : simple H φ, (m i - n i) • i.val)) =
      ∑ i : simple H φ, (m i - n i) • i.val by abel]
    exact (cone H φ).sum_mem fun i _ => (cone H φ).smul_mem _ (simple_mem_cone H φ i)
  have hPWO : (Set.range f).IsPWO :=
    Set.image_univ ▸ (Set.isPWO_of_wellQuasiOrderedLE Set.univ).image_of_monotone hf
  refine hPWO.mono fun x hx => ?_
  change (exponent H φ).symm a - (exponent H φ).symm x ∈ cone H φ at hx
  obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℕ).mp hx
  refine ⟨n, ?_⟩
  change (exponent H φ).symm a - (∑ i : simple H φ, n i • i.val) = (exponent H φ).symm x
  rw [hn, sub_sub_cancel]

private theorem bounded_support_isPWO [Fintype (simple H φ)] {f : Exponent H φ → ℤ}
    (hf : Bounded H φ f) : (Function.support f).IsPWO := by
  obtain ⟨s, hs⟩ := hf
  have hp (s : Finset (Exponent H φ)) : {x | ∃ a ∈ s, a ≤ x}.IsPWO := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s _ ih =>
      have he : {x | ∃ b ∈ insert a s, b ≤ x} =
          Set.Ici a ∪ {x | ∃ b ∈ s, b ≤ x} := by
        ext x
        simp [Finset.mem_insert, or_and_right, exists_or]
      rw [he]
      exact (upperCone_isPWO H φ a).union ih
  exact (hp s).mono fun x hx => hs x hx

private theorem finite_positive [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]
    (hss : IsSemisimple_value ℂ L) : (positive H φ).Finite :=
  (rootSet_finite H (RealRootSpace.cartan_isMaximalToral hss H).1).subset
    (fun _ ha => ha.1)

theorem bounded_coefficients : bounded_coefficients_type.{u} := by
  intro L _ _ _ hss H _ φ f
  letI : Fintype (simple H φ) :=
    ((finite_positive H φ hss).subset (fun _ ha => ha.1)).fintype
  constructor
  · rintro ⟨x, hx⟩
    exact (show x.val.coeff = fun a => f ((exponent H φ).symm a) from funext hx) ▸ x.property
  · intro hf
    exact ⟨⟨⟨_, bounded_support_isPWO H φ hf⟩, hf⟩, fun _ => rfl⟩

theorem convolution : convolution_type.{u} := by
  intro L _ _ H φ f g η
  let s := Finset.antidiagonal f.val.isPWO_support g.val.isPWO_support (exponent H φ η)
  let e : Exponent H φ × Exponent H φ ≃ Module.Dual ℂ H × Module.Dual ℂ H :=
    Equiv.prodCongr (exponent H φ).symm.toEquiv (exponent H φ).symm.toEquiv
  refine ⟨s.map e.toEmbedding, ?_, ?_⟩
  · intro p
    obtain ⟨q, rfl⟩ := e.surjective p
    rw [Finset.mem_map_equiv]
    exact Finset.mem_antidiagonal
  · rw [Finset.sum_map]
    exact HahnSeries.coeff_mul

section Finite

variable [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]
variable (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
  [FiniteDimensional ℂ V]

@[simp] theorem finiteCharacter_coeff (a : Module.Dual ℂ H) :
    (finiteCharacter H V).coeff a = multiplicity H V a := rfl

@[simp] theorem character_coeff (a : integralWeights H φ) :
    (character H φ V).coeff a = multiplicity H V a.val := rfl

end Finite

theorem finiteCharacter_integral : finiteCharacter_integral_type.{u,v} := by
  intro L _ _ _ hss H _ φ V _ _ _ _ _ μ hμ
  have hW : weightSpace_value V H μ ≠ ⊥ := by
    intro h
    exact hμ (by simp [Specs.LieAlgebrasAndRepresentations.FormalCharacters.multiplicity, h])
  intro i
  exact FiniteModuleWeights.integral_weights hss (LieModule.toEnd ℂ L V) H
    (RealRootSpace.cartan_isMaximalToral hss H) μ hW i.val i.property.1.1

theorem weyl_invariance : weyl_invariance_type.{u,v} := by
  intro L _ _ _ hss H _ V _ _ _ _ _ w μ
  simp only [finiteCharacter_coeff, Specs.LieAlgebrasAndRepresentations.FormalCharacters.multiplicity]
  exact congrArg (fun n : ℕ => (n : ℤ))
    (WeightStringsConvexity.multiplicities hss (LieModule.toEnd ℂ L V) H
      (RealRootSpace.cartan_isMaximalToral hss H) w μ)

section WeightMaps

variable [H.IsCartanSubalgebra]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
variable {W : Type w} [AddCommGroup W] [Module ℂ W] [LieRingModule L W] [LieModule ℂ L W]
variable {X : Type z} [AddCommGroup X] [Module ℂ X] [LieRingModule L X] [LieModule ℂ L X]

private theorem mem_weight {a : Module.Dual ℂ H} {x : V} :
    x ∈ weightSpace_value V H a ↔ ∀ h : H, ⁅(h : L), x⁆ = a h • x :=
  LieModule.mem_weightSpace _ x

private theorem map_mem_weight (f : V →ₗ⁅ℂ,L⁆ W) {a : Module.Dual ℂ H}
    {x : V} (hx : x ∈ weightSpace_value V H a) :
    f x ∈ weightSpace_value W H a := by
  apply (mem_weight H).mpr
  intro h
  rw [← f.map_lie, (mem_weight H).mp hx h, map_smul]

private theorem mem_weight_of_map (f : V →ₗ⁅ℂ,L⁆ W) (hf : Function.Injective f)
    {a : Module.Dual ℂ H} {x : V} (hx : f x ∈ weightSpace_value W H a) :
    x ∈ weightSpace_value V H a := by
  apply (mem_weight H).mpr
  intro h
  apply hf
  rw [f.map_lie, map_smul]
  exact (mem_weight H).mp hx h

private theorem map_weightSpace_eq (f : V →ₗ⁅ℂ,L⁆ W) (hf : Function.Surjective f)
    (hint : DirectSum.IsInternal (weightSpace_value V H)) (a : Module.Dual ℂ H) :
    (weightSpace_value V H a).map f.toLinearMap = weightSpace_value W H a := by
  have hsub : (fun b => (weightSpace_value V H b).map f.toLinearMap) ≤ weightSpace_value W H := by
    rintro b _ ⟨x, hx, rfl⟩
    exact map_mem_weight H f hx
  have htop : (⨆ b, (weightSpace_value V H b).map f.toLinearMap) = ⊤ := by
    rw [← Submodule.map_iSup, hint.submodule_iSup_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hf
  exact congrFun ((weightSpaces_independent H W).le_iff_eq_of_iSup_eq_top htop |>.mp hsub) a

private def weightMap (f : V →ₗ⁅ℂ,L⁆ W) (a : Module.Dual ℂ H) :
    weightSpace_value V H a →ₗ[ℂ] weightSpace_value W H a :=
  (f.toLinearMap.comp (weightSpace_value V H a).subtype).codRestrict _
    (fun x => map_mem_weight H f x.property)

private theorem finite_weightSpaces_internal [FiniteDimensional ℂ L]
    (hss : IsSemisimple_value ℂ L) [FiniteDimensional ℂ V] :
    DirectSum.IsInternal (weightSpace_value V H) := by
  let hT := (RealRootSpace.cartan_isMaximalToral hss H).1
  letI : IsLieAbelian H := hT.1
  exact RepresentationJordan.toral_weight_decomposition ℂ L V hss (LieModule.toEnd ℂ L V) H
    (fun x y => trivial_lie_zero H H x y)
    (fun x => (absolutely_semisimple_iff _).mpr (hT.2 x))

theorem additivity : additivity_type.{u,v,w,z} := by
  intro L _ _ _ hss H _ φ V _ _ _ _ _ W _ _ _ _ _ X _ _ _ _ _ f g hf he hg
  ext a
  let fₐ := weightMap H f a.val
  let gₐ := weightMap H g a.val
  have hfₐ : Function.Injective fₐ := fun x y h =>
    Subtype.ext (hf (congrArg Subtype.val h))
  have hgₐ : Function.Surjective gₐ := by
    intro x
    have hx : (x : X) ∈ (weightSpace_value W H a.val).map g.toLinearMap :=
      (map_weightSpace_eq H g hg (finite_weightSpaces_internal H hss) a.val).symm ▸ x.property
    obtain ⟨y, hy, heq⟩ := hx
    exact ⟨⟨y, hy⟩, Subtype.ext heq⟩
  have heₐ : gₐ.ker = fₐ.range := by
    ext x
    change gₐ x = 0 ↔ ∃ y, fₐ y = x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := (he (x : W)).mp (congrArg Subtype.val hx)
      exact ⟨⟨y, mem_weight_of_map H f hf (hy ▸ x.property)⟩, Subtype.ext hy⟩
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      exact he.apply_apply_eq_zero _
  have hdim := gₐ.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hgₐ, finrank_top, heₐ,
    (LinearEquiv.ofInjective fₐ hfₐ).finrank_eq.symm] at hdim
  change multiplicity H W a.val = multiplicity H V a.val + multiplicity H X a.val
  unfold Specs.LieAlgebrasAndRepresentations.FormalCharacters.multiplicity
  exact_mod_cast ((add_comm _ _).trans hdim).symm

end WeightMaps

section WeightBasis

variable [H.IsCartanSubalgebra]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
variable {ι : Type w}

/-- An eigenbasis restricts to a basis of each weight space. -/
private def weightBasis (b : Basis ι ℂ V) (weight : ι → Module.Dual ℂ H)
    (hb : ∀ i, b i ∈ weightSpace_value V H (weight i)) (a : Module.Dual ℂ H) :
    Basis {i // weight i = a} ℂ (weightSpace_value V H a) := by
  let S (μ : Module.Dual ℂ H) :=
    Submodule.span ℂ (Set.range (fun i : {i // weight i = μ} => b i.val))
  have hS : S ≤ weightSpace_value V H := by
    intro μ
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, rfl⟩, rfl⟩
    exact hb i
  have htop : iSup S = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_iSup_of_mem (weight i) (Submodule.subset_span ⟨⟨i, rfl⟩, rfl⟩)
  have hEq := congrFun ((weightSpaces_independent H V).le_iff_eq_of_iSup_eq_top htop |>.mp hS) a
  exact (Basis.span (b.linearIndependent.comp _ Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ hEq)

private theorem finiteCharacter_eq_sum [FiniteDimensional ℂ V] [Fintype ι]
    (b : Basis ι ℂ V) (weight : ι → Module.Dual ℂ H)
    (hb : ∀ i, b i ∈ weightSpace_value V H (weight i)) :
    finiteCharacter H V = ∑ i, AddMonoidAlgebra.single (weight i) (1 : ℤ) := by
  ext a
  have hdim := Module.finrank_eq_card_basis (weightBasis H b weight hb a)
  change (Module.finrank ℂ (weightSpace_value V H a) : ℤ) =
    (∑ i, AddMonoidAlgebra.single (weight i) (1 : ℤ)).coeff a
  simp only [hdim, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  exact Fintype.card_subtype (fun i : ι => weight i = a)

end WeightBasis

section IntegralGroupRing

variable [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]
variable (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
  [FiniteDimensional ℂ V]

/-- The inclusion of the integral weight group ring into the full weight group ring. -/
def integralInclusion : IntegralGroupRing H φ →+* GroupRing H :=
  AddMonoidAlgebra.mapDomainRingHom ℤ (integralWeights H φ).subtype.toAddMonoidHom

private theorem integralInclusion_injective : Function.Injective (integralInclusion H φ) := by
  intro f g h
  apply AddMonoidAlgebra.ext
  exact Finsupp.mapDomain_injective Subtype.val_injective
    (congrArg AddMonoidAlgebra.coeff h)

theorem integralInclusion_character (hss : IsSemisimple_value ℂ L) :
    integralInclusion H φ (character H φ V) = finiteCharacter H V := by
  ext a
  change (Finsupp.mapDomain Subtype.val
    (Finsupp.subtypeDomain (fun a => a ∈ integralWeights H φ) (finiteCharacter H V).coeff)) a =
      (finiteCharacter H V).coeff a
  by_cases ha : a ∈ integralWeights H φ
  · exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨a, ha⟩
  · rw [Finsupp.mapDomain_of_notMem_range]
    · symm
      by_contra hn
      exact ha (finiteCharacter_integral hss H φ V a hn)
    · rintro ⟨i, rfl⟩
      exact ha i.property

/-- Ordinary Weyl reindexing fixes the finite character extended from the integral lattice. -/
theorem character_weyl_invariant (hss : IsSemisimple_value ℂ L)
    (w : Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights.weightWeylGroup H) :
    AddMonoidAlgebra.mapDomainRingHom ℤ w.val.toLinearMap.toAddMonoidHom
        (integralInclusion H φ (character H φ V)) =
      integralInclusion H φ (character H φ V) := by
  rw [integralInclusion_character H φ V hss]
  ext a
  obtain ⟨μ, rfl⟩ := w.val.surjective a
  change Finsupp.mapDomain w.val (finiteCharacter H V).coeff (w.val μ) =
    (finiteCharacter H V).coeff (w.val μ)
  rw [Finsupp.mapDomain_apply_of_injective w.val.injective]
  exact (weyl_invariance hss H V w μ).symm

end IntegralGroupRing

theorem multiplicativity : multiplicativity_type.{u,v,w} := by
  intro L _ _ _ hss H _ φ V _ _ _ _ _ W _ _ _ _ _
  let b := (finite_weightSpaces_internal (V := V) H hss).collectedBasis
    (fun a => Module.finBasis ℂ (weightSpace_value V H a))
  let c := (finite_weightSpaces_internal (V := W) H hss).collectedBasis
    (fun a => Module.finBasis ℂ (weightSpace_value W H a))
  letI := Module.Finite.finite_basis b
  letI := Module.Finite.finite_basis c
  letI := Fintype.ofFinite (Σ a : Module.Dual ℂ H, Fin (Module.finrank ℂ (weightSpace_value V H a)))
  letI := Fintype.ofFinite (Σ a : Module.Dual ℂ H, Fin (Module.finrank ℂ (weightSpace_value W H a)))
  have hb (i : _) : b i ∈ weightSpace_value V H i.1 := DirectSum.IsInternal.collectedBasis_mem _ _ _
  have hc (i : _) : c i ∈ weightSpace_value W H i.1 := DirectSum.IsInternal.collectedBasis_mem _ _ _
  have hbc (ij : _ × _) :
      b.tensorProduct c ij ∈ weightSpace_value (V ⊗[ℂ] W) H (ij.1.1 + ij.2.1) := by
    apply (mem_weight H).mpr
    intro h
    rw [Basis.tensorProduct_apply', TensorProduct.LieModule.lie_tmul_right,
      (mem_weight H).mp (hb ij.1) h, (mem_weight H).mp (hc ij.2) h,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    exact (add_smul (ij.1.1 h) (ij.2.1 h) (b ij.1 ⊗ₜ[ℂ] c ij.2)).symm
  apply integralInclusion_injective H φ
  rw [map_mul, integralInclusion_character H φ V hss, integralInclusion_character H φ W hss,
    integralInclusion_character H φ (V ⊗[ℂ] W) hss,
    finiteCharacter_eq_sum H b Sigma.fst hb, finiteCharacter_eq_sum H c Sigma.fst hc,
    finiteCharacter_eq_sum H (b.tensorProduct c) (fun ij => ij.1.1 + ij.2.1) hbc]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  simp only [Finset.mul_sum, AddMonoidAlgebra.single_mul_single, mul_one]

section SimpleCharacters

open IntegrableHighestWeightQuotient (IsDominant)
open private quotient_highest_ne_zero from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
open private positive_direction from MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FormalCharacterDefinitions

theorem independence : independence_type.{u} := by
  intro L _ _ _ hss H _ φ hφ χ hχ
  let D := {a : Module.Dual ℂ H // IsDominant H φ a}
  have finite (a : D) : FiniteDimensional ℂ (simpleQuotient_value H φ (χ a)) :=
    ((HighestWeightClassification.finite_simple_iff_dominant hss H φ hφ a.val (χ a) (hχ a)).mpr
      a.property).1
  let C (a : D) : IntegralGroupRing H φ :=
    letI := inducedLieRingModule H φ (χ a)
    letI := inducedLieModule H φ (χ a)
    letI := finite a
    character H φ (simpleQuotient_value H φ (χ a))
  let asIntegral (a : D) : integralWeights H φ := ⟨a.val, fun i => by
    obtain ⟨n, hn⟩ := a.property i
    exact ⟨n, by simpa using hn⟩⟩
  have hw (a b : D) : (C b).coeff (asIntegral a) ≠ 0 → b.val - a.val ∈ cone H φ := by
    letI := inducedLieRingModule H φ (χ b)
    letI := inducedLieModule H φ (χ b)
    obtain ⟨hint, _, hs, _⟩ := VermaWeightsUniversal.verma_weights hss H φ hφ b.val (χ b) (hχ b)
    have hm := map_weightSpace_eq H (quotientMap H φ (χ b))
      (LieSubmodule.Quotient.surjective_mk' _) hint a.val
    intro h
    apply (hs a.val).mp
    intro hn
    rw [hn, Submodule.map_bot] at hm
    exact h (by
      change (Module.finrank ℂ (weightSpace_value (simpleQuotient_value H φ (χ b)) H a.val) : ℤ) = 0
      simp [← hm])
  have hdiag (a : D) : (C a).coeff (asIntegral a) = 1 := by
    letI := inducedLieRingModule H φ (χ a)
    letI := inducedLieModule H φ (χ a)
    obtain ⟨hint, _, _, hline⟩ := VermaWeightsUniversal.verma_weights hss H φ hφ a.val (χ a) (hχ a)
    have hm := map_weightSpace_eq H (quotientMap H φ (χ a))
      (LieSubmodule.Quotient.surjective_mk' _) hint a.val
    rw [hline, Submodule.map_span, Set.image_singleton] at hm
    change (Module.finrank ℂ (weightSpace_value (simpleQuotient_value H φ (χ a)) H a.val) : ℤ) = 1
    rw [← hm]
    change (Module.finrank ℂ (ℂ ∙ quotientHighestVector H φ (χ a)) : ℤ) = 1
    rw [finrank_span_singleton (quotient_highest_ne_zero H φ (χ a) hss hφ a.val (hχ a))]
    rfl
  refine ⟨finite, ?_⟩
  change LinearIndependent ℤ C
  apply linearIndependent_iff.mpr
  intro l hl
  by_contra hne
  have hs : l.support.Nonempty := Finsupp.support_nonempty_iff.mpr hne
  obtain ⟨a, ha, hmax⟩ := l.support.exists_max_image (fun b => φ b.val) hs
  have hz := congrArg (fun f : IntegralGroupRing H φ => f.coeff (asIntegral a)) hl
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hz
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_smul_apply, Int.zsmul_eq_mul] at hz
  rw [Finset.sum_eq_single a, hdiag, mul_one] at hz
  · exact (Finsupp.mem_support_iff.mp ha) hz
  · intro b hb hba
    have hz' : (C b).coeff (asIntegral a) = 0 := by
      by_contra hc
      rcases positive_direction H φ (hw a b hc) with he | hp
      · exact hba (Subtype.ext (sub_eq_zero.mp he))
      · rw [map_sub] at hp
        exact (not_lt_of_ge (hmax b hb)) (sub_pos.mp hp)
    rw [hz', mul_zero]
  · exact fun hn => (hn ha).elim

theorem simple_character_family : simple_character_family_type.{u} := by
  intro L _ _ _ hss H _ φ hφ
  choose χ hχ using fun a : {a : Module.Dual ℂ H // IsDominant H φ a} =>
    (VermaModules.character_existsUnique hss H φ hφ a.val).exists
  exact ⟨χ, hχ, independence hss H φ hφ χ hχ⟩

end SimpleCharacters



section Geometric

open HahnSeries (SummableFamily)
local notation "S" => Series H φ
local notation "e[" a "]" => HahnSeries.single (exponent H φ a) (1 : ℤ)

private theorem single_mul (a b : Module.Dual ℂ H) : (e[a] : S) * e[b] = e[a + b] := by
  rw [HahnSeries.single_mul_single, mul_one, map_add]

private theorem coeff_single_one (a : Module.Dual ℂ H) (x : Exponent H φ) :
    (e[a] : S).coeff x = if x = exponent H φ a then 1 else 0 := by
  split_ifs with h <;> simp [h]

private def geometricFamily (a : Module.Dual ℂ H)
    (ha : a ∈ cone H φ) (hp : 0 < φ a) : SummableFamily (Exponent H φ) ℤ ℕ where
  toFun n := e[-(n • a)]
  isPWO_iUnion_support' := by
    let f (n : ℕ) := exponent H φ (-(n • a))
    have hm : Monotone f := by
      intro n m h
      change -(n • a) - -(m • a) ∈ cone H φ
      rw [show -(n • a) - -(m • a) = (m - n) • a by
        have he : m • a = n • a + (m - n) • a := by
          rw [← add_nsmul, Nat.add_sub_of_le h]
        rw [he]
        abel]
      exact (cone H φ).smul_mem _ ha
    have he : (⋃ n : ℕ, (e[-(n • a)] : S).support) = Set.range f := by
      ext x
      simp only [HahnSeries.support_single_of_ne (one_ne_zero : (1 : ℤ) ≠ 0),
        Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_range, f]
      exact exists_congr fun n => eq_comm
    rw [he, ← Set.image_univ]
    exact (Set.isPWO_of_wellQuasiOrderedLE Set.univ).image_of_monotone hm
  finite_co_support' x := by
    apply Set.Subsingleton.finite
    intro n hn m hm
    have h (k : ℕ) (hk : (e[-(k • a)] : S).coeff x ≠ 0) :
        x = exponent H φ (-(k • a)) := by
      by_contra hx
      exact hk (by rw [coeff_single_one, ite_eq_right hx])
    have he := (exponent H φ).injective ((h n hn).symm.trans (h m hm))
    have hf := congrArg φ (neg_injective he)
    simp only [map_nsmul, nsmul_eq_mul] at hf
    exact_mod_cast (mul_right_cancel₀ (ne_of_gt hp) hf)

private def geometric (a : Module.Dual ℂ H)
    (ha : a ∈ cone H φ) (hp : 0 < φ a) : Completion H φ :=
  ⟨(geometricFamily H φ a ha hp).hsum, ⟨{0}, by
    intro x hx
    have hx' := HahnSeries.SummableFamily.support_hsum_subset (s := geometricFamily H φ a ha hp) hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx'
    change x ∈ (e[-(n • a)] : S).support at hn
    rw [HahnSeries.support_single_of_ne one_ne_zero, Set.mem_singleton_iff] at hn
    refine ⟨0, Finset.mem_singleton_self _, ?_⟩
    subst x
    change (0 : Module.Dual ℂ H) - -(n • a) ∈ cone H φ
    simpa using (cone H φ).smul_mem n ha⟩⟩

private theorem geometric_inverse (a : Module.Dual ℂ H)
    (ha : a ∈ cone H φ) (hp : 0 < φ a) :
    (1 - monomial H φ (-a)) * geometric H φ a ha hp = 1 := by
  apply Subtype.ext
  let F := geometricFamily H φ a ha hp
  let T : SummableFamily (Exponent H φ) ℤ ℕ :=
    HahnSeries.SummableFamily.ofFinsupp (Finsupp.single 0 1)
  let shift : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩
  have he : (((e[-a] : S) • F).embDomain shift) = F - T := by
    apply HahnSeries.SummableFamily.ext
    rintro (_ | n)
    · have hn : 0 ∉ Set.range shift := by
        rintro ⟨i, hi⟩
        exact Nat.succ_ne_zero i hi
      rw [HahnSeries.SummableFamily.embDomain_of_notMem_range _ shift hn]
      change (0 : S) = e[-(0 • a)] - Finsupp.single (0 : ℕ) (1 : S) 0
      simp
    · change (((e[-a] : S) • F).embDomain shift) (shift n) = _
      rw [HahnSeries.SummableFamily.embDomain_image, HahnSeries.SummableFamily.smul_apply]
      change (e[-a] : S) * e[-(n • a)] =
        e[-((n + 1) • a)] - Finsupp.single (0 : ℕ) (1 : S) (n + 1)
      rw [Finsupp.single_eq_of_ne (Nat.succ_ne_zero n), sub_zero, single_mul, add_nsmul, one_nsmul]
      rw [neg_add, add_comm]
  change ((1 : S) - e[-a]) * F.hsum = 1
  rw [sub_mul]
  have hshift := congrArg HahnSeries.SummableFamily.hsum he
  rw [HahnSeries.SummableFamily.hsum_embDomain, HahnSeries.SummableFamily.hsum_smul,
    HahnSeries.SummableFamily.hsum_sub] at hshift
  rw [one_mul, hshift, sub_sub_cancel]
  simp [T, HahnSeries.SummableFamily.hsum_ofFinsupp]

end Geometric



section GeometricProduct

open HahnSeries (SummableFamily)
local notation "S" => Series H φ
local notation "e[" a "]" => HahnSeries.single (exponent H φ a) (1 : ℤ)

variable {A : Type w} (root : A → Module.Dual ℂ H)
  (hcone : ∀ a, root a ∈ cone H φ) (hpos : ∀ a, 0 < φ (root a))

private def exponentSum (s : Finset A) (n : ∀ i ∈ s, ℕ) : Module.Dual ℂ H :=
  ∑ i : s, n i.val i.property • root i.val

private theorem exponentSum_insert {s : Finset A} {a : A} (ha : a ∉ s)
    (n : ∀ i ∈ insert a s, ℕ) :
    exponentSum H root (insert a s) n =
      n a (Finset.mem_insert_self _ _) • root a +
        exponentSum H root s (fun i hi => n i (Finset.mem_insert_of_mem hi)) := by
  let f (i : A) : Module.Dual ℂ H := if hi : i ∈ insert a s then n i hi • root i else 0
  have hs (t : Finset A) (ht : t ⊆ insert a s) :
      exponentSum H root t (fun i hi => n i (ht hi)) = ∑ i ∈ t, f i := by
    rw [Finset.sum_subtype t (fun _ => Iff.rfl) f]
    exact Finset.sum_congr rfl fun i _ => by
      dsimp only [f]
      rw [dite_eq_left (ht i.property)]
  rw [hs (insert a s) (fun _ h => h), hs s (fun _ h => Finset.mem_insert_of_mem h),
    Finset.sum_insert ha]
  simp [f]

private theorem geometricProductFamily (s : Finset A) :
    ∃ F : SummableFamily (Exponent H φ) ℤ (∀ i ∈ s, ℕ),
      (∀ n, F n = e[-exponentSum H root s n]) ∧
      F.hsum = ∏ a ∈ s, (geometricFamily H φ (root a) (hcone a) (hpos a)).hsum := by
  induction s using Finset.induction_on with
  | empty =>
    letI : Unique (∀ i ∈ (∅ : Finset A), ℕ) :=
      ⟨⟨fun _ _ => 0⟩, fun _ => funext fun i => funext fun hi => (Finset.notMem_empty i hi).elim⟩
    refine ⟨HahnSeries.SummableFamily.const _ 1, ?_, ?_⟩
    · intro n
      change (1 : S) = e[-exponentSum H root ∅ n]
      have hz : exponentSum H root ∅ n = 0 := by
        unfold exponentSum
        exact Finset.sum_empty
      simp [hz]
    · rw [HahnSeries.SummableFamily.hsum_unique, Finset.prod_empty]
      rfl
  | insert a s ha ih =>
    obtain ⟨F, hF, hsum⟩ := ih
    let G := geometricFamily H φ (root a) (hcone a) (hpos a)
    let E := Finset.insertPiProdEquiv (s := s) (a := a) (fun _ => ℕ) ha
    refine ⟨(G.mul F).Equiv E.symm, ?_, ?_⟩
    · intro n
      rw [HahnSeries.SummableFamily.Equiv_toFun]
      change (e[-(n a (Finset.mem_insert_self _ _) • root a)] : S) *
          F (fun i hi => n i (Finset.mem_insert_of_mem hi)) = _
      rw [hF, single_mul, exponentSum_insert H root ha, neg_add]
    · rw [HahnSeries.SummableFamily.hsum_equiv, HahnSeries.SummableFamily.hsum_mul, hsum,
        Finset.prod_insert ha]

end GeometricProduct


section Verma

open Shared.Lie.PBW (OrderedWord orderedBasis orderedBasis_apply orderedMonomial)
open HahnSeries (SummableFamily)
open private exists_negative_basis monomial_mem_weight wordRoot positiveRoot_mem_cone from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaWeightsUniversal
local notation "S" => Series H φ
local notation "e[" a "]" => HahnSeries.single (exponent H φ a) (1 : ℤ)

private def orderedWordMultiset (A : Type w) [LinearOrder A] :
    OrderedWord A ≃ Multiset A where
  toFun l := l.val
  invFun s := ⟨s.sort (· ≤ ·), s.pairwise_sort _⟩
  left_inv l := Subtype.ext (List.mergeSort_eq_self _ l.property)
  right_inv s := s.sort_eq _

private theorem weightedMultiset_sum {A : Type w} [Fintype A]
    (f : A → Module.Dual ℂ H) (s : Multiset A) :
    (s.map f).sum = ∑ i, (@Multiset.toFinsupp A (Classical.decEq A) s) i • f i := by
  let F : Multiset A →+ Module.Dual ℂ H :=
    Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom f)
  calc
    (s.map f).sum = F s := rfl
    _ = F (Finsupp.toMultiset (@Multiset.toFinsupp A (Classical.decEq A) s)) := by
      rw [Multiset.toFinsupp_toMultiset]
    _ = ∑ i, (@Multiset.toFinsupp A (Classical.decEq A) s) i • f i := by
      rw [Finsupp.toMultiset_apply, Finsupp.sum, map_sum]
      have hsingle (i : A) : F ({i} : Multiset A) = f i := by simp [F]
      simp only [map_nsmul, hsingle]
      exact Finsupp.sum_fintype _ (fun i n => n • f i) (fun _ => zero_nsmul _)

private def orderedWordCounts (A : Type w) [LinearOrder A] [Fintype A] :
    OrderedWord A ≃ (∀ i ∈ (Finset.univ : Finset A), ℕ) :=
  (orderedWordMultiset A).trans <| (@Multiset.toFinsupp A (Classical.decEq A)).toEquiv.trans <|
    Finsupp.equivFunOnFinite.trans
      { toFun := fun n i _ => n i
        invFun := fun n i => n i (Finset.mem_univ i)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

private theorem wordRoot_exponentSum [LinearOrder (positive H φ)] [Fintype (positive H φ)]
    (l : OrderedWord (positive H φ)) :
    exponentSum H Subtype.val Finset.univ (orderedWordCounts _ l) = wordRoot H φ l.val := by
  let A := positive H φ
  let f (i : A) : Module.Dual ℂ H :=
    (@Multiset.toFinsupp A (Classical.decEq A) (l.val : Multiset A)) i • i.val
  calc
    exponentSum H Subtype.val Finset.univ (orderedWordCounts A l) =
        ∑ i : (Finset.univ : Finset A), f i.val := by
      unfold exponentSum
      exact Finset.sum_congr rfl fun i _ => by rfl
    _ = ∑ i : A, f i := (Finset.sum_subtype Finset.univ (fun _ => Iff.rfl) f).symm
    _ = wordRoot H φ l.val := (weightedMultiset_sum H Subtype.val (l.val : Multiset A)).symm

private def geometricUnit (a : Module.Dual ℂ H) (ha : a ∈ cone H φ) (hp : 0 < φ a) :
    (Completion H φ)ˣ where
  val := 1 - monomial H φ (-a)
  inv := geometric H φ a ha hp
  val_inv := geometric_inverse H φ a ha hp
  inv_val := mul_comm _ _ |>.trans (geometric_inverse H φ a ha hp)

set_option maxHeartbeats 1500000 in
theorem verma_character : verma_character_type.{u} := by
  intro L _ _ _ hss H _ φ hφ lam χ hχ
  letI := inducedLieRingModule H φ χ
  letI := inducedLieModule H φ χ
  let A := positive H φ
  letI : Fintype A := (finite_positive H φ hss).fintype
  letI : LinearOrder A := WellOrderingRel.isWellOrder.linearOrder
  let d (a : A) := geometricUnit H φ a.val (positiveRoot_mem_cone H φ hss a) a.property.2
  refine ⟨Finset.univ, Finset.mem_univ, d, fun _ => rfl, ?_⟩
  obtain ⟨b, hb⟩ := exists_negative_basis H φ hss
  obtain ⟨E, hE, _⟩ := VermaModules.induced_free hss H φ hφ χ
  let B := (orderedBasis b).map E
  let wgt (l : OrderedWord A) := lam - wordRoot H φ l.val
  have hB (l : OrderedWord A) : B l ∈ weightSpace_value (induced_value H φ χ) H (wgt l) := by
    simpa only [B, wgt, Module.Basis.map_apply, orderedBasis_apply, orderedMonomial, hE] using
      monomial_mem_weight H φ χ lam hχ b hb l.val
  obtain ⟨F, hF, hsum⟩ := geometricProductFamily H φ (A := A) Subtype.val
    (positiveRoot_mem_cone H φ hss) (fun a => a.property.2) Finset.univ
  let T : SummableFamily (Exponent H φ) ℤ PUnit.{1} := HahnSeries.SummableFamily.const _ (HahnSeries.single (exponent H φ lam) (1 : ℤ))
  let e : OrderedWord A ≃ PUnit.{1} × (∀ i ∈ (Finset.univ : Finset A), ℕ) :=
    (orderedWordCounts A).trans (Equiv.punitProd _).symm
  let G := (T.mul F).Equiv e.symm
  have hG (l : OrderedWord A) : G l = HahnSeries.single (exponent H φ (wgt l)) (1 : ℤ) := by
    change (HahnSeries.single (exponent H φ lam) (1 : ℤ) : Series H φ) * F (orderedWordCounts A l) = _
    rw [hF, single_mul, wordRoot_exponentSum]
    rfl
  let emb := (boundedRing H φ).subtype
  have hGs : G.hsum = emb (monomial H φ lam * ∏ a : A, ((d a)⁻¹).val) := by
    have hT : T.hsum = emb (monomial H φ lam) :=
      (HahnSeries.SummableFamily.hsum_unique T).trans rfl
    calc
      G.hsum = T.hsum * F.hsum := by
        change ((T.mul F).Equiv e.symm).hsum = _
        rw [HahnSeries.SummableFamily.hsum_equiv, HahnSeries.SummableFamily.hsum_mul]
      _ = emb (monomial H φ lam) * ∏ a : A, emb (((d a)⁻¹).val) := by
        rw [hT, hsum]
        apply congrArg (fun x : Series H φ => emb (monomial H φ lam) * x)
        apply Finset.prod_congr rfl
        intro a _
        rfl
      _ = _ := ((map_mul emb _ _).trans (congrArg _ (map_prod emb _ _))).symm
  intro μ
  let I : Set (OrderedWord A) := {l | wgt l = μ}
  have hI : I.Finite :=
    (G.finite_co_support (exponent H φ μ)).subset fun l hl => by
      change wgt l = μ at hl
      change (G l).coeff (exponent H φ μ) ≠ 0
      rw [hG, coeff_single_one, hl, ite_eq_left rfl]
      exact one_ne_zero
  letI instI : Fintype ↑I := hI.fintype
  letI : Fintype {l // wgt l = μ} := instI
  change ((((boundedRing H φ).subtype)
    (monomial H φ lam * ∏ a : A, ((d a)⁻¹).val))).coeff (exponent H φ μ) = _
  rw [← hGs, HahnSeries.SummableFamily.coeff_hsum_eq_sum_of_subset (t := hI.toFinset)]
  · have hdim := Module.finrank_eq_card_basis (weightBasis H B wgt hB μ)
    change (∑ l ∈ hI.toFinset, (G l).coeff (exponent H φ μ)) =
      (Module.finrank ℂ (weightSpace_value (induced_value H φ χ) H μ) : ℤ)
    have hcard : Fintype.card {l // wgt l = μ} = hI.toFinset.card :=
      (Set.Finite.card_toFinset hI).symm
    rw [hdim, hcard]
    rw [show (∑ l ∈ hI.toFinset, (G l).coeff (exponent H φ μ)) =
        ∑ _l ∈ hI.toFinset, (1 : ℤ) by
      apply Finset.sum_congr rfl
      intro l hl
      have he : wgt l = μ := hI.mem_toFinset.mp hl
      rw [hG, coeff_single_one, he, ite_eq_left rfl]]
    simp
  · intro l hl
    apply hI.mem_toFinset.mpr
    change wgt l = μ
    by_contra he
    apply hl
    change (G l).coeff (exponent H φ μ) = 0
    rw [hG, coeff_single_one, ite_eq_right]
    exact fun h => he ((exponent H φ).injective h).symm

theorem every_verma_character : every_verma_character_type.{u} := by
  intro L _ _ _ hss H _ φ hφ lam
  obtain ⟨χ, hχ, hu⟩ := VermaModules.character_existsUnique hss H φ hφ lam
  exact ⟨χ, ⟨hχ, verma_character hss H φ hφ lam χ hχ⟩, fun χ' hχ' => hu χ' hχ'.1⟩

end Verma

theorem completion_ext : completion_ext_type.{u} := by
  intro L _ _ H φ f g h
  exact Subtype.ext (HahnSeries.ext (funext fun a => h ((exponent H φ).symm a)))

theorem monomial_laws : monomial_laws_type.{u} := by
  intro L _ _ H φ
  refine ⟨rfl, fun a b => Subtype.ext ?_⟩
  exact single_mul H φ a b

end LieAlgebrasAndRepresentations.FormalCharacters
