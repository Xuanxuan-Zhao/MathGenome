import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FormalCharacters
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.WeightDecomposition
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.RootWeightAction
open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj DirectSum TensorProduct Kronecker

universe u

namespace LinearAlgebraicGroups.Representation.FormalCharacters

open _root_.LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character StandardLattice)
open Specs.CharacterPairing (characterValue)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap)
open Specs.FormalCharacters (CoefficientFormula ExactAdditivity TensorMultiplicativity
  WeylInvariance Equivariant formalCharacter tensorRepresentation)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.RootWeightAction (Representation act actLinear extendVector extendLinear
  weightSpace mem_weightSpace WeylTransport)

open LinearAlgebraicGroups.RationalRepresentations
open scoped Classical
open private splitPresentation charactersOfIso algebraPoint characterValue_monomial
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private pointMatrix pointMatrix_evaluation pointMatrix_isCoactionMatrix
  tensor_eq_sum_basis tensorCoordinate_tmul
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
open private fibreTorsor splitFibrePoint from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
variable {I J L : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L]

private theorem splitCharacterValue {M : Type u} [CommGroup M] {T : GroupScheme k}
    (s : specGroup (groupAlgebra k M) ≅ T)
    (χ : M ≃* Character (specGroup (groupAlgebra k M)))
    (hχ : ∀ m, χ m = specGroupMap (groupAlgebraMap k
      ((zpowersHom M m).comp MulEquiv.ulift.toMonoidHom)))
    (m : M) (R : TestAlgebra k) (f : groupAlgebra k M →ₐ[k] R) :
    characterValue ((χ.trans (charactersOfIso s)) m) R
      (algebraPoint R f ≫ s.hom.hom.hom) = f (MonoidAlgebra.of k M m) := by
  have h : (algebraPoint R f ≫ s.hom.hom.hom) ≫ ((χ.trans (charactersOfIso s)) m).hom.hom =
      algebraPoint R f ≫ (χ m).hom.hom := by
    change (algebraPoint R f ≫ s.hom.hom.hom) ≫ s.inv.hom.hom ≫ (χ m).hom.hom = _
    simp only [Category.assoc]
    have he : s.hom.hom.hom ≫ s.inv.hom.hom = 𝟙 _ :=
      (Grp.forget _).congr_map s.hom_inv_id
    rw [← Category.assoc (f := s.hom.hom.hom), he, Category.id_comp]
  change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    ((algebraPoint R f ≫ s.hom.hom.hom) ≫ ((χ.trans (charactersOfIso s)) m).hom.hom)).unop.hom
    (MonoidAlgebra.single _ 1) = _
  rw [h]
  change characterValue (χ m) R (algebraPoint R f) = _
  rw [hχ, characterValue_monomial]
  rfl

private theorem splitPointPresentation {M : Type u} [CommGroup M] {T : GroupScheme k}
    (s : specGroup (groupAlgebra k M) ≅ T) (R : TestAlgebra k) (t : GroupPoints T R) :
    ∃ f : groupAlgebra k M →ₐ[k] R, algebraPoint R f ≫ s.hom.hom.hom = t := by
  let p : GroupPoints (specGroup (groupAlgebra k M)) R := t ≫ s.inv.hom.hom
  let f : groupAlgebra k M →ₐ[k] R := ((algSpec.fullyFaithful
    (R := CommRingCat.of k)).preimage p).unop.hom
  have hp : algebraPoint R f = p :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage p
  refine ⟨f, ?_⟩
  rw [hp, show p = t ≫ s.inv.hom.hom from rfl, Category.assoc]
  have he : s.inv.hom.hom ≫ s.hom.hom.hom = 𝟙 _ :=
    (Grp.forget _).congr_map s.inv_hom_id
  rw [he, Category.comp_id]

private theorem characterValue_mul_of_split {T : GroupScheme k} (hs : IsSplitTorus T)
    (χ ψ : Character T) (R : TestAlgebra k) (t : GroupPoints T R) :
    characterValue (χ * ψ) R t = characterValue χ R t * characterValue ψ R t := by
  obtain ⟨r, ⟨s⟩⟩ := splitPresentation hs
  obtain ⟨ξ, _, hξ, _, _⟩ :=
    LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing (k := k) r
  let e := ξ.trans (charactersOfIso s)
  obtain ⟨m, rfl⟩ := e.surjective χ
  obtain ⟨n, rfl⟩ := e.surjective ψ
  obtain ⟨f, rfl⟩ := splitPointPresentation s R t
  rw [← map_mul e m n, splitCharacterValue s ξ hξ, splitCharacterValue s ξ hξ,
    splitCharacterValue s ξ hξ, map_mul, map_mul]

/-- The coordinate comparison for a split torus uses the generic algebra-valued
point, so it also detects weights over finite fields. -/
private theorem splitWeightComparison (T : ClosedSubgroup G.val) (hs : IsSplitTorus T.group) :
    ∃ (M : Type u) (_ : CommGroup M) (e : M ≃* Character T.group),
      ∀ {I : Type u} [Fintype I] [DecidableEq I] (ρ : Representation G.val I),
        ∃ δ : RightComodule k (groupAlgebra k M) (I → k),
          ∀ m, weightSpace ρ T (e m) = WeightDecomposition.weightSpace δ m := by
  obtain ⟨r, ⟨s⟩⟩ := splitPresentation hs
  let M := StandardLattice.{u} r
  let A := groupAlgebra k M
  obtain ⟨χ, _, hχ, _, _⟩ :=
    LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing (k := k) r
  let e := χ.trans (charactersOfIso s)
  refine ⟨M, inferInstance, e, ?_⟩
  intro I _ _ ρ
  let i : specGroup A ⟶ G.val := s.hom ≫ T.inclusion
  let E := hopfSpecPointIso A
  let α : convolutionPoints A ⟶ StandardGroups.generalLinearPoints k I :=
    E.hom ≫ (groupPointsFunctor k).map i ≫ ρ
  let b := Pi.basisFun k I
  let δ := pointsCoactionEquiv A b α
  have hmat : coefficients A b δ = pointMatrix A α :=
    coefficients_coactionOfMatrix A b _ (pointMatrix_isCoactionMatrix A α)
  have hcoord (R : TestAlgebra k) (f : A →ₐ[k] R) (v : I → k) (j : I) :
      f (tensorCoordinate b j (δ.coaction v)) =
        act ρ R ((algebraPoint R f ≫ s.hom.hom.hom) ≫ T.inclusion.hom.hom)
          (extendVector R v) j := by
    let p : (I → k) →ₗ[k] R :=
      f.toLinearMap ∘ₗ tensorCoordinate b j ∘ₗ δ.coaction
    let q : (I → k) →ₗ[k] R :=
      (LinearMap.proj j : (I → R) →ₗ[k] R) ∘ₗ
        ((actLinear ρ R ((algebraPoint R f ≫ s.hom.hom.hom) ≫
          T.inclusion.hom.hom)).restrictScalars k) ∘ₗ extendLinear R
    have hq : p = q := by
      apply b.ext
      intro l
      change f (coefficients A b δ j l) = _
      rw [hmat]
      have h := pointMatrix_evaluation A α R (WithConv.toConv f)
      have h' : (ρ.app R ((algebraPoint R f ≫ s.hom.hom.hom) ≫
          T.inclusion.hom.hom)).val = f.mapMatrix (pointMatrix A α) := by
        have hE : E.hom.app R (WithConv.toConv f) = algebraPoint R f := by
          apply Over.OverMorphism.ext
          rfl
        change (ρ.app R (((groupPointsFunctor k).map i).app R
          (E.hom.app R (WithConv.toConv f)))).val = _ at h
        rw [hE] at h
        change (ρ.app R (algebraPoint R f ≫ (s.hom.hom.hom ≫ T.inclusion.hom.hom))).val = _ at h
        rw [← Category.assoc] at h
        exact h
      change _ = (ρ.app R _).val.mulVec (extendVector R (b l)) j
      rw [h']
      simp [b, extendVector, Matrix.mulVec, dotProduct, Pi.basisFun_apply, Pi.single_apply]
    exact DFunLike.congr_fun hq v
  refine ⟨δ, ?_⟩
  intro m
  ext v
  rw [mem_weightSpace, WeightDecomposition.mem_weightSpace]
  constructor
  · intro hv
    let R := CommAlgCat.of k A
    let f : A →ₐ[k] R := AlgHom.id k A
    have h (j : I) : tensorCoordinate b j (δ.coaction v) =
        tensorCoordinate b j (v ⊗ₜ[k] MonoidAlgebra.of k M m) := by
      have hj := congrFun (hv R (algebraPoint R f ≫ s.hom.hom.hom)) j
      rw [← hcoord, splitCharacterValue s χ hχ] at hj
      rw [tensorCoordinate_tmul, Module.Basis.coord_apply, Pi.basisFun_repr]
      change tensorCoordinate b j (δ.coaction v) =
        (MonoidAlgebra.of k M m : A) * algebraMap k A (v j) at hj
      rw [Algebra.smul_def, mul_comm]
      exact hj
    rw [← tensor_eq_sum_basis b (δ.coaction v), ← tensor_eq_sum_basis b
      (v ⊗ₜ[k] MonoidAlgebra.of k M m)]
    simp only [h]
  · intro hv R t
    obtain ⟨f, rfl⟩ := splitPointPresentation s R t
    funext j
    rw [← hcoord, splitCharacterValue s χ hχ, hv, tensorCoordinate_tmul,
      Module.Basis.coord_apply, Pi.basisFun_repr, map_smul]
    change _ = f (MonoidAlgebra.of k M m) * algebraMap k R (v j)
    rw [Algebra.smul_def, mul_comm]

private theorem internalWeights (T : ClosedSubgroup G.val) (hs : IsSplitTorus T.group)
    (ρ : Representation G.val I) : DirectSum.IsInternal (weightSpace ρ T) := by
  classical
  obtain ⟨M, _, e, he⟩ := splitWeightComparison T hs
  obtain ⟨δ, hδ⟩ := he ρ
  have h : DirectSum.IsInternal (WeightDecomposition.weightSpace δ) :=
    WeightDecomposition.weightDecomposition δ
  have hr : weightSpace ρ T = WeightDecomposition.weightSpace δ ∘ e.symm := by
    funext χ
    exact (congrArg (weightSpace ρ T) (e.apply_symm_apply χ)).symm.trans (hδ (e.symm χ))
  rw [hr]
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (h.submodule_iSupIndep.comp e.symm.injective)
    ((e.symm.surjective.iSup_comp _).trans h.submodule_iSup_eq_top)

private theorem coefficientFormula (T : ClosedSubgroup G.val) (hs : IsSplitTorus T.group) :
    CoefficientFormula T := by
  classical
  intro I _ _ ρ
  have h := Submodule.finite_ne_bot_of_iSupIndep (internalWeights T hs ρ).submodule_iSupIndep
  have hf : (Function.support (Specs.FormalCharacters.multiplicity T ρ)).Finite := by
    apply h.subset
    intro χ hχ
    change Specs.FormalCharacters.multiplicity T ρ χ ≠ 0 at hχ
    change weightSpace ρ T χ ≠ ⊥
    intro hz
    exact hχ (by simp [Specs.FormalCharacters.multiplicity, hz])
  exact ⟨hf, fun χ => by simp [formalCharacter, dite_eq_left hf]⟩

omit [Fintype J] [DecidableEq J] in
private theorem extendMap_apply (f : (I → k) →ₗ[k] (J → k))
    (R : TestAlgebra k) (v : I → k) :
    ((LinearMap.toMatrix' f).map (algebraMap k R)).mulVec (extendVector R v) =
      extendVector R (f v) := by
  funext j
  rw [← LinearMap.toMatrix'_mulVec f v]
  simp [extendVector, Matrix.mulVec, dotProduct, map_sum, map_mul]

private theorem mapsWeight {T : ClosedSubgroup G.val}
    {ρ : Representation G.val I} {σ : Representation G.val J}
    {f : (I → k) →ₗ[k] (J → k)} (hf : Equivariant ρ σ f)
    {χ : Character T.group} {v : I → k} (hv : v ∈ weightSpace ρ T χ) :
    f v ∈ weightSpace σ T χ := by
  rw [mem_weightSpace] at hv ⊢
  intro R t
  have h := hf R (t ≫ T.inclusion.hom.hom) (extendVector R v)
  dsimp only at h
  rw [hv R t, Matrix.mulVec_smul, extendMap_apply] at h
  exact h.symm

section InternalSum

variable {X V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [DecidableEq X] {A : X → Submodule k V} {B : X → Submodule k W}

private def weightProjection (h : DirectSum.IsInternal A) (m : X) : V →ₗ[k] A m :=
  DirectSum.component k X (fun m => A m) m ∘ₗ
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h).symm.toLinearMap

private theorem project_same (h : DirectSum.IsInternal A) {m : X} (v : A m) :
    weightProjection h m v = v :=
  h.ofBijective_coeLinearMap_same v

private theorem project_other (h : DirectSum.IsInternal A) {m n : X} (hmn : m ≠ n)
    (v : A m) : weightProjection h n v = 0 :=
  h.ofBijective_coeLinearMap_of_ne hmn v

omit [DecidableEq X] in
private def restrictWeight (f : V →ₗ[k] W) (hf : ∀ m, ∀ v ∈ A m, f v ∈ B m) (m : X) :
    A m →ₗ[k] B m :=
  (f.comp (A m).subtype).codRestrict (B m) (fun v => hf m v v.property)

private theorem project_natural (hA : DirectSum.IsInternal A) (hB : DirectSum.IsInternal B)
    (f : V →ₗ[k] W) (hf : ∀ m, ∀ v ∈ A m, f v ∈ B m) (m : X) (v : V) :
    weightProjection hB m (f v) = restrictWeight f hf m (weightProjection hA m v) := by
  let E := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hA
  let F := restrictWeight f hf
  have h : (weightProjection hB m ∘ₗ f) ∘ₗ DirectSum.coeLinearMap A =
      (F m ∘ₗ weightProjection hA m) ∘ₗ DirectSum.coeLinearMap A := by
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof]
    change weightProjection hB m (F n x : W) = F m (weightProjection hA m x)
    by_cases hn : n = m
    · subst n
      rw [project_same, project_same]
    · rw [project_other hB hn, project_other hA hn, map_zero]
  simpa [E] using DFunLike.congr_fun h (E.symm v)

end InternalSum

private theorem exactAdditivity (T : ClosedSubgroup G.val) (hs : IsSplitTorus T.group) :
    ExactAdditivity T := by
  classical
  intro I J L _ _ _ _ _ _ ρ σ τ f g hf hg hi he hx
  have hρ := internalWeights T hs ρ
  have hσ := internalWeights T hs σ
  have hτ := internalWeights T hs τ
  ext χ
  simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, (coefficientFormula T hs _).2]
  let F := restrictWeight (A := weightSpace ρ T) (B := weightSpace σ T) f
    (fun _ _ hv => mapsWeight hf hv) χ
  let H := restrictWeight (A := weightSpace σ T) (B := weightSpace τ T) g
    (fun _ _ hv => mapsWeight hg hv) χ
  have hF : Function.Injective F := fun _ _ e => Subtype.ext (hi (congrArg Subtype.val e))
  have hH : Function.Surjective H := by
    intro z
    obtain ⟨y, hy⟩ := hx (z : L → k)
    refine ⟨weightProjection hσ χ y, ?_⟩
    dsimp only [H]
    rw [← project_natural hσ hτ, hy, project_same]
  have hExact : LinearMap.ker H = LinearMap.range F := by
    ext y
    constructor
    · intro hy
      have hy' : (y : J → k) ∈ LinearMap.ker g :=
        LinearMap.mem_ker.mpr (congrArg Subtype.val (LinearMap.mem_ker.mp hy))
      rw [he.linearMap_ker_eq] at hy'
      obtain ⟨x, hx⟩ := hy'
      refine ⟨weightProjection hρ χ x, ?_⟩
      dsimp only [F]
      rw [← project_natural hρ hσ, hx, project_same]
    · rintro ⟨x, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change g (f x) = 0
      exact DFunLike.congr_fun he.linearMap_comp_eq_zero (x : I → k)
  have hdim := H.finrank_range_add_finrank_ker
  rw [hExact, (LinearEquiv.ofInjective F hF).finrank_eq.symm,
    LinearMap.range_eq_top.mpr hH, finrank_top, add_comm] at hdim
  unfold Specs.FormalCharacters.multiplicity
  exact_mod_cast hdim.symm

section WeightBasis

variable {X V N : Type u} [AddCommGroup V] [Module k V] [DecidableEq X]
  {A : X → Submodule k V}

/-- In a basis of weight vectors the vectors of each specified weight form
a basis of that weight space. -/
private theorem weightFinrank (h : DirectSum.IsInternal A) (b : Module.Basis N k V)
    (w : N → X) (hw : ∀ j, b j ∈ A (w j)) (m : X) :
    Module.finrank k (A m) = Nat.card {j // w j = m} := by
  let S := Set.range (fun j : {j // w j = m} => b j)
  have hs : Submodule.span k S = A m := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      change b j.val ∈ A m
      exact (congrArg (fun n => b j.val ∈ A n) j.property).mp (hw j.val)
    · intro v hv
      let p := weightProjection h m
      have hsum := congrArg p (b.linearCombination_repr v)
      change p (Finsupp.linearCombination k b (b.repr v)) = p v at hsum
      rw [show p v = ⟨v, hv⟩ from project_same h ⟨v, hv⟩] at hsum
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum] at hsum
      have hvsum : (∑ j ∈ (b.repr v).support, (p ((b.repr v) j • b j) : V)) = v := by
        simpa only [Submodule.coe_sum] using congrArg (fun z : A m => (z : V)) hsum
      rw [← hvsum]
      apply Submodule.sum_mem
      intro j _
      rw [map_smul]
      apply Submodule.smul_mem
      by_cases hwm : w j = m
      · have hb : b j ∈ A m := hwm ▸ hw j
        rw [show p (b j) = ⟨b j, hb⟩ from project_same h ⟨b j, hb⟩]
        exact Submodule.subset_span ⟨⟨j, hwm⟩, rfl⟩
      · rw [show p (b j) = 0 from project_other h hwm ⟨b j, hw j⟩]
        exact Submodule.zero_mem _
  rw [← hs]
  let f (j : {j // w j = m}) : V := b j
  have hf : LinearIndependent k f :=
    b.linearIndependent.comp Subtype.val Subtype.val_injective
  exact Module.finrank_eq_nat_card_basis (Module.Basis.span hf)

end WeightBasis

private theorem characterOfBasis {N : Type u} [Fintype N]
    (T : ClosedSubgroup G.val) (hs : IsSplitTorus T.group) (ρ : Representation G.val I)
    (b : Module.Basis N k (I → k)) (w : N → Character T.group)
    (hw : ∀ j, b j ∈ weightSpace ρ T (w j)) :
    formalCharacter T ρ = ∑ j, MonoidAlgebra.single (w j) 1 := by
  classical
  ext m
  rw [(coefficientFormula T hs ρ).2, Specs.FormalCharacters.multiplicity, weightFinrank (internalWeights T hs ρ) b w hw]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [← Finset.sum_filter]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

private def tensorVectors {R : Type u} [CommRing R] (v : I → R) (w : J → R) : I × J → R :=
  fun p => v p.1 * w p.2

private def tensorVectorEquiv : ((I → k) ⊗[k] (J → k)) ≃ₗ[k] (I × J → k) :=
  ((Pi.basisFun k I).tensorProduct (Pi.basisFun k J)).equiv (Pi.basisFun k (I × J)) (Equiv.refl _)

private theorem tensorVectorEquiv_tmul (v : I → k) (w : J → k) :
    tensorVectorEquiv (v ⊗ₜ[k] w) = tensorVectors v w := by
  let F : (I → k) →ₗ[k] (J → k) →ₗ[k] (I × J → k) :=
    LinearMap.mk₂ k tensorVectors
      (by intros; ext; simp [tensorVectors, add_mul])
      (by intros; ext; simp [tensorVectors, mul_assoc])
      (by intros; ext; simp [tensorVectors, mul_add])
      (by intros; ext; simp [tensorVectors, mul_left_comm])
  have h : tensorVectorEquiv.toLinearMap = TensorProduct.lift F := by
    apply ((Pi.basisFun k I).tensorProduct (Pi.basisFun k J)).ext
    rintro ⟨i, j⟩
    rw [LinearEquiv.coe_coe, tensorVectorEquiv, Module.Basis.equiv_apply,
      Module.Basis.tensorProduct_apply']
    change Pi.basisFun k (I × J) (i, j) = tensorVectors (Pi.basisFun k I i) (Pi.basisFun k J j)
    ext ⟨p, q⟩
    by_cases hi : i = p <;> by_cases hj : j = q <;>
      simp [tensorVectors, Pi.basisFun_apply, Prod.mk.injEq, hi, hj,
        eq_comm (a := p) (b := i), eq_comm (a := q) (b := j)]
  exact DFunLike.congr_fun h (v ⊗ₜ[k] w)

private theorem tensorWeights {T : ClosedSubgroup G.val} (hs : IsSplitTorus T.group)
    {ρ : Representation G.val I} {σ : Representation G.val J}
    {χ ψ : Character T.group} {v : I → k} {w : J → k}
    (hv : v ∈ weightSpace ρ T χ) (hw : w ∈ weightSpace σ T ψ) :
    tensorVectors v w ∈ weightSpace (tensorRepresentation ρ σ) T (χ * ψ) := by
  rw [mem_weightSpace] at hv hw ⊢
  intro R t
  let g := t ≫ T.inclusion.hom.hom
  let A := (ρ.app R g).val
  let B := (σ.app R g).val
  have hact : (A ⊗ₖ B).mulVec (tensorVectors (extendVector R v) (extendVector R w)) =
      tensorVectors (A.mulVec (extendVector R v)) (B.mulVec (extendVector R w)) := by
    ext ⟨i, j⟩
    simp only [tensorVectors, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kronecker_apply]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ac_rfl
  have hext : extendVector R (tensorVectors v w) =
      tensorVectors (extendVector R v) (extendVector R w) := by
    ext p
    exact map_mul (algebraMap k R) _ _
  change (A ⊗ₖ B).mulVec (extendVector R (tensorVectors v w)) = _
  rw [hext, hact]
  change tensorVectors (act ρ R g (extendVector R v)) (act σ R g (extendVector R w)) = _
  rw [hv R t, hw R t, characterValue_mul_of_split hs]
  ext p
  simp only [tensorVectors, Pi.smul_apply, smul_eq_mul]
  ac_rfl

private theorem tensorMultiplicativity (T : ClosedSubgroup G.val) (hs : IsSplitTorus T.group) :
    TensorMultiplicativity T := by
  classical
  intro I J _ _ _ _ ρ σ
  let A := fun χ => weightSpace ρ T χ
  let B := fun χ => weightSpace σ T χ
  let b := (internalWeights T hs ρ).collectedBasis (fun χ => Module.finBasis k (A χ))
  let c := (internalWeights T hs σ).collectedBasis (fun χ => Module.finBasis k (B χ))
  letI := FiniteDimensional.fintypeBasisIndex b
  letI := FiniteDimensional.fintypeBasisIndex c
  have hb (i : Σ χ, Fin (Module.finrank k (A χ))) : b i ∈ A i.1 :=
    (internalWeights T hs ρ).collectedBasis_mem _ i
  have hc (j : Σ χ, Fin (Module.finrank k (B χ))) : c j ∈ B j.1 :=
    (internalWeights T hs σ).collectedBasis_mem _ j
  let d := (b.tensorProduct c).map tensorVectorEquiv
  have hd (p : (Σ χ, Fin (Module.finrank k (A χ))) ×
      (Σ χ, Fin (Module.finrank k (B χ)))) :
      d p ∈ weightSpace (tensorRepresentation ρ σ) T (p.1.1 * p.2.1) := by
    simpa only [d, Module.Basis.map_apply, Module.Basis.tensorProduct_apply',
      tensorVectorEquiv_tmul] using tensorWeights hs (hb p.1) (hc p.2)
  rw [characterOfBasis T hs ρ b Sigma.fst hb, characterOfBasis T hs σ c Sigma.fst hc,
    characterOfBasis T hs _ d (fun p => p.1.1 * p.2.1) hd]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, MonoidAlgebra.single_mul_single, one_mul, Fintype.sum_prod_type]

private theorem weylInvariance {T : ClosedSubgroup G.val} (hs : IsSplitTorus T.group)
    [IsCommMonObj T.group.X] {D : Specs.AbstractPairing.Datum T}
    (e : Specs.DatumAndWeyl.Identification D)
    (h : ∀ {I : Type u} [Fintype I] [DecidableEq I] (ρ : Representation G.val I),
      WeylTransport ρ e) : WeylInvariance e := by
  intro I _ _ ρ w χ
  let K := CommAlgCat.of k k
  let T' : ClosedSubgroup e.normalizer.group := ⟨T.group, e.torusInclusion, e.torusClosed⟩
  let a := e.image.constantGroup.sectionPoint (e.labelEquiv w)
  have ht := fibreTorsor (G := Specs.Unipotent.closedSubgroupAlgebraicGroup e.normalizer)
    (W := e.scheme) T' e.quotient e.isQuotient a
  obtain ⟨n, hn⟩ := splitFibrePoint
    (G := Specs.Unipotent.closedSubgroupAlgebraicGroup e.normalizer) (W := e.scheme)
    T' hs e.quotient a ht
  have hlift : ((toUnit ((testSpec k).obj (Opposite.op K))) ≫ n) ≫ e.quotient.hom.hom =
      toUnit _ ≫ a := by rw [Category.assoc, hn]
  obtain ⟨F, _⟩ := h ρ w _ hlift χ
  simp only [(coefficientFormula T hs ρ).2, Specs.FormalCharacters.multiplicity, F.finrank_eq]

/-- Integral character identities, with the full E02 result as an explicit premise. -/
theorem formalCharacters_conditional (h : Specs.RootWeightAction.Statement.{u}) :
    Specs.FormalCharacters.Statement.{u} := by
  intro k _ G hG T B hs hmax hB hTB
  refine ⟨@coefficientFormula k _ G T hs, @exactAdditivity k _ G T hs,
    @tensorMultiplicativity k _ G T hs, ?_⟩
  obtain ⟨hc, D, e, _, _, _, _, hweights⟩ := h G hG T B hs hmax hB hTB
  letI := hc
  exact ⟨hc, D, e, weylInvariance hs e (fun ρ => (hweights ρ).2.1)⟩

end

end LinearAlgebraicGroups.Representation.FormalCharacters

universe v8_closure_c8acf968990d9189_u0
theorem _root_.«LinearAlgebraicGroups».«Representation».«FormalCharacters».«formalCharacters» : _root_.«LinearAlgebraicGroups».«Specs».«FormalCharacters».«Statement».{v8_closure_c8acf968990d9189_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«FormalCharacters».«formalCharacters_conditional».{v8_closure_c8acf968990d9189_u0} (@_root_.«LinearAlgebraicGroups».«Representation».«RootWeightAction».«rootWeightAction».{v8_closure_c8acf968990d9189_u0})
