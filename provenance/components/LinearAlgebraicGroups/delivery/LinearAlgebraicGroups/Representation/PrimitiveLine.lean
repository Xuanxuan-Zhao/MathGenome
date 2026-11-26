import Specs.LinearAlgebraicGroups.Representation.PrimitiveLine
import LinearAlgebraicGroups.Affine.RationalRepresentations
import LinearAlgebraicGroups.Multiplicative.WeightDecomposition
import LinearAlgebraicGroups.RootData.BorelsAndChambers
import Mathlib.Data.Matrix.Block
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Representation.CyclicHighestWeight
import LinearAlgebraicGroups.Representation.RootWeightAction
open CategoryTheory Opposite WithConv
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Representation.PrimitiveLine

open LinearAlgebraicGroups.Specs
open Specs.PrimitiveLine
open Specs.RootWeightAction (Representation act extendVector weightSpace IsPrimitive DominanceLE
  IsDominant actLinear mem_weightSpace mem_fixedSpace)
open Specs.CyclicHighestWeight (orbitSpan)
open Specs.CharacterDescent (Character StandardLattice)
open Specs.CharacterPairing (characterValue)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.GeometricRadicals (IsSplitTorus)
open RationalRepresentations (coefficients tensorCoordinate evaluate pointsCoactionEquiv
  evaluate_id coaction_apply_basis)

open private tensorCoordinate_tmul tensor_eq_sum_basis
  from LinearAlgebraicGroups.Affine.RationalRepresentations
open private splitPresentation characterValue_monomial algebraPoint charactersOfIso
  from LinearAlgebraicGroups.RootData.CharacterPairing
open private weightProjection projection_mem projection_of_mem tensorCoefficients
  from LinearAlgebraicGroups.Multiplicative.WeightDecomposition

noncomputable section

variable {k I J : Type u} [Field k] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {G : AffineAlgebraicGroup k}

private def contract {A V : Type u} [AddCommGroup A] [Module k A]
    [AddCommGroup V] [Module k V] (ℓ : A →ₗ[k] k) : V ⊗[k] A →ₗ[k] V :=
  (TensorProduct.rid k V).toLinearMap.comp (ℓ.lTensor V)

@[simp] private theorem contract_tmul {A V : Type u} [AddCommGroup A] [Module k A]
    [AddCommGroup V] [Module k V] (ℓ : A →ₗ[k] k) (v : V) (a : A) :
    contract ℓ (v ⊗ₜ[k] a) = ℓ a • v := by
  simp [contract]

section Coordinates

variable {H : GroupScheme k} {A : HopfAlgebraCategory k}
  {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

private def fromCoaction (e : convolutionPoints A ≅ (groupPointsFunctor k).obj H)
    (b : Module.Basis I k V) (δ : RightComodule k A V) : Representation H I :=
  e.inv ≫ (pointsCoactionEquiv A b).symm δ

private def toCoaction (e : convolutionPoints A ≅ (groupPointsFunctor k).obj H)
    (b : Module.Basis I k V) (ρ : Representation H I) : RightComodule k A V :=
  pointsCoactionEquiv A b (e.hom ≫ ρ)

private theorem from_toCoaction (e : convolutionPoints A ≅ (groupPointsFunctor k).obj H)
    (b : Module.Basis I k V) (ρ : Representation H I) :
    fromCoaction e b (toCoaction e b ρ) = ρ := by
  simp [fromCoaction, toCoaction]

private theorem evaluation (e : convolutionPoints A ≅ (groupPointsFunctor k).obj H)
    (b : Module.Basis I k V) (δ : RightComodule k A V)
    (R : TestAlgebra k) (a : A →ₐ[k] R) (v : V) (i : I) :
    act (fromCoaction e b δ) R (e.hom.app R (toConv a)) (extendVector R (b.equivFun v)) i =
      tensorCoordinate b i (evaluate A δ a v) := by
  let α := (pointsCoactionEquiv A b).symm δ
  have he : e.inv.app R (e.hom.app R (toConv a)) = toConv a :=
    congrArg (fun f : convolutionPoints A ⟶ convolutionPoints A ↦ f.app R (toConv a)) e.hom_inv_id
  change ((α.app R (e.inv.app R (e.hom.app R (toConv a)))).val.mulVec
    (extendVector R (b.equivFun v))) i = _
  rw [he]
  change (∑ j, a (coefficients A b δ i j) * algebraMap k R (b.equivFun v j)) = _
  conv_rhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul, coaction_apply_basis, LinearMap.comp_apply,
    RationalRepresentations.evaluate, LinearMap.lTensor_tmul, tensorCoordinate_tmul,
    Module.Basis.coord_apply, AlgHom.toLinearMap_apply,
    Module.Basis.repr_self, Finsupp.single_apply, ite_smul, one_smul, zero_smul]
  classical
  simp [eq_comm, Algebra.smul_def, mul_comm, Module.Basis.equivFun_apply]

omit [DecidableEq I] in
private theorem coord_contract (b : Module.Basis I k V) (i : I) (R : TestAlgebra k)
    (a : A →ₐ[k] R) (ℓ : R →ₗ[k] k) (t : V ⊗[k] A) :
    b.equivFun (contract (ℓ.comp a.toLinearMap) t) i =
      ℓ (tensorCoordinate b i (a.toLinearMap.lTensor V t)) := by
  refine TensorProduct.inductionOn t ?_ ?_
  · intro v c
    simp [Module.Basis.equivFun_apply, mul_comm]
  · intro x y hx hy
    simpa only [map_add, Pi.add_apply] using congrArg₂ (· + ·) hx hy

private theorem act_contract (e : convolutionPoints A ≅ (groupPointsFunctor k).obj H)
    (b : Module.Basis I k V) (δ : RightComodule k A V)
    (R : TestAlgebra k) (a : A →ₐ[k] R) (ℓ : R →ₗ[k] k) (v : V) :
    (fun i ↦ ℓ (act (fromCoaction e b δ) R (e.hom.app R (toConv a))
      (extendVector R (b.equivFun v)) i)) =
      b.equivFun (contract (ℓ.comp a.toLinearMap) (δ.coaction v)) := by
  funext i
  rw [evaluation, coord_contract]
  rfl

private theorem contract_natural (f : V →ₗ[k] W) (ℓ : A →ₗ[k] k) (t : V ⊗[k] A) :
    f (contract ℓ t) = contract ℓ (f.rTensor A t) := by
  refine TensorProduct.inductionOn t ?_ ?_
  · intro v a
    simp
  · intro x y hx hy
    simp [hx, hy]

omit [DecidableEq I] in
private theorem coords_injective (b : Module.Basis I k V) (R : TestAlgebra k) :
    Function.Injective (fun t : V ⊗[k] R ↦ fun i ↦ tensorCoordinate b i t) := by
  intro x y h
  rw [← tensor_eq_sum_basis b x, ← tensor_eq_sum_basis b y]
  exact congrArg (fun z : I → R ↦ ∑ i, b i ⊗ₜ[k] z i) h

end Coordinates

private theorem orbit_mem (ρ : Representation G.val I) (v : I → k)
    (R : TestAlgebra k) (g : GroupPoints G.val R) (ℓ : R →ₗ[k] k) :
    orbitCoefficient ρ R g ℓ v ∈ orbitSpan ρ (𝟙 G.val.X) v := by
  apply Submodule.mem_iSup_of_mem R
  apply Submodule.mem_iSup_of_mem g
  apply Submodule.subset_span
  refine ⟨ℓ, ?_⟩
  funext i
  change ℓ (act ρ R (g ≫ 𝟙 G.val.X) (extendVector R v) i) =
    ℓ (act ρ R g (extendVector R v) i)
  erw [Category.comp_id]

private theorem orbit_le_iff (ρ : Representation G.val I) (v : I → k)
    (M : Submodule k (I → k)) :
    orbitSpan ρ (𝟙 G.val.X) v ≤ M ↔
      ∀ R g ℓ, orbitCoefficient ρ R g ℓ v ∈ M := by
  refine ⟨fun h R g ℓ ↦ h (orbit_mem ρ v R g ℓ), ?_⟩
  intro h
  apply iSup_le
  intro R
  apply iSup_le
  intro g
  apply Submodule.span_le.mpr
  rintro _ ⟨ℓ, rfl⟩
  rw [Category.comp_id]
  exact h R g ℓ

private def coefficientMap (ρ : Representation G.val I) (R : TestAlgebra k)
    (g : GroupPoints G.val R) (ℓ : R →ₗ[k] k) : (I → k) →ₗ[k] (I → k) :=
  (LinearMap.pi fun i ↦ ℓ.comp (LinearMap.proj i)).comp
    (((actLinear ρ R g).restrictScalars k).comp (Specs.RootWeightAction.extendLinear R))

private theorem stable_iSup {S : Sort*} {ρ : Representation G.val I}
    {M : S → Submodule k (I → k)} (h : ∀ s, IsStable ρ (M s)) :
    IsStable ρ (⨆ s, M s) := by
  intro v hv
  apply (orbit_le_iff ρ v _).mpr
  intro R g ℓ
  have H : (⨆ s, M s) ≤ (⨆ s, M s).comap (coefficientMap ρ R g ℓ) := by
    refine iSup_le fun s w hw ↦ ?_
    exact le_iSup M s ((orbit_le_iff ρ w _).mp (h s w hw) R g ℓ)
  exact H hv

private theorem orbit_properties (h : Specs.CyclicHighestWeight.CoactionComparison.{u})
    (ρ : Representation G.val I) (A : HopfAlgebraCategory k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val) :
    let δ := toCoaction e (Pi.basisFun k I) ρ
    ∀ v, let C := orbitSpan ρ (𝟙 G.val.X) v
      v ∈ C ∧ δ.IsSubcomodule C ∧
        ∀ M : Submodule k (I → k), δ.IsSubcomodule M → v ∈ M → C ≤ M := by
  obtain ⟨δ, hδ, hC⟩ := h G ρ A e
  let b := Pi.basisFun k I
  let τ := toCoaction e b ρ
  have hc : δ.coaction = τ.coaction := by
    apply LinearMap.ext
    intro v
    apply coords_injective b (CommAlgCat.of k A)
    funext i
    have ha := evaluation e b τ (CommAlgCat.of k A) (AlgHom.id k A) v i
    rw [from_toCoaction, evaluate_id] at ha
    have hb := hδ (CommAlgCat.of k A) (AlgHom.id k A) v i
    rw [evaluate_id] at hb
    exact hb.trans ha
  have heq : δ = τ := by
    cases δ
    cases hτ : τ
    simp only [hτ, RightComodule.mk.injEq] at hc ⊢
    exact hc
  rw [heq] at hC
  dsimp only
  intro v
  exact (hC v).2

/-- Stability under all orbit coefficients is the subcomodule condition. -/
private theorem stable_iff (h : Specs.CyclicHighestWeight.CoactionComparison.{u})
    (ρ : Representation G.val I) (A : HopfAlgebraCategory k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (M : Submodule k (I → k)) :
    IsStable ρ M ↔ (toCoaction e (Pi.basisFun k I) ρ).IsSubcomodule M := by
  let b := Pi.basisFun k I
  let δ := toCoaction e b ρ
  constructor
  · intro hm v
    obtain ⟨_, hs, _⟩ := orbit_properties h ρ A e (v : I → k)
    obtain ⟨t, ht⟩ := hs ⟨v, (orbit_properties h ρ A e v).1⟩
    let f := Submodule.inclusion (hm v v.property)
    refine ⟨f.rTensor A t, ?_⟩
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    exact ht
  · intro hm v hv
    exact (orbit_properties h ρ A e v).2.2 M hm hv

private theorem orbit_stable (h : Specs.CyclicHighestWeight.CoactionComparison.{u})
    (ρ : Representation G.val I) (A : HopfAlgebraCategory k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val) (v : I → k) :
    IsStable ρ (orbitSpan ρ (𝟙 G.val.X) v) :=
  (stable_iff h ρ A e _).mpr (orbit_properties h ρ A e v).2.1

/-- The weight projection contracts the orbit at the universal point of the split torus,
so it preserves every rational submodule. -/
private theorem exists_weightProjection (ρ : Representation G.val I) (T : ClosedSubgroup G.val)
    (hT : IsSplitTorus T.group) (lam : Character T.group) :
    ∃ P : (I → k) →ₗ[k] (I → k),
      (∀ v, P v ∈ weightSpace ρ T lam) ∧
      (∀ v ∈ weightSpace ρ T lam, P v = v) ∧
      ∀ M : Submodule k (I → k), IsStable ρ M → ∀ v ∈ M, P v ∈ M := by
  classical
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hT
  obtain ⟨χ, _, hχ, _, _⟩ := LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing
    (k := k) r
  let chars := χ.trans (charactersOfIso i)
  obtain ⟨m, rfl⟩ := chars.surjective lam
  let M := StandardLattice.{u} r
  let A := groupAlgebra k M
  let e : convolutionPoints A ≅ (groupPointsFunctor k).obj T.group :=
    hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso i
  let σ : Representation T.group I := (groupPointsFunctor k).map T.inclusion ≫ ρ
  let b := Pi.basisFun k I
  let δ := toCoaction e b σ
  let P := weightProjection δ m
  have hval (R : TestAlgebra k) (a : A →ₐ[k] R) :
      characterValue (chars m) R (e.hom.app R (toConv a)) = a (MonoidAlgebra.of k M m) := by
    let p := algebraPoint R a
    have he : (e.hom.app R (toConv a) : GroupPoints T.group R) =
        p ≫ i.hom.hom.hom := rfl
    rw [he]
    change characterValue (i.inv ≫ χ m) R (p ≫ i.hom.hom.hom) = _
    have hi : i.hom.hom.hom ≫ i.inv.hom.hom = 𝟙 _ :=
      (Grp.forget _).congr_map i.hom_inv_id
    have hg : i.hom.hom.hom ≫ i.inv.hom.hom ≫ (χ m).hom.hom = (χ m).hom.hom := by
      rw [← Category.assoc, hi, Category.id_comp]
    have hcomp : (p ≫ i.hom.hom.hom) ≫ (i.inv ≫ χ m).hom.hom = p ≫ (χ m).hom.hom :=
      (Category.assoc p i.hom.hom.hom (i.inv.hom.hom ≫ (χ m).hom.hom)).trans
        (congrArg (fun f ↦ p ≫ f) hg)
    unfold characterValue
    dsimp only
    rw [hcomp]
    change characterValue (χ m) R (algebraPoint R a) = _
    rw [hχ]
    exact characterValue_monomial R a m
  have hEval (R : TestAlgebra k) (a : A →ₐ[k] R) (v : I → k) (j : I) :
      act ρ R ((e.hom.app R (toConv a) : GroupPoints T.group R) ≫ T.inclusion.hom.hom)
        (extendVector R v) j = tensorCoordinate b j (evaluate A δ a v) := by
    have h := evaluation e b δ R a v j
    rw [from_toCoaction] at h
    exact h
  have hweight (v : I → k) :
      v ∈ weightSpace ρ T (chars m) ↔
        v ∈ LinearAlgebraicGroups.WeightDecomposition.weightSpace δ m := by
    rw [LinearAlgebraicGroups.WeightDecomposition.mem_weightSpace, mem_weightSpace]
    constructor
    · intro hv
      apply coords_injective b (CommAlgCat.of k A)
      funext j
      let R := CommAlgCat.of k A
      have h := congrFun (hv R (e.hom.app R (toConv (AlgHom.id k A)))) j
      rw [hval] at h
      change tensorCoordinate b j (δ.coaction v) =
        tensorCoordinate b j (v ⊗ₜ[k] MonoidAlgebra.of k M m)
      rw [← LinearMap.congr_fun (evaluate_id A δ) v]
      erw [← hEval R (AlgHom.id k A)]
      rw [tensorCoordinate_tmul]
      change _ = v j • MonoidAlgebra.of k M m
      apply h.trans
      change MonoidAlgebra.of k M m * algebraMap k R (v j) =
        v j • MonoidAlgebra.of k M m
      rw [Algebra.smul_def, mul_comm]
    · intro hv R t
      obtain ⟨a, rfl⟩ := ((forget GrpCat).mapIso (e.app R)).toEquiv.surjective t
      funext j
      change act ρ R ((e.hom.app R (toConv a.ofConv) : GroupPoints T.group R) ≫
        T.inclusion.hom.hom) (extendVector R v) j =
          (characterValue (chars m) R (e.hom.app R (toConv a.ofConv)) • extendVector R v) j
      erw [hEval R a.ofConv, hval]
      simp [evaluate, hv, tensorCoordinate_tmul, b, Algebra.smul_def, mul_comm, extendVector]
  refine ⟨P, fun v ↦ (hweight (P v)).mpr (projection_mem δ m v),
    fun v hv ↦ ?_, ?_⟩
  · simp [P, projection_of_mem ((hweight v).mp hv)]
  · intro N hN v hv
    let ℓ : A →ₗ[k] k := Finsupp.lapply m ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap
    have hcontract (t : (I → k) ⊗[k] A) :
        contract ℓ t = tensorCoefficients t m := by
      refine TensorProduct.inductionOn t ?_ ?_
      · intro w c
        simp [contract_tmul, tensorCoefficients,
          TensorProduct.finsuppScalarRight_apply_tmul_apply, ℓ]
        rfl
      · intro a b ha hb
        simp [ha, hb]
    let R := CommAlgCat.of k A
    let t := e.hom.app R (toConv (AlgHom.id k A))
    have hh := act_contract e b δ R (AlgHom.id k A) ℓ v
    have hId : ℓ.comp (AlgHom.id k A).toLinearMap = ℓ := rfl
    rw [from_toCoaction, hId, Pi.basisFun_equivFun, LinearEquiv.refl_apply, hcontract] at hh
    have hp : orbitCoefficient ρ R ((t : GroupPoints T.group R) ≫ T.inclusion.hom.hom) ℓ v =
        P v := by
      change _ = tensorCoefficients (δ.coaction v) m
      exact hh
    rw [← hp]
    exact (orbit_le_iff ρ v N).mp (hN v hv) R _ ℓ

private theorem stable_maximum (ρ : Representation G.val I) (T : ClosedSubgroup G.val)
    (hT : IsSplitTorus T.group) (lam : Character T.group) (v : I → k)
    (hv : v ≠ 0) (hW : weightSpace ρ T lam = Submodule.span k {v})
    (hC : orbitSpan ρ (𝟙 G.val.X) v = ⊤) :
    let M := ⨆ W : {W : Submodule k (I → k) // IsStable ρ W ∧ W ≠ ⊤}, W.val
    IsStable ρ M ∧ M ≠ ⊤ ∧ ∀ W : Submodule k (I → k),
      IsStable ρ W → W ≠ ⊤ → W ≤ M := by
  obtain ⟨P, hP, hId, hPres⟩ := exists_weightProjection ρ T hT lam
  let S := {W : Submodule k (I → k) // IsStable ρ W ∧ W ≠ ⊤}
  let M := ⨆ W : S, W.val
  have hker : M ≤ LinearMap.ker P := by
    apply iSup_le
    intro W w hw
    have hPmem := hP w
    rw [hW, Submodule.mem_span_singleton] at hPmem
    obtain ⟨a, ha⟩ := hPmem
    have hPw := hPres W.val W.property.1 w hw
    change P w = 0
    by_contra hn
    have ha0 : a ≠ 0 := by
      intro h
      subst a
      exact hn (by simpa using ha.symm)
    have hvW : v ∈ W.val := by
      have hh := W.val.smul_mem a⁻¹ hPw
      rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul] at hh
      exact hh
    have hle := W.property.1 v hvW
    rw [hC] at hle
    exact W.property.2 (top_unique hle)
  refine ⟨stable_iSup (fun W : S ↦ W.property.1), ?_, fun W hs hp ↦ le_iSup (fun W : S ↦ W.val) ⟨W, hs, hp⟩⟩
  intro ht
  change M = ⊤ at ht
  have hvM : v ∈ M := ht.symm ▸ Submodule.mem_top
  have hfix : P v = v := by
    apply hId
    rw [hW]
    exact Submodule.subset_span (Set.mem_singleton v)
  exact hv (hfix.symm.trans (hker hvM))

private theorem dominance_lt {T B : ClosedSubgroup G.val}
    (p : Additive (Character T.group) →ₗ[ℤ] ℝ)
    (hp : ∀ a : Specs.RootWeightAction.SimpleRoot T B, 0 < p (Additive.ofMul a.val.val))
    {mu lam : Character T.group} (hne : mu ≠ lam) (h : DominanceLE T B mu lam) :
    p (Additive.ofMul mu) < p (Additive.ofMul lam) := by
  classical
  obtain ⟨c, hc⟩ := h
  have h₀ : c ≠ 0 := by
    intro hc0
    subst c
    simp only [Finsupp.sum_zero_index] at hc
    exact hne (div_eq_one.mp hc).symm
  obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.mpr h₀
  have hs : 0 < ∑ t ∈ c.support, c t • p (Additive.ofMul t.val.val) := by
    exact Finset.sum_pos' (fun t _ ↦ nsmul_nonneg (hp t).le _)
      ⟨a, ha, nsmul_pos (hp a) (Finsupp.mem_support_iff.mp ha)⟩
  have hh := congrArg p hc
  change p (Additive.ofMul lam - Additive.ofMul mu) = _ at hh
  rw [map_sub] at hh
  simp only [Finsupp.sum, map_sum, map_nsmul] at hh
  exact sub_pos.mp (hh.symm ▸ hs)

private theorem exists_primitive
    {T B : ClosedSubgroup G.val} {U : ClosedSubgroup B.group}
    (ρ : Representation G.val I) (hunip : Specs.Unipotent.IsUnipotent
      (Specs.Unipotent.closedSubgroupAlgebraicGroup
        (G := Specs.Unipotent.closedSubgroupAlgebraicGroup B) U))
    (hweights : by
      classical
      exact DirectSum.IsInternal (fun mu : Character T.group ↦
        (weightSpace ρ T mu).comap (Specs.RootWeightAction.fixedSpace ρ
          (U.inclusion ≫ B.inclusion)).subtype))
    (hn : (⊤ : Submodule k (I → k)) ≠ ⊥) :
    ∃ (lam : Character T.group) (v : I → k), IsPrimitive ρ T B U lam v := by
  classical
  let N := Specs.RootWeightAction.fixedSpace ρ (U.inclusion ≫ B.inclusion)
  obtain ⟨A, ⟨i⟩, hA⟩ := hunip
  let e : convolutionPoints A ≅ (groupPointsFunctor k).obj U.group :=
    hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso i
  let σ : Representation U.group I := (groupPointsFunctor k).map
    (U.inclusion ≫ B.inclusion) ≫ ρ
  let b := Pi.basisFun k I
  let δ := toCoaction e b σ
  haveI : Nontrivial (I → k) := by
    obtain ⟨v, _, hv⟩ := (Submodule.ne_bot_iff _).mp hn
    exact ⟨⟨v, 0, hv⟩⟩
  obtain ⟨v, hv0, hv⟩ := hA (I → k) δ
  have hf : v ∈ N := by
    apply mem_fixedSpace.mpr
    intro R g
    obtain ⟨a, rfl⟩ := ((forget GrpCat).mapIso (e.app R)).toEquiv.surjective g
    have hv' := (RationalRepresentations.invariantKernel A δ v).mpr hv R a.ofConv
    funext j
    have hh := evaluation e b δ R a.ofConv v j
    rw [from_toCoaction, hv'] at hh
    rw [tensorCoordinate_tmul, Algebra.smul_def, mul_one] at hh
    exact hh
  by_contra! hnone
  have hbot (lam : Character T.group) : (weightSpace ρ T lam).comap N.subtype = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    apply Subtype.ext
    by_contra hne
    exact hnone lam (x : I → k) ⟨hne, x.property, hx⟩
  have hle : (⨆ lam : Character T.group, (weightSpace ρ T lam).comap N.subtype) ≤ ⊥ :=
    iSup_le fun lam ↦ (hbot lam).le
  have hEq := hweights.submodule_iSup_eq_top
  have hz : (⟨v, hf⟩ : N) ∈ (⊥ : Submodule k N) :=
    hle (hEq.symm ▸ Submodule.mem_top)
  exact hv0 (congrArg Subtype.val ((Submodule.mem_bot k).mp hz))

private theorem act_eq_scalar_iff (ρ : Representation G.val I) (R : TestAlgebra k)
    (g : GroupPoints G.val R) (v : I → k) (c : R) :
    act ρ R g (extendVector R v) = c • extendVector R v ↔
      ∀ ℓ : R →ₗ[k] k, orbitCoefficient ρ R g ℓ v = ℓ c • v := by
  have hs (ℓ : R →ₗ[k] k) (j : I) : ℓ ((c • extendVector R v) j) = (ℓ c • v) j := by
    change ℓ (c * algebraMap k R (v j)) = ℓ c * v j
    rw [mul_comm c, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  constructor
  · intro h ℓ
    funext j
    exact (congrArg (fun x : I → R ↦ ℓ (x j)) h).trans (hs ℓ j)
  · intro h
    funext j
    by_contra hn
    obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero k (sub_ne_zero.mpr hn)
    apply hℓ
    rw [map_sub, show ℓ (act ρ R g (extendVector R v) j) = (ℓ c • v) j from
      congrFun (h ℓ) j, hs, sub_self]

private theorem stable_map {ρ : Representation G.val I} {σ : Representation G.val J}
    {f : (I → k) →ₗ[k] (J → k)} (hf : IsEquivariant ρ σ f)
    (M : Submodule k (I → k)) (hM : IsStable ρ M) : IsStable σ (M.map f) := by
  intro v hv
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
  apply (orbit_le_iff σ (f x) _).mpr
  intro R g ℓ
  rw [← hf R g ℓ x]
  exact Submodule.mem_map.mpr ⟨_, (orbit_le_iff ρ x M).mp (hM x hx) R g ℓ, rfl⟩

private theorem stable_ker {ρ : Representation G.val I} {σ : Representation G.val J}
    {f : (I → k) →ₗ[k] (J → k)} (hf : IsEquivariant ρ σ f) :
    IsStable ρ (LinearMap.ker f) := by
  intro v hv
  apply (orbit_le_iff ρ v _).mpr
  intro R g ℓ
  change f (orbitCoefficient ρ R g ℓ v) = 0
  rw [hf, LinearMap.mem_ker.mp hv]
  exact (coefficientMap σ R g ℓ).map_zero

private theorem generates_of_simple (h : Specs.CyclicHighestWeight.CoactionComparison.{u})
    (ρ : Representation G.val I) (A : HopfAlgebraCategory k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (hsimple : IsSimple ρ) {v : I → k} (hv : v ≠ 0) :
    orbitSpan ρ (𝟙 G.val.X) v = ⊤ := by
  rcases hsimple.2 _ (orbit_stable h ρ A e v) with hb | ht
  · exact False.elim (hv ((Submodule.mem_bot k).mp (hb ▸ (orbit_properties h ρ A e v).1)))
  · exact ht

private def blockUnits {R : Type u} [CommRing R]
    (x : Matrix.GeneralLinearGroup I R) (y : Matrix.GeneralLinearGroup J R) :
    Matrix.GeneralLinearGroup (I ⊕ J) R where
  val := Matrix.fromBlocks x.val 0 0 y.val
  inv := Matrix.fromBlocks x.inv 0 0 y.inv
  val_inv := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  inv_val := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

private def sumRepresentation (ρ : Representation G.val I) (σ : Representation G.val J) :
    Representation G.val (I ⊕ J) where
  app R := GrpCat.ofHom
    { toFun := fun g ↦ blockUnits (ρ.app R g) (σ.app R g)
      map_one' := by
        apply Units.ext
        change (blockUnits ((ρ.app R).hom 1) ((σ.app R).hom 1)).val = 1
        rw [map_one, map_one]
        exact Matrix.fromBlocks_one
      map_mul' := by
        intro x y
        apply Units.ext
        change (blockUnits ((ρ.app R).hom (x * y)) ((σ.app R).hom (x * y))).val = _
        erw [map_mul, map_mul]
        simp [blockUnits, Matrix.fromBlocks_multiply] <;> constructor <;> rfl }
  naturality R S a := by
    apply GrpCat.ext
    intro g
    have hρ := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (ρ.naturality a)) g
    have hσ := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (σ.naturality a)) g
    change ρ.app S (mapPoints a g) = Matrix.GeneralLinearGroup.map a.hom.toRingHom (ρ.app R g) at hρ
    change σ.app S (mapPoints a g) = Matrix.GeneralLinearGroup.map a.hom.toRingHom (σ.app R g) at hσ
    apply Units.ext
    change (blockUnits (ρ.app S (mapPoints a g)) (σ.app S (mapPoints a g))).val =
      a.hom.mapMatrix (blockUnits (ρ.app R g) (σ.app R g)).val
    rw [hρ, hσ]
    ext x y
    cases x <;> cases y <;> simp [blockUnits] <;> rfl

private def leftProjection : ((I ⊕ J) → k) →ₗ[k] (I → k) :=
  LinearMap.pi fun i ↦ LinearMap.proj (Sum.inl i)

private def rightProjection : ((I ⊕ J) → k) →ₗ[k] (J → k) :=
  LinearMap.pi fun j ↦ LinearMap.proj (Sum.inr j)

private theorem sum_evaluation (ρ : Representation G.val I) (σ : Representation G.val J)
    (R : TestAlgebra k) (g : GroupPoints G.val R) (v : (I ⊕ J) → k) :
    act (sumRepresentation ρ σ) R g (extendVector R v) =
      Sum.elim (act ρ R g (extendVector R (leftProjection v)))
        (act σ R g (extendVector R (rightProjection v))) := by
  change (Matrix.fromBlocks (ρ.app R g).val 0 0 (σ.app R g).val).mulVec
    (extendVector R v) = _
  have hv : extendVector R v = Sum.elim (extendVector R (leftProjection v))
      (extendVector R (rightProjection v)) := by
    funext i
    cases i <;> rfl
  rw [hv, Matrix.fromBlocks_mulVec]
  simp [act]

private theorem left_equivariant (ρ : Representation G.val I) (σ : Representation G.val J) :
    IsEquivariant (sumRepresentation ρ σ) ρ leftProjection := by
  intro R g ℓ v
  funext i
  exact congrArg (fun x : I ⊕ J → R ↦ ℓ (x (Sum.inl i))) (sum_evaluation ρ σ R g v)

private theorem right_equivariant (ρ : Representation G.val I) (σ : Representation G.val J) :
    IsEquivariant (sumRepresentation ρ σ) σ rightProjection := by
  intro R g ℓ v
  funext i
  exact congrArg (fun x : I ⊕ J → R ↦ ℓ (x (Sum.inr i))) (sum_evaluation ρ σ R g v)

private theorem comp_equivariant {L : Type u} [Fintype L] [DecidableEq L]
    {ρ : Representation G.val I} {σ : Representation G.val J} {τ : Representation G.val L}
    {f : (I → k) →ₗ[k] (J → k)} {g : (J → k) →ₗ[k] (L → k)}
    (hf : IsEquivariant ρ σ f) (hg : IsEquivariant σ τ g) :
    IsEquivariant ρ τ (g.comp f) := by
  intro R x ℓ v
  change g (f (orbitCoefficient ρ R x ℓ v)) = _
  rw [hf, hg]
  rfl

private theorem inclusion_equivariant {A : HopfAlgebraCategory k}
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (ρ : Representation G.val I) (C : Submodule k (I → k))
    (b : Module.Basis J k C) (δ : RightComodule k A C)
    (hδ : (C.subtype.rTensor A).comp δ.coaction =
      (toCoaction e (Pi.basisFun k I) ρ).coaction.comp C.subtype) :
    IsEquivariant (fromCoaction e b δ) ρ
      (C.subtype.comp b.equivFun.symm.toLinearMap) := by
  intro R g ℓ v
  obtain ⟨a, rfl⟩ := ((forget GrpCat).mapIso (e.app R)).toEquiv.surjective g
  obtain ⟨x, rfl⟩ := b.equivFun.surjective v
  have hl := act_contract e b δ R a.ofConv ℓ x
  have hr := act_contract e (Pi.basisFun k I) (toCoaction e (Pi.basisFun k I) ρ)
    R a.ofConv ℓ (x : I → k)
  rw [from_toCoaction] at hr
  change C.subtype (b.equivFun.symm (orbitCoefficient (fromCoaction e b δ) R
    (e.hom.app R a) ℓ (b.equivFun x))) = orbitCoefficient ρ R
      (e.hom.app R a) ℓ (C.subtype (b.equivFun.symm (b.equivFun x)))
  rw [LinearEquiv.symm_apply_apply]
  change C.subtype (b.equivFun.symm (fun j ↦ ℓ (act (fromCoaction e b δ) R
    (e.hom.app R (toConv a.ofConv)) (extendVector R (b.equivFun x)) j))) =
      fun j ↦ ℓ (act ρ R (e.hom.app R (toConv a.ofConv)) (extendVector R (x : I → k)) j)
  simp only [Pi.basisFun_equivFun, LinearEquiv.refl_apply] at hr
  rw [hl, hr, LinearEquiv.symm_apply_apply, contract_natural]
  exact congrArg (contract (ℓ.comp a.ofConv.toLinearMap)) (LinearMap.congr_fun hδ x)

private theorem projection_bijective {L : Type u} [Fintype L] [DecidableEq L]
    {ρ : Representation G.val I} {σ : Representation G.val J} {τ : Representation G.val L}
    {T : ClosedSubgroup G.val} {lam : Character T.group} {v : I → k}
    {f : (I → k) →ₗ[k] (J → k)} {g : (I → k) →ₗ[k] (L → k)}
    (hf : IsEquivariant ρ σ f) (hg : IsEquivariant ρ τ g)
    (hjoint : ∀ x, f x = 0 → g x = 0 → x = 0)
    (hσ : IsSimple σ) (hτ : IsSimple τ) (hvf : f v ≠ 0) (hvg : g v ≠ 0)
    (hwg : g v ∈ weightSpace τ T lam)
    (hline : weightSpace ρ T lam = Submodule.span k {v}) : Function.Bijective f := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    by_contra hne
    let C := (LinearMap.ker f).map g
    have hC : C = ⊤ := by
      rcases hτ.2 C (stable_map hg _ (stable_ker hf)) with hb | ht
      · have hmem : g x ∈ C := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
        exact False.elim (hne (hjoint x (LinearMap.mem_ker.mp hx) ((Submodule.mem_bot k).mp (hb ▸ hmem))))
      · exact ht
    obtain ⟨y, hyf, hyg⟩ : g v ∈ C := hC ▸ Submodule.mem_top
    have hwy : y ∈ weightSpace ρ T lam := by
      apply mem_weightSpace.mpr
      intro R t
      apply (act_eq_scalar_iff ρ R _ _ _).mpr
      intro ℓ
      let z := orbitCoefficient ρ R (t ≫ T.inclusion.hom.hom) ℓ y - ℓ (characterValue lam R t) • y
      have hzf : f z = 0 := by
        dsimp only [z]
        rw [map_sub]
        erw [hf R (t ≫ T.inclusion.hom.hom) ℓ y]
        rw [map_smul, LinearMap.mem_ker.mp hyf]
        change coefficientMap σ R (t ≫ T.inclusion.hom.hom) ℓ 0 - _ = _
        simp
      have hzg : g z = 0 := by
        dsimp only [z]
        rw [map_sub]
        erw [hg R (t ≫ T.inclusion.hom.hom) ℓ y]
        rw [map_smul, hyg]
        erw [(act_eq_scalar_iff τ R _ _ _).mp (mem_weightSpace.mp hwg R t) ℓ, sub_self]
      exact sub_eq_zero.mp (hjoint z hzf hzg)
    rw [hline, Submodule.mem_span_singleton] at hwy
    obtain ⟨a, ha⟩ := hwy
    have ha0 : a = 0 := by
      have h := congrArg f ha
      rw [map_smul, LinearMap.mem_ker.mp hyf] at h
      exact (smul_eq_zero.mp h).resolve_right hvf
    rw [← ha, ha0, zero_smul, map_zero] at hyg
    exact hvg hyg.symm
  · apply LinearMap.range_eq_top.mp
    rcases hσ.2 (LinearMap.range f) (by simpa using stable_map hf ⊤ (fun _ _ ↦ le_top)) with hb | ht
    · exact False.elim (hvf ((Submodule.mem_bot k).mp (hb ▸ LinearMap.mem_range_self f v)))
    · exact ht

/-- The cyclic module generated by the pair of primitive vectors projects isomorphically
onto each of the two simple summands. -/
private theorem simple_isomorphism
    (hC : Specs.CyclicHighestWeight.CoactionComparison.{u})
    (A : HopfAlgebraCategory k) (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    {T B : ClosedSubgroup G.val} {U : ClosedSubgroup B.group}
    (htop : ∀ {L : Type u} [Fintype L] [DecidableEq L] (τ : Representation G.val L)
      (lam : Character T.group) (v : L → k), IsPrimitive τ T B U lam v →
      orbitSpan τ (𝟙 G.val.X) v = ⊤ → weightSpace τ T lam = Submodule.span k {v})
    (ρ : Representation G.val I) (σ : Representation G.val J)
    (hρ : IsSimple ρ) (hσ : IsSimple σ)
    (lam : Character T.group) (v : I → k) (w : J → k)
    (hv : IsPrimitive ρ T B U lam v) (hw : IsPrimitive σ T B U lam w) :
    ∃ F : (I → k) ≃ₗ[k] (J → k), IsEquivariant ρ σ F.toLinearMap := by
  classical
  let τ := sumRepresentation ρ σ
  let s : I ⊕ J → k := Sum.elim v w
  let C := orbitSpan τ (𝟙 G.val.X) s
  obtain ⟨hs, hsub, _⟩ := orbit_properties hC τ A e s
  obtain ⟨δ, hδ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction
    (toCoaction e (Pi.basisFun k (I ⊕ J)) τ) C).mp hsub
  let L := ULift.{u} (Fin (Module.finrank k C))
  let b : Module.Basis L k C := (Module.finBasis k C).reindex Equiv.ulift.symm
  let restricted := fromCoaction e b δ
  let inc := C.subtype.comp b.equivFun.symm.toLinearMap
  have hinc : IsEquivariant restricted τ inc := inclusion_equivariant e τ C b δ hδ
  have hInj : Function.Injective inc := Subtype.val_injective.comp b.equivFun.symm.injective
  let p := leftProjection.comp inc
  let q := rightProjection.comp inc
  have hp : IsEquivariant restricted ρ p := comp_equivariant hinc (left_equivariant ρ σ)
  have hq : IsEquivariant restricted σ q := comp_equivariant hinc (right_equivariant ρ σ)
  have hjoint (z : L → k) (hp0 : p z = 0) (hq0 : q z = 0) : z = 0 := by
    apply hInj
    rw [map_zero]
    funext i
    cases i with
    | inl i => exact congrFun hp0 i
    | inr j => exact congrFun hq0 j
  let x : L → k := b.equivFun ⟨s, hs⟩
  have hx : inc x = s := by simp [inc, x]
  have hpx : p x = v := by
    change leftProjection (inc x) = v
    rw [hx]
    rfl
  have hqx : q x = w := by
    change rightProjection (inc x) = w
    rw [hx]
    rfl
  have hscalar (R : TestAlgebra k) (g : GroupPoints G.val R) (c : R)
      (h1 : act ρ R g (extendVector R v) = c • extendVector R v)
      (h2 : act σ R g (extendVector R w) = c • extendVector R w) :
      act restricted R g (extendVector R x) = c • extendVector R x := by
    apply (act_eq_scalar_iff restricted R g x c).mpr
    intro ℓ
    apply sub_eq_zero.mp
    apply hjoint
    · rw [map_sub, hp, map_smul, hpx, (act_eq_scalar_iff ρ R g v c).mp h1 ℓ, sub_self]
    · rw [map_sub, hq, map_smul, hqx, (act_eq_scalar_iff σ R g w c).mp h2 ℓ, sub_self]
  have hxprim : IsPrimitive restricted T B U lam x := by
    refine ⟨fun hz ↦ hv.1 (hpx.symm.trans (hz ▸ p.map_zero)),
      mem_fixedSpace.mpr ?_, mem_weightSpace.mpr ?_⟩
    · intro R g
      apply (hscalar R _ 1 ?_ ?_).trans (one_smul _ _)
      · simpa using mem_fixedSpace.mp hv.2.1 R g
      · simpa using mem_fixedSpace.mp hw.2.1 R g
    · intro R t
      exact hscalar R _ _ (mem_weightSpace.mp hv.2.2 R t) (mem_weightSpace.mp hw.2.2 R t)
  have hcyc : orbitSpan restricted (𝟙 G.val.X) x = ⊤ := by
    let N := orbitSpan restricted (𝟙 G.val.X) x
    have hxN := (orbit_properties hC restricted A e x).1
    have hsN : s ∈ N.map inc := Submodule.mem_map.mpr ⟨x, hxN, hx⟩
    have hle : C ≤ N.map inc := (stable_map hinc N (orbit_stable hC restricted A e x)) s hsN
    apply top_unique
    intro z _
    have hz : inc z ∈ C := (b.equivFun.symm z).property
    obtain ⟨z', hz', heq⟩ := Submodule.mem_map.mp (hle hz)
    exact hInj heq ▸ hz'
  have hline := htop restricted lam x hxprim hcyc
  have hp' : Function.Bijective p :=
    projection_bijective hp hq hjoint hρ hσ (hpx.symm ▸ hv.1) (hqx.symm ▸ hw.1)
      (hqx.symm ▸ hw.2.2) hline
  have hq' : Function.Bijective q :=
    projection_bijective hq hp (fun z hz hz' ↦ hjoint z hz' hz) hσ hρ
      (hqx.symm ▸ hw.1) (hpx.symm ▸ hv.1) (hpx.symm ▸ hv.2.2) hline
  let P := LinearEquiv.ofBijective p hp'
  let Q := LinearEquiv.ofBijective q hq'
  refine ⟨P.symm.trans Q, comp_equivariant ?_ hq⟩
  intro R g ℓ y
  apply hp'.injective
  change p (P.symm _) = p _
  have hP (z : I → k) : p (P.symm z) = z := P.apply_symm_apply z
  rw [hP, hp]
  exact congrArg (orbitCoefficient ρ R g ℓ) (hP y).symm

/-- The primitive-line theorem conditional on root-weight transport and the cyclic
highest-weight theorem, in that order. -/
theorem primitiveLine_conditional (hroot : Specs.RootWeightAction.Statement.{u})
    (hcyc : Specs.CyclicHighestWeight.Statement.{u}) : Specs.PrimitiveLine.Statement.{u} := by
  classical
  intro k _ G hG T B hT hTmax hB hTB
  obtain ⟨comm, D, high⟩ := hcyc.2 G hG T B hT hTmax hB hTB
  letI := comm
  obtain ⟨_, _, _, U, _, hU, _, hrootFacts⟩ := hroot G hG T B hT hTmax hB hTB
  have hi := (LinearAlgebraicGroups.RootData.BorelsAndChambers.borelsThroughT
    G hG T hT hTmax).1 B hB hTB
  obtain ⟨cochar, L, hreg, _, hpos⟩ := hi
  obtain ⟨p, _, hp⟩ := (LinearAlgebraicGroups.RootData.BorelsAndChambers.positiveSystemsFromCocharacters
    G hG T hT hTmax (subgroupRoots T B)).mpr ⟨cochar, hreg, hpos.symm⟩
  have hp' (a : Specs.RootWeightAction.SimpleRoot T B) : 0 < p (Additive.ofMul a.val.val) := by
    have ha : a.val ∈ subgroupRoots T B := a.property.1
    have hm := congrArg (fun S : Set (Specs.AbstractPairing.Root T) ↦ a.val ∈ S) hp
    exact hm.mp ha
  let G' : AffineGroupCategory k := ⟨G.val, G.property.1⟩
  let A := coordinateHopf G'
  let e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val :=
    hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso
      ((affineGroupInclusion k).mapIso (coordinateHopfSpecIso G'))
  refine ⟨comm, D, U, hU, ?_, ?_, ?_⟩
  · intro I _ _ ρ lam v hv hgen
    obtain ⟨hw, hle, hd⟩ := (high U hU ρ lam v hv).2 hgen
    refine ⟨hw, fun mu hmu hne ↦ ⟨hle mu hne hmu, ?_⟩, hd,
      stable_maximum ρ T hT lam v hv.1 hw hgen⟩
    intro hrev
    exact (not_lt_of_gt (dominance_lt p hp' hne (hle mu hne hmu)))
      (dominance_lt p hp' hne.symm hrev)
  · intro I _ _ ρ hsimple
    obtain ⟨lam, v, hv⟩ := exists_primitive ρ hU.2.1 (hrootFacts ρ).2.2.2.2 hsimple.1
    obtain ⟨hline, hvmax, _⟩ := (high U hU ρ lam v hv).2
      (generates_of_simple hcyc.1 ρ A e hsimple hv.1)
    refine ⟨lam, v, hv, fun mu w hw ↦ ?_⟩
    have heq : mu = lam := by
      by_contra hn
      obtain ⟨_, hwmax, _⟩ := (high U hU ρ mu w hw).2
        (generates_of_simple hcyc.1 ρ A e hsimple hw.1)
      have hn₁ : weightSpace ρ T mu ≠ ⊥ := (Submodule.ne_bot_iff _).mpr ⟨w, hw.2.2, hw.1⟩
      have hn₂ : weightSpace ρ T lam ≠ ⊥ := (Submodule.ne_bot_iff _).mpr ⟨v, hv.2.2, hv.1⟩
      exact (not_lt_of_gt (dominance_lt p hp' hn (hvmax mu hn hn₁)))
        (dominance_lt p hp' (Ne.symm hn) (hwmax lam (Ne.symm hn) hn₂))
    subst mu
    exact ⟨rfl, hline ▸ hw.2.2⟩
  · intro I J _ _ _ _ ρ σ hρ hσ lam v w hv hw
    exact simple_isomorphism hcyc.1 A e (fun τ m x hx hgen ↦
      ((high U hU τ m x hx).2 hgen).1) ρ σ hρ hσ lam v w hv hw

end

end LinearAlgebraicGroups.Representation.PrimitiveLine

universe v8_closure_01f866bec3a1742a_u0
theorem _root_.«LinearAlgebraicGroups».«Representation».«PrimitiveLine».«primitiveLine» : _root_.«LinearAlgebraicGroups».«Specs».«PrimitiveLine».«Statement».{v8_closure_01f866bec3a1742a_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«PrimitiveLine».«primitiveLine_conditional».{v8_closure_01f866bec3a1742a_u0} (@_root_.«LinearAlgebraicGroups».«Representation».«RootWeightAction».«rootWeightAction».{v8_closure_01f866bec3a1742a_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«CyclicHighestWeight».«cyclicHighestWeight».{v8_closure_01f866bec3a1742a_u0})
