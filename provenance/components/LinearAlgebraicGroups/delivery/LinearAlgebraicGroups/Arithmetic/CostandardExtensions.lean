import Specs.LinearAlgebraicGroups.Arithmetic.CostandardExtensions
import LinearAlgebraicGroups.Representation.WeylModules
import LinearAlgebraicGroups.Representation.InductionAdjunction
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory WithConv Coalgebra
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj TensorProduct

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LinearAlgebraicGroups.Arithmetic.CostandardExtensions

open LinearAlgebraicGroups.Specs
open Specs.CostandardExtensions
open Specs.AbstractPairing (Datum Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue pairing)
open Specs.FlagLineBundle
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.PrimitiveLine (IsEquivariant orbitCoefficient)
open Specs.RootWeightAction (Representation act actLinear extendVector extendLinear weightSpace
  mem_weightSpace DominanceLE)
open Specs.SimpleClassification (SocleModel)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.WeylModules (IsDual HighestWeightLine oppositeWeight)
open private act_eq_scalar_iff from LinearAlgebraicGroups.Representation.PrimitiveLine
open private equivariant_weight from LinearAlgebraicGroups.Representation.WeylModules

variable {k : Type u} [Field k] {H : AffineAlgebraicGroup k}
variable {I J M : Type u}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]

private theorem weight_of_injective {ρ : Representation H.val I} {σ : Representation H.val J}
    {f : (I → k) →ₗ[k] (J → k)} (hf : IsEquivariant ρ σ f) (hi : Function.Injective f)
    {T : ClosedSubgroup H.val} {χ : Character T.group} {v : I → k}
    (hv : f v ∈ weightSpace σ T χ) : v ∈ weightSpace ρ T χ := by
  apply mem_weightSpace.mpr
  intro R t
  apply (act_eq_scalar_iff ρ R _ v _).mpr
  intro ℓ
  apply hi
  rw [hf R _ ℓ v, map_smul]
  exact (act_eq_scalar_iff σ R _ (f v) _).mp (mem_weightSpace.mp hv R t) ℓ

private theorem middle_weights {ρ : Representation H.val J} {σ : Representation H.val M}
    {τ : Representation H.val I} {i : (J → k) →ₗ[k] (M → k)}
    {q : (M → k) →ₗ[k] (I → k)} (hi : IsEquivariant ρ σ i)
    (hq : IsEquivariant σ τ q) (hInj : Function.Injective i) (hExact : Function.Exact i q)
    {T : ClosedSubgroup H.val} {χ : Character T.group}
    (hχ : weightSpace σ T χ ≠ ⊥) :
    weightSpace ρ T χ ≠ ⊥ ∨ weightSpace τ T χ ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hχ
  by_cases hqv : q v = 0
  · obtain ⟨w, hw⟩ := (hExact v).mp hqv
    left
    refine (Submodule.ne_bot_iff _).mpr ⟨w, weight_of_injective hi hInj ?_, ?_⟩
    · rwa [hw]
    · intro he
      exact hv0 (hw.symm.trans (he ▸ i.map_zero))
  · exact Or.inr ((Submodule.ne_bot_iff _).mpr ⟨q v, equivariant_weight hq hv, hqv⟩)


open private splitPresentation from LinearAlgebraicGroups.RootData.CharacterPairing
open private charactersOfIso torusPoint_weights from LinearAlgebraicGroups.Representation.RootWeightAction
open private weightProjection from LinearAlgebraicGroups.Representation.CyclicHighestWeight

private theorem weights_span (P : OppositeBorelPair H) (ρ : Representation H.val I) :
    ⨆ χ, weightSpace ρ P.torus χ = ⊤ := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := splitPresentation P.split
  obtain ⟨φ, _, hφ, _, _⟩ := LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing (k := k) n
  obtain ⟨δ, hδ⟩ := torusPoint_weights ρ e φ hφ
  let E := φ.toEquiv.trans (charactersOfIso e)
  rw [← E.surjective.iSup_comp]
  change ⨆ m, weightSpace ρ P.torus (E m) = ⊤
  simp_rw [show ∀ m, weightSpace ρ P.torus (E m) = _ from hδ]
  let : DecidableEq (Specs.CharacterDescent.StandardLattice n) := Classical.decEq _
  exact (LinearAlgebraicGroups.WeightDecomposition.weightDecomposition δ).submodule_iSup_eq_top

private theorem linear_eq_on_weights (P : OppositeBorelPair H) (ρ : Representation H.val I)
    {V : Type*} [AddCommGroup V] [Module k V] {f g : (I → k) →ₗ[k] V}
    (h : ∀ χ v, v ∈ weightSpace ρ P.torus χ → f v = g v) : f = g := by
  have htop : (⊤ : Submodule k (I → k)) ≤ f.eqLocus g :=
    (weights_span P ρ) ▸ iSup_le fun χ v hv ↦ h χ v hv
  exact LinearMap.ext fun v ↦ htop (Submodule.mem_top (x := v))

private def extendFunctional (R : TestAlgebra k) (f : (I → k) →ₗ[k] k) :
    (I → R) →ₗ[R] R :=
  ∑ i, algebraMap k R (f (Pi.basisFun k I i)) • LinearMap.proj i

omit [DecidableEq I] in
private theorem extendFunctional_apply (R : TestAlgebra k) (f : (I → k) →ₗ[k] k) (v : I → k) :
    extendFunctional R f (extendVector R v) = algebraMap k R (f v) := by
  have h := congrArg (fun w : I → k ↦ algebraMap k R (f w)) ((Pi.basisFun k I).sum_repr v)
  simpa only [map_sum, map_smul, smul_eq_mul, map_mul, Pi.basisFun_repr,
    extendFunctional, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, extendVector, mul_comm] using h

omit [DecidableEq I] in
private theorem extendFunctional_contract (R : TestAlgebra k) (f : (I → k) →ₗ[k] k)
    (ℓ : R →ₗ[k] k) (v : I → R) :
    ℓ (extendFunctional R f v) = f (fun i ↦ ℓ (v i)) := by
  have h := congrArg f ((Pi.basisFun k I).sum_repr (fun i ↦ ℓ (v i)))
  simp only [map_sum, map_smul, Pi.basisFun_repr, smul_eq_mul] at h
  rw [← h]
  simp only [extendFunctional, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    map_sum]
  congr 1
  funext i
  rw [smul_eq_mul, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

private theorem functional_eq_on_weight_vectors (P : OppositeBorelPair H)
    (ρ : Representation H.val I) (R : TestAlgebra k) {f g : (I → R) →ₗ[R] R}
    (h : ∀ χ v, v ∈ weightSpace ρ P.torus χ →
      f (extendVector R v) = g (extendVector R v)) : f = g := by
  have hlin : (f.restrictScalars k).comp (extendLinear R) =
      (g.restrictScalars k).comp (extendLinear R) := linear_eq_on_weights P ρ h
  apply (Pi.basisFun R I).ext
  intro j
  have hval := LinearMap.congr_fun hlin (Pi.basisFun k I j)
  have hbase : extendVector R (Pi.basisFun k I j) = Pi.basisFun R I j := by
    ext i
    simp [extendVector, Pi.basisFun_apply, Pi.single_apply]
  change f (extendVector R (Pi.basisFun k I j)) = g (extendVector R (Pi.basisFun k I j)) at hval
  simpa only [hbase] using hval

private theorem torus_covariance (P : OppositeBorelPair H)
    (ρ : Representation H.val I) (mu : Character P.torus.group) (f : (I → k) →ₗ[k] k)
    (hf : ∀ χ ≠ mu, ∀ v ∈ weightSpace ρ P.torus χ, f v = 0)
    (R : TestAlgebra k) (t : GroupPoints P.torus.group R) :
    (extendFunctional R f).comp (actLinear ρ R (t ≫ P.torus.inclusion.hom.hom)) =
      characterValue mu R t • extendFunctional R f := by
  apply functional_eq_on_weight_vectors P ρ
  intro χ v hv
  change extendFunctional R f (act ρ R (t ≫ P.torus.inclusion.hom.hom) (extendVector R v)) = _
  rw [mem_weightSpace.mp hv R t, map_smul, LinearMap.smul_apply, extendFunctional_apply]
  by_cases h : χ = mu
  · rw [h]
  · rw [hf χ h v hv, map_zero, smul_zero, smul_zero]

open Specs.RootWeightAction (RootOrbit)
open Specs.RootGroups (AdditiveLine IsRootSubgroup HasScalarAction rootPoint)
open private act_one act_mul rootOrbit from LinearAlgebraicGroups.Representation.RootWeightAction

private theorem root_invariance (P : OppositeBorelPair H)
    (ρ : Representation H.val I) (hρ : RootOrbit ρ P.torus)
    (f : (I → k) →ₗ[k] k) (α : Root P.torus)
    (hvanish : ∀ χ : Character P.torus.group, weightSpace ρ P.torus χ ≠ ⊥ →
      ∀ j : ℕ, 0 < j → ∀ v ∈ weightSpace ρ P.torus (χ * α.val ^ j), f v = 0)
    (Z : ClosedSubgroup H.val) (hZ : IsRootSubgroup P.torus Z α.val)
    (A : AdditiveLine k) (x : A.group ≅ Z.group)
    (hx : HasScalarAction P.torus α.val (x.hom ≫ Z.inclusion))
    (R : TestAlgebra k) (a : R) :
    (extendFunctional R f).comp (actLinear ρ R (rootPoint (x.hom ≫ Z.inclusion) R a)) =
      extendFunctional R f := by
  apply functional_eq_on_weight_vectors P ρ
  intro χ v hv
  by_cases hχ : weightSpace ρ P.torus χ = ⊥
  · have hzero := (Submodule.mem_bot k).mp (hχ ▸ hv)
    subst v
    simp only [map_zero, show extendVector R (0 : I → k) = 0 from (extendLinear R).map_zero]
  obtain ⟨p, h0, hcoeff, hp⟩ := hρ α Z hZ A x hx χ ⟨v, hv⟩
  let n := (Finset.univ.sup fun i : I ↦ (p i).natDegree) + 1
  have hsum : (fun i ↦ Polynomial.aeval a (p i)) =
      ∑ j ∈ Finset.range n, a ^ j • extendVector R (fun i ↦ (p i).coeff j) := by
    funext i
    have hn : (p i).natDegree < n :=
      Nat.lt_succ_of_le (Finset.le_sup (f := fun i : I ↦ (p i).natDegree) (Finset.mem_univ i))
    rw [Polynomial.aeval_eq_sum_range' hn]
    simp only [Finset.sum_apply, Algebra.smul_def]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  change extendFunctional R f
      (act ρ R (rootPoint (x.hom ≫ Z.inclusion) R a) (extendVector R v)) = _
  rw [hp R a, hsum, map_sum, Finset.sum_eq_single 0]
  · simp [h0]
  · intro j _ hj
    rw [map_smul, extendFunctional_apply, hvanish χ hχ j (Nat.pos_of_ne_zero hj) _ (hcoeff j
      (Nat.pos_of_ne_zero hj)), map_zero, smul_zero]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr (Nat.succ_pos _)))


open Specs.OrderedRootProducts (RootSubgroupFamily rootProduct product)
open private existsEnumeration radicalProductFor from LinearAlgebraicGroups.Flag.OpenCell
open private rootPoint_surjective neg_shift from LinearAlgebraicGroups.Representation.CyclicHighestWeight
open private splitPoint pointMap characterValue_eq_eval
  from LinearAlgebraicGroups.Representation.RootWeightAction

private theorem rootProduct_invariance (ρ : Representation H.val I)
    {T : ClosedSubgroup H.val} (roots : RootSubgroupFamily T)
    (S : Set (Root T)) (l : List (Root T)) (hl : ∀ α ∈ l, α ∈ S)
    (R : TestAlgebra k) (f : (I → R) →ₗ[R] R)
    (hf : ∀ α ∈ S, ∀ g : GroupPoints (roots α).val.group R, ∀ v,
      f (act ρ R (g ≫ (roots α).val.inclusion.hom.hom) v) = f v)
    (g : Points (product (fun α => (roots α).val.group.X) l) R) (v : I → R) :
    f (act ρ R (g ≫ rootProduct roots l) v) = f v := by
  induction l with
  | nil =>
    rw [show g ≫ rootProduct roots [] = (1 : GroupPoints H.val R) from
      MonObj.comp_one _, act_one]
  | cons α l ih =>
    let x := g ≫ fst _ _
    let y := g ≫ snd _ _
    let gx : GroupPoints H.val R := x ≫ (roots α).val.inclusion.hom.hom
    let gy : GroupPoints H.val R := y ≫ rootProduct roots l
    have he : g ≫ rootProduct roots (α :: l) = gx * gy := by
      simp only [gx, gy, x, y, rootProduct, MonObj.comp_mul, Category.assoc]
    rw [he, act_mul, hf α (hl α (List.mem_cons_self ..)) x,
      ih (fun β hβ ↦ hl β (List.mem_cons_of_mem _ hβ)) y]

private theorem borel_covariance (P : OppositeBorelPair H) [IsCommMonObj P.torus.group.X]
    (D : Datum P.torus) (ρ : Representation H.val I) (hρ : RootOrbit ρ P.torus)
    (p : BorelProjection P) (mu : Character P.torus.group) (f : (I → k) →ₗ[k] k)
    (hf : ∀ χ ≠ mu, ∀ v ∈ weightSpace ρ P.torus χ, f v = 0)
    (hvanish : ∀ α ∈ subgroupRoots P.torus P.negative,
      ∀ χ, weightSpace ρ P.torus χ ≠ ⊥ →
      ∀ j : ℕ, 0 < j → ∀ v ∈ weightSpace ρ P.torus (χ * α.val ^ j), f v = 0)
    (R : TestAlgebra k) (b : GroupPoints P.negative.group R) (v : I → R) :
    extendFunctional R f (act ρ R (b ≫ P.negative.inclusion.hom.hom) v) =
      characterValue mu R (b ≫ p.projection.hom.hom) * extendFunctional R f v := by
  classical
  let := D.finiteRoots
  let Coord (α : Root P.torus) :=
    Σ Z : {Z : ClosedSubgroup H.val // IsRootSubgroup P.torus Z α.val},
      Σ A : AdditiveLine k, {x : A.group ≅ Z.val.group //
        HasScalarAction P.torus α.val (x.hom ≫ Z.val.inclusion)}
  have hc (α : Root P.torus) : Nonempty (Coord α) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, A, pos, _, hpos, _, hact, _, _⟩ := D.attached α
    exact ⟨⟨⟨_, hpos⟩, A, ⟨pos.root, hact⟩⟩⟩
  let coord (α : Root P.torus) := Classical.choice (hc α)
  let roots : RootSubgroupFamily P.torus := fun α ↦ (coord α).1
  obtain ⟨l, hl⟩ := existsEnumeration (subgroupRoots P.torus P.negative)
  obtain ⟨_, _, _, _, _, _, dec⟩ :=
    LinearAlgebraicGroups.RootData.BorelPositivity.borelPositivity
      H P.reductive P.torus P.split P.maximal
  obtain ⟨V, _, _, hV, _, _, _, _, _, chart⟩ := dec P.negative P.negativeBorel P.inNegative
  obtain ⟨E, hE⟩ := radicalProductFor roots l p.isRadical hV (chart roots l hl)
  obtain ⟨u, hu⟩ := splitPoint p.radical p.inclusion p.projection p.section_projection
    p.isKernel R b
  let t := b ≫ p.projection.hom.hom
  have hinc : p.inclusion.hom.hom ≫ P.negative.inclusion.hom.hom =
      P.torus.inclusion.hom.hom := (Grp.forget _).congr_map p.inclusion_comp
  have hb : b ≫ P.negative.inclusion.hom.hom =
      (t ≫ P.torus.inclusion.hom.hom) *
        (u ≫ p.radical.inclusion.hom.hom ≫ P.negative.inclusion.hom.hom) := by
    conv_lhs => rw [hu, MonObj.mul_comp]
    change (((b ≫ p.projection.hom.hom) ≫ p.inclusion.hom.hom) ≫
      P.negative.inclusion.hom.hom) * ((u ≫ p.radical.inclusion.hom.hom) ≫
      P.negative.inclusion.hom.hom) = _
    simp only [Category.assoc, hinc, t]
  let z := u ≫ E.inv
  have hz : z ≫ rootProduct roots l =
      u ≫ p.radical.inclusion.hom.hom ≫ P.negative.inclusion.hom.hom := by
    rw [← hE]
    change (u ≫ E.inv) ≫ E.hom ≫ _ = _
    erw [Category.assoc, E.inv_hom_id_assoc]
  have hrad : extendFunctional R f
      (act ρ R (z ≫ rootProduct roots l) v) = extendFunctional R f v := by
    apply rootProduct_invariance ρ roots _ l (fun α hα ↦ (hl.2 α).mp hα)
    intro α hα g w
    obtain ⟨a, ha⟩ := rootPoint_surjective (coord α).2.2.val R g
    have hg : g ≫ (roots α).val.inclusion.hom.hom =
        rootPoint ((coord α).2.2.val.hom ≫ (roots α).val.inclusion) R a := by
      rw [← ha]
      rfl
    rw [hg]
    exact LinearMap.congr_fun
      (root_invariance P ρ hρ f α (hvanish α hα) (roots α).val (roots α).property
        (coord α).2.1 (coord α).2.2.val (coord α).2.2.property R a) w
  rw [hb, act_mul, ← hz]
  have ht := LinearMap.congr_fun (torus_covariance P ρ mu f hf R t)
    (act ρ R (z ≫ rootProduct roots l) v)
  change _ = characterValue mu R t * _
  change extendFunctional R f (act ρ R (t ≫ P.torus.inclusion.hom.hom)
    (act ρ R (z ≫ rootProduct roots l) v)) = characterValue mu R t * _ at ht
  rw [ht, hrad]

open private pointIso inducedPoint evaluationLinear_act evaluationLinear_extend eval_torus
  IsLeftTranslation TranslatedEvaluation
  from LinearAlgebraicGroups.Representation.InducedSocle
open private realizes_unique from LinearAlgebraicGroups.Representation.SimpleClassification
open private fromCoaction toCoaction from_toCoaction act_contract contract_tmul contract_natural
  comp_equivariant from LinearAlgebraicGroups.Representation.PrimitiveLine
open private matrix_equivariant from LinearAlgebraicGroups.Representation.WeylModules
open private reciprocityEquiv from LinearAlgebraicGroups.Representation.InductionAdjunction

private def evaluationAtOne {P : OppositeBorelPair H} {U : ClosedSubgroup P.positive.group}
    {mu : Character P.torus.group} (N : SocleModel P U mu) : (N.I → k) →ₗ[k] k :=
  (counit (R := k) (A := N.A)).comp
    ((covariantFunctions N.restriction N.coordinate).subtype.comp
      N.inducedBasis.equivFun.symm.toLinearMap)

private theorem evaluationAtOne_other_weight
    {P : OppositeBorelPair H} {U : ClosedSubgroup P.positive.group}
    {mu χ : Character P.torus.group} (N : SocleModel P U mu) (hχ : χ ≠ mu)
    {v : N.I → k} (hv : v ∈ weightSpace N.inducedAction P.torus χ) :
    evaluationAtOne N v = 0 := by
  by_contra hn
  apply hχ
  apply LinearAlgebraicGroups.RootData.CharacterPairing.characterValuesDetectCharacters P.split
  intro R t
  have hρ := realizes_unique N.groupIso N.inducedBasis N.inducedCoaction
    N.inducedAction N.inducedAction_spec
  let h := LinearAlgebraicGroups.FlagLineBundle.covariantCoaction N.restriction N.coordinate
  have htrans : IsLeftTranslation N.inducedCoaction := by
    intro R g a w
    have h₁ := LinearMap.congr_fun N.leftTranslation w
    have h₂ := LinearMap.congr_fun h.choose_spec.1 w
    simp only [LinearMap.comp_apply] at h₁ h₂
    rw [h₁, ← h₂]
    exact h.choose_spec.2 R g a w
  have hact : TranslatedEvaluation N.groupIso N.inducedBasis N.inducedAction := by
    rw [hρ]
    exact evaluationLinear_act N.inducedBasis N.inducedCoaction (pointIso N.groupIso) htrans
  have heval := eval_torus N.projection mu N.groupIso N.borelIso N.restriction_spec
    N.character N.character_spec N.coordinate_spec N.inducedBasis N.inducedAction hact R t v
  rw [mem_weightSpace.mp hv R t, map_smul, evaluationLinear_extend] at heval
  change characterValue χ R t * algebraMap k R (evaluationAtOne N v) =
    characterValue mu R t * algebraMap k R (evaluationAtOne N v) at heval
  exact (IsUnit.mul_left_inj ((isUnit_iff_ne_zero.mpr hn).map (algebraMap k R))).mp heval


open RationalRepresentations (tensorCoordinate)
open private contract coord_contract coords_injective
  from LinearAlgebraicGroups.Representation.PrimitiveLine

omit [DecidableEq I] in
private theorem tensor_eq_of_contracts {A : HopfAlgebraCategory k}
    {V : Type u} [AddCommGroup V] [Module k V] (b : Module.Basis I k V)
    {x y : V ⊗[k] A} (h : ∀ ℓ : A →ₗ[k] k, contract ℓ x = contract ℓ y) : x = y := by
  let R := CommAlgCat.of k A
  apply coords_injective b R
  funext i
  by_contra hne
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero k (sub_ne_zero.mpr hne)
  apply hℓ
  rw [map_sub, sub_eq_zero]
  have hx := coord_contract b i R (AlgHom.id k A) ℓ x
  have hy := coord_contract b i R (AlgHom.id k A) ℓ y
  simp only [AlgHom.toLinearMap_id, LinearMap.comp_id, LinearMap.lTensor_id] at hx hy
  change b.equivFun (contract ℓ x) i = ℓ (tensorCoordinate b i x) at hx
  change b.equivFun (contract ℓ y) i = ℓ (tensorCoordinate b i y) at hy
  change ℓ (tensorCoordinate b i x) = ℓ (tensorCoordinate b i y)
  rw [← hx, ← hy, h ℓ]

private theorem coaction_equivariant
    {A : HopfAlgebraCategory k} (e : convolutionPoints A ≅ (groupPointsFunctor k).obj H.val)
    {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (b : Module.Basis I k V) (c : Module.Basis J k W)
    (δ : RightComodule k A V) (τ : RightComodule k A W) (f : V →ₗ[k] W)
    (hf : IsEquivariant (fromCoaction e b δ) (fromCoaction e c τ)
      (c.equivFun.toLinearMap.comp (f.comp b.equivFun.symm.toLinearMap))) :
    (f.rTensor A).comp δ.coaction = τ.coaction.comp f := by
  let R := CommAlgCat.of k A
  let g : GroupPoints H.val R := e.hom.app R (toConv (AlgHom.id k A))
  apply LinearMap.ext
  intro v
  change f.rTensor A (δ.coaction v) = τ.coaction (f v)
  apply tensor_eq_of_contracts c
  intro ℓ
  have hx := act_contract e b δ R (AlgHom.id k A) ℓ v
  have hy := act_contract e c τ R (AlgHom.id k A) ℓ (f v)
  change orbitCoefficient _ R g ℓ (b.equivFun v) = _ at hx
  change orbitCoefficient _ R g ℓ (c.equivFun (f v)) = _ at hy
  simp only [AlgHom.toLinearMap_id, LinearMap.comp_id] at hx hy
  have he := hf R g ℓ (b.equivFun v)
  rw [hx] at he
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at he
  rw [hy] at he
  rw [← contract_natural]
  exact c.equivFun.injective he

private theorem contract_restriction {A D : HopfAlgebraCategory k}
    {V : Type u} [AddCommGroup V] [Module k V] (q : A ⟶ D) (ℓ : D →ₗ[k] k)
    (z : V ⊗[k] A) :
    contract ℓ (q.hom.toAlgHom.toLinearMap.lTensor V z) =
      contract (ℓ.comp q.hom.toAlgHom.toLinearMap) z := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro v a
    rw [LinearMap.lTensor_tmul, contract_tmul, contract_tmul, LinearMap.comp_apply]
  · intro x y hx hy
    simp only [map_add, hx, hy]

private theorem borel_character_value {P : OppositeBorelPair H}
    {U : ClosedSubgroup P.positive.group} {mu : Character P.torus.group}
    (N : SocleModel P U mu) (R : TestAlgebra k) (a : WithConv (N.D →ₐ[k] R)) :
    characterValue mu R ((pointIso N.borelIso).hom.app R a ≫
      N.projection.projection.hom.hom) = a (N.coordinate : N.D) := by
  let C := DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters
  have he := inducedPoint (q := N.character) (Iso.refl (specGroup C)) N.borelIso
    (N.projection.projection ≫ mu)
    (by change specGroupMap N.character ≫ 𝟙 _ = _
        rw [Category.comp_id]
        exact N.character_spec) R a
  change (hopfSpecPointIso C).hom.app R (toConv (a.ofConv.comp N.character.hom.toAlgHom)) =
    (pointIso N.borelIso).hom.app R a ≫
      (N.projection.projection.hom.hom ≫ mu.hom.hom) at he
  have hi := ((hopfSpecPointIso C).app R).hom_inv_id_apply
    (toConv (a.ofConv.comp N.character.hom.toAlgHom))
  change (hopfSpecPointIso C).inv.app R
    ((hopfSpecPointIso C).hom.app R (toConv (a.ofConv.comp N.character.hom.toAlgHom))) = _ at hi
  erw [characterValue_eq_eval, Category.assoc, ← he, hi, N.coordinate_spec]
  rfl

private theorem equivariant_character_of_covariance {P : OppositeBorelPair H}
    {U : ClosedSubgroup P.positive.group} {mu : Character P.torus.group}
    (N : SocleModel P U mu) (ρ : Representation H.val I) (f : (I → k) →ₗ[k] k)
    (hf : ∀ (R : TestAlgebra k) (g : GroupPoints P.negative.group R) (v : I → R),
      extendFunctional R f (act ρ R (g ≫ P.negative.inclusion.hom.hom) v) =
        characterValue mu R (g ≫ N.projection.projection.hom.hom) * extendFunctional R f v)
    (χ : RightComodule k N.D k) (hχ : ∀ z, χ.coaction z = z ⊗ₜ[k] (N.coordinate : N.D)) :
    let δ := toCoaction (pointIso N.groupIso) (Pi.basisFun k I) ρ
    f ∈ InductionAdjunction.equivariantHom
      (N.restriction.hom.toAlgHom.toLinearMap.lTensor (I → k) ∘ₗ δ.coaction) χ.coaction := by
  let E := pointIso N.groupIso
  let b := Pi.basisFun k I
  let δ := toCoaction E b ρ
  let R := CommAlgCat.of k N.D
  let a : WithConv (N.D →ₐ[k] R) := toConv (AlgHom.id k N.D)
  let g : GroupPoints P.negative.group R := (pointIso N.borelIso).hom.app R a
  have hg := inducedPoint N.groupIso N.borelIso P.negative.inclusion N.restriction_spec R a
  change E.hom.app R (toConv N.restriction.hom.toAlgHom) =
    g ≫ P.negative.inclusion.hom.hom at hg
  change (f.rTensor N.D).comp (_ ∘ₗ δ.coaction) = χ.coaction.comp f
  apply LinearMap.ext
  intro v
  change f.rTensor N.D (N.restriction.hom.toAlgHom.toLinearMap.lTensor (I → k) (δ.coaction v)) =
    χ.coaction (f v)
  rw [hχ]
  let d : Module.Basis (PUnit : Type u) k k := Module.basisUnique (PUnit : Type u) (by simp : Module.finrank k k = 1)
  apply tensor_eq_of_contracts d
  intro ℓ
  rw [← contract_natural, contract_restriction, contract_tmul]
  have hac := act_contract E b δ R N.restriction.hom.toAlgHom ℓ v
  rw [from_toCoaction, hg] at hac
  have hac' : orbitCoefficient ρ R (g ≫ P.negative.inclusion.hom.hom) ℓ v =
      contract (ℓ.comp N.restriction.hom.toAlgHom.toLinearMap) (δ.coaction v) := by
    change (fun i ↦ ℓ (act ρ R (g ≫ P.negative.inclusion.hom.hom) (extendVector R v) i)) = _
    simpa only [b, Pi.basisFun_equivFun, LinearEquiv.refl_apply] using hac
  rw [← hac']
  change f (fun i ↦ ℓ (act ρ R (g ≫ P.negative.inclusion.hom.hom) (extendVector R v) i)) = _
  rw [← extendFunctional_contract R f ℓ
    (act ρ R (g ≫ P.negative.inclusion.hom.hom) (extendVector R v))]
  have hv := hf R g (extendVector R v)
  rw [borel_character_value N R a, extendFunctional_apply] at hv
  rw [hv]
  change ℓ ((N.coordinate : N.D) * algebraMap k N.D (f v)) = ℓ (N.coordinate : N.D) • f v
  rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  rfl

private theorem retract_of_character {P : OppositeBorelPair H}
    {U : ClosedSubgroup P.positive.group} {mu : Character P.torus.group}
    (N : SocleModel P U mu) (ρ : Representation H.val I)
    (i : (N.I → k) →ₗ[k] (I → k)) (hi : IsEquivariant N.inducedAction ρ i)
    (f : (I → k) →ₗ[k] k) (hf : f.comp i = evaluationAtOne N)
    (hcov : ∀ (R : TestAlgebra k) (g : GroupPoints P.negative.group R) (v : I → R),
      extendFunctional R f (act ρ R (g ≫ P.negative.inclusion.hom.hom) v) =
        characterValue mu R (g ≫ N.projection.projection.hom.hom) * extendFunctional R f v) :
    ∃ r : (I → k) →ₗ[k] (N.I → k), IsEquivariant ρ N.inducedAction r ∧
      r.comp i = LinearMap.id := by
  obtain ⟨χ, hχ⟩ := LinearAlgebraicGroups.FlagLineBundle.characterLine N.D N.coordinate
  let E := pointIso N.groupIso
  let b := Pi.basisFun k I
  let W := covariantFunctions N.restriction N.coordinate
  let δ := toCoaction E b ρ
  let τ := N.inducedCoaction
  let B := N.inducedBasis.equivFun
  have hρ : fromCoaction E b δ = ρ := from_toCoaction E b ρ
  have hτ : fromCoaction E N.inducedBasis τ = N.inducedAction :=
    (realizes_unique _ _ _ _ N.inducedAction_spec).symm
  let j : W →ₗ[k] (I → k) := i.comp B.toLinearMap
  have hj : (j.rTensor N.A).comp τ.coaction = δ.coaction.comp j := by
    apply coaction_equivariant E N.inducedBasis b
    rw [hρ, hτ]
    simpa only [j, B, b, LinearMap.comp_assoc, Pi.basisFun_equivFun,
      LinearEquiv.refl_toLinearMap, LinearEquiv.comp_symm, LinearMap.id_comp,
      LinearMap.comp_id] using hi
  let F := reciprocityEquiv N.restriction N.coordinate χ τ δ hχ N.leftTranslation
  let l := F.symm ⟨f, equivariant_character_of_covariance N ρ f hcov χ hχ⟩
  have hl : (l.val.rTensor N.A).comp δ.coaction = τ.coaction.comp l.val := l.property
  let r := B.toLinearMap.comp l.val
  have hr : IsEquivariant ρ N.inducedAction r := by
    have he := matrix_equivariant E b N.inducedBasis hl
    rw [hρ, hτ] at he
    simpa only [r, B, b, Pi.basisFun_equivFun, LinearEquiv.refl_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.comp_id] using he
  refine ⟨r, hr, ?_⟩
  let X : InductionAdjunction.equivariantHom τ.coaction τ.coaction :=
    ⟨l.val.comp j, by
      change ((l.val.comp j).rTensor N.A).comp τ.coaction = τ.coaction.comp (l.val.comp j)
      rw [LinearMap.rTensor_comp, LinearMap.comp_assoc, hj, ← LinearMap.comp_assoc, hl,
        LinearMap.comp_assoc]⟩
  let Y : InductionAdjunction.equivariantHom τ.coaction τ.coaction :=
    ⟨LinearMap.id, by
      change ((LinearMap.id).rTensor N.A).comp τ.coaction = τ.coaction.comp LinearMap.id
      rw [LinearMap.rTensor_id, LinearMap.id_comp, LinearMap.comp_id]⟩
  let F₀ := reciprocityEquiv N.restriction N.coordinate χ τ τ hχ N.leftTranslation
  have hlval := LinearEquiv.apply_symm_apply F
    ⟨f, equivariant_character_of_covariance N ρ f hcov χ hχ⟩
  have hlval' (v : I → k) : counit (R := k) (l.val v : N.A) = f v :=
    congrArg (fun x ↦ x.val v) hlval
  have hXY : X = Y := by
    apply F₀.injective
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    change counit (R := k) (l.val (i (B w)) : N.A) = counit (R := k) (w : N.A)
    rw [hlval']
    have hw := LinearMap.congr_fun hf (B w)
    change f (i (B w)) = _ at hw
    simpa only [evaluationAtOne, LinearMap.comp_apply, LinearEquiv.coe_coe,
      B, LinearEquiv.symm_apply_apply, Submodule.subtype_apply] using hw
  apply LinearMap.ext
  intro v
  have hw := congrArg (fun x : InductionAdjunction.equivariantHom τ.coaction τ.coaction ↦
    x.val (B.symm v)) hXY
  change l.val (i (B (B.symm v))) = B.symm v at hw
  rw [LinearEquiv.apply_symm_apply] at hw
  change B (l.val (i v)) = v
  rw [hw, LinearEquiv.apply_symm_apply]


private theorem split_of_weight_order (P : OppositeBorelPair H) [IsCommMonObj P.torus.group.X]
    (D : Datum P.torus) (height : Additive (Character P.torus.group) →ₗ[ℤ] ℝ)
    (hreg : ∀ α : Root P.torus, height (Additive.ofMul α.val) ≠ 0)
    (hpos : ∀ α : Root P.torus, α ∈ subgroupRoots P.torus P.positive ↔
      0 < height (Additive.ofMul α.val))
    {U : ClosedSubgroup P.positive.group} {lam mu : Character P.torus.group}
    (N : SocleModel P U mu) (Δ : Representation H.val I)
    (hΔ : HighestWeightLine P Δ lam) (hN : HighestWeightLine P N.inducedAction mu)
    (hle : ¬ (mu ≠ lam ∧ DominanceLE P.torus P.positive mu lam)) :
    ExtensionsSplit Δ N.inducedAction := by
  classical
  intro M _ _ ρ i q hi hq hInj hExact _
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective i (LinearMap.ker_eq_bot.mpr hInj)
  obtain ⟨f, hf⟩ := weightProjection ρ P.torus mu
  let ℓ := (evaluationAtOne N).comp (r.comp f)
  have hℓ : ∀ χ ≠ mu, ∀ v ∈ weightSpace ρ P.torus χ, ℓ v = 0 := by
    intro χ hχ v hv
    simp only [ℓ, LinearMap.comp_apply, hf χ v hv, ite_eq_right hχ, map_zero]
  have hl : ℓ.comp i = evaluationAtOne N := by
    apply linear_eq_on_weights P N.inducedAction
    intro χ v hv
    by_cases hχ : χ = mu
    · have he := LinearMap.congr_fun hr v
      change r (i v) = v at he
      simp only [ℓ, LinearMap.comp_apply, hf χ (i v) (equivariant_weight hi hv), ite_eq_left hχ, he]
    · exact (hℓ χ hχ (i v) (equivariant_weight hi hv)).trans
        (evaluationAtOne_other_weight N hχ hv).symm
  apply retract_of_character N ρ i hi ℓ hl
  apply borel_covariance P D ρ (rootOrbit ρ P.torus) N.projection mu ℓ hℓ
  intro α hα χ hχ j hj v hv
  have hn : α ∉ subgroupRoots P.torus P.positive := by
    rw [P.opposite] at hα
    exact hα
  rcases middle_weights hi hq hInj hExact hχ with hMu | hLam
  · exact hℓ _ (neg_shift P.torus P.positive D height hreg hpos α hn (hN.2 _ hMu) j hj).1 v hv
  · apply hℓ _ _ v hv
    intro he
    exact hle (he ▸ neg_shift P.torus P.positive D height hreg hpos α hn (hΔ.2 _ hLam) j hj)

open private isDual_exists isDual_symm dotDual dotDual_apply transposeMap transposeMap_dot
  transposeMap_equivariant from LinearAlgebraicGroups.Representation.WeylModules
open private coefficientMap from LinearAlgebraicGroups.Representation.PrimitiveLine

private theorem exact_transpose {i : (J → k) →ₗ[k] (M → k)} {q : (M → k) →ₗ[k] (I → k)}
    (h : Function.Exact i q) : Function.Exact (transposeMap q) (transposeMap i) := by
  intro v
  have he : transposeMap i v = 0 ↔ dotDual v ∈ LinearMap.ker i.dualMap := by
    change dotDual.symm (i.dualMap (dotDual v)) = 0 ↔ i.dualMap (dotDual v) = 0
    rw [← dotDual.symm.map_zero, dotDual.symm.injective.eq_iff]
  have h₁ : LinearMap.ker i.dualMap = LinearMap.range q.dualMap := by
    rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range,
      LinearMap.range_dualMap_eq_dualAnnihilator_ker, LinearMap.exact_iff.mp h]
  rw [he, h₁]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨dotDual.symm f, ?_⟩
    change dotDual.symm (q.dualMap (dotDual (dotDual.symm f))) = v
    rw [LinearEquiv.apply_symm_apply, hf, LinearEquiv.symm_apply_apply]
  · rintro ⟨w, hw⟩
    refine ⟨dotDual w, ?_⟩
    change dotDual.symm (q.dualMap (dotDual w)) = v at hw
    rw [← hw, LinearEquiv.apply_symm_apply]

private theorem retract_of_section {ρ : Representation H.val J} {σ : Representation H.val M}
    {τ : Representation H.val I} {i : (J → k) →ₗ[k] (M → k)}
    {q : (M → k) →ₗ[k] (I → k)} (hi : IsEquivariant ρ σ i)
    (hq : IsEquivariant σ τ q) (hInj : Function.Injective i) (hExact : Function.Exact i q)
    (s : (I → k) →ₗ[k] (M → k)) (hs : IsEquivariant τ σ s) (hsec : q.comp s = LinearMap.id) :
    ∃ r : (M → k) →ₗ[k] (J → k), IsEquivariant σ ρ r ∧ r.comp i = LinearMap.id := by
  let f : (M → k) →ₗ[k] (M → k) := LinearMap.id - s.comp q
  have hf : ∀ v, q (f v) = 0 := by
    intro v
    have he := LinearMap.congr_fun hsec (q v)
    change q (s (q v)) = q v at he
    simp only [f, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_sub, he, sub_self]
  let e := LinearEquiv.ofInjective i hInj
  let F := f.codRestrict (LinearMap.range i) fun v ↦ (hExact _).mp (hf v)
  let r := e.symm.toLinearMap.comp F
  have hr (v : M → k) : i (r v) = f v :=
    congrArg Subtype.val (e.apply_symm_apply (F v))
  refine ⟨r, ?_, ?_⟩
  · intro R g ℓ v
    apply hInj
    rw [hr, hi R g ℓ (r v), hr]
    have he := comp_equivariant hq hs R g ℓ v
    change (s.comp q) (orbitCoefficient σ R g ℓ v) =
      orbitCoefficient σ R g ℓ ((s.comp q) v) at he
    change orbitCoefficient σ R g ℓ v - (s.comp q) (orbitCoefficient σ R g ℓ v) =
      coefficientMap σ R g ℓ (v - (s.comp q) v)
    rw [map_sub, he]
    rfl
  · apply LinearMap.ext
    intro v
    apply hInj
    change i (r (i v)) = i v
    rw [hr]
    have hz : q (i v) = 0 := (hExact _).mpr ⟨v, rfl⟩
    simp only [f, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hz,
      map_zero, sub_zero]

private theorem split_of_dual_split {ρ ρ' : Representation H.val J}
    {τ τ' : Representation H.val I} (hρ : IsDual ρ ρ') (hτ : IsDual τ τ')
    (A : HopfAlgebraCategory k) (e : specGroup A ≅ H.val)
    (h : ExtensionsSplit ρ' τ') : ExtensionsSplit τ ρ := by
  intro M _ _ σ i q hi hq hInj hExact hSurj
  obtain ⟨σ', hσ⟩ := isDual_exists A e σ
  have hinj' : Function.Injective (transposeMap q) :=
    dotDual.symm.injective.comp
      ((LinearMap.dualMap_injective_of_surjective hSurj).comp dotDual.injective)
  have hsurj' : Function.Surjective (transposeMap i) :=
    dotDual.symm.surjective.comp
      ((LinearMap.dualMap_surjective_of_injective hInj).comp dotDual.surjective)
  obtain ⟨r, hr, hrq⟩ := h σ' (transposeMap q) (transposeMap i)
    (transposeMap_equivariant hσ hτ hq) (transposeMap_equivariant hρ hσ hi)
    hinj' (exact_transpose hExact) hsurj'
  apply retract_of_section hi hq hInj hExact (transposeMap r)
    (transposeMap_equivariant (isDual_symm hσ) (isDual_symm hτ) hr)
  apply LinearMap.ext
  intro v
  apply dotDual.injective
  apply LinearMap.ext
  intro w
  change dotDual (q (transposeMap r v)) w = dotDual v w
  simp only [dotDual_apply]
  calc
    q (transposeMap r v) ⬝ᵥ w = transposeMap q w ⬝ᵥ transposeMap r v := by
      rw [transposeMap_dot, dotProduct_comm]
    _ = transposeMap r v ⬝ᵥ transposeMap q w := dotProduct_comm _ _
    _ = v ⬝ᵥ r (transposeMap q w) := transposeMap_dot r _ _
    _ = v ⬝ᵥ w := by
      rw [show r (transposeMap q w) = w from LinearMap.congr_fun hrq w]

open private longest_flips_sign from LinearAlgebraicGroups.Flag.OpenCell
open private dominance_lt from LinearAlgebraicGroups.Representation.PrimitiveLine
open private length_inverse from LinearAlgebraicGroups.RootData.SimpleRoots
open private induced_highest dual_highest oppositeWeight_inverse
  from LinearAlgebraicGroups.Representation.WeylModules

private theorem opposite_height (P : OppositeBorelPair H) [IsCommMonObj P.torus.group.X]
    (D : Datum P.torus) (e : DatumAndWeyl.Identification D)
    (f : Additive (Character P.torus.group) →ₗ[ℤ] ℤ) (b : D.rootDatum.Base)
    (hf : ∀ α, f (D.rootDatum.root α) ≠ 0)
    (hb : ∀ α, b.IsPos α ↔ α ∈ SimpleRoots.positive D.rootDatum f)
    (hB : ∀ α, b.IsPos α ↔ α ∈ subgroupRoots P.torus P.positive)
    (height : Additive (Character P.torus.group) →ₗ[ℤ] ℝ)
    (hreg : ∀ α : Root P.torus, height (Additive.ofMul α.val) ≠ 0)
    (hpos : ∀ α : Root P.torus, α ∈ subgroupRoots P.torus P.positive ↔
      0 < height (Additive.ofMul α.val))
    (w : D.rootDatum.weylGroup)
    (hw : ∀ v, SimpleRoots.wordLength D.rootDatum b v ≤ SimpleRoots.wordLength D.rootDatum b w⁻¹) :
    ∃ g : Additive (Character P.torus.group) →ₗ[ℤ] ℝ,
      (∀ α ∈ subgroupRoots P.torus P.positive, 0 < g (Additive.ofMul α.val)) ∧
      ∀ chi : Character P.torus.group,
        g (Additive.ofMul (oppositeWeight e w chi)) = height (Additive.ofMul chi) := by
  let := D.finiteRoots
  let := D.freeCharacters
  let := D.finiteCharacters
  let := D.reduced
  let a := (w⁻¹).val.weightEquiv.toLinearMap
  let g := -(height.comp a)
  refine ⟨g, ?_, ?_⟩
  · intro α hα
    let β := D.rootDatum.weylGroupToPerm w⁻¹ α
    have hβ : ¬ β ∈ subgroupRoots P.torus P.positive := fun h ↦
      (longest_flips_sign b f hf hb w⁻¹ hw α).mp ((hB β).mpr h) ((hB α).mpr hα)
    have hneg := lt_of_le_of_ne (not_lt.mp (fun he ↦ hβ ((hpos β).mpr he))) (hreg β)
    have he : a (Additive.ofMul α.val) = Additive.ofMul β.val := by
      change (w⁻¹).val.weightEquiv (Additive.ofMul α.val) = Additive.ofMul β.val
      rw [← D.root_eq α, ← D.root_eq β]
      exact D.rootDatum.weylGroup_apply_root _ _
    change 0 < -height (a (Additive.ofMul α.val))
    rw [he]
    exact neg_pos.mpr hneg
  · intro chi
    have hg (nu : Character P.torus.group) :
        g (Additive.ofMul nu) = height (Additive.ofMul (oppositeWeight e w⁻¹ nu)) := by
      change -height ((w⁻¹).val.weightEquiv (Additive.ofMul nu)) =
        height (-Additive.ofMul ((e.labelEquiv w⁻¹).val nu))
      rw [map_neg, e.characterAction]
    rw [hg, oppositeWeight_inverse e w]

/-- Every finite-dimensional rational extension of a Weyl module by a
costandard module splits. -/
theorem costandardExtensions : Statement.{u} := by
  classical
  intro k _ _ _ _ _ H _ _ P U hU
  let T := P.torus
  let B := P.positive
  obtain ⟨comm, D, e, b, w, hB, hw, hmodels⟩ :=
    LinearAlgebraicGroups.Representation.WeylModules.weylModules H P U hU
  let := comm
  let := D.finiteRoots
  let := D.freeCharacters
  let := D.finiteCharacters
  let := D.reduced
  obtain ⟨c, _, hc, _, hpos⟩ :=
    (LinearAlgebraicGroups.RootData.BorelsAndChambers.borelsThroughT
      H P.reductive T P.split P.maximal).1 B P.positiveBorel P.inPositive
  let f := Specs.SimpleRoots.evaluate D c
  have hf (α : Root T) : f (D.rootDatum.root α) = pairing T.group α.val c := by
    change D.rootDatum.toLinearMap (D.rootDatum.root α) (Additive.ofMul c) = _
    rw [D.root_eq, D.pairing_eq]
  have hreg (α : Root T) : f (D.rootDatum.root α) ≠ 0 := hf α ▸ hc α
  have hb (α : Root T) : b.IsPos α ↔ α ∈ SimpleRoots.positive D.rootDatum f := by
    rw [hB, hpos]
    change 0 < pairing T.group α.val c ↔ 0 < f (D.rootDatum.root α)
    rw [hf]
  let height := Specs.SimpleRoots.realFunctional f
  have hheight (α : Root T) : α ∈ subgroupRoots T B ↔ 0 < height (Additive.ofMul α.val) := by
    rw [← hB, hb, ← D.root_eq α]
    change 0 < f (D.rootDatum.root α) ↔ 0 < (f (D.rootDatum.root α) : ℝ)
    exact_mod_cast Iff.rfl
  have hheight_reg (α : Root T) : height (Additive.ofMul α.val) ≠ 0 := by
    rw [← D.root_eq α]
    change (f (D.rootDatum.root α) : ℝ) ≠ 0
    exact_mod_cast hreg α
  have hwi (v) : SimpleRoots.wordLength D.rootDatum b v ≤
      SimpleRoots.wordLength D.rootDatum b w⁻¹ := by
    rw [length_inverse]
    exact hw v
  refine ⟨comm, D, e, b, w, hB, hw, ?_⟩
  intro lam mu hlam hmu
  constructor
  · obtain ⟨_, _, S, Δ, _, hΔ, _⟩ := hmodels lam hlam
    obtain ⟨_, N, _⟩ := hmodels mu hmu
    exact ⟨S, N, Δ, hΔ⟩
  intro S N Δ hdual
  let fpos (α : Root T) (hα : α ∈ subgroupRoots T B) := (hheight α).mp hα
  have hLamOpp : HighestWeightLine P S.inducedAction (oppositeWeight e w lam) :=
    induced_highest P D hU height fpos S (rootOrbit S.inducedAction T)
  have hMu : HighestWeightLine P N.inducedAction mu :=
    induced_highest P D hU height fpos N (rootOrbit N.inducedAction T)
  have hLam : HighestWeightLine P Δ lam := by
    have he := dual_highest P D e f b hreg hb hB height fpos w⁻¹ hwi hdual
      (oppositeWeight e w lam) hLamOpp
    rwa [oppositeWeight_inverse e w] at he
  rcases Classical.em (mu ≠ lam ∧ DominanceLE T B mu lam) with h | h
  · obtain ⟨N', hN'⟩ := isDual_exists N.A N.groupIso N.inducedAction
    have hMuOpp := dual_highest P D e f b hreg hb hB height fpos w hw hN' mu hMu
    apply split_of_dual_split (ρ := N.inducedAction) (ρ' := N') (τ := Δ)
      (τ' := S.inducedAction) hN' (isDual_symm hdual) S.A S.groupIso
    apply split_of_weight_order (I := N.I) P D height hheight_reg hheight
      S N' hMuOpp hLamOpp
    rintro ⟨hne, hle⟩
    obtain ⟨g, hgpos, hg⟩ := opposite_height P D e f b hreg hb hB height hheight_reg
      hheight w hwi
    have hlt := dominance_lt (T := T) (B := B) g (fun a ↦ hgpos a.val a.property.1) hne hle
    rw [hg, hg] at hlt
    exact (not_lt_of_gt (dominance_lt (T := T) (B := B) height
      (fun a ↦ fpos a.val a.property.1) h.1 h.2)) hlt
  · intro L _ _ middle i q hi hq hInj hExact hSurj
    exact split_of_weight_order (I := S.I) P D height hheight_reg hheight
      N Δ hLam hMu h (M := L) middle i q hi hq hInj hExact hSurj

end LinearAlgebraicGroups.Arithmetic.CostandardExtensions
