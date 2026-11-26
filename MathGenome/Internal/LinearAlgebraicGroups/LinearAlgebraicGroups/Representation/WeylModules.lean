import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.WeylModules
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SimpleClassification
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.CompleteReducibility
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Dual.Lemmas

open AlgebraicGeometry CategoryTheory Opposite WithConv
open CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj TensorProduct

universe u

noncomputable section

namespace LinearAlgebraicGroups.Representation.WeylModules

open LinearAlgebraicGroups.Specs
open Specs.WeylModules
open Specs.AdjointRepresentation (GroupPoints)
open Specs.FlagLineBundle (OppositeBorelPair)
open Specs.SimpleClassification (SocleModel)
open Specs.RootWeightAction (Representation act extendVector weightSpace)
open Specs.PrimitiveLine (IsEquivariant IsSimple IsStable orbitCoefficient)
open private orbit_le_iff stable_ker fromCoaction toCoaction
  act_contract contract contract_natural from_toCoaction
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.PrimitiveLine
open private pointIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.InducedSocle
open private realizes_unique from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SimpleClassification

variable {k I J : Type u} [Field k] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {G : AffineAlgebraicGroup k}

private theorem isDual_exists (A : HopfAlgebraCategory k) (e : specGroup A ≅ G.val)
    (ρ : Representation G.val I) :
    ∃ σ : Representation G.val I, IsDual ρ σ := by
  let E := pointIso e
  let b := Pi.basisFun k I
  let δ := toCoaction E b ρ
  let σ := fromCoaction E b.dualBasis (RationalRepresentations.dualCoaction A b δ)
  refine ⟨σ, ?_⟩
  intro R g
  obtain ⟨a, rfl⟩ := ((forget GrpCat).mapIso (E.app R)).toEquiv.surjective g
  rw [← from_toCoaction E b ρ]
  change (((RationalRepresentations.pointsCoactionEquiv A b.dualBasis).symm
    (RationalRepresentations.dualCoaction A b δ)).app R
      (E.inv.app R (E.hom.app R a))).val = _
  have h : E.inv.app R (E.hom.app R a) = a :=
    congrArg (fun f : convolutionPoints A ⟶ convolutionPoints A ↦ f.app R a) E.hom_inv_id
  change _ = ((((RationalRepresentations.pointsCoactionEquiv A b).symm δ).app R
    (E.inv.app R (E.hom.app R a)))⁻¹).val.transpose
  rw [h]
  ext i j
  change a.ofConv (RationalRepresentations.coefficients A b.dualBasis
    (RationalRepresentations.dualCoaction A b δ) i j) =
    a.ofConv (HopfAlgebra.antipode k (RationalRepresentations.coefficients A b δ j i))
  rw [RationalRepresentations.dualCoaction, RationalRepresentations.coefficients_coactionOfMatrix]
  rfl

private theorem dotProduct_coefficient_dual {ρ σ : Representation G.val I} (h : IsDual ρ σ)
    (R : TestAlgebra k) (g : GroupPoints G.val R) (ℓ : R →ₗ[k] k) (x y : I → k) :
    orbitCoefficient σ R g ℓ x ⬝ᵥ y = x ⬝ᵥ orbitCoefficient ρ R g⁻¹ ℓ y := by
  have hg : (σ.app R g : Matrix.GeneralLinearGroup I R).val =
      (ρ.app R g⁻¹ : Matrix.GeneralLinearGroup I R).val.transpose := by
    rw [h, show (ρ.app R g⁻¹ : Matrix.GeneralLinearGroup I R) = (ρ.app R g)⁻¹ from
      map_inv (ρ.app R).hom g]
  simp only [orbitCoefficient, act, hg, Matrix.transpose_apply, dotProduct,
    Matrix.mulVec, extendVector, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext i
  congr 1
  funext j
  rw [mul_comm _ (algebraMap k R (x i)), mul_comm _ (algebraMap k R (y j)), ← Algebra.smul_def, ← Algebra.smul_def, map_smul,
    map_smul, smul_eq_mul, smul_eq_mul]
  ring

private theorem isDual_symm {ρ σ : Representation G.val I} (h : IsDual ρ σ) : IsDual σ ρ := by
  intro R g
  have h' := h R g⁻¹
  have hs : (σ.app R g⁻¹ : Matrix.GeneralLinearGroup I R) = (σ.app R g)⁻¹ :=
    map_inv (σ.app R).hom g
  have hr : (ρ.app R g⁻¹ : Matrix.GeneralLinearGroup I R) = (ρ.app R g)⁻¹ :=
    map_inv (ρ.app R).hom g
  rw [hs, hr, inv_inv] at h'
  rw [h', Matrix.transpose_transpose]

private def dotDual : (I → k) ≃ₗ[k] Module.Dual k (I → k) :=
  LinearMap.linearEquivOfInjective (dotProductBilin k k) (fun x y h => by
      funext i
      simpa only [dotProductBilin_apply_apply, dotProduct_single_one] using
        congrArg (fun f : Module.Dual k (I → k) => f (Pi.single i 1)) h) (by rw [Subspace.dual_finrank_eq])

private theorem dotDual_apply (x y : I → k) : dotDual x y = x ⬝ᵥ y := rfl

private def orthogonal (M : Submodule k (I → k)) : Submodule k (I → k) :=
  M.dualAnnihilator.comap dotDual.toLinearMap

private theorem mem_orthogonal {M : Submodule k (I → k)} {x : I → k} :
    x ∈ orthogonal M ↔ ∀ y ∈ M, x ⬝ᵥ y = 0 :=
  Submodule.mem_dualAnnihilator _

private theorem orthogonal_anti : Antitone (orthogonal : Submodule k (I → k) → _) :=
  fun _ _ h _ hx => mem_orthogonal.mpr fun y hy => mem_orthogonal.mp hx y (h hy)

private theorem orthogonal_orthogonal (M : Submodule k (I → k)) :
    orthogonal (orthogonal M) = M := by
  ext x
  rw [mem_orthogonal, ← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff M x]
  constructor
  · intro h f hf
    obtain ⟨y, rfl⟩ := dotDual.surjective f
    rw [dotDual_apply, dotProduct_comm]
    exact h y hf
  · intro h y hy
    rw [dotProduct_comm, ← dotDual_apply]
    exact h _ hy

private theorem orthogonal_bot : orthogonal (⊥ : Submodule k (I → k)) = ⊤ := by
  simp [orthogonal, Submodule.dualAnnihilator_bot]

private theorem orthogonal_top : orthogonal (⊤ : Submodule k (I → k)) = ⊥ := by
  rw [← orthogonal_bot, orthogonal_orthogonal]

private theorem stable_orthogonal {ρ σ : Representation G.val I} (h : IsDual ρ σ)
    {M : Submodule k (I → k)} (hM : IsStable ρ M) : IsStable σ (orthogonal M) := by
  intro v hv
  apply (orbit_le_iff σ v _).mpr
  intro R g ℓ
  apply mem_orthogonal.mpr
  intro w hw
  rw [dotProduct_coefficient_dual h]
  exact mem_orthogonal.mp hv _ ((orbit_le_iff ρ w M).mp (hM w hw) R g⁻¹ ℓ)

private theorem dual_simple {ρ σ : Representation G.val I} (h : IsDual ρ σ)
    (hs : IsSimple ρ) : IsSimple σ := by
  refine ⟨hs.1, fun M hM => ?_⟩
  rcases hs.2 _ (stable_orthogonal (isDual_symm h) hM) with hbot | htop
  · right
    rw [← orthogonal_orthogonal M, hbot, orthogonal_bot]
  · left
    rw [← orthogonal_orthogonal M, htop, orthogonal_top]

private def transposeMap (f : (I → k) →ₗ[k] (J → k)) : (J → k) →ₗ[k] (I → k) :=
  dotDual.symm.toLinearMap.comp (f.dualMap.comp dotDual.toLinearMap)

private theorem transposeMap_dot (f : (I → k) →ₗ[k] (J → k)) (x : J → k) (y : I → k) :
    transposeMap f x ⬝ᵥ y = x ⬝ᵥ f y := by
  rw [← dotDual_apply, ← dotDual_apply]
  change dotDual (dotDual.symm (f.dualMap (dotDual x))) y = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

private theorem transposeMap_equivariant {ρ ρ' : Representation G.val I}
    {σ σ' : Representation G.val J} (hr : IsDual ρ ρ') (hs : IsDual σ σ')
    {f : (I → k) →ₗ[k] (J → k)} (hf : IsEquivariant ρ σ f) :
    IsEquivariant σ' ρ' (transposeMap f) := by
  intro R g ℓ x
  have h (y : I → k) :
      transposeMap f (orbitCoefficient σ' R g ℓ x) ⬝ᵥ y =
        orbitCoefficient ρ' R g ℓ (transposeMap f x) ⬝ᵥ y := by
    rw [transposeMap_dot, dotProduct_coefficient_dual hs, ← hf, ← transposeMap_dot,
      dotProduct_coefficient_dual hr]
  apply dotDual.injective
  exact LinearMap.ext h

private theorem exists_simpleSubmodule {ρ : Representation G.val I}
    {M : Submodule k (I → k)} (hM : IsStable ρ M) (hn : M ≠ ⊥) :
    ∃ N ≤ M, InducedSocle.IsSimpleSubmodule ρ N := by
  classical
  let Q (n : ℕ) := ∃ N : Submodule k (I → k),
    IsStable ρ N ∧ N ≠ ⊥ ∧ N ≤ M ∧ Module.finrank k N = n
  have hex : ∃ n, Q n := ⟨_, M, hM, hn, le_rfl, rfl⟩
  obtain ⟨N, hN, hN0, hNM, hd⟩ := Nat.find_spec hex
  refine ⟨N, hNM, hN, hN0, fun L hL hLN => ?_⟩
  by_cases hL0 : L = ⊥
  · exact Or.inl hL0
  right
  by_contra hne
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hLN hne)
  exact (Nat.find_min' hex ⟨L, hL, hL0, hLN.trans hNM, rfl⟩).not_gt (hd ▸ hlt)

private theorem head_of_dual_socle {ρ ρ' : Representation G.val I}
    {σ σ' : Representation G.val J} (hr : IsDual ρ ρ') (hs : IsDual σ σ')
    (hσ : IsSimple σ) {f : (J → k) →ₗ[k] (I → k)}
    (hf : IsEquivariant σ ρ f) (hi : Function.Injective f)
    (hsocle : ∀ M, InducedSocle.IsSimpleSubmodule ρ M → M = LinearMap.range f) :
    HasHead ρ' σ' := by
  let p := transposeMap f
  have hp : Function.Surjective p := dotDual.symm.surjective.comp
    ((LinearMap.dualMap_surjective_of_injective hi).comp dotDual.surjective)
  have hk : LinearMap.ker p = orthogonal (LinearMap.range f) := by
    ext x
    rw [LinearMap.mem_ker, mem_orthogonal]
    constructor
    · intro h y hy
      obtain ⟨z, rfl⟩ := hy
      rw [← transposeMap_dot, show transposeMap f x = 0 from h, zero_dotProduct]
    · intro h
      apply dotDual.injective
      apply LinearMap.ext
      intro y
      rw [dotDual_apply, dotDual_apply, zero_dotProduct, transposeMap_dot]
      exact h _ (LinearMap.mem_range_self _ _)
  refine ⟨p, transposeMap_equivariant hs hr hf, hp, ?_, ?_⟩
  · intro ht
    apply hσ.1
    rw [← LinearMap.range_eq_top.mpr hp, LinearMap.range_eq_bot.mpr (LinearMap.ker_eq_top.mp ht)]
  · intro N hN hNtop
    have hn : orthogonal N ≠ ⊥ := fun hb => hNtop (by
      rw [← orthogonal_orthogonal N, hb, orthogonal_bot])
    obtain ⟨M, hM, hS⟩ := exists_simpleSubmodule (stable_orthogonal (isDual_symm hr) hN) hn
    rw [hsocle M hS] at hM
    rw [hk, ← orthogonal_orthogonal N]
    exact orthogonal_anti hM

open Specs.CharacterDescent (Character StandardLattice)
open Specs.CharacterPairing (characterValue)
open Specs.RootWeightAction (mem_weightSpace WeylTransport DominanceLE)
open private postInv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
open private characterValue_inverse from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.InducedNonvanishing
open private act_eq_scalar_iff inclusion_equivariant
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.PrimitiveLine
open private splitPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private torusPoint_weights charactersOfIso universal_torus_character pointMap algebraPoint
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.RootWeightAction
open private weightSpacesIndependent from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.InducedSocle

private theorem dual_weight_finrank (P : OppositeBorelPair G)
    {ρ σ : Representation G.val I} (h : IsDual ρ σ) (χ : Character P.torus.group) :
    Module.finrank k (weightSpace σ P.torus χ⁻¹) =
      Module.finrank k (weightSpace ρ P.torus χ) := by
  classical
  let T := P.torus
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation P.split
  obtain ⟨φ, _, hφ, _, _⟩ := LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing (k := k) r
  obtain ⟨δ, hδ⟩ := torusPoint_weights ρ i φ hφ
  let E := φ.toEquiv.trans (charactersOfIso i)
  let W := weightSpace ρ T
  have ht : ⨆ ψ, W ψ = ⊤ := by
    rw [← E.surjective.iSup_comp]
    change ⨆ m, weightSpace ρ T (E m) = ⊤
    simp_rw [show ∀ m, weightSpace ρ T (E m) = _ from hδ]
    letI : DecidableEq (StandardLattice r) := Classical.decEq _
    exact (LinearAlgebraicGroups.WeightDecomposition.weightDecomposition δ).submodule_iSup_eq_top
  let M := ⨆ (ψ) (_ : ψ ≠ χ), W ψ
  have hleM (ψ : Character T.group) (hψ : ψ ≠ χ) : W ψ ≤ M :=
    le_iSup_of_le ψ (le_iSup (fun _ : ψ ≠ χ ↦ W ψ) hψ)
  have hdis : Disjoint (W χ) M := (iSupIndep_def.mp (weightSpacesIndependent P ρ)) χ
  have hsup : W χ ⊔ M = ⊤ := by
    apply top_unique
    rw [← ht]
    apply iSup_le
    intro ψ
    by_cases he : ψ = χ
    · exact he ▸ le_sup_left
    · exact (hleM ψ he).trans le_sup_right
  have hsep {ψ : Character T.group} (hψ : ψ ≠ χ) :
      ∃ (R : TestAlgebra k) (t : GroupPoints T.group R) (ℓ : R →ₗ[k] k),
        ℓ (characterValue ψ R t) - ℓ (characterValue χ R t) ≠ 0 := by
    obtain ⟨m, hm⟩ := E.surjective ψ
    obtain ⟨n, hn⟩ := E.surjective χ
    have hmn : m ≠ n := fun he => hψ (hm.symm.trans (he ▸ hn))
    have hv := universal_torus_character i φ hφ m
    have hw := universal_torus_character i φ hφ n
    dsimp only at hv hw
    rw [show charactersOfIso i (φ m) = ψ from hm] at hv
    rw [show charactersOfIso i (φ n) = χ from hn] at hw
    have hz : (MonoidAlgebra.of k (StandardLattice r) m :
        MonoidAlgebra k (StandardLattice r)) - MonoidAlgebra.of k _ n ≠ 0 :=
      sub_ne_zero.mpr ((MonoidAlgebra.of_injective (R := k) (M := StandardLattice r)).ne hmn)
    obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero k hz
    let R := CommAlgCat.of k (MonoidAlgebra k (StandardLattice r))
    let A := Specs.DiagonalizableGroups.groupAlgebra k (StandardLattice r)
    let t := pointMap i.hom R (algebraPoint A R (AlgHom.id k A))
    refine ⟨R, t, ℓ, ?_⟩
    change characterValue ψ R t = _ at hv
    change characterValue χ R t = _ at hw
    rw [hv, hw, ← map_sub]
    exact hℓ
  let D := weightSpace σ T χ⁻¹
  have hd : D = orthogonal M := by
    ext x
    constructor
    · intro hx
      apply mem_orthogonal.mpr
      suffices M ≤ LinearMap.ker (dotDual x) by
        exact fun y hy => this hy
      apply iSup_le
      intro ψ
      apply iSup_le
      intro hψ y hy
      obtain ⟨R, t, ℓ, hdiff⟩ := hsep hψ
      let g : GroupPoints G.val R := t ≫ T.inclusion.hom.hom
      let g' : GroupPoints G.val R := t⁻¹ ≫ T.inclusion.hom.hom
      have hg : g' = g⁻¹ := postInv T.inclusion t
      have hinv : g'⁻¹ = g := by rw [hg, inv_inv]
      have hz := dotProduct_coefficient_dual h R g' ℓ x y
      rw [hinv] at hz
      have hdx := (act_eq_scalar_iff σ R g' x _).mp
        (mem_weightSpace.mp hx R t⁻¹) ℓ
      have hdy := (act_eq_scalar_iff ρ R g y _).mp
        (mem_weightSpace.mp hy R t) ℓ
      rw [hdx, hdy, smul_dotProduct, dotProduct_smul, characterValue_inverse, inv_inv,
        smul_eq_mul, smul_eq_mul] at hz
      change x ⬝ᵥ y = 0
      apply (mul_eq_zero.mp _).resolve_left hdiff
      rw [sub_mul, ← hz, sub_self]
    · intro hx
      apply mem_weightSpace.mpr
      intro R t
      apply (act_eq_scalar_iff σ R _ x _).mpr
      intro ℓ
      let g : GroupPoints G.val R := t ≫ T.inclusion.hom.hom
      let N := LinearMap.ker (dotDual
        (orbitCoefficient σ R g ℓ x -
          ℓ (characterValue χ⁻¹ R t) • x))
      have hN (ψ : Character T.group) : W ψ ≤ N := by
        intro y hy
        change (_ - _) ⬝ᵥ y = 0
        rw [sub_dotProduct, smul_dotProduct, dotProduct_coefficient_dual h]
        let g' : GroupPoints G.val R := t⁻¹ ≫ T.inclusion.hom.hom
        have hg : g⁻¹ = g' := (postInv T.inclusion t).symm
        rw [hg]
        have hcy := (act_eq_scalar_iff ρ R g' y _).mp
          (mem_weightSpace.mp hy R t⁻¹) ℓ
        rw [hcy, dotProduct_smul, characterValue_inverse]
        by_cases hψ : ψ = χ
        · rw [hψ, sub_self]
        · rw [mem_orthogonal.mp hx y (hleM ψ hψ hy),
            smul_zero, smul_zero, sub_self]
      have htop : ⊤ ≤ N := ht ▸ iSup_le hN
      apply sub_eq_zero.mp
      apply dotDual.injective
      apply LinearMap.ext
      intro y
      rw [map_zero, LinearMap.zero_apply]
      exact htop (Submodule.mem_top : y ∈ (⊤ : Submodule k (I → k)))
  change Module.finrank k D = Module.finrank k (W χ)
  rw [hd]
  let f := dotDual.toLinearMap.submoduleComap M.dualAnnihilator
  have hfi : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply dotDual.injective
    exact congrArg (fun z : M.dualAnnihilator ↦ (z : Module.Dual k (I → k))) he
  have hfs := dotDual.toLinearMap.submoduleComap_surjective_of_surjective M.dualAnnihilator
    dotDual.surjective
  have he : Module.finrank k (orthogonal M) = Module.finrank k M.dualAnnihilator :=
    (LinearEquiv.ofBijective f ⟨hfi, hfs⟩).finrank_eq
  have hfin := Subspace.finrank_add_finrank_dualAnnihilator_eq M
  have hfin' := Submodule.finrank_add_eq_of_isCompl
    (show IsCompl (W χ) M from ⟨hdis, codisjoint_iff.mpr hsup⟩)
  omega

open Specs.AbstractPairing (Datum Root)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.CharacterPairing (pairing)
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.OrderedRootProducts (RootSubgroupFamily rootProduct product)
open Specs.RootWeightAction (fixedSpace mem_fixedSpace IsPrimitive RootOrbit)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private dominanceLE_iff positiveCone_nonneg rootPoint_surjective act_one act_mul
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.CyclicHighestWeight
open private exists_primitive_above lowerBound
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.InducedSocle
open private existsEnumeration radicalProductFor from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.OpenCell
open private length_inverse from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SimpleRoots
open private representative_exists from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SimpleParabolicProduct
open private weylTransport from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.RootWeightAction

private theorem act_rootProduct_fixed (ρ : Representation G.val I) {T : ClosedSubgroup G.val}
    (roots : RootSubgroupFamily T) (S : Set (Root T)) (l : List (Root T))
    (hl : ∀ α ∈ l, α ∈ S) (R : TestAlgebra k) (v : I → R)
    (hfix : ∀ α ∈ S, ∀ p : GroupPoints (roots α).val.group R,
      act ρ R (p ≫ (roots α).val.inclusion.hom.hom) v = v)
    (p : Points (product (fun α => (roots α).val.group.X) l) R) :
    act ρ R (p ≫ rootProduct roots l) v = v := by
  induction l with
  | nil =>
    rw [show p ≫ rootProduct roots [] = (1 : GroupPoints G.val R) from MonObj.comp_one p,
      act_one]
  | cons α l ih =>
    let g₁ : GroupPoints G.val R := (p ≫ fst _ _) ≫ (roots α).val.inclusion.hom.hom
    let g₂ : GroupPoints G.val R := (p ≫ snd _ _) ≫ rootProduct roots l
    let g : GroupPoints G.val R := p ≫ rootProduct roots (α :: l)
    have hg : g = g₁ * g₂ := by
      dsimp only [g, g₁, g₂, rootProduct]
      erw [MonObj.comp_mul, Category.assoc, Category.assoc]
      rfl
    change act ρ R g v = v
    rw [hg, act_mul]
    have h₂ : act ρ R g₂ v = v := ih (fun β hβ ↦ hl β (List.mem_cons_of_mem _ hβ)) _
    rw [h₂]
    exact hfix α (hl α (List.mem_cons_self ..)) (p ≫ fst _ _)

private theorem greatestWeight_fixed (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
    (D : Datum P.torus) {U : ClosedSubgroup P.positive.group}
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    (height : Additive (Character P.torus.group) →ₗ[ℤ] ℝ)
    (hheight : ∀ α ∈ subgroupRoots P.torus P.positive, 0 < height (Additive.ofMul α.val))
    (ρ : Representation G.val I) (horbit : RootOrbit ρ P.torus) (χ : Character P.torus.group)
    (hupper : ∀ ψ, weightSpace ρ P.torus ψ ≠ ⊥ → DominanceLE P.torus P.positive ψ χ) :
    weightSpace ρ P.torus χ ≤ fixedSpace ρ (U.inclusion ≫ P.positive.inclusion) := by
  classical
  let T := P.torus
  let B := P.positive
  let := D.finiteRoots
  have hshift (α : Root T) (hα : α ∈ subgroupRoots T B) (j : ℕ) (hj : 0 < j) :
      weightSpace ρ T (χ * α.val ^ j) = ⊥ := by
    by_contra h
    have hc := (dominanceLE_iff T B _ _).mp (hupper _ h)
    have hp := positiveCone_nonneg T B height hheight hc
    change 0 ≤ height (Additive.ofMul χ - (Additive.ofMul χ + j • Additive.ofMul α.val)) at hp
    rw [map_sub, map_add, map_nsmul] at hp
    linarith [nsmul_pos (hheight α hα) hj.ne']
  let Coord (α : Root T) :=
    Σ H : {H : ClosedSubgroup G.val // Specs.RootGroups.IsRootSubgroup T H α.val},
      Σ L : Specs.RootGroups.AdditiveLine k, {x : L.group ≅ H.val.group //
        Specs.RootGroups.HasScalarAction T α.val (x.hom ≫ H.val.inclusion)}
  have hc (α : Root T) : Nonempty (Coord α) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, L, pos, _, hpos, _, hact, _, _⟩ := D.attached α
    exact ⟨⟨⟨_, hpos⟩, L, ⟨pos.root, hact⟩⟩⟩
  let coord (α : Root T) := Classical.choice (hc α)
  let roots : RootSubgroupFamily T := fun α ↦ (coord α).1
  obtain ⟨l, hl⟩ := existsEnumeration (subgroupRoots T B)
  obtain ⟨_, _, _, _, _, _, dec⟩ :=
    LinearAlgebraicGroups.RootData.BorelPositivity.borelPositivity G P.reductive T P.split P.maximal
  obtain ⟨V, _, _, hV, _, _, _, _, _, chart⟩ := dec B P.positiveBorel P.inPositive
  obtain ⟨E, hE⟩ := radicalProductFor roots l hU hV (chart roots l hl)
  intro v hv
  apply mem_fixedSpace.mpr
  intro R u
  let x := u ≫ E.inv
  have hx : x ≫ rootProduct roots l = u ≫ (U.inclusion ≫ B.inclusion).hom.hom := by
    rw [← hE]
    change ((u : Points U.group.X R) ≫ E.inv) ≫ E.hom ≫ _ = _
    erw [Category.assoc, E.inv_hom_id_assoc]
    rfl
  rw [← hx]
  apply act_rootProduct_fixed ρ roots (subgroupRoots T B) l (fun α hα ↦ (hl.2 α).mp hα)
  intro α hα a
  obtain ⟨z, hz⟩ := rootPoint_surjective (coord α).2.2.val R a
  obtain ⟨p, h0, hcoef, hact⟩ := horbit α (roots α).val (roots α).property
    (coord α).2.1 (coord α).2.2.val (coord α).2.2.property χ ⟨v, hv⟩
  have hg : a ≫ (roots α).val.inclusion.hom.hom =
      Specs.RootGroups.rootPoint ((coord α).2.2.val.hom ≫ (roots α).val.inclusion) R z := by
    rw [← hz]
    rfl
  rw [hg, hact R z]
  funext i
  have hp : p i = Polynomial.C (v i) := by
    ext j
    rcases j with _ | j
    · simpa using congrFun h0 i
    · have h := hcoef (j + 1) (Nat.succ_pos _)
      rw [hshift α hα _ (Nat.succ_pos _), Submodule.mem_bot] at h
      simpa using congrFun h i
  simp [hp, extendVector]

private theorem induced_highest (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
    (D : Datum P.torus) {U : ClosedSubgroup P.positive.group}
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    (height : Additive (Character P.torus.group) →ₗ[ℤ] ℝ)
    (hheight : ∀ α ∈ subgroupRoots P.torus P.positive, 0 < height (Additive.ofMul α.val))
    {χ : Character P.torus.group} (S : SocleModel P U χ) (hroot : RootOrbit S.inducedAction P.torus) :
    HighestWeightLine P S.inducedAction χ := by
  let v : S.I → k := S.highestVector
  have hspan : Submodule.span k {v} ≤ weightSpace S.inducedAction P.torus χ :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr S.highest_primitive.2.2)
  have hupper ψ (hψ : weightSpace S.inducedAction P.torus ψ ≠ ⊥) :
      DominanceLE P.torus P.positive ψ χ := by
    obtain ⟨ν, hle, x, hx⟩ :=
      exists_primitive_above P D hU S.inducedAction hroot height hheight ψ hψ
    have hxχ := hspan (S.inducedFixedLine.le hx.2.1)
    have he : ν = χ := by
      by_contra hn
      exact hx.1 ((Submodule.mem_bot k).mp
        (((weightSpacesIndependent P S.inducedAction).pairwiseDisjoint hn).le_bot
          (show x ∈ weightSpace S.inducedAction P.torus ν ⊓
            weightSpace S.inducedAction P.torus χ from ⟨hx.2.2, hxχ⟩)))
    exact he ▸ hle
  have hline := le_antisymm
    ((greatestWeight_fixed P D hU height hheight S.inducedAction hroot χ hupper).trans
      S.inducedFixedLine.le) hspan
  refine ⟨?_, hupper⟩
  rw [hline]
  exact finrank_span_singleton S.highest_primitive.1

private theorem weyl_weight_finrank (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
    {D : Datum P.torus} (e : DatumAndWeyl.Identification D) (w : D.rootDatum.weylGroup)
    (ρ : Representation G.val I) (hw : WeylTransport ρ e) (χ : Character P.torus.group) :
    Module.finrank k (weightSpace ρ P.torus ((e.labelEquiv w).val χ)) =
      Module.finrank k (weightSpace ρ P.torus χ) := by
  obtain ⟨n, hn⟩ := representative_exists e P.split w
  let K := CommAlgCat.of k k
  let Y := unop ((testSpec k).rightOp.obj K)
  let nK : GroupPoints e.normalizer.group K := toUnit Y ≫ n
  have hK : nK ≫ e.quotient.hom.hom =
      toUnit Y ≫ e.image.constantGroup.sectionPoint (e.labelEquiv w) := by
    change (toUnit Y ≫ n) ≫ e.quotient.hom.hom = _
    rw [Category.assoc, show n ≫ e.quotient.hom.hom = _ from hn]
  obtain ⟨F, _⟩ := hw w nK hK χ
  exact F.finrank_eq.symm

private theorem inverse_dominance (P : OppositeBorelPair G) {χ ψ : Character P.torus.group}
    (h : DominanceLE P.torus P.positive χ ψ) :
    DominanceLE P.torus P.positive ψ⁻¹ χ⁻¹ := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, by simpa only [inv_div_inv] using hc⟩

private theorem dual_highest (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
    (D : Datum P.torus) (e : DatumAndWeyl.Identification D)
    (f : Additive (Character P.torus.group) →ₗ[ℤ] ℤ) (b : D.rootDatum.Base)
    (hf : ∀ i, f (D.rootDatum.root i) ≠ 0)
    (hb : ∀ i, b.IsPos i ↔ i ∈ Specs.SimpleRoots.positive D.rootDatum f)
    (hB : ∀ i, b.IsPos i ↔ i ∈ subgroupRoots P.torus P.positive)
    (height : Additive (Character P.torus.group) →ₗ[ℤ] ℝ)
    (hheight : ∀ α ∈ subgroupRoots P.torus P.positive, 0 < height (Additive.ofMul α.val))
    (w : D.rootDatum.weylGroup) (hw : ∀ w', Specs.SimpleRoots.wordLength D.rootDatum b w' ≤
      Specs.SimpleRoots.wordLength D.rootDatum b w)
    {ρ σ : Representation G.val I} (h : IsDual ρ σ) (χ : Character P.torus.group)
    (hχ : HighestWeightLine P ρ χ) :
    HighestWeightLine P σ (oppositeWeight e w χ) := by
  have hW := weylTransport ρ e
  refine ⟨?_, ?_⟩
  · unfold oppositeWeight
    rw [dual_weight_finrank P h, weyl_weight_finrank P e w ρ hW χ]
    exact hχ.1
  · intro ψ hψ
    have hψ' : weightSpace ρ P.torus ψ⁻¹ ≠ ⊥ := by
      intro he
      have hh := dual_weight_finrank P h ψ⁻¹
      rw [inv_inv, he, finrank_bot] at hh
      exact hψ (Submodule.finrank_eq_zero.mp hh)
    have hl := lowerBound P D e f b hf hb hB height hheight ρ hW χ ψ⁻¹ hψ' hχ.2 w hw
    simpa only [oppositeWeight, inv_inv] using inverse_dominance P hl

private theorem primitive_of_highest (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
    (D : Datum P.torus) {U : ClosedSubgroup P.positive.group}
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    (height : Additive (Character P.torus.group) →ₗ[ℤ] ℝ)
    (hheight : ∀ α ∈ subgroupRoots P.torus P.positive, 0 < height (Additive.ofMul α.val))
    (ρ : Representation G.val I) (hroot : RootOrbit ρ P.torus) (χ : Character P.torus.group)
    (hχ : HighestWeightLine P ρ χ) :
    SimpleClassification.HasHighestWeight P U ρ χ := by
  have hne : weightSpace ρ P.torus χ ≠ ⊥ := by
    intro h
    have hr := hχ.1
    rw [h, finrank_bot] at hr
    exact Nat.zero_ne_one hr
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hne
  exact ⟨v, hv0, greatestWeight_fixed P D hU height hheight ρ hroot χ hχ.2 hv, hv⟩

private theorem oppositeWeight_inverse {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} (e : DatumAndWeyl.Identification D) (w : D.rootDatum.weylGroup)
    (χ : Character T.group) :
    oppositeWeight e w⁻¹ (oppositeWeight e w χ) = χ := by
  unfold oppositeWeight
  rw [map_inv, inv_inv]
  change ((e.labelEquiv w⁻¹ : e.image.labels) : MulAut (Character T.group))
    (((e.labelEquiv w : e.image.labels) : MulAut (Character T.group)) χ) = χ
  rw [← MulAut.mul_apply, ← Subgroup.coe_mul, ← map_mul, inv_mul_cancel, map_one]
  rfl

open private comp_equivariant from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.PrimitiveLine
open private realizedCoaction_transport from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SimpleClassification
open private connectedOfGeometricallyConnected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived

private theorem matrix_equivariant {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] {A : HopfAlgebraCategory k}
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (b : Module.Basis I k V) (c : Module.Basis J k W)
    {δ : RightComodule k A V} {τ : RightComodule k A W} {f : V →ₗ[k] W}
    (hf : RationalRepresentations.IsEquivariant A δ τ f) :
    IsEquivariant (fromCoaction e b δ) (fromCoaction e c τ)
      (c.equivFun.toLinearMap.comp (f.comp b.equivFun.symm.toLinearMap)) := by
  intro R g ℓ v
  obtain ⟨a, rfl⟩ := ((forget GrpCat).mapIso (e.app R)).toEquiv.surjective g
  obtain ⟨x, rfl⟩ := b.equivFun.surjective v
  let F := c.equivFun.toLinearMap.comp (f.comp b.equivFun.symm.toLinearMap)
  have hFx (y : V) : F (b.equivFun y) = c.equivFun (f y) := by simp [F]
  change F (orbitCoefficient (fromCoaction e b δ) R (e.hom.app R a) ℓ (b.equivFun x)) =
    orbitCoefficient (fromCoaction e c τ) R (e.hom.app R a) ℓ (F (b.equivFun x))
  rw [hFx x]
  have h₁ := act_contract e b δ R a.ofConv ℓ x
  have h₂ := act_contract e c τ R a.ofConv ℓ (f x)
  change orbitCoefficient (fromCoaction e b δ) R (e.hom.app R a) ℓ (b.equivFun x) = _ at h₁
  change orbitCoefficient (fromCoaction e c τ) R (e.hom.app R a) ℓ (c.equivFun (f x)) = _ at h₂
  rw [h₁, h₂, hFx, contract_natural]
  exact congrArg (fun z ↦ c.equivFun (contract (ℓ.comp a.ofConv.toLinearMap) z))
    (LinearMap.congr_fun hf x)

private def socleInclusion {P : OppositeBorelPair G} {U : ClosedSubgroup P.positive.group}
    {χ : Character P.torus.group} (S : SocleModel P U χ) : (S.J → k) →ₗ[k] (S.I → k) :=
  S.socle.subtype.comp S.socleBasis.equivFun.symm.toLinearMap

private theorem socleInclusion_injective {P : OppositeBorelPair G}
    {U : ClosedSubgroup P.positive.group} {χ : Character P.torus.group} (S : SocleModel P U χ) :
    Function.Injective (socleInclusion S) :=
  Subtype.val_injective.comp S.socleBasis.equivFun.symm.injective

private theorem socleInclusion_range {P : OppositeBorelPair G}
    {U : ClosedSubgroup P.positive.group} {χ : Character P.torus.group} (S : SocleModel P U χ) :
    LinearMap.range (socleInclusion S) = S.socle := by
  rw [socleInclusion, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    Submodule.range_subtype]

private theorem socleInclusion_coaction {P : OppositeBorelPair G}
    {U : ClosedSubgroup P.positive.group} {χ : Character P.torus.group} (S : SocleModel P U χ) :
    RationalRepresentations.IsEquivariant S.A S.socleCoaction
      (toCoaction (pointIso S.groupIso) (Pi.basisFun k S.I) S.inducedAction) S.socle.subtype := by
  let F := S.inducedBasis.equivFun.symm.toLinearMap
  let δ := toCoaction (pointIso S.groupIso) (Pi.basisFun k S.I) S.inducedAction
  have hF : Function.Injective (F.rTensor S.A) :=
    (S.inducedBasis.equivFun.symm.rTensor S.A).injective
  apply LinearMap.ext
  intro x
  apply hF
  have h₁ := LinearMap.congr_fun S.socleCoaction_spec x
  rw [LinearMap.rTensor_comp] at h₁
  have h₂ := LinearMap.congr_fun
    (realizedCoaction_transport S.groupIso S.inducedBasis S.inducedCoaction
      S.inducedAction S.inducedAction_spec) (x : S.I → k)
  change F.rTensor S.A (S.socle.subtype.rTensor S.A (S.socleCoaction.coaction x)) =
    S.inducedCoaction.coaction (F x.val) at h₁
  change F.rTensor S.A (δ.coaction x.val) = S.inducedCoaction.coaction (F x.val) at h₂
  exact h₁.trans h₂.symm

private theorem socleInclusion_equivariant {P : OppositeBorelPair G}
    {U : ClosedSubgroup P.positive.group} {χ : Character P.torus.group} (S : SocleModel P U χ) :
    IsEquivariant S.socleAction S.inducedAction (socleInclusion S) := by
  rw [realizes_unique _ _ _ _ S.socleAction_spec]
  exact inclusion_equivariant (pointIso S.groupIso) S.inducedAction S.socle S.socleBasis
    S.socleCoaction (socleInclusion_coaction S)

private theorem equivariant_weight {ρ : Representation G.val I} {σ : Representation G.val J}
    {F : (I → k) →ₗ[k] (J → k)} (hF : IsEquivariant ρ σ F)
    {T : ClosedSubgroup G.val} {χ : Character T.group} {v : I → k}
    (hv : v ∈ weightSpace ρ T χ) :
    F v ∈ weightSpace σ T χ := by
  apply mem_weightSpace.mpr
  intro R t
  let g : GroupPoints G.val R := t ≫ T.inclusion.hom.hom
  apply (act_eq_scalar_iff σ R g _ _).mpr
  intro ℓ
  rw [← hF R g ℓ v, (act_eq_scalar_iff ρ R g v _).mp (mem_weightSpace.mp hv R t) ℓ,
    map_smul]

private theorem socle_highest {P : OppositeBorelPair G}
    {U : ClosedSubgroup P.positive.group} {χ : Character P.torus.group} (S : SocleModel P U χ)
    (hχ : HighestWeightLine P S.inducedAction χ) :
    HighestWeightLine P S.socleAction χ := by
  refine ⟨?_, ?_⟩
  · rw [S.highestLine]
    exact finrank_span_singleton S.primitive.1
  · intro ψ hψ
    obtain ⟨v, hv, hv₀⟩ := (Submodule.ne_bot_iff _).mp hψ
    apply hχ.2
    exact (Submodule.ne_bot_iff _).mpr ⟨socleInclusion S v,
      equivariant_weight (socleInclusion_equivariant S) hv, fun he ↦
        hv₀ (socleInclusion_injective S (he.trans (socleInclusion S).map_zero.symm))⟩

private theorem head_isomorphic_of_simple {ρ : Representation G.val I}
    {σ : Representation G.val J} (hs : IsSimple ρ) (hh : HasHead ρ σ) : Isomorphic ρ σ := by
  obtain ⟨p, heq, hp, hk, _⟩ := hh
  have hker := (hs.2 _ (stable_ker heq)).resolve_right hk
  exact ⟨⟨LinearEquiv.ofBijective p ⟨LinearMap.ker_eq_bot.mp hker, hp⟩, heq⟩⟩

private theorem change_head_target {L : Type u} [Fintype L] [DecidableEq L]
    {ρ : Representation G.val I} {σ : Representation G.val J} {τ : Representation G.val L}
    (hh : HasHead ρ σ) (he : Isomorphic σ τ) : HasHead ρ τ := by
  obtain ⟨p, hp, hsurj, hproper, hmax⟩ := hh
  obtain ⟨f, hf⟩ := he
  have heq : LinearMap.ker (f.toLinearMap.comp p) = LinearMap.ker p := by
    rw [LinearMap.ker_comp, f.ker, Submodule.comap_bot]
  exact ⟨_, comp_equivariant hp hf, f.surjective.comp hsurj, heq.symm ▸ hproper,
    fun N hN ht ↦ heq.symm ▸ hmax N hN ht⟩

private theorem induced_simple_of_charZero [CharZero k] {P : OppositeBorelPair G}
    {U : ClosedSubgroup P.positive.group} {χ : Character P.torus.group} (S : SocleModel P U χ) :
    IsSimple S.inducedAction ∧ Isomorphic S.socleAction S.inducedAction := by
  let := connectedOfGeometricallyConnected G P.reductive.2.1
  let E := pointIso S.groupIso
  let b := Pi.basisFun k S.I
  let δ := toCoaction E b S.inducedAction
  have hs := (CompleteReducibility.characteristicZeroCompleteReducibility G S.A S.groupIso).1.mp
    P.reductive (S.I → k) δ
  obtain ⟨r, hr, hri⟩ := hs S.socle S.socleCoaction (socleInclusion_coaction S)
  let p := S.socleBasis.equivFun.toLinearMap.comp r
  have hp : IsEquivariant S.inducedAction S.socleAction p := by
    have h := matrix_equivariant E b S.socleBasis hr
    rw [from_toCoaction, ← realizes_unique _ _ _ _ S.socleAction_spec] at h
    simpa only [b, Pi.basisFun_equivFun, LinearEquiv.refl_symm, LinearEquiv.refl_toLinearMap,
      LinearMap.comp_id] using h
  have hk : LinearMap.ker p = ⊥ := by
    by_contra h
    obtain ⟨N, hN, hsimple⟩ := exists_simpleSubmodule (stable_ker hp) h
    rw [S.socle_unique N hsimple] at hN
    apply S.socle_simple.2.1
    refine (Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_
    have hpx : p x = 0 := hN hx
    have hrx : r x = 0 := S.socleBasis.equivFun.injective
      (hpx.trans S.socleBasis.equivFun.map_zero.symm)
    have he := LinearMap.congr_fun hri (⟨x, hx⟩ : S.socle)
    change r x = (⟨x, hx⟩ : S.socle) at he
    exact congrArg Subtype.val (he.symm.trans hrx)
  let f := socleInclusion S
  have hleft (x : S.J → k) : p (f x) = x := by
    have he := LinearMap.congr_fun hri (S.socleBasis.equivFun.symm x)
    change r (f x) = S.socleBasis.equivFun.symm x at he
    change S.socleBasis.equivFun (r (f x)) = x
    rw [he, LinearEquiv.apply_symm_apply]
  have hsurj : Function.Surjective f := fun y ↦
    ⟨p y, (LinearMap.ker_eq_bot.mp hk) (hleft (p y))⟩
  have htop : S.socle = ⊤ := (socleInclusion_range S).symm.trans (LinearMap.range_eq_top.mpr hsurj)
  refine ⟨⟨?_, ?_⟩, ⟨⟨LinearEquiv.ofBijective f ⟨socleInclusion_injective S, hsurj⟩,
    socleInclusion_equivariant S⟩⟩⟩
  · simpa only [htop] using S.socle_simple.2.1
  · intro M hM
    simpa only [htop] using S.socle_simple.2.2 M hM (htop.symm ▸ le_top)

open Specs.InducedNonvanishing (Dominant)

/-- Duality identifies the Weyl head with the induced socle, and in
characteristic zero the head quotient and the socle inclusion are isomorphisms. -/
theorem weylModules : Statement.{u} := by
  classical
  intro k _ G P U hU
  let T := P.torus
  let B := P.positive
  obtain ⟨comm, D, e, _, _, _, _, hroot⟩ := RootWeightAction.rootWeightAction
    G P.reductive T B P.split P.maximal P.positiveBorel P.inPositive
  let := comm
  let := D.finiteRoots
  let := D.freeCharacters
  let := D.finiteCharacters
  let := D.reduced
  obtain ⟨c, _, hc, _, hpos⟩ :=
    (LinearAlgebraicGroups.RootData.BorelsAndChambers.borelsThroughT
      G P.reductive T P.split P.maximal).1 B P.positiveBorel P.inPositive
  let f := Specs.SimpleRoots.evaluate D c
  have hf (i : Root T) : f (D.rootDatum.root i) = pairing T.group i.val c := by
    change D.rootDatum.toLinearMap (D.rootDatum.root i) (Additive.ofMul c) = _
    rw [D.root_eq, D.pairing_eq]
  have hreg (i : Root T) : f (D.rootDatum.root i) ≠ 0 := hf i ▸ hc i
  obtain ⟨b, hb⟩ := LinearAlgebraicGroups.RootData.SimpleRoots.baseFor D.rootDatum f hreg
  have hB (i : Root T) : b.IsPos i ↔ i ∈ subgroupRoots T B := by
    rw [hb.positive_iff, hpos]
    change 0 < f (D.rootDatum.root i) ↔ 0 < pairing T.group i.val c
    rw [hf]
  let height := Specs.SimpleRoots.realFunctional f
  have hheight (i : Root T) (hi : i ∈ subgroupRoots T B) :
      0 < height (Additive.ofMul i.val) := by
    have hi' := (hb.positive_iff i).mp ((hB i).mpr hi)
    change 0 < f (D.rootDatum.root i) at hi'
    rw [D.root_eq] at hi'
    change 0 < (f (Additive.ofMul i.val) : ℝ)
    exact_mod_cast hi'
  let : Finite e.image.labels := e.image.finite
  let : Finite D.rootDatum.weylGroup := Finite.of_injective e.labelEquiv e.labelEquiv.injective
  let : Fintype D.rootDatum.weylGroup := Fintype.ofFinite _
  let len := Specs.SimpleRoots.wordLength D.rootDatum b
  obtain ⟨w, _, hw₀⟩ := Finset.exists_max_image Finset.univ len Finset.univ_nonempty
  have hw (v) : len v ≤ len w := hw₀ v (Finset.mem_univ v)
  have hwi (v) : len v ≤ len w⁻¹ := by
    change len v ≤ Specs.SimpleRoots.wordLength D.rootDatum b w⁻¹
    rw [length_inverse]
    exact hw v
  have cls := SimpleClassification.classification G P U hU
  refine ⟨comm, D, e, b, w, hB, hw, ?_⟩
  intro χ hχ
  change Dominant P χ at hχ
  let χ' := oppositeWeight e w χ
  obtain ⟨S, hS⟩ := cls.2.2 χ hχ
  have hInd := induced_highest P D hU height hheight S (hroot S.inducedAction).1
  have hL := socle_highest S hInd
  obtain ⟨Ldual, hdual⟩ := isDual_exists S.A S.groupIso S.socleAction
  have hsimple := dual_simple hdual S.simple
  have hdualline := dual_highest P D e f b hreg hb.positive_iff hB height hheight w hw hdual χ hL
  have hprim := primitive_of_highest P D hU height hheight Ldual (hroot Ldual).1 χ' hdualline
  have hχ' := cls.2.1 Ldual hsimple χ' hprim
  obtain ⟨S', hS'⟩ := cls.2.2 χ' hχ'
  have hIso := (hS' Ldual hsimple).mpr hprim
  have hInd' := induced_highest P D hU height hheight S' (hroot S'.inducedAction).1
  have hL' := socle_highest S' hInd'
  obtain ⟨Δ, hΔ⟩ := isDual_exists S'.A S'.groupIso S'.inducedAction
  obtain ⟨Ld', hLd'⟩ := isDual_exists S'.A S'.groupIso S'.socleAction
  have inverseχ : oppositeWeight e w⁻¹ χ' = χ := oppositeWeight_inverse e w χ
  have hΔline := dual_highest P D e f b hreg hb.positive_iff hB height hheight w⁻¹ hwi hΔ χ' hInd'
  have hLd'line := dual_highest P D e f b hreg hb.positive_iff hB height hheight w⁻¹ hwi hLd' χ' hL'
  rw [inverseχ] at hΔline hLd'line
  have hIso' := (hS Ld' (dual_simple hLd' S'.simple)).mpr
    (primitive_of_highest P D hU height hheight Ld' (hroot Ld').1 χ hLd'line)
  have hh := head_of_dual_socle hΔ hLd' S'.simple (socleInclusion_equivariant S')
    (socleInclusion_injective S') (fun M hM ↦ (S'.socle_unique M hM).trans (socleInclusion_range S').symm)
  have hhead := change_head_target hh hIso'
  refine ⟨hχ', S, S', Δ, Ldual, hΔ, hdual, hhead, hIso, hInd, hL, hΔline, ?_⟩
  intro hzero
  let := hzero
  exact ⟨head_isomorphic_of_simple (dual_simple hΔ (induced_simple_of_charZero S').1) hhead,
    (induced_simple_of_charZero S).2⟩

end LinearAlgebraicGroups.Representation.WeylModules
