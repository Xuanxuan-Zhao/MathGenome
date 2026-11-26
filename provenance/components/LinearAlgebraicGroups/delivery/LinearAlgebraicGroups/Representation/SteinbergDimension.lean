import Specs.LinearAlgebraicGroups.Representation.SteinbergDimension
import LinearAlgebraicGroups.Representation.SteinbergDistributions
import LinearAlgebraicGroups.Representation.RestrictedCyclicity
import LinearAlgebraicGroups.Representation.DominantOrder
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Module
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Representation.SteinbergDimension

open _root_.LinearAlgebraicGroups.Specs
open Specs.AbstractPairing (Datum Root IsAttachedCoroot)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (pairing)
open Specs.DominantOrder (IsBaseFor)
open Specs.FlagLineBundle (OppositeBorelPair)
open Specs.InducedNonvanishing (Dominant)
open Specs.SteinbergDimension
open Specs.SteinbergDistributions (HasDistributionSocle powersIdeal)
open LinearAlgebraicGroups.FiniteDistributions (Dist LeftAction)

open private sum_coroot_pairing positive_flip
  from LinearAlgebraicGroups.Representation.DominantOrder
open private truncatedBasis
  from LinearAlgebraicGroups.Representation.SteinbergDistributions
open private coroot_eq_of_reflection
  from LinearAlgebraicGroups.Classification.TransportedRootCoordinates

noncomputable section

section Lattice

variable {I X Y : Type u} [Finite I] [AddCommGroup X] [AddCommGroup Y]
  [IsTorsionFree ℤ X] (D : RootPairing I ℤ X Y) [D.IsReduced] [D.flip.IsReduced]

private theorem sum_roots_pairing (S : Set I) (b : D.Base) (hb : IsBaseFor D S b)
    (i : b.support) :
    D.toLinearMap (∑ᶠ a : S, D.root a.val) (D.coroot i.val) = 2 := by
  classical
  let := Fintype.ofFinite I
  let := Fintype.ofFinite S
  have hdual : IsBaseFor D.flip S b.flip := fun j => (positive_flip D b j).trans (hb j)
  have hsum : (∑ᶠ a : S, D.root a.val) = Specs.DominantOrder.twoRhoCoroot D.flip S := by
    rw [finsum_eq_sum_of_fintype]
    unfold Specs.DominantOrder.twoRhoCoroot
    rw [← Finset.sum_subtype]
    · rfl
    · intro x
      simp
  rw [hsum]
  exact sum_coroot_pairing D.flip b.flip hdual i.property

omit [Finite I] [IsTorsionFree ℤ X] [D.IsReduced] [D.flip.IsReduced] in
private theorem eq_of_simple_coroot_pairings (b : D.Base)
    (x y : X) (h : ∀ i : b.support, D.toLinearMap x (D.coroot i.val) =
      D.toLinearMap y (D.coroot i.val))
    (hspan : Submodule.span ℤ (Set.range D.coroot) = ⊤) : x = y := by
  apply D.toLinearMap.toPerfPair.injective
  apply LinearMap.ext_on
  · rw [b.span_int_coroot_support, hspan]
  · rintro _ ⟨i, hi, rfl⟩
    exact h ⟨i, hi⟩

private theorem exists_halfSum (S : Set I) (b : D.Base) (hb : IsBaseFor D S b)
    (hspan : Submodule.span ℤ (Set.range D.coroot) = ⊤) :
    ∃ x : X, (2 : ℤ) • x = ∑ᶠ a : S, D.root a.val := by
  classical
  let basis : Basis b.support ℤ Y :=
    Basis.mk b.linearIndepOn_coroot (by
      change ⊤ ≤ Submodule.span ℤ (Set.range (fun i : b.support => D.coroot i.val))
      rw [show Set.range (fun i : b.support => D.coroot i.val) = D.coroot '' b.support by
        ext y
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨i.val, i.property, rfl⟩
        · rintro ⟨i, hi, rfl⟩
          exact ⟨⟨i, hi⟩, rfl⟩]
      rw [b.span_int_coroot_support, hspan])
  have hbasis (i : b.support) : basis i = D.coroot i.val := Basis.mk_apply _ _ i
  let x := D.toLinearMap.toPerfPair.symm (basis.constr ℤ fun _ => (1 : ℤ))
  have hx (i : b.support) : D.toLinearMap x (D.coroot i.val) = 1 := by
    change D.toLinearMap.toPerfPair x (D.coroot i.val) = 1
    rw [← hbasis i, LinearEquiv.apply_symm_apply, Basis.constr_basis]
  refine ⟨x, eq_of_simple_coroot_pairings D b _ _ (fun i => ?_) hspan⟩
  rw [sum_roots_pairing D S b hb i, map_smul, LinearMap.smul_apply, hx]
  decide

end Lattice

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private theorem markedBase (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X] :
    ∃ D : Datum P.torus, ∃ b : D.rootDatum.Base,
      IsBaseFor D.rootDatum (subgroupRoots P.torus P.positive) b := by
  obtain ⟨h, D, _, hB, _, _, _⟩ :=
    RootData.BorelPositivity.borelPositivity G P.reductive P.torus P.split P.maximal
  let := h
  have hp := hB.1 P.positive P.positiveBorel P.inPositive
  obtain ⟨h, D, _, hbase⟩ :=
    LinearAlgebraicGroups.Representation.DominantOrder.dominantOrder
      G P.reductive P.torus P.split P.maximal
  let := h
  obtain ⟨⟨b, hb⟩, _⟩ := hbase _ hp
  exact ⟨D, b, hb⟩

theorem halfSumExists : HalfSumExists.{u} := by
  intro k _ _ G hG hsc P _
  obtain ⟨D, b, hb⟩ := markedBase P
  let := D.finiteRoots
  let := D.freeCharacters
  let := D.reduced
  let := D.reducedCoroots
  have hc := (Classification.SimplyConnectedLattice.latticeCriterion
    G hG P.torus P.split P.maximal D).mp hsc
  obtain ⟨x, hx⟩ := exists_halfSum D.rootDatum _ b hb hc
  refine ⟨Additive.toMul x, ?_⟩
  change (2 : ℤ) • x = _
  simpa only [D.root_eq] using hx

open private borel_of_regular_cocharacter
  from LinearAlgebraicGroups.RootData.BorelsAndChambers

/-- Half the positive-root sum pairs to one with every attached simple coroot. -/
theorem halfSum_simpleCoroot (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
    (ρ : Character P.torus.group) (hρ : IsHalfPositiveRootSum P ρ)
    (a : Specs.RootWeightAction.SimpleRoot P.torus P.positive)
    (c : Specs.CharacterDescent.Cocharacter P.torus.group)
    (hc : IsAttachedCoroot P.torus a.val c) :
    pairing P.torus.group ρ c = 1 := by
  obtain ⟨t, _, ht, _, hpos⟩ :=
    borel_of_regular_cocharacter G P.reductive P.torus P.split P.maximal
      P.positive P.positiveBorel P.inPositive
  obtain ⟨h, D, _, hbase⟩ :=
    RootData.SimpleRoots.simpleRoots G P.reductive P.torus P.split P.maximal
  let := h
  obtain ⟨b, hb, _⟩ := hbase t ht
  have hval (j : Root P.torus) : j ∈ Specs.SimpleRoots.positive D.rootDatum
      (Specs.SimpleRoots.evaluate D t) ↔ j ∈ subgroupRoots P.torus P.positive := by
    rw [hpos]
    change 0 < D.rootDatum.toLinearMap (D.rootDatum.root j) (Additive.ofMul t) ↔
      0 < pairing P.torus.group j.val t
    rw [D.root_eq, D.pairing_eq]
  have hab : a.val ∈ b.support := by
    refine (hb.simple_iff a.val).2 ⟨(hval _).2 a.property.1, ?_⟩
    intro i hi j hj he
    apply a.property.2 i ((hval _).1 hi) j ((hval _).1 hj)
    rw [D.root_eq, D.root_eq, D.root_eq] at he
    exact Additive.ofMul.injective he
  let := D.finiteRoots
  let := D.freeCharacters
  let := D.reduced
  let := D.reducedCoroots
  have hsum := sum_roots_pairing D.rootDatum _ b
    (fun j => (hb.positive_iff j).trans (hval j)) ⟨a.val, hab⟩
  have hh : (2 : ℤ) • Additive.ofMul ρ =
      ∑ᶠ j : subgroupRoots P.torus P.positive, D.rootDatum.root j.val := by
    simpa only [IsHalfPositiveRootSum, D.root_eq] using hρ
  rw [← hh, map_smul, LinearMap.smul_apply, zsmul_eq_mul] at hsum
  change (2 : ℤ) * D.rootDatum.toLinearMap (Additive.ofMul ρ) (D.rootDatum.coroot a.val) = 2 at hsum
  obtain ⟨C, s, _, _, M, N, _, Q, F, J, L, x, y, _, _, _, _, R, hR⟩ := hc
  rw [← hR, coroot_eq_of_reflection P.reductive P.split P.maximal D a.val R,
    ← D.pairing_eq]
  change D.rootDatum.toLinearMap (Additive.ofMul ρ) (D.rootDatum.coroot a.val) = 1
  omega

/-- The Steinberg highest weight has simple-coroot coordinates all equal to `q - 1`. -/
theorem steinbergWeight_pairing (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
    (ρ : Character P.torus.group) (hρ : IsHalfPositiveRootSum P ρ) (q : ℕ)
    (a : Specs.RootWeightAction.SimpleRoot P.torus P.positive)
    (c : Specs.CharacterDescent.Cocharacter P.torus.group)
    (hc : IsAttachedCoroot P.torus a.val c) :
    pairing P.torus.group (Additive.toMul ((q - 1) • Additive.ofMul ρ)) c =
      ((q - 1 : ℕ) : ℤ) := by
  obtain ⟨D, _, _⟩ := markedBase P
  have h := halfSum_simpleCoroot P ρ hρ a c hc
  rw [← D.pairing_eq] at h ⊢
  change D.rootDatum.toLinearMap ((q - 1) • Additive.ofMul ρ) (Additive.ofMul c) = _
  rw [map_nsmul, LinearMap.smul_apply, h, nsmul_eq_mul, mul_one]

section DimensionArgument

variable {A : HopfAlgebraCategory k} {V : Type u} [AddCommGroup V] [Module k V]

private theorem dist_finrank {n q : ℕ}
    (e : (MvPolynomial (Fin n) k ⧸ powersIdeal k (Fin n) q) ≃ₐ[k] A) :
    finrank k (Dist k A) = q ^ n := by
  rw [(WithConv.linearEquiv k (Module.Dual k A)).finrank_eq, Subspace.dual_finrank_eq]
  rw [Module.finrank_eq_card_basis ((truncatedBasis k n q).map e.toLinearEquiv)]
  simp

private theorem injective_evaluation (action : LeftAction k A V) (v : V)
    (ω : Module.Dual k A) (hω : HasDistributionSocle A ω)
    (hn : action (WithConv.toConv ω) v ≠ 0) :
    Function.Injective (fun a => action a v) := by
  let ev : Dist k A →ₗ[k] V := action.toLinearMap.flip v
  let J : Ideal (Dist k A) :=
    { ev.ker with
      smul_mem' := fun a b hb => by
        change action b v = 0 at hb
        change action (a * b) v = 0
        rw [map_mul]
        change action a (action b v) = 0
        rw [hb, map_zero] }
  have hJ : J = ⊥ := by
    by_contra h
    exact hn (hω.2 J h)
  change Function.Injective ev
  apply LinearMap.ker_eq_bot.mp
  ext a
  change a ∈ J ↔ a ∈ (⊥ : Ideal (Dist k A))
  rw [hJ]

/-- The top distribution detects injectivity of evaluation at a cyclic vector. -/
theorem finrank_of_cyclic_top_distribution {n q : ℕ}
    (e : (MvPolynomial (Fin n) k ⧸ powersIdeal k (Fin n) q) ≃ₐ[k] A)
    (action : LeftAction k A V) (v : V) (ω : Module.Dual k A)
    (hω : HasDistributionSocle A ω) (hn : action (WithConv.toConv ω) v ≠ 0)
    (hs : Function.Surjective (fun a => action a v)) :
    finrank k V = q ^ n := by
  let ev : Dist k A →ₗ[k] V := action.toLinearMap.flip v
  let E := LinearEquiv.ofBijective ev ⟨injective_evaluation action v ω hω hn, hs⟩
  exact E.finrank_eq.symm.trans (dist_finrank e)

end DimensionArgument

section NegativeKernel

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory Opposite
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (characterValue)
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.RootWeightAction (act extendVector mem_fixedSpace mem_weightSpace)
open Specs.SimpleClassification (SocleModel)
open Specs.SteinbergDistributions (KernelPresentation)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.RationalRepresentations (tensorCoordinate)
open LinearAlgebraicGroups.FiniteDistributions
  (pair restrict toAction toAction_pairs frobeniusPullback frobeniusPullback_formula)

open private affinePoint affinePoint_specGroupMap
  from LinearAlgebraicGroups.Representation.FlagLineBundle
open private toAlgebra fromAlgebra_toAlgebra cellKernel_iso
  from LinearAlgebraicGroups.Representation.SteinbergDistributions
open private fixedSpace_eq_of_radical hopfPreimage_comp_iso
  from LinearAlgebraicGroups.Representation.SimpleClassification
open private hopfPreimage from LinearAlgebraicGroups.Reductive.CentralTorus
open private tensorCoordinate_evaluation
  from LinearAlgebraicGroups.Affine.RationalRepresentations
open private act_mul act_smul
  from LinearAlgebraicGroups.Representation.RootWeightAction
open private basis_pair_apply
  from LinearAlgebraicGroups.Representation.RestrictedCyclicity

variable {p r : ℕ} [Fact p.Prime] [CharP k p]
local instance kernelHopfAlgebra {H : Specs.GroupScheme k} (K : KernelPresentation p r H) :
    HopfAlgebra k (K.hopf : Type u) :=
  CommHopfAlgCat.hopfAlgebra K.hopf

variable {P : OppositeBorelPair G} {U : ClosedSubgroup P.positive.group}
variable {χ : Character P.torus.group}

set_option backward.isDefEq.respectTransparency false in
private theorem orbitCoordinate (S : SocleModel P U χ)
    (R : TestAlgebra k) (f : S.A →ₐ[k] R) (v : S.socle) (i : S.J) :
    act S.socleAction R (affinePoint R f ≫ S.groupIso.hom.hom.hom)
      (extendVector R (S.socleBasis.equivFun v)) i =
      f (tensorCoordinate S.socleBasis i (S.socleCoaction.coaction v)) := by
  have h := S.socleAction_spec R f (S.socleBasis.equivFun v) i
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.trans (tensorCoordinate_evaluation S.socleBasis f.toLinearMap _ i)

private def negativeRestriction (S : SocleModel P U χ)
    (N : ClosedSubgroup P.negative.group) (PN : KernelPresentation p r N.group) :
    S.A ⟶ PN.hopf :=
  letI := PN.idealIsHopf
  hopfPreimage
    (((specGroupMap (hopfQuotientMap PN.coordinates (kernelIdeal PN.frobenius)) ≫
      PN.ambient.hom) ≫ (N.inclusion ≫ P.negative.inclusion)) ≫ S.groupIso.inv)

set_option backward.isDefEq.respectTransparency false in
private theorem negativeRestriction_spec (S : SocleModel P U χ)
    (N : ClosedSubgroup P.negative.group) (PN : KernelPresentation p r N.group) :
    (specGroupMap (negativeRestriction S N PN)).hom.hom ≫ S.groupIso.hom.hom.hom =
      PN.inclusion ≫ (N.inclusion ≫ P.negative.inclusion).hom.hom := by
  let := PN.idealIsHopf
  let f := (specGroupMap (hopfQuotientMap PN.coordinates (kernelIdeal PN.frobenius)) ≫
    PN.ambient.hom) ≫ (N.inclusion ≫ P.negative.inclusion)
  exact congrArg (fun a : specGroup PN.hopf ⟶ G.val => a.hom.hom)
    (hopfPreimage_comp_iso S.groupIso f)

set_option backward.isDefEq.respectTransparency false in
private def negativeAction (S : SocleModel P U χ)
    (N : ClosedSubgroup P.negative.group) (PN : KernelPresentation p r N.group) :
    LeftAction k (PN.hopf : Type u) S.socle :=
  toAction (restrict (negativeRestriction S N PN).hom.toCoalgHom S.socleCoaction)

set_option backward.isDefEq.respectTransparency false in
private theorem negativeAction_coordinate (S : SocleModel P U χ)
    (N : ClosedSubgroup P.negative.group) (PN : KernelPresentation p r N.group)
    (a : Module.Dual k PN.hopf) (i : S.J) :
    S.socleBasis.equivFun (negativeAction S N PN (WithConv.toConv a) S.highestVector) i =
      a ((negativeRestriction S N PN).hom.toAlgHom
        (tensorCoordinate S.socleBasis i (S.socleCoaction.coaction S.highestVector))) := by
  rw [negativeAction, toAction_pairs, basis_pair_apply]
  change a (tensorCoordinate S.socleBasis i
    ((negativeRestriction S N PN).hom.toAlgHom.toLinearMap.lTensor S.socle
      (S.socleCoaction.coaction S.highestVector))) = _
  rw [tensorCoordinate_evaluation]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem negativeKernel_cyclic [IsAlgClosed k] (hr : 1 ≤ r)
    (S : SocleModel P U χ)
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    (hχ : Dominant P χ)
    (hsmall : ∀ (a : Specs.RootWeightAction.SimpleRoot P.torus P.positive)
      (c : Specs.CharacterDescent.Cocharacter P.torus.group),
      IsAttachedCoroot P.torus a.val c → pairing P.torus.group χ c < ((p ^ r : ℕ) : ℤ))
    (N : ClosedSubgroup P.negative.group)
    (hN : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.negative) N)
    (PN : KernelPresentation p r N.group) :
    Function.Surjective (fun a : Dist k PN.hopf => negativeAction S N PN a S.highestVector) := by
  let F := frobeniusPullback p r S.A
  let hF := hopfKernelIdeal k F
  let PG : KernelPresentation p r G.val :=
    ⟨S.A, S.groupIso, F, frobeniusPullback_formula p r S.A, hF⟩
  obtain ⟨M, Upos, hM, hUpos, _, hT, _, hP, _⟩ :=
    LinearAlgebraicGroups.Representation.SteinbergDistributions.kernelFactorization
      (k := k) p r hr G P.reductive P.torus P.positive P.negative P.split P.maximal
      P.positiveBorel P.negativeBorel P.inPositive P.inNegative P.opposite
  obtain ⟨PT⟩ := hT
  obtain ⟨PP⟩ := hP
  have hcell := LinearAlgebraicGroups.Flag.OpenCell.openCell G P.reductive P.torus
    P.split P.maximal P.positive P.negative P.positiveBorel P.negativeBorel
    P.inPositive P.inNegative P.opposite N Upos hN hUpos
  let := hcell.1
  obtain ⟨e, he⟩ := cellKernel_iso
    P.torus N Upos PG PT PN PP
  let R := CommAlgCat.of k PG.hopf
  let yN : Points PN.scheme R := e.inv ≫ fst _ _
  let yT : Points PT.scheme R := e.inv ≫ snd _ _ ≫ fst _ _
  let yP : Points PP.scheme R := e.inv ≫ snd _ _ ≫ snd _ _
  let n : GroupPoints G.val R := yN ≫ PN.inclusion ≫ (N.inclusion ≫ P.negative.inclusion).hom.hom
  let t : GroupPoints P.torus.group R := yT ≫ PT.inclusion
  let u : GroupPoints Upos.group R := yP ≫ PP.inclusion
  let tG : GroupPoints G.val R := t ≫ P.torus.inclusion.hom.hom
  let uG : GroupPoints G.val R := u ≫ (Upos.inclusion ≫ P.positive.inclusion).hom.hom
  have hprod : (PG.inclusion : GroupPoints G.val R) = n * (tG * uG) := by
    have h := congrArg (e.inv ≫ ·) he
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at h
    rw [h]
    simp [Specs.OpenCell.cellMap, CocharacterDynamics.multiplyFactors,
      MonObj.comp_mul, n, t, u, tG, uG, yN, yT, yP, Category.assoc]
  let v := S.socleBasis.equivFun S.highestVector
  let c := characterValue χ R t
  have hfix := S.primitive.2.1
  rw [fixedSpace_eq_of_radical hU hUpos S.socleAction] at hfix
  have hu := mem_fixedSpace.mp hfix R u
  have ht := mem_weightSpace.mp S.primitive.2.2 R t
  have horb : act S.socleAction R PG.inclusion (extendVector R v) =
      c • act S.socleAction R n (extendVector R v) := by
    rw [hprod, act_mul, act_mul]
    exact by rw [show uG = u ≫ (Upos.inclusion ≫ P.positive.inclusion).hom.hom from rfl,
      hu, show tG = t ≫ P.torus.inclusion.hom.hom from rfl, ht, act_smul]
  let fN : PN.hopf →ₐ[k] R := toAlgebra yN
  let qN := negativeRestriction S N PN
  let := hF
  let qG := hopfQuotientMap S.A (kernelIdeal F)
  have hG : PG.inclusion = affinePoint R qG.hom.toAlgHom ≫ S.groupIso.hom.hom.hom := rfl
  have hn : n = affinePoint R (fN.comp qN.hom.toAlgHom) ≫ S.groupIso.hom.hom.hom := by
    have hpre : affinePoint R fN = yN := fromAlgebra_toAlgebra yN
    rw [← affinePoint_specGroupMap, Category.assoc, negativeRestriction_spec, hpre]
  have hcoords (i : S.J) :
      qG.hom.toAlgHom (tensorCoordinate S.socleBasis i (S.socleCoaction.coaction S.highestVector)) =
        c * fN (qN.hom.toAlgHom
          (tensorCoordinate S.socleBasis i (S.socleCoaction.coaction S.highestVector))) := by
    have h := congrFun horb i
    rw [hG, hn, orbitCoordinate S] at h
    change _ = c * act S.socleAction R
      (affinePoint R (fN.comp qN.hom.toAlgHom) ≫ S.groupIso.hom.hom.hom)
      (extendVector R v) i at h
    rw [orbitCoordinate S] at h
    exact h
  intro w
  obtain ⟨a, ha⟩ := LinearAlgebraicGroups.Representation.RestrictedCyclicity.cyclicity
    (k := k) p r (by omega) P U hU χ hχ hsmall S F PG.formula hF w
  let b : Module.Dual k PN.hopf :=
    a.ofConv.comp ((LinearMap.mulLeft k c).comp fN.toLinearMap)
  refine ⟨WithConv.toConv b, S.socleBasis.equivFun.injective (funext fun i => ?_)⟩
  rw [negativeAction_coordinate]
  have ha' := congrArg (fun v : S.socle => S.socleBasis.equivFun v i) ha
  rw [← WithConv.toConv_ofConv a, basis_pair_apply, tensorCoordinate_evaluation] at ha'
  change a.ofConv (c * fN (qN.hom.toAlgHom
    (tensorCoordinate S.socleBasis i (S.socleCoaction.coaction S.highestVector)))) = _
  rw [← hcoords i]
  exact ha'

end NegativeKernel


section ExtremalWeight

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory Opposite
open Specs.AdjointRepresentation (GroupPoints)
open Specs.BorelsAndChambers (IsPositiveSystem)
open Specs.BruhatOrbitParametrization
open Specs.OrderedRootProducts (Enumerates)
open Specs.RootWeightAction (Representation weightSpace act)
open private representativeExists from LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
open private weylTransport from LinearAlgebraicGroups.Representation.RootWeightAction

variable {P : OppositeBorelPair G}

private theorem sum_roots_comp_equiv {I X : Type u} [Finite I] [AddCommMonoid X]
    (S S' : Set I) (π : Equiv.Perm I) (hπ : π '' S = S') (f : I → X) :
    (∑ᶠ a : S, f (π a.val)) = ∑ᶠ a : S', f a.val := by
  classical
  let := Fintype.ofFinite S
  let := Fintype.ofFinite S'
  simp only [finsum_eq_sum_of_fintype]
  let E : S ≃ S' := π.subtypeEquiv fun a => by
    rw [← hπ]
    refine ⟨fun ha => ⟨a, ha, rfl⟩, ?_⟩
    rintro ⟨b, hb, he⟩
    exact π.injective he ▸ hb
  exact E.sum_comp (fun a : S' => f a.val)

private theorem negative_root_sum [IsCommMonObj P.torus.group.X]
    (D : Datum P.torus) (hB : IsPositiveSystem P.torus (subgroupRoots P.torus P.positive)) :
    (∑ᶠ a : subgroupRoots P.torus P.negative, D.rootDatum.root a.val) =
      -∑ᶠ a : subgroupRoots P.torus P.positive, D.rootDatum.root a.val := by
  let := D.finiteRoots
  let := D.rootDatum.indexNeg
  let π : Equiv.Perm (Root P.torus) := Equiv.neg _
  obtain ⟨f, hf, hfpos⟩ := hB
  have hneg (a : Root P.torus) : D.rootDatum.root (π a) = -D.rootDatum.root a := by
    change D.rootDatum.root (-a) = _
    simp
  have hπ : π '' subgroupRoots P.torus P.positive = subgroupRoots P.torus P.negative := by
    ext a
    rw [P.opposite, hfpos, π.image_eq_preimage_symm]
    change (0 < f (Additive.ofMul (π a).val)) ↔ ¬ (0 < f (Additive.ofMul a.val))
    rw [← D.root_eq, ← D.root_eq, hneg, map_neg, neg_pos, D.root_eq]
    exact lt_iff_le_and_ne.trans ((and_iff_left (hf a)).trans not_lt.symm)
  rw [← sum_roots_comp_equiv _ _ π hπ D.rootDatum.root]
  let := Fintype.ofFinite (subgroupRoots P.torus P.positive)
  simp only [finsum_eq_sum_of_fintype, hneg, Finset.sum_neg_distrib]

private theorem extremal_weight [IsCommMonObj P.torus.group.X]
    (D : Datum P.torus) (I : DatumAndWeyl.Identification D)
    (hB : IsPositiveSystem P.torus (subgroupRoots P.torus P.positive))
    (hW : Specs.BorelPositivity.WeylAction D)
    (hBneg : IsPositiveSystem P.torus (subgroupRoots P.torus P.negative))
    (ρ : Character P.torus.group) (hρ : IsHalfPositiveRootSum P ρ)
    (q : ℕ) {J : Type u} [Fintype J] [DecidableEq J] (σ : Representation G.val J)
    (v : weightSpace σ P.torus (Additive.toMul ((q - 1) • Additive.ofMul ρ)))
    (hv : (v : J → k) ≠ 0) :
    ∃ w : weightSpace σ P.torus (Additive.toMul (-((q - 1) • Additive.ofMul ρ))),
      (w : J → k) ≠ 0 := by
  classical
  let := D.finiteRoots
  let := D.freeCharacters
  obtain ⟨w, hw, _⟩ := hW.2.2 _ _ hB hBneg
  have hsum : (2 : ℤ) • Additive.ofMul ρ =
      ∑ᶠ a : subgroupRoots P.torus P.positive, D.rootDatum.root a.val := by
    simpa only [IsHalfPositiveRootSum, D.root_eq] using hρ
  let W := w.val.weightEquiv
  have hWsum : W (∑ᶠ a : subgroupRoots P.torus P.positive, D.rootDatum.root a.val) =
      ∑ᶠ a : subgroupRoots P.torus P.negative, D.rootDatum.root a.val := by
    rw [← sum_roots_comp_equiv _ _ _ hw D.rootDatum.root]
    let := Fintype.ofFinite (subgroupRoots P.torus P.positive)
    simp only [finsum_eq_sum_of_fintype, map_sum]
    exact Finset.sum_congr rfl (fun a _ => D.rootDatum.weylGroup_apply_root w a.val)
  have hWρ : W (Additive.ofMul ρ) = -Additive.ofMul ρ := by
    have h := hWsum.trans (negative_root_sum D hB)
    rw [← hsum, map_smul, ← smul_neg] at h
    exact (smul_right_injective (Additive (Character P.torus.group)) (by decide : (2 : ℤ) ≠ 0)) h
  let χ := Additive.toMul ((q - 1) • Additive.ofMul ρ)
  have hχ : (I.labelEquiv w).val χ = Additive.toMul (-((q - 1) • Additive.ofMul ρ)) := by
    apply Additive.ofMul.injective
    rw [← I.characterAction]
    change W ((q - 1) • Additive.ofMul ρ) = -((q - 1) • Additive.ofMul ρ)
    rw [map_nsmul, hWρ, smul_neg]
  obtain ⟨n, hn⟩ := representativeExists I P.split w
  let K := CommAlgCat.of k k
  let n' : GroupPoints I.normalizer.group K := toUnit _ ≫ n
  have hn' : n' ≫ I.quotient.hom.hom =
      toUnit _ ≫ I.image.constantGroup.sectionPoint (I.labelEquiv w) := by
    dsimp only [n']
    rw [Category.assoc, hn]
  obtain ⟨e, _⟩ := weylTransport σ I w n' hn' χ
  have he : e v ≠ 0 := fun h => hv (congrArg Subtype.val (e.injective (h.trans e.map_zero.symm)))
  rw [← hχ]
  exact ⟨e v, fun h => he (Subtype.ext h)⟩

end ExtremalWeight


section ChartWeights

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory Opposite
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (characterValue)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.RootWeightAction (act actLinear extendVector mem_weightSpace weightSpace)
open Specs.SimpleClassification (SocleModel)
open Specs.SteinbergDistributions (KernelPresentation RootCoordinates orderedPoint)
open LinearAlgebraicGroups.RationalRepresentations (tensorCoordinate)
open private orderedPoint_conjugate scaledCoordinates scaledCoordinates_X
  scaledCoordinates_monomial monomialWeight characterValueHom characterValueHom_apply
  from LinearAlgebraicGroups.Representation.SteinbergDistributions
open private scalar_action_of_normalized_tangent characterValue_natural
  from LinearAlgebraicGroups.RootData.RootGroups
open private act_natural act_mul act_smul from LinearAlgebraicGroups.Representation.RootWeightAction
open private affinePoint affinePoint_specGroupMap
  from LinearAlgebraicGroups.Representation.FlagLineBundle

variable {p r : ℕ} [Fact p.Prime] [CharP k p]
variable {P : OppositeBorelPair G} {U : ClosedSubgroup P.positive.group}
variable {χ : Character P.torus.group}

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
private theorem chartCoefficient_mem_weight
    (S : SocleModel P U χ) (N : ClosedSubgroup P.negative.group)
    (PN : KernelPresentation p r N.group)
    {family : RootSubgroupFamily P.torus} {l : List (Root P.torus)}
    (x : RootCoordinates family l) (q : ℕ)
    (e : (MvPolynomial (Fin l.length) k ⧸ powersIdeal k (Fin l.length) q) ≃ₐ[k] PN.hopf)
    (hchart : ∀ (R : TestAlgebra k) (a : PN.hopf →ₐ[k] R),
      affinePoint R a ≫ PN.inclusion ≫ (N.inclusion ≫ P.negative.inclusion).hom.hom =
        orderedPoint x R (fun i => a (e (Ideal.Quotient.mk _ (MvPolynomial.X i)))))
    (d : Fin l.length → Fin q) :
    S.socleBasis.equivFun
      (negativeAction S N PN (WithConv.toConv (((truncatedBasis k l.length q).map
        e.toLinearEquiv).coord d)) S.highestVector) ∈
      weightSpace S.socleAction P.torus (χ * monomialWeight (fun i => (l.get i).val) d) := by
  classical
  let A := PN.hopf
  let b := (truncatedBasis k l.length q).map e.toLinearEquiv
  let qN := negativeRestriction S N PN
  let v := S.socleBasis.equivFun S.highestVector
  let f (i : S.J) : A := qN.hom.toAlgHom (tensorCoordinate S.socleBasis i
    (S.socleCoaction.coaction S.highestVector))
  let w (j : Fin l.length → Fin q) : S.J → k := fun i => b.coord j (f i)
  have hw : S.socleBasis.equivFun
      (negativeAction S N PN (WithConv.toConv (b.coord d)) S.highestVector) = w d :=
    funext (negativeAction_coordinate S N PN (b.coord d))
  change _ ∈ weightSpace _ _ _
  rw [show _ = w d from hw]
  apply mem_weightSpace.mpr
  intro R t
  let B := CommAlgCat.of k (R ⊗[k] A)
  let lt : R →ₐ[k] B := Algebra.TensorProduct.includeLeft
  let rt : A →ₐ[k] B := Algebra.TensorProduct.includeRight
  let t' : GroupPoints P.torus.group B := mapPoints (CommAlgCat.ofHom lt) t
  let g : GroupPoints G.val R := t ≫ P.torus.inclusion.hom.hom
  let g' : GroupPoints G.val B := t' ≫ P.torus.inclusion.hom.hom
  let α (i : Fin l.length) := (l.get i).val
  let c (i : Fin l.length) := characterValue (α i) B t'
  let s (j : Fin l.length → Fin q) := characterValue (monomialWeight α j) R t
  let cχ := characterValue χ R t
  let gA (a : A →ₐ[k] B) : GroupPoints G.val B :=
    affinePoint B (a.comp qN.hom.toAlgHom) ≫ S.groupIso.hom.hom.hom
  have gA_chart (a : A →ₐ[k] B) :
      gA a = orderedPoint x B (fun i => a (e (Ideal.Quotient.mk _ (MvPolynomial.X i)))) := by
    dsimp only [gA]
    rw [← affinePoint_specGroupMap, Category.assoc, negativeRestriction_spec]
    exact hchart B a
  let rt' := scaledCoordinates e c rt
  have hconj : MulAut.conj g' (gA rt) = gA rt' := by
    rw [gA_chart, gA_chart]
    have hc (i : Fin l.length) : rt' (e (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
        c i * rt (e (Ideal.Quotient.mk _ (MvPolynomial.X i))) :=
      scaledCoordinates_X e c rt i
    rw [show (fun i => rt' (e (Ideal.Quotient.mk _ (MvPolynomial.X i)))) =
      (fun i => c i * rt (e (Ideal.Quotient.mk _ (MvPolynomial.X i)))) from funext hc]
    exact orderedPoint_conjugate x B t'
      (fun i => scalar_action_of_normalized_tangent P.torus (family (l.get i)).val
        P.split (α i) (family (l.get i)).prop (x.line i) (x.groupIso i)) _
  have hmul : g' * gA rt = gA rt' * g' := by
    rw [← hconj, MulAut.conj_apply, inv_mul_cancel_right]
  have hχ : characterValue χ B t' = lt cχ := characterValue_natural χ (CommAlgCat.ofHom lt) t
  have heq : act S.socleAction B g' (act S.socleAction B (gA rt) (extendVector B v)) =
      lt cχ • act S.socleAction B (gA rt') (extendVector B v) := by
    rw [← act_mul, hmul, act_mul]
    have h := mem_weightSpace.mp S.primitive.2.2 B t'
    change act S.socleAction B g' (extendVector B v) = _ at h
    rw [h, hχ, act_smul]
  have hr (a : A →ₐ[k] B) :
      act S.socleAction B (gA a) (extendVector B v) =
        ∑ j, a (b j) • extendVector B (w j) := by
    have hf (i : S.J) : act S.socleAction B (gA a) (extendVector B v) i = a (f i) :=
      orbitCoordinate S B (a.comp qN.hom.toAlgHom) S.highestVector i
    funext i
    rw [hf, Finset.sum_apply]
    conv_lhs => rw [← b.sum_repr (f i)]
    simp only [map_sum, map_smul, Pi.smul_apply, extendVector]
    apply Finset.sum_congr rfl
    intro j _
    calc
      (b.repr (f i)) j • a (b j) = algebraMap k B ((b.repr (f i)) j) * a (b j) :=
        Algebra.smul_def (R := k) (A := B) ((b.repr (f i)) j) (a (b j))
      _ = a (b j) * algebraMap k B (w j i) := mul_comm _ _
      _ = a (b j) • algebraMap k B (w j i) := (smul_eq_mul _ _).symm
  have hs (j : Fin l.length → Fin q) : rt' (b j) = lt (s j) * rt (b j) := by
    change scaledCoordinates e c rt (e (truncatedBasis k l.length q j)) = _
    rw [scaledCoordinates_monomial]
    congr 1
    dsimp only [c, s, monomialWeight]
    simp only [← characterValueHom_apply, map_prod, map_pow]
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    simp only [characterValueHom_apply]
    exact characterValue_natural _ (CommAlgCat.ofHom lt) t
  have han (j : Fin l.length → Fin q) :
      act S.socleAction B g' (extendVector B (w j)) =
        fun i => lt (act S.socleAction R g (extendVector R (w j)) i) := by
    have h := act_natural S.socleAction (CommAlgCat.ofHom lt) g (extendVector R (w j))
    change act S.socleAction B (mapPoints (CommAlgCat.ofHom lt) g)
      (fun i => lt (algebraMap k R (w j i))) = _ at h
    have hg : mapPoints (CommAlgCat.ofHom lt) g = g' :=
      (Category.assoc ((testSpec k).map (CommAlgCat.ofHom lt).op) t
        P.torus.inclusion.hom.hom).symm
    rw [hg] at h
    change act S.socleAction B g' (fun i => lt (algebraMap k R (w j i))) =
      (fun i => lt (act S.socleAction R g (extendVector R (w j)) i)) at h
    rw [show (fun i => lt (algebraMap k R (w j i))) = extendVector B (w j) from
      funext (fun i => lt.commutes (w j i))] at h
    exact h
  rw [hr, hr] at heq
  change (actLinear S.socleAction B g') (∑ j, rt (b j) • extendVector B (w j)) =
    lt cχ • ∑ j, rt' (b j) • extendVector B (w j) at heq
  have hlinear (j : Fin l.length → Fin q) :
      actLinear S.socleAction B g' (extendVector B (w j)) =
        fun i => lt (act S.socleAction R g (extendVector R (w j)) i) := han j
  simp only [map_sum, map_smul, hlinear, hs, Finset.smul_sum] at heq
  let L : B →ₗ[k] R := (TensorProduct.rid k R).toLinearMap.comp ((b.coord d).lTensor R)
  have hL (a : R) (x : A) : L (lt a * rt x) = b.coord d x • a := by
    change L ((a ⊗ₜ[k] (1 : A)) * ((1 : R) ⊗ₜ[k] x)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  have hLbasis (a : R) (j : Fin l.length → Fin q) :
      L (lt a * rt (b j)) = if j = d then a else 0 := by
    rw [hL, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  have hχs : characterValue (χ * monomialWeight α d) R t = cχ * s d := by
    rw [← characterValueHom_apply, map_mul, characterValueHom_apply, characterValueHom_apply]
  rw [hχs]
  funext i
  have h := congrArg (fun z : S.J → B => L (z i)) heq
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum] at h
  have hp (j : Fin l.length → Fin q) :
      lt cχ * (lt (s j) * rt (b j) * algebraMap k B (w j i)) =
        lt ((cχ * s j) * algebraMap k R (w j i)) * rt (b j) := by
    rw [map_mul, map_mul, AlgHom.commutes]
    ring
  simp only [mul_comm (rt (b _)), extendVector, hp, hLbasis, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  exact h

end ChartWeights


section TopCoefficient

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Specs.BorelsAndChambers (IsPositiveSystem)
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.OrderedRootProducts (Enumerates RootSubgroupFamily)
open Specs.RootWeightAction (weightSpace)
open Specs.SimpleClassification (SocleModel)
open Specs.SteinbergDistributions
  (KernelPresentation RootCoordinates IsTopCoefficient topExponent orderedPoint)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private affinePoint from LinearAlgebraicGroups.Representation.FlagLineBundle
open private monomialWeight truncatedBasis_apply truncatedMonomial exponent exponent_injective
  topExponent_apply from LinearAlgebraicGroups.Representation.SteinbergDistributions
open private weightSpacesIndependent from LinearAlgebraicGroups.Representation.InducedSocle

variable {p r : ℕ} [Fact p.Prime] [CharP k p]
variable {P : OppositeBorelPair G} {U : ClosedSubgroup P.positive.group}

private def enumerationEquiv {I : Type u} {S : Set I} {l : List I}
    (hl : Enumerates l S) : Fin l.length ≃ S :=
  Equiv.ofBijective (fun i => ⟨l.get i, (hl.2 _).mp (List.get_mem l i)⟩) (by
    constructor
    · intro i j h
      exact hl.1.get_inj_iff.mp (congrArg Subtype.val h)
    · intro a
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp ((hl.2 a.val).mpr a.property)
      exact ⟨i, Subtype.ext hi⟩)

private theorem length_of_enumerates {I : Type u} {S : Set I} {l : List I}
    (hl : Enumerates l S) :
    l.length = S.ncard := by
  classical
  let E := enumerationEquiv hl
  let : Fintype S := Fintype.ofEquiv (Fin l.length) E
  rw [Set.ncard_eq_toFinset_card S (Set.toFinite S)]
  simpa using Fintype.card_congr E

private def topIndex (n q : ℕ) (hq : 0 < q) : Fin n → Fin q :=
  fun _ => ⟨q - 1, by omega⟩

private theorem monomialWeight_additive (χ : Character P.torus.group)
    {l : List (Root P.torus)} {q : ℕ} (d : Fin l.length → Fin q) :
    Additive.ofMul (χ * monomialWeight (fun i => (l.get i).val) d) =
      Additive.ofMul χ + ∑ i, (d i).val • Additive.ofMul (l.get i).val := by
  simp only [monomialWeight, ofMul_mul, ofMul_prod, ofMul_pow]

private theorem extremal_only_at_top [IsCommMonObj P.torus.group.X]
    (D : Datum P.torus) (hpos : IsPositiveSystem P.torus (subgroupRoots P.torus P.positive))
    (hneg : IsPositiveSystem P.torus (subgroupRoots P.torus P.negative))
    (ρ : Character P.torus.group) (hρ : IsHalfPositiveRootSum P ρ)
    {l : List (Root P.torus)} (hl : Enumerates l (subgroupRoots P.torus P.negative))
    {q : ℕ} (hq : 0 < q) (d : Fin l.length → Fin q) (hd : d ≠ topIndex l.length q hq) :
    Additive.toMul ((q - 1) • Additive.ofMul ρ) *
        monomialWeight (fun i => (l.get i).val) d ≠
      Additive.toMul (-((q - 1) • Additive.ofMul ρ)) := by
  classical
  let χ := Additive.toMul ((q - 1) • Additive.ofMul ρ)
  let dmax := topIndex l.length q hq
  let a (i : Fin l.length) := Additive.ofMul (l.get i).val
  let E := enumerationEquiv hl
  let := Fintype.ofEquiv _ E
  have hsum : (∑ i, a i) = -(2 : ℤ) • Additive.ofMul ρ := by
    have ht := E.sum_comp (fun j => Additive.ofMul (j : Root P.torus).val)
    change (∑ i, a i) = _ at ht
    rw [ht, ← finsum_eq_sum_of_fintype]
    have h := negative_root_sum D hpos
    simp only [D.root_eq] at h
    change (2 : ℤ) • Additive.ofMul ρ = _ at hρ
    rw [h, ← hρ, neg_smul]
  have htop :
      Additive.ofMul (χ * monomialWeight (fun i => (l.get i).val) dmax) =
        -((q - 1) • Additive.ofMul ρ) := by
    rw [monomialWeight_additive]
    change (q - 1) • Additive.ofMul ρ + (∑ i, (q - 1) • a i) = _
    rw [← Finset.smul_sum, hsum, neg_smul, two_smul, smul_neg, smul_add]
    abel
  obtain ⟨F, _, hF⟩ := hneg
  have hpositive (i : Fin l.length) : 0 < F (a i) := by
    have hi := (hl.2 _).mp (List.get_mem l i)
    rwa [hF] at hi
  have hstrict : (∑ i, (d i).val • F (a i)) < ∑ i, (dmax i).val • F (a i) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact nsmul_le_nsmul_left (hpositive i).le (by change (d i).val ≤ q - 1; omega)
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hd
      refine ⟨i, Finset.mem_univ _, ?_⟩
      exact nsmul_lt_nsmul_left (hpositive i) (lt_of_le_of_ne
        (by change (d i).val ≤ q - 1; omega) (fun h => hi (Fin.ext h)))
  intro he
  have hh : Additive.ofMul (χ * monomialWeight (fun i => (l.get i).val) d) =
      Additive.ofMul (χ * monomialWeight (fun i => (l.get i).val) dmax) := by
    change χ * _ = _ at he
    rw [htop, he]
    rfl
  simp only [monomialWeight_additive, add_right_inj] at hh
  have h := congrArg F hh
  simp only [map_sum, map_nsmul] at h
  exact hstrict.ne h

set_option backward.isDefEq.respectTransparency false in
private theorem topFunctional_eq_coordinate
    {A : HopfAlgebraCategory k} {n q : ℕ} (hq : 0 < q)
    (e : (MvPolynomial (Fin n) k ⧸ powersIdeal k (Fin n) q) ≃ₐ[k] A)
    (ω : Module.Dual k A) (hω : IsTopCoefficient e.toLinearEquiv ω) :
    ω = ((truncatedBasis k n q).map e.toLinearEquiv).coord (topIndex n q hq) := by
  classical
  let b := (truncatedBasis k n q).map e.toLinearEquiv
  let d := topIndex n q hq
  apply b.ext
  intro j
  have hj : b j = e (Ideal.Quotient.mk _ (MvPolynomial.monomial (exponent j) 1)) := by
    change e (truncatedBasis k n q j) = _
    rw [truncatedBasis_apply, truncatedMonomial]
  have hd : exponent d = topExponent n q := by
    ext i
    exact (topExponent_apply n q i).symm
  have hh : ω (b j) = (MvPolynomial.monomial (exponent j) (1 : k)).coeff (topExponent n q) :=
    (congrArg ω hj).trans (hω _)
  change ω (b j) = b.coord d (b j)
  rw [hh, MvPolynomial.coeff_monomial, ← hd]
  simp only [exponent_injective.eq_iff, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem topDistribution_nonzero [IsCommMonObj P.torus.group.X]
    (D : Datum P.torus) (I : DatumAndWeyl.Identification D)
    (hB : IsPositiveSystem P.torus (subgroupRoots P.torus P.positive))
    (hBneg : IsPositiveSystem P.torus (subgroupRoots P.torus P.negative))
    (hW : Specs.BorelPositivity.WeylAction D)
    (ρ : Character P.torus.group) (hρ : IsHalfPositiveRootSum P ρ)
    {q : ℕ} (hq : 0 < q)
    (S : SocleModel P U (Additive.toMul ((q - 1) • Additive.ofMul ρ)))
    (N : ClosedSubgroup P.negative.group)
    (PN : KernelPresentation p r N.group)
    {family : RootSubgroupFamily P.torus} {l : List (Root P.torus)}
    (hl : Enumerates l (subgroupRoots P.torus P.negative))
    (x : RootCoordinates family l)
    (e : (MvPolynomial (Fin l.length) k ⧸ powersIdeal k (Fin l.length) q) ≃ₐ[k] PN.hopf)
    (hchart : ∀ (R : TestAlgebra k) (a : PN.hopf →ₐ[k] R),
      affinePoint R a ≫ PN.inclusion ≫ (N.inclusion ≫ P.negative.inclusion).hom.hom =
        orderedPoint x R (fun i => a (e (Ideal.Quotient.mk _ (MvPolynomial.X i)))))
    (ω : Module.Dual k PN.hopf) (hω : IsTopCoefficient e.toLinearEquiv ω)
    (hs : Function.Surjective (fun a : Dist k PN.hopf => negativeAction S N PN a S.highestVector)) :
    negativeAction S N PN (WithConv.toConv ω) S.highestVector ≠ 0 := by
  classical
  let χ := Additive.toMul ((q - 1) • Additive.ofMul ρ)
  let χlow := Additive.toMul (-((q - 1) • Additive.ofMul ρ))
  let v : weightSpace S.socleAction P.torus χ := ⟨_, S.primitive.2.2⟩
  obtain ⟨w, hw⟩ := extremal_weight D I hB hW hBneg ρ hρ q S.socleAction v S.primitive.1
  let b := (truncatedBasis k l.length q).map e.toLinearEquiv
  let dmax := topIndex l.length q hq
  let := CommHopfAlgCat.hopfAlgebra PN.hopf
  let ev : Dist k PN.hopf →ₗ[k] (S.J → k) :=
    S.socleBasis.equivFun.toLinearMap.comp ((negativeAction S N PN).toLinearMap.flip S.highestVector)
  let W : Submodule k (S.J → k) :=
    ⨆ (ψ) (_ : ψ ≠ χlow), weightSpace S.socleAction P.torus ψ
  obtain ⟨a, ha⟩ := hs (S.socleBasis.equivFun.symm w.val)
  have he : ev a = w.val := by
    change S.socleBasis.equivFun (negativeAction S N PN a S.highestVector) = _
    exact (congrArg S.socleBasis.equivFun ha).trans (LinearEquiv.apply_symm_apply _ _)
  have hb : (∑ d, a.ofConv (b d) • WithConv.toConv (b.coord d)) = a := by
    apply WithConv.ofConv_injective
    simpa only [WithConv.ofConv_sum, WithConv.ofConv_smul, WithConv.ofConv_toConv,
      Basis.coe_dualBasis, Basis.dualBasis_repr] using b.dualBasis.sum_repr a.ofConv
  intro hz
  have hz' : ev (WithConv.toConv (b.coord dmax)) = 0 := by
    have htop := topFunctional_eq_coordinate hq e ω hω
    rw [← htop]
    change S.socleBasis.equivFun (negativeAction S N PN (WithConv.toConv ω) S.highestVector) = _
    rw [hz, map_zero]
  have hmem : ev a ∈ W := by
    rw [← hb, map_sum]
    apply Submodule.sum_mem
    intro d _
    rw [ev.map_smul (a.ofConv (b d)) (WithConv.toConv (b.coord d))]
    apply Submodule.smul_mem
    by_cases hd : d = dmax
    · rw [hd, hz']
      exact W.zero_mem
    · let ψ := χ * monomialWeight (fun i => (l.get i).val) d
      have hψ : ψ ≠ χlow := extremal_only_at_top D hB hBneg ρ hρ hl hq d hd
      have hle : weightSpace S.socleAction P.torus ψ ≤ W :=
        (le_iSup (fun _ : ψ ≠ χlow => weightSpace S.socleAction P.torus ψ) hψ).trans
          (le_iSup (fun ψ => ⨆ _ : ψ ≠ χlow, weightSpace S.socleAction P.torus ψ) ψ)
      exact hle (chartCoefficient_mem_weight S N PN x q e hchart d)
  have hdis : Disjoint (weightSpace S.socleAction P.torus χlow) W :=
    iSupIndep_def.mp (weightSpacesIndependent P S.socleAction) χlow
  rw [he] at hmem
  exact hw ((Submodule.mem_bot k).mp (hdis.le_bot ⟨w.property, hmem⟩))

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem dimension : Dimension.{u} := by
  classical
  intro k _ _ p r _ _ hr G hG hsc P _ ρ hρ U hU S
  let q := p ^ r
  have hq : 0 < q := pow_pos (Fact.out : p.Prime).pos r
  have hpairs := steinbergWeight_pairing P ρ hρ q
  have hdom : Dominant P (Additive.toMul ((q - 1) • Additive.ofMul ρ)) := by
    intro a c hc
    rw [hpairs a c hc]
    exact Int.natCast_nonneg _
  have hsmall (a : Specs.RootWeightAction.SimpleRoot P.torus P.positive)
      (c : Specs.CharacterDescent.Cocharacter P.torus.group)
      (hc : IsAttachedCoroot P.torus a.val c) :
      pairing P.torus.group (Additive.toMul ((q - 1) • Additive.ofMul ρ)) c < (q : ℤ) := by
    rw [hpairs a c hc]
    omega
  obtain ⟨N, hN, ⟨PN⟩, ⟨family⟩, ⟨l, hl⟩, hcoord⟩ :=
    LinearAlgebraicGroups.Representation.SteinbergDistributions.orderedNegativeDistributions
      (k := k) p r hr G P.reductive P.torus P.positive P.negative P.split P.maximal
      P.positiveBorel P.negativeBorel P.inPositive P.inNegative P.opposite
  obtain ⟨lpos, hlpos, hlen, x, hx⟩ := hcoord PN family l hl
  obtain ⟨e, he, ω, hω, _, _, hωsoc⟩ := hx x
  obtain ⟨comm, D, ⟨I⟩, hB, hW, _, _⟩ :=
    RootData.BorelPositivity.borelPositivity G P.reductive P.torus P.split P.maximal
  let := comm
  have hs := negativeKernel_cyclic hr S hU hdom hsmall N hN PN
  have hn := topDistribution_nonzero D I
    (hB.1 P.positive P.positiveBorel P.inPositive)
    (hB.1 P.negative P.negativeBorel P.inNegative) hW ρ hρ hq S N PN hl x e he ω hω hs
  have hdim := finrank_of_cyclic_top_distribution e (negativeAction S N PN) S.highestVector
    ω hωsoc hn hs
  rw [hlen, length_of_enumerates hlpos] at hdim
  exact hdim

end TopCoefficient


end

end LinearAlgebraicGroups.Representation.SteinbergDimension
