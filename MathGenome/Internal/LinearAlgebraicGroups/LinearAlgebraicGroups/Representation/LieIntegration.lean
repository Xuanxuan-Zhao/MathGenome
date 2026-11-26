import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.LieIntegration
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SplitLieIntegration
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FrobeniusDifferential
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SemisimplyDifferentiated
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.TensorAndDual
import Batteries.Tactic.OpenPrivate
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Algebra.Lie.BaseChange
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompleteReducibility

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Representation.LieIntegration

open _root_.LinearAlgebraicGroups.Specs
open Specs.LieIntegration
open Specs.GeometricRadicals (IsSemisimple)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.SplitLieIntegration
open Specs.Pinning (SplitBorelPair AttachedDatum)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (pairing)
open Specs.RootWeightAction (SimpleRoot)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section

section SplitWeights

variable {k : Type u} [Field k] [CharZero k]

/-- Integral values on the attached simple coroots specify a character when
the cocharacter lattice is the coroot lattice. -/
theorem character_of_dominant_weight
    {G : AffineAlgebraicGroup k} (P : FlagLineBundle.OppositeBorelPair G)
    (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G)
    (t : IdentityLieStructure P.torus.group) (lam : Weight t)
    (hdom : IsDominant P t lam) :
    ∃ χ : Character P.torus.group, ∀ h, lam h = characterDifferential χ h := by
  classical
  letI := t.lieRing
  letI := t.lieAlgebra
  let Q : SplitBorelPair k :=
    ⟨G, P.reductive, P.torus, P.split, P.maximal, P.positive, P.positiveBorel, P.inPositive⟩
  let D := Classification.Pinning.attachedDatum Q
  letI := D.comm
  let Y := Additive (Cocharacter P.torus.group)
  let c : SimpleRoot P.torus P.positive → Y := fun α => D.datum.rootDatum.coroot α.val
  obtain ⟨hspan, b, hb⟩ := SimpleCorootTangents.basisAndLattice Q hG D t
  have htop : Submodule.span ℤ (Set.range c) = ⊤ :=
    hspan.trans ((Classification.SimplyConnectedLattice.latticeCriterion
      G hG P.torus P.split P.maximal D.datum).mp hsc)
  have hc : LinearIndependent ℤ c := by
    let e : SimpleRoot P.torus P.positive → D.base.support :=
      fun α => ⟨α.val, (D.simple_iff _).mpr α.property⟩
    exact D.base.linearIndepOn_coroot.comp e (fun _ _ he =>
      Subtype.ext (congrArg (fun z : D.base.support => z.val) he))
  let cb : Module.Basis (SimpleRoot P.torus P.positive) ℤ Y :=
    Module.Basis.mk hc (ge_of_eq htop)
  have hnat (i : SimpleRoot P.torus P.positive) : ∃ n : ℕ, lam (b i) = (n : k) :=
    hdom i (Additive.toMul (c i)) (b i) (D.datum.attached i.val) (hb i)
  choose n hn using hnat
  have hcb (i : SimpleRoot P.torus P.positive) : cb i = c i := by simp [cb]
  let p := D.datum.rootDatum.toLinearMap
  let y : Module.Dual ℤ Y := cb.constr ℤ fun i => (n i : ℤ)
  let χ : Character P.torus.group := Additive.toMul (p.toPerfPair.symm y)
  have hχ (i : SimpleRoot P.torus P.positive) :
      pairing P.torus.group χ (Additive.toMul (c i)) = (n i : ℤ) := by
    rw [← D.datum.pairing_eq]
    change p.toPerfPair (p.toPerfPair.symm y) (c i) = _
    rw [LinearEquiv.apply_symm_apply, ← hcb i]
    exact cb.constr_basis ℤ _ i
  obtain ⟨d, hd⟩ := (SplitLieIntegration.characterComparison P.torus.group P.split t).2.2.1
  have hd_eq : lam = d (Additive.ofMul χ) := by
    let b' : Module.Basis (SimpleRoot P.torus P.positive) k (Lie k P.torus.group) := b
    apply b'.ext
    intro i
    change lam (b i) = d (Additive.ofMul χ) (b i)
    rw [hn i, hd, SplitLieIntegration.characterDifferential_apply_cocharacter χ
      (Additive.toMul (c i)) (hb i), hχ i, Int.cast_natCast]
  exact ⟨χ, fun h => (LinearMap.congr_fun hd_eq h).trans (hd χ h)⟩

/-- The split simply connected case for an irreducible finite-dimensional Lie module. -/
theorem integrates_simple_of_split
    {G : AffineAlgebraicGroup k} (P : FlagLineBundle.OppositeBorelPair G)
    (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G)
    (s : IdentityLieStructure G.val) (t : IdentityLieStructure P.torus.group) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      [LieRingModule (Lie k G.val) V] [LieModule k (Lie k G.val) V],
      LieModule.IsIrreducible k (Lie k G.val) V → Integrates G V := by
  letI := s.lieRing
  letI := s.lieAlgebra
  intro V _ _ _ _ _ hV
  obtain ⟨⟨lam, h, _⟩, criterion⟩ := SplitLieIntegration.splitIntegration G hG P s t V hV
  obtain ⟨hdom, hInt, _⟩ := criterion lam h
  exact hInt.mpr (character_of_dominant_weight P hG hsc t lam hdom)

end SplitWeights

section Coactions

open RationalRepresentations
open Specs.RationalHighestWeightComparison (AgreesWithCoaction)

open private tangentPoint_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.LieStableSubspaces
open private exists_directSumCoaction differentiatedCoaction_natural from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FullyFaithfulDifferentiation
open private integrates_of_lieEquiv from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SplitLieIntegration

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private abbrev presentedTangent {A : HopfAlgebraCategory k}
    (e : specGroup A ≅ G.val) (x : Lie k G.val) :=
  tangentPointOfLie A (mapPointKernel e.inv x)

private theorem coordinatePresentation (G : AffineAlgebraicGroup k) :
    ∃ (A : HopfAlgebraCategory k), Nonempty (specGroup A ≅ G.val) := by
  letI := G.property.1
  obtain ⟨A, e⟩ := (essImage_hopfSpec (R := CommRingCat.of k)).mpr
    (show IsAffine G.val.X.left from inferInstance)
  exact ⟨A.unop, e⟩

private theorem coordinateTangent_changePresentation
    {A B : HopfAlgebraCategory k} (e : specGroup A ≅ G.val) (f : specGroup B ≅ G.val)
    (a : A ⟶ B) (ha : specGroupMap a ≫ e.hom = f.hom) (x : Lie k G.val) :
    (presentedTangent e x).val = (presentedTangent f x).val.comp a.hom.toAlgHom := by
  have hcomp : f.inv ≫ specGroupMap a = e.inv := by
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, ha, f.inv_hom_id, e.inv_hom_id]
  have hpoint : mapPointKernel (specGroupMap a) (mapPointKernel f.inv x) = mapPointKernel e.inv x := by
    rw [← (lieFunctoriality k).2.2, hcomp]
  have h := tangentPoint_natural a (mapPointKernel f.inv x)
  rw [hpoint] at h
  exact h

private theorem integrates_in_presentation
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [LieRing (Lie k G.val)] [LieRingModule (Lie k G.val) V]
    {B : HopfAlgebraCategory k} (f : specGroup B ≅ G.val) (h : Integrates G V) :
    ∃ σ : RightComodule k B V, AgreesWithCoaction f σ := by
  obtain ⟨A, e, ρ, hρ⟩ := h
  let F := hopfSpec (CommRingCat.of k)
  let a := ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage (f.hom ≫ e.inv)).unop
  have ha : specGroupMap a ≫ e.hom = f.hom := by
    change F.map ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage (f.hom ≫ e.inv)) ≫ e.hom = f.hom
    rw [Functor.FullyFaithful.map_preimage]
    simp
  let σ := restrictCoaction a ρ
  refine ⟨σ, fun x v => ?_⟩
  rw [← hρ x v]
  have hpoint := coordinateTangent_changePresentation e f a ha x
  simp only [differentiatedCoaction, evaluate, LinearMap.comp_apply,
    σ, restrictCoaction_coaction, ← LinearMap.lTensor_comp_apply]
  rw [hpoint]
  rfl

private theorem integrates_of_complement
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [LieRing (Lie k G.val)] [LieAlgebra k (Lie k G.val)]
    [LieRingModule (Lie k G.val) V] [LieModule k (Lie k G.val) V]
    {U W : LieSubmodule k (Lie k G.val) V} (h : IsCompl U W)
    (hU : Integrates G U) (hW : Integrates G W) :
    Integrates G V := by
  letI : LieRingModule (Lie k G.val) (U × W) :=
    { bracket := fun x v => (⁅x, v.1⁆, ⁅x, v.2⁆)
      add_lie := fun x y v => Prod.ext (add_lie x y v.1) (add_lie x y v.2)
      lie_add := fun x v w => Prod.ext (lie_add x v.1 w.1) (lie_add x v.2 w.2)
      leibniz_lie := fun x y v => Prod.ext (leibniz_lie x y v.1) (leibniz_lie x y v.2) }
  let e := Submodule.prodEquivOfIsCompl U.toSubmodule W.toSubmodule
    (LieSubmodule.isCompl_toSubmodule.mpr h)
  let d : (U × W) ≃ₗ⁅k, Lie k G.val⁆ V :=
    { e with
      map_lie' := by
        intro x uv
        change (⁅x, uv.1⁆ : U).val + (⁅x, uv.2⁆ : W).val =
          ⁅x, (uv.1 : V) + (uv.2 : V)⁆
        exact (lie_add ..).symm }
  obtain ⟨A, a, ρ, hρ⟩ := hU
  obtain ⟨σ, hσ⟩ := integrates_in_presentation a hW
  obtain ⟨τ, hf, hg⟩ := exists_directSumCoaction A ρ σ
  apply integrates_of_lieEquiv d.symm
  refine ⟨A, a, τ, fun x v => Prod.ext ?_ ?_⟩
  · exact (differentiatedCoaction_natural A τ ρ _ (LinearMap.fst k U W) hf v).trans (hρ x v.1)
  · exact (differentiatedCoaction_natural A τ σ _ (LinearMap.snd k U W) hg v).trans (hσ x v.2)

end Coactions

section Split

variable {k : Type u} [Field k] [CharZero k]

/-- Complete reducibility extends split integration from the simple modules
to all finite-dimensional Lie modules, including the zero module. -/
theorem integrates_of_split
    {G : AffineAlgebraicGroup k} (P : FlagLineBundle.OppositeBorelPair G)
    (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G)
    (s : IdentityLieStructure G.val) (t : IdentityLieStructure P.torus.group) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      [LieRingModule (Lie k G.val) V] [LieModule k (Lie k G.val) V], Integrates G V := by
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨hfin, hss⟩ := SemisimplyDifferentiated.lieSemisimple G hG s
  letI := hfin
  suffices h : ∀ n : ℕ, ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      [LieRingModule (Lie k G.val) V] [LieModule k (Lie k G.val) V],
      Module.finrank k V = n → Integrates G V from
    fun V _ _ _ _ _ => h (Module.finrank k V) V rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ _ _ hn
    by_cases hsub : Subsingleton V
    · letI := hsub
      obtain ⟨A, ⟨e⟩⟩ := coordinatePresentation G
      exact ⟨A, e, ⟨0, by simp, fun v => Subsingleton.elim _ v⟩,
        fun _ _ => Subsingleton.elim _ _⟩
    · letI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
      by_cases hirr : LieModule.IsIrreducible k (Lie k G.val) V
      · exact integrates_simple_of_split P hG hsc s t V hirr
      · have hproper : ∃ U : LieSubmodule k (Lie k G.val) V, U ≠ ⊥ ∧ U ≠ ⊤ := by
          by_contra! h
          exact hirr (LieModule.IsIrreducible.mk h)
        obtain ⟨U, hUbot, hUtop⟩ := hproper
        obtain ⟨W, hcompl⟩ := LieAlgebrasAndRepresentations.CompleteReducibility.invariant_complement
          k (Lie k G.val) V hss U
        have hWtop : W ≠ ⊤ := fun hW => hUbot <| by
          simpa [hW, disjoint_top] using hcompl.disjoint
        have lt_finrank (Z : LieSubmodule k (Lie k G.val) V) (hZ : Z ≠ ⊤) :
            Module.finrank k Z < n := hn ▸ Submodule.finrank_lt
              (mt (LieSubmodule.toSubmodule_eq_top Z).mp hZ)
        exact integrates_of_complement hcompl (ih _ (lt_finrank U hUtop) U rfl)
          (ih _ (lt_finrank W hWtop) W rfl)

end Split

section GeometricIntegration

open Specs.GeometricRadicals (GeometricGroup IsReductive)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots)

open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private splitBorelPair from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private rational_maximal_exists from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriExist
open private isTorus_iff_coordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private split_of_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private geometricallyMaximal_of_maximal_split from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers

private theorem exists_oppositePair {k : Type u} [Field k] (P : SplitBorelPair k) :
    Nonempty (FlagLineBundle.OppositeBorelPair P.G) := by
  obtain ⟨c, _, hc, _, hpos⟩ := (RootData.BorelsAndChambers.borelsThroughT
    P.G P.reductive P.T P.split P.maximal).1 P.B P.borel P.containsTorus
  let D := Classification.Pinning.attachedDatum P
  letI := D.comm
  have hpair (α : AbstractPairing.Root P.T) :
      pairing P.T.group α.val c⁻¹ = - pairing P.T.group α.val c := by
    rw [← D.datum.pairing_eq, ← D.datum.pairing_eq α.val c]
    change D.datum.rootDatum.toLinearMap (Additive.ofMul α.val) (- Additive.ofMul c) = _
    exact map_neg _ _
  have hneg : IsRegular P.T c⁻¹ := fun α => by rw [hpair]; exact neg_ne_zero.mpr (hc α)
  obtain ⟨E⟩ := CocharacterDynamics.existsLimitDecomposition P.G (c⁻¹ ≫ P.T.inclusion)
  obtain ⟨_, hB, hTB, hroots, _⟩ := RootData.BorelsAndChambers.regularCocharacterBorel
    P.G P.reductive P.T P.split P.maximal c⁻¹ hneg E
  refine ⟨⟨P.T, P.B, E.parabolic, P.reductive, P.split, P.maximal, P.borel, hB,
    P.containsTorus, hTB, ?_⟩⟩
  change subgroupRoots P.T E.parabolic = (subgroupRoots P.T P.B)ᶜ
  rw [hroots, hpos]
  ext α
  change 0 < pairing P.T.group α.val c⁻¹ ↔ ¬ 0 < pairing P.T.group α.val c
  rw [hpair]
  have hn := hc α
  omega

private theorem integrates_of_split_model
    {k : Type u} [Field k] [CharZero k] {G : AffineAlgebraicGroup k}
    (P : SplitBorelPair k) (hH : IsSemisimple P.G)
    (hsc : GeometricallySimplyConnected P.G) (e : P.G.val ≅ G.val)
    (s : IdentityLieStructure G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      [LieRingModule (Lie k G.val) V] [LieModule k (Lie k G.val) V], Integrates G V := by
  letI := s.lieRing
  letI := s.lieAlgebra
  intro V _ _ _ _ _
  obtain ⟨P'⟩ := exists_oppositePair P
  obtain ⟨s'⟩ := identityLieBracket k P.G
  obtain ⟨t'⟩ := identityLieBracket k (closedSubgroupAlgebraicGroup P'.torus)
  letI := s'.lieRing
  letI := s'.lieAlgebra
  letI := P.G.property.1
  letI := G.property.1
  obtain ⟨d, hd⟩ := identityDifferentialLieHom k P.G.val G.val e.hom s' s
  letI := LieRingModule.compLieHom V d
  letI := LieModule.compLieHom V d
  obtain ⟨A, a, ρ, hρ⟩ := integrates_of_split P' hH hsc s' t' V
  refine ⟨A, a ≪≫ e, ρ, fun x v => ?_⟩
  have heq : (a ≪≫ e).inv = e.inv ≫ a.inv := rfl
  change differentiatedCoaction A ρ (tangentPointOfLie A (mapPointKernel (a ≪≫ e).inv x)) v =
    ⁅x, v⁆
  rw [heq, (lieFunctoriality k).2.2]
  refine (hρ _ _).trans ?_
  change ⁅d (mapPointKernel e.inv x), v⁆ = ⁅x, v⁆
  rw [hd, ← (lieFunctoriality k).2.2, e.inv_hom_id, (lieFunctoriality k).2.1]

/-- Over the algebraic closure the split simply connected cover is an
isomorphism by geometric simple connectedness of the original group. -/
private theorem exists_geometric_split_model
    {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G) :
    ∃ P : SplitBorelPair (AlgebraicClosure k),
      IsSemisimple P.G ∧ GeometricallySimplyConnected P.G ∧
        Nonempty (P.G.val ≅ (GeometricGroup G).val) := by
  let K := AlgebraicClosure k
  let H := GeometricGroup G
  have hH : IsSemisimple H :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := K) G hG.1 hG.2.1).mpr hG
  let hr := reductive_of_semisimple H hH
  obtain ⟨T, hT⟩ := rational_maximal_exists H
  have hs := split_of_torus ((isTorus_iff_coordinates (closedSubgroupAlgebraicGroup T)).mp hT.1)
  let P := splitBorelPair H hr T hs (geometricallyMaximal_of_maximal_split H T hT hs)
  let D := Classification.Pinning.attachedDatum P
  letI := D.comm
  obtain ⟨Q, _, f, _, hQ, hQsc, hf, _⟩ := Classification.SimplyConnectedLattice.splitCover
    H hH P.T P.split P.maximal D.datum
  letI : IsIso f := hsc Q.G hQ f hf
  exact ⟨Q, hQ, hQsc, ⟨asIso f⟩⟩

end GeometricIntegration

set_option maxHeartbeats 850000

section GaloisCoefficients

open Coalgebra RationalRepresentations

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The canonical Galois conjugation of a scalar extension, as a map over the
ground field. -/
private def conjugateTensor {M : Type u} [AddCommGroup M] [Module k M]
    (σ : K ≃ₐ[k] K) : K ⊗[k] M →ₗ[k] K ⊗[k] M :=
  TensorProduct.map σ.toLinearEquiv.toLinearMap LinearMap.id

@[simp] private theorem conjugateTensor_tmul {M : Type u} [AddCommGroup M] [Module k M]
    (σ : K ≃ₐ[k] K) (a : K) (m : M) :
    conjugateTensor σ (a ⊗ₜ[k] m) = σ a ⊗ₜ[k] m :=
  rfl

private theorem baseChangeCoord_conjugate {M : Type u} [AddCommGroup M] [Module k M]
    {I : Type u} (b : Module.Basis I k M) (i : I) (σ : K ≃ₐ[k] K) (x : K ⊗[k] M) :
    (b.baseChange K).repr (conjugateTensor σ x) i = σ ((b.baseChange K).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp [Algebra.smul_def]
  | add x y hx hy => simp [hx, hy]

/-- The fixed tensors for the action on the field factor are the images of
the original vectors. This works in arbitrary dimension and for infinite
Galois extensions, including an algebraic closure in characteristic zero. -/
private theorem exists_of_fixedTensor [IsGalois k K] {M : Type u} [AddCommGroup M] [Module k M]
    (x : K ⊗[k] M) (h : ∀ σ : K ≃ₐ[k] K, conjugateTensor σ x = x) :
    ∃ m : M, (1 : K) ⊗ₜ[k] m = x := by
  classical
  let b := Module.Basis.ofVectorSpace k M
  let c := (b.baseChange K).repr x
  have hc (i : c.support) : ∃ a : k, algebraMap k K a = c i := by
    apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
    intro σ
    rw [← baseChangeCoord_conjugate, h σ]
  choose a ha using hc
  refine ⟨∑ i : c.support, a i • b i, ?_⟩
  calc
    (1 : K) ⊗ₜ[k] (∑ i : c.support, a i • b i) =
        ∑ i : c.support, c i • b.baseChange K i := by
      rw [TensorProduct.tmul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Module.Basis.baseChange_apply, TensorProduct.tmul_smul, ← ha i]
      simp
    _ = x := by
      exact (Finset.sum_coe_sort c.support (fun i => c i • b.baseChange K i)).trans ((b.baseChange K).linearCombination_repr x)

variable (A : HopfAlgebraCategory k)

private abbrev twoTensorComparison :=
  TensorProduct.AlgebraTensorModule.distribBaseChange k K A A

private theorem comul_scalarExtension (z : K ⊗[k] A) :
    (twoTensorComparison (K := K) A).symm
      (comul (R := K) (A := scalarExtension A K) z) =
        (comul (R := k) (A := A)).baseChange K z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul a b =>
    rw [LinearMap.baseChange_tmul, TensorProduct.comul_tmul]
    change (twoTensorComparison (K := K) A).symm
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm k K k K K K A A
        ((1 ⊗ₜ[K] a) ⊗ₜ[k] comul b)) = a ⊗ₜ[k] comul b
    generalize comul (R := k) b = w
    induction w using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul x y => simp

private theorem conjugateTensor_comul (σ : K ≃ₐ[k] K) (z : K ⊗[k] A) :
    (twoTensorComparison (K := K) A).symm
      (comul (R := K) (A := scalarExtension A K) (conjugateTensor σ z)) =
        conjugateTensor σ ((twoTensorComparison (K := K) A).symm
          (comul (R := K) (A := scalarExtension A K) z)) := by
  rw [comul_scalarExtension A (conjugateTensor σ z), comul_scalarExtension A z]
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul a b => simp

private theorem conjugateTensor_pair (σ : K ≃ₐ[k] K) (x y : K ⊗[k] A) :
    (twoTensorComparison (K := K) A).symm
      (conjugateTensor σ x ⊗ₜ[K] conjugateTensor σ y) =
        conjugateTensor σ ((twoTensorComparison (K := K) A).symm (x ⊗ₜ[K] y)) := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp [TensorProduct.add_tmul, hx, hz]
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, TensorProduct.tmul_add, hy, hz]
    | tmul c d => simp

private theorem conjugateTensor_counit (σ : K ≃ₐ[k] K) (z : K ⊗[k] A) :
    counit (R := K) (A := scalarExtension A K) (conjugateTensor σ z) =
      σ (counit (R := K) (A := scalarExtension A K) z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul a b => simp [Algebra.smul_def]

private theorem conjugateCoactionMatrix {I : Type u} [Fintype I] [DecidableEq I]
    {M : Matrix I I (scalarExtension A K)} (h : IsCoactionMatrix (scalarExtension A K) M)
    (σ : K ≃ₐ[k] K) :
    IsCoactionMatrix (scalarExtension A K) (fun i j => conjugateTensor σ (M i j)) := by
  constructor
  · intro i j
    apply (twoTensorComparison (K := K) A).symm.injective
    rw [conjugateTensor_comul, h.comul]
    simp only [map_sum, conjugateTensor_pair]
  · intro i j
    rw [conjugateTensor_counit, h.counit]
    simp [Matrix.one_apply]

private theorem descendCoactionMatrix [IsGalois k K]
    {I : Type u} [Fintype I] [DecidableEq I]
    {M : Matrix I I (scalarExtension A K)} (hM : IsCoactionMatrix (scalarExtension A K) M)
    (h : ∀ (σ : K ≃ₐ[k] K) i j, conjugateTensor σ (M i j) = M i j) :
    ∃ N : Matrix I I A, IsCoactionMatrix A N ∧ ∀ i j, (1 : K) ⊗ₜ[k] N i j = M i j := by
  classical
  have hentry (i j : I) := exists_of_fixedTensor (M i j) (fun σ => h σ i j)
  choose N hN using hentry
  refine ⟨N, ⟨?_, ?_⟩, hN⟩
  · intro i j
    have hK := congrArg (twoTensorComparison (K := K) A).symm (hM.comul i j)
    simp_rw [← hN] at hK
    have hC := comul_scalarExtension (K := K) A ((1 : K) ⊗ₜ[k] N i j)
    change (twoTensorComparison (K := K) A).symm
      (comul (R := K) (A := scalarExtension A K) ((1 : K) ⊗ₜ[k] N i j)) = _ at hK
    rw [hC] at hK
    simp only [LinearMap.baseChange_tmul, map_sum,
      TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul, one_mul,
      ← TensorProduct.tmul_sum] at hK
    have hz : (1 : K) ⊗ₜ[k] (comul (R := k) (N i j) - ∑ l, N i l ⊗ₜ[k] N l j) = 0 :=
      by rw [TensorProduct.tmul_sub, hK, sub_self]
    exact sub_eq_zero.mp ((Module.FaithfullyFlat.one_tmul_eq_zero_iff k (A ⊗[k] A) _).mp hz)
  · intro i j
    have hK := hM.counit i j
    rw [← hN, TensorProduct.counit_tmul, Bialgebra.counit_one] at hK
    apply (algebraMap k K).injective
    simpa [Algebra.smul_def, Matrix.one_apply, apply_ite] using hK

end GaloisCoefficients

section TangentCoefficients

open Coalgebra WithConv RationalRepresentations

open private mapDualKernel_scale dualKernelIso snd_conv from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private def presentedKernel {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val) :
    PointKernel G.val →+ DualKernel (convolutionPoints A) :=
  (dualKernelIso (hopfSpecPointIso A)).symm.toAddMonoidHom.comp (mapPointKernel e.inv)

private abbrev tangentCoefficient {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val)
    (x : Lie k G.val) (a : A) : k := ((presentedTangent e x).val a).snd

private theorem tangentCoefficient_add {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val)
    (s : IdentityLieStructure G.val) (x y : Lie k G.val) (a : A) :
    tangentCoefficient e (s.lieRing.toAddGroup.toAdd.add x y) a =
      tangentCoefficient e x a + tangentCoefficient e y a := by
  have h := congrArg (fun law : AddGroup (PointKernel G.val) => law.toAdd.add x y) s.group_law
  rw [h]
  let d := presentedKernel e
  change (((hopfKernelLifts A) (d (_ + _))).val a).snd = _
  rw [map_add]
  exact snd_conv ((hopfKernelLifts A) (d x)) ((hopfKernelLifts A) (d y)) a

private theorem tangentCoefficient_smul {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val)
    (s : IdentityLieStructure G.val) (c : k) (x : Lie k G.val) (a : A) :
    tangentCoefficient e
      (s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul.smul c x) a =
      c • tangentCoefficient e x a := by
  rw [s.scalar_law]
  let F := hopfSpecPointIso A
  change (((hopfKernelLifts A) (mapDualKernel F.inv
    (mapPointKernel e.inv (scalePointKernel G.val c x)))).val a).snd = _
  rw [mapDualKernel_scale, mapDualKernel_scale]
  change (dualNumberScale c ((presentedTangent e x).val a)).snd = _
  rw [dualNumberScale, TrivSqZeroExt.snd_map]
  rfl

variable {V I : Type u} [AddCommGroup V] [Module k V] [Fintype I] [DecidableEq I]

private theorem differentiatedCoaction_entry
    (A : HopfAlgebraCategory k) (b : Module.Basis I k V) (ρ : RightComodule k A V)
    (x : HopfTangentPoint A) (i j : I) :
    b.coord i (differentiatedCoaction A ρ x (b j)) = (x.val (coefficients A b ρ i j)).snd := by
  simp only [differentiatedCoaction, evaluate, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [coaction_apply_basis]
  simp [map_sum, LinearMap.lTensor_tmul, Module.Basis.coord_apply, Finsupp.single_apply]

end TangentCoefficients

section ScalarExtension

open Specs.Unipotent (baseChangedAlgebraicGroup)
open RationalRepresentations

open private point_of_presentedTangent from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.RationalHighestWeightComparison

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem baseChangePresentation
    (G : AffineAlgebraicGroup k) {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val)
    (s : IdentityLieStructure G.val) (sK : IdentityLieStructure (baseChangedAlgebraicGroup K G).val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    letI := sK.lieRing
    letI := sK.lieAlgebra
    ∃ (d : (K ⊗[k] Lie k G.val) ≃ₗ⁅K⁆ Lie K (baseChangedAlgebraicGroup K G).val)
      (eK : specGroup (scalarExtension A K) ≅ (baseChangedAlgebraicGroup K G).val),
      ∀ (x : Lie k G.val) (a : A),
        tangentCoefficient eK (d (1 ⊗ₜ[k] x)) (1 ⊗ₜ[k] a) =
          algebraMap k K (tangentCoefficient e x a) := by
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := sK.lieRing
  letI := sK.lieAlgebra
  obtain ⟨_, hd⟩ := identityLieBracketBaseChange k K G
  obtain ⟨d, hgen⟩ := hd s sK
  obtain ⟨j, hj⟩ := hopfSpectrumBaseChange k K A
  let H := baseChangedAlgebraicGroup K G
  let eK : specGroup (scalarExtension A K) ≅ H.val := j ≪≫ (groupBaseChange k K).mapIso e
  refine ⟨d, eK, fun x a => ?_⟩
  let R := CommAlgCat.of K (DualNumber K)
  let f := (presentedTangent e x).val
  let g := (presentedTangent (G := H) eK (d (1 ⊗ₜ[k] x))).val
  let t : Points ((baseChange k K).obj (specGroup A).X) R :=
    Spec.mapMulEquiv (R := K) (S := scalarExtension A K) (T := R) (WithConv.toConv g) ≫
      j.hom.hom.hom
  have ht : (baseChangePoint k K (specGroup A).X R t).left =
      Spec.map (CommRingCat.ofHom (restrictCoordinateRingPoint K
        (R := R) g)) := hj R g
  have hp := point_of_presentedTangent (G := H) eK (d (1 ⊗ₜ[k] x))
  change t ≫ (baseChange k K).map e.hom.hom.hom = (d (1 ⊗ₜ[k] x)).toMul.val at hp
  have hleft := (baseChangePointsSchemeNaturality k K e.hom.hom.hom R t).symm
  rw [hp, hgen] at hleft
  have hl := congrArg (fun h => h.left) hleft
  change (baseChangePoint k K (specGroup A).X R t).left ≫ e.hom.hom.hom.left =
    ((mapPoints (extendDualNumber K) x.toMul.val).left) at hl
  have hx := congrArg (fun h => h.left) (point_of_presentedTangent e x)
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ e.hom.hom.hom.left = x.toMul.val.left at hx
  change _ = ((testSpec k).map (extendDualNumber K).op).left ≫ x.toMul.val.left at hl
  rw [ht, ← hx] at hl
  letI : IsIso e.hom.hom.hom.left :=
    ((Grp.forget (SchemeOver k)) ⋙ Over.forget (Spec (CommRingCat.of k))).map_isIso e.hom
  have hr := (cancel_mono e.hom.hom.hom.left).mp
    (hl.trans (Category.assoc _ _ _).symm)
  let b : A →+* DualNumber K := (dualNumberCoefficients K).comp f.toRingHom
  have heq : CommRingCat.ofHom (restrictCoordinateRingPoint K (R := R) g) =
      CommRingCat.ofHom b := by
    apply Spec.map_injective
    change _ = Spec.map (CommRingCat.ofHom (dualNumberCoefficients K)) ≫
      Spec.map (CommRingCat.ofHom f.toRingHom) at hr
    rw [← Spec.map_comp] at hr
    exact hr
  exact congrArg (fun l => (l.hom a).snd) heq

private theorem tangentCoefficient_conjugate
    {G : AffineAlgebraicGroup k} {A : HopfAlgebraCategory k}
    (e : specGroup A ≅ G.val)
    {H : AffineAlgebraicGroup K} (eK : specGroup (scalarExtension A K) ≅ H.val)
    (x : Lie k G.val) (y : Lie K H.val)
    (h : ∀ a : A, tangentCoefficient eK y (1 ⊗ₜ[k] a) =
      algebraMap k K (tangentCoefficient e x a))
    (σ : K ≃ₐ[k] K) (z : K ⊗[k] A) :
    tangentCoefficient eK y (conjugateTensor σ z) = σ (tangentCoefficient eK y z) := by
  let f := (presentedTangent eK y).val
  have ht (a : K) (b : A) :
      tangentCoefficient eK y (a ⊗ₜ[k] b) = a * algebraMap k K (tangentCoefficient e x b) := by
    rw [TensorProduct.tmul_eq_smul_one_tmul]
    change (f.toLinearMap (a • (1 ⊗ₜ[k] b))).snd = _
    rw [f.toLinearMap.map_smul, TrivSqZeroExt.snd_smul]
    exact congrArg (a * ·) (h b)
  induction z using TensorProduct.inductionOn with
  | tmul a m => simp [ht]
  | add a b ha hb =>
    change (f (conjugateTensor σ (a + b))).snd = σ ((f (a + b)).snd)
    simp only [map_add, TrivSqZeroExt.snd_add]
    exact congrArg₂ (· + ·) ha hb

end ScalarExtension

section Descent

open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.RationalHighestWeightComparison (AgreesWithCoaction)
open RationalRepresentations

variable {k K : Type u} [Field k] [Field K] [CharZero K] [Algebra k K]
  [IsGalois k K]

omit [IsGalois k K] in
private theorem fixedIntegrationCoefficients
    (G : AffineAlgebraicGroup k) (H : AffineAlgebraicGroup K) [ConnectedSpace H.val.X.left]
    (s : IdentityLieStructure G.val) (t : IdentityLieStructure H.val)
    {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val)
    (eK : specGroup (scalarExtension A K) ≅ H.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    letI := t.lieRing
    letI := t.lieAlgebra
    ∀ (d : (K ⊗[k] Lie k G.val) ≃ₗ⁅K⁆ Lie K H.val)
      (_ : ∀ (x : Lie k G.val) (a : A),
        tangentCoefficient eK (d (1 ⊗ₜ[k] x)) (1 ⊗ₜ[k] a) =
          algebraMap k K (tangentCoefficient e x a))
      {I V : Type u} [Fintype I] [DecidableEq I] [AddCommGroup V] [Module k V]
      (b : Module.Basis I k V)
      (ρ : RightComodule K (scalarExtension A K) (K ⊗[k] V)),
      (∀ (x : Lie k G.val) (i j : I),
        tangentCoefficient eK (d (1 ⊗ₜ[k] x)) (coefficients _ (b.baseChange K) ρ i j)
          ∈ Set.range (algebraMap k K)) →
      ∀ (σ : K ≃ₐ[k] K) (i j : I),
        conjugateTensor σ (coefficients _ (b.baseChange K) ρ i j) =
          coefficients _ (b.baseChange K) ρ i j := by
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := t.lieRing
  letI := t.lieAlgebra
  intro d hd I V _ _ _ _ b ρ hρ σ
  let B := scalarExtension A K
  let bK := b.baseChange K
  letI : FiniteDimensional K (K ⊗[k] V) := Module.Finite.of_basis bK
  let M := coefficients B bK ρ
  let M' : Matrix I I B := fun i j => conjugateTensor σ (M i j)
  have hM' : IsCoactionMatrix B M' :=
    conjugateCoactionMatrix A (coefficients_isCoactionMatrix B bK ρ) σ
  let τ := coactionOfMatrix B bK M' hM'
  have hτ : coefficients B bK τ = M' := coefficients_coactionOfMatrix B bK M' hM'
  have hgen (x : Lie k G.val) (i j : I) :
      tangentCoefficient eK (d (1 ⊗ₜ[k] x)) (M' i j) =
        tangentCoefficient eK (d (1 ⊗ₜ[k] x)) (M i j) := by
    change tangentCoefficient eK (d (1 ⊗ₜ[k] x)) (conjugateTensor σ (M i j)) = _
    rw [tangentCoefficient_conjugate e eK x _ (hd x)]
    obtain ⟨a, ha⟩ := hρ x i j
    change algebraMap k K a = tangentCoefficient eK (d (1 ⊗ₜ[k] x)) (M i j) at ha
    rw [← ha, σ.commutes]
  have hfull (x : Lie K H.val) (i j : I) :
      tangentCoefficient eK x (M' i j) = tangentCoefficient eK x (M i j) := by
    obtain ⟨z, rfl⟩ := d.surjective x
    induction z using TensorProduct.inductionOn with
    | tmul a y =>
      change tangentCoefficient eK (d.toLinearEquiv (a ⊗ₜ[k] y)) (M' i j) =
        tangentCoefficient eK (d.toLinearEquiv (a ⊗ₜ[k] y)) (M i j)
      have hmap : d.toLinearEquiv (a ⊗ₜ[k] y) =
          t.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul.smul a
            (d (1 ⊗ₜ[k] y)) := by
        rw [TensorProduct.tmul_eq_smul_one_tmul, d.toLinearEquiv.map_smul]
        rfl
      rw [hmap, tangentCoefficient_smul eK t, tangentCoefficient_smul eK t, hgen]
    | add y z hy hz =>
      change tangentCoefficient eK (d.toLinearEquiv (y + z)) (M' i j) =
        tangentCoefficient eK (d.toLinearEquiv (y + z)) (M i j)
      have hmap : d.toLinearEquiv (y + z) = t.lieRing.toAddGroup.toAdd.add (d y) (d z) :=
        d.toLinearEquiv.map_add y z
      rw [hmap, tangentCoefficient_add eK t, tangentCoefficient_add eK t]
      exact congrArg₂ (· + ·) hy hz
  have hint (x : Lie K H.val) :
      differentiatedCoaction B τ (presentedTangent eK x) =
        differentiatedCoaction B ρ (presentedTangent eK x) := by
    apply bK.ext
    intro j
    apply bK.repr.injective
    ext i
    change bK.coord i (differentiatedCoaction B τ (presentedTangent eK x) (bK j)) =
      bK.coord i (differentiatedCoaction B ρ (presentedTangent eK x) (bK j))
    rw [differentiatedCoaction_entry, differentiatedCoaction_entry, hτ]
    exact hfull x i j
  have h := (fullyFaithfulDifferentiationOfPresentation H eK τ ρ LinearMap.id).mpr
    (fun x => by rw [hint, LinearMap.id_comp, LinearMap.comp_id])
  have hc : τ.coaction = ρ.coaction := by
    simpa only [IsEquivariant, LinearMap.rTensor_id, LinearMap.id_comp, LinearMap.comp_id] using h
  intro i j
  have hh := congrArg (fun f : (K ⊗[k] V) →ₗ[K] (K ⊗[k] V) ⊗[K] B =>
    tensorCoordinate bK i (f (bK j))) hc
  change coefficients B bK τ i j = M i j at hh
  rw [hτ] at hh
  exact hh

private theorem descendIntegratedModule
    (G : AffineAlgebraicGroup k)
    (s : IdentityLieStructure G.val) (t : IdentityLieStructure (baseChangedAlgebraicGroup K G).val)
    [ConnectedSpace (baseChangedAlgebraicGroup K G).val.X.left] :
    letI := s.lieRing
    letI := s.lieAlgebra
    letI := t.lieRing
    letI := t.lieAlgebra
    ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      [LieRingModule (Lie k G.val) V] [LieModule k (Lie k G.val) V],
    (∀ (d : (K ⊗[k] Lie k G.val) ≃ₗ⁅K⁆ Lie K (baseChangedAlgebraicGroup K G).val),
      letI := LieRingModule.compLieHom (K ⊗[k] V) d.symm.toLieHom
      Integrates (baseChangedAlgebraicGroup K G) (K ⊗[k] V)) →
    Integrates G V := by
  classical
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := t.lieRing
  letI := t.lieAlgebra
  intro V _ _ _ _ _ hInt
  obtain ⟨A, ⟨e⟩⟩ := coordinatePresentation G
  let H := baseChangedAlgebraicGroup K G
  let B := scalarExtension A K
  obtain ⟨d, eK, hd⟩ := baseChangePresentation (K := K) G e s t
  letI := LieRingModule.compLieHom (K ⊗[k] V) d.symm.toLieHom
  let b := Module.Basis.ofVectorSpace k V
  let bK := b.baseChange K
  letI : FiniteDimensional K (K ⊗[k] V) := Module.Finite.of_basis bK
  obtain ⟨ρ, hρ⟩ := integrates_in_presentation eK (hInt d)
  let M := coefficients B bK ρ
  have hcoord (x : Lie k G.val) (i j : _) :
      tangentCoefficient eK (d (1 ⊗ₜ[k] x)) (M i j) =
        algebraMap k K (b.coord i ⁅x, b j⁆) := by
    have hc := congrArg (bK.coord i) (hρ (d (1 ⊗ₜ[k] x)) (bK j))
    rw [differentiatedCoaction_entry] at hc
    refine hc.trans ?_
    change bK.coord i ⁅d.symm (d (1 ⊗ₜ[k] x)), bK j⁆ = _
    rw [d.symm_apply_apply, show bK j = 1 ⊗ₜ[k] b j from Module.Basis.baseChange_apply (S := K) b j,
      LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
    change (b.baseChange K).repr (1 ⊗ₜ[k] ⁅x, b j⁆) i = _
    rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one, Module.Basis.coord_apply]
  have hfix := fixedIntegrationCoefficients G H s t e eK d hd b ρ
    (fun x i j => ⟨_, (hcoord x i j).symm⟩)
  obtain ⟨N, hN, hsrc⟩ := descendCoactionMatrix A (coefficients_isCoactionMatrix B bK ρ) hfix
  let δ := coactionOfMatrix A b N hN
  have hδ := coefficients_coactionOfMatrix A b N hN
  refine ⟨A, e, δ, fun x v => ?_⟩
  have hder : differentiatedCoaction A δ (presentedTangent e x) = LieModule.toEnd k _ V x := by
    apply b.ext
    intro j
    apply b.repr.injective
    ext i
    change b.coord i (differentiatedCoaction A δ (presentedTangent e x) (b j)) =
      b.coord i ⁅x, b j⁆
    rw [differentiatedCoaction_entry, hδ]
    apply (algebraMap k K).injective
    rw [← hd x, hsrc, hcoord]
  exact LinearMap.congr_fun hder v

end Descent

open Specs.GeometricRadicals (GeometricGroup)
open Specs.Unipotent (baseChangedAlgebraicGroup)

/-- A finite-dimensional representation of the identity Lie algebra of a
simply connected semisimple group in characteristic zero integrates over the
original field. -/
theorem essentialSurjectivity : EssentialSurjectivity.{u} := by
  intro k _ _ G hG hsc s
  letI := s.lieRing
  letI := s.lieAlgebra
  intro V _ _ _ _ _
  let K := AlgebraicClosure k
  let H := GeometricGroup G
  obtain ⟨⟨t₀⟩, _⟩ := identityLieBracketBaseChange k K G
  let t : IdentityLieStructure (baseChangedAlgebraicGroup K G).val := t₀
  letI : LieRing (Lie K (baseChangedAlgebraicGroup K G).val) := t.lieRing
  letI : LieAlgebra K (Lie K (baseChangedAlgebraicGroup K G).val) := t.lieAlgebra
  have hH : IsSemisimple H :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := K) G hG.1 hG.2.1).mpr hG
  letI : GeometricallyConnected (baseChangedAlgebraicGroup K G).val.X.hom := hH.2.1
  letI : ConnectedSpace (baseChangedAlgebraicGroup K G).val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton
      (f := (baseChangedAlgebraicGroup K G).val.X.hom)
  apply descendIntegratedModule (K := K) G s t V
  intro d
  letI := LieRingModule.compLieHom (K ⊗[k] V) d.symm.toLieHom
  letI := LieModule.compLieHom (K ⊗[k] V) d.symm.toLieHom
  obtain ⟨P, hP, hPsc, ⟨e⟩⟩ := exists_geometric_split_model G hG hsc
  exact integrates_of_split_model (G := H) P hP hPsc e t (K ⊗[k] V)

/-- Differentiation and the integral lattice, with the positive-characteristic
Frobenius example. -/
theorem lieIntegration : Statement.{u} :=
  ⟨fullyFaithfulDifferentiationOfPresentation, essentialSurjectivity,
    SplitLieIntegration.splitIntegration, FrobeniusDifferential.relativeFrobeniusDifferential,
    FrobeniusDifferential.splitSL2Example⟩

end

end LinearAlgebraicGroups.Representation.LieIntegration
