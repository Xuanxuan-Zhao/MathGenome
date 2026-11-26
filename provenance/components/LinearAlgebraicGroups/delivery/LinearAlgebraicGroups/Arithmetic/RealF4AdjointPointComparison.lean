import Specs.LinearAlgebraicGroups.Arithmetic.RealF4AdjointPointComparison
import LinearAlgebraicGroups.Arithmetic.AdjointLieAutomorphisms
import LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart
import LinearAlgebraicGroups.Reductive.RadicalBaseChange
import LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import LinearAlgebraicGroups.Descent.AutomorphismSequence
import Mathlib.Analysis.Complex.Polynomial.Basic
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealFormsConjugations
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LieAlgebrasAndRepresentations.RealForms
open scoped TensorProduct Matrix

noncomputable section

namespace LinearAlgebraicGroups.Arithmetic.RealF4AdjointPointComparison

open LinearAlgebraicGroups.Specs
open Specs.GeometricRadicals (IsSemisimple)
open Specs.IntegralModels (MatrixRealization)
open Specs.RealF4AdjointPointComparison (ComplexTangentData complexGroup coordinateTopology
  fixedAutomorphisms)
open AdelicGroups (PointsIn asMatrix)

universe u v w

open Module RootData
open Specs.AbsoluteDynkinTypes (HasDynkinType PreservesCartan)
open Specs.Pinning (AttachedDatum SplitBorelPair BasedIso)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.style.haveILetI false

/-- A full-rank F₄ coroot lattice equals the ambient cocharacter lattice. -/
theorem f4_coroot_span_eq_top
    {I : Type u} {X : Type v} {Y : Type w} [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : _root_.RootDatum I X Y) (B : P.Base)
    (hfull : finrank ℤ (Submodule.span ℤ (Set.range P.coroot)) = finrank ℤ Y)
    (hF : HasDynkinType (integralCartan P B) .F4) :
    Submodule.span ℤ (Set.range P.coroot) = ⊤ := by
  classical
  obtain ⟨e, he⟩ := hF
  change B.support ≃ Fin 4 at e
  change ∀ i j, integralCartan P B i j = CartanMatrix.F₄ (e i) (e j) at he
  let a (j : Fin 4) := P.root (e.symm j).val
  let c (j : Fin 4) := P.coroot (e.symm j).val
  let f : Y →ₗ[ℤ] (Fin 4 → ℤ) := LinearMap.pi fun j => P.toLinearMap (a j)
  have hcartan (i j : Fin 4) : f (c i) j = CartanMatrix.F₄ i j := by
    change integralCartan P B (e.symm i) (e.symm j) = _
    simpa only [Equiv.apply_symm_apply] using he (e.symm i) (e.symm j)
  have hsum (u : Fin 4 → ℤ) : f (∑ i, u i • c i) = u ᵥ* CartanMatrix.F₄ := by
    rw [map_sum, Matrix.vecMul_eq_sum]
    simp only [map_smul, show ∀ i, f (c i) = CartanMatrix.F₄ i from fun i => funext (hcartan i)]
  let C : Matrix (Fin 4) (Fin 4) ℤ := CartanMatrix.F₄
  have hC : IsUnit C.det := CartanMatrix.F₄_det ▸ isUnit_one
  have hf : Function.Surjective f := by
    intro z
    refine ⟨∑ i, (z ᵥ* C⁻¹) i • c i, ?_⟩
    rw [hsum]
    change (z ᵥ* C⁻¹) ᵥ* C = z
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hC, Matrix.vecMul_one]
  have hY : finrank ℤ Y = 4 := by
    have hset : Set.range c = P.coroot '' (B.support : Set I) := by
      ext y
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨_, (e.symm j).property, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨e ⟨j, hj⟩, congrArg (fun i : B.support => P.coroot i.val) (e.symm_apply_apply ⟨j,hj⟩)⟩
    rw [← hfull, ← B.span_int_coroot_support, ← hset]
    have hind : LinearIndependent ℤ c := B.linearIndepOn_coroot.comp e.symm e.symm.injective
    rw [finrank_span_eq_card hind, Fintype.card_fin]
  have hker : f.ker = ⊥ := by
    have hr : (⊤ : Submodule ℤ Y).map f = ⊤ := by
      rw [Submodule.map_top, LinearMap.range_eq_top]
      exact hf
    have hle : finrank ℤ (⊤ : Submodule ℤ Y) ≤ finrank ℤ ((⊤ : Submodule ℤ Y).map f) := by
      rw [hr, finrank_top, finrank_top, hY, finrank_fin_fun]
    simpa using Submodule.disjoint_ker_of_finrank_le f hle
  apply eq_top_iff.mpr
  intro y _
  let z := f y ᵥ* C⁻¹
  have hz : f (∑ i, z i • c i) = f y := by
    rw [hsum]
    change (f y ᵥ* C⁻¹) ᵥ* C = f y
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hC, Matrix.vecMul_one]
  rw [← (LinearMap.ker_eq_bot.mp hker) hz]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- In a full-rank root datum of type F₄ the roots generate the entire
character lattice. This is the character-lattice counterpart of the coroot
span calculation. -/
theorem f4_root_span_eq_top
    {I : Type u} {X : Type v} {Y : Type w} [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : _root_.RootDatum I X Y) (B : P.Base)
    (hfull : finrank ℤ (Submodule.span ℤ (Set.range P.coroot)) = finrank ℤ Y)
    (hF : HasDynkinType (integralCartan P B) .F4) :
    Submodule.span ℤ (Set.range P.root) = ⊤ := by
  classical
  have hcoroot := f4_coroot_span_eq_top P B hfull hF
  obtain ⟨e, he⟩ := hF
  change B.support ≃ Fin 4 at e
  change ∀ i j, integralCartan P B i j = CartanMatrix.F₄ (e i) (e j) at he
  let a (j : Fin 4) := P.root (e.symm j).val
  let c (j : Fin 4) := P.coroot (e.symm j).val
  let f : X →ₗ[ℤ] (Fin 4 → ℤ) := LinearMap.pi fun i => P.toLinearMap.flip (c i)
  have hc (i j : Fin 4) : f (a j) i = CartanMatrix.F₄ i j := by
    change integralCartan P B (e.symm i) (e.symm j) = _
    simpa only [Equiv.apply_symm_apply] using he (e.symm i) (e.symm j)
  have hsum (z : Fin 4 → ℤ) : f (∑ j, z j • a j) = CartanMatrix.F₄ *ᵥ z := by
    ext i
    rw [map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc, Matrix.mulVec,
      dotProduct, mul_comm]
  have hC : IsUnit CartanMatrix.F₄.det := CartanMatrix.F₄_det ▸ isUnit_one
  apply eq_top_iff.mpr
  intro x _
  let z := CartanMatrix.F₄⁻¹ *ᵥ f x
  have hz : f (∑ j, z j • a j) = f x := by
    rw [hsum]
    change CartanMatrix.F₄ *ᵥ (CartanMatrix.F₄⁻¹ *ᵥ f x) = f x
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hC, Matrix.one_mulVec]
  have hinj : Function.Injective f := by
    intro x y hxy
    apply P.toPerfPair.injective
    apply LinearMap.ext_on (s := P.coroot '' (B.support : Set I)) (by
      rw [B.span_int_coroot_support, hcoroot])
    rintro _ ⟨i, hi, rfl⟩
    have h := congrFun hxy (e ⟨i, hi⟩)
    change P.toLinearMap x (c (e ⟨i, hi⟩)) = P.toLinearMap y (c (e ⟨i, hi⟩)) at h
    change P.toLinearMap x (P.coroot i) = P.toLinearMap y (P.coroot i)
    simpa only [c, Equiv.symm_apply_apply] using h
  rw [← hinj hz]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- Triviality of the full based automorphism group follows from the
Cartan permutation and the fact that the simple coroots span the lattice. -/
theorem basedAutomorphism_eq_one (B : Specs.Pinning.BasedRootDatum.{u})
    (hspan : Submodule.span ℤ (Set.range B.datum.coroot) = ⊤)
    (hF : HasDynkinType (integralCartan B.datum B.base) .F4)
    (f : Aut B) : f = 1 := by
  classical
  let F : BasedIso B B := f.asIso.hom
  let p : Equiv.Perm B.base.support :=
    (F.val.indexEquiv.image (B.base.support : Set B.I)).trans (Set.equivOfEq F.property)
  have hp (i : B.base.support) : F.val.indexEquiv i.val = (p i).val := rfl
  have hpC : PreservesCartan (integralCartan B.datum B.base)
      (integralCartan B.datum B.base) p := by
    intro i j
    change B.datum.pairing j.val i.val = B.datum.pairing (p j).val (p i).val
    rw [← hp j, ← hp i]
    exact F.val.toHom.pairing.symm
  obtain ⟨e, he⟩ := hF
  change B.base.support ≃ Fin 4 at e
  have hperm := (RootData.AbsoluteDynkinTypes.cartanPermutationTransport
    (e := e) he p).mp hpC
  have hfix : (e.symm.trans p).trans e = Equiv.refl _ :=
    (RootData.AbsoluteDynkinTypes.exceptionalPermutations.2.2.2.1 _).mp hperm
  have hpfix (i : B.base.support) : p i = i := by
    apply e.injective
    simpa only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.refl_apply]
      using Equiv.congr_fun hfix (e i)
  obtain ⟨q, hq, huniq⟩ :=
    (RootData.AbsoluteDynkinTypes.cartanDeterminesBasedDatum B B hspan hspan
      (Equiv.refl B.base.support)).mp (fun _ _ => rfl)
  apply Aut.ext
  apply Iso.ext
  exact (huniq F (fun i => (hp i).trans (congrArg Subtype.val (hpfix i)))).trans
    (huniq (𝟙 B) (fun _ => rfl)).symm

open LinearAlgebraicGroups.Specs (ClosedSubgroup)
open Specs.CentralTorus (IsSchemeCentre)
open Specs.SchemeCentre (rootLattice)
open Specs.DiagonalizableGroups (groupAlgebra)
open scoped CategoryTheory.MonObj

open private semisimple_iff_corootFullRank from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private isIso_of_schemeIso from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private factor_group_through_subgroup from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private trivial_baseChange_iff from LinearAlgebraicGroups.Reductive.RadicalBaseChange

/-- The roots generate the full character group of the torus of a split
semisimple group of type F₄. -/
theorem rootLattice_eq_top {k : Type u} [Field k] (P : SplitBorelPair k)
    (D : AttachedDatum P) (hP : IsSemisimple P.G)
    (hF : letI := D.comm; HasDynkinType (integralCartan D.datum.rootDatum D.base) .F4) :
    rootLattice P.T = ⊤ := by
  letI := D.comm
  letI := D.datum.freeCocharacters
  letI := D.datum.finiteCocharacters
  have hspan := f4_root_span_eq_top D.datum.rootDatum D.base
    ((semisimple_iff_corootFullRank P D).mp hP) hF
  apply top_unique
  intro x _
  change Additive.ofMul x ∈ (rootLattice P.T).toAddSubgroup.toIntSubmodule
  have hle : Submodule.span ℤ (Set.range D.datum.rootDatum.root) ≤
      (rootLattice P.T).toAddSubgroup.toIntSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨α, rfl⟩
    rw [D.datum.root_eq]
    change α.val ∈ rootLattice P.T
    exact Subgroup.subset_closure α.property
  exact hle (hspan.symm ▸ Submodule.mem_top)

/-- With full root lattice every representative of the scheme centre is
the trivial group scheme. -/
theorem centreIsTrivial {k : Type u} [Field k] (P : SplitBorelPair k)
    (hroot : rootLattice P.T = ⊤) (Z : ClosedSubgroup P.G.val) (hZ : IsSchemeCentre Z) :
    Nonempty (Z.group ≅ Grp.trivial (SchemeOver k)) := by
  obtain ⟨_, e, _, hj, hz, _⟩ :=
    LinearAlgebraicGroups.RootData.SchemeCentre.schemeCentre P.G P.reductive P.T P.split P.maximal
  let M := Specs.CharacterDescent.Character P.T.group ⧸ rootLattice P.T
  let C : ClosedSubgroup P.G.val :=
    ⟨specGroup (groupAlgebra k M),
      Specs.DiagonalizableGroups.diagonalClosedInclusion k (rootLattice P.T) ≫
        e.hom ≫ P.T.inclusion, hj⟩
  letI : Subsingleton M := by
    change Subsingleton (Specs.CharacterDescent.Character P.T.group ⧸ rootLattice P.T)
    rw [hroot]
    exact QuotientGroup.subsingleton_quotient_top
  let A := CommHopfAlgCat.of k k
  let d : groupAlgebra k M ≅ A :=
    CommHopfAlgCat.isoMk (MonoidAlgebra.bialgEquivOfSubsingleton M)
  let t : specGroup A ⟶ Grp.trivial (SchemeOver k) := default
  have ht : IsIso t.hom.hom.left := by
    have h := Over.w t.hom.hom
    change t.hom.hom.left ≫ 𝟙 _ = (specGroup A).X.hom at h
    rw [Category.comp_id] at h
    rw [h, show (specGroup A).X.hom = 𝟙 _ from Spec.map_id _]
    infer_instance
  letI : IsIso t := isIso_of_schemeIso t
  let et : C.group ≅ Grp.trivial (SchemeOver k) :=
    (hopfSpec (CommRingCat.of k)).mapIso d.op.symm ≪≫ asIso t
  have hzc := (hZ Z.group.X Z.inclusion.hom.hom).mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨a, ha⟩ := hz Z.group.X Z.inclusion.hom.hom |>.mp hzc
  obtain ⟨f, hf⟩ := factor_group_through_subgroup C Z.inclusion a ha
  have h0 : C.inclusion = 0 := ((Grp.isZero_trivial _).of_iso et).eq_of_src _ _
  have hi : Z.inclusion = 0 := by rw [← hf, h0, comp_zero]
  letI := Z.isClosedImmersion
  letI : Mono Z.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : Mono Z.inclusion := (Grp.forget (SchemeOver k)).mono_of_mono_map
    (show Mono Z.inclusion.hom.hom from inferInstance)
  exact ⟨(IsZero.of_mono_eq_zero Z.inclusion hi).iso (Grp.isZero_trivial _)⟩

/-- The centre of the real form is trivial by faithful scalar extension. -/
theorem realCentreIsTrivial (G : AffineAlgebraicGroup ℝ) (hG : IsSemisimple G)
    (P : SplitBorelPair (AlgebraicClosure ℝ)) (hP : P.G = GeometricRadicals.GeometricGroup G)
    (D : AttachedDatum P)
    (hF : letI := D.comm; HasDynkinType (integralCartan D.datum.rootDatum D.base) .F4)
    (Z : ClosedSubgroup G.val) (hZ : IsSchemeCentre Z) :
    Nonempty (Z.group ≅ Grp.trivial (SchemeOver ℝ)) := by
  let K := AlgebraicClosure ℝ
  have hPss : IsSemisimple P.G := hP ▸
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := K) G hG.1 hG.2.1).mpr hG
  have hroot := rootLattice_eq_top P D hPss hF
  obtain ⟨hc, he⟩ :=
    LinearAlgebraicGroups.centralizerSchemeBaseChange ℝ K (𝟙 G.val) Z hZ
  have hid : (groupBaseChange ℝ K).map (𝟙 G.val) =
      𝟙 ((groupBaseChange ℝ K).obj G.val) := CategoryTheory.Functor.map_id _ _
  rw [hid] at he
  have hK := centreIsTrivial P hroot
  rw [hP] at hK
  exact (trivial_baseChange_iff (K := K) Z.group).mp
    (hK (scalarExtendedSubgroup K Z hc) he)

open private isIso_of_trivial_kernel from LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness

private theorem adjointProjection_isIso (G : AffineAlgebraicGroup ℝ) {Q : AffineAlgebraicGroup ℝ}
    (Z : ClosedSubgroup G.val) (q : G.val ⟶ Q.val)
    (hq : Specs.AdjointCocharacters.IsAdjointQuotient Z q)
    (hZ : Nonempty (Z.group ≅ Grp.trivial (SchemeOver ℝ))) : IsIso q :=
  isIso_of_trivial_kernel q Z ⟨hq.2.1, hq.2.2.2.1, hq.2.2.2.2.1, hq.2.2.2.2.2, hq.2.2.1⟩ hZ

open Opposite
open scoped CategoryTheory.MonoidalCategory
open Specs.AutomorphismSequence (RelativeAut innerAut)

open private surjectiveOnSections from LinearAlgebraicGroups.Reductive.CentralDerived

/-- Every relative automorphism over an algebraically closed field of a split
semisimple group of type F₄ is implemented by a rational point. -/
theorem automorphism_is_inner {k : Type u} [Field k] [IsAlgClosed k]
    (P : SplitBorelPair k) (D : AttachedDatum P) (hP : IsSemisimple P.G)
    (hF : letI := D.comm; HasDynkinType (integralCartan D.datum.rootDatum D.base) .F4)
    (a : RelativeAut P.G.val (𝟙_ (SchemeOver k))) :
    ∃ g : (𝟙_ (SchemeOver k)) ⟶ P.G.val.X, a = innerAut g := by
  letI := D.comm
  letI := D.datum.freeCocharacters
  letI := D.datum.finiteCocharacters
  have hspan := f4_coroot_span_eq_top D.datum.rootDatum D.base
    ((semisimple_iff_corootFullRank P D).mp hP) hF
  letI : Subsingleton (Aut D.toBased) := ⟨fun f g =>
    (basedAutomorphism_eq_one D.toBased hspan hF f).trans
      (basedAutomorphism_eq_one D.toBased hspan hF g).symm⟩
  let A := Classification.Pinning.standardAdditiveLine k
  obtain ⟨U, ⟨p⟩⟩ := Classification.Pinning.pinningsExist A P
  let R : Specs.Pinning.PinnedGroup A := ⟨P, U, p⟩
  obtain ⟨E, l, Q, F, _, _⟩ := Descent.AutomorphismSequence.automorphismSequence R
  let d : D.toBased ⟶ E.toBased :=
    Classification.Pinning.inducedBasedIso (Specs.Pinning.PinnedIso.refl R) D E
  letI : Subsingleton (Aut E.toBased) := ⟨fun f g =>
    (Aut.autMulEquivOfIso (asIso d)).symm.injective (Subsingleton.elim _ _)⟩
  have hout : F.toExactSequence.outer.app (op (𝟙_ (SchemeOver k))) a = 1 := by
    apply ULift.ext
    apply LocallyConstant.ext
    intro z
    exact Subsingleton.elim (α := Aut E.toBased) _ _
  obtain ⟨⟨x⟩, hx⟩ := (F.toExactSequence.exact (op (𝟙_ (SchemeOver k))) a).mp hout
  obtain ⟨g, hg⟩ := surjectiveOnSections Q.projection Q.fppf.2.1 x
  refine ⟨g, ?_⟩
  rw [← hx, ← hg]
  exact F.toExactSequence.onLift _ g

theorem complexSemisimple (G : AffineAlgebraicGroup ℝ) (hG : IsSemisimple G) :
    IsSemisimple (complexGroup G) :=
  (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := ℂ) G hG.1 hG.2.1).mpr hG

theorem complexRealization (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G) :
    ∃ j : MatrixRealization (complexGroup G), Nonempty (PointsIn j ℂ ≃ₜ* PointsIn i ℂ) := by
  obtain ⟨_, j, _, e, _, _⟩ :=
    ArchimedeanLieChart.baseChangeMatrixComparison ℝ ℂ G i
  exact ⟨j, ⟨e⟩⟩

theorem complexTangent (G : AffineAlgebraicGroup ℝ) (s : IdentityLieStructure G.val) :
    ∃ sC : IdentityLieStructure (complexGroup G).val, ComplexTangentData G s sC := by
  obtain ⟨⟨sC⟩, h⟩ := LinearAlgebraicGroups.identityLieBracketBaseChange ℝ ℂ G
  exact ⟨sC, h s sC⟩

private theorem transportedConjugation_apply {L H : Type} [LieRing L] [LieAlgebra ℂ L]
    [LieRing H] [LieAlgebra ℂ H] (τ : Conjugation L) (e : L ≃ₗ⁅ℂ⁆ H) (z : L) :
    (τ.transport e).map (e z) = e (τ.map z) := by
  change e (τ.map (e.symm (e z))) = _
  rw [e.symm_apply_apply]


open Topology
open Specs.Unipotent (Index)
open StandardGroups (GLCoordinates)

open private glEvaluation glEvaluation_entry glCoordinates_ext
  from LinearAlgebraicGroups.Affine.StandardGroups
open private matrixPresentation asMatrix_isClosedEmbedding glVal_isEmbedding coordinateMap_of_map
  from LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private coordinateMap coordinateMap_spec from LinearAlgebraicGroups.Arithmetic.IntegralModels

private abbrev realCoefficients : CommAlgCat.of ℝ ℝ ⟶ CommAlgCat.of ℝ ℂ :=
  CommAlgCat.ofHom (Algebra.ofId ℝ ℂ)

private theorem asMatrix_extendRealPoint {G : AffineAlgebraicGroup ℝ}
    (i : MatrixRealization G) (p : PointsIn i ℝ) :
    asMatrix i ℂ (mapPoints realCoefficients p) =
      Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) (asMatrix i ℝ p) := by
  let n := ((groupPointsFunctor ℝ).map i.embedding) ≫ i.matrix.hom
  exact ConcreteCategory.congr_hom (n.naturality realCoefficients) p

/-- Real matrix entries characterize the real points in the scalar-extended
test algebra of a closed real matrix realization. -/
theorem realPoint_iff_realEntries {G : AffineAlgebraicGroup ℝ} (i : MatrixRealization G)
    (g : PointsIn i ℂ) :
    (∃ p : PointsIn i ℝ, mapPoints (CommAlgCat.ofHom (Algebra.ofId ℝ ℂ)) p = g) ↔
      ∀ r d, ((asMatrix i ℂ g).val r d).im = 0 := by
  let aC := realCoefficients
  constructor
  · rintro ⟨p, rfl⟩ r d
    change ((asMatrix i ℂ (mapPoints aC p)).val r d).im = 0
    rw [asMatrix_extendRealPoint]
    change (Complex.ofReal ((asMatrix i ℝ p).val r d)).im = 0
    exact Complex.ofReal_im _
  · intro hg
    let M := asMatrix i ℂ g
    let N : Matrix (Index i.size) (Index i.size) ℝ := fun r d => (M.val r d).re
    have hN : N.map (algebraMap ℝ ℂ) = M.val := by
      ext r d
      apply Complex.ext
      · rfl
      · exact (hg r d).symm
    have hdet : N.det ≠ 0 := by
      intro h
      have hm := congrArg Matrix.det hN
      change ((algebraMap ℝ ℂ).mapMatrix N).det = M.val.det at hm
      rw [← RingHom.map_det, h, map_zero] at hm
      exact (Matrix.GeneralLinearGroup.det M).ne_zero hm.symm
    let U := Matrix.GeneralLinearGroup.mkOfDetNeZero N hdet
    have hU : Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) U = M := Units.ext hN
    have hEval : glEvaluation (k := ℝ) M =
        (Algebra.ofId ℝ ℂ).comp (glEvaluation U) := by
      apply glCoordinates_ext
      intro r d
      rw [glEvaluation_entry, AlgHom.comp_apply, glEvaluation_entry, ← hU]
      rfl
    obtain ⟨B, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.prop.1
    obtain ⟨a, ha, hmatrix⟩ := matrixPresentation B.unop e i
    let ev : B.unop ⟶ CommAlgCat.of ℝ ℂ := coordinateMap (g ≫ e.inv)
    have heq (z : GLCoordinates ℝ (Index i.size)) :
        ev.hom (a.hom z) = (algebraMap ℝ ℂ) (glEvaluation U z) :=
      congrArg (fun f : GLCoordinates ℝ (Index i.size) →ₐ[ℝ] ℂ => f z)
        ((hmatrix ℂ g).symm.trans hEval)
    have hreal (z : B.unop) : (ev.hom z).im = 0 := by
      obtain ⟨w, rfl⟩ := ha z
      rw [heq]
      rfl
    let fe : B.unop →ₐ[ℝ] ℝ :=
      { toFun := fun z => (ev.hom z).re
        map_one' := by simp
        map_zero' := by simp
        map_add' := by intros; simp
        map_mul' x y := by simp [Complex.mul_re, hreal]
        commutes' x := congrArg Complex.re (ev.hom.commutes x) }
    let f : B.unop ⟶ CommAlgCat.of ℝ ℝ := CommAlgCat.ofHom fe
    have hf : f ≫ aC = ev := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro z
      change Complex.ofReal (ev.hom z).re = ev.hom z
      exact Complex.ext rfl (hreal z).symm
    let p : PointsIn i ℝ := (testSpec ℝ).map f.op ≫ e.hom
    refine ⟨p, ?_⟩
    change (testSpec ℝ).map aC.op ≫ ((testSpec ℝ).map f.op ≫ e.hom) = g
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, ← op_comp, hf, coordinateMap_spec,
      Category.assoc, e.inv_hom_id, Category.comp_id]


open Specs.AdjointLieAutomorphisms (PreservesBracket coordinateBracket)
open private coordinateBracket_basis from LinearAlgebraicGroups.Arithmetic.AdjointLieAutomorphisms

/-- The matrix homomorphism on the full group of Lie automorphisms. -/
def automorphismMatrix {k L I : Type u} [Field k] [LieRing L] [LieAlgebra k L]
    [Fintype I] [DecidableEq I] (b : Module.Basis I k L) :
    (L ≃ₗ⁅k⁆ L) →* Matrix.GeneralLinearGroup I k :=
  (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp
    { toFun := fun f => LinearMap.GeneralLinearGroup.ofLinearEquiv f.toLinearEquiv
      map_one' := rfl
      map_mul' _ _ := rfl }

private theorem automorphismMatrix_entry {k L I : Type u} [Field k] [LieRing L]
    [LieAlgebra k L] [Fintype I] [DecidableEq I] (b : Module.Basis I k L)
    (f : L ≃ₗ⁅k⁆ L) (i j : I) :
    (automorphismMatrix b f).val i j = b.repr (f (b j)) i :=
  LinearMap.toMatrixAlgEquiv_apply b f.toLinearEquiv.toLinearMap i j

private theorem automorphismMatrix_mulVec {k L I : Type u} [Field k] [LieRing L]
    [LieAlgebra k L] [Fintype I] [DecidableEq I] (b : Module.Basis I k L)
    (f : L ≃ₗ⁅k⁆ L) (x : L) :
    (automorphismMatrix b f).val *ᵥ b.equivFun x = b.equivFun (f x) :=
  LinearMap.toMatrix_mulVec_repr b b f.toLinearEquiv.toLinearMap x

private theorem automorphismMatrix_injective {k L I : Type u} [Field k] [LieRing L]
    [LieAlgebra k L] [Fintype I] [DecidableEq I] (b : Module.Basis I k L) :
    Function.Injective (automorphismMatrix b) := by
  intro f g h
  ext x
  apply b.equivFun.injective
  rw [← automorphismMatrix_mulVec b f, ← automorphismMatrix_mulVec b g, h]

/-- In any finite basis, the invertible matrices preserving the bracket
are exactly the matrices of Lie automorphisms. -/
theorem preservesBracket_iff_matrixOfLieAut {k L I : Type u} [Field k]
    [LieRing L] [LieAlgebra k L] [Fintype I] [DecidableEq I] (b : Module.Basis I k L)
    (M : Matrix.GeneralLinearGroup I k) :
    PreservesBracket (fun i j l => b.repr ⁅b i, b j⁆ l) (RingHom.id k) M ↔
      M ∈ (automorphismMatrix b).range := by
  constructor
  · intro h
    let e := LinearMap.GeneralLinearGroup.toLinearEquiv
      (Units.map (Matrix.toLinAlgEquiv b).toMonoidHom M)
    have he (x : L) : b.equivFun (e x) = M.val *ᵥ b.equivFun x :=
      Matrix.repr_toLin b b M.val x
    let f : L ≃ₗ⁅k⁆ L :=
      { e with
        map_lie' := fun {x y} => by
          apply b.equivFun.injective
          change b.equivFun (e ⁅x, y⁆) = b.equivFun ⁅e x, e y⁆
          rw [he, ← coordinateBracket_basis b (e x) (e y), he, he,
            h, coordinateBracket_basis] }
    refine ⟨f, Units.ext ?_⟩
    exact LinearMap.toMatrixAlgEquiv_toLinAlgEquiv b M.val
  · rintro ⟨f, rfl⟩ x y
    obtain ⟨p, rfl⟩ := b.equivFun.surjective x
    obtain ⟨q, rfl⟩ := b.equivFun.surjective y
    rw [automorphismMatrix_mulVec, automorphismMatrix_mulVec, coordinateBracket_basis,
      coordinateBracket_basis, automorphismMatrix_mulVec, f.map_lie]

/-- A Lie automorphism commutes with a real conjugation precisely when
its entries in a conjugation-fixed basis are real. -/
theorem intertwines_iff_realMatrix {L I : Type} [LieRing L] [LieAlgebra ℂ L]
    [Fintype I] [DecidableEq I] (b : Module.Basis I ℂ L) (σ : Conjugation L)
    (hb : ∀ i, σ.map (b i) = b i) (f : L ≃ₗ⁅ℂ⁆ L) :
    Intertwines σ σ f ↔ ∀ i j, ((automorphismMatrix b f).val i j).im = 0 := by
  have hconj (x : L) (i : I) : b.repr (σ.map x) i = star (b.repr x i) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum, map_sum]
    simp only [Finsupp.finsetSum_apply, σ.antilinear, hb, map_smul,
      Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  have hreal (z : ℂ) : star z = z ↔ z.im = 0 := by
    constructor
    · intro h
      have h' := congrArg Complex.im h
      change -z.im = z.im at h'
      linarith
    · intro h
      exact Complex.ext rfl (by change -z.im = z.im; rw [h, neg_zero])
  constructor
  · intro h i j
    rw [automorphismMatrix_entry, ← hreal, ← hconj, h (b j), hb]
  · intro h x
    apply b.equivFun.injective
    ext i
    change b.repr (σ.map (f x)) i = b.repr (f (σ.map x)) i
    rw [hconj]
    have hf (y : L) : b.repr (f y) i =
        ∑ j, (automorphismMatrix b f).val i j * b.repr y j :=
      (congrFun (automorphismMatrix_mulVec b f y) i).symm
    rw [hf x, hf (σ.map x)]
    change Complex.conjAe (∑ j, (automorphismMatrix b f).val i j * b.repr x j) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, hconj]
    change star ((automorphismMatrix b f).val i j) * star (b.repr x j) = _
    rw [(hreal _).mpr (h i j)]


open Specs.Pinning (BasedRootDatum)
open private transportSubgroup from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private pushKBorel maximalTransport pinAlignedPairs from LinearAlgebraicGroups.Classification.PinnedEquivalence
open private fibreTowerIso from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private groupBaseChangeTower from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private reductive_of_semisimple from LinearAlgebraicGroups.Arithmetic.AdjointLieAutomorphisms
open private groupObjectsFunctor_isEquivalence from LinearAlgebraicGroups.RootData.BorelNormalizer

private theorem hasTypeF4_of_basedIso {D E : BasedRootDatum.{u}} (e : BasedIso D E)
    (h : HasDynkinType (integralCartan D.datum D.base) .F4) :
    HasDynkinType (integralCartan E.datum E.base) .F4 := by
  obtain ⟨p, hp⟩ := h
  let q : D.base.support ≃ E.base.support :=
    (e.val.indexEquiv.image (D.base.support : Set D.I)).trans (Set.equivOfEq e.property)
  have hc (i j : D.base.support) :
      integralCartan D.datum D.base i j = integralCartan E.datum E.base (q i) (q j) :=
    e.val.toHom.pairing.symm
  refine ⟨q.symm.trans p, ?_⟩
  intro i j
  simpa only [Equiv.apply_symm_apply, Equiv.trans_apply] using
    (hc (q.symm i) (q.symm j)).symm.trans (hp (q.symm i) (q.symm j))

private theorem hasTypeF4_of_pinnedIso {k : Type u} [Field k] {A : Specs.RootGroups.AdditiveLine k}
    {S T : Specs.Pinning.PinnedGroup A} {P Q : SplitBorelPair k}
    (hP : S.pair = P) (hQ : T.pair = Q) (f : Specs.Pinning.PinnedIso S T)
    (D : AttachedDatum P) (E : AttachedDatum Q)
    (hF : letI := D.comm; HasDynkinType (integralCartan D.datum.rootDatum D.base) .F4) :
    letI := E.comm
    HasDynkinType (integralCartan E.datum.rootDatum E.base) .F4 := by
  subst P
  subst Q
  exact hasTypeF4_of_basedIso (Classification.Pinning.inducedBasedIso f D E) hF

/-- Transfer the geometric Cartan type to the actual complex group. The
integral model supplies a single split model across the two algebraic closures. -/
theorem complexBorelPair (G : AffineAlgebraicGroup ℝ) (hG : IsSemisimple G)
    (P : SplitBorelPair (AlgebraicClosure ℝ)) (hP : P.G = GeometricRadicals.GeometricGroup G)
    (D : AttachedDatum P)
    (hF : letI := D.comm; HasDynkinType (integralCartan D.datum.rootDatum D.base) .F4) :
    ∃ (PC : SplitBorelPair ℂ) (_ : PC.G = complexGroup G) (DC : AttachedDatum PC),
      letI := DC.comm
      HasDynkinType (integralCartan DC.datum.rootDatum DC.base) .F4 := by
  let K := AlgebraicClosure ℝ
  letI : IsAlgClosure ℝ ℂ := ⟨inferInstance, inferInstance⟩
  let σ := IsAlgClosure.equiv ℝ ℂ K
  letI : Algebra ℂ K := σ.toRingHom.toAlgebra
  letI : IsScalarTower ℝ ℂ K := IsScalarTower.of_algebraMap_eq fun x => (σ.commutes x).symm
  have hfield : IsIso (fieldSpecMap ℂ K) := by
    change IsIso (Spec.map σ.toRingEquiv.toCommRingCatIso.hom)
    infer_instance
  letI : IsIso (fieldSpecMap ℂ K) := hfield
  letI : (Over.pullback (fieldSpecMap ℂ K)).IsEquivalence :=
    (Over.mapPullbackAdj (fieldSpecMap ℂ K)).isEquivalence_right_of_isEquivalence_left
  letI : (groupBaseChange ℂ K).IsEquivalence :=
    groupObjectsFunctor_isEquivalence (Over.pullback (fieldSpecMap ℂ K))
  let F := groupBaseChange ℂ K
  obtain ⟨M⟩ := Classification.IntegralRealization.integralRealization D.toBased
  obtain ⟨A, FC, eC, _, _, _, _, _, _⟩ := M.fieldFibre ℂ
  obtain ⟨_, FK, eK, _, _, _, _, _, _⟩ := M.fieldFibre K
  obtain ⟨d⟩ := (Classification.PinnedEquivalence.pinnedEquivalence.2 K).2.1
    P FK.pinned.pair D FK.attached |>.mpr ⟨FK.datumIso.val⟩
  let tK : F.obj FC.pinned.pair.G.val ≅ F.obj (complexGroup G).val :=
    (F.mapIso eC).symm ≪≫ ((fibreTowerIso ℂ K).app M.group).symm ≪≫ eK ≪≫ d.symm ≪≫
      eqToIso (congrArg (fun X : AffineAlgebraicGroup K => X.val) hP) ≪≫
      (groupBaseChangeTower (k := ℝ) (K := ℂ) K).app G.val
  let t := (CategoryTheory.Functor.FullyFaithful.ofFullyFaithful F).preimageIso tK
  have hGCr : GeometricRadicals.IsReductive (complexGroup G) := by
    have hr : GeometricRadicals.IsReductive G := by
      exact reductive_of_semisimple G hG
    exact (Reductive.RadicalBaseChange.reductiveFieldExtension (K := ℂ) G hr.1 hr.2.1).mpr hr
  let S := FC.pinned.pair
  let PC : SplitBorelPair ℂ :=
    { G := complexGroup G
      reductive := hGCr
      T := transportSubgroup t S.T
      split := S.split
      maximal := maximalTransport t S.T S.maximal
      B := transportSubgroup t S.B
      borel := pushKBorel t S.borel
      containsTorus := by
        obtain ⟨m, hm⟩ := S.containsTorus
        refine ⟨m, ?_⟩
        change m ≫ S.B.inclusion ≫ t.hom = S.T.inclusion ≫ t.hom
        rw [← Category.assoc, hm] }
  obtain ⟨S', C', hS', hC', ⟨f⟩⟩ :=
    pinAlignedPairs S PC A t (Iso.refl _) (by simp [PC, transportSubgroup])
      (Iso.refl _) (by simp [PC, transportSubgroup])
  have hFC : HasDynkinType (integralCartan FC.attached.toBased.datum FC.attached.toBased.base) .F4 :=
    hasTypeF4_of_basedIso FC.datumIso hF
  let DC := Classification.Pinning.attachedDatum PC
  refine ⟨PC, rfl, DC, ?_⟩
  exact hasTypeF4_of_pinnedIso hS' hC' f FC.attached DC hFC


open CategoryTheory.CartesianMonoidalCategory
open Specs.GeometricRadicals (GeometricGroup)
open private innerIso comp_innerMap innerMap from LinearAlgebraicGroups.Reductive.BorelProper
open private connectedOfGeometricallyConnected closedSurjectiveSections
  from LinearAlgebraicGroups.Reductive.CentralDerived
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private factors_through_closed_of_range from LinearAlgebraicGroups.Relative.RationalDensity
open private inclusion_mono from LinearAlgebraicGroups.RootData.OrderedRootProducts

private theorem restrictConjugation {k : Type u} [Field k]
    {G A : AffineAlgebraicGroup k} (hG : IsSemisimple G)
    (f : G.val ⟶ A.val) (hf : IsClosedImmersion f.hom.hom.left)
    (hr : Set.range f.hom.hom.left = connectedComponent (groupIdentityPoint A.val))
    (a : (𝟙_ (SchemeOver k)) ⟶ A.val.X) :
    ∃ e : G.val ≅ G.val, e.hom ≫ f = f ≫ innerMap a := by
  letI := hG.1
  letI : IsReduced G.val.X.left := isReduced_of_smooth_over_field G.val.X.hom
  letI : ConnectedSpace G.val.X.left := connectedOfGeometricallyConnected G hG.2.1
  let S : ClosedSubgroup A.val := ⟨G.val, f, hf⟩
  letI : Mono f := inclusion_mono S
  have factor (x : (𝟙_ (SchemeOver k)) ⟶ A.val.X) :
      ∃ v : G.val ⟶ G.val, v ≫ f = f ≫ innerMap x := by
    apply factors_through_closed_of_range (f ≫ innerMap x) S
    change Set.range (f ≫ innerMap x).hom.hom.left ⊆ Set.range f.hom.hom.left
    rw [hr]
    refine (isConnected_range (f ≫ innerMap x).hom.hom.left.continuous).subset_connectedComponent ?_
    refine ⟨groupIdentityPoint G.val, ?_⟩
    change (η[G.val.X] ≫ (f ≫ innerMap x).hom.hom).left (IsLocalRing.closedPoint k) = _
    rw [IsMonHom.one_hom]
    rfl
  obtain ⟨e, he⟩ := factor a
  obtain ⟨d, hd⟩ := factor a⁻¹
  refine ⟨⟨e, d, ?_, ?_⟩, he⟩
  · apply (cancel_mono f).mp
    rw [Category.assoc, hd, ← Category.assoc, he, Category.assoc]
    change f ≫ ((innerIso a).hom ≫ (innerIso a).inv) = _
    simp
  · apply (cancel_mono f).mp
    rw [Category.assoc, he, ← Category.assoc, hd, Category.assoc]
    change f ≫ ((innerIso a).inv ≫ (innerIso a).hom) = _
    simp

private theorem innerMap_of_relative {k : Type u} [Field k]
    {G : GroupScheme k} (e : G ≅ G) (g : (𝟙_ (SchemeOver k)) ⟶ G.X)
    (h : Specs.AutomorphismSequence.scalarAut (Aut.of e) (𝟙_ (SchemeOver k)) = innerAut g) :
    e.hom = innerMap g := by
  let W : Over (𝟙_ (SchemeOver k)) := Over.mk (toUnit G.X)
  have he := congrArg (fun t : RelativeAut G (𝟙_ (SchemeOver k)) =>
    (t.asIso.hom.app (op W)).hom (𝟙 G.X)) h
  apply Grp.hom_ext
  change 𝟙 G.X ≫ e.hom.hom.hom =
    (toUnit G.X ≫ g) * 𝟙 G.X * (toUnit G.X ≫ g)⁻¹ at he
  rw [Category.id_comp] at he
  exact he.trans (by
    simpa only [Category.id_comp] using (comp_innerMap g (𝟙 G.X)).symm)

private theorem conjugate_postcompose {k : Type u} [Field k] {G A : GroupScheme k}
    (f : G ⟶ A) (g : (𝟙_ (SchemeOver k)) ⟶ G.X) :
    innerMap g ≫ f = f ≫ innerMap (g ≫ f.hom.hom) := by
  apply Grp.hom_ext
  change (innerMap g).hom.hom ≫ f.hom.hom = f.hom.hom ≫ (innerMap _).hom.hom
  rw [comp_innerMap]
  have h := comp_innerMap g (𝟙 G.X)
  rw [Category.id_comp] at h
  rw [h, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, Category.id_comp, Category.assoc]


open AdjointRepresentation (GroupPoints TangentCoordinates constants conjugate ScalarExtension)
open Specs.StandardGroups (generalLinearPoints)
open InfinitesimalCommutator (matrixDifferential)
open private differential_formula from LinearAlgebraicGroups.Affine.AdjointRepresentation
open private lieIsKilling baseTestSpecIso scalar_bracket_constants
  from LinearAlgebraicGroups.Arithmetic.AdjointLieAutomorphisms

private theorem commute_dual_coefficient {k I : Type u}
    [Field k] [Fintype I] [DecidableEq I] (M : Matrix.GeneralLinearGroup I k)
    (P : Matrix.GeneralLinearGroup I (DualNumber k))
    (h : Commute
      (Matrix.GeneralLinearGroup.map (constants (CommAlgCat.of k k)).hom.toRingHom M) P) :
    Commute M.val (P.val.map TrivSqZeroExt.snd) := by
  have he := congrArg (fun z : Matrix.GeneralLinearGroup I (DualNumber k) =>
      z.val.map TrivSqZeroExt.snd) h.eq
  ext i j
  have hh := congrFun (congrFun he i) j
  change (∑ l, (TrivSqZeroExt.inl (M.val i l) : DualNumber k) * P.val l j).snd =
    (∑ l, P.val i l * (TrivSqZeroExt.inl (M.val l j) : DualNumber k)).snd at hh
  simpa only [Matrix.mul_apply, Matrix.map_apply, TrivSqZeroExt.snd_sum,
    DualNumber.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
    zero_mul, mul_zero, zero_add, add_zero] using hh

private theorem automorphismMatrix_eq_one_of_commutes_ad {k V I : Type u} [Field k]
    [LieRing V] [LieAlgebra k V] [Fintype I] [DecidableEq I]
    (b : Module.Basis I k V) (f : V ≃ₗ⁅k⁆ V) (D : V → Matrix I I k)
    (hcenter : LieAlgebra.center k V = ⊥)
    (hD : ∀ x y, D x *ᵥ b.equivFun y = b.equivFun ⁅x, y⁆)
    (hc : ∀ x, Commute (automorphismMatrix b f).val (D x)) :
    automorphismMatrix b f = 1 := by
  have hf (x : V) : f x = x := by
    apply (LieDerivation.injective_ad_of_center_eq_bot hcenter)
    apply LieDerivation.ext
    intro z
    obtain ⟨y, rfl⟩ := f.surjective z
    simp only [LieDerivation.ad_apply_apply]
    change ⁅f x, f y⁆ = ⁅x, f y⁆
    rw [← f.map_lie]
    apply b.equivFun.injective
    rw [← automorphismMatrix_mulVec, ← hD, Matrix.mulVec_mulVec,
      (hc x).eq, ← Matrix.mulVec_mulVec, automorphismMatrix_mulVec, hD]
  have e : f = 1 := by ext x; exact hf x
  rw [e, map_one]


private theorem component_isFull {k I : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    [Fintype I] [DecidableEq I] (G A L : AffineAlgebraicGroup k)
    (hG : IsSemisimple G)
    (f : G.val ⟶ A.val) (j : A.val ⟶ L.val)
    (hf : IsClosedImmersion f.hom.hom.left) (hj : IsClosedImmersion j.hom.hom.left)
    (hr : Set.range f.hom.hom.left = connectedComponent (groupIdentityPoint A.val))
    (houter : ∀ a : RelativeAut G.val (𝟙_ (SchemeOver k)),
      ∃ g : (𝟙_ (SchemeOver k)) ⟶ G.val.X, a = innerAut g)
    (s : IdentityLieStructure G.val)
    (b : letI := s.lieRing; letI := s.lieAlgebra; Module.Basis I k (Lie k G.val))
    (T : letI := s.lieRing; letI := s.lieAlgebra; TangentCoordinates G.val I b)
    (l : (groupPointsFunctor k).obj L.val ≅ generalLinearPoints k I)
    (hAd : letI := s.lieRing; letI := s.lieAlgebra;
      ∀ (R : TestAlgebra k) (g : GroupPoints G.val R) (v : I → R),
        let M := (l.hom.app R).hom (((groupPointsFunctor k).map (f ≫ j)).app R g)
        (T.equiv R (M.val *ᵥ v)).toMul.val = conjugate g (T.equiv R v))
    (hbr : letI := s.lieRing; letI := s.lieAlgebra;
      ∀ a : GroupPoints A.val (CommAlgCat.of k k),
        PreservesBracket (fun i d r => b.repr ⁅b i, b d⁆ r) (RingHom.id k)
          ((l.hom.app (CommAlgCat.of k k)).hom
            (((groupPointsFunctor k).map j).app (CommAlgCat.of k k) a))) :
    IsIso f := by
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : FiniteDimensional k (Lie k G.val) := b.finiteDimensional_of_finite
  letI := lieIsKilling G hG s
  have hcenter : LieAlgebra.center k (Lie k G.val) = ⊥ :=
    LieAlgebra.IsKilling.ideal_eq_bot_of_isLieAbelian _
  let V := (groupPointsFunctor k).obj A.val
  let J := ((groupPointsFunctor k).map j) ≫ l.hom
  let R := CommAlgCat.of k k
  let Rε := CommAlgCat.of k (DualNumber k)
  let S := (testSpec k).obj (op R)
  let E := baseTestSpecIso k
  have hsection (a : (𝟙_ (SchemeOver k)) ⟶ A.val.X) :
      ∃ g : (𝟙_ (SchemeOver k)) ⟶ G.val.X, g ≫ f.hom.hom = a := by
    obtain ⟨e, he⟩ := restrictConjugation hG f hf hr a
    obtain ⟨g, hg⟩ := houter (Specs.AutomorphismSequence.scalarAut (Aut.of e) _)
    have e_inner := innerMap_of_relative e g hg
    let c := g ≫ f.hom.hom
    have hconj : f ≫ innerMap a = f ≫ innerMap c :=
      he.symm.trans (e_inner ▸ conjugate_postcompose f g)
    -- The residual automorphism centralizes the adjoint image and hence its differential.
    let r := c⁻¹ * a
    let ra : GroupPoints A.val R := E.inv ≫ r
    let M : Matrix.GeneralLinearGroup I k := (J.app R).hom ra
    obtain ⟨m, hm⟩ := (preservesBracket_iff_matrixOfLieAut b M).mp (hbr ra)
    have hc (x : Lie k G.val) :
        Commute M.val (matrixDifferential (f ≫ j) l x) := by
      let U := (testSpec k).obj (op Rε)
      let p : U ⟶ G.val.X := x.toMul.val
      let v : GroupPoints A.val Rε := p ≫ f.hom.hom
      let aU : GroupPoints A.val Rε := toUnit U ≫ a
      let cU : GroupPoints A.val Rε := toUnit U ≫ c
      let rU : GroupPoints A.val Rε := toUnit U ≫ r
      have hv : aU * v * aU⁻¹ = cU * v * cU⁻¹ := by
        have h := congrArg (fun d : G.val ⟶ A.val => p ≫ d.hom.hom) hconj
        change p ≫ (f.hom.hom ≫ (innerMap a).hom.hom) =
          p ≫ (f.hom.hom ≫ (innerMap c).hom.hom) at h
        rw [← Category.assoc, comp_innerMap, ← Category.assoc, comp_innerMap] at h
        exact h
      have hrU : rU = cU⁻¹ * aU := by
        simp only [rU, r, MonObj.comp_mul, GrpObj.comp_inv, cU, aU]
      have hcomm : Commute rU v := by
        apply mul_inv_eq_iff_eq_mul.mp
        rw [hrU]
        calc
          (cU⁻¹ * aU) * v * (cU⁻¹ * aU)⁻¹ =
              cU⁻¹ * (aU * v * aU⁻¹) * cU := by group
          _ = v := by rw [hv]; group
      have haU : (V.map (constants R)).hom ra = rU := by
        change ((testSpec k).map (constants R).op) ≫ (E.inv ≫ r) = toUnit U ≫ r
        rw [← Category.assoc]
        exact congrArg (· ≫ r) ((isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _)
      have hM : (J.app Rε).hom rU =
          Matrix.GeneralLinearGroup.map (constants R).hom.toRingHom M := by
        have h := ConcreteCategory.congr_hom (J.naturality (constants R)) ra
        change (J.app Rε).hom ((V.map (constants R)).hom ra) = _ at h
        rwa [haU] at h
      have hmat := hcomm.map (J.app Rε).hom
      rw [hM] at hmat
      exact commute_dual_coefficient M ((J.app Rε).hom v) hmat
    have hD := differential_formula T l (f ≫ j) hAd s.commutator_law
    have hM1 : M = 1 := hm ▸
      automorphismMatrix_eq_one_of_commutes_ad b m (matrixDifferential (f ≫ j) l)
        hcenter hD (fun x => hm.symm ▸ hc x)
    letI := hj
    letI : Mono j.hom.hom := Over.mono_of_mono_left _
    have hJ : Function.Injective (J.app R).hom := by
      intro x y h
      apply (cancel_mono j.hom.hom).mp
      exact (ConcreteCategory.bijective_of_isIso (l.hom.app R)).1 h
    have h1 : ra = 1 := hJ (hM1.trans (map_one (J.app R).hom).symm)
    have harr : r = 1 := by
      have h := congrArg (fun z : S ⟶ A.val.X => E.hom ≫ z) h1
      simpa only [ra, Iso.hom_inv_id_assoc, MonObj.comp_one] using h
    exact ⟨g, inv_mul_eq_one.mp harr⟩
  letI := hf
  letI := closedSurjectiveSections f hf hsection
  letI := characteristicZeroSmoothness k A
  letI := isReduced_of_smooth_over_field A.val.X.hom
  letI := isIso_of_isClosedImmersion_of_surjective f.hom.hom.left
  exact isIso_of_schemeIso f


open Specs.AdjointLieAutomorphisms (RepresentsBracketAutomorphisms)
open private baseChangePointIso from LinearAlgebraicGroups.Affine.IdentityTangent
open private isIso_of_scalarExtension from LinearAlgebraicGroups.Classification.SimplyConnectedLattice

private def extendMatrixPoints {k K I : Type u} [Field k] [Field K] [Algebra k K]
    [Fintype I] [DecidableEq I] {L : GroupScheme k}
    (l : (groupPointsFunctor k).obj L ≅ generalLinearPoints k I) :
    (groupPointsFunctor K).obj ((groupBaseChange k K).obj L) ≅ generalLinearPoints K I :=
  baseChangePointIso K L ≪≫ CategoryTheory.Functor.isoWhiskerLeft _ l

private theorem extendedBracket {k K I : Type u} [Field k] [Field K] [Algebra k K]
    [Fintype I] [DecidableEq I] {V W : Type u} [LieRing V] [LieAlgebra k V]
    [LieRing W] [LieAlgebra K W] (b : Module.Basis I k V)
    (e : (K ⊗[k] V) ≃ₗ⁅K⁆ W) (M : Matrix.GeneralLinearGroup I K) :
    let B := (b.baseChange K).map e.toLinearEquiv
    PreservesBracket (fun i d r => B.repr ⁅B i, B d⁆ r) (RingHom.id K) M ↔
      PreservesBracket (fun i d r => b.repr ⁅b i, b d⁆ r) (algebraMap k K) M := by
  dsimp only
  have h : (fun i d r => ((b.baseChange K).map e.toLinearEquiv).repr
      ⁅((b.baseChange K).map e.toLinearEquiv) i, ((b.baseChange K).map e.toLinearEquiv) d⁆ r) =
      fun i d r => algebraMap k K (b.repr ⁅b i, b d⁆ r) :=
    funext fun i => funext fun d => funext fun r => scalar_bracket_constants b e i d r
  rw [h]
  rfl

set_option maxHeartbeats 1200000 in
private theorem adjointFactor_isIso (G A L : AffineAlgebraicGroup ℝ)
    (P : SplitBorelPair (AlgebraicClosure ℝ)) (hP : P.G = GeometricGroup G)
    (D : AttachedDatum P) (hF : letI := D.comm;
      HasDynkinType (integralCartan D.datum.rootDatum D.base) .F4)
    (hG : IsSemisimple G) (f : G.val ⟶ A.val) (j : A.val ⟶ L.val)
    (hf : IsClosedImmersion (f ≫ j).hom.hom.left)
    (hcomp : Specs.AdjointLieAutomorphisms.IsGeometricIdentityComponent f)
    {I : Type} [Fintype I] [DecidableEq I] (s : IdentityLieStructure G.val)
    (b : letI := s.lieRing; letI := s.lieAlgebra; Module.Basis I ℝ (Lie ℝ G.val))
    (T : letI := s.lieRing; letI := s.lieAlgebra; TangentCoordinates G.val I b)
    (l : (groupPointsFunctor ℝ).obj L.val ≅ generalLinearPoints ℝ I)
    (hRep : letI := s.lieRing; letI := s.lieAlgebra;
      RepresentsBracketAutomorphisms (fun i d r => b.repr ⁅b i, b d⁆ r) j l)
    (hAct : ScalarExtension s b T l (f ≫ j)) :
    IsIso f := by
  letI := s.lieRing
  letI := s.lieAlgebra
  let K := AlgebraicClosure ℝ
  let GK := GeometricGroup G
  let AK := GeometricGroup A
  let LK := GeometricGroup L
  let fK := (groupBaseChange ℝ K).map f
  let jK := (groupBaseChange ℝ K).map j
  let lK := extendMatrixPoints (K := K) l
  have hGK : IsSemisimple GK :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := K) G hG.1 hG.2.1).mpr hG
  obtain ⟨sK⟩ := identityLieBracket K GK
  letI : LieRing (Lie K ((groupBaseChange ℝ K).obj G.val)) := sK.lieRing
  letI : LieAlgebra K (Lie K ((groupBaseChange ℝ K).obj G.val)) := sK.lieAlgebra
  obtain ⟨e, TK, _, _, hK⟩ := hAct K sK
  let bK := (b.baseChange K).map e.toLinearEquiv
  have hC : IsClosedImmersion f.hom.hom.left := by
    letI := hRep.1
    letI : IsClosedImmersion (f.hom.hom.left ≫ j.hom.hom.left) := hf
    exact IsClosedImmersion.of_comp_isClosedImmersion f.hom.hom.left j.hom.hom.left
  have houter : ∀ a : RelativeAut GK.val (𝟙_ (SchemeOver K)),
      ∃ g : (𝟙_ (SchemeOver K)) ⟶ GK.val.X, a = innerAut g := by
    rw [show GK = P.G from hP.symm]
    exact automorphism_is_inner P D (hP.symm ▸ hGK) hF
  refine isIso_of_scalarExtension K f ?_
  change IsIso fK
  refine component_isFull GK AK LK hGK fK jK
    (baseChangeClosedSubgroup ℝ K f hC) (baseChangeClosedSubgroup ℝ K j hRep.1)
    hcomp.2 houter sK bK TK lK ?_ ?_
  · intro R g v
    have he : (groupBaseChange ℝ K).map (f ≫ j) = fK ≫ jK :=
      CategoryTheory.Functor.map_comp _ _ _
    rw [he] at hK
    exact hK R g v
  · intro a
    let R := CommAlgCat.of K K
    let R₀ := (restrictTestAlgebra ℝ K).obj R
    let M := (lK.hom.app R).hom (((groupPointsFunctor K).map jK).app R a)
    apply (extendedBracket b e M).mpr
    apply (hRep.2 R₀ M).mpr
    refine ⟨baseChangePoint ℝ K A.val.X R a, ?_⟩
    have hh := baseChangePointsSchemeNaturality ℝ K j.hom.hom R a
    exact congrArg (l.hom.app R₀).hom hh.symm


private theorem extendRealPoint_isEmbedding {G : AffineAlgebraicGroup ℝ}
    (i : MatrixRealization G) :
    IsEmbedding (fun p : PointsIn i ℝ => (show PointsIn i ℂ from mapPoints realCoefficients p)) := by
  let matrixR (p : PointsIn i ℝ) := (asMatrix i ℝ p).val
  let matrixC (p : PointsIn i ℂ) := (asMatrix i ℂ p).val
  have hr : IsEmbedding matrixR :=
    glVal_isEmbedding.comp (asMatrix_isClosedEmbedding i ℝ).isEmbedding
  have hc : IsEmbedding matrixC :=
    glVal_isEmbedding.comp (asMatrix_isClosedEmbedding i ℂ).isEmbedding
  let e (M : Matrix (Index i.size) (Index i.size) ℝ) :
      Matrix (Index i.size) (Index i.size) ℂ :=
    fun a d => Complex.ofReal (M a d)
  have he : IsEmbedding e :=
    IsEmbedding.piMap fun _ => IsEmbedding.piMap fun _ => Complex.isometry_ofReal.isEmbedding
  have h : matrixC ∘ (fun p : PointsIn i ℝ => (show PointsIn i ℂ from
      mapPoints realCoefficients p)) = e ∘ matrixR := by
    funext p
    exact congrArg Units.val (asMatrix_extendRealPoint i p)
  refine ⟨(hc.isInducing.of_comp_iff).mp (h.symm ▸ (he.comp hr).isInducing), ?_⟩
  intro x y hh
  exact (he.comp hr).injective (by rw [← h]; exact congrArg matrixC hh)

private def matrixReindexHomeomorph {I J : Type} (e : I ≃ J) :
    Matrix I I ℂ ≃ₜ Matrix J J ℂ :=
  { Matrix.reindex e e with
    continuous_toFun := continuous_matrix fun a d => (continuous_apply (e.symm d)).comp
      (continuous_apply (e.symm a))
    continuous_invFun := continuous_matrix fun a d => (continuous_apply (e d)).comp
      (continuous_apply (e a)) }

/-- A bijective matrix realization of the complex Lie automorphisms gives
both point comparisons, with the topologies induced by matrix entries. -/
private theorem compareMatrixPoints {G : AffineAlgebraicGroup ℝ} (i iAd : MatrixRealization G)
    {L : Type} [LieRing L] [LieAlgebra ℂ L]
    (B : Module.Basis (Index iAd.size) ℂ L) (σ : Conjugation L)
    (hf : ∀ j, σ.map (B j) = B j)
    (hfull : (asMatrix iAd ℂ).range = (automorphismMatrix B).range) :
    let b := B.reindex Equiv.ulift
    letI := coordinateTopology b
    ∃ (eC : PointsIn iAd ℂ ≃ₜ* (L ≃ₗ⁅ℂ⁆ L))
      (eR : PointsIn i ℝ ≃ₜ fixedAutomorphisms σ),
      (∀ g, automorphismMatrix B (eC g) = asMatrix iAd ℂ g) ∧
      ∀ g, (eR g).val = eC (mapPoints realCoefficients g) := by
  let p := asMatrix iAd ℂ
  let J := automorphismMatrix B
  let b := B.reindex Equiv.ulift
  letI := coordinateTopology b
  let eC : PointsIn iAd ℂ ≃* (L ≃ₗ⁅ℂ⁆ L) :=
    (MonoidHom.ofInjective (asMatrix_isClosedEmbedding iAd ℂ).isEmbedding.injective).trans
      ((MulEquiv.subgroupCongr hfull).trans
        (MonoidHom.ofInjective (automorphismMatrix_injective B)).symm)
  have hC (g : PointsIn iAd ℂ) : J (eC g) = p g := by
    change J ((MonoidHom.ofInjective (automorphismMatrix_injective B)).symm _) = _
    rw [MonoidHom.apply_ofInjective_symm]
    rfl
  let r := matrixReindexHomeomorph (Equiv.ulift : Index iAd.size ≃ Fin iAd.size)
  have hp : IsInducing (fun g : PointsIn iAd ℂ => r (p g).val) :=
    r.isInducing.comp (glVal_isEmbedding.comp
      (asMatrix_isClosedEmbedding iAd ℂ).isEmbedding).isInducing
  have hJ : IsInducing (fun f : L ≃ₗ⁅ℂ⁆ L => r (J f).val) := by
    have h : (fun f : L ≃ₗ⁅ℂ⁆ L => r (J f).val) =
        fun f => fun a d : Fin iAd.size => b.repr (f (b d)) a := by
      funext f a d
      change (J f).val (ULift.up a) (ULift.up d) = b.repr (f (b d)) a
      rw [automorphismMatrix_entry, Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
      rfl
    rw [h]
    exact .induced _
  have htop : IsInducing eC := by
    apply hJ.of_comp_iff.mp
    have h : (fun f => r (J f).val) ∘ eC = fun g => r (p g).val :=
      funext fun g => congrArg (fun M : Matrix.GeneralLinearGroup (Index iAd.size) ℂ =>
        r M.val) (hC g)
    rw [h]
    exact hp
  let e : PointsIn iAd ℂ ≃ₜ* (L ≃ₗ⁅ℂ⁆ L) :=
    { eC, eC.toEquiv.toHomeomorphOfIsInducing htop with }
  let extR (g : PointsIn i ℝ) : PointsIn iAd ℂ :=
    mapPoints realCoefficients (AdelicGroups.changePoints i iAd ℝ g)
  have hreal (g : PointsIn iAd ℂ) :
      (∃ x : PointsIn i ℝ, extR x = g) ↔ Intertwines σ σ (eC g) := by
    rw [intertwines_iff_realMatrix B σ hf, hC, ← realPoint_iff_realEntries]
    rfl
  let e0 (g : PointsIn i ℝ) : fixedAutomorphisms σ :=
    ⟨eC (extR g), (hreal _).mp ⟨g, rfl⟩⟩
  let changeI := AdelicGroups.changePoints i iAd ℝ
  let changeHomeomorph : PointsIn i ℝ ≃ₜ PointsIn iAd ℝ :=
    { changeI.toEquiv with
      continuous_toFun := AdelicGroups.continuous_changePoints i iAd ℝ
      continuous_invFun := AdelicGroups.continuous_changePoints iAd i ℝ }
  have hchange : IsEmbedding changeI := changeHomeomorph.isEmbedding
  have he0 : IsEmbedding e0 :=
    IsEmbedding.subtypeVal.of_comp_iff.mp
      (e.toHomeomorph.isEmbedding.comp ((extendRealPoint_isEmbedding iAd).comp hchange))
  have hsurj : Function.Surjective e0 := by
    intro z
    let g := eC.symm z.val
    have hg : eC g = z.val := eC.apply_symm_apply _
    obtain ⟨x, hx⟩ := (hreal g).mpr (hg ▸ z.property)
    exact ⟨x, Subtype.ext ((congrArg eC hx).trans hg)⟩
  let eR := (Equiv.ofBijective e0 ⟨he0.injective, hsurj⟩).toHomeomorphOfIsInducing
    he0.isInducing
  exact ⟨e, eR, hC, fun _ => rfl⟩


private abbrev complexTest := CommAlgCat.of ℂ ℂ
private abbrev restrictedComplexTest := (restrictTestAlgebra ℝ ℂ).obj complexTest

private def standardComplexTestMap : restrictedComplexTest ⟶ CommAlgCat.of ℝ ℂ :=
  CommAlgCat.ofHom {
    toRingHom := RingHom.id ℂ
    commutes' := fun _ => rfl }

set_option maxHeartbeats 1600000 in
/-- The actual complex base change of a real semisimple group of type F₄
is the full complex adjoint automorphism group. Real coefficient extension
identifies the real points with the conjugation-fixed subgroup. -/
theorem adjointPointComparison :
    Specs.RealF4AdjointPointComparison.AdjointPointComparison := by
  classical
  intro G i hG P hP D hF
  dsimp only
  have hGC := complexSemisimple G hG
  refine ⟨hGC, complexBorelPair G hG P hP D hF, ?_⟩
  obtain ⟨Z, Q, q, hq, _, _, _, s, n, br, T, V, l, A, jA, p, hRep, hpj, hp, _, hSc, _, _⟩ :=
    AdjointLieAutomorphisms.adjointRealization G hG
  letI := s.lieRing
  letI := s.lieAlgebra
  let f := q ≫ p
  letI : IsIso q := adjointProjection_isIso G Z q hq (realCentreIsTrivial G hG P hP D hF Z hq.1)
  have hfcl : IsClosedImmersion (f ≫ jA).hom.hom.left := by
    rw [show f ≫ jA = q ≫ (p ≫ jA) from Category.assoc _ _ _]
    let F := Grp.forget (SchemeOver ℝ) ⋙ Over.forget (Spec (CommRingCat.of ℝ))
    letI : IsIso q.hom.hom.left := inferInstanceAs (IsIso (F.map q))
    letI := hpj
    change IsClosedImmersion (q.hom.hom.left ≫ (p ≫ jA).hom.hom.left)
    infer_instance
  have hfgeo : Specs.AdjointLieAutomorphisms.IsGeometricIdentityComponent f := by
    let K := AlgebraicClosure ℝ
    let F := groupBaseChange ℝ K
    let U := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
    have hm : U.map (F.map f) = U.map (F.map q) ≫ U.map (F.map p) := by
      simp only [f, CategoryTheory.Functor.map_comp]
    change IsOpenImmersion (U.map (F.map f)) ∧
      Set.range (U.map (F.map f)) = connectedComponent (groupIdentityPoint (F.obj A.val))
    rw [hm]
    letI : IsIso (U.map (F.map q)) := inferInstance
    letI : IsOpenImmersion (U.map (F.map p)) := hp.1
    refine ⟨inferInstance, ?_⟩
    change Set.range ((U.map (F.map p)) ∘ (U.map (F.map q))) = _
    have hsurj : Function.Surjective (U.map (F.map q)) :=
      (U.map (F.map q)).homeomorph.surjective
    rw [Set.range_comp, hsurj.range_eq, Set.image_univ]
    exact hp.2
  have hAct : ScalarExtension s br T l (f ≫ jA) := by
    simpa only [f, Category.assoc] using hSc
  letI : IsIso f :=
    adjointFactor_isIso G A V P hP D hF hG f jA hfcl hfgeo s br T l hRep hAct
  let iAd : MatrixRealization G := ⟨n, V, l, f ≫ jA, hfcl⟩
  obtain ⟨h, j, _, ePoints, hPoints, _⟩ :=
    ArchimedeanLieChart.baseChangeMatrixComparison ℝ ℂ G iAd
  obtain ⟨sC⟩ := identityLieBracket ℂ (complexGroup G)
  letI : LieRing (Lie ℂ ((groupBaseChange ℝ ℂ).obj G.val)) := sC.lieRing
  letI : LieAlgebra ℂ (Lie ℂ ((groupBaseChange ℝ ℂ).obj G.val)) := sC.lieAlgebra
  obtain ⟨e, TK, he, _, hAdj⟩ := hAct ℂ sC
  let B := (br.baseChange ℂ).map e.toLinearEquiv
  let σ := (coefficientConjugation (Lie ℝ G.val)).transport e
  have hB (k : Index iAd.size) : σ.map (B k) = B k := by
    have hb : B k = e (1 ⊗ₜ[ℝ] br k) := by
      change ((br.baseChange ℂ).map e.toLinearEquiv) k = _
      rw [Module.Basis.map_apply, Module.Basis.baseChange_apply]
      rfl
    rw [hb, transportedConjugation_apply]
    simp [coefficientConjugation]
  have hMatrix (g : PointsIn iAd ℂ) :
      asMatrix iAd ℂ g = ((l.hom.app (CommAlgCat.of ℝ ℂ)).hom
        (((groupPointsFunctor ℝ).map jA).app (CommAlgCat.of ℝ ℂ)
          (((groupPointsFunctor ℝ).map f).app (CommAlgCat.of ℝ ℂ) g))) := by
    change ((l.hom.app _).hom (((groupPointsFunctor ℝ).map (f ≫ jA)).app _ g)) = _
    rw [CategoryTheory.Functor.map_comp, NatTrans.comp_app, GrpCat.comp_apply]
  have hfull : (asMatrix iAd ℂ).range = (automorphismMatrix B).range := by
    ext M
    have hbr : PreservesBracket (fun a d r => B.repr ⁅B a, B d⁆ r) (RingHom.id ℂ) M ↔
        PreservesBracket (fun a d r => br.repr ⁅br a, br d⁆ r) (algebraMap ℝ ℂ) M :=
      extendedBracket br e M
    refine Iff.trans ?_ (hbr.symm.trans (preservesBracket_iff_matrixOfLieAut B M))
    constructor
    · rintro ⟨g, rfl⟩
      exact (hRep.2 _ _).mpr ⟨_, (hMatrix g).symm⟩
    · intro hM
      obtain ⟨a, ha⟩ := (hRep.2 (CommAlgCat.of ℝ ℂ) M).mp hM
      obtain ⟨g, rfl⟩ := (ConcreteCategory.bijective_of_isIso
        (((groupPointsFunctor ℝ).map f).app (CommAlgCat.of ℝ ℂ))).2 a
      exact ⟨g, (hMatrix g).trans ha⟩
  obtain ⟨eC, eR, hC, hR⟩ := compareMatrixPoints i iAd B σ hB hfull
  let b := B.reindex Equiv.ulift
  letI := coordinateTopology b
  let aC := ePoints.trans eC
  have hcomp (g : PointsIn j ℂ) :
      ePoints g = mapPoints standardComplexTestMap
        (baseChangePoint ℝ ℂ G.val.X complexTest g) := by
    apply Over.OverMorphism.ext
    change _ = ((testSpec ℝ).map standardComplexTestMap.op).left ≫ _
    have hmap : ((testSpec ℝ).map standardComplexTestMap.op).left = 𝟙 _ :=
      Scheme.Spec.map_id _
    rw [hmap, Category.id_comp]
    exact hPoints g
  let adjMatrix (g : PointsIn j ℂ) := (l.hom.app restrictedComplexTest).hom
    (baseChangePoint ℝ ℂ V.val.X complexTest
      (((groupPointsFunctor ℂ).map ((groupBaseChange ℝ ℂ).map (f ≫ jA))).app complexTest g))
  have hCMatrix (g : PointsIn j ℂ) : asMatrix iAd ℂ (ePoints g) = adjMatrix g := by
    let n := ((groupPointsFunctor ℝ).map (f ≫ jA)) ≫ l.hom
    have hnat := ConcreteCategory.congr_hom (n.naturality standardComplexTestMap)
      (baseChangePoint ℝ ℂ G.val.X complexTest g)
    rw [hcomp]
    change _ = (l.hom.app restrictedComplexTest).hom
      (baseChangePoint ℝ ℂ V.val.X complexTest
        (g ≫ (baseChange ℝ ℂ).map (f ≫ jA).hom.hom))
    rw [baseChangePointsSchemeNaturality]
    change _ = (n.app restrictedComplexTest).hom _
    exact hnat.trans (by
      change Matrix.GeneralLinearGroup.map (RingHom.id ℂ)
        ((n.app restrictedComplexTest).hom _) = _
      rw [Matrix.GeneralLinearGroup.map_id, MonoidHom.id_apply])
  obtain ⟨hfin, hss⟩ := Representation.SemisimplyDifferentiated.lieSemisimple
    (complexGroup G) hGC sC
  refine ⟨j, s, sC, hfin, hss, e, σ, n, b, he, ?_, ⟨aC.toMulEquiv, eR, ?_, ?_, ?_, ?_⟩⟩
  · intro z
    exact transportedConjugation_apply _ e z
  · exact aC.continuous_toFun
  · exact aC.symm.continuous_toFun
  · intro g v
    have h := automorphismMatrix_mulVec B (aC g) v
    change (automorphismMatrix B (eC (ePoints g))).val *ᵥ B.equivFun v =
      B.equivFun (aC g v) at h
    rw [hC, hCMatrix] at h
    have hc := hAdj complexTest g (B.equivFun v)
    change ((TK.equiv complexTest) ((adjMatrix g).val *ᵥ B.equivFun v)).toMul.val =
      conjugate g ((TK.equiv complexTest) (B.equivFun v)) at hc
    have hv : TK.equiv complexTest (B.equivFun v) = v := Subtype.ext (TK.at_base v)
    rw [h, hv] at hc
    exact (TK.at_base (aC g v)).symm.trans hc
  · intro gr gc hg
    change (eR gr).val = eC (ePoints gc)
    refine (hR gr).trans (congrArg eC ?_)
    rw [hcomp, hg]
    change (testSpec ℝ).map realCoefficients.op ≫ gr =
      (testSpec ℝ).map standardComplexTestMap.op ≫
        ((testSpec ℝ).map (CommAlgCat.ofHom (Algebra.ofId ℝ restrictedComplexTest)).op ≫ gr)
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, ← op_comp]
    rfl

end LinearAlgebraicGroups.Arithmetic.RealF4AdjointPointComparison
