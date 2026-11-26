import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalLieAutomorphismTransport
import LinearAlgebraicGroups.Arithmetic.AdjointLieAutomorphisms
import LinearAlgebraicGroups.Representation.LieIntegration
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Matrix
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompactConjugation
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Matrix TensorProduct CategoryTheory.MonObj CategoryTheory.GrpObj

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalLieAutomorphismTransport

open LinearAlgebraicGroups.Specs
open Specs.ExceptionalLieAutomorphismTransport
open Specs.AdjointRepresentation (TangentCoordinates dualMap dualRestriction)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open LieAlgebrasAndRepresentations.RealForms

noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

private def transportConjugation {U V : Type} [LieRing U] [LieAlgebra ℂ U]
    [LieRing V] [LieAlgebra ℂ V] (e : U ≃ₗ⁅ℂ⁆ V) (σ : Conjugation U) : Conjugation V where
  map := {
    toFun := fun x => e (σ.map (e.symm x))
    map_add' := fun x y => by simp
    map_smul' := fun r x => by
      change e (σ.map (e.symm ((r : ℂ) • x))) = (r : ℂ) • e (σ.map (e.symm x))
      rw [map_smul, σ.antilinear, Complex.star_def, Complex.conj_ofReal, map_smul]
    map_lie' := fun {x y} => by
      rw [e.symm.map_lie, σ.map.map_lie, e.map_lie] }
  antilinear r x := by
    change e (σ.map (e.symm (r • x))) = star r • e (σ.map (e.symm x))
    rw [map_smul, σ.antilinear, map_smul]
  involutive x := by
    change e (σ.map (e.symm (e (σ.map (e.symm x))))) = x
    rw [LieEquiv.symm_apply_apply, σ.involutive, LieEquiv.apply_symm_apply]

private theorem tensorCoefficientConjugation_tmul
    {U : Type} [LieRing U] [LieAlgebra ℝ U] (c : ℂ) (u : U) :
    coefficientConjugationMap U (c ⊗ₜ[ℝ] u) = (star c) ⊗ₜ[ℝ] u := rfl

private def tensorConjugation (U : Type) [LieRing U] [LieAlgebra ℝ U] :
    Conjugation (ℂ ⊗[ℝ] U) where
  map := coefficientConjugationMap U
  antilinear r x := by
    induction x using TensorProduct.inductionOn with
    | tmul c u =>
      change coefficientConjugationMap U ((r * c) ⊗ₜ[ℝ] u) =
        (star r * (Complex.conjAe c)) ⊗ₜ[ℝ] u
      change coefficientConjugationMap U ((r * c) ⊗ₜ[ℝ] u) = (star r * star c) ⊗ₜ[ℝ] u
      rw [tensorCoefficientConjugation_tmul, star_mul, mul_comm]
    | add x y hx hy => simp [smul_add, hx, hy]
  involutive x := by
    induction x using TensorProduct.inductionOn with
    | tmul c u =>
      rw [tensorCoefficientConjugation_tmul, tensorCoefficientConjugation_tmul, star_star]
    | add x y hx hy => simp [hx, hy]

private theorem tensorConjugation_basis {U : Type} [LieRing U] [LieAlgebra ℝ U]
    {idx : Type} [Fintype idx] (b : Module.Basis idx ℝ U) (x : ℂ ⊗[ℝ] U) :
    (b.baseChange ℂ).equivFun ((tensorConjugation U).map x) =
      fun i => star ((b.baseChange ℂ).equivFun x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul c u =>
    funext i
    simp only [tensorConjugation, tensorCoefficientConjugation_tmul, Module.Basis.equivFun_apply,
      Module.Basis.baseChange_repr_tmul]
    change (b.repr u i : ℂ) * star c = star ((b.repr u i : ℂ) * c)
    rw [star_mul, Complex.star_def, Complex.conj_ofReal, mul_comm]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]
    funext i
    rw [map_add]
    exact (star_add _ _).symm

private theorem groundFieldConjugationInBasis
    (G : AffineAlgebraicGroup ℝ) (s : IdentityLieStructure G.val)
    (sC : IdentityLieStructure (complexGroup G)) {idx : Type} [Fintype idx] [DecidableEq idx]
    (b : letI := s.lieRing; letI := s.lieAlgebra; Module.Basis idx ℝ (Lie ℝ G.val))
    (T : letI := s.lieRing; letI := s.lieAlgebra; TangentCoordinates G.val idx b) :
    letI := s.lieRing; letI := s.lieAlgebra
    letI := sC.lieRing; letI := sC.lieAlgebra
    ∀ (e : (ℂ ⊗[ℝ] Lie ℝ G.val) ≃ₗ⁅ℂ⁆ Lie ℂ (complexGroup G))
      (TC : TangentCoordinates (complexGroup G) idx ((b.baseChange ℂ).map e.toLinearEquiv)),
      (∀ v : idx → ℂ,
        mapPoints (dualRestriction (k := ℝ) ℂ complexPointsAlgebra).hom
          (onDual G (TC.equiv complexPointsAlgebra v).toMul.val) =
          (T.equiv realPointsAlgebra v).toMul.val) →
      ∃ σ : Conjugation (Lie ℂ (complexGroup G)), IsGroundFieldConjugation G sC σ := by
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := sC.lieRing
  letI := sC.lieAlgebra
  intro e TC hcomp
  let σ := transportConjugation e (tensorConjugation (Lie ℝ G.val))
  refine ⟨σ, ?_⟩
  let bC := (b.baseChange ℂ).map e.toLinearEquiv
  have hσ (x : Lie ℂ (complexGroup G)) :
      bC.equivFun (σ.map x) = fun i => star (bC.equivFun x i) := by
    change bC.equivFun (e ((tensorConjugation (Lie ℝ G.val)).map (e.symm x))) = _
    simp only [bC, Module.Basis.map_equivFun, LinearEquiv.trans_apply]
    change (b.baseChange ℂ).equivFun (e.symm (e _)) = fun i =>
      star ((b.baseChange ℂ).equivFun (e.symm x) i)
    rw [LieEquiv.symm_apply_apply, tensorConjugation_basis]
  have ht (x : Lie ℂ (complexGroup G)) :
      mapPoints (dualRestriction (k := ℝ) ℂ complexPointsAlgebra).hom (onDual G x.toMul.val) =
        (T.equiv realPointsAlgebra (bC.equivFun x)).toMul.val := by
    rw [← TC.at_base x]
    exact hcomp _
  intro x
  let d := dualRestriction (k := ℝ) ℂ complexPointsAlgebra
  apply (show Function.Injective (mapPoints (X := G.val.X) d.hom) from fun p q h => by
    exact (cancel_epi ((testSpec ℝ).map d.hom.op)).mp h)
  change mapPoints d.hom (onDual G (σ.map x).toMul.val) =
    mapPoints d.hom (mapPoints dualConjugation (onDual G x.toMul.val))
  rw [ht, hσ]
  have h := T.naturality coefficientConjugation (bC.equivFun x)
  change (T.equiv realPointsAlgebra (fun i => star (bC.equivFun x i))).toMul.val =
    mapPoints (dualMap coefficientConjugation) (T.equiv realPointsAlgebra (bC.equivFun x)).toMul.val at h
  rw [h, ← ht]
  have hc : dualConjugation ≫ d.hom = d.hom ≫ dualMap coefficientConjugation := by
    change (d.hom ≫ dualMap coefficientConjugation ≫ d.inv) ≫ d.hom = _
    simp
  simp only [mapPoints, ← Category.assoc, ← Functor.map_comp, ← op_comp, hc]
  rfl

/-- Coefficientwise conjugation on dual numbers induces the real form on the
identity Lie algebra of the actual complex base change. -/
theorem groundFieldConjugation : GroundFieldConjugationStatement := by
  intro G sC
  let s := identityLieStructure G
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := sC.lieRing
  letI := sC.lieAlgebra
  obtain ⟨_, b, T, _, l, Ad, _, _, hscalar⟩ := adjointRepresentation ℝ G s
  obtain ⟨e, TC, _, he, _⟩ := hscalar ℂ sC
  exact groundFieldConjugationInBasis G s sC b T e TC (he complexPointsAlgebra)

/-- The compact form and polar intertwiner for the Lie algebra of the actual
complex algebraic group with its ground-field real structure. -/
theorem liePolarReduction : LiePolarStatement := by
  intro G hG s
  letI := s.lieRing
  letI := s.lieAlgebra
  let H := baseChangedAlgebraicGroup ℂ G
  have hH : GeometricRadicals.IsSemisimple H :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension G hG.1 hG.2.1).mpr hG
  let L := Lie ℂ (complexGroup G)
  letI : LieRing L := s.lieRing
  letI : LieAlgebra ℂ L := s.lieAlgebra
  letI : AddCommMonoid L := s.lieRing.toAddCommGroup.toAddCommMonoid
  letI : Module ℂ L := s.lieAlgebra.toModule
  have h' := Representation.SemisimplyDifferentiated.lieSemisimple H hH s
  change FiniteDimensional ℂ L ∧ _ at h'
  obtain ⟨hfin, hss⟩ := h'
  letI : FiniteDimensional ℂ L := hfin
  obtain ⟨σ, hσ⟩ := groundFieldConjugation G s
  open _root_.LieAlgebrasAndRepresentations.CompactConjugation in
  obtain ⟨_, _, a, ha, hInv, hNeg, _, _, _⟩ := exists_compact_conjugation (L := L) hss
  let ω : Conjugation L :=
    { map := {
        toFun := a
        map_add' := a.map_add
        map_smul' := fun r x => by
          have h := a.map_smulₛₗ (r : ℂ) x
          rw [show (starRingEnd ℂ) (r : ℂ) = (r : ℂ) from Complex.conj_ofReal r] at h
          exact h
        map_lie' := fun {x y} => ha x y }
      antilinear := fun r x => a.map_smulₛₗ r x
      involutive := hInv }
  have hω : _root_.Specs.LieAlgebrasAndRepresentations.PolarRealStructures.IsCompact ω := hNeg
  obtain ⟨_, θ, hcomm, hθ, c, _, _, hc⟩ :=
    _root_.LieAlgebrasAndRepresentations.PolarRealStructures.polar_reduction ω hω σ
  exact ⟨σ, ω, θ, c, hσ, hω, hθ, fun x => (hcomm x).symm, fun x => (hc x).symm⟩


section AlgebraicLifting

open Specs.GeometricRadicals (IsSemisimple)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.RootWeightAction (Representation)
open Specs.StandardGroups (generalLinearPoints)
open InfinitesimalCommutator (matrixDifferential)
open private pointIso from LinearAlgebraicGroups.Representation.InducedSocle
open private fromCoaction from LinearAlgebraicGroups.Representation.PrimitiveLine
open private realizes_fromCoaction from LinearAlgebraicGroups.Representation.SimpleClassification
open private pointActionDifferential pointActionDifferential_apply differentiated_matrix
  from LinearAlgebraicGroups.Representation.RationalHighestWeightComparison
open private schemePullback from LinearAlgebraicGroups.Descent.AdjointCocharacters
open private connectedOfGeometricallyConnected from LinearAlgebraicGroups.Reductive.CentralDerived
open private closedSubgroup_iso_of_surjective_tangent
  from LinearAlgebraicGroups.Arithmetic.AdjointLieAutomorphisms

variable {k : Type} [Field k] [CharZero k]

private theorem integral_of_semisimple (H : AffineAlgebraicGroup k) (hs : IsSemisimple H) :
    IsIntegral H.val.X.left := by
  letI := hs.2.1
  exact WordDomainGeometry.smoothConnectedGroupIntegral H hs.1
    (connectedOfGeometricallyConnected H hs.2.1)

/-- A homomorphism with differential in the tangent of a closed subgroup
factors through that subgroup when its source is connected in characteristic zero. -/
private theorem factor_of_differential
    (H N M : AffineAlgebraicGroup k) [IsIntegral H.val.X.left]
    (f : H.val ⟶ M.val) (j : N.val ⟶ M.val) (hj : IsClosedImmersion j.hom.hom.left)
    (b : Lie k H.val → Lie k N.val)
    (hb : ∀ x, mapPointKernel f x = mapPointKernel j (b x)) :
    ∃ a : H.val ⟶ N.val, a ≫ j = f ∧ ∀ x, mapPointKernel a x = b x := by
  let P := pullback f j
  let p : P ⟶ H.val := pullback.fst f j
  let q : P ⟶ N.val := pullback.snd f j
  have hpb : IsPullback p q f j := IsPullback.of_hasPullback f j
  have hp : IsClosedImmersion p.hom.hom.left :=
    MorphismProperty.of_isPullback (schemePullback hpb).flip hj
  let C : ClosedSubgroup H.val := ⟨P, p, hp⟩
  have hs : Function.Surjective (mapPointKernel p) := by
    intro x
    obtain ⟨z, hz, _⟩ := liePullbackComparison k hpb x (b x) (hb x)
    exact ⟨z, hz.1⟩
  letI : IsIso p := closedSubgroup_iso_of_surjective_tangent H C
    (characteristicZeroSmoothness k (Unipotent.closedSubgroupAlgebraicGroup C)) hs
  refine ⟨inv p ≫ q, ?_, ?_⟩
  · rw [Category.assoc, ← hpb.w, IsIso.inv_hom_id_assoc]
  · intro x
    let z := mapPointKernel (inv p) x
    have hpz : mapPointKernel p z = x := by
      rw [← (lieFunctoriality k).2.2, IsIso.inv_hom_id, (lieFunctoriality k).2.1]
    obtain ⟨w, ⟨hwp, hwq⟩, _⟩ := liePullbackComparison k hpb x (b x) (hb x)
    have hzw : z = w := by
      apply_fun mapPointKernel (inv p) at hpz hwp
      simpa only [← (lieFunctoriality k).2.2, IsIso.hom_inv_id, (lieFunctoriality k).2.1]
        using hpz.trans hwp.symm
    rw [(lieFunctoriality k).2.2]
    exact (congrArg (mapPointKernel q) hzw).trans hwq

private theorem integrateMatrixDifferential (H : AffineAlgebraicGroup k)
    (hs : IsSemisimple H) (hsc : GeometricallySimplyConnected H)
    {idx : Type} [Fintype idx] [DecidableEq idx]
    (M : AffineAlgebraicGroup k)
    (l : (groupPointsFunctor k).obj M.val ≅ generalLinearPoints k idx)
    (s : IdentityLieStructure H.val) :
    letI := s.lieRing; letI := s.lieAlgebra
    letI : LieRing (Matrix idx idx k) := LieRing.ofAssociativeRing
    letI : LieAlgebra k (Matrix idx idx k) := LieAlgebra.ofAssociativeAlgebra
    ∀ D : Lie k H.val →ₗ⁅k⁆ Matrix idx idx k,
      ∃ f : H.val ⟶ M.val, ∀ x, matrixDifferential f l x = D x := by
  intro D
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : LieRing (Matrix idx idx k) := LieRing.ofAssociativeRing
  letI : LieAlgebra k (Matrix idx idx k) := LieAlgebra.ofAssociativeAlgebra
  letI := LieRingModule.compLieHom (idx → k) D
  letI := LieModule.compLieHom (idx → k) D
  obtain ⟨A, e, δ, hδ⟩ :=
    Representation.LieIntegration.essentialSurjectivity H hs hsc s (idx → k)
  let ρ : Representation H.val idx := fromCoaction (pointIso e) (Pi.basisFun k idx) δ
  let E := groupHomEquiv H.val M.val H.property.1
  let f := E.symm (ρ ≫ l.inv)
  have hρ : (groupPointsFunctor k).map f ≫ l.hom = ρ := by
    change E f ≫ l.hom = ρ
    rw [E.apply_symm_apply, Category.assoc, l.inv_hom_id, Category.comp_id]
  refine ⟨f, fun x => ?_⟩
  have hmatrix : matrixDifferential f l x = pointActionDifferential s ρ x := by
    ext i j
    rw [pointActionDifferential_apply]
    exact congrArg (fun a : Representation H.val idx =>
      ((a.app (CommAlgCat.of k (DualNumber k)) x.toMul.val).val i j).snd) hρ
  rw [hmatrix]
  apply Matrix.ext_of_mulVec_single
  intro i
  have h := differentiated_matrix s e ρ δ (realizes_fromCoaction e _ δ) x (Pi.single i 1)
  exact h.symm.trans (hδ x (Pi.single i 1))

private theorem hom_eq_of_differential {H N : AffineAlgebraicGroup k}
    [IsIntegral H.val.X.left] {f g : H.val ⟶ N.val}
    (h : ∀ x, mapPointKernel f x = mapPointKernel g x) : f = g := by
  let p := equalizer.ι f g
  let U := Grp.forget (SchemeOver k)
  let e := PreservesEqualizer.iso U f g
  haveI : IsAffine N.val.X.left := N.property.1
  haveI : IsAffineHom N.val.X.hom := isAffineHom_of_isAffine _
  have hidx : e.inv ≫ p.hom.hom = equalizer.ι f.hom.hom g.hom.hom :=
    PreservesEqualizer.iso_inv_ι U f g
  have hp : IsClosedImmersion p.hom.hom.left := by
    letI : IsIso e.inv.left := (Over.forget (Spec (CommRingCat.of k))).map_isIso e.inv
    have h₀ : IsClosedImmersion (e.inv.left ≫ p.hom.hom.left) := by
      change IsClosedImmersion ((e.inv ≫ p.hom.hom).left)
      rw [hidx]
      infer_instance
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
      e.inv.left p.hom.hom.left).mp h₀
  let C : ClosedSubgroup H.val := ⟨equalizer f g, p, hp⟩
  have hs : Function.Surjective (mapPointKernel p) := by
    intro x
    have hx := congrArg (fun y : Lie k N.val => y.toMul.val) (h x)
    change x.toMul.val ≫ f.hom.hom = x.toMul.val ≫ g.hom.hom at hx
    let z := equalizer.lift x.toMul.val hx ≫ e.inv
    have hz : z ≫ p.hom.hom = x.toMul.val := by
      simp only [z, Category.assoc, hidx, equalizer.lift_ι]
    letI := hp
    letI : Mono p.hom.hom := Over.mono_of_mono_left _
    have hred : reduceTangentPoints C.group z = 1 := by
      apply (cancel_mono p.hom.hom).mp
      change mapPoints (dualReduction k) z ≫ p.hom.hom = 1 ≫ p.hom.hom
      rw [Category.assoc, hz, MonObj.one_comp]
      exact x.toMul.property
    exact ⟨⟨z, hred⟩, Subtype.ext hz⟩
  letI : IsIso p := closedSubgroup_iso_of_surjective_tangent H C
    (characteristicZeroSmoothness k (Unipotent.closedSubgroupAlgebraicGroup C)) hs
  exact (cancel_epi p).mp (equalizer.condition f g)

/-- Every automorphism of the Lie algebra of a simply connected
semisimple group in characteristic zero integrates to a unique
scheme automorphism. -/
private theorem liftLieAutomorphism (H : AffineAlgebraicGroup k)
    (hs : IsSemisimple H) (hsc : GeometricallySimplyConnected H)
    (s : IdentityLieStructure H.val) :
    letI := s.lieRing; letI := s.lieAlgebra
    ∀ b : Lie k H.val ≃ₗ⁅k⁆ Lie k H.val,
      ∃ a : Aut H.val, ∀ x, mapPointKernel a.asIso.hom x = b x := by
  intro b
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := integral_of_semisimple H hs
  obtain ⟨n, M, ⟨l⟩, j, hj⟩ := faithfulLinearization k H
  let idx := ULift.{0} (Fin n)
  let ρ : Representation H.val idx := (groupPointsFunctor k).map j ≫ l.hom
  letI : LieRing (Matrix idx idx k) := LieRing.ofAssociativeRing
  letI : LieAlgebra k (Matrix idx idx k) := LieAlgebra.ofAssociativeAlgebra
  let D := pointActionDifferential s ρ
  have hD (x : Lie k H.val) : D x = matrixDifferential j l x := by
    ext i l
    exact pointActionDifferential_apply s ρ x i l
  have hLift (d : Lie k H.val ≃ₗ⁅k⁆ Lie k H.val) :
      ∃ a : H.val ⟶ H.val, ∀ x, mapPointKernel a x = d x := by
    obtain ⟨f, hf⟩ := integrateMatrixDifferential H hs hsc M l s (D.comp d.toLieHom)
    letI : IsAffine H.val.X.left := H.property.1
    letI : IsAffine M.val.X.left := M.property.1
    have hi := (identityLieBracketMatrix k M.val M.val idx (𝟙 M.val) l
      (by change IsClosedImmersion (𝟙 M.val.X.left); infer_instance)).1
    have hcomp (x : Lie k H.val) : mapPointKernel f x = mapPointKernel j (d x) := by
      apply hi
      have he := (hf x).trans (hD (d x))
      exact he
    obtain ⟨a, _, ha⟩ := factor_of_differential H H M f j hj d hcomp
    exact ⟨a, ha⟩
  obtain ⟨f, hf⟩ := hLift b
  obtain ⟨g, hg⟩ := hLift b.symm
  have hinv : f ≫ g = 𝟙 H.val := hom_eq_of_differential (fun x => by
    rw [(lieFunctoriality k).2.2, hf, hg, (lieFunctoriality k).2.1, b.symm_apply_apply])
  have hinv' : g ≫ f = 𝟙 H.val := hom_eq_of_differential (fun x => by
    rw [(lieFunctoriality k).2.2, hf, hg, (lieFunctoriality k).2.1, b.apply_symm_apply])
  exact ⟨⟨f, g, hinv, hinv'⟩, hf⟩

end AlgebraicLifting

section ScalarExtension

open Specs.CentralIsogenies (IsCentralIsogeny)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.CentralFrobeniusDescent (IsCentral)
open private baseChangeMapPullback baseChangeKernelSquare from LinearAlgebraicGroups.Affine.Components
open private baseChange_central from LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private centralIsogeny_postIso isIso_of_scalarExtension
  from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private groupBaseChangeTower from LinearAlgebraicGroups.Reductive.RadicalBaseChange

private theorem isCentral_iff_centralizes {k : Type} [Field k] {S G : GroupScheme k}
    (i : S ⟶ G) : IsCentral i ↔ Centralizes (𝟙 G) i.hom.hom := by
  constructor
  · intro hi
    apply (centralizes_iff _ _).mpr
    intro U t g
    change Commute (t ≫ i.hom.hom) (g ≫ 𝟙 G.X)
    simpa only [Category.comp_id, Category.id_comp] using
      (((centralizes_iff _ _).mp (hi U g)) U (𝟙 U) t).symm
  · intro hi U g
    apply (centralizes_iff _ _).mpr
    intro V t s
    have h := ((centralizes_iff _ _).mp hi) V s (t ≫ g)
    change Commute (s ≫ i.hom.hom) ((t ≫ g) ≫ 𝟙 G.X) at h
    simpa only [Category.comp_id] using h.symm

private theorem centralIsogeny_baseExtension {k K : Type} [Field k] [Field K] [Algebra k K]
    {S G : GroupScheme k} (f : S ⟶ G) (hf : IsCentralIsogeny f) :
    IsCentralIsogeny ((groupBaseChange k K).map f) := by
  obtain ⟨hfin, hflat, hsurj, Z, hk, hc⟩ := hf
  let h := (baseChangeMapPullback (K := K) f.hom.hom).flip
  let ZK := GeometricRadicals.baseChangedSubgroup K Z
    (MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) Z.inclusion.hom.hom).flip
      Z.isClosedImmersion)
  exact ⟨MorphismProperty.of_isPullback h hfin,
    MorphismProperty.of_isPullback h hflat, MorphismProperty.of_isPullback h hsurj,
    ZK, baseChangeKernelSquare f Z.inclusion hk,
    (isCentral_iff_centralizes ZK.inclusion).mp
      (baseChange_central K ((isCentral_iff_centralizes Z.inclusion).mpr hc))⟩

/-- Geometric simple connectedness passes from the real group to its
complex scalar extension. -/
private theorem simplyConnected_complexBaseChange
    (G : AffineAlgebraicGroup ℝ) (hG : GeometricallySimplyConnected G) :
    GeometricallySimplyConnected (baseChangedAlgebraicGroup ℂ G) := by
  let K := AlgebraicClosure ℂ
  let F := AlgebraicClosure ℝ
  let e := IsAlgClosure.equiv ℝ K F
  letI : Algebra K F := e.toRingHom.toAlgebra
  letI : IsScalarTower ℝ K F := IsScalarTower.of_algebraMap_eq (fun r => (e.commutes r).symm)
  letI : Algebra ℂ F := ((algebraMap K F).comp (algebraMap ℂ K)).toAlgebra
  letI : IsScalarTower ℂ K F := IsScalarTower.of_algebraMap_eq' rfl
  intro J hJ f hf
  let JF := baseChangedAlgebraicGroup F J
  have hJF : GeometricRadicals.IsSemisimple JF :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension J hJ.1 hJ.2.1).mpr hJ
  let e₂ := ((groupBaseChangeTower (k := ℝ) (K := K) F).app G.val).symm
  let e₃ := ((groupBaseChangeTower (k := ℝ) (K := ℂ) K).app G.val).symm
  let d := (groupBaseChange K F).mapIso e₃ ≪≫ e₂
  let fF := (groupBaseChange K F).map f
  letI : IsIso (fF ≫ d.hom) := hG JF hJF _ (centralIsogeny_postIso d (centralIsogeny_baseExtension f hf))
  have hfF : IsIso fF := IsIso.of_isIso_comp_right _ d.hom
  exact isIso_of_scalarExtension F f hfF

end ScalarExtension

/-- Lift a Lie automorphism of the complex identity tangent to the
complex group scheme obtained from the original real group. -/
theorem liftComplexLieAutomorphism : LieLiftStatement := by
  intro G hG hsc s b
  let H := baseChangedAlgebraicGroup ℂ G
  have hH : GeometricRadicals.IsSemisimple H :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension G hG.1 hG.2.1).mpr hG
  exact liftLieAutomorphism H hH (simplyConnected_complexBaseChange G hsc) s b

section AdjointComparison

open Specs.AdjointRepresentation (GroupPoints)
open private scalar_bracket_constants from LinearAlgebraicGroups.Arithmetic.AdjointLieAutomorphisms

/-- A finite surjective morphism lifts points over an algebraically
closed field, via a closed point of its fiber. -/
private theorem surjective_points_of_finite {k K : Type} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed K] {X Y : SchemeOver k} (f : X ⟶ Y)
    (hfin : IsFinite f.left) (hsurj : AlgebraicGeometry.Surjective f.left) :
    Function.Surjective (fun x : Points X (CommAlgCat.of k K) => x ≫ f) := by
  intro y
  let P := pullback f.left y.left
  let π : P ⟶ Spec (CommRingCat.of K) := pullback.snd _ _
  have hp := IsPullback.of_hasPullback f.left y.left
  letI : IsFinite π := MorphismProperty.of_isPullback hp hfin
  have hπ : AlgebraicGeometry.Surjective π := MorphismProperty.of_isPullback hp hsurj
  have hne : (Set.univ : Set P).Nonempty :=
    ⟨(hπ.surj (IsLocalRing.closedPoint K)).choose, Set.mem_univ _⟩
  letI : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace π
  obtain ⟨z, _, hz⟩ := nonempty_inter_closedPoints hne isOpen_univ.isLocallyClosed
  let v := pointOfClosedPoint π z hz
  let x := v ≫ pullback.fst f.left y.left
  have he : x ≫ f.left = y.left := by
    change (v ≫ pullback.fst f.left y.left) ≫ f.left = y.left
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
  have hx : x ≫ X.hom = ((testSpec k).obj (Opposite.op (CommAlgCat.of k K))).hom := by
    rw [← Over.w f, ← Category.assoc, he, Over.w y]
  exact ⟨Over.homMk x hx, Over.OverMorphism.ext he⟩

set_option maxHeartbeats 800000 in
/-- The real adjoint quotient, presented by matrices acting on the actual
complex identity tangent. -/
theorem complexAdjointComparison : ComplexAdjointStatement := by
  intro G hG sC
  letI := sC.lieRing
  letI := sC.lieAlgebra
  obtain ⟨Z, Q, q, hq, hZ, hf, _, s, n, b, T, N, l, A, j, i, hj, hi, hcomp, _, hs, hd, _⟩ :=
    AdjointLieAutomorphisms.adjointRealization G hG
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : AddCommMonoid (Lie ℂ (complexGroup G)) := sC.lieRing.toAddCommGroup.toAddCommMonoid
  letI : Module ℂ (Lie ℂ (complexGroup G)) := sC.lieAlgebra.toModule
  obtain ⟨e, TC, _, _, hconj⟩ := hs ℂ sC
  let bC := (b.baseChange ℂ).map e.toLinearEquiv
  have hcentral : CentralIsogenies.IsCentralIsogeny q :=
    ⟨hf, hq.2.2.2.1, hq.2.2.2.2.1, Z, hq.2.1, (hq.1 _ _).mpr ⟨𝟙 _, Category.id_comp _⟩⟩
  refine ⟨Z, Q, q, n, N, A, i, j, l, bC, hq, hcentral, hZ, hi,
    hj.1, surjective_points_of_finite q.hom.hom hf hq.2.2.2.2.1, hcomp, ?_, ?_, ?_⟩
  · intro g x
    let v := bC.equivFun x
    let M := matrixPoint (i ≫ j) l (pointMap q (baseChangePoint ℝ ℂ G.val.X complexPointsAlgebra g))
    have hM :
        (l.hom.app ((restrictTestAlgebra ℝ ℂ).obj complexPointsAlgebra)).hom
          (baseChangePoint ℝ ℂ N.val.X complexPointsAlgebra
            (((groupPointsFunctor ℂ).map ((groupBaseChange ℝ ℂ).map (q ≫ i ≫ j))).app
              complexPointsAlgebra g)) = M := by
      change (l.hom.app realPointsAlgebra).hom
        (baseChangePoint ℝ ℂ N.val.X complexPointsAlgebra
          (g ≫ (baseChange ℝ ℂ).map (q ≫ i ≫ j).hom.hom)) = M
      rw [baseChangePointsSchemeNaturality]
      change (l.hom.app realPointsAlgebra).hom
        (baseChangePoint ℝ ℂ G.val.X complexPointsAlgebra g ≫
          q.hom.hom ≫ (i ≫ j).hom.hom) =
        (l.hom.app realPointsAlgebra).hom
          ((baseChangePoint ℝ ℂ G.val.X complexPointsAlgebra g ≫ q.hom.hom) ≫ (i ≫ j).hom.hom)
      rw [Category.assoc]
    have he := hconj complexPointsAlgebra g v
    change (TC.equiv complexPointsAlgebra (_ *ᵥ v)).toMul.val = _ at he
    rw [hM] at he
    have hv (w : ULift.{0} (Fin n) → ℂ) :
        TC.equiv complexPointsAlgebra w = bC.equivFun.symm w := by
      apply Subtype.ext
      change (TC.equiv complexPointsAlgebra w).toMul.val = (bC.equivFun.symm w).toMul.val
      have h := TC.at_base (bC.equivFun.symm w)
      change (TC.equiv complexPointsAlgebra (bC.equivFun (bC.equivFun.symm w))).toMul.val =
        (bC.equivFun.symm w).toMul.val at h
      rw [LinearEquiv.apply_symm_apply] at h
      exact h
    change (bC.equivFun.symm (M.val *ᵥ v)).toMul.val = AdjointRepresentation.conjugate g x
    rw [hv, hv, LinearEquiv.symm_apply_apply] at he
    exact he
  · intro y
    have he := hd realPointsAlgebra y
    have hcoeff : (fun r t u => bC.repr ⁅bC r, bC t⁆ u) =
        fun r t u => algebraMap ℝ ℂ (b.repr ⁅b r, b t⁆ u) := by
      funext r t u
      exact scalar_bracket_constants b e r t u
    rw [hcoeff]
    exact he
  · intro m
    have hcoeff : (fun r t u => bC.repr ⁅bC r, bC t⁆ u) =
        fun r t u => algebraMap ℝ ℂ (b.repr ⁅b r, b t⁆ u) := by
      funext r t u
      exact scalar_bracket_constants b e r t u
    rw [hcoeff]
    exact hj.2 realPointsAlgebra m

end AdjointComparison

section PointActions

open Specs.AdjointRepresentation (GroupPoints)

/-- On the original real functor of points, conjugating the coefficients twice
is the identity on the complex points. -/
private theorem realConjugation_involutive (G : AffineAlgebraicGroup ℝ) :
    Function.Involutive (realConjugation G) := by
  let F := (groupPointsFunctor ℝ).obj G.val
  have h : coefficientConjugation ≫ coefficientConjugation = 𝟙 realPointsAlgebra := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    exact star_star z
  intro x
  change (F.map coefficientConjugation).hom ((F.map coefficientConjugation).hom x) = x
  have hc : F.map coefficientConjugation ≫ F.map coefficientConjugation = 𝟙 _ :=
    (F.map_comp _ _).symm.trans ((congrArg F.map h).trans (F.map_id _))
  exact congrArg (fun f => GrpCat.Hom.hom f x) hc

private def pointAut (G : AffineAlgebraicGroup ℝ) (a : Aut (complexGroup G)) :
    MulAut (ComplexPoints G) := by
  let F := groupPointsFunctor ℂ ⋙ (evaluation (TestAlgebra ℂ) GrpCat).obj complexPointsAlgebra
  let e := F.mapIso a.asIso
  let b : MulAut (GroupPoints (complexGroup G) complexPointsAlgebra) :=
    { toFun := e.hom.hom
      invFun := e.inv.hom
      left_inv := fun x => congrArg (fun f => GrpCat.Hom.hom f x) e.hom_inv_id
      right_inv := fun x => congrArg (fun f => GrpCat.Hom.hom f x) e.inv_hom_id
      map_mul' := e.hom.hom.map_mul }
  let p := baseChangePointGroupEquiv ℂ G.val complexPointsAlgebra
  exact p.symm.trans (b.trans p)

private theorem pointAut_acts (G : AffineAlgebraicGroup ℝ) (a : Aut (complexGroup G)) :
    ActsOnComplexPoints G a (pointAut G a) := by
  intro z
  change (baseChangePointGroupEquiv ℂ G.val complexPointsAlgebra)
      (((groupPointsFunctor ℂ).map a.asIso.hom).app complexPointsAlgebra
        ((baseChangePointGroupEquiv ℂ G.val complexPointsAlgebra).symm
          (baseChangePointGroupEquiv ℂ G.val complexPointsAlgebra z))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

private def conjugationProduct {L : Type} [LieRing L] [LieAlgebra ℂ L]
    (a b : Conjugation L) : L ≃ₗ⁅ℂ⁆ L :=
  let f : L →ₗ⁅ℂ⁆ L :=
    { toFun := fun x => a.map (b.map x)
      map_add' := fun x y => by simp
      map_smul' := fun r x => by
        change a.map (b.map (r • x)) = r • a.map (b.map x)
        rw [b.antilinear, a.antilinear, star_star]
      map_lie' := fun {x y} => by rw [b.map.map_lie, a.map.map_lie] }
  LieEquiv.ofBijective f (a.involutive.bijective.comp b.involutive.bijective)


end PointActions

section CoefficientTwist

open private fieldAutomorphismSpec twist twistGroupBaseChangeIso twistBaseChangeIso
  scalarSchemeMap scalarSchemeMap_fst scalarSchemeMap_snd
  from LinearAlgebraicGroups.Reductive.RadicalBaseChange

private abbrev sigmaField := Complex.conjAe

private def coefficientTwist (G : AffineAlgebraicGroup ℝ) (a : Aut (complexGroup G)) :
    Aut (complexGroup G) :=
  Aut.autMulEquivOfIso ((twistGroupBaseChangeIso sigmaField).app G.val)
    (((twist sigmaField).mapGrp.mapAut (complexGroup G)) a)

private theorem coefficientSchemeMap_involutive (X : SchemeOver ℝ) :
    scalarSchemeMap sigmaField X ≫ scalarSchemeMap sigmaField X = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, scalarSchemeMap_fst, Category.id_comp]
  · have h : (fieldAutomorphismSpec sigmaField).hom ≫ (fieldAutomorphismSpec sigmaField).hom = 𝟙 _ := by
      change Spec.map (CommRingCat.ofHom sigmaField.toRingHom) ≫
        Spec.map (CommRingCat.ofHom sigmaField.toRingHom) = 𝟙 _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id, ← CommRingCat.ofHom_id]
      congr 2
      ext x
      exact star_star x
    rw [Category.assoc, scalarSchemeMap_snd, ← Category.assoc, scalarSchemeMap_snd,
      Category.assoc, h, Category.comp_id, Category.id_comp]

private theorem coefficientTwist_commutes (G : AffineAlgebraicGroup ℝ)
    (a : Aut (complexGroup G)) :
    a.asIso.hom.hom.hom.left ≫ scalarSchemeMap sigmaField G.val.X =
      scalarSchemeMap sigmaField G.val.X ≫ (coefficientTwist G a).asIso.hom.hom.hom.left := by
  let X := G.val.X
  let Y := (baseChange ℝ ℂ).obj X
  let S := (fieldAutomorphismSpec sigmaField).hom
  let e := (twistBaseChangeIso sigmaField).app X
  let f := a.asIso.hom.hom.hom
  let p := pullback.fst Y.hom S
  have hmap : ((twist sigmaField).map f).left ≫ p = p ≫ f.left :=
    pullback.lift_fst _ _ _
  have haux : (coefficientTwist G a).asIso.hom.hom.hom.left ≫ scalarSchemeMap sigmaField X =
      scalarSchemeMap sigmaField X ≫ f.left := by
    change (e.inv.left ≫ ((twist sigmaField).map f).left ≫ e.hom.left) ≫ (e.inv.left ≫ p) =
      (e.inv.left ≫ p) ≫ f.left
    let U := Over.forget (Spec (CommRingCat.of ℂ))
    have hi : e.hom.left ≫ e.inv.left = 𝟙 _ := (U.mapIso e).hom_inv_id
    simp only [Category.assoc, reassoc_of% hi, hmap]
  let b := scalarSchemeMap sigmaField X
  have hb : b ≫ b = 𝟙 _ := coefficientSchemeMap_involutive X
  change f.left ≫ b = _
  calc
    f.left ≫ b = b ≫ (b ≫ f.left) ≫ b := by simp [← Category.assoc, hb]
    _ = b ≫ ((coefficientTwist G a).asIso.hom.hom.hom.left ≫ b) ≫ b := by rw [haux]
    _ = b ≫ (coefficientTwist G a).asIso.hom.hom.hom.left ≫ (b ≫ b) := by
      simp only [Category.assoc]
    _ = b ≫ (coefficientTwist G a).asIso.hom.hom.hom.left := by
      rw [hb]
      exact congrArg (b ≫ ·) (Category.comp_id _)

private def conjugateTestPoint (G : AffineAlgebraicGroup ℝ) (R : TestAlgebra ℂ)
    (a : (restrictTestAlgebra ℝ ℂ).obj R ⟶ (restrictTestAlgebra ℝ ℂ).obj R)
    (x : Points (complexGroup G).X R) : Points (complexGroup G).X R :=
  (baseChangePointsEquiv ℂ G.val.X R).symm
    (mapPoints a (baseChangePoint ℝ ℂ G.val.X R x))

private theorem conjugateTestPoint_left (G : AffineAlgebraicGroup ℝ) (R : TestAlgebra ℂ)
    (a : (restrictTestAlgebra ℝ ℂ).obj R ⟶ (restrictTestAlgebra ℝ ℂ).obj R)
    (ha : ∀ z : ℂ, a.hom (algebraMap ℂ R z) = algebraMap ℂ R (sigmaField z))
    (x : Points (complexGroup G).X R) :
    (conjugateTestPoint G R a x).left =
      Spec.map (CommRingCat.ofHom a.hom.toRingHom) ≫ x.left ≫
        scalarSchemeMap sigmaField G.val.X := by
  let X := G.val.X
  let Y := (baseChange ℝ ℂ).obj X
  let P := (testSpec ℂ).obj (Opposite.op R)
  let S := (fieldAutomorphismSpec sigmaField).hom
  let f := Spec.map (CommRingCat.ofHom a.hom.toRingHom)
  have hf : f ≫ P.hom = P.hom ≫ S := by
    change f ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ R)) ≫ Spec.map (CommRingCat.ofHom sigmaField.toRingHom)
    simp only [f, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext z
    exact ha z
  have hS : S ≫ S = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom sigmaField.toRingHom) ≫
      Spec.map (CommRingCat.ofHom sigmaField.toRingHom) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id, ← CommRingCat.ofHom_id]
    congr 2
    ext x
    exact star_star x
  apply pullback.hom_ext
  · have h := (baseChangePointsEquiv ℂ X R).apply_symm_apply
      (mapPoints a (baseChangePoint ℝ ℂ X R x))
    have he := congrArg (fun p : Points X ((restrictTestAlgebra ℝ ℂ).obj R) => p.left) h
    change (conjugateTestPoint G R a x).left ≫ pullback.fst X.hom (fieldSpecMap ℝ ℂ) =
      f ≫ (x.left ≫ pullback.fst X.hom (fieldSpecMap ℝ ℂ)) at he
    simpa only [Category.assoc, scalarSchemeMap_fst] using he
  · change (conjugateTestPoint G R a x).left ≫ Y.hom =
      (f ≫ x.left ≫ scalarSchemeMap sigmaField X) ≫ Y.hom
    have hu : (conjugateTestPoint G R a x).left ≫ Y.hom = P.hom :=
      Over.w (conjugateTestPoint G R a x)
    have hx : x.left ≫ Y.hom = P.hom := Over.w x
    calc
      _ = P.hom := hu
      _ = (f ≫ P.hom) ≫ S := by rw [hf, Category.assoc, hS, Category.comp_id]
      _ = f ≫ (x.left ≫ Y.hom) ≫ S := by rw [hx, Category.assoc]
      _ = _ := by
        have hh : scalarSchemeMap sigmaField X ≫ Y.hom = Y.hom ≫ S :=
          scalarSchemeMap_snd sigmaField X
        simp only [Category.assoc, hh]

private theorem coefficientTwist_onTestPoints (G : AffineAlgebraicGroup ℝ) (R : TestAlgebra ℂ)
    (a : (restrictTestAlgebra ℝ ℂ).obj R ⟶ (restrictTestAlgebra ℝ ℂ).obj R)
    (ha : ∀ z : ℂ, a.hom (algebraMap ℂ R z) = algebraMap ℂ R (sigmaField z))
    (f : Aut (complexGroup G)) (x : Points (complexGroup G).X R) :
    conjugateTestPoint G R a (x ≫ f.asIso.hom.hom.hom) =
      conjugateTestPoint G R a x ≫ (coefficientTwist G f).asIso.hom.hom.hom := by
  apply Over.OverMorphism.ext
  rw [conjugateTestPoint_left G R a ha]
  change Spec.map (CommRingCat.ofHom a.hom.toRingHom) ≫
      (x.left ≫ f.asIso.hom.hom.hom.left) ≫ scalarSchemeMap sigmaField G.val.X =
    (conjugateTestPoint G R a x).left ≫ (coefficientTwist G f).asIso.hom.hom.hom.left
  rw [conjugateTestPoint_left G R a ha]
  simp only [Category.assoc, coefficientTwist_commutes]

private theorem coefficientTwist_onPoints (G : AffineAlgebraicGroup ℝ)
    (f : Aut (complexGroup G)) (x : ComplexPoints G) :
    realConjugation G (pointAut G f x) =
      pointAut G (coefficientTwist G f) (realConjugation G x) := by
  let P := baseChangePointsEquiv ℂ G.val.X complexPointsAlgebra
  let z := P.symm x
  let a : (restrictTestAlgebra ℝ ℂ).obj complexPointsAlgebra ⟶
      (restrictTestAlgebra ℝ ℂ).obj complexPointsAlgebra := coefficientConjugation
  have he := coefficientTwist_onTestPoints G complexPointsAlgebra a (fun _ => rfl) f z
  have hc (y : Points (complexGroup G).X complexPointsAlgebra) :
      P (conjugateTestPoint G complexPointsAlgebra a y) = realConjugation G (P y) :=
    P.apply_symm_apply _
  have hf (g : Aut (complexGroup G)) (y : Points (complexGroup G).X complexPointsAlgebra) :
      P (y ≫ g.asIso.hom.hom.hom) = pointAut G g (P y) :=
    (pointAut_acts G g y).symm
  replace he := congrArg P he
  rw [hc, hf, hf, hc, P.apply_symm_apply] at he
  exact he

private theorem coefficientTwist_differential (G : AffineAlgebraicGroup ℝ)
    (s : IdentityLieStructure (complexGroup G)) :
    letI := s.lieRing; letI := s.lieAlgebra
    ∀ (σ : Conjugation (Lie ℂ (complexGroup G))),
      IsGroundFieldConjugation G s σ →
      ∀ (f : Aut (complexGroup G)) (x : Lie ℂ (complexGroup G)),
        mapPointKernel (coefficientTwist G f).asIso.hom x =
          σ.map (mapPointKernel f.asIso.hom (σ.map x)) := by
  intro σ hσ f x
  letI := s.lieRing
  letI := s.lieAlgebra
  let R := CommAlgCat.of ℂ (DualNumber ℂ)
  let P := baseChangePointsEquiv ℂ G.val.X R
  have hR (z : ℂ) : dualConjugation.hom (algebraMap ℂ R z) = algebraMap ℂ R (sigmaField z) := by
    apply TrivSqZeroExt.ext
    · rfl
    · exact map_zero Complex.conjAe
  have hc (v : Lie ℂ (complexGroup G)) :
      conjugateTestPoint G R dualConjugation v.toMul.val = (σ.map v).toMul.val := by
    apply P.injective
    exact (P.apply_symm_apply _).trans (hσ v).symm
  have he := coefficientTwist_onTestPoints G R dualConjugation hR f (σ.map x).toMul.val
  change conjugateTestPoint G R dualConjugation (mapPointKernel f.asIso.hom (σ.map x)).toMul.val =
    conjugateTestPoint G R dualConjugation (σ.map x).toMul.val ≫ (coefficientTwist G f).asIso.hom.hom.hom at he
  rw [hc, hc, σ.involutive] at he
  apply Subtype.ext
  exact he.symm

private theorem pointAut_eq_id_of_comp (G : AffineAlgebraicGroup ℝ)
    (a b : Aut (complexGroup G)) (h : a.asIso.hom ≫ b.asIso.hom = 𝟙 _) :
    ∀ x, pointAut G b (pointAut G a x) = x := by
  intro x
  let p := baseChangePointGroupEquiv ℂ G.val complexPointsAlgebra
  let z := p.symm x
  have hx : baseChangePoint ℝ ℂ G.val.X complexPointsAlgebra z = x := p.apply_symm_apply x
  rw [← hx, pointAut_acts G a, pointAut_acts G b]
  have he : z ≫ a.asIso.hom.hom.hom ≫ b.asIso.hom.hom.hom = z := by
    change z ≫ (a.asIso.hom ≫ b.asIso.hom).hom.hom = z
    rw [h]
    exact Category.comp_id z
  exact congrArg p he

private theorem pointAut_comp (G : AffineAlgebraicGroup ℝ)
    (f g : Aut (complexGroup G)) (x : ComplexPoints G) :
    pointAut G (Aut.of (f.asIso ≪≫ g.asIso)) x = pointAut G g (pointAut G f x) := by
  let p := baseChangePointGroupEquiv ℂ G.val complexPointsAlgebra
  let z := p.symm x
  have hx : baseChangePoint ℝ ℂ G.val.X complexPointsAlgebra z = x := p.apply_symm_apply x
  rw [← hx, pointAut_acts, pointAut_acts, pointAut_acts]
  change baseChangePoint ℝ ℂ G.val.X complexPointsAlgebra
    (((groupPointsFunctor ℂ).map (f.asIso.hom ≫ g.asIso.hom)).app complexPointsAlgebra z) = _
  rw [Functor.map_comp, NatTrans.comp_app, GrpCat.comp_apply]

private theorem pointAut_eq (G : AffineAlgebraicGroup ℝ)
    {a b : Aut (complexGroup G)} (h : a.asIso.hom = b.asIso.hom) :
    pointAut G a = pointAut G b := by
  have he' : a = b := Aut.ext (Iso.ext h)
  rw [he']

set_option maxHeartbeats 1000000 in
/-- Lift the Lie automorphisms and their relations to the actual complex group
with its ground-field real structure. -/
theorem liftPolarActions : PointLiftStatement := by
  intro G hG hsc
  let H := baseChangedAlgebraicGroup ℂ G
  let s : IdentityLieStructure (complexGroup G) := identityLieStructure H
  letI := s.lieRing
  letI := s.lieAlgebra
  have hH : GeometricRadicals.IsSemisimple H :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension G hG.1 hG.2.1).mpr hG
  letI : IsIntegral H.val.X.left := integral_of_semisimple H hH
  have hom_ext (f g : complexGroup G ⟶ complexGroup G)
      (h : ∀ x : Lie ℂ (complexGroup G), mapPointKernel f x = mapPointKernel g x) : f = g :=
    hom_eq_of_differential (H := H) (N := H) h
  obtain ⟨σL, ωL, θL, cL, hσ, hω, hθ, hcomm, hc⟩ := liePolarReduction G hG s
  obtain ⟨aω, haω⟩ := liftComplexLieAutomorphism G hG hsc s (conjugationProduct ωL σL)
  obtain ⟨aθ, haθ⟩ := liftComplexLieAutomorphism G hG hsc s θL
  obtain ⟨ac, hac⟩ := liftComplexLieAutomorphism G hG hsc s cL
  let a := pointAut G aω
  let θ := pointAut G aθ
  let c := pointAut G ac
  let σ : MulAut (ComplexPoints G) := MulEquiv.ofBijective
    (realConjugation G) (realConjugation_involutive G).bijective
  let ω := σ.trans a
  have hda (x : Lie ℂ (complexGroup G)) :
      mapPointKernel aω.asIso.hom x = ωL.map (σL.map x) := haω x
  have htw (f : Aut (complexGroup G)) (x : Lie ℂ (complexGroup G)) :
      mapPointKernel (coefficientTwist G f).asIso.hom x =
        σL.map (mapPointKernel f.asIso.hom (σL.map x)) :=
    coefficientTwist_differential G s σL hσ f x
  have hθθ : aθ.asIso.hom ≫ aθ.asIso.hom = 𝟙 _ :=
    hom_ext _ _ (fun x => by
      rw [(lieFunctoriality ℂ).2.2, (lieFunctoriality ℂ).2.1, haθ, haθ, hθ])
  have hωω : (coefficientTwist G aω).asIso.hom ≫ aω.asIso.hom = 𝟙 _ :=
    hom_ext _ _ (fun x => by
      rw [(lieFunctoriality ℂ).2.2, (lieFunctoriality ℂ).2.1, htw, hda, hda,
        σL.involutive, σL.involutive, ωL.involutive])
  have hθω : aω.asIso.hom ≫ aθ.asIso.hom =
      (coefficientTwist G aθ).asIso.hom ≫ aω.asIso.hom :=
    hom_ext _ _ (fun x => by
      simp only [(lieFunctoriality ℂ).2.2, htw, hda, haθ]
      rw [σL.involutive]
      exact hcomm (σL.map x))
  have hca : ac.asIso.hom =
      ((coefficientTwist G ac).asIso.hom ≫ aω.asIso.hom) ≫ aθ.asIso.hom :=
    hom_ext _ _ (fun x => by
      simp only [(lieFunctoriality ℂ).2.2, htw, hda, haθ, hac]
      rw [σL.involutive]
      exact (congrArg cL (σL.involutive x).symm).trans (hc (σL.map x)))
  refine ⟨s, σL, ωL, θL, cL, ω, θ, c, aω, aθ, ac, hσ, hω, hθ, hcomm, hc,
    ?_, pointAut_acts G aθ, pointAut_acts G ac, ?_, fun x => (haθ x).symm,
    fun x => (hac x).symm, pointAut_eq_id_of_comp G aθ aθ hθθ, ?_, ?_, ?_⟩
  · intro z
    change a (realConjugation G (realConjugation G (baseChangePoint ℝ ℂ G.val.X complexPointsAlgebra z))) = _
    rw [realConjugation_involutive]
    exact pointAut_acts G aω z
  · intro x
    rw [hda, σL.involutive]
  · intro x
    change a (realConjugation G (pointAut G aω (realConjugation G x))) = x
    rw [coefficientTwist_onPoints, realConjugation_involutive]
    exact pointAut_eq_id_of_comp G _ _ hωω x
  · intro x
    change pointAut G aθ (pointAut G aω (realConjugation G x)) =
      a (realConjugation G (pointAut G aθ x))
    rw [coefficientTwist_onPoints, ← pointAut_comp, ← pointAut_comp]
    exact congrFun (congrArg DFunLike.coe (pointAut_eq G hθω)) (realConjugation G x)
  · intro x
    change pointAut G ac (realConjugation G x) =
      pointAut G aθ (a (realConjugation G (pointAut G ac x)))
    rw [coefficientTwist_onPoints, ← pointAut_comp, ← pointAut_comp]
    exact congrFun (congrArg DFunLike.coe (pointAut_eq G hca)) (realConjugation G x)

end CoefficientTwist

section MatrixTopology

open Opposite Topology
open Specs.ExceptionalLieAutomorphismTransport
open Specs.StandardGroups (GLCoordinates genericDeterminant)
open Specs.AdjointRepresentation (GroupPoints)
open private glEvaluation matrixEvaluation isUnit_matrixEvaluation_det glEvaluation_entry
  from LinearAlgebraicGroups.Affine.StandardGroups
open private matrixEvaluation_mapMatrix generalLinearRepresentation Representation.convolutionIso
  from LinearAlgebraicGroups.Affine.StandardGroups

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 650000

private theorem continuous_glCoordinates {idx U : Type} [Fintype idx] [DecidableEq idx]
    [TopologicalSpace U] (m : U → Matrix.GeneralLinearGroup idx ℂ)
    (hm : Continuous (fun u => (m u).val)) (f : GLCoordinates ℝ idx) :
    Continuous (fun u => glEvaluation (k := ℝ) (m u) f) := by
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (genericDeterminant ℝ idx) f
  have he (u : U) (v : MvPolynomial (idx × idx) ℝ) :
      glEvaluation (k := ℝ) (m u) (algebraMap _ _ v) = matrixEvaluation (m u).val v :=
    IsLocalization.Away.lift_eq (S := GLCoordinates ℝ idx) (genericDeterminant ℝ idx)
      (g := (matrixEvaluation (m u).val).toRingHom) (isUnit_matrixEvaluation_det (m u)) v
  have hval (u : U) : glEvaluation (k := ℝ) (m u) f =
      matrixEvaluation (m u).val p / (m u).val.det ^ n := by
    have hv := congrArg (glEvaluation (k := ℝ) (m u)) hp
    have hd : matrixEvaluation (m u).val (genericDeterminant ℝ idx) = (m u).val.det := by
      change matrixEvaluation (m u).val (Specs.StandardGroups.genericMatrix ℝ idx).det = _
      rw [AlgHom.map_det, matrixEvaluation_mapMatrix]
    rw [map_mul, map_pow, he, he, hd] at hv
    exact (eq_div_iff (pow_ne_zero n (m u).det_ne_zero)).mpr hv
  simp only [hval]
  apply Continuous.div _ (hm.matrix_det.pow n) (fun u => pow_ne_zero _ (m u).det_ne_zero)
  have hp' : Continuous (fun u => fun ij : idx × idx => (m u).val ij.1 ij.2) :=
    continuous_pi fun ij => (continuous_apply ij.2).comp ((continuous_apply ij.1).comp hm)
  simpa only [matrixEvaluation, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map, Function.comp_def] using
    (MvPolynomial.continuous_eval (p.map (algebraMap ℝ ℂ))).comp hp'

private theorem continuous_glSpectrumPoint {idx U : Type} [Fintype idx] [DecidableEq idx]
    [TopologicalSpace U] (m : U → Matrix.GeneralLinearGroup idx ℂ)
    (hm : Continuous (fun u => (m u).val)) :
    Continuous (fun u => (Spec.map (CommRingCat.ofHom
      (glEvaluation (k := ℝ) (m u)).toRingHom)) (IsLocalRing.closedPoint ℂ)) := by
  apply continuous_iff_isClosed.mpr
  intro Z hZ
  change IsClosed (Z : Set (PrimeSpectrum (GLCoordinates ℝ idx))) at hZ
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus Z).mp hZ
  rw [hs]
  have he : (fun u => (Spec.map (CommRingCat.ofHom
      (glEvaluation (k := ℝ) (m u)).toRingHom)) (IsLocalRing.closedPoint ℂ)) ⁻¹'
        PrimeSpectrum.zeroLocus s =
      ⋂ f ∈ s, {u | glEvaluation (k := ℝ) (m u) f = 0} := by
    ext u
    simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq, Spec.map_apply]
    let q : PrimeSpectrum (GLCoordinates ℝ idx) :=
      PrimeSpectrum.comap (glEvaluation (k := ℝ) (m u)).toRingHom (IsLocalRing.closedPoint ℂ)
    change q ∈ PrimeSpectrum.zeroLocus s ↔ _
    rw [PrimeSpectrum.mem_zeroLocus]
    change (∀ f ∈ s, glEvaluation (k := ℝ) (m u) f ∈ IsLocalRing.maximalIdeal ℂ) ↔ _
    simp only [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]
  rw [he]
  exact isClosed_iInter fun f => isClosed_iInter fun _ =>
    isClosed_eq (continuous_glCoordinates m hm f) continuous_const

private theorem continuous_matrixSchemePoint {idx U : Type} [Fintype idx] [DecidableEq idx]
    [TopologicalSpace U] {N : AffineAlgebraicGroup ℝ}
    (l : (groupPointsFunctor ℝ).obj N.val ≅ Specs.StandardGroups.generalLinearPoints ℝ idx)
    (m : U → Matrix.GeneralLinearGroup idx ℂ) (hm : Continuous fun u => (m u).val) :
    Continuous (fun u => ((l.inv.app realPointsAlgebra) (m u) : ComplexPoints N).left
      (IsLocalRing.closedPoint ℂ)) := by
  let L := StandardGroups.generalLinearGroup ℝ idx
  let lL := StandardGroups.generalLinearGroupPointsIso ℝ idx
  let E := groupHomEquiv L.val N.val L.property.1
  let φ := E.symm (lL.hom ≫ l.inv)
  have hφ : (groupPointsFunctor ℝ).map φ = lL.hom ≫ l.inv := E.apply_symm_apply _
  letI := StandardGroups.generalLinearHopf ℝ idx
  let A := CommHopfAlgCat.of ℝ (GLCoordinates ℝ idx)
  let z (u : U) : ComplexPoints L :=
    (hopfSpecPointIso A).hom.app realPointsAlgebra (WithConv.toConv (glEvaluation (m u)))
  have hz (u : U) : (lL.hom.app realPointsAlgebra) (z u) = m u := by
    let e := hopfSpecPointIso A
    let c := Representation.convolutionIso (@generalLinearRepresentation ℝ _ idx _ _)
    have he : e ≪≫ lL = c := by
      change e ≪≫ (e.symm ≪≫ c) = c
      simp
    change ((e ≪≫ lL).hom.app realPointsAlgebra) (WithConv.toConv (glEvaluation (m u))) = m u
    rw [he]
    exact Matrix.GeneralLinearGroup.ext fun i j => glEvaluation_entry (m u) i j
  have h (u : U) : pointMap φ (z u) = (l.inv.app realPointsAlgebra) (m u) := by
    change (((groupPointsFunctor ℝ).map φ).app realPointsAlgebra) (z u) = _
    rw [hφ, NatTrans.comp_app, GrpCat.comp_apply, hz]
  simp only [← h]
  change Continuous (fun u => φ.hom.hom.left
    ((Spec.map (CommRingCat.ofHom (glEvaluation (k := ℝ) (m u)).toRingHom))
      (IsLocalRing.closedPoint ℂ)))
  exact φ.hom.hom.left.continuous.comp (continuous_glSpectrumPoint m hm)

private theorem closedImmersion_lift_point {X Y : SchemeOver ℝ} (f : X ⟶ Y)
    [IsClosedImmersion f.left] (y : Points Y realPointsAlgebra)
    (h : y.left (IsLocalRing.closedPoint ℂ) ∈ Set.range f.left) :
    ∃ x : Points X realPointsAlgebra, x ≫ f = y := by
  letI : Subsingleton (testSpec ℝ |>.obj (op realPointsAlgebra)).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of ℂ)))
  letI : IsReduced (testSpec ℝ |>.obj (op realPointsAlgebra)).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of ℂ)))
  let p := pullback.fst y.left f.left
  haveI : IsClosedImmersion p := MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback y.left f.left).flip inferInstance
  haveI : AlgebraicGeometry.Surjective p := ⟨by
    apply Set.range_eq_univ.mp
    change Set.range ⇑(pullback.fst y.left f.left) = _
    rw [Scheme.Pullback.range_fst]
    exact Set.eq_univ_of_forall (fun z => by
      change y.left z ∈ Set.range f.left
      rw [show z = IsLocalRing.closedPoint ℂ from Subsingleton.elim _ _]
      exact h)⟩
  letI : IsIso p := isIso_of_isClosedImmersion_of_surjective p
  let t := inv p ≫ pullback.snd y.left f.left
  have ht : t ≫ f.left = y.left := by
    dsimp only [t]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    change (inv p ≫ p) ≫ y.left = y.left
    rw [IsIso.inv_hom_id, Category.id_comp]
  have hw : t ≫ X.hom = ((testSpec ℝ).obj (op realPointsAlgebra)).hom := by
    rw [← Over.w f, ← Category.assoc, ht, Over.w y]
  exact ⟨Over.homMk t hw, Over.OverMorphism.ext ht⟩

open private baseChangeMapPullback from LinearAlgebraicGroups.Affine.Components

private theorem isClopen_range_of_geometricComponent {Q A : AffineAlgebraicGroup ℝ}
    (i : Q.val ⟶ A.val) (hi : IsClosedImmersion i.hom.hom.left)
    (hgeom : AdjointLieAutomorphisms.IsGeometricIdentityComponent (Q := Q) (A := A) i) :
    IsClopen (Set.range i.hom.hom.left) := by
  let K := AlgebraicClosure ℝ
  let πQ := pullback.fst Q.val.X.hom (fieldSpecMap ℝ K)
  let πA := pullback.fst A.val.X.hom (fieldSpecMap ℝ K)
  let j := ((groupBaseChange ℝ K).map i).hom.hom.left
  haveI : AlgebraicGeometry.Surjective (fieldSpecMap ℝ K) := ⟨fun _ =>
    ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  have hs : Function.Surjective πQ := (inferInstance : AlgebraicGeometry.Surjective πQ).surj
  have he : πA '' Set.range j = Set.range i.hom.hom.left := by
    rw [← Set.range_comp]
    have hw : j ≫ πA = πQ ≫ i.hom.hom.left := (baseChangeMapPullback (K := K) i.hom.hom).w
    change Set.range ⇑(j ≫ πA) = _
    rw [hw]
    exact (hs.range_comp i.hom.hom.left)
  haveI : IsOpenImmersion j := hgeom.1
  have hOpen : IsOpen (πA '' Set.range j) := πA.isOpenMap _ j.isOpenEmbedding.isOpen_range
  exact ⟨hi.isClosedEmbedding.isClosed_range, he ▸ hOpen⟩

private theorem pointMap_injective_of_closed {G Q : AffineAlgebraicGroup ℝ}
    (i : G.val ⟶ Q.val) (hi : IsClosedImmersion i.hom.hom.left) :
    Function.Injective (pointMap i) := by
  letI := hi
  intro a b h
  apply Over.OverMorphism.ext
  exact (cancel_mono i.hom.hom.left).mp (congrArg (fun y : ComplexPoints Q => y.left) h)

private theorem matrixPoint_injective_of_closed {idx : Type} [Fintype idx] [DecidableEq idx]
    {A N : AffineAlgebraicGroup ℝ} (j : A.val ⟶ N.val)
    (l : (groupPointsFunctor ℝ).obj N.val ≅ Specs.StandardGroups.generalLinearPoints ℝ idx)
    (hj : IsClosedImmersion j.hom.hom.left) : Function.Injective (matrixPoint j l) :=
  (l.app realPointsAlgebra).groupIsoToMulEquiv.injective.comp (pointMap_injective_of_closed j hj)

private theorem matrixPoint_comp {idx : Type} [Fintype idx] [DecidableEq idx]
    {Q A N : AffineAlgebraicGroup ℝ} (i : Q.val ⟶ A.val) (j : A.val ⟶ N.val)
    (l : (groupPointsFunctor ℝ).obj N.val ≅ Specs.StandardGroups.generalLinearPoints ℝ idx)
    (x : ComplexPoints Q) : matrixPoint (i ≫ j) l x = matrixPoint j l (pointMap i x) := by
  change (l.hom.app realPointsAlgebra) (((groupPointsFunctor ℝ).map (i ≫ j)).app
    realPointsAlgebra x) = _
  rw [Functor.map_comp, NatTrans.comp_app, GrpCat.comp_apply]
  rfl

private theorem adjointPoint_closedEmbedding {idx : Type} [Fintype idx] [DecidableEq idx]
    {Q A N : AffineAlgebraicGroup ℝ} (i : Q.val ⟶ A.val) (j : A.val ⟶ N.val)
    (l : (groupPointsFunctor ℝ).obj N.val ≅ Specs.StandardGroups.generalLinearPoints ℝ idx)
    (hi : IsClosedImmersion i.hom.hom.left) (hj : IsClosedImmersion j.hom.hom.left)
    (hgeom : AdjointLieAutomorphisms.IsGeometricIdentityComponent (Q := Q) (A := A) i)
    (B : Subgroup (Matrix.GeneralLinearGroup idx ℂ))
    (hA : ∀ p : B, ∃ a : ComplexPoints A, matrixPoint j l a = p.val)
    (hB : ∀ y, matrixPoint (i ≫ j) l y ∈ B) :
    letI : TopologicalSpace (ComplexPoints Q) :=
      TopologicalSpace.induced (matrixPointValue (i ≫ j) l) inferInstance
    letI : TopologicalSpace B :=
      TopologicalSpace.induced (fun p : B => (p.val.val : Matrix idx idx ℂ)) inferInstance
    let ρ := (matrixPoint (i ≫ j) l).codRestrict B hB
    IsClosedEmbedding ρ ∧ connectedComponent (1 : B) ⊆ Set.range ρ := by
  letI : TopologicalSpace (ComplexPoints Q) :=
    TopologicalSpace.induced (matrixPointValue (i ≫ j) l) inferInstance
  letI : TopologicalSpace B :=
    TopologicalSpace.induced (fun p : B => (p.val.val : Matrix idx idx ℂ)) inferInstance
  let ρ := (matrixPoint (i ≫ j) l).codRestrict B hB
  let a (p : B) := (hA p).choose
  have ha (p : B) : matrixPoint j l (a p) = p.val := (hA p).choose_spec
  have hjin := matrixPoint_injective_of_closed j l hj
  let F (p : B) : A.val.X.left := (a p).left (IsLocalRing.closedPoint ℂ)
  have hF : Continuous F := by
    apply hj.isClosedEmbedding.isInducing.continuous_iff.mpr
    have he (p : B) : pointMap j (a p) = (l.inv.app realPointsAlgebra) p.val := by
      apply (l.app realPointsAlgebra).groupIsoToMulEquiv.injective
      change matrixPoint j l (a p) = (l.hom.app realPointsAlgebra) ((l.inv.app realPointsAlgebra) p.val)
      rw [ha]
      exact ((l.app realPointsAlgebra).groupIsoToMulEquiv.apply_symm_apply _).symm
    change Continuous (fun p => ((pointMap j (a p)).left (IsLocalRing.closedPoint ℂ)))
    simp only [he]
    exact continuous_matrixSchemePoint l (fun p : B => p.val) continuous_induced_dom
  have hR : Set.range ρ = F ⁻¹' Set.range i.hom.hom.left := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      have he : a (ρ x) = pointMap i x := hjin (by rw [ha]; exact matrixPoint_comp i j l x)
      exact ⟨x.left (IsLocalRing.closedPoint ℂ), by change _ = (a (ρ x)).left _; rw [he]; rfl⟩
    · intro hp
      letI := hi
      obtain ⟨x, hx⟩ := closedImmersion_lift_point i.hom.hom (a p) hp
      refine ⟨x, Subtype.ext ?_⟩
      change matrixPoint (i ≫ j) l x = p.val
      rw [matrixPoint_comp, show pointMap i x = a p from hx, ha]
  have hClopen : IsClopen (Set.range ρ) := hR ▸ (isClopen_range_of_geometricComponent i hi hgeom).preimage hF
  have hidx : IsInducing ρ := by
    constructor
    change TopologicalSpace.induced (matrixPointValue (i ≫ j) l) _ =
      TopologicalSpace.induced ρ (TopologicalSpace.induced (fun p : B => p.val.val) _)
    rw [induced_compose]
    rfl
  have hinj : Function.Injective ρ := by
    letI := hi
    letI := hj
    intro x y h
    apply matrixPoint_injective_of_closed (i ≫ j) l (IsClosedImmersion.comp i.hom.hom.left j.hom.hom.left)
    exact congrArg Subtype.val h
  exact ⟨⟨⟨hidx, hinj⟩, hClopen.1⟩,
    hClopen.connectedComponent_subset ⟨1, ρ.map_one⟩⟩

end MatrixTopology

section FaithfulConjugation

open Opposite Topology
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Specs.ExceptionalLieAutomorphismTransport
open Specs.AdjointRepresentation (GroupPoints constants conjugate)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open Specs.AdjointCocharacters (IsAdjointQuotient)
open private baseChangeMapPullback baseChangeKernelSquare from LinearAlgebraicGroups.Affine.Components
open private centre_baseChange from LinearAlgebraicGroups.Reductive.CentralTorus
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private affineBaseTerminal from LinearAlgebraicGroups.Solvable.SplitFixedPoint
open private pointConjugation pointConjugation_apply
  from LinearAlgebraicGroups.Representation.SemisimplyDifferentiated
open private baseTestSpecIso from LinearAlgebraicGroups.Arithmetic.AdjointLieAutomorphisms

set_option maxHeartbeats 140000
set_option synthInstance.maxHeartbeats 10000

private theorem eq_of_complexPoints {X Y : SchemeOver ℂ} (f g : X ⟶ Y)
    [IsReduced X.left] [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom]
    (h : ∀ x : Points X complexPointsAlgebra, x ≫ f = x ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  haveI : LocallyOfFiniteType (f.left ≫ Y.hom) := (Over.w f).symm ▸ ‹_›
  apply AlgebraicGeometry.ext_of_apply_eq Y.hom Set.univ isOpen_univ.isLocallyClosed dense_univ _ _
  · intro x _ hx
    let z := pointOfClosedPoint X.hom x hx
    let p : Points X complexPointsAlgebra :=
      Over.homMk z (by
        rw [pointOfClosedPoint_comp]
        change (𝟙 _) = Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ))
        rw [show algebraMap ℂ ℂ = RingHom.id ℂ from rfl, CommRingCat.ofHom_id, Spec.map_id])
    have he := congrArg (fun a : Points Y complexPointsAlgebra => a.left (IsLocalRing.closedPoint ℂ)) (h p)
    change f.left (z (IsLocalRing.closedPoint ℂ)) = g.left (z (IsLocalRing.closedPoint ℂ)) at he
    simpa only [z, pointOfClosedPoint_apply] using he
  · exact (Over.w f).trans (Over.w g).symm

private theorem finiteOverField_discrete {k : Type} [Field k] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite f] : DiscreteTopology X := by
  letI : IsAffine X := isAffine_of_isAffineHom f
  let e := X.isoSpec
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (e.inv ≫ f)
  haveI : IsFinite (e.inv ≫ f) := inferInstance
  have hfin := (IsFinite.SpecMap_iff φ).mp (hφ ▸ ‹IsFinite (e.inv ≫ f)›)
  letI : Algebra k (Γ(X, ⊤)) := φ.hom.toAlgebra
  letI : Module.Finite k (Γ(X, ⊤)) := hfin
  letI : IsArtinianRing (Γ(X, ⊤)) := IsArtinianRing.of_finite k _
  letI : IsLocallyArtinian (Spec Γ(X, ⊤)) := Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  exact e.hom.homeomorph.symm.discreteTopology

private theorem baseChangePointMap (G Q : AffineAlgebraicGroup ℝ) (q : G.val ⟶ Q.val)
    (g : GroupPoints (complexGroup G) complexPointsAlgebra) :
    baseChangePointGroupEquiv ℂ Q.val complexPointsAlgebra
      (((groupPointsFunctor ℂ).map ((groupBaseChange ℝ ℂ).map q)).app complexPointsAlgebra g) =
    pointMap q (baseChangePointGroupEquiv ℂ G.val complexPointsAlgebra g) :=
  baseChangePointsSchemeNaturality ℝ ℂ q.hom.hom complexPointsAlgebra g

private theorem eq_of_equal_at_point_finite {X Y : SchemeOver ℂ}
    [IsReduced X.left] [LocallyOfFiniteType X.hom] [ConnectedSpace X.left] [IsFinite Y.hom]
    (f g : X ⟶ Y) (x₀ : X.left) (h₀ : f.left x₀ = g.left x₀) : f = g := by
  letI : DiscreteTopology Y.left := finiteOverField_discrete Y.hom
  haveI : LocallyOfFiniteType (f.left ≫ Y.hom) := (Over.w f).symm ▸ ‹_›
  have hconst (a : X ⟶ Y) (x : X.left) : a.left x = a.left x₀ := by
    apply a.left.continuous.image_eq_of_connectedComponent_eq
    rw [PreconnectedSpace.connectedComponent_eq_univ, PreconnectedSpace.connectedComponent_eq_univ]
  apply Over.OverMorphism.ext
  exact AlgebraicGeometry.ext_of_apply_eq Y.hom Set.univ isOpen_univ.isLocallyClosed dense_univ
    (fun x _ _ => (hconst f x).trans (h₀.trans (hconst g x).symm))
    ((Over.w f).trans (Over.w g).symm)

private abbrev complexPointSource := (testSpec ℂ).obj (op complexPointsAlgebra)

private def conjugationByComplexPoint {H : GroupScheme ℂ} (g : complexPointSource ⟶ H.X) :
    H ⟶ H :=
  pointConjugation ((baseTestSpecIso ℂ).hom ≫ g)

private theorem conjugationByComplexPoint_apply {H : GroupScheme ℂ}
    (g : complexPointSource ⟶ H.X) {S : SchemeOver ℂ} (a : S ⟶ complexPointSource)
    (w : S ⟶ H.X) :
    w ≫ (conjugationByComplexPoint g).hom.hom = (a ≫ g) * w * (a ≫ g)⁻¹ := by
  let t := (baseTestSpecIso ℂ).hom
  have h : (toUnit S ≫ t) ≫ g = a ≫ g :=
    congrArg (· ≫ g) ((affineBaseTerminal ℂ).hom_ext (toUnit S ≫ t) a)
  change w ≫ (pointConjugation (t ≫ g)).hom.hom = _
  rw [pointConjugation_apply, ← Category.assoc, h]

private theorem conjugationOverQuotient_eq {H P : AffineAlgebraicGroup ℂ}
    [IsReduced H.val.X.left] (q : H.val ⟶ P.val) (g : complexPointSource ⟶ H.val.X)
    (h : ∀ x : complexPointSource ⟶ H.val.X,
      Commute (g ≫ q.hom.hom) (x ≫ q.hom.hom)) :
    (conjugationByComplexPoint g).hom.hom ≫ q.hom.hom = q.hom.hom := by
  letI : LocallyOfFiniteType H.val.X.hom := H.property.2.1
  letI : LocallyOfFiniteType P.val.X.hom := P.property.2.1
  letI : IsAffine P.val.X.left := P.property.1
  letI : IsSeparated P.val.X.hom := inferInstance
  apply eq_of_complexPoints
  intro x
  rw [← Category.assoc, conjugationByComplexPoint_apply g (𝟙 complexPointSource) x,
    Category.id_comp, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, (h x).eq,
    mul_assoc, mul_inv_cancel, mul_one]

private theorem conjugationOverFiniteKernel_eq_id (H : AffineAlgebraicGroup ℂ)
    [IsIntegral H.val.X.left] {P : GroupScheme ℂ} {q : H.val ⟶ P}
    {Z : ClosedSubgroup H.val} (hker : IsSchemeKernel q Z) (hfin : IsFinite Z.group.X.hom)
    (u : H.val ⟶ H.val) (hu : u.hom.hom ≫ q.hom.hom = q.hom.hom) :
    u.hom.hom = 𝟙 H.val.X := by
  let v : H.val.X ⟶ H.val.X := u.hom.hom * (𝟙 H.val.X)⁻¹
  have hv : v ≫ q.hom.hom = 1 := by
    change (u.hom.hom * (𝟙 H.val.X)⁻¹) ≫ q.hom.hom = 1
    rw [MonObj.mul_comp, GrpObj.inv_comp, hu, Category.id_comp, mul_inv_cancel]
  obtain ⟨d, hd⟩ := (schemeKernel_sections hker v).mpr hv
  change d ≫ Z.inclusion.hom.hom = v at hd
  let e : complexPointSource ⟶ H.val.X := 1
  let r : H.val.X ⟶ Z.group.X := 1
  have hr : r ≫ Z.inclusion.hom.hom = 1 := MonObj.one_comp _
  have he : e ≫ d = e ≫ r := by
    letI : IsClosedImmersion Z.inclusion.hom.hom.left := Z.isClosedImmersion
    haveI : Mono Z.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono Z.inclusion.hom.hom).mp
    rw [Category.assoc, hd, Category.assoc, hr, MonObj.comp_one]
    have huu : e ≫ u.hom.hom = 1 := MonObj.one_comp _
    change e ≫ (u.hom.hom * (𝟙 H.val.X)⁻¹) = 1
    rw [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, huu]
    change (1 : complexPointSource ⟶ H.val.X) * (1 : complexPointSource ⟶ H.val.X)⁻¹ = 1
    exact mul_inv_cancel _
  letI : LocallyOfFiniteType H.val.X.hom := H.property.2.1
  letI : IsFinite Z.group.X.hom := hfin
  have hd1 : d = r := eq_of_equal_at_point_finite d r (e.left (IsLocalRing.closedPoint ℂ))
    (congrArg (fun a : complexPointSource ⟶ Z.group.X => a.left (IsLocalRing.closedPoint ℂ)) he)
  have hv' : v = 1 := hd.symm.trans (hd1 ▸ hr)
  exact mul_inv_eq_one.mp hv'

private theorem central_image_eq_one (H P : AffineAlgebraicGroup ℂ)
    [IsIntegral H.val.X.left] (Z : ClosedSubgroup H.val) (q : H.val ⟶ P.val)
    (hcentre : CentralTorus.IsSchemeCentre Z) (hker : IsSchemeKernel q Z)
    (hfin : IsFinite Z.group.X.hom) (g : complexPointSource ⟶ H.val.X)
    (h : ∀ x : complexPointSource ⟶ H.val.X,
      Commute (g ≫ q.hom.hom) (x ≫ q.hom.hom)) :
    g ≫ q.hom.hom = 1 := by
  have hu := conjugationOverFiniteKernel_eq_id H hker hfin (conjugationByComplexPoint g)
    (conjugationOverQuotient_eq q g h)
  have hcent : Centralizes (𝟙 H.val) g := by
    apply (centralizes_iff _ _).mpr
    intro S a w
    have hp := conjugationByComplexPoint_apply g a w
    rw [hu, Category.comp_id] at hp
    change Commute (a ≫ g) (w ≫ 𝟙 H.val.X)
    rw [Category.comp_id]
    exact mul_inv_eq_iff_eq_mul.mp hp.symm
  exact (schemeKernel_sections hker g).mp ((hcentre _ g).mp hcent)

private theorem adjointConjugation_faithful (G Q : AffineAlgebraicGroup ℝ)
    (hG : GeometricRadicals.IsSemisimple G) (Z : ClosedSubgroup G.val)
    (q : G.val ⟶ Q.val) (hq : IsAdjointQuotient Z q) (hZ : IsFinite Z.group.X.hom)
    (hsurj : Function.Surjective (pointMap q)) :
    Function.Injective (MulAut.conj : ComplexPoints Q →* MulAut (ComplexPoints Q)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro y hy
  obtain ⟨z, hz⟩ := hsurj y
  let H := baseChangedAlgebraicGroup ℂ G
  let P := baseChangedAlgebraicGroup ℂ Q
  let qC : H.val ⟶ P.val := (groupBaseChange ℝ ℂ).map q
  have hH : GeometricRadicals.IsSemisimple H :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension G hG.1 hG.2.1).mpr hG
  letI : IsIntegral H.val.X.left := integral_of_semisimple H hH
  let eG : GroupPoints H.val complexPointsAlgebra ≃* ComplexPoints G :=
    baseChangePointGroupEquiv ℂ G.val complexPointsAlgebra
  let eQ : GroupPoints P.val complexPointsAlgebra ≃* ComplexPoints Q :=
    baseChangePointGroupEquiv ℂ Q.val complexPointsAlgebra
  let g : GroupPoints H.val complexPointsAlgebra := eG.symm z
  let π : GroupPoints H.val complexPointsAlgebra →* GroupPoints P.val complexPointsAlgebra :=
    (((groupPointsFunctor ℂ).map qC).app complexPointsAlgebra).hom
  have hqg : eQ (π g) = y :=
    (baseChangePointMap G Q q g).trans ((congrArg (pointMap q) (eG.apply_symm_apply z)).trans hz)
  obtain ⟨hZC, hcentre⟩ := centre_baseChange hq.1 ℂ
  let ZC : ClosedSubgroup H.val := GeometricRadicals.baseChangedSubgroup ℂ Z hZC
  have hker : IsSchemeKernel qC ZC := baseChangeKernelSquare q Z.inclusion hq.2.1
  have hfin : IsFinite ZC.group.X.hom :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback Z.group.X.hom (fieldSpecMap ℝ ℂ)) hZ
  have he : π g = 1 := central_image_eq_one H P ZC qC hcentre hker hfin g (fun x => by
    change Commute (π g) (π x)
    change π g * π x = π x * π g
    apply eQ.injective
    rw [map_mul, map_mul, hqg]
    have hh : y * eQ (π x) * y⁻¹ = eQ (π x) :=
      DFunLike.congr_fun hy (eQ (π x))
    exact mul_inv_eq_iff_eq_mul.mp hh)
  exact hqg.symm.trans ((congrArg eQ he).trans eQ.map_one)

end FaithfulConjugation

section AdjointActions

open Specs.ExceptionalLieAutomorphismTransport
open Specs.AdjointRepresentation (GroupPoints constants dualMap dualRestriction conjugate)
open LieAlgebrasAndRepresentations.RealForms (Conjugation)
open private pointRestrict_conjugate relativePointRestrict tangentRestrict
  from LinearAlgebraicGroups.Affine.AdjointRepresentation

set_option maxHeartbeats 130000
set_option synthInstance.maxHeartbeats 10000

private abbrev matrixAction {idx V : Type} [Fintype idx] [DecidableEq idx]
    [AddCommGroup V] [Module ℂ V] (b : Module.Basis idx ℂ V)
    (m : Matrix.GeneralLinearGroup idx ℂ) (v : V) : V :=
  b.equivFun.symm (m.val *ᵥ b.equivFun v)

private theorem matrixAction_injective {idx V : Type} [Fintype idx] [DecidableEq idx]
    [AddCommGroup V] [Module ℂ V] (b : Module.Basis idx ℂ V) :
    Function.Injective (matrixAction b) := by
  intro m n he
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  have h := congrFun he (b.equivFun.symm (Pi.single i 1))
  change b.equivFun.symm (m.val *ᵥ b.equivFun (b.equivFun.symm (Pi.single i 1))) =
    b.equivFun.symm (n.val *ᵥ b.equivFun (b.equivFun.symm (Pi.single i 1))) at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact b.equivFun.symm.injective h

private theorem matrixAction_one {idx V : Type} [Fintype idx] [DecidableEq idx]
    [AddCommGroup V] [Module ℂ V] (b : Module.Basis idx ℂ V) (v : V) :
    matrixAction b 1 v = v := by
  change b.equivFun.symm ((1 : Matrix idx idx ℂ) *ᵥ b.equivFun v) = v
  rw [Matrix.one_mulVec, LinearEquiv.symm_apply_apply]

private theorem adjoint_commutes_with_differential {X : GroupScheme ℂ}
    (a : X ⟶ X) (g : GroupPoints X complexPointsAlgebra) (v : Lie ℂ X) :
    conjugate (g ≫ a.hom.hom) (mapPointKernel a v) =
      conjugate g v ≫ a.hom.hom := by
  let R := complexPointsAlgebra
  let S := CommAlgCat.of ℂ (DualNumber ℂ)
  let F := groupPointsFunctor ℂ
  let c : GroupPoints X R →* GroupPoints X S := ((F.obj X).map (constants R)).hom
  let d : GroupPoints X S →* GroupPoints X S := ((F.map a).app S).hom
  let dR : GroupPoints X R →* GroupPoints X R := ((F.map a).app R).hom
  have hn : c (dR g) = d (c g) := by
    have h := (F.map a).naturality (constants R)
    exact (congrArg (fun f => GrpCat.Hom.hom f g) h).symm
  change c (dR g) * d v.toMul.val * (c (dR g))⁻¹ =
    d (c g * v.toMul.val * (c g)⁻¹)
  rw [hn, d.map_mul, d.map_mul, d.map_inv]

private theorem adjoint_intertwines_algebraic {idx : Type} [Fintype idx] [DecidableEq idx]
    {G Q N : AffineAlgebraicGroup ℝ} (q : G.val ⟶ Q.val) (i : Q.val ⟶ N.val)
    (l : (groupPointsFunctor ℝ).obj N.val ≅ Specs.StandardGroups.generalLinearPoints ℝ idx)
    (s : IdentityLieStructure (complexGroup G))
    (b : letI := s.lieRing; letI := s.lieAlgebra; Module.Basis idx ℂ (Lie ℂ (complexGroup G)))
    (hAdj : ActsByAdjoint q i l s b)
    (a : Aut (complexGroup G)) (u : ComplexPoints G → ComplexPoints G)
    (hu : ActsOnComplexPoints G a u) :
    letI := s.lieRing; letI := s.lieAlgebra
    ∀ (x : ComplexPoints G) (v : Lie ℂ (complexGroup G)),
      matrixAction b (matrixPoint i l (pointMap q (u x))) (mapPointKernel a.asIso.hom v) =
        mapPointKernel a.asIso.hom (matrixAction b (matrixPoint i l (pointMap q x)) v) := by
  letI := s.lieRing
  letI := s.lieAlgebra
  let e := baseChangePointGroupEquiv ℂ G.val complexPointsAlgebra
  have he (g : GroupPoints (complexGroup G) complexPointsAlgebra) (v : Lie ℂ (complexGroup G)) :
      (matrixAction b (matrixPoint i l (pointMap q (e g))) v).toMul.val = conjugate g v :=
    hAdj g v
  intro x v
  obtain ⟨g, rfl⟩ := e.surjective x
  have hx : u (e g) = e (g ≫ a.asIso.hom.hom.hom) := hu g
  rw [hx]
  apply Subtype.ext
  change (matrixAction b (matrixPoint i l (pointMap q (e (g ≫ a.asIso.hom.hom.hom))))
    (mapPointKernel a.asIso.hom v)).toMul.val =
      (matrixAction b (matrixPoint i l (pointMap q (e g))) v).toMul.val ≫ a.asIso.hom.hom.hom
  calc
    _ = conjugate (g ≫ a.asIso.hom.hom.hom) (mapPointKernel a.asIso.hom v) := he _ _
    _ = conjugate g v ≫ a.asIso.hom.hom.hom := adjoint_commutes_with_differential a.asIso.hom g v
    _ = _ := congrArg (fun p => p ≫ a.asIso.hom.hom.hom) (he g v).symm

private theorem adjoint_intertwines_groundField {idx : Type} [Fintype idx] [DecidableEq idx]
    {G Q N : AffineAlgebraicGroup ℝ} (q : G.val ⟶ Q.val) (i : Q.val ⟶ N.val)
    (l : (groupPointsFunctor ℝ).obj N.val ≅ Specs.StandardGroups.generalLinearPoints ℝ idx)
    (s : IdentityLieStructure (complexGroup G))
    (b : letI := s.lieRing; letI := s.lieAlgebra; Module.Basis idx ℂ (Lie ℂ (complexGroup G)))
    (hAdj : ActsByAdjoint q i l s b) :
    letI := s.lieRing; letI := s.lieAlgebra
    ∀ (σ : Conjugation (Lie ℂ (complexGroup G))), IsGroundFieldConjugation G s σ →
    ∀ (x : ComplexPoints G) (v : Lie ℂ (complexGroup G)),
      matrixAction b (matrixPoint i l (pointMap q (realConjugation G x))) (σ.map v) =
        σ.map (matrixAction b (matrixPoint i l (pointMap q x)) v) := by
  letI := s.lieRing
  letI := s.lieAlgebra
  intro σ hσ x v
  let e := baseChangePointGroupEquiv ℂ G.val complexPointsAlgebra
  let E := relativePointRestrict ℂ G.val complexPointsAlgebra
  let T := tangentRestrict ℂ G.val complexPointsAlgebra
  let τ := dualMap coefficientConjugation
  have hσ' (w : Lie ℂ (complexGroup G)) : E (σ.map w).toMul.val = mapPoints τ (E w.toMul.val) := by
    let d := dualRestriction (k := ℝ) ℂ complexPointsAlgebra
    have h := congrArg (mapPoints (X := G.val.X) d.hom) (hσ w)
    change E (σ.map w).toMul.val =
      mapPoints d.hom (mapPoints dualConjugation (onDual G w.toMul.val)) at h
    have hc : dualConjugation ≫ d.hom = d.hom ≫ τ := by
      change (d.hom ≫ τ ≫ d.inv) ≫ d.hom = _
      simp
    rw [show mapPoints d.hom (mapPoints dualConjugation (onDual G w.toMul.val)) =
        mapPoints τ (E w.toMul.val) from by
      change mapPoints d.hom (mapPoints dualConjugation (onDual G w.toMul.val)) =
        mapPoints τ (mapPoints d.hom (onDual G w.toMul.val))
      simp only [mapPoints, ← Category.assoc, ← Functor.map_comp, ← op_comp, hc]] at h
    exact h
  have he (y : ComplexPoints G) (w : Lie ℂ (complexGroup G)) :
      E (matrixAction b (matrixPoint i l (pointMap q y)) w).toMul.val = conjugate y (T w) := by
    obtain ⟨g, rfl⟩ := e.surjective y
    have hz : (matrixAction b (matrixPoint i l (pointMap q (e g))) w).toMul.val =
        conjugate g w := hAdj g w
    exact (congrArg E hz).trans (pointRestrict_conjugate ℂ G.val complexPointsAlgebra g w)
  apply Subtype.ext
  apply E.injective
  change E (matrixAction b (matrixPoint i l (pointMap q (realConjugation G x)))
    (σ.map v)).toMul.val = E (σ.map (matrixAction b (matrixPoint i l (pointMap q x)) v)).toMul.val
  rw [he, hσ', he]
  let F := (groupPointsFunctor ℝ).obj G.val
  let C := constants realPointsAlgebra
  have hτ : coefficientConjugation ≫ C = C ≫ τ := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    apply TrivSqZeroExt.ext
    · rfl
    · exact (map_zero Complex.conjAe).symm
  change (F.map C).hom ((F.map coefficientConjugation).hom x) * (T (σ.map v)).toMul.val *
      ((F.map C).hom ((F.map coefficientConjugation).hom x))⁻¹ =
    (F.map τ).hom ((F.map C).hom x * (T v).toMul.val * ((F.map C).hom x)⁻¹)
  have hc : (F.map C).hom ((F.map coefficientConjugation).hom x) =
      (F.map τ).hom ((F.map C).hom x) := by
    change ((F.map coefficientConjugation ≫ F.map C).hom x) =
      ((F.map C ≫ F.map τ).hom x)
    rw [← F.map_comp, hτ, F.map_comp]
  change (F.map C).hom ((F.map coefficientConjugation).hom x) * E (σ.map v).toMul.val *
      ((F.map C).hom ((F.map coefficientConjugation).hom x))⁻¹ =
    (F.map τ).hom ((F.map C).hom x * E v.toMul.val * ((F.map C).hom x)⁻¹)
  rw [hc, hσ']
  rw [map_mul, map_mul, map_inv]
  rfl

private theorem quotientInvolution {X Y : Type} [Group X] [Group Y] (q : X →* Y)
    (u : MulAut X) (hq : Function.Surjective q) (hu : Function.Involutive u)
    (hk : ∀ x, q x = 1 → q (u x) = 1) :
    ∃ v : MulAut Y, ∀ x, q (u x) = v (q x) := by
  let f := q.comp u.toMonoidHom
  have he : q.ker = f.ker := le_antisymm hk fun x hx => by
    exact hu x ▸ hk (u x) hx
  let e := QuotientGroup.liftEquiv q.ker hq rfl
  have hsurj : Function.Surjective f := hq.comp u.surjective
  let s := QuotientGroup.liftEquiv q.ker hsurj he
  refine ⟨e.symm.trans s, ?_⟩
  intro x
  change f x = s (e.symm (q x))
  have h1 : e (QuotientGroup.mk x) = q x := QuotientGroup.liftEquiv_mk q.ker hq rfl x
  rw [← h1, MulEquiv.symm_apply_apply]
  exact (QuotientGroup.liftEquiv_mk q.ker hsurj he x).symm

private theorem quotientActionByAdjoint {idx V X Y : Type} [Fintype idx] [DecidableEq idx]
    [AddCommGroup V] [Module ℂ V] [Group X] [Group Y] (q : X →* Y)
    (f : Y →* Matrix.GeneralLinearGroup idx ℂ) (b : Module.Basis idx ℂ V)
    (u : MulAut X) (D : V → V) (Dinv : V → V) (hD : Function.RightInverse Dinv D)
    (hq : Function.Surjective q) (hf : Function.Injective f) (hu : Function.Involutive u)
    (hc : ∀ x v, matrixAction b (f (q (u x))) (D v) = D (matrixAction b (f (q x)) v)) :
    ∃ w : MulAut Y, (∀ x, q (u x) = w (q x)) ∧
      (∀ y v, matrixAction b (f (w y)) v = D (matrixAction b (f y) (Dinv v))) := by
  have hk (x : X) (h : q x = 1) : q (u x) = 1 := by
    apply hf
    apply matrixAction_injective b
    funext v
    have hv := hc x (Dinv v)
    rw [hD, h, map_one, matrixAction_one, hD] at hv
    rw [map_one, matrixAction_one]
    exact hv
  obtain ⟨w, hw⟩ := quotientInvolution q u hq hu hk
  refine ⟨w, hw, ?_⟩
  intro y v
  obtain ⟨x, rfl⟩ := hq y
  have he := hc x (Dinv v)
  rw [hD v] at he
  rw [← hw x]
  exact he

end AdjointActions

section Transport

set_option maxHeartbeats 600000 in
/-- The polar involutions of the actual complex identity Lie algebra lift to
the simply connected group and act by conjugation on its adjoint model. -/
theorem exceptionalLieAutomorphismTransport : Statement := by
  intro G _ _ _ _ _ hG hsc _
  obtain ⟨s, hs⟩ := liftPolarActions G hG.1 hsc
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨σL, ωL, θL, cL, ω, θ, c, aω, aθ, ac, hσ, hωL, hθL, hcommL, hcL,
    haω, haθ, hac, hdω, hdθ, hdc, hθ, hω, hcomm, hc⟩ := hs
  refine ⟨s, σL, ωL, θL, cL, ω, θ, c, aω, aθ, ac, hσ, hωL, hθL, hcommL, hcL,
    haω, haθ, hac, hdω, hdθ, hdc, hω, hθ, hcomm, hc, ?_⟩
  obtain ⟨Z, Q, q, d, N, A, i, j, l, b, hq, hcentral, hZ, hClosed, hj, hsurj, hgeom,
    hAdj, hPreserves, hAll⟩ := complexAdjointComparison G hG.1 s
  let f := matrixPoint (i ≫ j) l
  let B := (matrixPoint j l).range
  letI : IsClosedImmersion j.hom.hom.left := hj
  letI : IsClosedImmersion (i.hom.hom.left ≫ j.hom.hom.left) := hClosed
  have hi : IsClosedImmersion i.hom.hom.left :=
    IsClosedImmersion.of_comp_isClosedImmersion i.hom.hom.left j.hom.hom.left
  have hB (y : ComplexPoints Q) : f y ∈ B := (hAll _).mp (hPreserves y).1
  have hEmbed := adjointPoint_closedEmbedding i j l hi hj hgeom B (fun p => p.property) hB
  have hσAdj := adjoint_intertwines_groundField q (i ≫ j) l s b hAdj σL hσ
  have hωAdj (x : ComplexPoints G) (v : Lie ℂ (complexGroup G)) :
      matrixAction b (f (pointMap q (ω x))) (ωL.map v) =
        ωL.map (matrixAction b (f (pointMap q x)) v) := by
    have he := adjoint_intertwines_algebraic q (i ≫ j) l s b hAdj aω _ haω
      (realConjugation G x) (σL.map v)
    rw [realConjugation_involutive, ← hdω v, hσAdj x v, ← hdω] at he
    exact he
  have hθAdj (x : ComplexPoints G) (v : Lie ℂ (complexGroup G)) :
      matrixAction b (f (pointMap q (θ x))) (θL v) =
        θL (matrixAction b (f (pointMap q x)) v) := by
    have he := adjoint_intertwines_algebraic q (i ≫ j) l s b hAdj aθ _ haθ x v
    simpa only [← hdθ] using he
  have hf : Function.Injective f := matrixPoint_injective_of_closed (i ≫ j) l hClosed
  obtain ⟨ωQ, hωQ, hωAction⟩ := quotientActionByAdjoint (pointMap q) f b ω
    ωL.map ωL.map ωL.involutive hsurj hf hω hωAdj
  obtain ⟨θQ, hθQ, hθAction⟩ := quotientActionByAdjoint (pointMap q) f b θ
    θL θL.symm θL.apply_symm_apply hsurj hf hθ hθAdj
  exact ⟨Z, Q, q, d, N, i ≫ j, l, b, B, hq, hcentral, hZ, hClosed, hsurj, hAdj,
    fun m => (hAll m).symm, hB, hEmbed.1, hEmbed.2,
    adjointConjugation_faithful G Q hG.1 Z q hq hZ hsurj, ωQ, θQ, hωQ, hθQ, hωAction, hθAction⟩

end Transport

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalLieAutomorphismTransport
