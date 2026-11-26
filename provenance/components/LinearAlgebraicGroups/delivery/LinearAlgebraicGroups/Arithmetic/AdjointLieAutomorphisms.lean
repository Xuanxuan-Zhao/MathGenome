import Specs.LinearAlgebraicGroups.Arithmetic.AdjointLieAutomorphisms
import LinearAlgebraicGroups.Descent.AdjointCocharacters
import LinearAlgebraicGroups.Representation.SemisimplyDifferentiated
import LinearAlgebraicGroups.Classification.CellHomomorphism
import LinearAlgebraicGroups.Relative.RationalDensity
import Mathlib.Algebra.Lie.Derivation.Killing
import Mathlib.Algebra.Lie.CartanCriterion
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleIdealDecomposition
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

universe u

namespace LinearAlgebraicGroups.AdjointLieAutomorphisms

open _root_.LinearAlgebraicGroups.Specs
open Specs.AdjointCocharacters (IsAdjointQuotient)
open Specs.GeometricRadicals
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.SchemeDerivedGroup (IsSolvable IsSubgroupOf)
open LinearAlgebraicGroups.EquivariantUnipotentSeries
  (exists_smooth_identity_component smooth_identity_component_normal)

open private trivialOfSubgroup connectedOfGeometricallyConnected
  from LinearAlgebraicGroups.Reductive.CentralDerived
open private solvable_iff_sections rationalSections from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private unipotent_sections_solvable from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private preimageSubgroup preimage_isNormal trivial_of_subsingleton_points
  from LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent
open private centre_baseChange from LinearAlgebraicGroups.Reductive.CentralTorus
open private baseChangeMapPullback baseChangeKernelSquare from LinearAlgebraicGroups.Affine.Components
open private component_surjects solvable_of_central_kernel schemePullback
  from LinearAlgebraicGroups.Descent.AdjointCocharacters
open private finite_of_finite_kernel from LinearAlgebraicGroups.Classification.CellHomomorphism
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k]

private theorem reductive_of_semisimple (G : AffineAlgebraicGroup k)
    (hG : IsSemisimple G) : IsReductive G := by
  let U := geometricUnipotentRadical G
  let R := geometricSolvableRadical G
  have hU := LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest G
  have hR := LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest G
  let S := closedSubgroupAlgebraicGroup U
  have hsol : IsSolvable U.group := (solvable_iff_sections S hU.1.1 hU.1.2.1).mpr
    (unipotent_sections_solvable S hU.2.1)
  exact ⟨hG.1, hG.2.1, trivialOfSubgroup (hR.2.2 U hU.1 hsol) hG.2.2⟩

private theorem semisimple_of_adjointQuotient {G Q : AffineAlgebraicGroup k}
    (hG : IsSemisimple G) (hQ : IsReductive Q)
    {Z : ClosedSubgroup G.val} {q : G.val ⟶ Q.val} (hq : IsAdjointQuotient Z q) :
    IsSemisimple Q := by
  refine ⟨hQ.1, hQ.2.1, ?_⟩
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let G' := GeometricGroup G
  let Q' := GeometricGroup Q
  let q' := F.map q
  let R := geometricSolvableRadical Q
  let S := closedSubgroupAlgebraicGroup R
  obtain ⟨hz', hc'⟩ := centre_baseChange hq.1 K
  let Z' := baseChangedSubgroup K Z hz'
  have hker : IsSchemeKernel q' Z' := baseChangeKernelSquare q Z.inclusion hq.2.1
  have hb := (baseChangeMapPullback (K := K) q.hom.hom).flip
  have hf' : Flat q'.hom.hom.left := MorphismProperty.of_isPullback hb hq.2.2.2.1
  have hl' : LocallyOfFinitePresentation q'.hom.hom.left :=
    MorphismProperty.of_isPullback hb hq.2.2.2.2.2
  have hR := LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest Q
  obtain ⟨P, p, hp⟩ := preimageSubgroup (G := G') (Q := Q') q' R
  let A := closedSubgroupAlgebraicGroup P
  obtain ⟨D⟩ := exists_smooth_identity_component A
  let B := closedSubgroupAlgebraicGroup D.subgroup
  let V := subgroupOfSubgroup P D.subgroup
  let f := D.subgroup.inclusion ≫ p
  have hp' := schemePullback hp
  have hfs : Surjective f.hom.hom.left :=
    component_surjects A S p D hR.1.2.1
      (MorphismProperty.of_isPullback hp' hf') (MorphismProperty.of_isPullback hp' hl')
  have hsG' : Smooth G'.val.X.hom :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback G.val.X.hom (fieldSpecMap k K)) hG.1
  have hcG' : ConnectedSpace G'.val.X.left :=
    hG.2.1.geometrically_connectedSpace _ _ _
      (IsPullback.of_hasPullback G.val.X.hom (fieldSpecMap k K))
  have hV : IsSmoothConnectedNormal (G := G') V :=
    ⟨D.smooth, D.connected, smooth_identity_component_normal hsG' hcG'
      P (preimage_isNormal hp hR.1.2.2) D⟩
  letI : Group.IsSolvable (rationalSections S.val) :=
    (solvable_iff_sections S hR.1.1 hR.1.2.1).mp hR.2.1
  have hcomp : V.inclusion ≫ q' = f ≫ R.inclusion := by
    change (D.subgroup.inclusion ≫ P.inclusion) ≫ q' =
      (D.subgroup.inclusion ≫ p) ≫ R.inclusion
    simp only [Category.assoc, hp.w]
  have hVsol : IsSolvable V.group :=
    solvable_of_central_kernel (A := B) (S := S) hker hc'
      V.inclusion V.isClosedImmersion f R.inclusion hcomp D.smooth D.connected
  have hRG := LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest G
  have htriv : IsTrivialSubgroup V := trivialOfSubgroup (hRG.2.2 V hV hVsol) hG.2.2
  obtain ⟨e⟩ := htriv
  have hf0 : f = 0 := IsZero.eq_of_src ((Grp.isZero_trivial _).of_iso e) _ _
  have hpoint (x : B.val.X.left) :
      f.hom.hom.left x = η[S.val.X].left (IsLocalRing.closedPoint K) := by
    rw [hf0]
    change η[S.val.X].left (B.val.X.hom x) = _
    rw [Subsingleton.elim (B.val.X.hom x) (IsLocalRing.closedPoint K)]
  letI : Subsingleton S.val.X.left := ⟨fun a b ↦ by
    obtain ⟨x, rfl⟩ := hfs.1 a
    obtain ⟨y, rfl⟩ := hfs.1 b
    exact (hpoint x).trans (hpoint y).symm⟩
  letI : Smooth S.val.X.hom := hR.1.1
  letI := isReduced_of_smooth_over_field S.val.X.hom
  exact trivial_of_subsingleton_points S

/-- The adjoint quotient of a semisimple group is semisimple, and its quotient
map and full central kernel are both finite. -/
theorem finiteSemisimpleAdjointQuotient (G : AffineAlgebraicGroup k) (hG : IsSemisimple G) :
    ∃ (Z : ClosedSubgroup G.val) (Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val),
      IsAdjointQuotient Z q ∧ IsFinite Z.group.X.hom ∧ IsFinite q.hom.hom.left ∧
        IsSemisimple Q := by
  have hGr := reductive_of_semisimple G hG
  obtain ⟨Z, Q, q, hq, hQr⟩ := Descent.AdjointCocharacters.adjointQuotientExists G hGr
  letI : IsFinite Z.group.X.hom :=
    (LinearAlgebraicGroups.Reductive.CentralDerived.semisimpleIffFiniteCentre G hGr Z hq.1).mp hG
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsAffine Q.val.X.left := Q.property.1
  letI : Flat q.hom.hom.left := hq.2.2.2.1
  letI : Surjective q.hom.hom.left := hq.2.2.2.2.1
  letI : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.2.2.2
  exact ⟨Z, Q, q, hq, inferInstance, finite_of_finite_kernel q hq.2.1,
    semisimple_of_adjointQuotient hG hQr hq⟩

section BracketEquations

open Specs.AdjointLieAutomorphisms (coordinateBracket PreservesBracket RepresentsBracketAutomorphisms)

variable {R S idx : Type u} [CommRing R] [CommRing S] [Fintype idx] [DecidableEq idx]
variable (c : idx → idx → idx → k) (f : k →+* R)

private def bracketLinear : (idx → R) →ₗ[R] (idx → R) →ₗ[R] (idx → R) :=
  LinearMap.mk₂ R (coordinateBracket c f)
    (by intro x y z; ext l; simp [coordinateBracket, add_mul, Finset.sum_add_distrib])
    (by
      intro r x y
      ext l
      simp only [coordinateBracket, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc])
    (by intro x y z; ext l; simp [coordinateBracket, mul_add, add_mul, Finset.sum_add_distrib])
    (by
      intro r x y
      ext l
      simp only [coordinateBracket, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring)))

omit [DecidableEq idx] in
private theorem bracket_map (h : R →+* S) (x y : idx → R) :
    (fun l => h (coordinateBracket c f x y l)) =
      coordinateBracket c (h.comp f) (fun i => h (x i)) (fun j => h (y j)) := by
  ext l
  simp [coordinateBracket, map_sum, map_mul]

private def bracketEquation (M : Matrix idx idx R) (i j l : idx) : R :=
  (coordinateBracket c f (M *ᵥ Pi.single i 1) (M *ᵥ Pi.single j 1) -
    M *ᵥ coordinateBracket c f (Pi.single i 1) (Pi.single j 1)) l

private theorem bracketEquation_map (h : R →+* S) (M : Matrix idx idx R) (i j l : idx) :
    h (bracketEquation c f M i j l) = bracketEquation c (h.comp f) (M.map h) i j l := by
  have hs (i : idx) : (fun r => h ((Pi.single i 1 : idx → R) r)) = Pi.single i (1 : S) := by
    ext r
    by_cases hr : r = i <;> simp [hr]
  have hvec (x : idx → R) :
      (fun r => h ((M *ᵥ x) r)) = M.map h *ᵥ (fun r => h (x r)) := funext (h.map_mulVec M x)
  rw [bracketEquation, bracketEquation, Pi.sub_apply, Pi.sub_apply, map_sub,
    congrFun (bracket_map c f h _ _) l, congrFun (hvec _) l, bracket_map c f h,
    hvec, hvec, hs, hs]

private theorem preservesBracket_iff_equations (M : Matrix.GeneralLinearGroup idx R) :
    PreservesBracket c f M ↔ ∀ i j l, bracketEquation c f M.val i j l = 0 := by
  constructor
  · intro h i j l
    exact sub_eq_zero.mpr (congrFun (h (Pi.single i 1) (Pi.single j 1)) l)
  · intro h x y
    let B := bracketLinear c f
    let D := Matrix.toLin' M.val
    let left := (B.compl₂ D).comp D
    let right := B.compr₂ D
    have he : left = right := by
      apply (Pi.basisFun R idx).ext
      intro i
      apply (Pi.basisFun R idx).ext
      intro j
      ext l
      simpa only [Pi.basisFun_apply, left, right, B, D, bracketLinear,
        LinearMap.comp_apply, LinearMap.compl₂_apply, LinearMap.compr₂_apply,
        LinearMap.mk₂_apply, Matrix.toLin'_apply] using (sub_eq_zero.mp (h i j l))
    exact LinearMap.congr_fun (LinearMap.congr_fun he x) y

private theorem preservesBracket_one : PreservesBracket c f (1 : Matrix.GeneralLinearGroup idx R) := by
  intro x y
  change coordinateBracket c f ((1 : Matrix idx idx R) *ᵥ x) ((1 : Matrix idx idx R) *ᵥ y) =
    (1 : Matrix idx idx R) *ᵥ coordinateBracket c f x y
  simp

private theorem preservesBracket_mul {M N : Matrix.GeneralLinearGroup idx R}
    (hM : PreservesBracket c f M) (hN : PreservesBracket c f N) : PreservesBracket c f (M * N) := by
  intro x y
  change coordinateBracket c f ((M.val * N.val) *ᵥ x) ((M.val * N.val) *ᵥ y) =
    (M.val * N.val) *ᵥ coordinateBracket c f x y
  simp only [← Matrix.mulVec_mulVec]
  rw [hM _ _, hN _ _]

private theorem preservesBracket_inv {M : Matrix.GeneralLinearGroup idx R}
    (hM : PreservesBracket c f M) : PreservesBracket c f M⁻¹ := by
  intro x y
  have hleft (z : idx → R) : M.val *ᵥ (M⁻¹.val *ᵥ z) = z := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hright (z : idx → R) : M⁻¹.val *ᵥ (M.val *ᵥ z) = z := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have h := congrArg (M⁻¹.val *ᵥ ·) (hM (M⁻¹.val *ᵥ x) (M⁻¹.val *ᵥ y))
  simpa only [hleft, hright] using h.symm

end BracketEquations

section BracketScheme

open Specs.AdjointLieAutomorphisms (PreservesBracket RepresentsBracketAutomorphisms)
open Specs.AdjointCocharacters (coordinateHopf coordinateHopfIso)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.StandardGroups (generalLinearPoints)
open HopfAlgebra Bialgebra WithConv
open scoped TensorProduct

open private hopfPoint_map from LinearAlgebraicGroups.Reductive.SemisimpleLieCentralizer

variable {idx : Type u} [Fintype idx] [DecidableEq idx]
variable (A : HopfAlgebraCategory k)
variable (e : convolutionPoints A ≅ generalLinearPoints k idx)
variable (c : idx → idx → idx → k)

private def matrixPoint (R : TestAlgebra k) (a : A →ₐ[k] R) :
    Matrix.GeneralLinearGroup idx R :=
  (e.hom.app R).hom (toConv a)

private theorem matrixPoint_natural {R S : TestAlgebra k} (h : R ⟶ S) (a : A →ₐ[k] R) :
    matrixPoint A e S (h.hom.comp a) = Matrix.GeneralLinearGroup.map h.hom.toRingHom (matrixPoint A e R a) :=
  ConcreteCategory.congr_hom (e.hom.naturality h) (toConv a)

private abbrev universalMatrix : Matrix idx idx A :=
  (matrixPoint A e (CommAlgCat.of k A) (AlgHom.id k A)).val

private def bracketIdeal : Ideal A :=
  Ideal.span (Set.range fun p : idx × idx × idx =>
    bracketEquation c (algebraMap k A) (universalMatrix A e) p.1 p.2.1 p.2.2)

private theorem bracketIdeal_le_ker (R : TestAlgebra k) (a : A →ₐ[k] R) :
    bracketIdeal A e c ≤ RingHom.ker a.toRingHom ↔
      PreservesBracket c (algebraMap k R) (matrixPoint A e R a) := by
  rw [preservesBracket_iff_equations, bracketIdeal, Ideal.span_le]
  have hM : (matrixPoint A e R a).val = (universalMatrix A e).map a :=
    congrArg Units.val (matrixPoint_natural A e (CommAlgCat.ofHom a) (AlgHom.id k A))
  have he (i j l : idx) :
      a (bracketEquation c (algebraMap k A) (universalMatrix A e) i j l) =
      bracketEquation c (algebraMap k R) (matrixPoint A e R a).val i j l := by
    calc
      _ = bracketEquation c (a.toRingHom.comp (algebraMap k A))
          ((universalMatrix A e).map a) i j l :=
        bracketEquation_map c (algebraMap k A) a.toRingHom (universalMatrix A e) i j l
      _ = _ := congrArg₂ (fun f M => bracketEquation c f M i j l) a.comp_algebraMap hM.symm
  constructor
  · intro h i j l
    exact (he i j l).symm.trans (h ⟨(i, j, l), rfl⟩)
  · rintro h _ ⟨⟨i, j, l⟩, rfl⟩
    exact (he i j l).trans (h i j l)

private theorem bracketIdeal_isHopf : (bracketIdeal A e c).IsHopfIdeal k := by
  let J := bracketIdeal A e c
  let B := A ⧸ J
  let q : A →ₐ[k] B := Ideal.Quotient.mkₐ k J
  have hq {R : TestAlgebra k} (a : B →ₐ[k] R) :
      PreservesBracket c (algebraMap k R) (matrixPoint A e R (a.comp q)) :=
    (bracketIdeal_le_ker A e c R _).mp fun x hx => by
      change a (q x) = 0
      rw [show q x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  let Rl : TestAlgebra k := CommAlgCat.of k (B ⊗[k] B)
  let l : B →ₐ[k] Rl := Algebra.TensorProduct.includeLeft
  let r : B →ₐ[k] Rl := Algebra.TensorProduct.includeRight
  let Rb : TestAlgebra k := CommAlgCat.of k B
  let Rk : TestAlgebra k := CommAlgCat.of k k
  let δ : A →ₐ[k] Rl := (Algebra.TensorProduct.map q q).comp (comulAlgHom k A)
  have hδ : matrixPoint A e Rl δ =
      matrixPoint A e Rl (l.comp q) * matrixPoint A e Rl (r.comp q) := by
    change (e.hom.app Rl).hom (toConv δ) =
      (e.hom.app Rl).hom (toConv (l.comp q)) * (e.hom.app Rl).hom (toConv (r.comp q))
    rw [← (e.hom.app Rl).hom.map_mul]
    apply congrArg ((e.hom.app Rl).hom)
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro x
    rw [show (toConv (l.comp q) * toConv (r.comp q)).ofConv x =
      (toConv (l.comp q) * toConv (r.comp q)) x from rfl, AlgHom.convMul_apply]
    have h : Algebra.TensorProduct.lift (l.comp q) (r.comp q) (fun _ _ => Commute.all _ _) =
        Algebra.TensorProduct.map q q := by
      ext y <;> simp [l, r, Rl]
    rw [h]
    rfl
  have hS : matrixPoint A e Rb (q.comp (antipodeAlgHom k A)) =
      (matrixPoint A e Rb q)⁻¹ :=
    (e.hom.app Rb).hom.map_inv (toConv q)
  have hε : matrixPoint A e Rk (counitAlgHom k A) = 1 := (e.hom.app Rk).hom.map_one
  refine { toIsCoideal := ⟨?_, ?_⟩, antipode_mem := ?_ }
  · intro x hx
    have h : PreservesBracket c (algebraMap k Rk) (matrixPoint A e Rk (counitAlgHom k A)) := by
      rw [hε]
      exact preservesBracket_one c _
    exact (bracketIdeal_le_ker A e c Rk _).mpr h hx
  · intro x hx
    have h : PreservesBracket c (algebraMap k Rl) (matrixPoint A e Rl δ) := by
      rw [hδ]
      exact preservesBracket_mul c _ (hq l) (hq r)
    exact (bracketIdeal_le_ker A e c Rl δ).mpr h hx
  · intro x hx
    have h : PreservesBracket c (algebraMap k Rb)
        (matrixPoint A e Rb (q.comp (antipodeAlgHom k A))) := by
      rw [hS]
      have hq' := hq (R := Rb) (AlgHom.id k B)
      rw [AlgHom.id_comp] at hq'
      exact preservesBracket_inv c _ hq'
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      ((bracketIdeal_le_ker A e c Rb _).mpr h hx)

private theorem bracketIdeal_iff_quotient (R : TestAlgebra k)
    (M : Matrix.GeneralLinearGroup idx R) :
    PreservesBracket c (algebraMap k R) M ↔
      ∃ b : (A ⧸ bracketIdeal A e c) →ₐ[k] R,
        matrixPoint A e R (b.comp (Ideal.Quotient.mkₐ k (bracketIdeal A e c))) = M := by
  let m : A →ₐ[k] R := ((e.inv.app R).hom M).ofConv
  have hm : matrixPoint A e R m = M :=
    DFunLike.congr_fun (congrArg GrpCat.Hom.hom (e.app R).inv_hom_id) M
  constructor
  · intro h
    have hI : bracketIdeal A e c ≤ RingHom.ker m.toRingHom :=
      (bracketIdeal_le_ker A e c R m).mpr (hm ▸ h)
    exact ⟨Ideal.Quotient.liftₐ _ m hI, hm⟩
  · rintro ⟨b, rfl⟩
    apply (bracketIdeal_le_ker A e c R _).mp
    intro x hx
    change b (Ideal.Quotient.mk _ x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

private theorem evaluation_after_quotient (L : AffineAlgebraicGroup k) (a : specGroup A ≅ L.val)
    (l : (groupPointsFunctor k).obj L.val ≅ generalLinearPoints k idx)
    (I : Ideal A) [I.IsHopfIdeal k] (R : TestAlgebra k) (b : (A ⧸ I) →ₐ[k] R) :
    (l.hom.app R).hom (((groupPointsFunctor k).map (specGroupMap (hopfQuotientMap A I) ≫ a.hom)).app R
      ((hopfSpecPointIso (hopfQuotient A I)).hom.app R (toConv b))) =
      matrixPoint A (hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso a ≪≫ l) R
        (b.comp (Ideal.Quotient.mkₐ k I)) := by
  let q := hopfQuotientMap A I
  rw [Functor.map_comp, NatTrans.comp_app, GrpCat.comp_apply, hopfPoint_map q]
  rfl

/-- The bracket equations define a closed affine group with the prescribed
points over every commutative test algebra. -/
theorem bracketAutomorphismScheme (L : AffineAlgebraicGroup k)
    (l : (groupPointsFunctor k).obj L.val ≅ generalLinearPoints k idx) :
    ∃ (H : AffineAlgebraicGroup k) (i : H.val ⟶ L.val),
      RepresentsBracketAutomorphisms c i l := by
  let A := Specs.AdjointCocharacters.coordinateHopf L
  let a := Specs.AdjointCocharacters.coordinateHopfIso L
  let e := hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso a ≪≫ l
  let I := bracketIdeal A e c
  letI : I.IsHopfIdeal k := bracketIdeal_isHopf A e c
  let q := hopfQuotientMap A I
  let j := specGroupMap q
  letI : IsClosedImmersion j.hom.hom.left :=
    (hopfMapClosedImmersion k q).mpr Ideal.Quotient.mk_surjective
  letI : IsIso a.hom.hom.hom.left :=
    (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso a.hom
  have hi : IsClosedImmersion (j ≫ a.hom).hom.hom.left :=
    IsClosedImmersion.comp j.hom.hom.left a.hom.hom.hom.left
  let H : AffineAlgebraicGroup k := closedSubgroupAlgebraicGroup (G := L) ⟨_, j ≫ a.hom, hi⟩
  refine ⟨H, j ≫ a.hom, hi, ?_⟩
  intro R M
  rw [bracketIdeal_iff_quotient A e c R M]
  let τ := (hopfSpecPointIso (hopfQuotient A I)).app R
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨τ.hom (toConv b), ?_⟩
    exact (evaluation_after_quotient A L a l I R b).trans hb
  · rintro ⟨p, hp⟩
    obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso τ.hom).2 p
    exact ⟨b.ofConv, (evaluation_after_quotient A L a l I R b.ofConv).symm.trans hp⟩

end BracketScheme

section BracketTangents
attribute [local instance 100] LieRing.ofAssociativeRing

open Specs.AdjointLieAutomorphisms (coordinateBracket PreservesBracket)
open AdjointRepresentation (GroupPoints)
open InfinitesimalCommutator (matrixDifferential)

variable {idx : Type u} [Fintype idx] [DecidableEq idx]

private theorem coordinateBracket_basis {V : Type u} [LieRing V] [LieAlgebra k V]
    (b : Module.Basis idx k V) (x y : V) :
    coordinateBracket (fun i j l => b.repr ⁅b i, b j⁆ l) (RingHom.id k)
      (b.equivFun x) (b.equivFun y) = b.equivFun ⁅x, y⁆ := by
  let B := bracketLinear (fun i j l => b.repr ⁅b i, b j⁆ l) (RingHom.id k)
  let E := b.equivFun
  let C := ((LieAlgebra.ad k V).toLinearMap.compl₂ E.symm.toLinearMap).comp E.symm.toLinearMap
  have hB : B = C.compr₂ E.toLinearMap := by
    apply (Pi.basisFun k idx).ext
    intro i
    apply (Pi.basisFun k idx).ext
    intro j
    funext l
    simp [B, C, E, bracketLinear, coordinateBracket, Pi.basisFun_apply,
      Pi.single_apply, mul_ite, ite_mul]
  have h := LinearMap.congr_fun (LinearMap.congr_fun hB (b.equivFun x)) (b.equivFun y)
  simpa [B, C, E, bracketLinear] using h

omit [DecidableEq idx] in
private theorem dual_mulVec_constants (M : Matrix idx idx (DualNumber k)) (x : idx → k) :
    (fun i => (M.mulVec (fun j => algebraMap k (DualNumber k) (x j)) i).fst) =
      (M.map TrivSqZeroExt.fst) *ᵥ x ∧
    (fun i => (M.mulVec (fun j => algebraMap k (DualNumber k) (x j)) i).snd) =
      (M.map TrivSqZeroExt.snd) *ᵥ x := by
  constructor <;> ext i <;>
    simp [Matrix.mulVec, dotProduct, TrivSqZeroExt.fst_sum, TrivSqZeroExt.snd_sum,
      TrivSqZeroExt.fst_mul, TrivSqZeroExt.algebraMap_eq_inl]

omit [DecidableEq idx] in
private theorem bracket_dual_snd (c : idx → idx → idx → k)
    (x y : idx → DualNumber k) :
    (fun l => (coordinateBracket c (algebraMap k (DualNumber k)) x y l).snd) =
      coordinateBracket c (RingHom.id k) (fun i => (x i).fst) (fun i => (y i).snd) +
      coordinateBracket c (RingHom.id k) (fun i => (x i).snd) (fun i => (y i).fst) := by
  ext l
  simp [coordinateBracket, TrivSqZeroExt.snd_sum, TrivSqZeroExt.fst_mul,
    TrivSqZeroExt.algebraMap_eq_inl, Finset.sum_add_distrib]

private theorem infinitesimal_bracket_identity (c : idx → idx → idx → k)
    (M : Matrix.GeneralLinearGroup idx (DualNumber k))
    (hM : PreservesBracket c (algebraMap k (DualNumber k)) M)
    (h₁ : M.val.map TrivSqZeroExt.fst = 1) (x y : idx → k) :
    let D := M.val.map TrivSqZeroExt.snd
    D *ᵥ coordinateBracket c (RingHom.id k) x y =
      coordinateBracket c (RingHom.id k) x (D *ᵥ y) +
      coordinateBracket c (RingHom.id k) (D *ᵥ x) y := by
  let f := algebraMap k (DualNumber k)
  let X := fun i => f (x i)
  let Y := fun i => f (y i)
  have hb : (fun i => f (coordinateBracket c (RingHom.id k) x y i)) =
      coordinateBracket c f X Y :=
    bracket_map c (RingHom.id k) f x y
  have ht := congrArg (fun v : idx → DualNumber k => fun l => (v l).snd) (hM X Y)
  change (fun l => (coordinateBracket c f (M.val *ᵥ X) (M.val *ᵥ Y) l).snd) =
    (fun l => ((M.val *ᵥ coordinateBracket c f X Y) l).snd) at ht
  rw [bracket_dual_snd, ← hb] at ht
  dsimp only [X, Y, f] at ht
  simp only [(dual_mulVec_constants M.val _).1, (dual_mulVec_constants M.val _).2,
    h₁, Matrix.one_mulVec] at ht
  exact ht.symm

/-- The linear term of an infinitesimal bracket automorphism is a derivation. -/
private def bracketAutomorphismDerivation {V : Type u} [LieRing V] [LieAlgebra k V]
    (b : Module.Basis idx k V) (M : Matrix.GeneralLinearGroup idx (DualNumber k))
    (hM : PreservesBracket (fun i j l => b.repr ⁅b i, b j⁆ l)
      (algebraMap k (DualNumber k)) M) (h₁ : M.val.map TrivSqZeroExt.fst = 1) :
    LieDerivation k V V where
  toLinearMap := b.equivFun.symm.toLinearMap.comp
    ((Matrix.toLin' (M.val.map TrivSqZeroExt.snd)).comp b.equivFun.toLinearMap)
  leibniz' x y := by
    let D := M.val.map TrivSqZeroExt.snd
    let d : V →ₗ[k] V := b.equivFun.symm.toLinearMap.comp
      ((Matrix.toLin' D).comp b.equivFun.toLinearMap)
    have hd (z : V) : b.equivFun (d z) = D *ᵥ b.equivFun z := by
      change b.equivFun (b.equivFun.symm (Matrix.toLin' D (b.equivFun z))) = _
      rw [LinearEquiv.apply_symm_apply, Matrix.toLin'_apply]
    change d ⁅x, y⁆ = ⁅x, d y⁆ - ⁅y, d x⁆
    rw [← lie_skew y (d x), sub_neg_eq_add]
    apply b.equivFun.injective
    rw [map_add, hd, ← coordinateBracket_basis b x y, ← coordinateBracket_basis b x (d y),
      ← coordinateBracket_basis b (d x) y, hd, hd]
    exact infinitesimal_bracket_identity _ M hM h₁ _ _

private theorem lieIsKilling [CharZero k] (G : AffineAlgebraicGroup k)
    (hG : IsSemisimple G) (s : IdentityLieStructure G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    LieAlgebra.IsKilling k (Lie k G.val) := by
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨hfin, hrad⟩ := Representation.SemisimplyDifferentiated.lieSemisimple G hG s
  letI : FiniteDimensional k (Lie k G.val) := hfin
  letI : LieAlgebra.HasTrivialRadical k (Lie k G.val) := ⟨hrad⟩
  infer_instance

open AdjointRepresentation (GroupPoints)
open Specs.AdjointLieAutomorphisms (RepresentsBracketAutomorphisms)
open Specs.StandardGroups (generalLinearPoints)

open private matrixDual_kernel matrixDifferential_injective
  from LinearAlgebraicGroups.Affine.LieBracket

/-- In characteristic zero the differential of the adjoint action is onto
the identity tangent of the bracket-automorphism scheme. -/
theorem bracketDifferential_surjective [CharZero k]
    (G A L : AffineAlgebraicGroup k) (hG : IsSemisimple G) (s : IdentityLieStructure G.val)
    (b : letI := s.lieRing; letI := s.lieAlgebra; Module.Basis idx k (Lie k G.val))
    (f : G.val ⟶ A.val) (j : A.val ⟶ L.val)
    (l : (groupPointsFunctor k).obj L.val ≅ generalLinearPoints k idx)
    (hj : letI := s.lieRing; letI := s.lieAlgebra;
      RepresentsBracketAutomorphisms (fun i d r => b.repr ⁅b i, b d⁆ r) j l)
    (hd : letI := s.lieRing; letI := s.lieAlgebra;
      ∀ x y : Lie k G.val, matrixDifferential (f ≫ j) l x *ᵥ b.equivFun y = b.equivFun ⁅x, y⁆) :
    Function.Surjective (mapPointKernel f) := by
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : FiniteDimensional k (Lie k G.val) := Module.Finite.of_basis b
  letI : LieAlgebra.IsKilling k (Lie k G.val) := lieIsKilling G hG s
  intro p
  let R := CommAlgCat.of k (DualNumber k)
  let t := (groupPointsFunctor k).map j ≫ l.hom
  let m := mapDualKernel t p
  let M : Matrix.GeneralLinearGroup idx (DualNumber k) := m.toMul.val
  have hM := (hj.2 R M).mpr ⟨p.toMul.val, rfl⟩
  have h₁ : M.val.map TrivSqZeroExt.fst = 1 :=
    congrArg TrivSqZeroExt.fst (matrixDual_kernel m)
  let D := bracketAutomorphismDerivation b M hM h₁
  obtain ⟨x, hx⟩ := LieDerivation.IsKilling.exists_eq_ad D
  refine ⟨x, matrixDifferential_injective j l hj.1 ?_⟩
  unfold matrixDifferential
  rw [← (lieFunctoriality k).2.2 G.val A.val L.val f j x]
  change matrixDifferential (f ≫ j) l x = M.val.map TrivSqZeroExt.snd
  apply Matrix.ext_of_mulVec_single
  intro i
  have hb : b.equivFun (b i) = Pi.single i 1 := by
    funext d
    by_cases h : i = d <;> simp [Module.Basis.equivFun_self, h, eq_comm]
  rw [← hb, hd]
  have h := congrArg (fun a : LieDerivation k (Lie k G.val) (Lie k G.val) =>
    b.equivFun (a (b i))) hx
  rw [LieDerivation.ad_apply_apply] at h
  change b.equivFun ⁅x, b i⁆ =
    b.equivFun (b.equivFun.symm (Matrix.toLin' (M.val.map TrivSqZeroExt.snd) (b.equivFun (b i)))) at h
  simpa only [LinearEquiv.apply_symm_apply, Matrix.toLin'_apply] using h

end BracketTangents

section Centre

open Opposite
open AdjointRepresentation (GroupPoints constants)
open private familyCentralizer commutesOver_iff
  from LinearAlgebraicGroups.Representation.SemisimplyDifferentiated
open private affineBaseTerminal from LinearAlgebraicGroups.Solvable.SplitFixedPoint
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private closedSubgroup_iso_of_smooth_lie_surjective
  from LinearAlgebraicGroups.Relative.RationalDensity

private theorem centralizes_of_tangent_commutes [CharZero k]
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (g : GroupPoints G.val (CommAlgCat.of k k))
    (hg : ∀ p : Lie k G.val, Commute (mapPoints (constants (CommAlgCat.of k k)) g) p.toMul.val) :
    Centralizes (𝟙 G.val) g := by
  let U := (testSpec k).obj (op (CommAlgCat.of k k))
  let D := (testSpec k).obj (op (CommAlgCat.of k (DualNumber k)))
  let a : D ⟶ U := (testSpec k).map (constants (CommAlgCat.of k k)).op
  have hU : IsTerminal U := affineBaseTerminal k
  letI : IsAffine U.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
  obtain ⟨C, hC⟩ := familyCentralizer G (A := U) g
  have hinj : Mono C.inclusion.hom.hom := by
    letI := C.isClosedImmersion
    exact Over.mono_of_mono_left _
  have htan : Function.Surjective (mapPointKernel C.inclusion) := by
    intro p
    obtain ⟨z, hz⟩ := (hC D p.toMul.val).mp ((commutesOver_iff g p.toMul.val).mpr
      (fun Y t w => by
        have ht : t = w ≫ a := hU.hom_ext _ _
        rw [ht, Category.assoc]
        have h := congrArg (w ≫ ·) (hg p).eq
        change (w ≫ a ≫ g) * (w ≫ p.toMul.val) = (w ≫ p.toMul.val) * (w ≫ a ≫ g)
        simpa only [MonObj.comp_mul, Category.assoc] using h))
    let e := (testSpec k).map (dualReduction k).op
    have hz' : e ≫ z = 1 := by
      apply (cancel_mono C.inclusion.hom.hom).mp
      rw [Category.assoc, hz, MonObj.one_comp]
      exact p.toMul.property
    let v : Lie k C.group := Additive.ofMul ⟨z, hz'⟩
    exact ⟨v, Subtype.ext hz⟩
  have hCs : Smooth C.group.X.hom :=
    characteristicZeroSmoothness k (closedSubgroupAlgebraicGroup C)
  letI : IsIso C.inclusion := closedSubgroup_iso_of_smooth_lie_surjective G hG C hCs htan
  have he : (inv C.inclusion).hom.hom ≫ C.inclusion.hom.hom = 𝟙 G.val.X :=
    congrArg (Grp.forget (SchemeOver k)).map (IsIso.inv_hom_id C.inclusion)
  have hfix := (hC G.val.X (𝟙 G.val.X)).mpr ⟨(inv C.inclusion).hom.hom, he⟩
  apply (centralizes_iff (𝟙 G.val) g).mpr
  intro Y t w
  change Commute (t ≫ g) (w ≫ 𝟙 G.val.X)
  simpa only [Category.comp_id] using (commutesOver_iff g (𝟙 G.val.X)).mp hfix Y t w

end Centre

section Components

open Specs.AdjointLieAutomorphisms (IsGeometricIdentityComponent)
open Specs.AdjointCocharacters (coordinateHopfIso)
open Opposite

open private smooth_spec_iff from LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
open private groupPresentation from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private factors_through_closed_of_range
  from LinearAlgebraicGroups.Relative.RationalDensity

/-- A smooth closed subgroup that exhausts the tangent of an integral group is
the full subgroup, by the augmentation-ideal form of the tangent criterion. -/
private theorem closedSubgroup_iso_of_surjective_tangent (G : AffineAlgebraicGroup k)
    [IsIntegral G.val.X.left] (H : ClosedSubgroup G.val)
    (hH : Smooth H.group.X.hom) (hd : Function.Surjective (mapPointKernel H.inclusion)) :
    IsIso H.inclusion := by
  obtain ⟨A, hA, ⟨e⟩⟩ := groupPresentation G
  let j := H.inclusion ≫ e.inv
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  letI : IsIso e.inv.hom.hom.left := F.map_isIso e.inv
  letI := H.isClosedImmersion
  have hj : IsClosedImmersion j.hom.hom.left :=
    IsClosedImmersion.comp H.inclusion.hom.hom.left e.inv.hom.hom.left
  obtain ⟨J, ⟨hJ, eH, heH⟩, _⟩ := (closedSubgroupClassification k A H.group j).mp hj
  letI := hJ
  let q := hopfQuotientMap A J
  let i := specGroupMap q
  have hd' : Function.Surjective (mapPointKernel i) := by
    intro x
    obtain ⟨y, hy⟩ := hd (mapPointKernel e.hom x)
    refine ⟨mapPointKernel eH.hom y, ?_⟩
    rw [← (lieFunctoriality k).2.2, heH]
    change mapPointKernel (H.inclusion ≫ e.inv) y = x
    rw [(lieFunctoriality k).2.2, hy, ← (lieFunctoriality k).2.2, e.hom_inv_id,
      (lieFunctoriality k).2.1]
  have hs : Smooth (specGroup (hopfQuotient A J)).X.hom := by
    letI := hH
    letI : IsIso eH.inv.hom.hom.left := F.map_isIso eH.inv
    rw [← eH.inv.hom.hom.w]
    infer_instance
  letI : Algebra.Smooth k (A ⧸ J) := (smooth_spec_iff (k := k) (A := A ⧸ J)).mp hs
  letI : IsDomain A := (affine_isIntegral_iff (CommRingCat.of A)).mp
    (IsIntegral.of_isIso e.inv.hom.hom.left)
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hJ0 := LinearAlgebraicGroups.Relative.RationalDensity.hopfQuotient_eq_bot_of_surjective_tangent
    A J hd'
  have hq : Function.Bijective q.hom := ⟨fun x y hxy => by
    have h : x - y ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp (by
      change q.hom (x - y) = 0
      rw [map_sub, hxy, sub_self])
    simpa [hJ0, sub_eq_zero] using h, Ideal.Quotient.mk_surjective⟩
  let e₀ := CommHopfAlgCat.isoMk (BialgEquiv.ofBijective q.hom hq)
  letI : IsIso i := (hopfSpec (CommRingCat.of k)).map_isIso e₀.op.hom
  have he : H.inclusion = (eH.hom ≫ i) ≫ e.hom := by
    rw [heH]
    simp [j]
  rw [he]
  infer_instance

open private differential_injective from LinearAlgebraicGroups.RootData.BorelsAndChambers

private theorem identityComponentFactor [CharZero k]
    (Q A : AffineAlgebraicGroup k) (i : Q.val ⟶ A.val)
    (hi : IsClosedImmersion i.hom.hom.left) (hc : GeometricallyConnected Q.val.X.hom)
    (hd : Function.Surjective (mapPointKernel i))
    {E H : GroupScheme k} {q : A.val ⟶ E} {j : H ⟶ A.val} (hj : ComponentQuotient E H q j) :
    ∃ d : Q.val ⟶ H, IsIso d ∧ d ≫ j = i := by
  let S : ClosedSubgroup A.val := ⟨H, j, hj.closedImmersion⟩
  let B := closedSubgroupAlgebraicGroup S
  letI : Smooth Q.val.X.hom := characteristicZeroSmoothness k Q
  letI : IsReduced Q.val.X.left := isReduced_of_smooth_over_field Q.val.X.hom
  letI : ConnectedSpace Q.val.X.left := connectedOfGeometricallyConnected Q hc
  have hsub : Set.range i.hom.hom.left ⊆ Set.range j.hom.hom.left := by
    rw [hj.identityComponent]
    apply (isConnected_range i.hom.hom.left.continuous).subset_connectedComponent
    let x := Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k)))
    refine ⟨η[Q.val.X].left x, ?_⟩
    change (η[Q.val.X] ≫ i.hom.hom).left x = _
    rw [IsMonHom.one_hom]
  obtain ⟨d, hdi⟩ := factors_through_closed_of_range i S hsub
  change d ≫ j = i at hdi
  have hdj : IsClosedImmersion d.hom.hom.left := by
    letI := hj.closedImmersion
    haveI : IsClosedImmersion (d.hom.hom.left ≫ j.hom.hom.left) := by
      change IsClosedImmersion (d ≫ j).hom.hom.left
      rwa [hdi]
    exact IsClosedImmersion.of_comp_isClosedImmersion _ j.hom.hom.left
  have hds : Function.Surjective (mapPointKernel d) := by
    letI := hj.closedImmersion
    letI : Mono j.hom.hom := Over.mono_of_mono_left _
    intro x
    obtain ⟨y, hy⟩ := hd (mapPointKernel j x)
    refine ⟨y, differential_injective j ?_⟩
    rw [← (lieFunctoriality k).2.2, hdi, hy]
  have hsB : Smooth B.val.X.hom := characteristicZeroSmoothness k B
  have hcB := connectedOfGeometricallyConnected B hj.geometricallyConnected
  letI : IsIntegral B.val.X.left := WordDomainGeometry.smoothConnectedGroupIntegral B hsB hcB
  let S' : ClosedSubgroup B.val := ⟨Q.val, d, hdj⟩
  letI : IsIso d := closedSubgroup_iso_of_surjective_tangent B S'
    (characteristicZeroSmoothness k Q) hds
  exact ⟨d, inferInstance, hdi⟩

/-- A geometrically connected closed subgroup that exhausts the tangent
is the geometric identity component of a characteristic-zero affine group. -/
theorem geometricIdentityComponent_of_surjective_tangent [CharZero k]
    (Q A : AffineAlgebraicGroup k) (i : Q.val ⟶ A.val)
    (hi : IsClosedImmersion i.hom.hom.left) (hc : GeometricallyConnected Q.val.X.hom)
    (hd : Function.Surjective (mapPointKernel i)) :
    IsGeometricIdentityComponent (Q := Q) (A := A) i := by
  obtain ⟨E, H, q, j, hj, _, _, hbase⟩ := identityComponentAndQuotient k A
  obtain ⟨d, hd', hdi⟩ := identityComponentFactor Q A i hi hc hd hj
  letI := hd'
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let U := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
  have hcomp : U.map (F.map i) = U.map (F.map d) ≫ U.map (F.map j) := by
    rw [← hdi, F.map_comp, U.map_comp]
  constructor
  · change IsOpenImmersion (U.map (F.map i))
    letI : IsOpenImmersion (U.map (F.map j)) := (hbase K).openImmersion
    rw [hcomp]
    infer_instance
  · change Set.range (U.map (F.map i)) = _
    rw [hcomp]
    change Set.range (U.map (F.map j) ∘ U.map (F.map d)) = _
    have hr : Set.range (U.map (F.map d)) = Set.univ := Set.range_eq_univ.mpr
      (show Function.Surjective (U.map (F.map d)) from (U.map (F.map d)).homeomorph.surjective)
    rw [Set.range_comp, hr, Set.image_univ]
    change Set.range ((F.map j).hom.hom.left : _ → _) =
      connectedComponent (groupIdentityPoint (F.obj A.val))
    rw [(hbase K).identityComponent]
    congr 2
    exact Subsingleton.elim (α := Spec (CommRingCat.of K)) _ _

end Components

section Determinant

open Specs.AdjointRepresentation (GroupPoints)
open Specs.StandardGroups (generalLinearPoints multiplicativePoints)

open private commutativePoints_bracket from LinearAlgebraicGroups.Affine.LieLeftExact
open private schemeKernel_exists from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private closedSubgroup_iso_of_smooth_lie_surjective
  from LinearAlgebraicGroups.Relative.RationalDensity

private theorem character_eq_zero [CharZero k] (G : AffineAlgebraicGroup k)
    (hG : IsSemisimple G) (φ : G.val ⟶ (StandardGroups.multiplicativeGroup k).val) :
    φ = 0 := by
  let T := StandardGroups.multiplicativeGroup k
  let s := identityLieStructure G
  let t := identityLieStructure T
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := t.lieRing
  letI := t.lieAlgebra
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsAffine T.val.X.left := T.property.1
  obtain ⟨hfin, hrad⟩ := Representation.SemisimplyDifferentiated.lieSemisimple G hG s
  letI : FiniteDimensional k (Lie k G.val) := hfin
  obtain ⟨d, hd⟩ := identityDifferentialLieHom k G.val T.val φ s t
  have hbr (x y : Lie k G.val) : d ⁅x, y⁆ = 0 := by
    rw [LieHom.map_lie]
    exact commutativePoints_bracket (StandardGroups.multiplicativeGroupPointsIso k)
      (fun a b => Units.ext (mul_comm a.val b.val)) t (d x) (d y)
  have hperfect := LieAlgebrasAndRepresentations.semisimple_perfect k (Lie k G.val) hrad
  have hker : (⊤ : LieIdeal k (Lie k G.val)) ≤ d.ker := by
    rw [← hperfect]
    apply (LieSubmodule.lie_le_iff _ _ _).mpr
    exact fun x _ y _ => hbr x y
  have hzero (x : Lie k G.val) : mapPointKernel φ x = 0 :=
    (hd x).symm.trans (hker (LieSubmodule.mem_top x))
  obtain ⟨N, hN⟩ := schemeKernel_exists φ
  have hsur : Function.Surjective (mapPointKernel N.inclusion) := by
    intro p
    have hp : p.toMul.val ≫ φ.hom.hom = 1 :=
      congrArg (fun x : Lie k T.val => x.toMul.val) (hzero p)
    let y := hN.lift p.toMul.val (toUnit _) hp
    have hy := hN.lift_fst p.toMul.val (toUnit _) hp
    letI := N.isClosedImmersion
    letI : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
    have hbase : mapPoints (dualReduction k) y = 1 := by
      apply (cancel_mono N.inclusion.hom.hom).mp
      rw [MonObj.one_comp]
      change _ ≫ y ≫ N.inclusion.hom.hom = _
      rw [hy]
      exact p.toMul.property
    let x : Lie k N.group := Additive.ofMul ⟨y, hbase⟩
    exact ⟨x, Subtype.ext hy⟩
  letI : IsIso N.inclusion := closedSubgroup_iso_of_smooth_lie_surjective
    G (reductive_of_semisimple G hG) N
    (characteristicZeroSmoothness k (closedSubgroupAlgebraicGroup N)) hsur
  have hh : N.inclusion ≫ φ = 0 := Grp.hom_ext _ _ hN.w
  apply (cancel_epi N.inclusion).mp
  simpa only [comp_zero] using hh

private def determinantOnPoints (k : Type u) [Field k] (idx : Type u)
    [Fintype idx] [DecidableEq idx] :
    generalLinearPoints k idx ⟶ multiplicativePoints k where
  app R := GrpCat.ofHom Matrix.GeneralLinearGroup.det
  naturality R S f := by
    apply GrpCat.ext
    intro a
    exact Matrix.GeneralLinearGroup.map_det f.hom.toRingHom a

/-- All matrices in a representation of a characteristic-zero semisimple
group have determinant one on every commutative test ring. -/
theorem semisimple_det_eq_one [CharZero k] {idx : Type u} [Fintype idx] [DecidableEq idx]
    (G L : AffineAlgebraicGroup k) (hG : IsSemisimple G) (f : G.val ⟶ L.val)
    (l : (groupPointsFunctor k).obj L.val ≅ generalLinearPoints k idx)
    (R : TestAlgebra k) (g : GroupPoints G.val R) :
    let M : Matrix.GeneralLinearGroup idx R :=
      (l.hom.app R).hom (((groupPointsFunctor k).map f).app R g)
    M.val.det = 1 := by
  let T := StandardGroups.multiplicativeGroup k
  let t := StandardGroups.multiplicativeGroupPointsIso k
  let F := groupPointsFunctor k
  let a := F.map f ≫ l.hom ≫ determinantOnPoints k idx ≫ t.inv
  obtain ⟨φ, hφ⟩ := (groupHomComparison k G.val T.val G.property.1).2 a
  have h := DFunLike.congr_fun
    (congrArg (fun b : F.obj G.val ⟶ F.obj T.val => (b.app R).hom) hφ) g
  rw [character_eq_zero G hG φ] at h
  have h1 : ((F.map (0 : G.val ⟶ T.val)).app R).hom g = 1 := by
    change g ≫ (0 : G.val ⟶ T.val).hom.hom = _
    change g ≫ toUnit G.val.X ≫ η[T.val.X] = toUnit _ ≫ η[T.val.X]
    rw [comp_toUnit_assoc]
  rw [h1] at h
  have hh := congrArg (t.hom.app R).hom h
  change (t.hom.app R).hom 1 =
    (t.hom.app R).hom ((t.inv.app R).hom
      (Matrix.GeneralLinearGroup.det ((l.hom.app R).hom ((F.map f).app R g)))) at hh
  rw [map_one] at hh
  have hinv : Function.LeftInverse (t.hom.app R).hom (t.inv.app R).hom := by
    intro x
    exact DFunLike.congr_fun (congrArg GrpCat.Hom.hom (t.app R).inv_hom_id) x
  rw [hinv] at hh
  exact congrArg Units.val hh.symm

end Determinant

section Conjugation

open Opposite
open scoped TensorProduct
open AdjointRepresentation (GroupPoints TangentCoordinates conjugate constants ScalarExtension)
open Specs.AdjointLieAutomorphisms (PreservesBracket RepresentsBracketAutomorphisms)
open Specs.StandardGroups (generalLinearPoints)

open private pointConjugationIso pointConjugation_apply point_kernel_of_iso
  from LinearAlgebraicGroups.Representation.SemisimplyDifferentiated
open private affineBaseTerminal from LinearAlgebraicGroups.Solvable.SplitFixedPoint
open private geometricallyReduced_of_smooth from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private factor_group_through_subgroup from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

private abbrev baseTest (k : Type u) [Field k] := CommAlgCat.of k k
private abbrev dualTest (k : Type u) [Field k] := CommAlgCat.of k (DualNumber k)

private def baseTestSpecIso (k : Type u) [Field k] :
    𝟙_ (SchemeOver k) ≅ (testSpec k).obj (op (baseTest k)) :=
  (isTerminalTensorUnit (C := SchemeOver k)).uniqueUpToIso (affineBaseTerminal k)

private theorem conjugation_preserves_bracket {idx : Type u} [Fintype idx] [DecidableEq idx]
    (G : AffineAlgebraicGroup k) (s : IdentityLieStructure G.val)
    (b : letI := s.lieRing; letI := s.lieAlgebra; Module.Basis idx k (Lie k G.val))
    (T : letI := s.lieRing; letI := s.lieAlgebra; TangentCoordinates G.val idx b)
    (g : GroupPoints G.val (baseTest k)) (M : Matrix.GeneralLinearGroup idx k)
    (hM : letI := s.lieRing; letI := s.lieAlgebra; ∀ v : idx → k, (T.equiv (baseTest k) (M.val *ᵥ v)).toMul.val =
      conjugate g (T.equiv (baseTest k) v)) :
    letI := s.lieRing
    letI := s.lieAlgebra
    PreservesBracket (fun a d r => b.repr ⁅b a, b d⁆ r) (RingHom.id k) M := by
  letI := s.lieRing
  letI := s.lieAlgebra
  let R := baseTest k
  let D := (testSpec k).obj (op (dualTest k))
  let e := baseTestSpecIso k
  let g₀ := e.hom ≫ g
  let z : D ⟶ G.val.X := mapPoints (constants R) g
  obtain ⟨d, hd⟩ := @point_kernel_of_iso k _ G.val G.property.1 s (pointConjugationIso g₀)
  have ha : z = toUnit D ≫ g₀ := by
    change ((testSpec k).map (constants R).op) ≫ g = toUnit D ≫ e.hom ≫ g
    rw [← Category.assoc, (affineBaseTerminal k).hom_ext
      (toUnit D ≫ e.hom) ((testSpec k).map (constants R).op)]
  have hv (p : Lie k G.val) : M.val *ᵥ b.equivFun p = b.equivFun (d p) := by
    apply (T.equiv R).injective
    apply Subtype.ext
    change (T.equiv R (M.val *ᵥ b.equivFun p)).toMul.val =
      (T.equiv R (b.equivFun (d p))).toMul.val
    rw [hM, T.at_base, hd]
    let x : D ⟶ G.val.X := (T.equiv R (b.equivFun p)).toMul.val
    let y : D ⟶ G.val.X := p.toMul.val
    have hxy : x = y := T.at_base p
    change z * x * z⁻¹ = y ≫ (pointConjugationIso g₀).hom.hom.hom
    rw [hxy, ha]
    exact (pointConjugation_apply g₀ y).symm
  intro x y
  obtain ⟨p, rfl⟩ := b.equivFun.surjective x
  obtain ⟨q, rfl⟩ := b.equivFun.surjective y
  rw [hv, hv, coordinateBracket_basis, coordinateBracket_basis, hv, LieEquiv.map_lie]

private theorem scalar_bracket_constants {K V W idx : Type u} [Field K] [Algebra k K]
    [LieRing V] [LieAlgebra k V] [LieRing W] [LieAlgebra K W] [Fintype idx]
    (b : Module.Basis idx k V) (e : (K ⊗[k] V) ≃ₗ⁅K⁆ W) (i j r : idx) :
    let B := (b.baseChange K).map e.toLinearEquiv
    B.repr ⁅B i, B j⁆ r = algebraMap k K (b.repr ⁅b i, b j⁆ r) := by
  change ((b.baseChange K).map e.toLinearEquiv).repr
    ⁅e ((b.baseChange K) i), e ((b.baseChange K) j)⁆ r = _
  rw [← e.map_lie]
  simp only [Module.Basis.baseChange_apply, LieAlgebra.ExtendScalars.bracket_tmul, one_mul,
    Module.Basis.map_repr]
  change (b.baseChange K).repr (e.toLinearEquiv.symm (e.toLinearEquiv (1 ⊗ₜ[k] ⁅b i, b j⁆))) r = _
  rw [LinearEquiv.symm_apply_apply, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]

/-- The adjoint action factors through the closed group defined by the actual
bracket on the identity tangent. -/
private theorem adjoint_factors_through_bracket {idx : Type u} [Fintype idx] [DecidableEq idx]
    (G A L : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom) (s : IdentityLieStructure G.val)
    (b : letI := s.lieRing; letI := s.lieAlgebra; Module.Basis idx k (Lie k G.val))
    (T : letI := s.lieRing; letI := s.lieAlgebra; TangentCoordinates G.val idx b)
    (Ad : G.val ⟶ L.val) (j : A.val ⟶ L.val)
    (l : (groupPointsFunctor k).obj L.val ≅ generalLinearPoints k idx)
    (h : ScalarExtension s b T l Ad)
    (hj : letI := s.lieRing; letI := s.lieAlgebra;
      RepresentsBracketAutomorphisms (fun i d r => b.repr ⁅b i, b d⁆ r) j l) :
    ∃ f : G.val ⟶ A.val, f ≫ j = Ad := by
  letI := s.lieRing
  letI := s.lieAlgebra
  let K := AlgebraicClosure k
  let R := baseTest K
  let R' := (restrictTestAlgebra k K).obj R
  let H := GeometricGroup G
  let sK : IdentityLieStructure ((groupBaseChange k K).obj G.val) := identityLieStructure H
  letI := sK.lieRing
  letI := sK.lieAlgebra
  letI : AddCommMonoid (Lie K ((groupBaseChange k K).obj G.val)) :=
    sK.lieRing.toAddCommGroup.toAddCommMonoid
  letI : Module K (Lie K ((groupBaseChange k K).obj G.val)) := sK.lieAlgebra.toModule
  letI := hs
  obtain ⟨e, TK, _, _, hK⟩ := h K sK
  have he := baseTestSpecIso K
  let C : ClosedSubgroup L.val := ⟨A.val, j, hj.1⟩
  have hfac := (geometricClosedImmersionTest k K Ad.hom.hom j.hom.hom
    (geometricallyReduced_of_smooth G.val.X.hom) G.property.2.1 hj.1).mpr
  apply Exists.elim (hfac ?_) fun a ha => factor_group_through_subgroup C Ad a ha
  intro p
  let g : Points ((baseChange k K).obj G.val.X) R := he.inv ≫ p
  let jK := (baseChange k K).map j.hom.hom
  let AdK := (baseChange k K).map Ad.hom.hom
  let M : Matrix.GeneralLinearGroup idx K := (l.hom.app R').hom
    (baseChangePoint k K L.val.X R (g ≫ AdK))
  let bK := (b.baseChange K).map e.toLinearEquiv
  have hMB := conjugation_preserves_bracket H sK bK TK g M (hK R g)
  let c := fun i d r => b.repr ⁅b i, b d⁆ r
  have hc : (fun i d r => bK.repr ⁅bK i, bK d⁆ r) =
      fun i d r => algebraMap k K (c i d r) :=
    funext fun i => funext fun d => funext fun r => scalar_bracket_constants b e i d r
  have hMB' : PreservesBracket (fun i d r => algebraMap k K (c i d r)) (RingHom.id K) M :=
    (congrArg (fun tensor => PreservesBracket tensor (RingHom.id K) M) hc).mp hMB
  have hp : PreservesBracket c (algebraMap k R') M := hMB'
  obtain ⟨a, ha⟩ := (hj.2 R' M).mp hp
  let a' := (baseChangePointsEquiv K A.val.X R).symm a
  have ha' : baseChangePoint k K A.val.X R a' = a :=
    (baseChangePointsEquiv K A.val.X R).apply_symm_apply a
  have heq : a' ≫ jK = g ≫ AdK := by
    apply (baseChangePointsEquiv K L.val.X R).injective
    have hleft := baseChangePointsSchemeNaturality k K j.hom.hom R a'
    have hright : a ≫ j.hom.hom = baseChangePoint k K L.val.X R (g ≫ AdK) :=
      (ConcreteCategory.bijective_of_isIso (l.hom.app R')).1 ha
    exact hleft.trans ((congrArg (· ≫ j.hom.hom) ha').trans hright)
  have hg : he.hom ≫ g = p := he.hom_inv_id_assoc p
  refine ⟨he.hom ≫ a', ?_⟩
  change (he.hom ≫ a') ≫ jK = p ≫ AdK
  rw [Category.assoc, heq, ← Category.assoc, hg]

end Conjugation

section AdjointKernel

open Opposite
open AdjointRepresentation (GroupPoints TangentCoordinates conjugate constants ScalarExtension)
open Specs.StandardGroups (generalLinearPoints)
open Specs.CentralTorus (IsSchemeCentre)
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private geometricallyReduced_of_smooth from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private factor_group_through_subgroup from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private subgroupIso from LinearAlgebraicGroups.Reductive.CentralDerived

private theorem adjoint_matrix_eq_one_iff_centralizes [CharZero k]
    {idx : Type u} [Fintype idx] [DecidableEq idx]
    (G : AffineAlgebraicGroup k) (hG : IsReductive G) (s : IdentityLieStructure G.val)
    (b : letI := s.lieRing; letI := s.lieAlgebra; Module.Basis idx k (Lie k G.val))
    (T : letI := s.lieRing; letI := s.lieAlgebra; TangentCoordinates G.val idx b)
    (g : GroupPoints G.val (baseTest k)) (M : Matrix.GeneralLinearGroup idx k)
    (h : letI := s.lieRing; letI := s.lieAlgebra; ∀ v : idx → k, (T.equiv (baseTest k) (M.val *ᵥ v)).toMul.val =
      conjugate g (T.equiv (baseTest k) v)) :
    M = 1 ↔ Centralizes (𝟙 G.val) g := by
  letI := s.lieRing
  letI := s.lieAlgebra
  let R := baseTest k
  let D := (testSpec k).obj (op (dualTest k))
  let a := (testSpec k).map (constants R).op
  let z : D ⟶ G.val.X := a ≫ g
  let p (v : idx → k) : D ⟶ G.val.X := (T.equiv R v).toMul.val
  have hp (x : Lie k G.val) : p (b.equivFun x) = x.toMul.val := T.at_base x
  have h' (v : idx → k) : p (M.val *ᵥ v) = z * p v * z⁻¹ := h v
  constructor
  · intro hM
    apply centralizes_of_tangent_commutes G hG g
    intro x
    have hx := h' (b.equivFun x)
    rw [hM, Units.val_one, Matrix.one_mulVec, hp] at hx
    exact mul_inv_eq_iff_eq_mul.mp hx.symm
  · intro hg
    apply Units.ext
    apply Matrix.ext_of_mulVec_single
    intro i
    change M.val *ᵥ Pi.single i 1 = (1 : Matrix idx idx k) *ᵥ Pi.single i 1
    rw [Matrix.one_mulVec]
    apply (T.equiv R).injective
    apply Subtype.ext
    change p (M.val *ᵥ Pi.single i 1) = p (Pi.single i 1)
    rw [h']
    have hz := (centralizes_iff (𝟙 G.val) g).mp hg D a (p (Pi.single i 1))
    change Commute z (p (Pi.single i 1) ≫ 𝟙 G.val.X) at hz
    rw [Category.comp_id] at hz
    rw [hz.eq, mul_assoc, mul_inv_cancel, mul_one]

private theorem centralizes_precomp_iso {G : GroupScheme k} {X Y : SchemeOver k}
    (e : X ≅ Y) (g : Y ⟶ G.X) :
    Centralizes (𝟙 G) (e.hom ≫ g) ↔ Centralizes (𝟙 G) g := by
  simp only [centralizes_iff]
  constructor
  · intro h U t u
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h U (t ≫ e.inv) u
  · intro h U t u
    simpa only [Category.assoc] using h U (t ≫ e.hom) u

private theorem matrix_eq_one_iff_of_closed_comp {G A L : GroupScheme k} {R : TestAlgebra k}
    {idx : Type u} [Fintype idx] [DecidableEq idx]
    (f : G ⟶ A) (j : A ⟶ L) [Mono j.hom.hom]
    (ρ : GroupPoints L R →* Matrix.GeneralLinearGroup idx R) (hρ : Function.Injective ρ)
    (g : GroupPoints G R) :
    ρ (g ≫ (f ≫ j).hom.hom) = 1 ↔ g ≫ f.hom.hom = 1 := by
  rw [map_eq_one_iff ρ hρ]
  change g ≫ f.hom.hom ≫ j.hom.hom = 1 ↔ g ≫ f.hom.hom = 1
  rw [← Category.assoc, ← MonObj.one_comp j.hom.hom]
  exact cancel_mono j.hom.hom

private theorem adjointKernel_isCentre [CharZero k] {idx : Type u} [Fintype idx] [DecidableEq idx]
    (G A L : AffineAlgebraicGroup k) (hG : IsSemisimple G) (s : IdentityLieStructure G.val)
    (b : letI := s.lieRing; letI := s.lieAlgebra; Module.Basis idx k (Lie k G.val))
    (T : letI := s.lieRing; letI := s.lieAlgebra; TangentCoordinates G.val idx b)
    (f : G.val ⟶ A.val) (j : A.val ⟶ L.val)
    (l : (groupPointsFunctor k).obj L.val ≅ generalLinearPoints k idx)
    (hj : IsClosedImmersion j.hom.hom.left)
    (hAd : ScalarExtension s b T l (f ≫ j))
    (N : ClosedSubgroup G.val) (hN : IsSchemeKernel f N) : IsSchemeCentre N := by
  letI := s.lieRing
  letI := s.lieAlgebra
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let H := GeometricGroup G
  let R := baseTest K
  let R' := (restrictTestAlgebra k K).obj R
  let sK : IdentityLieStructure ((groupBaseChange k K).obj G.val) := identityLieStructure H
  letI := sK.lieRing
  letI := sK.lieAlgebra
  letI : AddCommMonoid (Lie K ((groupBaseChange k K).obj G.val)) :=
    sK.lieRing.toAddCommGroup.toAddCommMonoid
  letI : Module K (Lie K ((groupBaseChange k K).obj G.val)) := sK.lieAlgebra.toModule
  obtain ⟨e, TK, _, _, hK⟩ := hAd K sK
  let bK := (b.baseChange K).map e.toLinearEquiv
  have hH := reductive_of_semisimple H
    ((Reductive.RadicalBaseChange.semisimpleFieldExtension (K := K) G hG.1 hG.2.1).mpr hG)
  let j' := F.map j
  let f' := F.map f
  have hj' : IsClosedImmersion j'.hom.hom.left := MorphismProperty.of_isPullback
    (baseChangeMapPullback (K := K) j.hom.hom).flip hj
  letI := hj'
  letI : Mono j'.hom.hom := Over.mono_of_mono_left _
  let eL := baseChangePointGroupEquiv K L.val R
  let ρ : GroupPoints (F.obj L.val) R →* Matrix.GeneralLinearGroup idx K :=
    (l.hom.app R').hom.comp eL.toMonoidHom
  have hρ : Function.Injective ρ :=
    (ConcreteCategory.bijective_of_isIso (l.hom.app R')).1.comp eL.injective
  have hfix (g : GroupPoints H.val R) :
      g ≫ f'.hom.hom = 1 ↔ Centralizes (𝟙 H.val) g := by
    let M := ρ (g ≫ (F.map (f ≫ j)).hom.hom)
    have hmat : M = 1 ↔ Centralizes (𝟙 H.val) g :=
      adjoint_matrix_eq_one_iff_centralizes H hH sK bK
        TK g M (hK R g)
    have hcomp : F.map (f ≫ j) = f' ≫ j' := F.map_comp f j
    have hker : M = 1 ↔ g ≫ f'.hom.hom = 1 := by
      change ρ (g ≫ (F.map (f ≫ j)).hom.hom) = 1 ↔ _
      rw [hcomp]
      exact matrix_eq_one_iff_of_closed_comp f' j' ρ hρ g
    exact hker.symm.trans hmat
  let U : ClosedSubgroup G.val := ⟨G.val, 𝟙 _, by
    change IsClosedImmersion (𝟙 G.val.X.left)
    infer_instance⟩
  obtain ⟨Z, hZ⟩ := centralizerScheme k G U
  change IsSchemeCentre Z at hZ
  obtain ⟨hZ', hcentre⟩ := centre_baseChange hZ K
  let ZK := baseChangedSubgroup K Z hZ'
  have hN' : IsClosedImmersion (F.map N.inclusion).hom.hom.left := MorphismProperty.of_isPullback
    (baseChangeMapPullback (K := K) N.inclusion.hom.hom).flip N.isClosedImmersion
  let NK := baseChangedSubgroup K N hN'
  have hk : IsSchemeKernel f' NK := baseChangeKernelSquare f N.inclusion hN
  have hcompare (W : SchemeOver K) (w : W ⟶ H.val.X) :
      (∃ z : W ⟶ ZK.group.X, z ≫ ZK.inclusion.hom.hom = w) ↔
      Centralizes (𝟙 H.val) w := (hcentre W w).symm
  have he := baseTestSpecIso K
  have hpoint (w : 𝟙_ (SchemeOver K) ⟶ H.val.X) :
      Centralizes (𝟙 H.val) w ↔ w ≫ f'.hom.hom = 1 := by
    rw [← centralizes_precomp_iso he.symm w, ← hfix]
    change (he.inv ≫ w) ≫ f'.hom.hom = 1 ↔ w ≫ f'.hom.hom = 1
    rw [Category.assoc, ← MonObj.comp_one he.inv]
    exact (cancel_epi he.inv)
  have hfac (X Y : ClosedSubgroup G.val)
      (h : ∀ p : 𝟙_ (SchemeOver K) ⟶ (F.obj X.group).X,
        ∃ t : 𝟙_ (SchemeOver K) ⟶ (F.obj Y.group).X,
          t ≫ (F.map Y.inclusion).hom.hom = p ≫ (F.map X.inclusion).hom.hom) :
      IsSubgroupOf X Y := by
    let B := closedSubgroupAlgebraicGroup X
    letI : Smooth X.group.X.hom := characteristicZeroSmoothness k B
    obtain ⟨a, ha⟩ := (geometricClosedImmersionTest k K
      X.inclusion.hom.hom Y.inclusion.hom.hom
      (geometricallyReduced_of_smooth X.group.X.hom) B.property.2.1 Y.isClosedImmersion).mpr h
    exact factor_group_through_subgroup Y X.inclusion a ha
  have hnz : IsSubgroupOf N Z := hfac N Z (by
    intro p
    apply (hcompare _ _).mpr
    apply (hpoint _).mpr
    let p' : 𝟙_ (SchemeOver K) ⟶ NK.group.X := p
    change p' ≫ NK.inclusion.hom.hom ≫ f'.hom.hom = 1
    rw [hk.w, comp_toUnit_assoc]
    rfl)
  have hzn : IsSubgroupOf Z N := hfac Z N (by
    intro p
    apply (schemeKernel_sections hk _).mpr
    apply (hpoint _).mp
    exact (hcompare _ _).mp ⟨p, rfl⟩)
  obtain ⟨v, hv⟩ := subgroupIso hnz hzn
  intro X g
  refine (hZ X g).trans ?_
  constructor
  · rintro ⟨z, hz⟩
    use z ≫ v.inv.hom.hom
    have hx : v.inv.hom.hom ≫ N.inclusion.hom.hom = Z.inclusion.hom.hom := by
      change (v.inv ≫ N.inclusion).hom.hom = _
      rw [← hv, Iso.inv_hom_id_assoc]
    simpa only [Category.assoc, hx] using hz
  · rintro ⟨n, hn⟩
    use n ≫ v.hom.hom.hom
    have hx : v.hom.hom.hom ≫ Z.inclusion.hom.hom = N.inclusion.hom.hom :=
      congrArg (Grp.forget (SchemeOver k)).map hv
    simpa only [Category.assoc, hx] using hn

end AdjointKernel

section RationalCosets

open Specs.AdjointRepresentation (GroupPoints)
open Specs.AdjointLieAutomorphisms (PreservesBracket RepresentsBracketAutomorphisms)
open Specs.StandardGroups (generalLinearPoints)
open private mapPoints_injective from LinearAlgebraicGroups.Classification.RankOneRelations
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient

private theorem finiteRationalComponentPoints {E : GroupScheme k}
    (hE : IsFinite E.X.hom) (hc : ComponentGalois E) :
    Finite (GroupPoints E (CommAlgCat.of k k)) := by
  letI := hE
  let K := SeparableClosure k
  have hfin : Finite (Points E.X (CommAlgCat.of k K)) := hc.1
  let a : CommAlgCat.of k k ⟶ CommAlgCat.of k K := CommAlgCat.ofHom (Algebra.ofId k K)
  letI : IsAffine E.X.left := isAffine_of_isAffineHom E.X.hom
  exact Finite.of_injective (mapPoints (X := E.X) a)
    (mapPoints_injective ‹IsAffine E.X.left› a (algebraMap k K).injective)

/-- The rational points in a geometrically connected closed subgroup with
surjective differential account for every rational coset of the bracket
automorphism group up to a finite list of rational matrices. -/
theorem rationalBracketCosets [CharZero k] {idx : Type u} [Fintype idx] [DecidableEq idx]
    (Q A L : AffineAlgebraicGroup k) (i : Q.val ⟶ A.val)
    (hi : IsClosedImmersion i.hom.hom.left) (hc : GeometricallyConnected Q.val.X.hom)
    (hd : Function.Surjective (mapPointKernel i))
    (j : A.val ⟶ L.val) (l : (groupPointsFunctor k).obj L.val ≅ generalLinearPoints k idx)
    (c : idx → idx → idx → k) (hj : RepresentsBracketAutomorphisms c j l) :
    ∃ (m : ℕ) (r : Fin m → Matrix.GeneralLinearGroup idx k),
      (∀ t, PreservesBracket c (RingHom.id k) (r t)) ∧
      ∀ M : Matrix.GeneralLinearGroup idx k, PreservesBracket c (RingHom.id k) M →
        ∃ (a : GroupPoints Q.val (CommAlgCat.of k k)) (t : Fin m),
          M = (show Matrix.GeneralLinearGroup idx k from (l.hom.app (CommAlgCat.of k k)).hom
            (((groupPointsFunctor k).map (i ≫ j)).app (CommAlgCat.of k k) a)) * r t := by
  classical
  obtain ⟨E, H, q, b, hb, _, hg, _⟩ := identityComponentAndQuotient k A
  obtain ⟨d, hIso, hdb⟩ := identityComponentFactor Q A i hi hc hd hb
  letI := hIso
  letI := finiteRationalComponentPoints hb.finite hg
  let S : ClosedSubgroup A.val := ⟨H, b, hb.closedImmersion⟩
  have hker : IsSchemeKernel q S := by
    apply IsPullback.of_map_of_faithful (Over.forget (Spec (CommRingCat.of k)))
    exact hb.kernel
  let R := CommAlgCat.of k k
  let F := groupPointsFunctor k
  let π : GroupPoints A.val R →* GroupPoints E R := ((F.map q).app R).hom
  let B : GroupPoints A.val R →* Matrix.GeneralLinearGroup idx k :=
    (l.hom.app R).hom.comp ((F.map j).app R).hom
  letI := Fintype.ofFinite π.range
  let n := Fintype.card π.range
  let e : π.range ≃ Fin n := Fintype.equivFin _
  let z (t : Fin n) : GroupPoints A.val R := (e.symm t).property.choose
  have hz (t : Fin n) : π (z t) = (e.symm t).val := (e.symm t).property.choose_spec
  refine ⟨n, fun t => B (z t), ?_, ?_⟩
  · intro t
    exact (hj.2 R (B (z t))).mpr ⟨z t, rfl⟩
  · intro M hM
    obtain ⟨a, ha⟩ := (hj.2 R M).mp hM
    let t := e ⟨π a, ⟨a, rfl⟩⟩
    have ht : π (z t) = π a := (hz t).trans (congrArg Subtype.val (e.symm_apply_apply _))
    let w := a * (z t)⁻¹
    have hw : π w = 1 := by simp [w, ht]
    obtain ⟨h, hh⟩ := (schemeKernel_sections hker w).mpr hw
    let y : GroupPoints Q.val R := ((F.map (inv d)).app R).hom h
    have hy : ((F.map i).app R).hom y = w := by
      change (h ≫ (inv d).hom.hom) ≫ i.hom.hom = w
      rw [Category.assoc, ← hdb]
      change h ≫ (inv d).hom.hom ≫ d.hom.hom ≫ b.hom.hom = w
      have hdd : (inv d).hom.hom ≫ d.hom.hom = 𝟙 H.X :=
        congrArg (Grp.forget (SchemeOver k)).map (IsIso.inv_hom_id d)
      rw [← Category.assoc (inv d).hom.hom, hdd, Category.id_comp]
      exact hh
    refine ⟨y, t, ?_⟩
    rw [F.map_comp, NatTrans.comp_app, GrpCat.comp_apply, hy]
    change M = B w * B (z t)
    rw [← B.map_mul, show w * z t = a by simp [w]]
    exact ha.symm

end RationalCosets

section AdjointRealization

open Specs.AdjointLieAutomorphisms
open AdjointRepresentation (GroupPoints TangentCoordinates conjugate)
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private reductive_of_central_quotient from LinearAlgebraicGroups.Descent.AdjointCocharacters

private theorem kernel_of_closed_factor {G Q A : GroupScheme k}
    {f : G ⟶ A} {q : G ⟶ Q} {i : Q ⟶ A} (h : q ≫ i = f)
    (hi : IsClosedImmersion i.hom.hom.left) {N : ClosedSubgroup G} (hN : IsSchemeKernel f N) :
    IsSchemeKernel q N := by
  letI := hi
  letI : Mono i.hom.hom := Over.mono_of_mono_left _
  letI := N.isClosedImmersion
  letI : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  have hcomp : q.hom.hom ≫ i.hom.hom = f.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map h
  have hunit : η[Q.X] ≫ i.hom.hom = η[A.X] := IsMonHom.one_hom _
  have hw : N.inclusion.hom.hom ≫ q.hom.hom = toUnit _ ≫ η[Q.X] := by
    apply (cancel_mono i.hom.hom).mp
    simp only [Category.assoc, hcomp, hN.w, hunit]
  refine IsPullback.mk' hw (fun X a b hab _ => (cancel_mono N.inclusion.hom.hom).mp hab) ?_
  intro X a b hab
  have hb : b = toUnit X := toUnit_unique _ _
  have hc : a ≫ f.hom.hom = toUnit X ≫ η[A.X] := by
    rw [← hcomp, ← Category.assoc, hab, Category.assoc, hunit, hb]
  exact ⟨hN.lift a (toUnit X) hc, hN.lift_fst _ _ _, by rw [hb]; exact toUnit_unique _ _⟩

/-- In characteristic zero, the adjoint quotient is a closed matrix group in
the basis of the actual Lie algebra. It is the geometric identity component
of the bracket automorphism scheme and has finitely many rational cosets there. -/
theorem adjointRealization : Specs.AdjointLieAutomorphisms.AdjointRealization.{u} := by
  intro k _ _ G hG
  let s := identityLieStructure G
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨n, b, T, L, l, Ad, hconj, hdiff, hscalar⟩ := adjointRepresentation k G s
  let c := fun a d r => b.repr ⁅b a, b d⁆ r
  obtain ⟨A, j, hj⟩ := bracketAutomorphismScheme c L l
  obtain ⟨f, hf⟩ := adjoint_factors_through_bracket G A L hG.1 s b T Ad j l hscalar hj
  have hsf : AdjointRepresentation.ScalarExtension s b T l (f ≫ j) := by rwa [hf]
  have ht := bracketDifferential_surjective G A L hG s b f j l hj (by rwa [hf])
  obtain ⟨Q, q, i, N, hqi, _, hN, hrep⟩ := schemeImageQuotient G A f
  have hZ := adjointKernel_isCentre G A L hG s b T f j l hj.1 hsf N hN
  have hNq := kernel_of_closed_factor hqi.1 hqi.2.2.2.2.2 hN
  have hq : IsAdjointQuotient N q :=
    ⟨hZ, hNq, hrep, hqi.2.1, hqi.2.2.1, hqi.2.2.2.1⟩
  have hGr := reductive_of_semisimple G hG
  have hQr := reductive_of_central_quotient hGr hNq hZ hqi.2.1 hqi.2.2.1 hqi.2.2.2.1
  have hQ := semisimple_of_adjointQuotient hG hQr hq
  letI : IsFinite N.group.X.hom :=
    (LinearAlgebraicGroups.Reductive.CentralDerived.semisimpleIffFiniteCentre G hGr N hZ).mp hG
  letI : IsAffineHom q.hom.hom.left := hqi.2.2.2.2.1
  letI : Flat q.hom.hom.left := hqi.2.1
  letI : Surjective q.hom.hom.left := hqi.2.2.1
  letI : LocallyOfFinitePresentation q.hom.hom.left := hqi.2.2.2.1
  have hfinite := finite_of_finite_kernel q hNq
  have hi := hqi.2.2.2.2.2
  have ht' : Function.Surjective (mapPointKernel i) := by
    intro x
    obtain ⟨z, hz⟩ := ht x
    refine ⟨mapPointKernel q z, ?_⟩
    rw [← (lieFunctoriality k).2.2, hqi.1, hz]
  have hAdj : q ≫ i ≫ j = Ad := by
    rw [← Category.assoc, hqi.1, hf]
  let F := groupPointsFunctor k
  letI := hi
  letI := hj.1
  refine ⟨N, Q, q, hq, inferInstance, hfinite, hQ, s, n, b, T, L, l, A, j, i,
    hj, IsClosedImmersion.comp i.hom.hom.left j.hom.hom.left,
    geometricIdentityComponent_of_surjective_tangent Q A i hi hQ.2.1 ht',
    ?_, ?_, ?_, rationalBracketCosets Q A L i hi hQ.2.1 ht' j l c hj⟩
  · intro R g v
    have hw : ((F.map (i ≫ j)).app R).hom ((F.map q).app R g) =
        (F.map Ad).app R g := by
      rw [← hAdj, F.map_comp, NatTrans.comp_app, GrpCat.comp_apply]
      rfl
    change (T.equiv R (((l.hom.app R).hom
      (((F.map (i ≫ j)).app R).hom ((F.map q).app R g))).val *ᵥ v)).toMul.val = _
    rw [hw]
    exact hconj R g v
  · rwa [hAdj]
  · intro R g
    refine ⟨?_, semisimple_det_eq_one Q L hQ (i ≫ j) l R g⟩
    apply (hj.2 R _).mpr
    refine ⟨(F.map i).app R g, ?_⟩
    change (l.hom.app R).hom (((F.map j).app R).hom (((F.map i).app R).hom g)) =
      (l.hom.app R).hom (((F.map (i ≫ j)).app R).hom g)
    rw [F.map_comp, NatTrans.comp_app, GrpCat.comp_apply]

end AdjointRealization

end

end LinearAlgebraicGroups.AdjointLieAutomorphisms
