import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.InnerTypeANormOneModel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OuterTypeAModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.InnerTypeANormOneModel

open LinearAlgebraicGroups.Specs
open Specs.AutomorphismSequence Specs.GeneralLinearStructure
open Specs.OuterTypeAModels Specs.RelativeFormComparison Specs.TypeAMatrixDescentData
open Specs.Unipotent (Index)
open Descent Descent.Forms Descent.NonabelianCohomology

noncomputable section

open private affineLift from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.InnerTypeA
open private relativeEvaluate from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
open private restriction_evaluate modelPoint modelPoint_surjective modelPoint_project
  modelPoint_coefficient restrictCoordinate extendMatrixPoints field_formula_parity
  transportedPoint_coefficient standardPointChange_matrix
  fieldSemilinearMap_semilinear map_inverse_transpose standardPointChange matrixFormula_field
  matrix_diagram_exists
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TypeAMatrixDescentData
open private extendedGroupIso extendedSpecIso_hom_fst
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private hopfIsoEquiv hopfInduced_iff hopfIsoEquiv_trans restrict_hopfIso hopfSchemeIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeFormComparison
open private conjugatesByTransportedDifference from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
open private transportedDifference_raise difference_apply
  transportedDifference standard transported inLevel inLevel_tmul raiseIso_inLevel raiseIso_symm exists_coordinate_model
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms

set_option backward.isDefEq.respectTransparency false

private abbrev fieldInclusion {k S T : Type u} [Field k] [Field S] [CommRing T]
    [Algebra k S] [Algebra S T] :
    CommAlgCat.of k S ⟶ (restrictTestAlgebra k S).obj (CommAlgCat.of S T) :=
  let C := (restrictTestAlgebra k S).obj (CommAlgCat.of S T)
  letI : Algebra k T := C.algebra
  ConcreteCategory.ofHom { toRingHom := algebraMap S T, commutes' := fun _ => rfl }

/-- A section of a faithfully flat affine quotient over a field lifts after
an extension field, by taking a closed point of an affine faithfully flat lift. -/
private theorem liftOverField {k S : Type u} [Field k] [Field S] [Algebra k S]
    {G : AffineAlgebraicGroup k} (Q : AdjointQuotient G)
    (q : fieldTest k S ⟶ Q.quotient.val.X) :
    ∃ (T : Type u) (_ : Field T) (_ : Algebra S T)
      (z : Points G.val.X ((restrictTestAlgebra k S).obj (CommAlgCat.of S T))),
      z ≫ Q.projection.hom.hom = mapPoints (fieldInclusion (k := k)) q := by
  have : Flat Q.projection.hom.hom.left := Q.fppf.1
  have : Surjective Q.projection.hom.hom.left := Q.fppf.2.1
  obtain ⟨A, f, x, _, hsurj, hx⟩ := affineLift G.property.1 Q.quotient.property.1
    Q.projection.hom.hom (R := CommAlgCat.of k S) q
  have hA : Nonempty (PrimeSpectrum A) :=
    ⟨Classical.choose (hsurj.surj (IsLocalRing.closedPoint S))⟩
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.mp hA
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let T := A ⧸ m
  let : Field T := Ideal.Quotient.field m
  let r : A →+* T := Ideal.Quotient.mk m
  let : Algebra S T := (r.comp f.hom.toRingHom).toAlgebra
  let C := (restrictTestAlgebra k S).obj (CommAlgCat.of S T)
  let e : A ⟶ C := by
    letI : Algebra k T := C.algebra
    exact ConcreteCategory.ofHom
      { toRingHom := r, commutes' := fun a => congrArg r (f.hom.commutes a).symm }
  have he : f ≫ e = fieldInclusion (k := k) := by
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  refine ⟨T, inferInstance, inferInstance, mapPoints e x, ?_⟩
  change (testSpec k).map e.op ≫ x ≫ Q.projection.hom.hom =
    (testSpec k).map (fieldInclusion (k := k)).op ≫ q
  rw [hx, ← he, op_comp, Functor.map_comp, Category.assoc]

/-- Relative evaluation on an affine test over the extension agrees with
the ordinary evaluation on the scalar extension. -/
private theorem evaluateInduced {k S : Type u} [Field k] [Field S] [Algebra k S]
    {G H : GroupScheme k}
    {f : (groupBaseChange k S).obj G ≅ (groupBaseChange k S).obj H}
    {r : relativePoints G (fieldTest k S) ≅ relativePoints H (fieldTest k S)}
    (hr : IsInduced k S f r) (T : Type u) [CommRing T] [Algebra S T]
    (x : Points ((groupBaseChange k S).obj G).X (CommAlgCat.of S T)) :
    let a := (testSpec k).map (fieldInclusion (k := k) (S := S) (T := T)).op
    relativeEvaluate r.hom (Over.mk a) (baseChangePoint k S G.X (CommAlgCat.of S T) x) =
      baseChangePoint k S H.X (CommAlgCat.of S T) (x ≫ f.hom.hom.hom) := by
  dsimp only
  apply Over.OverMorphism.ext
  rw [hr]
  change _ ≫ f.hom.hom.hom.left ≫ pullback.fst H.X.hom (fieldSpecMap k S) =
    (x.left ≫ f.hom.hom.hom.left) ≫ pullback.fst H.X.hom (fieldSpecMap k S)
  rw [Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    rfl
  · rw [pullback.lift_snd]
    change ((testSpec S).obj (op (CommAlgCat.of S T))).hom =
      x.left ≫ ((groupBaseChange k S).obj G).X.hom
    exact (Over.w x).symm

section Coordinates

variable {k S : Type u} [Field k] [Field S] [Algebra k S] [IsGalois k S]
variable {G H : AffineAlgebraicGroup k} {P Q : HopfAlgebraCategory k}

private abbrev coordinateTrivialization {K : Type u} [Field K] [Algebra k K]
    (p : specGroup P ≅ G.val) (q : specGroup Q ≅ H.val)
    (i : extendedHopf K P ≅ extendedHopf K Q) :
    TrivializationCoordinates (hopfSchemeIso (extendedGroupIso K) p q i) :=
  ⟨P, Q, p, q, extendedGroupIso K, extendedSpecIso_hom_fst K, i, rfl⟩

omit [IsGalois k S] in
private theorem relativeHopfDifference
    (p : specGroup P ≅ G.val) (q : specGroup Q ≅ H.val)
    (i : extendedHopf S P ≅ extendedHopf S Q) (σ : Gal(S/k)) :
    hopfIsoEquiv (extendedGroupIso S) p p (transportedDifference i σ).asIso =
      (transportedAut k S (hopfIsoEquiv (extendedGroupIso S) p q i) σ).asIso :=
  by
    change _ = restrictIso (fieldMap k S σ) (hopfIsoEquiv (extendedGroupIso S) p q i) ≪≫
      (hopfIsoEquiv (extendedGroupIso S) p q i).symm
    rw [restrict_hopfIso (extendedGroupIso S) (extendedSpecIso_hom_fst S) p q σ
      (conjugatesByTransportedDifference i σ), hopfIsoEquiv_trans (extendedGroupIso S) p p q,
      Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]

variable (L : FiniteGaloisIntermediateField k S)
variable {T : Type u} [Field T] [Algebra S T]

local instance towerAlgebra : Algebra L T := ((algebraMap S T).comp (algebraMap L S)).toAlgebra

omit [IsGalois k S] in
set_option maxHeartbeats 1400000 in
private theorem projectedMatrixFormula {n : ℕ} (s : SpecialMatrixPoints G n)
    (p : specGroup P ≅ G.val) (q : specGroup Q ≅ H.val)
    (j : extendedHopf L P ≅ extendedHopf L Q) (d : Aut (extendedHopf L P))
    (g : GL (Index.{u} n) L) (parity : DiagramParity)
    (h : MatrixFormula (extendMatrixPoints (K := L) s)
      ((coordinateTrivialization p q j).schemeAut d) g parity)
    (x : Points G.val.X ((restrictTestAlgebra k S).obj (CommAlgCat.of S T))) :
    let a := (testSpec k).map (fieldInclusion (k := k) (S := S) (T := T)).op
    let e := hopfIsoEquiv (extendedGroupIso S) p p (raiseIso d.asIso)
    let C := (restrictTestAlgebra k S).obj (CommAlgCat.of S T)
    let gT := GeneralLinearGroup.map (algebraMap L T) g
    let X := s.hom.app C x
    (s.hom.app C (relativeEvaluate e.hom (Over.mk a) x)).val =
      gT.val * (if parity = 1 then X.val else X⁻¹.val.transpose) * gT⁻¹.val := by
  dsimp only
  let R := CommAlgCat.of S T
  let W := CommAlgCat.of L T
  let C := (restrictTestAlgebra k S).obj R
  let B := (restrictTestAlgebra k L).obj W
  let DL := coordinateTrivialization p q j
  let DS := coordinateTrivialization p q (raiseIso (S := S) j)
  let xS := (baseChangePointsEquiv S G.val.X R).symm x
  have hxS : baseChangePoint k S G.val.X R xS = x :=
    (baseChangePointsEquiv S G.val.X R).apply_symm_apply x
  obtain ⟨v, hv⟩ := modelPoint_surjective DS.splitComparison xS
  let inc : extendedHopf L P →ₐ[k] extendedHopf S P :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k L S) (AlgHom.id k P)
  have inc_eq (y : extendedHopf L P) : inc y = inLevel L P y := by
    induction y using TensorProduct.inductionOn with
    | add a b ha hb =>
      change inc (a + b) = (scalarTowerIso P).hom.hom ((1 : S) ⊗ₜ[L] (a + b))
      rw [map_add, TensorProduct.tmul_add, map_add, ha, hb]
    | tmul a b =>
      rw [inLevel_tmul]
      rfl
  let vL : extendedHopf L P →ₐ[L] W :=
    { toRingHom := v.toRingHom.comp inc.toRingHom
      commutes' := fun a => by
        change v (inc (a ⊗ₜ[k] (1 : P))) = _
        rw [inc_eq, inLevel_tmul]
        exact v.commutes (algebraMap L S a) }
  let : Algebra k T := C.algebra
  have compatible (d' : extendedHopf L P ≅ extendedHopf L P) :
      (restrictCoordinate (vL.comp d'.inv.hom.toAlgHom) : P →ₐ[k] T) =
        (restrictCoordinate (v.comp (raiseIso (S := S) d').inv.hom.toAlgHom) : P →ₐ[k] T) := by
    apply AlgHom.ext
    intro y
    change v (inc (d'.inv.hom (1 ⊗ₜ[k] y))) = v ((raiseIso (S := S) d').inv.hom (1 ⊗ₜ[k] y))
    rw [inc_eq]
    have hh := raiseIso_inLevel L d'.symm ((1 : L) ⊗ₜ[k] y)
    rw [raiseIso_symm, inLevel_tmul, map_one] at hh
    exact congrArg (fun z : extendedHopf S P => v z) hh.symm
  have compatibleInput : (restrictCoordinate vL : P →ₐ[k] T) =
      (restrictCoordinate v : P →ₐ[k] T) := by
    apply AlgHom.ext
    intro y
    change v (inc (1 ⊗ₜ[k] y)) = v (1 ⊗ₜ[k] y)
    rw [inc_eq, inLevel_tmul, map_one]
  have input : baseChangePoint k L G.val.X W (modelPoint DL.splitComparison vL) = x := by
    rw [modelPoint_project vL p _ DL.extensionProjection, compatibleInput,
      ← modelPoint_project v p _ DS.extensionProjection]
    exact (congrArg (baseChangePoint k S G.val.X R) hv).trans hxS
  have induced := (hopfInduced_iff (extendedGroupIso S) p p (raiseIso (S := S) d.asIso) _).mpr rfl
  have eval := evaluateInduced induced T (modelPoint DS.splitComparison v)
  rw [hv, hxS] at eval
  have output :
      baseChangePoint k L G.val.X W
        (modelPoint DL.splitComparison vL ≫ (DL.schemeAut d).asIso.hom.hom.hom) =
      relativeEvaluate (hopfIsoEquiv (extendedGroupIso S) p p
        (raiseIso (S := S) d.asIso)).hom
        (Over.mk ((testSpec k).map (fieldInclusion (k := k) (S := S) (T := T)).op)) x := by
    rw [eval, ← hv]
    change _ = baseChangePoint k S G.val.X R
      (modelPoint DS.splitComparison v ≫
        (DS.schemeAut (Aut.of (raiseIso (S := S) d.asIso))).asIso.hom.hom.hom)
    rw [modelPoint_coefficient DL, modelPoint_coefficient DS,
      modelPoint_project _ p _ DL.extensionProjection, modelPoint_project _ p _ DS.extensionProjection,
      compatible]
  have hh := h W (modelPoint DL.splitComparison vL)
  change (s.hom.app B (baseChangePoint k L G.val.X W
    (modelPoint DL.splitComparison vL ≫ (DL.schemeAut d).asIso.hom.hom.hom))).val =
    _ * (if parity = 1 then (s.hom.app B (baseChangePoint k L G.val.X W
      (modelPoint DL.splitComparison vL))).val else
      (s.hom.app B (baseChangePoint k L G.val.X W
        (modelPoint DL.splitComparison vL)))⁻¹.val.transpose) * _ at hh
  rwa [output, input] at hh

omit [IsGalois k S] in
set_option maxHeartbeats 900000 in
private theorem transportParity {K : Type u} [Field K] [Algebra k K] {n : ℕ}
    (hn : 3 ≤ n) (s : SpecialMatrixPoints G n)
    (p : specGroup P ≅ G.val) (q : specGroup Q ≅ H.val)
    (j : extendedHopf K P ≅ extendedHopf K Q)
    (χ : DiagramCharacter k K) (g : Gal(K/k) → GL (Index.{u} n) K)
    (hχ : HasMatrixTransport s (hopfSchemeIso (extendedGroupIso K) p q j) χ g)
    (τ : Gal(K/k)) (B : GL (Index.{u} n) K) (δ : DiagramParity)
    (hB : MatrixFormula (extendMatrixPoints (K := K) s)
      ((coordinateTrivialization p q j).schemeAut (transportedDifference j τ)) B δ) :
    χ τ = δ := by
  apply field_formula_parity hn (g τ) B
  intro X
  let R := CommAlgCat.of K K
  let b := fieldSemilinearMap τ
  let m := extendMatrixPoints (K := K) s
  let e := (m.app R).groupIsoToMulEquiv
  let x := e.symm (SpecialLinearGroup.map τ⁻¹.toRingHom X)
  let t := standardPointChange G.val b x
  let C := coordinateTrivialization p q j
  let d := transportedDifference j τ
  let y := t ≫ (C.schemeAut d).asIso.hom.hom.hom
  have hx : baseChangeMatrix s R x = SpecialLinearGroup.map τ⁻¹.toRingHom X :=
    e.apply_symm_apply _
  have hmap : SpecialLinearGroup.map τ.toRingHom (baseChangeMatrix s R x) = X := by
    rw [hx]
    exact Subtype.ext (Matrix.ext fun a b => τ.apply_symm_apply (X.val a b))
  have ht : m.hom.app R t = X := (standardPointChange_matrix s b x).trans hmap
  have hy : IsTransportedPoint (hopfSchemeIso (extendedGroupIso K) p q j) b x y :=
    transportedPoint_coefficient C τ b (fieldSemilinearMap_semilinear τ) d
      (difference_apply (transported j) (standard K P) τ) x
  have h := hχ τ b (fieldSemilinearMap_semilinear τ) x y hy
  have h' := matrixFormula_field m hB t
  dsimp only at h h'
  change (baseChangeMatrix s R y).val = B.val *
    (if δ = 1 then (m.hom.app R t).val else (m.hom.app R t)⁻¹.val.transpose) * B⁻¹.val at h'
  rw [ht] at h'
  have hg : GeneralLinearGroup.map (algebraMap K R) (g τ) = g τ := Units.ext rfl
  have hv : (baseChangeMatrix s R x).val.map τ.toRingHom = X.val := congrArg Subtype.val hmap
  have hi : (baseChangeMatrix s R x)⁻¹.val.transpose.map τ.toRingHom =
      X⁻¹.val.transpose :=
    (map_inverse_transpose τ.toRingHom (baseChangeMatrix s R x)).symm.trans
      (congrArg (fun z : SpecialLinearGroup (Index.{u} n) K => z⁻¹.val.transpose) hmap)
  change _ = (GeneralLinearGroup.map (algebraMap K R) (g τ)).val *
    (if χ τ = 1 then (baseChangeMatrix s R x).val.map τ.toRingHom
      else (baseChangeMatrix s R x)⁻¹.val.transpose.map τ.toRingHom) *
      (GeneralLinearGroup.map (algebraMap K R) (g τ))⁻¹.val at h
  rw [hg, hv, hi] at h
  exact h.symm.trans h'

end Coordinates

/-- At a lift of the given adjoint point, the relative automorphism acts
on sections by ordinary conjugation. -/
private theorem evaluateInnerLift {k S T : Type u} [Field k] [Field S] [Field T]
    [Algebra k S] [Algebra S T] {G : AffineAlgebraicGroup k} (V : AdjointQuotient G)
    (inn : groupSections V.quotient.val ⟶ automorphisms G.val)
    (hinn : ∀ (U : SchemeOver k) (g : U ⟶ G.val.X),
      inn.app (op U) ⟨g ≫ V.projection.hom.hom⟩ = innerAut g)
    (q : fieldTest k S ⟶ V.quotient.val.X)
    (z : Points G.val.X ((restrictTestAlgebra k S).obj (CommAlgCat.of S T)))
    (hz : z ≫ V.projection.hom.hom = mapPoints (fieldInclusion (k := k)) q)
    (x : Points G.val.X ((restrictTestAlgebra k S).obj (CommAlgCat.of S T))) :
    let a := (testSpec k).map (fieldInclusion (k := k) (S := S) (T := T)).op
    relativeEvaluate (inn.app (op (fieldTest k S)) ⟨q⟩).asIso.hom (Over.mk a) x =
      z * x * z⁻¹ := by
  dsimp only
  let a := (testSpec k).map (fieldInclusion (k := k) (S := S) (T := T)).op
  let f := inn.app (op (fieldTest k S)) ⟨q⟩
  have hh := NatTrans.naturality_apply inn a.op
    (⟨q⟩ : (groupSections V.quotient.val).obj (op (fieldTest k S)))
  change inn.app (op _) ⟨mapPoints (fieldInclusion (k := k)) q⟩ = restrictAut a f at hh
  rw [← hz, hinn] at hh
  rw [← restriction_evaluate a f x, ← hh]
  change ((𝟙 _) ≫ z) * x * ((𝟙 _) ≫ z)⁻¹ = _
  rw [Category.id_comp]

set_option maxHeartbeats 1800000 in
theorem innerTypeANormOneModel : Specs.InnerTypeANormOneModel.Statement.{u} := by
  intro F _ R H G hInner ⟨e⟩ sG
  let s : SpecialMatrixPoints R 6 := (groupPointsFunctor F).mapIso e ≪≫ sG
  let S := SeparableClosure F
  obtain ⟨V, inn, hinn, _, i, hi⟩ := hInner
  obtain ⟨P, hP, ⟨p⟩⟩ := exists_coordinate_model R
  obtain ⟨Q, hQ, ⟨q⟩⟩ := exists_coordinate_model H
  let E := hopfIsoEquiv (extendedGroupIso S) p q
  let jTop := E.symm i
  have hjTop : E jTop = i := E.apply_symm_apply i
  obtain ⟨L, j, _, hj⟩ := finiteLevelIsomorphisms P Q hP hQ
    (⊥ : FiniteGaloisIntermediateField F S) jTop
  let C := coordinateTrivialization p q j
  let jScheme := hopfSchemeIso (extendedGroupIso L) p q j
  have hn : 3 ≤ (6 : ℕ) := by decide
  obtain ⟨χ, g, β, hχ, _, _, _, _, _, hModel⟩ :=
    _root_.LinearAlgebraicGroups.OuterTypeAModels.typeAModelForTrivialization hn s jScheme
  obtain ⟨δ, hδ, _⟩ := matrix_diagram_exists hn (extendMatrixPoints (K := L) s)
  have heven : χ = 1 := by
    apply MonoidHom.ext
    intro τ
    obtain ⟨σ, rfl⟩ := (AlgEquiv.restrictNormalHom_surjective S :
      Function.Surjective (restriction L)) τ
    let d := transportedDifference j (restriction L σ)
    obtain ⟨B, hB⟩ := hδ (C.schemeAut d)
    have hparity := transportParity hn s p q j χ g hχ (restriction L σ) B _ hB
    change χ (restriction L σ) = 1
    rw [hparity]
    obtain ⟨u, hu⟩ := hi σ
    let w : fieldTest F S ⟶ V.quotient.val.X := u.down
    have hu' : inn.app (op (fieldTest F S)) ⟨w⟩ = transportedAut F S i σ := hu
    obtain ⟨T, _, _, z, hz⟩ := liftOverField V w
    let A := (restrictTestAlgebra F S).obj (CommAlgCat.of S T)
    let Z := SpecialLinearGroup.toGL (s.hom.app A z)
    let : Algebra L T := towerAlgebra L
    apply field_formula_parity hn (GeneralLinearGroup.map (algebraMap L T) B) Z
    intro X
    let eX := (s.app A).groupIsoToMulEquiv
    let x : Points R.val.X A := eX.symm X
    have hx : s.hom.app A x = X := eX.apply_symm_apply X
    have hBig := relativeHopfDifference p q (raiseIso (S := S) j) σ
    rw [transportedDifference_raise L, hj, hjTop] at hBig
    have hBig' : hopfIsoEquiv (extendedGroupIso S) p p (raiseIso d.asIso) =
        (transportedAut F S i σ).asIso := hBig
    have h := projectedMatrixFormula (T := T) L s p q j d B _ hB x
    dsimp only at h
    rw [hBig', ← hu', evaluateInnerLift V inn hinn w z hz x, hx] at h
    let zMatrix : SpecialLinearGroup (Index.{u} 6) T := s.hom.app A z
    have hmul : s.hom.app A (z * x * z⁻¹) = zMatrix * X * zMatrix⁻¹ := by
      change eX (z * x * z⁻¹) = zMatrix * X * zMatrix⁻¹
      rw [map_mul, map_mul, map_inv]
      exact congrArg (fun a : SpecialLinearGroup (Index.{u} 6) T => zMatrix * a * zMatrix⁻¹) hx
    rw [hmul] at h
    have hinv : Z⁻¹.val = zMatrix⁻¹.val := by
      change (SpecialLinearGroup.toGL zMatrix)⁻¹.val = _
      rw [← map_inv]
      rfl
    rw [ite_eq_left rfl, hinv]
    exact h.symm
  obtain ⟨ρ, _, hA, hd, I, hI, b, hb⟩ := hModel.1 heven
  exact ⟨ρ.fixedSubalgebra, inferInstance, inferInstance, hA, hd, I, hI, b, hb⟩

end

end LinearAlgebraicGroups.Arithmetic.InnerTypeANormOneModel
