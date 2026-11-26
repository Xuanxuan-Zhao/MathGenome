import Specs.LinearAlgebraicGroups.Affine.LieBracket
import LinearAlgebraicGroups.Affine.IdentityTangent
import LinearAlgebraicGroups.Affine.FaithfulLinearization
import Mathlib.Algebra.Lie.OfAssociative
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite WithConv TensorProduct

universe u

namespace LinearAlgebraicGroups

noncomputable section

open InfinitesimalCommutator
open private presentationPointIso baseChangePointIso mapDualKernel_scale isAffine_baseChange from LinearAlgebraicGroups.Affine.IdentityTangent

variable {k : Type u} [Field k]

theorem twoVariablesUniversalProperty : Specs.TwoVariablesUniversalProperty.{u} := by
  intro k R _ _ _
  let s : TwoVariables k := liftS k DualNumber.eps
  let t : TwoVariables k := liftT k DualNumber.eps
  have hs : s * s = 0 :=
    (map_mul (liftS k) DualNumber.eps DualNumber.eps).symm.trans (by rw [DualNumber.eps_mul_eps, map_zero])
  have ht : t * t = 0 :=
    (map_mul (liftT k) DualNumber.eps DualNumber.eps).symm.trans (by rw [DualNumber.eps_mul_eps, map_zero])
  have hst : liftST k DualNumber.eps = s * t := by
    apply TrivSqZeroExt.ext <;> apply TrivSqZeroExt.ext
    · change 0 = (0 : k) * 0
      simp
    · change 0 = (0 : k) * 0 + 1 * 0
      simp
    · change 0 = (0 : k) * 1 + 0 * 0
      simp
    · change 1 = (0 : k) * 0 + 1 * 1 + (0 * 0 + 0 * 0)
      simp
  let P := {z : R × R // z.1 * z.1 = 0 ∧ z.2 * z.2 = 0}
  let read (f : TwoVariables k →ₐ[k] R) : P :=
    ⟨(f s, f t), by rw [← map_mul, hs, map_zero],
      by rw [← map_mul, ht, map_zero]⟩
  let first (z : P) : DualNumber k →ₐ[k] R :=
    DualNumber.lift ⟨(Algebra.ofId k R, z.val.1), z.property.1, fun _ => Commute.all _ _⟩
  let build (z : P) : TwoVariables k →ₐ[k] R :=
    DualNumber.lift ⟨(first z, z.val.2), z.property.2, fun _ => Commute.all _ _⟩
  have hfs (z : P) : build z s = z.val.1 :=
    (DualNumber.lift_apply_inl _ _).trans (DualNumber.lift_apply_eps _)
  have hft (z : P) : build z t = z.val.2 := DualNumber.lift_apply_eps _
  refine ⟨{ toFun := read, invFun := build, left_inv := ?_, right_inv := ?_ }, ?_⟩
  · intro f
    apply (DualNumber.lift (R := k) (A := DualNumber k) (B := R)).symm.injective
    apply Subtype.ext
    apply Prod.ext
    · apply DualNumber.algHom_ext
      change build (read f) s = f s
      exact hfs (read f)
    · exact hft (read f)
  · intro z
    exact Subtype.ext (Prod.ext (hfs z) (hft z))
  · intro f
    exact ⟨rfl, (congrArg f hst).trans (map_mul f s t)⟩

private abbrev dualTest := CommAlgCat.of k (DualNumber k)
private abbrev twoVariableTest := CommAlgCat.of k (TwoVariables k)

private abbrev atS : dualTest (k := k) ⟶ twoVariableTest := CommAlgCat.ofHom (liftS k)
private abbrev atT : dualTest (k := k) ⟶ twoVariableTest := CommAlgCat.ofHom (liftT k)
private abbrev atST : dualTest (k := k) ⟶ twoVariableTest := CommAlgCat.ofHom (liftST k)

private def dropT : twoVariableTest (k := k) ⟶ dualTest :=
  CommAlgCat.ofHom (TrivSqZeroExt.fstHom k (DualNumber k) (DualNumber k))

private def dropS : twoVariableTest (k := k) ⟶ dualTest :=
  CommAlgCat.ofHom
    { toRingHom := mapCoefficients (TrivSqZeroExt.fstHom k k k).toRingHom
      commutes' := fun _ => rfl }

private abbrev constants : CommAlgCat.of k k ⟶ dualTest :=
  CommAlgCat.ofHom (TrivSqZeroExt.inlAlgHom k k k)

private theorem atT_dropT : (atT : dualTest (k := k) ⟶ _) ≫ dropT =
    dualReduction k ≫ constants := rfl

private theorem atS_dropS : (atS : dualTest (k := k) ⟶ _) ≫ dropS =
    dualReduction k ≫ constants := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro z
  change (z.fst, (TrivSqZeroExt.fstHom k k k) 0) = (z.fst, 0)
  rw [map_zero]

private theorem comp_map_apply (F : TestAlgebra k ⥤ GrpCat.{u})
    {R S T : TestAlgebra k} (a : R ⟶ S) (b : S ⟶ T) (x : F.obj R) :
    (F.map (a ≫ b)).hom x = (F.map b).hom ((F.map a).hom x) := by
  rw [F.map_comp]
  rfl

private theorem nat_apply {F H : TestAlgebra k ⥤ GrpCat.{u}} (f : F ⟶ H)
    {R S : TestAlgebra k} (a : R ⟶ S) (x : F.obj R) :
    (f.app S).hom ((F.map a).hom x) = (H.map a).hom ((f.app R).hom x) :=
  congrArg (fun g => GrpCat.Hom.hom g x) (f.naturality a)

private theorem map_commutator {F H : TestAlgebra k ⥤ GrpCat.{u}} (f : F ⟶ H)
    (p q : DualKernel F) :
    (f.app twoVariableTest).hom (commutator F p q) =
      commutator H (mapDualKernel f p) (mapDualKernel f q) := by
  simp only [InfinitesimalCommutator.commutator, map_mul, map_inv, nat_apply]
  rfl

private theorem dropT_commutator (F : TestAlgebra k ⥤ GrpCat.{u}) (p q : DualKernel F) :
    (F.map dropT).hom (commutator F p q) = 1 := by
  have hy : (F.map dropT).hom ((F.map atT).hom q.toMul.val) = 1 := by
    rw [← comp_map_apply, atT_dropT, comp_map_apply, q.toMul.property, map_one]
  simp [InfinitesimalCommutator.commutator, hy]

private theorem dropS_commutator (F : TestAlgebra k ⥤ GrpCat.{u}) (p q : DualKernel F) :
    (F.map dropS).hom (commutator F p q) = 1 := by
  have hx : (F.map dropS).hom ((F.map atS).hom p.toMul.val) = 1 := by
    rw [← comp_map_apply, atS_dropS, comp_map_apply, p.toMul.property, map_one]
  simp [InfinitesimalCommutator.commutator, hx]

private theorem liftST_injective : Function.Injective (liftST k) := by
  intro a b h
  exact TrivSqZeroExt.ext
    (congrArg (fun z : TwoVariables k => z.fst.fst) h)
    (congrArg (fun z : TwoVariables k => z.snd.snd) h)

private theorem coordinate_liftST_injective (A : HopfAlgebraCategory k) :
    Function.Injective (((convolutionPoints A).map atST).hom) := by
  intro a b h
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro r
  apply liftST_injective
  exact congrArg (fun p : WithConv (A →ₐ[k] TwoVariables k) => p.ofConv r) h

private theorem point_liftST_injective (G : Specs.GroupScheme k) [IsAffine G.X.left] :
    Function.Injective ((((groupPointsFunctor k).obj G).map atST).hom) := by
  let C : AffineGroupCategory k := ⟨G, inferInstance⟩
  let i : hopfSpectrum (coordinateHopf C) ≅ G :=
    (affineGroupInclusion k).mapIso (coordinateHopfSpecIso C)
  let e := presentationPointIso i
  intro p q h
  apply (e.app dualTest).groupIsoToMulEquiv.symm.injective
  apply coordinate_liftST_injective (coordinateHopf C)
  exact (nat_apply e.inv atST p).symm.trans
    ((congrArg (e.inv.app twoVariableTest).hom h).trans (nat_apply e.inv atST q))

private theorem mixed_factor (A : HopfAlgebraCategory k)
    (z : (convolutionPoints A).obj twoVariableTest)
    (hT : ((convolutionPoints A).map dropT).hom z = 1)
    (hS : ((convolutionPoints A).map dropS).hom z = 1) :
    ∃ p : DualKernel (convolutionPoints A), ((convolutionPoints A).map atST).hom p.toMul.val = z := by
  let x := Bialgebra.counitAlgHom k A
  let f : A →ₐ[k] TwoVariables k := z.ofConv
  have h1 (a : A) : (f a).fst = (x a, 0) :=
    congrArg (fun g : WithConv (A →ₐ[k] DualNumber k) => g.ofConv a) hT
  have h2 (a : A) : (f a).snd.fst = 0 :=
    congrArg (fun g : WithConv (A →ₐ[k] DualNumber k) => (g.ofConv a).snd) hS
  let g₀ (a : A) : DualNumber k := (x a, (f a).snd.snd)
  have hg (a : A) : liftST k (g₀ a) = f a := by
    apply TrivSqZeroExt.ext
    · exact (h1 a).symm
    · exact TrivSqZeroExt.ext (h2 a).symm rfl
  let g : A →ₐ[k] DualNumber k :=
    { toFun := g₀
      map_zero' := liftST_injective (by rw [hg, map_zero, map_zero])
      map_one' := liftST_injective (by rw [hg, map_one, map_one])
      map_add' a b := liftST_injective (by simp only [map_add, hg])
      map_mul' a b := liftST_injective (by simp only [map_mul, hg])
      commutes' a := liftST_injective (by rw [hg, f.commutes, (liftST k).commutes]) }
  have hker : toConv g ∈ (((convolutionPoints A).map (dualReduction k)).hom).ker := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro a
    rfl
  refine ⟨⟨toConv g, hker⟩, ?_⟩
  apply WithConv.ofConv_injective
  exact AlgHom.ext hg

private theorem bracket_point (G : Specs.GroupScheme k) [IsAffine G.X.left]
    (p q : Lie k G) :
    ∃ r : Lie k G, (((groupPointsFunctor k).obj G).map atST).hom r.toMul.val =
      commutator ((groupPointsFunctor k).obj G) p q := by
  let C : AffineGroupCategory k := ⟨G, inferInstance⟩
  let i : hopfSpectrum (coordinateHopf C) ≅ G :=
    (affineGroupInclusion k).mapIso (coordinateHopfSpecIso C)
  let e := presentationPointIso i
  let F := (groupPointsFunctor k).obj G
  let z := (e.inv.app twoVariableTest).hom (commutator F p q)
  obtain ⟨r, hr⟩ := mixed_factor (coordinateHopf C) z
    (by rw [← nat_apply, dropT_commutator, map_one])
    (by rw [← nat_apply, dropS_commutator, map_one])
  refine ⟨mapDualKernel e.hom r, ?_⟩
  change (F.map atST).hom ((e.hom.app dualTest).hom r.toMul.val) = _
  rw [← nat_apply, hr]
  exact (e.app twoVariableTest).groupIsoToMulEquiv.apply_symm_apply _

/-- The commutator of the two tangent lifts has a unique mixed tangent coefficient. -/
def lieBracket (G : Specs.GroupScheme k) [IsAffine G.X.left]
    (p q : Lie k G) : Lie k G :=
  Specs.intrinsicLieBracket k G p q

theorem lieBracket_isBracket (G : Specs.GroupScheme k) [IsAffine G.X.left] :
    IsBracket ((groupPointsFunctor k).obj G) (lieBracket G) :=
  fun p q => Classical.epsilon_spec (bracket_point G p q)

theorem identityLieBracketUnique : Specs.IdentityLieBracketUnique.{u} := by
  intro k _ G _ b c hb hc
  funext p q
  exact Subtype.ext (point_liftST_injective G ((hb p q).trans (hc p q).symm))

private theorem bracket_naturality {G H : Specs.GroupScheme k}
    [IsAffine G.X.left] [IsAffine H.X.left] (f : G ⟶ H)
    {b : Lie k G → Lie k G → Lie k G} {c : Lie k H → Lie k H → Lie k H}
    (hb : IsBracket ((groupPointsFunctor k).obj G) b)
    (hc : IsBracket ((groupPointsFunctor k).obj H) c) (p q : Lie k G) :
    mapPointKernel f (b p q) = c (mapPointKernel f p) (mapPointKernel f q) := by
  let η := (groupPointsFunctor k).map f
  apply Subtype.ext
  apply point_liftST_injective H
  change (((groupPointsFunctor k).obj H).map atST).hom
    ((η.app dualTest).hom (b p q).toMul.val) = _
  exact (nat_apply η atST (b p q).toMul.val).symm.trans
    ((congrArg (η.app twoVariableTest).hom (hb p q)).trans
      ((map_commutator η p q).trans (hc _ _).symm))

theorem identityLieBracketNaturality : Specs.IdentityLieBracketNaturality.{u} := by
  intro k _ G H _ _ f b c p q
  exact bracket_naturality f b.commutator_law c.commutator_law p q

theorem identityDifferentialLieHom : Specs.IdentityDifferentialLieHom.{u} := by
  intro k _ G H _ _ f b c
  letI : LieRing (Specs.Lie k G) := b.lieRing
  letI : LieAlgebra k (Specs.Lie k G) := b.lieAlgebra
  letI : LieRing (Specs.Lie k H) := c.lieRing
  letI : LieAlgebra k (Specs.Lie k H) := c.lieAlgebra
  let d : @LieHom k (Specs.Lie k G) (Specs.Lie k H) _
      b.lieRing b.lieAlgebra c.lieRing c.lieAlgebra := {
    toFun := mapPointKernel f
    map_add' := by
      intro p q
      have hb := congrArg (fun g : AddGroup (PointKernel G) => g.toAdd.add p q) b.group_law
      have hc := congrArg (fun g : AddGroup (PointKernel H) =>
        g.toAdd.add (mapPointKernel f p) (mapPointKernel f q)) c.group_law
      exact (congrArg (mapPointKernel f) hb).trans (((mapPointKernel f).map_add p q).trans hc.symm)
    map_smul' := by
      intro a p
      have hb := congrFun (congrFun b.scalar_law a) p
      have hc := congrFun (congrFun c.scalar_law a) (mapPointKernel f p)
      exact (congrArg (mapPointKernel f) hb).trans (((lieFunctoriality k).1 f a p).trans hc.symm)
    map_lie' := fun {p q} => bracket_naturality f b.commutator_law c.commutator_law p q
  }
  exact ⟨d, fun _ => rfl⟩

section Matrices

open Specs.StandardGroups

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

private def matrixDual {R : Type u} [CommRing R] :
    Matrix ι ι (DualNumber R) →+* DualNumber (Matrix ι ι R) where
  toFun m := (fun i j => (m i j).fst, fun i j => (m i j).snd)
  map_zero' := rfl
  map_one' := by
    apply TrivSqZeroExt.ext
    · apply Matrix.ext
      intro i j
      change ((1 : Matrix ι ι (DualNumber R)) i j).fst = (1 : Matrix ι ι R) i j
      by_cases e : i = j <;> simp [Matrix.one_apply, e]
    · apply Matrix.ext
      intro i j
      change ((1 : Matrix ι ι (DualNumber R)) i j).snd = 0
      by_cases e : i = j <;> simp [Matrix.one_apply, e]
  map_add' x y := rfl
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · apply Matrix.ext
      intro i j
      change (∑ l, x i l * y l j).fst = ∑ l, (x i l).fst * (y l j).fst
      simp only [TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul]
    · ext i j
      change (∑ l, x i l * y l j).snd =
        (∑ l, (x i l).fst * (y l j).snd) + ∑ l, (x i l).snd * (y l j).fst
      simp only [TrivSqZeroExt.snd_sum, DualNumber.snd_mul, Finset.sum_add_distrib]

private abbrev matrixTwo :
    Matrix ι ι (TwoVariables k) →+* TwoVariables (Matrix ι ι k) :=
  (mapCoefficients matrixDual).comp matrixDual

private abbrev matrixKernel := DualKernel (generalLinearPoints k ι)

private def matrixCoefficient (p : matrixKernel (k := k) (ι := ι)) : Matrix ι ι k :=
  (matrixDual p.toMul.val.val).snd

private theorem matrixDual_kernel (p : matrixKernel (k := k) (ι := ι)) :
    matrixDual p.toMul.val.val = (1, matrixCoefficient p) := by
  apply TrivSqZeroExt.ext
  · exact congrArg Units.val p.toMul.property
  · rfl

private theorem matrixCoefficient_injective :
    Function.Injective (matrixCoefficient (k := k) (ι := ι)) := by
  intro p q h
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  have he := (matrixDual_kernel p).trans ((congrArg (fun m => ((1 : Matrix ι ι k), m)) h).trans
    (matrixDual_kernel q).symm)
  exact TrivSqZeroExt.ext
    (congrArg (fun z : DualNumber (Matrix ι ι k) => z.fst i j) he)
    (congrArg (fun z : DualNumber (Matrix ι ι k) => z.snd i j) he)

private theorem matrixTwo_S (p : matrixKernel (k := k) (ι := ι)) :
    matrixTwo (((generalLinearPoints k ι).map atS).hom p.toMul.val).val =
      ((1, matrixCoefficient p), 0) := by
  apply TrivSqZeroExt.ext
  · exact matrixDual_kernel p
  · rfl

private theorem matrixTwo_T (p : matrixKernel (k := k) (ι := ι)) :
    matrixTwo (((generalLinearPoints k ι).map atT).hom p.toMul.val).val =
      (1, (matrixCoefficient p, 0)) := by
  apply TrivSqZeroExt.ext
  · exact congrArg (fun m : Matrix ι ι k => (m, (0 : Matrix ι ι k)))
      (congrArg TrivSqZeroExt.fst (matrixDual_kernel p))
  · rfl

private theorem matrixTwo_ST (p : matrixKernel (k := k) (ι := ι)) :
    matrixTwo (((generalLinearPoints k ι).map atST).hom p.toMul.val).val =
      (1, (0, matrixCoefficient p)) := by
  apply TrivSqZeroExt.ext
  · exact congrArg (fun m : Matrix ι ι k => (m, (0 : Matrix ι ι k)))
      (congrArg TrivSqZeroExt.fst (matrixDual_kernel p))
  · rfl

private theorem matrixCoefficient_inv (p : matrixKernel (k := k) (ι := ι)) :
    matrixCoefficient (Additive.ofMul p.toMul⁻¹) = -matrixCoefficient p := by
  let q : matrixKernel (k := k) (ι := ι) := Additive.ofMul p.toMul⁻¹
  have h := congrArg (fun z : Matrix.GeneralLinearGroup ι (DualNumber k) => matrixDual z.val)
    (mul_inv_cancel p.toMul.val)
  change matrixDual (p.toMul.val.val * q.toMul.val.val) = matrixDual 1 at h
  rw [map_mul, map_one, matrixDual_kernel p, matrixDual_kernel q] at h
  have hs := congrArg TrivSqZeroExt.snd h
  change 1 * matrixCoefficient q + matrixCoefficient p * 1 = 0 at hs
  rw [one_mul, mul_one] at hs
  exact eq_neg_of_add_eq_zero_left hs

private theorem matrixCoefficient_add (p q : matrixKernel (k := k) (ι := ι)) :
    matrixCoefficient (p + q) = matrixCoefficient p + matrixCoefficient q := by
  change (matrixDual (p.toMul.val.val * q.toMul.val.val)).snd = _
  rw [map_mul, matrixDual_kernel p, matrixDual_kernel q]
  change 1 * matrixCoefficient q + matrixCoefficient p * 1 = _
  rw [one_mul, mul_one, add_comm]

private theorem matrixCoefficient_scale (a : k) (p : matrixKernel (k := k) (ι := ι)) :
    matrixCoefficient (scaleDualKernel _ a p) = a • matrixCoefficient p := by
  apply Matrix.ext
  intro i j
  change (dualNumberScale a (p.toMul.val.val i j)).snd = a * (p.toMul.val.val i j).snd
  rw [dualNumberScale, TrivSqZeroExt.snd_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem four_factor_commutator {R : Type*} [Ring R] (X Y : R) :
    ((show TwoVariables R from ((1, X), 0)) * (show TwoVariables R from (1, (Y, 0))) *
      (show TwoVariables R from ((1, -X), 0)) * (show TwoVariables R from (1, (-Y, 0)))).snd.snd
      = X * Y - Y * X := by
  simp only [DualNumber.snd_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero, TrivSqZeroExt.fst_one,
    TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk]
  simp [sub_eq_add_neg, add_comm]

private theorem matrix_commutator (p q : matrixKernel (k := k) (ι := ι)) :
    (matrixTwo (commutator (generalLinearPoints k ι) p q).val).snd.snd =
      matrixCoefficient p * matrixCoefficient q - matrixCoefficient q * matrixCoefficient p := by
  let F := generalLinearPoints k ι
  let p' : DualKernel F := Additive.ofMul p.toMul⁻¹
  let q' : DualKernel F := Additive.ofMul q.toMul⁻¹
  have hp := matrixTwo_S p'
  have hq := matrixTwo_T q'
  change matrixTwo ((F.map atS).hom p.toMul.val⁻¹).val = _ at hp
  change matrixTwo ((F.map atT).hom q.toMul.val⁻¹).val = _ at hq
  rw [map_inv] at hp hq
  unfold InfinitesimalCommutator.commutator
  change (matrixTwo (((F.map atS).hom p.toMul.val).val *
    ((F.map atT).hom q.toMul.val).val *
    (((F.map atS).hom p.toMul.val)⁻¹).val *
    (((F.map atT).hom q.toMul.val)⁻¹).val)).snd.snd = _
  rw [map_mul, map_mul, map_mul, hp, hq, matrixTwo_S p, matrixTwo_T q]
  have hip : matrixCoefficient p' = -matrixCoefficient p := matrixCoefficient_inv p
  have hiq : matrixCoefficient q' = -matrixCoefficient q := matrixCoefficient_inv q
  rw [hip, hiq]
  exact four_factor_commutator (matrixCoefficient p) (matrixCoefficient q)

variable {G L : Specs.GroupScheme k}
variable (f : G ⟶ L)
variable (l : (groupPointsFunctor k).obj L ≅ generalLinearPoints k ι)

private abbrev matrixPointMap :
    (groupPointsFunctor k).obj G ⟶ generalLinearPoints k ι :=
  (groupPointsFunctor k).map f ≫ l.hom

private theorem matrixDifferential_eq (p : Lie k G) :
    matrixDifferential f l p = matrixCoefficient (mapDualKernel (matrixPointMap f l) p) := rfl

private theorem matrixDifferential_injective (hf : IsClosedImmersion f.hom.hom.left) :
    Function.Injective (matrixDifferential f l) := by
  intro p q h
  rw [matrixDifferential_eq, matrixDifferential_eq] at h
  have he := congrArg (fun x : matrixKernel (k := k) (ι := ι) => x.toMul.val)
    (matrixCoefficient_injective h)
  change (l.hom.app dualTest).hom
    (((groupPointsFunctor k).map f).app dualTest p.toMul.val) =
    (l.hom.app dualTest).hom (((groupPointsFunctor k).map f).app dualTest q.toMul.val) at he
  have he' := (l.app dualTest).groupIsoToMulEquiv.injective he
  let := hf
  apply Subtype.ext
  apply Over.OverMorphism.ext
  exact (cancel_mono f.hom.hom.left).mp
    (congrArg (fun x : Points L.X dualTest => x.left) he')

private theorem matrixDifferential_bracket {b : Lie k G → Lie k G → Lie k G}
    (hb : IsBracket ((groupPointsFunctor k).obj G) b) (p q : Lie k G) :
    matrixDifferential f l (b p q) =
      matrixDifferential f l p * matrixDifferential f l q -
        matrixDifferential f l q * matrixDifferential f l p := by
  let η := matrixPointMap f l
  have hm := (nat_apply η atST (b p q).toMul.val).symm.trans
    ((congrArg (η.app twoVariableTest).hom (hb p q)).trans (map_commutator η p q))
  have he := congrArg
    (fun z : Matrix.GeneralLinearGroup ι (TwoVariables k) => (matrixTwo z.val).snd.snd) hm
  change (matrixTwo (((generalLinearPoints k ι).map atST).hom
    (mapDualKernel η (b p q)).toMul.val).val).snd.snd = _ at he
  rw [matrixTwo_ST, matrix_commutator] at he
  exact he

theorem identityLieBracketMatrix : Specs.IdentityLieBracketMatrix.{u} := by
  intro k _ G L _ _ ι _ _ f l hf
  exact ⟨matrixDifferential_injective f l hf,
    fun b => matrixDifferential_bracket f l b.commutator_law⟩

private def matrixDifferentialLinear [IsAffine G.X.left] :
    Lie k G →ₗ[k] Matrix ι ι k where
  toFun := matrixDifferential f l
  map_add' p q := by
    simp only [matrixDifferential_eq, map_add, matrixCoefficient_add]
  map_smul' a p := by
    simp only [matrixDifferential_eq, RingHom.id_apply]
    change matrixCoefficient (mapDualKernel (matrixPointMap f l)
      (scaleDualKernel _ a p)) = a • _
    rw [mapDualKernel_scale, matrixCoefficient_scale]

end Matrices

private theorem lieBracket_laws (G : Specs.AffineAlgebraicGroup k)
    [IsAffine G.val.X.left] :
    let b := lieBracket G.val
    (∀ p q r, b (p + q) r = b p r + b q r) ∧
    (∀ p q r, b p (q + r) = b p q + b p r) ∧
    (∀ p, b p p = 0) ∧
    (∀ p q r, b p (b q r) = b (b p q) r + b q (b p r)) ∧
    (∀ (a : k) p q, b p (a • q) = a • b p q) := by
  let b := lieBracket G.val
  change (∀ p q r, b (p + q) r = b p r + b q r) ∧
    (∀ p q r, b p (q + r) = b p q + b p r) ∧
    (∀ p, b p p = 0) ∧
    (∀ p q r, b p (b q r) = b (b p q) r + b q (b p r)) ∧
    (∀ (a : k) p q, b p (a • q) = a • b p q)
  obtain ⟨n, L, ⟨l⟩, f, hf⟩ := faithfulLinearization k G
  let D := matrixDifferentialLinear f l
  have hD : Function.Injective D := matrixDifferential_injective f l hf
  let : LieRing (Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) k) :=
    LieRing.ofAssociativeRing
  let : LieAlgebra k (Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) k) :=
    LieAlgebra.ofAssociativeAlgebra
  have h (p q : Lie k G.val) : D (b p q) = ⁅D p, D q⁆ :=
    matrixDifferential_bracket f l (lieBracket_isBracket G.val) p q
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p q r
    apply hD
    simp only [h, map_add, add_lie]
  · intro p q r
    apply hD
    simp only [h, map_add, lie_add]
  · intro p
    apply hD
    simp only [h, map_zero, lie_self]
  · intro p q r
    apply hD
    simp only [h, map_add]
    exact leibniz_lie _ _ _
  · intro a p q
    apply hD
    simp only [h, map_smul, lie_smul]

@[instance_reducible]
private def identityLieRing (G : Specs.AffineAlgebraicGroup k)
    [IsAffine G.val.X.left] : LieRing (Lie k G.val) :=
  { lieAddCommGroup G.val with
    bracket := lieBracket G.val
    add_lie := (lieBracket_laws G).1
    lie_add := (lieBracket_laws G).2.1
    lie_self := (lieBracket_laws G).2.2.1
    leibniz_lie := (lieBracket_laws G).2.2.2.1 }

@[instance_reducible]
private def identityLieAlgebra (G : Specs.AffineAlgebraicGroup k)
    [IsAffine G.val.X.left] :
    @LieAlgebra k (Lie k G.val) _ (identityLieRing G) := by
  letI := identityLieRing G
  exact { toModule := lieModule G.val, lie_smul := (lieBracket_laws G).2.2.2.2 }

/-- The identity tangent Lie algebra of a finite-type affine group scheme. -/
def identityLieStructure (G : Specs.AffineAlgebraicGroup k) :
    Specs.IdentityLieStructure G.val :=
  letI : IsAffine G.val.X.left := G.property.1
  ⟨identityLieRing G, rfl, identityLieAlgebra G, rfl, lieBracket_isBracket G.val⟩

theorem identityLieBracket : Specs.IdentityLieBracket.{u} :=
  fun _ _ G => ⟨identityLieStructure G⟩

section FieldExtension

variable (K : Type u) [Field K] [Algebra k K]

private def extendTwoVariables : twoVariableTest (k := k) ⟶
    (restrictTestAlgebra k K).obj (twoVariableTest (k := K)) := by
  let S := (restrictTestAlgebra k K).obj (twoVariableTest (k := K))
  letI : Algebra k S := S.algebra
  let f : TwoVariables k →ₐ[k] S :=
    { toRingHom := mapCoefficients (dualNumberCoefficients K)
      commutes' := fun a => by
        apply TrivSqZeroExt.ext <;> apply TrivSqZeroExt.ext
        · rfl
        all_goals exact map_zero (algebraMap k K) }
  exact ConcreteCategory.ofHom (C := CommAlgCat k) (X := twoVariableTest) (Y := S) f

private theorem extend_atS :
    (atS : dualTest (k := k) ⟶ _) ≫ extendTwoVariables K =
      extendDualNumber K ≫ (restrictTestAlgebra k K).map atS := by
  apply CommAlgCat.hom_ext
  apply DFunLike.ext
  intro z
  apply TrivSqZeroExt.ext
  · rfl
  · apply TrivSqZeroExt.ext <;> exact map_zero (algebraMap k K)

private theorem extend_atT :
    (atT : dualTest (k := k) ⟶ _) ≫ extendTwoVariables K =
      extendDualNumber K ≫ (restrictTestAlgebra k K).map atT := by
  apply CommAlgCat.hom_ext
  apply DFunLike.ext
  intro z
  apply TrivSqZeroExt.ext <;> apply TrivSqZeroExt.ext
  · rfl
  · exact map_zero (algebraMap k K)
  · rfl
  · exact map_zero (algebraMap k K)

private theorem extend_atST :
    (atST : dualTest (k := k) ⟶ _) ≫ extendTwoVariables K =
      extendDualNumber K ≫ (restrictTestAlgebra k K).map atST := by
  apply CommAlgCat.hom_ext
  apply DFunLike.ext
  intro z
  apply TrivSqZeroExt.ext <;> apply TrivSqZeroExt.ext
  · rfl
  · exact map_zero (algebraMap k K)
  · exact map_zero (algebraMap k K)
  · rfl

private theorem bracket_baseChange_point
    (G : Specs.GroupScheme k)
    [IsAffine ((groupBaseChange k K).obj G).X.left]
    (b : Specs.IdentityLieStructure G)
    (c : Specs.IdentityLieStructure ((groupBaseChange k K).obj G))
    (j : Lie k G → Lie K ((groupBaseChange k K).obj G))
    (hj : ∀ p : Lie k G,
      baseChangePoint k K G.X dualTest (j p).toMul.val =
        mapPoints (extendDualNumber K) p.toMul.val)
    (p q : Lie k G) :
    j (b.lieRing.toBracket.bracket p q) = c.lieRing.toBracket.bracket (j p) (j q) := by
  let H := (groupBaseChange k K).obj G
  let F := (groupPointsFunctor k).obj G
  let F' := (groupPointsFunctor K).obj H
  let ρ := restrictTestAlgebra k K
  let η := (baseChangePointIso K G).hom
  have hmove (a : dualTest (k := k) ⟶ twoVariableTest)
      (a' : dualTest (k := K) ⟶ twoVariableTest)
      (ha : a ≫ extendTwoVariables K = extendDualNumber K ≫ ρ.map a')
      (p : Lie k G) :
      (η.app twoVariableTest).hom ((F'.map a').hom (j p).toMul.val) =
        (F.map (extendTwoVariables K)).hom ((F.map a).hom p.toMul.val) := by
    have hp : (η.app dualTest).hom (j p).toMul.val =
        (F.map (extendDualNumber K)).hom p.toMul.val := hj p
    rw [nat_apply η a', hp]
    exact (comp_map_apply F (extendDualNumber K) (ρ.map a') p.toMul.val).symm.trans
      ((congrArg (fun g => (F.map g).hom p.toMul.val) ha.symm).trans (comp_map_apply F _ _ _))
  have hcomm :
      (η.app twoVariableTest).hom (commutator F' (j p) (j q)) =
        (F.map (extendTwoVariables K)).hom (commutator F p q) := by
    simp only [InfinitesimalCommutator.commutator, map_mul, map_inv,
      hmove atS atS (extend_atS K), hmove atT atT (extend_atT K)]
  apply Subtype.ext
  apply point_liftST_injective H
  apply ((baseChangePointIso K G).app twoVariableTest).groupIsoToMulEquiv.injective
  change (η.app twoVariableTest).hom ((F'.map atST).hom
    (j (b.lieRing.toBracket.bracket p q)).toMul.val) =
      (η.app twoVariableTest).hom ((F'.map atST).hom
        (c.lieRing.toBracket.bracket (j p) (j q)).toMul.val)
  exact (hmove atST atST (extend_atST K) _).trans
    ((congrArg (F.map (extendTwoVariables K)).hom (b.commutator_law p q)).trans
      (hcomm.symm.trans (congrArg (η.app twoVariableTest).hom (c.commutator_law _ _).symm)))

end FieldExtension

private def Specs.IdentityLieStructure.toVectorStructure {G : Specs.GroupScheme k}
    (b : Specs.IdentityLieStructure G) : Specs.LieVectorStructure G :=
  ⟨b.lieRing.toAddCommGroup, b.group_law, b.lieAlgebra.toModule, b.scalar_law⟩

private theorem vectorStructure_unique {G : Specs.GroupScheme k}
    (m n : Specs.LieVectorStructure G) : m = n := by
  cases m with
  | mk A hA M hM =>
    cases n with
    | mk B hB N hN =>
      have h : A = B := AddCommGroup.ext (g₁ := A) (g₂ := B)
        (congrArg (fun g : AddGroup (PointKernel G) => g.toAdd.add) (hA.trans hB.symm))
      subst B
      have h : M = N := Module.ext' M N fun t p =>
        congrFun (congrFun (hM.trans hN.symm) t) p
      subst N
      rfl

private theorem lieEquiv_of_tensor_generators
    {k K V W : Type u} [Field k] [Field K] [Algebra k K]
    [LieRing V] [LieAlgebra k V] [LieRing W] [LieAlgebra K W]
    (e : (K ⊗[k] V) ≃ₗ[K] W)
    (hgen : ∀ (p q : V), e (1 ⊗ₜ[k] ⁅p, q⁆) = ⁅e (1 ⊗ₜ[k] p), e (1 ⊗ₜ[k] q)⁆) :
    ∃ d : (K ⊗[k] V) ≃ₗ⁅K⁆ W, ∀ x, d x = e x := by
  have hsmul (s : K) (p : V) : e (s ⊗ₜ[k] p) = s • e (1 ⊗ₜ[k] p) := by
    rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul]
  have htmul (s t : K) (p q : V) :
      e ⁅s ⊗ₜ[k] p, t ⊗ₜ[k] q⁆ = ⁅e (s ⊗ₜ[k] p), e (t ⊗ₜ[k] q)⁆ := by
    rw [LieAlgebra.ExtendScalars.bracket_tmul, hsmul (s * t), hsmul s, hsmul t, hgen,
      smul_lie, lie_smul, mul_smul]
  have hl (x y : K ⊗[k] V) : e ⁅x, y⁆ = ⁅e x, e y⁆ := by
    induction x using TensorProduct.inductionOn with
    | tmul s p =>
      induction y using TensorProduct.inductionOn with
      | tmul t q => exact htmul s t p q
      | add y z hy hz => simp only [lie_add, map_add, hy, hz]
    | add x z hx hz => simp only [add_lie, map_add, hx, hz]
  let d : (K ⊗[k] V) →ₗ⁅K⁆ W :=
    { e.toLinearMap with map_lie' := fun {x y} => hl x y }
  exact ⟨⟨d, e.symm, e.left_inv, e.right_inv⟩, fun _ => rfl⟩

theorem identityLieBracketBaseChange : Specs.IdentityLieBracketBaseChange.{u} := by
  intro k K _ _ _ G H
  constructor
  · let : IsAffine G.val.X.left := G.property.1
    let : LocallyOfFiniteType G.val.X.hom := G.property.2.1
    let : QuasiCompact G.val.X.hom := G.property.2.2
    have hH : IsAffine H.X.left ∧ LocallyOfFiniteType H.X.hom ∧ QuasiCompact H.X.hom := by
      refine ⟨isAffine_baseChange K G.val, ?_, ?_⟩
      · change LocallyOfFiniteType (Limits.pullback.snd G.val.X.hom (fieldSpecMap k K))
        infer_instance
      · change QuasiCompact (Limits.pullback.snd G.val.X.hom (fieldSpecMap k K))
        infer_instance
    exact ⟨identityLieStructure ⟨H, hH⟩⟩
  intro b c
  obtain ⟨m, n, h⟩ := lieBaseChange k K G
  have hm := vectorStructure_unique m b.toVectorStructure
  have hn := vectorStructure_unique n c.toVectorStructure
  subst m
  subst n
  obtain ⟨e, he⟩ := h
  have hs := @lieEquiv_of_tensor_generators k K (Specs.Lie k G.val) (Specs.Lie K H)
    _ _ _ b.lieRing b.lieAlgebra c.lieRing c.lieAlgebra e
  let : IsAffine G.val.X.left := G.property.1
  let : IsAffine H.X.left := isAffine_baseChange K G.val
  have hgen := bracket_baseChange_point K G.val b c
    (fun p => e (@TensorProduct.tmul k _ K (Specs.Lie k G.val) _ b.lieRing.toAddCommGroup.toAddCommMonoid _
      b.lieAlgebra.toModule 1 p)) he
  obtain ⟨d, hd⟩ := hs hgen
  refine ⟨d, fun p => ?_⟩
  exact (congrArg (fun x : Specs.Lie K H => baseChangePoint k K G.val.X dualTest
    x.toMul.val) (hd _)).trans (he p)

end
end LinearAlgebraicGroups
