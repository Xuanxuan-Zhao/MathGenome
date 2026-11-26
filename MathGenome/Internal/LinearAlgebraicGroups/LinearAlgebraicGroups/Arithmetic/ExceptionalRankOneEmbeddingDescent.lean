import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalRankOneEmbeddingDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRankOneExtension
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankOneRelations
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct CategoryTheory.MonObj Matrix

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalRankOneEmbeddingDescent

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalRankOneEmbeddingDescent (MatrixComparison DescendMatrixEmbedding)
open Specs.IntegralFibreReductivity (rankOnePoints)
open Specs.IntegralRootRelations (diagonal upper lower)
open Specs.RootGroups (AdditiveLine rootPoint)

open private exists_rankOne_pivots_after_injective_extension rankOne_pivot_factorization
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRankOneExtension
open private mapPoints_injective changeRing mapPoints_rootPoint
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankOneRelations
open private hom_ext_on_affine_tests from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private abbrev extendTest (R : TestAlgebra F) : TestAlgebra K :=
  CommAlgCat.of K (K ⊗[F] R)

private def tensorInclusion (R : TestAlgebra F) :
    R ⟶ (restrictTestAlgebra F K).obj (extendTest (K := K) R) := by
  let g : R →+* K ⊗[F] R := (Algebra.TensorProduct.includeRight :
    R →ₐ[F] K ⊗[F] R).toRingHom
  letI : Algebra F (K ⊗[F] R) :=
    ((algebraMap K (K ⊗[F] R)).comp (algebraMap F K)).toAlgebra
  have hg (a : F) : g (algebraMap F R a) = algebraMap F (K ⊗[F] R) a := by
    change (1 : K) ⊗ₜ[F] (algebraMap F R a) = (algebraMap F K a) ⊗ₜ[F] (1 : R)
    exact (Algebra.TensorProduct.algebraMap_apply' (A := K) (B := R) a).symm.trans
      (Algebra.TensorProduct.algebraMap_apply (R := F) (A := K) (B := R) a)
  exact CommAlgCat.ofHom (show R →ₐ[F] K ⊗[F] R from { toRingHom := g, commutes' := hg })


private def tensorMap {R S : TestAlgebra F} (a : R ⟶ S) :
    extendTest (K := K) R ⟶ extendTest (K := K) S :=
  CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id K K) a.hom)

private theorem tensorInclusion_natural {R S : TestAlgebra F} (a : R ⟶ S) :
    tensorInclusion (K := K) R ≫ (restrictTestAlgebra F K).map (tensorMap a) =
      a ≫ tensorInclusion (K := K) S := by
  apply ConcreteCategory.hom_ext
  intro r
  change Algebra.TensorProduct.map (AlgHom.id K K) a.hom (1 ⊗ₜ[F] r) =
    (1 : K) ⊗ₜ[F] a.hom r
  simp

/-- Extend a map to the restriction of a K-algebra by the tensor universal property. -/
private def tensorLift {R : TestAlgebra F} {S : TestAlgebra K}
    (a : R ⟶ (restrictTestAlgebra F K).obj S) : extendTest (K := K) R ⟶ S := by
  letI : Algebra F S := ((algebraMap K S).comp (algebraMap F K)).toAlgebra
  letI : IsScalarTower F K S := IsScalarTower.of_algebraMap_eq' rfl
  exact CommAlgCat.ofHom (AlgHom.liftEquiv F K R S a.hom)

private theorem tensorLift_comp {R : TestAlgebra F} {S : TestAlgebra K}
    (a : R ⟶ (restrictTestAlgebra F K).obj S) :
    tensorInclusion (K := K) R ≫ (restrictTestAlgebra F K).map (tensorLift a) = a := by
  apply ConcreteCategory.hom_ext
  intro r
  change (tensorLift a).hom ((1 : K) ⊗ₜ[F] r) = a.hom r
  simp [tensorLift]

private def scalarRetraction : K →ₗ[F] F :=
  ((Algebra.linearMap F K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective F K))).choose

private theorem scalarRetraction_one : scalarRetraction (F := F) (K := K) 1 = 1 := by
  have h := ((Algebra.linearMap F K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective F K))).choose_spec
  simpa [scalarRetraction] using LinearMap.congr_fun h (1 : F)

private def tensorRetraction (R : TestAlgebra F) : K ⊗[F] R →ₗ[F] R :=
  (TensorProduct.lid F R).toLinearMap ∘ₗ
    TensorProduct.map (scalarRetraction (F := F) (K := K)) (LinearMap.id (R := F))

private theorem tensorRetraction_inclusion (R : TestAlgebra F) (r : R) :
    tensorRetraction (K := K) R ((tensorInclusion (K := K) R).hom r) = r := by
  change tensorRetraction (K := K) R ((1 : K) ⊗ₜ[F] r) = r
  simp [tensorRetraction, scalarRetraction_one]

private theorem tensorRetraction_natural {R S : TestAlgebra F} (a : R ⟶ S)
    (z : K ⊗[F] R) :
    tensorRetraction (K := K) S ((tensorMap (K := K) a).hom z) =
      a.hom (tensorRetraction (K := K) R z) := by
  induction z using TensorProduct.inductionOn with
  | tmul c r =>
    change tensorRetraction (K := K) S (c ⊗ₜ[F] a.hom r) =
      a.hom (tensorRetraction (K := K) R (c ⊗ₜ[F] r))
    simp [tensorRetraction, Algebra.smul_def]
  | add z w hz hw => simp only [map_add, hz, hw]

private theorem tensorInclusion_injective (R : TestAlgebra F) :
    Function.Injective (tensorInclusion (K := K) R).hom :=
  Function.LeftInverse.injective (g := tensorRetraction (K := K) R)
    (f := (tensorInclusion (K := K) R).hom) (tensorRetraction_inclusion R)

private theorem tensorMap_injective {R S : TestAlgebra F} (a : R ⟶ S)
    (ha : Function.Injective a.hom) : Function.Injective (tensorMap (K := K) a).hom := by
  have he : ∀ z, (tensorMap (K := K) a).hom z = a.hom.toLinearMap.lTensor K z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul c r => rfl
    | add z w hz hw => simp only [map_add, hz, hw]
  intro z w h
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := K) a.hom.toLinearMap ha
  rwa [← he z, ← he w]

/-- If a coordinate belongs to the ground ring after an injective extension
of that ring, it belonged to the ground ring before the extension. -/
private theorem tensorInclusion_range {R S : TestAlgebra F} (a : R ⟶ S)
    (ha : Function.Injective a.hom) {z : K ⊗[F] R} {s : S}
    (h : (tensorMap (K := K) a).hom z = (tensorInclusion (K := K) S).hom s) :
    ∃ r : R, (tensorInclusion (K := K) R).hom r = z := by
  refine ⟨tensorRetraction (K := K) R z, ?_⟩
  have hs : a.hom (tensorRetraction (K := K) R z) = s := by
    rw [← tensorRetraction_natural, h, tensorRetraction_inclusion]
  apply tensorMap_injective a ha
  rw [h, ← hs]
  exact ConcreteCategory.congr_hom (tensorInclusion_natural (K := K) a) _

private theorem factor_algebra_map {A R T : TestAlgebra F} (b : R ⟶ T) (q : A ⟶ T)
    (hb : Function.Injective b.hom) (hq : ∀ c : A, ∃ r : R, b.hom r = q.hom c) :
    ∃ v : A ⟶ R, v ≫ b = q := by
  let d := AlgEquiv.ofInjective b.hom hb
  let v := CommAlgCat.ofHom (d.symm.toAlgHom.comp (q.hom.codRestrict b.hom.range hq))
  refine ⟨v, ?_⟩
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro c
  change b.hom (d.symm ⟨q.hom c, _⟩) = q.hom c
  exact congrArg Subtype.val (d.apply_symm_apply _)

/-- Pull back an affine point by applying the coordinate descent criterion. -/
private theorem point_of_tensor_square {X : SchemeOver F} (hX : IsAffine X.left)
    {R S : TestAlgebra F} (a : R ⟶ S) (ha : Function.Injective a.hom)
    (q : Points X ((restrictTestAlgebra F K).obj (extendTest R))) (p : Points X S)
    (h : mapPoints ((restrictTestAlgebra F K).map (tensorMap a)) q =
      mapPoints (tensorInclusion (K := K) S) p) :
    ∃ v : Points X R, mapPoints (tensorInclusion (K := K) R) v = q := by
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of F)).mpr hX
  let H := algSpec.fullyFaithful (R := CommRingCat.of F)
  let q' := (H.preimage (q ≫ e.inv)).unop
  let p' := (H.preimage (p ≫ e.inv)).unop
  have ht : q' ≫ (restrictTestAlgebra F K).map (tensorMap a) =
      p' ≫ tensorInclusion (K := K) S := by
    apply Quiver.Hom.op_inj
    apply H.map_injective
    change (testSpec F).map (_ ≫ q'.op) = (testSpec F).map (_ ≫ p'.op)
    rw [Functor.map_comp, Functor.map_comp]
    change mapPoints _ ((testSpec F).map (H.preimage (q ≫ e.inv))) =
      mapPoints _ ((testSpec F).map (H.preimage (p ≫ e.inv)))
    rw [H.map_preimage, H.map_preimage]
    change (testSpec F).map ((restrictTestAlgebra F K).map (tensorMap a)).op ≫ q ≫ e.inv =
      (testSpec F).map (tensorInclusion (K := K) S).op ≫ p ≫ e.inv
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ e.inv) h
  obtain ⟨v, hv⟩ := factor_algebra_map (tensorInclusion (K := K) R) q'
    (tensorInclusion_injective R)
    (fun c => tensorInclusion_range a ha (ConcreteCategory.congr_hom ht c))
  refine ⟨(testSpec F).map v.op ≫ e.hom, ?_⟩
  rw [mapPoints, ← Category.assoc, ← Functor.map_comp, ← op_comp, hv]
  change (testSpec F).map (H.preimage (q ≫ e.inv)) ≫ e.hom = q
  rw [H.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private abbrev SL (R : Type u) [CommRing R] := Matrix.SpecialLinearGroup (Fin 2) R

private abbrev matrixMap {k : Type u} [Field k] {R S : TestAlgebra k} (f : R ⟶ S) :
    SL R →* SL S :=
  Matrix.SpecialLinearGroup.map f.hom.toRingHom

private theorem matrixMap_upper {k : Type u} [Field k] {R S : TestAlgebra k} (f : R ⟶ S)
    (t : R) : matrixMap f (upper t) = upper (f.hom t) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, Matrix.SpecialLinearGroup.map, RingHom.mapMatrix_apply]

private theorem matrixMap_lower {k : Type u} [Field k] {R S : TestAlgebra k} (f : R ⟶ S)
    (t : R) : matrixMap f (lower t) = lower (f.hom t) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lower, Matrix.SpecialLinearGroup.map, RingHom.mapMatrix_apply]

private abbrev elementaryWord {R : Type u} [CommRing R] (b : Rˣ) : SL R :=
  upper (b : R) * lower (-(↑b⁻¹ : R)) * upper (b : R)

private theorem diagonal_eq_word {R : Type u} [CommRing R] (b : Rˣ) :
    diagonal b = elementaryWord b * (elementaryWord (1 : Rˣ))⁻¹ := by
  apply eq_mul_inv_of_mul_eq
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [elementaryWord, upper, lower, diagonal, Matrix.mul_apply, Fin.sum_univ_two]

section Descent

variable {G : AffineAlgebraicGroup F} (J : MatrixComparison F K)
    (i : J.extended.val ⟶ (groupBaseChange F K).obj G.val)
    {A B : AdditiveLine F} (x : A.group ⟶ G.val) (y : B.group ⟶ G.val)

private def embeddedHom (R : TestAlgebra K) :
    SL R →* GroupPoints G.val ((restrictTestAlgebra F K).obj R) :=
  (baseChangePointGroupEquiv K G.val R).toMonoidHom.comp
    ((((groupPointsFunctor K).map i).app R).hom.comp (J.extendedMatrices.inv.app R).hom)

private theorem embeddedHom_apply (R : TestAlgebra K) (m : SL R) :
    embeddedHom J i R m = J.embeddedPoint i R m := rfl

private theorem embeddedHom_natural {R S : TestAlgebra K} (a : R ⟶ S) (m : SL R) :
    changeRing ((restrictTestAlgebra F K).map a) (embeddedHom J i R m) =
      embeddedHom J i S (matrixMap a m) := by
  have hm := ConcreteCategory.congr_hom (J.extendedMatrices.inv.naturality a) m
  change J.extendedMatrices.inv.app S (matrixMap a m) =
    mapPoints a (J.extendedMatrices.inv.app R m) at hm
  change mapPoints ((restrictTestAlgebra F K).map a)
    (baseChangePoint F K G.val.X R (J.extendedMatrices.inv.app R m ≫ i.hom.hom)) =
    baseChangePoint F K G.val.X S (J.extendedMatrices.inv.app S (matrixMap a m) ≫ i.hom.hom)
  rw [← baseChangePointsNaturality F K, hm]
  unfold mapPoints
  rw [Category.assoc]

private def tensorValue (R : TestAlgebra F) :
    SL R →* GroupPoints G.val ((restrictTestAlgebra F K).obj (extendTest R)) :=
  (embeddedHom J i (extendTest R)).comp (matrixMap (tensorInclusion R))

private theorem tensorValue_natural {R S : TestAlgebra F} (a : R ⟶ S) (m : SL R) :
    changeRing ((restrictTestAlgebra F K).map (tensorMap a)) (tensorValue J i R m) =
      tensorValue J i S (matrixMap a m) := by
  change changeRing ((restrictTestAlgebra F K).map (tensorMap a))
    (embeddedHom J i _ (matrixMap (tensorInclusion (K := K) R) m)) = _
  rw [embeddedHom_natural]
  apply congrArg (embeddedHom J i (extendTest S))
  apply Subtype.ext
  ext r s
  exact ConcreteCategory.congr_hom (tensorInclusion_natural (K := K) a) (m.val r s)

private def rootWord (R : TestAlgebra F) (b : Rˣ) : GroupPoints G.val R :=
  rootPoint x R (b : R) * rootPoint y R (-(↑b⁻¹ : R)) * rootPoint x R (b : R)

variable (hx : ∀ (R : TestAlgebra K) (t : R),
    J.embeddedPoint i R (upper t) = rootPoint x ((restrictTestAlgebra F K).obj R) t)
  (hy : ∀ (R : TestAlgebra K) (t : R),
    J.embeddedPoint i R (lower t) = rootPoint y ((restrictTestAlgebra F K).obj R) t)

include hx in
private theorem embedded_upper {S : TestAlgebra F} {R : TestAlgebra K}
    (a : S ⟶ (restrictTestAlgebra F K).obj R) (t : S) :
    embeddedHom J i R (matrixMap a (upper t)) = changeRing a (rootPoint x S t) := by
  rw [matrixMap_upper, embeddedHom_apply, hx, show
    changeRing a (rootPoint x S t) = rootPoint x _ (a.hom t) from mapPoints_rootPoint x a t]

include hy in
private theorem embedded_lower {S : TestAlgebra F} {R : TestAlgebra K}
    (a : S ⟶ (restrictTestAlgebra F K).obj R) (t : S) :
    embeddedHom J i R (matrixMap a (lower t)) = changeRing a (rootPoint y S t) := by
  rw [matrixMap_lower, embeddedHom_apply, hy, show
    changeRing a (rootPoint y S t) = rootPoint y _ (a.hom t) from mapPoints_rootPoint y a t]

include hx hy in
private theorem embedded_diagonal {S : TestAlgebra F} {R : TestAlgebra K}
    (a : S ⟶ (restrictTestAlgebra F K).obj R) (b : Sˣ) :
    embeddedHom J i R (matrixMap a (diagonal b)) =
      changeRing a (rootWord x y S b * (rootWord x y S 1)⁻¹) := by
  rw [diagonal_eq_word]
  simp only [elementaryWord, rootWord, map_mul, map_inv,
    embedded_upper J i x hx a, embedded_lower J i y hy a]

include hx hy in
private theorem tensorValue_descends (R : TestAlgebra F) (m : SL R) :
    ∃ p : GroupPoints G.val R, changeRing (tensorInclusion R) p = tensorValue J i R m := by
  obtain ⟨S, hS, f, t, hf, hPivot⟩ := exists_rankOne_pivots_after_injective_extension [m]
  letI := hS
  letI : Algebra F S := (f.comp (algebraMap F R)).toAlgebra
  let T := CommAlgCat.of F S
  let a : R ⟶ T := CommAlgCat.ofHom ({ toRingHom := f, commutes' := fun _ => rfl } : R →ₐ[F] S)
  let n := upper t * matrixMap a m
  obtain ⟨b, hb⟩ := hPivot m (List.mem_singleton.mpr rfl)
  have hn := rankOne_pivot_factorization n b hb
  have hm : matrixMap a m = (upper t)⁻¹ *
      (lower (n.val 1 0 * ↑b⁻¹) * diagonal b * upper (n.val 0 1 * ↑b⁻¹)) := by
    rw [← hn]
    exact (inv_mul_cancel_left _ _).symm
  apply point_of_tensor_square G.property.1 a hf
    (tensorValue J i R m)
    ((rootPoint x T t)⁻¹ * (rootPoint y T (n.val 1 0 * ↑b⁻¹) *
      (rootWord x y T b * (rootWord x y T 1)⁻¹) * rootPoint x T (n.val 0 1 * ↑b⁻¹)))
  change changeRing _ (tensorValue J i R m) = changeRing _ _
  rw [tensorValue_natural, hm]
  change embeddedHom J i (extendTest T) (matrixMap (tensorInclusion T) _) = _
  simp only [map_mul, map_inv]
  simp only [embedded_upper J i x hx, embedded_lower J i y hy,
    embedded_diagonal J i x y hx hy, map_mul, map_inv]

include hx hy in
private def descendedPoint (R : TestAlgebra F) (m : SL R) : GroupPoints G.val R :=
  (tensorValue_descends J i x y hx hy R m).choose

include hx hy in
private theorem descendedPoint_tensor (R : TestAlgebra F) (m : SL R) :
    changeRing (tensorInclusion R) (descendedPoint J i x y hx hy R m) = tensorValue J i R m :=
  (tensorValue_descends J i x y hx hy R m).choose_spec

private theorem tensorPoints_injective (R : TestAlgebra F) :
    Function.Injective (changeRing (G := G.val) (tensorInclusion (K := K) R)) :=
  mapPoints_injective G.property.1 _ (tensorInclusion_injective R)

include hx hy in
private def descendedHom (R : TestAlgebra F) : SL R →* GroupPoints G.val R where
  toFun := descendedPoint J i x y hx hy R
  map_one' := by
    apply tensorPoints_injective (K := K) R
    rw [descendedPoint_tensor, map_one, map_one]
  map_mul' m n := by
    apply tensorPoints_injective (K := K) R
    rw [descendedPoint_tensor, map_mul, map_mul, descendedPoint_tensor, descendedPoint_tensor]

include hx hy in
private theorem descendedPoint_natural {R S : TestAlgebra F} (a : R ⟶ S) (m : SL R) :
    changeRing a (descendedPoint J i x y hx hy R m) =
      descendedPoint J i x y hx hy S (matrixMap a m) := by
  apply tensorPoints_injective (K := K) S
  rw [descendedPoint_tensor, ← tensorValue_natural]
  rw [← descendedPoint_tensor J i x y hx hy R m]
  change mapPoints _ (mapPoints a _) = mapPoints _ (mapPoints _ _)
  simp only [mapPoints, ← Category.assoc, ← Functor.map_comp, ← op_comp]
  exact congrArg (fun f : R ⟶ (restrictTestAlgebra F K).obj (extendTest S) =>
    (testSpec F).map f.op ≫ descendedPoint J i x y hx hy R m)
    (tensorInclusion_natural (K := K) a).symm

include hx hy in
private def descendedTransformation :
    rankOnePoints F ⟶ (groupPointsFunctor F).obj G.val where
  app R := GrpCat.ofHom (descendedHom J i x y hx hy R)
  naturality R S a := by
    apply GrpCat.ext
    intro m
    exact (descendedPoint_natural J i x y hx hy a m).symm

include hx hy in
private theorem descendedPoint_restrict (S : TestAlgebra K) (m : SL S) :
    descendedPoint J i x y hx hy ((restrictTestAlgebra F K).obj S) m = embeddedHom J i S m := by
  let R := (restrictTestAlgebra F K).obj S
  let b : extendTest (K := K) R ⟶ S := tensorLift (𝟙 R)
  let c := (restrictTestAlgebra F K).map b
  have h := congrArg (changeRing (G := G.val) c) (descendedPoint_tensor J i x y hx hy R m)
  have hb : tensorInclusion (K := K) R ≫ c = 𝟙 R := tensorLift_comp (𝟙 R)
  have hleft : changeRing c (changeRing (tensorInclusion R) (descendedPoint J i x y hx hy R m)) =
      descendedPoint J i x y hx hy R m := by
    change mapPoints c (mapPoints (tensorInclusion R) _) = _
    simp only [mapPoints, ← Category.assoc, ← Functor.map_comp, ← op_comp, hb,
      op_id]
    rw [(testSpec F).map_id, Category.id_comp]
  rw [hleft] at h
  rw [h]
  change changeRing c (embeddedHom J i _ (matrixMap (tensorInclusion R) m)) = _
  rw [embeddedHom_natural J i b]
  apply congrArg (embeddedHom J i S)
  apply Subtype.ext
  ext r s
  exact ConcreteCategory.congr_hom hb (m.val r s)

include hx in
private theorem descendedPoint_upper (R : TestAlgebra F) (t : R) :
    descendedPoint J i x y hx hy R (upper t) = rootPoint x R t := by
  apply tensorPoints_injective (K := K) R
  rw [descendedPoint_tensor J i x y hx hy]
  exact embedded_upper J i x hx (tensorInclusion R) t

include hy in
private theorem descendedPoint_lower (R : TestAlgebra F) (t : R) :
    descendedPoint J i x y hx hy R (lower t) = rootPoint y R t := by
  apply tensorPoints_injective (K := K) R
  rw [descendedPoint_tensor J i x y hx hy]
  exact embedded_lower J i y hy (tensorInclusion R) t

private theorem embeddedHom_injective (hi : IsClosedImmersion i.hom.hom.left)
    (R : TestAlgebra K) : Function.Injective (embeddedHom J i R) := by
  intro m n h
  have hpoints := (baseChangePointsEquiv K G.val.X R).injective h
  letI := hi
  have hleft := congrArg Over.Hom.left hpoints
  have he : J.extendedMatrices.inv.app R m = J.extendedMatrices.inv.app R n :=
    Over.OverMorphism.ext ((cancel_mono i.hom.hom.left).mp hleft)
  exact (ConcreteCategory.bijective_of_isIso (J.extendedMatrices.inv.app R)).1 he

include hx hy in
private theorem descendedPoint_injective (hi : IsClosedImmersion i.hom.hom.left)
    (R : TestAlgebra F) : Function.Injective (descendedPoint J i x y hx hy R) := by
  intro m n h
  have he := congrArg (changeRing (G := G.val) (tensorInclusion (K := K) R)) h
  rw [descendedPoint_tensor J i x y hx hy, descendedPoint_tensor J i x y hx hy] at he
  have hm := embeddedHom_injective J i hi (extendTest R) he
  apply Subtype.ext
  ext r s
  exact tensorInclusion_injective R (congrArg (fun p : SL (extendTest (K := K) R) => p.val r s) hm)

include hx hy in
/-- The rational elementary root maps determine the full rank-one embedding over the ground field. -/
private theorem descend_embedding (hi : IsClosedImmersion i.hom.hom.left) :
    ∃ j : J.ground.val ⟶ G.val, IsClosedImmersion j.hom.hom.left ∧
      J.scalarIso.hom ≫ (groupBaseChange F K).map j = i ∧
      (∀ (R : TestAlgebra F) (t : R),
        J.groundMatrices.inv.app R (upper t) ≫ j.hom.hom = rootPoint x R t) ∧
      (∀ (R : TestAlgebra F) (t : R),
        J.groundMatrices.inv.app R (lower t) ≫ j.hom.hom = rootPoint y R t) := by
  let τ := J.groundMatrices.hom ≫ descendedTransformation J i x y hx hy
  obtain ⟨j, hj⟩ := (groupHomComparison F _ _ J.ground.property.1).surjective τ
  have hpoint (R : TestAlgebra F) (p : GroupPoints J.ground.val R) :
      p ≫ j.hom.hom = descendedPoint J i x y hx hy R (J.groundMatrices.hom.app R p) :=
    ConcreteCategory.congr_hom (congrArg (fun f => f.app R) hj) p
  have hmat (R : TestAlgebra F) (m : SL R) :
      J.groundMatrices.inv.app R m ≫ j.hom.hom = descendedPoint J i x y hx hy R m := by
    rw [hpoint]
    exact congrArg (descendedPoint J i x y hx hy R)
      (ConcreteCategory.congr_hom (J.groundMatrices.inv_hom_id_app R) m)
  refine ⟨j, ?_, ?_, ?_, ?_⟩
  · apply RootData.RootGroups.isClosedImmersion_of_injectivePoints J.ground G
    intro R p q h
    change p ≫ j.hom.hom = q ≫ j.hom.hom at h
    rw [hpoint, hpoint] at h
    exact (ConcreteCategory.bijective_of_isIso (J.groundMatrices.hom.app R)).1
      (descendedPoint_injective J i x y hx hy hi R h)
  · apply Grp.hom_ext
    apply hom_ext_on_affine_tests
    intro S p
    obtain ⟨m, rfl⟩ := (ConcreteCategory.bijective_of_isIso (J.extendedMatrices.inv.app S)).2 p
    apply (baseChangePointsEquiv K G.val.X S).injective
    change baseChangePoint F K G.val.X S
      (J.extendedMatrices.inv.app S m ≫
        (J.scalarIso.hom.hom.hom ≫ (baseChange F K).map j.hom.hom)) = J.embeddedPoint i S m
    rw [← Category.assoc, baseChangePointsSchemeNaturality F K, hpoint, J.scalarMatrices,
      descendedPoint_restrict J i x y hx hy, embeddedHom_apply]
  · intro R t
    rw [hmat, descendedPoint_upper J i x y hx hy]
  · intro R t
    rw [hmat, descendedPoint_lower J i x y hx hy]

end Descent

theorem descendMatrixEmbedding : DescendMatrixEmbedding.{u} := by
  intro F _ G J i hi A B x y hx hy
  exact descend_embedding J i x y hx hy hi

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalRankOneEmbeddingDescent
