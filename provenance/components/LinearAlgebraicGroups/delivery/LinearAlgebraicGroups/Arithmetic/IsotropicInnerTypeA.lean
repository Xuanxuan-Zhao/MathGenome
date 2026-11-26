import Specs.LinearAlgebraicGroups.Arithmetic.IsotropicInnerTypeA
import LinearAlgebraicGroups.Arithmetic.InnerTypeALocalGeneration
import LinearAlgebraicGroups.Arithmetic.ApproximationOfLocalWords
import LinearAlgebraicGroups.Descent.InnerTypeA
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Topology.Algebra.MvPolynomial
import Batteries.Tactic.OpenPrivate

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Topology
open scoped TensorProduct WithZero

set_option linter.style.haveILetI false
set_option maxHeartbeats 900000

universe u v

namespace LinearAlgebraicGroups.Arithmetic.IsotropicInnerTypeA


set_option allowUnsafeReducibility true in
attribute [local reducible] _root_.Specs.RM03.CSA.isCentralSimple RM03.CSA.IsCentralSimple

open Spec AdelicGroups ApproximationOfLocalWords InnerTypeALocalGeneration.Spec
open LocalNormOneCommutators.Spec
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.IntegralModels (MatrixRealization)
open LinearAlgebraicGroups.Specs.StandardGroups (spectrum)
open LinearAlgebraicGroups.Descent.InnerTypeA.Specification (NormOneCoordinates normOneIdeal)
open RM03.CSA (IsCentralSimple reducedNorm isCentralSimple_baseChange)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)
open private coordinateMap coordinateMap_spec from LinearAlgebraicGroups.Arithmetic.IntegralModels

private theorem normAt_eq_reducedNorm {K A F : Type*} [Field K] [Ring A] [Algebra K A]
    [Field F] [Algebra K F] {ι : Type*} [Fintype ι] (hA : IsCentralSimple K A)
    (b : Module.Basis ι K A) (x : F ⊗[K] A) :
    normAt hA b x = reducedNorm (isCentralSimple_baseChange hA) x := by
  change RM03.CSA.NormOneGroup.normAt hA b x = _
  unfold RM03.CSA.NormOneGroup.normAt
  exact (RM03.CSA.genericReducedNorm_eval₂ hA b (fun i => (b.baseChange F).repr x i)).trans
    (congrArg (reducedNorm (isCentralSimple_baseChange hA)) (by simpa only [Module.Basis.baseChange_apply] using (b.baseChange F).sum_repr x))

private theorem existsPresentation {K A ι : Type u} [Field K] [Ring A] [Algebra K A]
    [Fintype ι] (hA : IsCentralSimple K A) (b : Module.Basis ι K A) :
    Nonempty (NormOnePresentation hA b) := by
  obtain ⟨H, F, p, h1, hmul, hnat, e, he, c, hc⟩ :=
    Descent.InnerTypeA.normOneRepresentability hA b
  letI := H.hopf
  let point (R : TestAlgebra K) :=
    (((c.app R).groupIsoToMulEquiv).toEquiv.trans (p R))
  refine ⟨⟨H, point, ?_, ?_, ?_, ?_⟩⟩
  · intro R
    change (p R (c.hom.app R 1)).1 = 1
    rw [map_one, h1]
  · intro R x y
    change (p R (c.hom.app R (x * y))).1 = _
    rw [map_mul, hmul]
    rfl
  · intro R S f x
    change (p S (c.hom.app S (((groupPointsFunctor K).obj _).map f x))).1 = _
    have h := congrArg (fun z => z x) (c.hom.naturality f)
    change c.hom.app S (((groupPointsFunctor K).obj _).map f x) =
      F.map f (c.hom.app R x) at h
    rw [h]
    exact hnat f _
  · intro R f l
    have hf : e.hom.app R (WithConv.toConv f) = (testSpec K).map (CommAlgCat.ofHom f).op := by
      apply Over.OverMorphism.ext
      exact he R f
    exact (congrArg (fun y => (b.baseChange R).repr (point R y).1 l) hf.symm).trans (hc R f l)

open private norm_algEquiv from LinearAlgebraicGroups.Arithmetic.LocalNormOneCommutators

section BlockElements

variable {K D : Type u} [Field K] [Ring D] [Algebra K D]
  {m r : ℕ} (d : Module.Basis (Fin r) K D) (j : BlockIndex.{u} m)

private theorem map_blockElement {R S : Type u} [CommRing R] [CommRing S]
    [Algebra K R] [Algebra K S] (f : R →ₐ[K] S) (a : Fin r → R) :
    Algebra.TensorProduct.map f (AlgHom.id K _) (blockElement d j a) =
      blockElement d j (f ∘ a) := by
  simp [blockElement]

private theorem baseChangeMatrix_blockElement {F : Type u} [Field F] [Algebra K F]
    (a : Fin r → F) :
    RM03.Brauer.baseChangeMatrix K F m D (blockElement d j a) =
      1 + Matrix.single j.down.1.1 j.down.1.2 (∑ l, a l ⊗ₜ[K] d l) := by
  classical
  rw [blockElement, map_add, map_one, map_sum]
  congr 1
  ext i k
  simp only [Matrix.sum_apply, RM03.Brauer.baseChangeMatrix_tmul, Matrix.single_apply]
  split_ifs <;> simp_all

private theorem blockElement_norm_field {ι : Type u} [Fintype ι] (hD : IsCentralSimple K D)
    (hm : 2 ≤ m) (b : Module.Basis ι K (Matrix (Fin m) (Fin m) D))
    {F : Type u} [Field F] [Algebra K F] [Infinite F] (a : Fin r → F) :
    normAt (matrixCentralSimple hD (Nat.zero_lt_two.trans_le hm)) b (blockElement d j a) = 1 := by
  let hA : IsCentralSimple K (Matrix (Fin m) (Fin m) D) :=
    matrixCentralSimple hD (Nat.zero_lt_two.trans_le hm)
  let hB := isCentralSimple_baseChange (L := F) hD
  let hE : IsCentralSimple F (Matrix (Fin m) (Fin m) (F ⊗[K] D)) :=
    matrixCentralSimple hB (by omega : 0 < m)
  let e := RM03.Brauer.baseChangeMatrix K F m D
  calc
    normAt hA b (blockElement d j a) =
        reducedNorm (isCentralSimple_baseChange hA) (blockElement d j a) :=
      normAt_eq_reducedNorm hA b _
    _ = reducedNorm hE (e (blockElement d j a)) := norm_algEquiv _ _ e _
    _ = 1 := by
      let u := elementary j.down.1.1 j.down.1.2 j.down.2 (∑ l, a l ⊗ₜ[K] d l)
      have he : e (blockElement d j a) = (u : Matrix _ _ _) :=
        baseChangeMatrix_blockElement d j a
      rw [he]
      letI : IsSimpleRing (F ⊗[K] D) := hB.1
      exact LocalNormOneCommutators.commutator_norm_one hE
        (LocalNormOneCommutators.elementaryGroup_le_commutator (F := F)
          (LocalNormOneCommutators.elementary_mem_elementaryGroup _ _ j.down.2 _ : u ∈ _))

private theorem blockElement_norm {ι : Type u} [Fintype ι] (hD : IsCentralSimple K D)
    (hm : 2 ≤ m) (b : Module.Basis ι K (Matrix (Fin m) (Fin m) D))
    {R : Type u} [CommRing R] [Algebra K R] (a : Fin r → R) :
    normAt (matrixCentralSimple hD (Nat.zero_lt_two.trans_le hm)) b (blockElement d j a) = 1 := by
  let hA : IsCentralSimple K (Matrix (Fin m) (Fin m) D) :=
    matrixCentralSimple hD (Nat.zero_lt_two.trans_le hm)
  let T := MvPolynomial (Fin r) K
  let F := FractionRing T
  let f : T →ₐ[K] F := IsScalarTower.toAlgHom K T F
  have hf : Function.Injective f := IsFractionRing.injective T F
  letI : IsSimpleRing D := hD.1
  letI : Nonempty (Fin r) := by
    apply not_isEmpty_iff.mp
    intro h
    letI := h
    simpa using (d.sum_repr (1 : D)).symm
  letI : Infinite F := Infinite.of_injective f hf
  let U := blockElement d j (MvPolynomial.X : Fin r → T)
  have ht : RM03.CSA.NormOneGroup.normAt hA b U = 1 := by
    apply hf
    rw [map_one, ← RM03.CSA.NormOneGroup.normAt_natural hA b f]
    change RM03.CSA.NormOneGroup.normAt hA b (Algebra.TensorProduct.map f (AlgHom.id K _) U) = 1
    rw [show U = blockElement d j (MvPolynomial.X : Fin r → T) from rfl, map_blockElement]
    exact blockElement_norm_field d j hD hm b (f ∘ MvPolynomial.X)
  trans (MvPolynomial.aeval a) (RM03.CSA.NormOneGroup.normAt hA b U)
  · rw [← RM03.CSA.NormOneGroup.normAt_natural hA b (MvPolynomial.aeval (R := K) a)]
    change normAt hA b (blockElement d j a) =
      normAt hA b (Algebra.TensorProduct.map (MvPolynomial.aeval a) (AlgHom.id K _)
        (blockElement d j (MvPolynomial.X : Fin r → T)))
    rw [map_blockElement, show (MvPolynomial.aeval a ∘ MvPolynomial.X) = a from
      funext (MvPolynomial.aeval_X a)]
  · rw [ht, map_one]

end BlockElements

section BlockMaps

variable {K D ι : Type u} [Field K] [Ring D] [Algebra K D] [Fintype ι]
  {m r : ℕ} (hD : IsCentralSimple K D) (hm : 2 ≤ m)

local notation "A" => Matrix (Fin m) (Fin m) D
local notation "hA" => matrixCentralSimple hD (Nat.zero_lt_two.trans_le hm)

variable {b : Module.Basis ι K (Matrix (Fin m) (Fin m) D)}
  (P : NormOnePresentation (matrixCentralSimple hD (Nat.zero_lt_two.trans_le hm)) b)
  (d : Module.Basis (Fin r) K D) (j : BlockIndex.{u} m)

include b

local notation "G₀" => @NormOnePresentation.group K A _ _ _ ι _ hA b P
local notation "p₀" => @NormOnePresentation.point K A _ _ _ ι _ hA b P

private def blockMap : ParameterSpace K r ⟶ (G₀).val.X := by
  let R : TestAlgebra K := CommAlgCat.of K (MvPolynomial (Fin r) K)
  let a : Fin r → R := MvPolynomial.X
  exact (p₀ R).symm
    (show {x : R ⊗[K] A // normAt hA b x = 1} from
      ⟨blockElement d j a, blockElement_norm d j hD hm b a⟩)

private theorem evaluate_blockMap (R : TestAlgebra K) (a : Fin r → R) :
    (p₀ R (evaluate (blockMap hD hm P d j) a)).1 = blockElement d j a := by
  let T := CommAlgCat.of K (MvPolynomial (Fin r) K)
  let φ : T ⟶ R := CommAlgCat.ofHom (MvPolynomial.aeval a)
  change (p₀ R (((groupPointsFunctor K).obj (G₀).val).map φ (blockMap hD hm P d j))).1 =
    blockElement d j a
  have h : (p₀ T (blockMap hD hm P d j)).1 = blockElement d j (MvPolynomial.X : Fin r → T) :=
    congrArg Subtype.val ((p₀ T).apply_symm_apply _)
  calc
    _ = Algebra.TensorProduct.map φ.hom (AlgHom.id K A) (p₀ T (blockMap hD hm P d j)).1 :=
      P.point_natural φ (blockMap hD hm P d j)
    _ = _ := by
      rw [h, map_blockElement, show (φ.hom ∘ MvPolynomial.X) = a from
        funext (MvPolynomial.aeval_X a)]

private theorem evaluate_blockMap_zero :
    evaluate (blockMap hD hm P d j) (0 : Fin r → K) = (1 :
      ((groupPointsFunctor K).obj (G₀).val).obj (CommAlgCat.of K K)) := by
  apply (p₀ (CommAlgCat.of K K)).injective
  apply Subtype.ext
  rw [evaluate_blockMap hD hm, @NormOnePresentation.point_one K A _ _ _ ι _ hA b P]
  simp [blockElement]

end BlockMaps

section PointTopology

open private glEvaluation_entry glEvaluation from LinearAlgebraicGroups.Affine.StandardGroups
open private matrixPresentation continuous_glEvaluation glVal_isEmbedding from LinearAlgebraicGroups.Arithmetic.AdelicGroups

variable {K A ι : Type u} [Field K] [Ring A] [Algebra K A] [Fintype ι]
  {hA : IsCentralSimple K A} {b : Module.Basis ι K A} (P : NormOnePresentation hA b)
  (i : MatrixRealization P.group)
  {F : Type u} [Field F] [Algebra K F] [TopologicalSpace F] [IsTopologicalDivisionRing F]

local notation "Q" => NormOneCoordinates hA b

private def pointCoord (x : PointsIn i F) (l : ι) : F :=
  (b.baseChange F).repr (P.point (CommAlgCat.of K F) x).1 l

private def evaluationHom (x : PointsIn i F) : Q →ₐ[K] F :=
  (coordinateMap (k := K) (x : Points ((testSpec K).obj (op (CommAlgCat.of K Q)))
    (CommAlgCat.of K F))).hom

omit [TopologicalSpace F] [IsTopologicalDivisionRing F] in
private theorem evaluationHom_X (x : PointsIn i F) (l : ι) :
    evaluationHom P i x (Ideal.Quotient.mk (normOneIdeal hA b) (MvPolynomial.X l)) =
      pointCoord P i x l := by
  symm
  have h := coordinateMap_spec (k := K)
    (x : Points ((testSpec K).obj (op (CommAlgCat.of K Q))) (CommAlgCat.of K F))
  change (testSpec K).map (CommAlgCat.ofHom (evaluationHom P i x)).op = x at h
  exact (congrArg (fun y : PointsIn i F => pointCoord P i y l) h.symm).trans
    (P.coordinate (CommAlgCat.of K F) (evaluationHom P i x) l)

private theorem evaluationHom_poly (x : PointsIn i F) (p : MvPolynomial ι K) :
    evaluationHom P i x (Ideal.Quotient.mk (normOneIdeal hA b) p) =
      MvPolynomial.aeval (pointCoord P i x) p := by
  have h : (evaluationHom P i x).comp (Ideal.Quotient.mkₐ K (normOneIdeal hA b)) =
      MvPolynomial.aeval (pointCoord P i x) := by
    ext l
    exact (evaluationHom_X P i x l).trans (MvPolynomial.aeval_X _ _).symm
  exact DFunLike.congr_fun h p

private theorem pointCoord_isInducing : IsInducing (pointCoord (F := F) P i) := by
  let T := CommAlgCat.of K Q
  let e : (testSpec K).obj (op T) ≅ P.group.val.X := Iso.refl _
  obtain ⟨q, hsurj, hq⟩ := matrixPresentation T e i
  have hq' (x : PointsIn i F) :
      glEvaluation (asMatrix i F x) = (evaluationHom P i x).comp q.hom := by
    have hx : (x : Points ((testSpec K).obj (op T)) (CommAlgCat.of K F)) ≫ e.inv = x :=
      Category.comp_id _
    have h := hq F x
    rw [hx] at h
    exact h
  let c : PointsIn i F → (ι → F) := pointCoord P i
  let s : TopologicalSpace (PointsIn i F) := inferInstance
  have hs : Continuous c := by
    refine continuous_pi fun l => ?_
    obtain ⟨y, hy⟩ := hsurj (Ideal.Quotient.mk (normOneIdeal hA b) (MvPolynomial.X l))
    have h (x : PointsIn i F) : c x l = glEvaluation (asMatrix i F x) y := by
      rw [hq', AlgHom.comp_apply, hy]
      exact (evaluationHom_X P i x l).symm
    simp_rw [h]
    exact (continuous_glEvaluation y).comp continuous_induced_dom
  have hI : IsInducing (fun x : PointsIn i F => (asMatrix i F x).val) :=
    glVal_isEmbedding.isInducing.comp (show IsInducing (asMatrix i F) from ⟨rfl⟩)
  let val (x : PointsIn i F) := (asMatrix i F x).val
  have ht : @Continuous (PointsIn i F) _ (TopologicalSpace.induced c inferInstance)
      inferInstance val := by
    letI : TopologicalSpace (PointsIn i F) := TopologicalSpace.induced c inferInstance
    refine continuous_matrix fun l k => ?_
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective
      (q.hom (LinearAlgebraicGroups.Specs.StandardGroups.universalMatrix K _ l k))
    have h (x : PointsIn i F) : val x l k = MvPolynomial.aeval (c x) p := by
      change (asMatrix i F x).val l k = MvPolynomial.aeval (c x) p
      rw [← glEvaluation_entry (k := K), hq', AlgHom.comp_apply, ← hp]
      exact evaluationHom_poly P i x p
    simp_rw [h, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
    exact (MvPolynomial.continuous_eval (MvPolynomial.map (algebraMap K F) p)).comp
      (show Continuous c from continuous_induced_dom)
  exact ⟨le_antisymm (continuous_iff_le_induced.mp hs)
    ((continuous_iff_le_induced.mp ht).trans hI.eq_induced.ge)⟩

end PointTopology

section LocalMatrices

open private continuous_linear_coordinate from LinearAlgebraicGroups.Arithmetic.LocalNormOneCommutators

variable {K D ι : Type u} [Field K] [Ring D] [Algebra K D] [Fintype ι]
  {m r : ℕ} (hD : IsCentralSimple K D) (hm : 2 ≤ m)

local notation "A" => Matrix (Fin m) (Fin m) D
local notation "hA" => matrixCentralSimple hD (Nat.zero_lt_two.trans_le hm)

variable {b : Module.Basis ι K (Matrix (Fin m) (Fin m) D)}
  (P : NormOnePresentation (matrixCentralSimple hD (Nat.zero_lt_two.trans_le hm)) b)
  (d : Module.Basis (Fin r) K D)
include b

local notation "G₀" => @NormOnePresentation.group K A _ _ _ ι _ hA b P
local notation "p₀" => @NormOnePresentation.point K A _ _ _ ι _ hA b P
variable (i : MatrixRealization (k := K) P.group) {F : Type u} [Field F] [Algebra K F]

local notation "CompletedD" => F ⊗[K] D
local notation "CompletedMatrix" => Matrix (Fin m) (Fin m) CompletedD
local notation "hB" => isCentralSimple_baseChange (L := F) hD
local notation "completedMatrixCSA" => matrixCentralSimple hB (Nat.zero_lt_two.trans_le hm)
local notation "e" => RM03.Brauer.baseChangeMatrix K F m D

private def pointMatrix (x : PointsIn (K := K) (G := G₀) i F) : CompletedMatrix :=
  e (p₀ (CommAlgCat.of K F) x).1

private theorem pointMatrix_norm (x : PointsIn (K := K) (G := G₀) i F) :
    reducedNorm completedMatrixCSA (pointMatrix hD hm P i x) = 1 := by
  change reducedNorm completedMatrixCSA (e (p₀ _ x).1) = _
  rw [← norm_algEquiv (isCentralSimple_baseChange hA) completedMatrixCSA e, ← normAt_eq_reducedNorm hA b]
  exact (p₀ _ x).2

private def pointUnit : PointsIn (K := K) (G := G₀) i F →* CompletedMatrixˣ where
  toFun x := ((RM03.CSA.reducedNorm_ne_zero_iff_isUnit completedMatrixCSA _).mp
    ((pointMatrix_norm hD hm P i x).trans_ne one_ne_zero)).unit
  map_one' := Units.ext (by
    change _ = (1 : CompletedMatrix)
    rw [IsUnit.unit_spec, pointMatrix]
    exact (congrArg (e) (P.point_one (CommAlgCat.of K F))).trans (map_one e))
  map_mul' x y := Units.ext (by
    simp only [Units.val_mul, IsUnit.unit_spec, pointMatrix]
    exact (congrArg (e) (P.point_mul (CommAlgCat.of K F) x y)).trans (map_mul e _ _))

private theorem pointUnit_val (x : PointsIn (K := K) (G := G₀) i F) :
    (pointUnit hD hm P i x : CompletedMatrix) = pointMatrix hD hm P i x :=
  IsUnit.unit_spec _

private theorem pointUnit_injective : Function.Injective (pointUnit (F := F) hD hm P i) := by
  intro x y h
  apply (p₀ _).injective
  apply Subtype.ext
  apply (e).injective
  exact (pointUnit_val hD hm P i x).symm.trans ((congrArg Units.val h).trans (pointUnit_val hD hm P i y))

private theorem pointUnit_mem_normOne (x : PointsIn (K := K) (G := G₀) i F) : pointUnit hD hm P i x ∈ normOne completedMatrixCSA := by
  change reducedNorm completedMatrixCSA (pointUnit hD hm P i x : CompletedMatrix) = 1
  rw [pointUnit_val, pointMatrix_norm]

private theorem pointUnit_evaluate (j : BlockIndex.{u} m) (a : Fin r → F) :
    pointUnit hD hm P i (evaluate (blockMap hD hm P d j) a) =
      elementary j.down.1.1 j.down.1.2 j.down.2 (∑ l, a l ⊗ₜ[K] d l) := by
  apply Units.ext
  let x : PointsIn (K := K) (G := G₀) i F := evaluate (blockMap hD hm P d j) a
  calc
    _ = pointMatrix hD hm P i x := pointUnit_val hD hm P i x
    _ = e (blockElement d j a) :=
      congrArg (e) (evaluate_blockMap hD hm P d j (CommAlgCat.of K F) a)
    _ = _ := baseChangeMatrix_blockElement d j a

omit b in
private theorem tensor_eq_sum_basis (x : CompletedD) :
    ∑ l, (d.baseChange F).repr x l ⊗ₜ[K] d l = x := by
  simpa only [Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one] using (d.baseChange F).sum_repr x

variable (places : GlobalFieldData.{u,v} K) (w : places.Place)

private theorem generatedAt_map :
    (generatedAt (G := G₀) (ι := BlockIndex.{u} m) (n := fun _ => r) (fun j => blockMap hD hm P d j) places i w).map (pointUnit hD hm P i) =
      elementaryGroup (B := places.Completion w ⊗[K] D) (Fin m) := by
  classical
  unfold generatedAt elementaryGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨j, a, rfl⟩, rfl⟩
    exact ⟨j.down.1.1, j.down.1.2, j.down.2, _, pointUnit_evaluate hD hm P d i j a⟩
  · rintro ⟨j, k, hjk, x, rfl⟩
    let J : BlockIndex.{u} m := ⟨⟨(j,k), hjk⟩⟩
    let a : Fin r → places.Completion w := (d.baseChange (places.Completion w)).repr x
    refine ⟨evaluate (blockMap hD hm P d J) a, ⟨J, a, rfl⟩, ?_⟩
    exact (pointUnit_evaluate hD hm P d i J a).trans (by rw [tensor_eq_sum_basis d])

private theorem generatedAt_eq_top_of_split {s : ℕ} (hs : 0 < s)
    (p : (places.Completion w ⊗[K] D) ≃ₐ[places.Completion w]
      Matrix (Fin s) (Fin s) (places.Completion w)) :
    generatedAt (G := G₀) (ι := BlockIndex.{u} m) (n := fun _ => r) (fun j => blockMap hD hm P d j) places i w = ⊤ := by
  apply top_unique
  intro g _
  have hg := pointUnit_mem_normOne (F := places.Completion w) hD hm P i g
  rw [← InnerTypeALocalGeneration.splitBlockGeneration
    (isCentralSimple_baseChange (L := places.Completion w) hD) m hm hs p] at hg
  rw [← generatedAt_map hD hm P d i places w] at hg
  obtain ⟨x, hx, h⟩ := hg
  rwa [pointUnit_injective hD hm P i h] at hx

private theorem dense_generatedAt
    (h : BlockDensity (isCentralSimple_baseChange (L := places.Completion w) hD) m hm) :
    Dense (generatedAt (G := G₀) (ι := BlockIndex.{u} m) (n := fun _ => r) (fun j => blockMap hD hm P d j) places i w :
      Set (LocalPoints places i w)) := by
  let F := places.Completion w
  letI : Field F := GlobalFieldData.instFieldCompletion places w
  letI : Algebra K F := completionAlgebra places w
  letI : TopologicalSpace F := GlobalFieldData.instTopologicalSpaceCompletion places w
  letI : IsTopologicalDivisionRing F := completionTopologicalDivisionRing places w
  let B := F ⊗[K] D
  let M := Matrix (Fin m) (Fin m) B
  let hM := matrixCentralSimple (isCentralSimple_baseChange (L := F) hD) (Nat.zero_lt_two.trans_le hm)
  letI := hM.2.2
  let c := Module.finBasis F M
  letI : TopologicalSpace M := coordinateTopology c
  let E := elementaryGroup (B := B) (Fin m)
  let H := generatedAt (G := G₀) (ι := BlockIndex.{u} m) (n := fun _ => r) (fun j => blockMap hD hm P d j) places i w
  let ψ (x : Mˣ) (l : ι) := (b.baseChange F).repr
    ((RM03.Brauer.baseChangeMatrix K F m D).symm (x : M)) l
  have hc : Continuous ψ := by
    apply continuous_pi
    intro l
    let L := ((b.baseChange F).coord l).comp
      (RM03.Brauer.baseChangeMatrix K F m D).symm.toLinearMap
    exact (continuous_linear_coordinate c L).comp Units.continuous_val
  have hψ (x : LocalPoints places i w) :
      pointCoord P i x = ψ (pointUnit hD hm P i x) := by
    funext l
    simp only [ψ, pointUnit_val, pointMatrix, AlgEquiv.symm_apply_apply, pointCoord]
    rfl
  have himage : ψ '' (E : Set Mˣ) =
      pointCoord P i '' (H : Set (LocalPoints places i w)) := by
    change ψ '' (elementaryGroup (B := B) (Fin m) : Set Mˣ) =
      pointCoord P i '' (H : Set (LocalPoints places i w))
    rw [← generatedAt_map hD hm P d i places w, Subgroup.coe_map, Set.image_image]
    exact congrArg (fun f => f '' (H : Set (LocalPoints places i w))) (funext fun x => (hψ x).symm)
  intro x
  change x ∈ closure (H : Set (LocalPoints places i w))
  rw [(pointCoord_isInducing (F := F) P i).closure_eq_preimage_closure_image]
  change pointCoord P i x ∈ closure (pointCoord P i '' (H : Set (LocalPoints places i w)))
  rw [← himage, hψ]
  exact image_closure_subset_closure_image hc (Set.mem_image_of_mem ψ
    (h.2 c (pointUnit_mem_normOne hD hm P i x)))

end LocalMatrices

section Completions

variable {F L A : Type*} [Field F] [Field L] [Ring A] [Algebra F A]
  (e : F ≃+* L)

private def transportedAlgebraEquiv :
    letI : Algebra F L := e.toRingHom.toAlgebra
    letI : Algebra L A := Algebra.compHom A e.symm.toRingHom
    L ⊗[F] A ≃ₐ[L] A := by
  letI : Algebra F L := e.toRingHom.toAlgebra
  letI : Algebra L A := Algebra.compHom A e.symm.toRingHom
  let f : F ≃ₐ[F] L := AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl)
  let g := (Algebra.TensorProduct.congr f.symm (AlgEquiv.refl : A ≃ₐ[F] A)).trans
    (Algebra.TensorProduct.lid F A)
  refine AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun z => ?_
  change g (z ⊗ₜ[F] (1 : A)) = algebraMap L A z
  change e.symm z • (1 : A) = algebraMap F A (e.symm z)
  exact (Algebra.algebraMap_eq_smul_one (e.symm z)).symm

private theorem transportedAlgebraEquiv_one_tmul (x : A) :
    letI : Algebra F L := e.toRingHom.toAlgebra
    letI : Algebra L A := Algebra.compHom A e.symm.toRingHom
    transportedAlgebraEquiv e (1 ⊗ₜ[F] x) = x := by
  change e.symm 1 • x = x
  rw [map_one, one_smul]

private theorem centralSimple_transport (hA : IsCentralSimple F A) :
    letI : Algebra L A := Algebra.compHom A e.symm.toRingHom
    IsCentralSimple L A := by
  letI : Algebra F L := e.toRingHom.toAlgebra
  letI : Algebra L A := Algebra.compHom A e.symm.toRingHom
  let f : L ⊗[F] A ≃ₐ[L] A := transportedAlgebraEquiv e
  let h := isCentralSimple_baseChange (L := L) hA
  letI := h.2.2
  letI := h.2.1
  refine ⟨hA.1, ⟨?_⟩, Module.Finite.equiv f.toLinearEquiv⟩
  intro z hz
  have hz' : f.symm z ∈ Subalgebra.center L (L ⊗[F] A) := by
    rw [Subalgebra.mem_center_iff] at hz ⊢
    intro y
    apply f.injective
    simpa only [map_mul, AlgEquiv.apply_symm_apply] using hz (f y)
  obtain ⟨r, hr⟩ := Algebra.mem_bot.mp (h.2.1.out hz')
  exact Algebra.mem_bot.mpr ⟨r, (f.commutes r).symm.trans (congrArg f hr) |>.trans
    (f.apply_symm_apply z)⟩

private theorem reducedNorm_transport (hA : IsCentralSimple F A) (x : A) :
    letI : Algebra L A := Algebra.compHom A e.symm.toRingHom
    reducedNorm (centralSimple_transport e hA) x = e (reducedNorm hA x) := by
  letI : Algebra F L := e.toRingHom.toAlgebra
  letI : Algebra L A := Algebra.compHom A e.symm.toRingHom
  calc
    reducedNorm (centralSimple_transport e hA) x =
        reducedNorm (centralSimple_transport e hA) (transportedAlgebraEquiv e (1 ⊗ₜ[F] x)) :=
      congrArg _ (transportedAlgebraEquiv_one_tmul e x).symm
    _ = reducedNorm (isCentralSimple_baseChange hA) (1 ⊗ₜ[F] x) :=
      (norm_algEquiv _ _ (transportedAlgebraEquiv e) _).symm
    _ = e (reducedNorm hA x) := RM03.CSA.reducedNorm_baseChange hA x

private theorem blockDensity_transport [TopologicalSpace F] [TopologicalSpace L]
    (he : Continuous e.symm) (hA : IsCentralSimple F A) (m : ℕ) (hm : 2 ≤ m)
    (hd : letI : Algebra L A := Algebra.compHom A e.symm.toRingHom
      BlockDensity (centralSimple_transport e hA) m hm) :
    BlockDensity hA m hm := by
  classical
  let M := Matrix (Fin m) (Fin m) A
  let hM := matrixCentralSimple hA (by omega : 0 < m)
  letI : Algebra F L := e.toRingHom.toAlgebra
  letI : Algebra L A := Algebra.compHom A e.symm.toRingHom
  let hM' := matrixCentralSimple (centralSimple_transport e hA) (by omega : 0 < m)
  let E := (elementaryGroup (B := A) (Fin m) : Set Mˣ)
  have hn (x : Mˣ) : x ∈ normOne hM' ↔ x ∈ normOne hM := by
    change reducedNorm hM' (x : M) = 1 ↔ reducedNorm hM (x : M) = 1
    letI : Algebra L M := Algebra.compHom M e.symm.toRingHom
    have h := reducedNorm_transport e hM (x : M)
    change reducedNorm hM' (x : M) = e (reducedNorm hM (x : M)) at h
    rw [h, ← map_one e, e.injective.eq_iff]
  refine ⟨fun x hx => (hn x).mp (hd.1 hx), ?_⟩
  intro b
  letI : Algebra L M := Algebra.compHom M e.symm.toRingHom
  let f : L ⊗[F] M ≃ₐ[L] M := transportedAlgebraEquiv e
  let b' := (b.baseChange L).map f.toLinearEquiv
  have hr : Module.finrank F M = Module.finrank L M := by
    rw [← f.toLinearEquiv.finrank_eq, RM03.CSA.finrank_baseChange hM]
  let c := b'.reindex (finCongr hr)
  let s : TopologicalSpace M := coordinateTopology b
  let t : TopologicalSpace M := coordinateTopology c
  have hcoord (x : M) (l : Fin (Module.finrank F M)) :
      b.repr x l = e.symm (c.repr x (finCongr hr l)) := by
    have h : c.repr x (finCongr hr l) = e (b.repr x l) := by
      have hx : f.symm x = 1 ⊗ₜ[F] x := by
        apply f.injective
        rw [AlgEquiv.apply_symm_apply]
        exact (transportedAlgebraEquiv_one_tmul e x).symm
      rw [Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply, Module.Basis.map_repr]
      change (b.baseChange L).repr (f.symm x) l = e (b.repr x l)
      rw [hx, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
      rfl
    exact (e.symm_apply_apply _).symm.trans (congrArg e.symm h.symm)
  have hcont : @Continuous M M t s id := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro l
    simp_rw [Function.comp_apply, id_eq, hcoord]
    exact he.comp ((continuous_apply _).comp continuous_induced_dom)
  let tU : TopologicalSpace Mˣ := @Units.instTopologicalSpaceUnits M t _
  let sU : TopologicalSpace Mˣ := @Units.instTopologicalSpaceUnits M s _
  have hu' := @Continuous.units_map M M _ _ t s (MonoidHom.id M) hcont
  have hu : @Continuous Mˣ Mˣ tU sU id := by
    rw [Units.map_id, MonoidHom.coe_id] at hu'
    exact hu'
  intro x hx
  have hy : x ∈ @closure Mˣ tU E := hd.2 c ((hn x).mpr hx)
  have hm' := @closure_subset_preimage_closure_image Mˣ Mˣ tU sU id E hu x hy
  simpa only [Set.mem_preimage, id_eq, Set.image_id'] using hm'

theorem completionBlockDensity {K A : Type u} [Field K] [Ring A] [Algebra K A]
    (places : GlobalFieldData.{u,v} K) (w : places.Place)
    (hA : IsCentralSimple K A) (m : ℕ) (hm : 2 ≤ m) :
    BlockDensity (isCentralSimple_baseChange (L := places.Completion w) hA) m hm := by
  cases w with
  | inl w =>
    letI : Algebra K (places.FiniteCompletion w) := (places.embedding (.inl w)).toAlgebra
    change BlockDensity (isCentralSimple_baseChange (L := places.FiniteCompletion w) hA) m hm
    exact InnerTypeALocalGeneration.localBlockGeneration.{u,u}.1 (isCentralSimple_baseChange hA) m hm
  | inr w =>
    cases places with
    | function F t => exact w.elim
    | number h =>
      let places' : GlobalFieldData.{u,v} K := .number h
      let F := places'.Completion (.inr w)
      letI : Field F := GlobalFieldData.instFieldCompletion places' (.inr w)
      letI : TopologicalSpace F := GlobalFieldData.instTopologicalSpaceCompletion places' (.inr w)
      letI : Algebra K F := completionAlgebra places' (.inr w)
      let hC := isCentralSimple_baseChange (L := F) hA
      change BlockDensity hC m hm
      rcases w.isReal_or_isComplex with hw | hw
      · obtain ⟨e, he⟩ := numberRealCompletion w hw
        let e₀ : F ≃+* ℝ := e
        let E : w.Completion ≃ᵢ ℝ := ⟨e.toEquiv, he⟩
        have he₀ : Continuous e₀.symm := E.symm.continuous
        letI : Algebra ℝ (F ⊗[K] A) := Algebra.compHom _ e₀.symm.toRingHom
        exact blockDensity_transport e₀ he₀ hC
          m hm (InnerTypeALocalGeneration.localBlockGeneration.{u,u}.2.1 (centralSimple_transport e₀ hC) m hm)
      · obtain ⟨e, he⟩ := numberComplexCompletion w hw
        let e₀ : F ≃+* ℂ := e
        let E : w.Completion ≃ᵢ ℂ := ⟨e.toEquiv, he⟩
        have he₀ : Continuous e₀.symm := E.symm.continuous
        letI : Algebra ℂ (F ⊗[K] A) := Algebra.compHom _ e₀.symm.toRingHom
        exact blockDensity_transport e₀ he₀ hC
          m hm (InnerTypeALocalGeneration.localBlockGeneration.{u,u}.2.2 (centralSimple_transport e₀ hC) m hm)

private theorem noncompact_localField {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : ¬ CompactSpace F := by
  letI := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := F)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := F).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI := Valued.toNontriviallyNormedField F (ValuativeRel.ValueGroupWithZero F)
  exact not_compactSpace_iff.mpr inferInstance

private theorem noncompact_completion {K : Type u} [Field K]
    (places : GlobalFieldData.{u,v} K) (w : places.Place) : ¬ CompactSpace (places.Completion w) := by
  cases w with
  | inl w =>
    change ¬ CompactSpace (places.FiniteCompletion w)
    exact noncompact_localField
  | inr w =>
    cases places with
    | function F t => exact w.elim
    | number h =>
      change ¬ CompactSpace w.Completion
      intro hc
      letI := hc
      rcases w.isReal_or_isComplex with hw | hw
      · obtain ⟨e, he⟩ := numberRealCompletion w hw
        exact not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℝ)
          (e.surjective.compactSpace he.continuous)
      · obtain ⟨e, he⟩ := numberComplexCompletion w hw
        exact not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℂ)
          (e.surjective.compactSpace he.continuous)

end Completions

open private continuous_linear_coordinate from LinearAlgebraicGroups.Arithmetic.LocalNormOneCommutators

private theorem localPoints_noncompact {K D ι : Type u} [Field K] [DivisionRing D] [Algebra K D]
    [Fintype ι] {m r : ℕ} (hD : IsCentralSimple K D) (hm : 2 ≤ m)
    {b : Module.Basis ι K (Matrix (Fin m) (Fin m) D)}
    (P : NormOnePresentation (matrixCentralSimple hD (Nat.zero_lt_two.trans_le hm)) b)
    (d : Module.Basis (Fin r) K D) (i : MatrixRealization P.group)
    (places : GlobalFieldData.{u,v} K) (w : places.Place) :
    ¬ CompactSpace (LocalPoints places i w) := by
  classical
  let F := places.Completion w
  letI : Field F := GlobalFieldData.instFieldCompletion places w
  letI : Algebra K F := completionAlgebra places w
  letI : TopologicalSpace F := GlobalFieldData.instTopologicalSpaceCompletion places w
  letI : IsTopologicalDivisionRing F := completionTopologicalDivisionRing places w
  let B := F ⊗[K] D
  let e := RM03.Brauer.baseChangeMatrix K F m D
  let j : BlockIndex.{u} m := ⟨⟨(⟨0, Nat.zero_lt_two.trans_le hm⟩, ⟨1, hm⟩),
    fun h => by simpa using congrArg Fin.val h⟩⟩
  letI : Nonempty (Fin r) := by
    apply not_isEmpty_iff.mp
    intro h
    letI := h
    simpa using (d.sum_repr (1 : D)).symm
  let l : Fin r := Classical.arbitrary (Fin r)
  let p : LocalPoints places i w → F := fun x =>
    (d.baseChange F).repr (pointMatrix hD hm P i x j.down.1.1 j.down.1.2) l
  have hc : Continuous p := by
    let L : (F ⊗[K] Matrix (Fin m) (Fin m) D) →ₗ[F] F :=
      ((d.baseChange F).coord l).comp
        ((Matrix.entryLinearMap F B j.down.1.1 j.down.1.2).comp e.toLinearMap)
    letI := coordinateTopology (b.baseChange F)
    have hL : Continuous L := continuous_linear_coordinate (b.baseChange F) L
    have hP : Continuous (fun x : LocalPoints places i w => (P.point (CommAlgCat.of K F) x).1) :=
      continuous_induced_rng.mpr (pointCoord_isInducing (F := F) P i).continuous
    exact hL.comp hP
  have hp : Function.Surjective p := by
    intro t
    let a : Fin r → F := fun k => if k = l then t else 0
    refine ⟨evaluate (blockMap hD hm P d j) a, ?_⟩
    have hmat : pointMatrix hD hm P i (evaluate (blockMap hD hm P d j) a) =
        1 + Matrix.single j.down.1.1 j.down.1.2 (∑ k, a k ⊗ₜ[K] d k) :=
      (congrArg e (evaluate_blockMap hD hm P d j (CommAlgCat.of K F) a)).trans
        (baseChangeMatrix_blockElement d j a)
    have hc := congrArg (fun M : Matrix (Fin m) (Fin m) B =>
      (d.baseChange F).repr (M j.down.1.1 j.down.1.2) l) hmat
    let x : B := ∑ k, a k ⊗ₜ[K] d k
    have hentry : ((1 : Matrix (Fin m) (Fin m) B) +
        Matrix.single j.down.1.1 j.down.1.2 x) j.down.1.1 j.down.1.2 = x := by
      simp only [Matrix.add_apply, Matrix.one_apply_ne j.down.2, Matrix.single_apply_same, zero_add]
    have hsum : x = t ⊗ₜ[K] d l := by
      dsimp only [x]
      rw [Finset.sum_eq_single l]
      · simp [a]
      · intro k _ hk
        simp [a, hk]
      · simp
    have hcoord : (d.baseChange F).repr (t ⊗ₜ[K] d l) l = t := by
      rw [Module.Basis.baseChange_repr_tmul, Module.Basis.repr_self]
      simp
    exact hc.trans ((congrArg (fun y : B => (d.baseChange F).repr y l)
      (hentry.trans hsum)).trans hcoord)
  intro h
  letI := h
  exact noncompact_completion places w (hp.compactSpace hc)

theorem strongApproximation : IsotropicInnerTypeAStrongApproximation.{u,v} := by
  intro K _ places D _ _ hD m hm A hA d b
  obtain ⟨P⟩ := existsPresentation (matrixCentralSimple hD (Nat.zero_lt_two.trans_le hm)) b
  let f (j : BlockIndex.{u} m) := blockMap hD hm P d j
  refine ⟨P, f, fun R j a => evaluate_blockMap hD hm P d j R a, ?_⟩
  obtain ⟨n, L, ⟨e⟩, g, hg⟩ := LinearAlgebraicGroups.faithfulLinearization K P.group
  refine ⟨⟨⟨n, L, e, g, hg⟩⟩, fun i => ?_⟩
  have hd (w : places.Place) : Dense (generatedAt (G := P.group) f places i w :
      Set (LocalPoints places i w)) :=
    dense_generatedAt hD hm P d i places w (completionBlockDensity places w hD m hm)
  refine ⟨hd, fun w s hs ⟨p⟩ => generatedAt_eq_top_of_split hD hm P d i places w hs p,
    fun w => localPoints_noncompact hD hm P d i places w, ?_⟩
  intro S hS
  exact localDenseGeneration places i S hS f (evaluate_blockMap_zero hD hm P d) (fun w => hd w.1)

end LinearAlgebraicGroups.Arithmetic.IsotropicInnerTypeA
