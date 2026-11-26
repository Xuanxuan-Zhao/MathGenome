import Specs.LinearAlgebraicGroups.Arithmetic.SplitQuadraticPairSpinComparison
import LinearAlgebraicGroups.Arithmetic.CharacteristicTwoQuadraticPairs
import LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
import LinearAlgebraicGroups.Arithmetic.SpinScalarExtension
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.ReducedCharpoly
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Matrix Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

universe u v w

namespace LinearAlgebraicGroups.Arithmetic.SplitQuadraticPairSpinComparison

open Specs.Arithmetic.SplitQuadraticPairSpinComparison
open Specs.Arithmetic.CharacteristicTwoQuadraticPairs
open Specs.Arithmetic.NontrialitarianSpinModels (DescendedQuadraticPair SpinModel symmetricPart)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open Specs.Arithmetic.IsotropicSpinGeneration (HyperbolicPair IsRegular HasSpinCocharacterFormula)
open Specs.CharacterDescent (Cocharacter)
open CocharacterDynamics (LimitDecomposition oppositeCocharacter)
open Specs.Arithmetic.OppositeRadicals (IsNoncentral)
open Albert.SpinSpecification (ScalarClifford IsSpinPointRepresentation)
open SymplecticIsometryDescent (tensorMap)

noncomputable section

set_option backward.isDefEq.respectTransparency false

section SplitComparison

variable {F K I : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ} {G : Specs.AffineAlgebraicGroup F}
  {n : ℕ} (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) F)

theorem testMatrix_tmul (R : TestAlgebra F) (r : R) (a : ρ.fixedSubalgebra) :
    testMatrix e R (r ⊗ₜ[F] a) = r • (e a).map (algebraMap F R) := by
  change (matrixEquivTensor (Fin n) F R).symm (r ⊗ₜ[F] e a) = _
  exact matrixEquivTensor_apply_symm _ _ _ r (e a)

theorem testMatrix_natural {R S : TestAlgebra F} (f : R ⟶ S)
    (a : R ⊗[F] ρ.fixedSubalgebra) :
    testMatrix e S (tensorMap f a) = (testMatrix e R a).map f.hom := by
  induction a using TensorProduct.inductionOn with
  | tmul r x =>
      change testMatrix e S (f.hom r ⊗ₜ[F] x) = (testMatrix e R (r ⊗ₜ[F] x)).map f.hom
      rw [testMatrix_tmul, testMatrix_tmul]
      ext i j
      simp
  | add a b ha hb =>
      simp only [map_add, ha, hb]
      ext i j
      exact (map_add f.hom _ _).symm

theorem recoveredForm_nonempty [CharP F 2] :
    Nonempty (RecoveredForm (D := D) e) := by
  obtain ⟨hrank, H, ell, q, hadj, hone, htrace, hq, hpolar, hreg, hisom⟩ :=
    CharacteristicTwoQuadraticPairs.splitPairRecovery D n e
  exact ⟨⟨hrank, H, ell, q, hadj, hone, htrace, hq, hpolar, hreg, hisom⟩⟩

private theorem testMatrix_adjoint (P : RecoveredForm (D := D) e) (R : TestAlgebra F)
    (x : R ⊗[F] ρ.fixedSubalgebra) :
    testMatrix e R ((D.involution.baseChange R).toLinearMap x) =
      (P.gram.inv.map (algebraMap F R)) * (testMatrix e R x).transpose *
        (P.gram.val.map (algebraMap F R)) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [SymplecticIsometryDescent.Involution.baseChange_tmul, testMatrix_tmul, testMatrix_tmul,
      P.adjoint]
    simp only [Matrix.map_mul, Matrix.transpose_smul, Matrix.transpose_map, mul_smul_comm,
      smul_mul_assoc]
  | add x y hx hy =>
    simp only [map_add, hx, hy, Matrix.transpose_add, mul_add, add_mul]

private theorem localField_infinite (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] : Infinite F := by
  obtain ⟨value, h₀, h₁⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := F)
  obtain ⟨a, rfl⟩ := ValuativeRel.valuation_surjective value
  apply Infinite.of_injective (fun m : ℕ => a ^ m)
  intro m n h
  apply (pow_right_strictAnti₀ h₀ h₁).injective
  simpa only [map_pow] using congrArg (ValuativeRel.valuation F) h

/-- The two parabolic radicals of the recovered scalar form generate the
local points once the Clifford representation on the original group is available. -/
theorem localGeneration_of_representation [CharP F 2] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (isotropy : ArithmeticSplitIsotropy.{u,v})
    (M : SpinModel G D) (P : RecoveredForm (D := D) e)
    (hG : IsAbsolutelyAlmostSimple G) (hn : 8 ≤ n)
    (a : ∀ R : TestAlgebra F, Points G.val.X R →* (ScalarClifford P.form R)ˣ)
    (ha : IsSpinPointRepresentation P.form G.val a) :
    ∃ (h : HyperbolicPair P.form) (c : Cocharacter G.val),
      HasSpinCocharacterFormula h a c ∧ IsNoncentral c ∧
      ∃ (B : LimitDecomposition c) (C : LimitDecomposition (oppositeCocharacter c)),
        Specs.SubgroupSections B.contracting (𝟙_ (SchemeOver F)) ⊔
          Specs.SubgroupSections C.contracting (𝟙_ (SchemeOver F)) = ⊤ := by
  let : Infinite F := localField_infinite F
  have harith : IsCharacteristicTwoArithmeticField.{u,v} F :=
    Or.inr ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨⟨x, hx, hqx⟩, _⟩ := isotropy harith M n P.rank hn e
    P.gram P.representative P.form P.adjoint P.traceOne P.semitrace P.diagonal P.polar P.regular
  have hreg : IsRegular P.form := Or.inl (LinearMap.BilinForm.Nondegenerate.ker_eq_bot P.regular)
  obtain ⟨h, _⟩ := IsotropicSpinGeneration.hyperbolicPairExistence P.form hreg x hx hqx
  let b := (Pi.basisFun F (Fin n)).reindex (Equiv.ulift.{u}.symm)
  obtain ⟨c, hc, hnc, _, hgen⟩ :=
    IsotropicSpinGeneration.localSpinGeneration P.form b G a ha hreg hG h
  obtain ⟨B⟩ := LinearAlgebraicGroups.CocharacterDynamics.existsLimitDecomposition G c
  obtain ⟨C⟩ := LinearAlgebraicGroups.CocharacterDynamics.existsLimitDecomposition G
    (oppositeCocharacter c)
  exact ⟨h, c, hc, hnc, B, C, (hgen B C).2.2⟩




private theorem localSplitSpinGeneration_of_comparison (isotropy : ArithmeticSplitIsotropy.{u,u})
    (comparison : SplitSpinComparison.{u}) : LocalSplitSpinGeneration.{u} := by
  intro F K I _ _ _ _ _ _ _ _ _ _ _ ρ D G M hG n hn e P
  obtain ⟨a, ha⟩ := comparison M n e P
  obtain ⟨h, c, hc, hnc, B, C, hBC⟩ :=
    localGeneration_of_representation e isotropy M P hG hn a ha.1
  exact ⟨a, h, c, ha, hc, hnc, B, C, hBC⟩

section SplitSemitrace

open Specs.Arithmetic.NontrialitarianSpinModels (adjoint hyperbolicGram hyperbolicProjection)
open SymplecticIsometryDescent (Involution)

include D in
private theorem splitIndexCard :
    Fintype.card (I ⊕ I) = _root_.Specs.RM03.CSA.degree F ρ.fixedSubalgebra := by
  rw [D.degree, Fintype.card_sum, two_mul]

include D in
private theorem splitIndex_nonempty : Nonempty (I ⊕ I) :=
  Fintype.card_pos_iff.mp (splitIndexCard (D := D) ▸ RM03.CSA.degree_pos D.centralSimple)

private theorem reducedTrace_splitting (x : ρ.fixedSubalgebra) :
    algebraMap F K (algebraReducedTrace D.centralSimple x) =
      (D.splitting (1 ⊗ₜ[F] x)).trace := by
  let : Nonempty (I ⊕ I) := splitIndex_nonempty (D := D)
  let reindex := Fintype.equivFinOfCardEq (splitIndexCard (D := D))
  have hc := RM03.CSA.reducedCharpoly_map D.centralSimple x
    (D.splitting.trans (Matrix.reindexAlgEquiv K K reindex))
  change (_root_.Specs.RM03.CSA.reducedCharpoly D.centralSimple x).map (algebraMap F K) =
    (Matrix.reindex reindex reindex (D.splitting (1 ⊗ₜ[F] x))).charpoly at hc
  rw [Matrix.charpoly_reindex] at hc
  rw [algebraReducedTrace, map_neg, Matrix.trace_eq_neg_charpoly_coeff, splitIndexCard (D := D),
    ← hc, Polynomial.coeff_map]

private theorem splitSymmetric_lift
    (x : K ⊗[F] ρ.fixedSubalgebra) (hx : (D.involution.baseChange K).toLinearMap x = x) :
    ∃ y : K ⊗[F] symmetricPart D.involution,
      (symmetricPart D.involution).subtype.baseChange K y = x := by
  let f := D.involution.toLinearMap - LinearMap.id
  have he : Function.Exact (symmetricPart D.involution).subtype f := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
    rfl
  have heK := Module.Flat.lTensor_exact (R := F) K
    (N := ↥(symmetricPart D.involution))
    (N' := ↥ρ.fixedSubalgebra) (N'' := ↥ρ.fixedSubalgebra)
    (f := (symmetricPart D.involution).subtype) (g := f) he x
  obtain ⟨y, hy⟩ := heK.mp (by
    change f.lTensor K x = 0
    rw [← LinearMap.baseChange_eq_lTensor, LinearMap.baseChange_sub, LinearMap.baseChange_id]
    change (D.involution.baseChange K).toLinearMap x - x = 0
    rw [hx, sub_self])
  exact ⟨y, hy⟩

/-- The recovered representative and the split hyperbolic projection
give equal traces on every scalar-extended self-adjoint matrix. -/
private theorem splitSemitrace_eq (P : RecoveredForm (D := D) e)
    (X : Matrix (I ⊕ I) (I ⊕ I) K) (hX : adjoint (hyperbolicGram I K) X = X) :
    (D.splitting (1 ⊗ₜ[F] P.representative) * X).trace =
      (hyperbolicProjection I K * X).trace := by
  let x := D.splitting.symm X
  have hx : (D.involution.baseChange K).toLinearMap x = x := by
    apply D.splitting.injective
    rw [D.splittingInvolution, show D.splitting x = X from D.splitting.apply_symm_apply X, hX]
  obtain ⟨y, hy⟩ := splitSymmetric_lift x hx
  rw [← D.splitting.apply_symm_apply X, ← show
    (symmetricPart D.involution).subtype.baseChange K y = D.splitting.symm X from hy]
  clear hy hx hX x X
  induction y using TensorProduct.inductionOn with
  | tmul r a =>
    rw [LinearMap.baseChange_tmul]
    change (D.splitting (1 ⊗ₜ[F] P.representative) * D.splitting (r ⊗ₜ[F] a.val)).trace =
      (hyperbolicProjection I K * D.splitting (r ⊗ₜ[F] a.val)).trace
    rw [D.splittingFormula r a.val, mul_smul_comm, mul_smul_comm,
      Matrix.trace_smul, Matrix.trace_smul]
    apply congrArg (r • ·)
    rw [← D.semitraceFormula, P.semitrace, reducedTrace_splitting (D := D)]
    rw [← show D.splitting (1 ⊗ₜ[F] a.val) = a.val.val by
      rw [D.splittingFormula, one_smul], ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add y z hy hz =>
    simp only [map_add, mul_add, Matrix.trace_add, hy, hz]

end SplitSemitrace


section MatrixAdjoints

variable {k J : Type*} [Field k] [Fintype J] [DecidableEq J] [Nonempty J]

private def transposeUnit (U : (Matrix J J k)ˣ) : (Matrix J J k)ˣ where
  val := U.val.transpose
  inv := U.inv.transpose
  val_inv := by rw [← Matrix.transpose_mul, U.inv_val, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, U.val_inv, Matrix.transpose_one]

/-- Two nonsingular Gram matrices inducing the same adjoint differ by a
nonzero scalar. The argument uses the center of the full matrix algebra. -/
private theorem gram_scalar (H C : (Matrix J J k)ˣ)
    (h : ∀ X : Matrix J J k, H.inv * X.transpose * H.val = C.inv * X.transpose * C.val) :
    ∃ d : kˣ, H.val = (d : k) • C.val := by
  have hc : H.val * C.inv ∈ Subalgebra.center k (Matrix J J k) := by
    rw [Subalgebra.mem_center_iff]
    intro X
    have he := congrArg (fun Y : Matrix J J k => H.val * Y * C.inv) (h X.transpose)
    have hh : H.val * (H.inv * (X * (H.val * C.inv))) =
        H.val * (C.inv * (X * (C.val * C.inv))) := by
      simpa only [Matrix.transpose_transpose, Matrix.mul_assoc] using he
    rw [show H.val * (H.inv * (X * (H.val * C.inv))) = X * (H.val * C.inv) from
      H.mul_inv_cancel_left _, C.val_inv, mul_one] at hh
    simpa only [Matrix.mul_assoc] using hh
  have hs : H.val * C.inv ∈ (⊥ : Subalgebra k (Matrix J J k)) :=
    (inferInstance : Algebra.IsCentral k (Matrix J J k)).out hc
  obtain ⟨d, hd⟩ := Algebra.mem_bot.mp hs
  have hd' : d • (1 : Matrix J J k) = H.val * C.inv := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact hd
  have heq : H.val = d • C.val := by
    have hh := congrArg (· * C.val) hd'
    simpa only [smul_mul_assoc, one_mul, Matrix.mul_assoc, C.inv_val, mul_one] using hh.symm
  have hn : d ≠ 0 := by
    rintro rfl
    exact H.ne_zero (by simp at heq)
  exact ⟨Units.mk0 d hn, heq⟩

omit [DecidableEq J] [Nonempty J] in
/-- The trace of a left multiplication against a rank-one operator recovers
the diagonal value associated to the Gram matrix. -/
private theorem trace_rankOne (H L : Matrix J J k) (x : J → k) :
    (L * Matrix.vecMulVec x (H.transpose *ᵥ x)).trace = x ⬝ᵥ (H *ᵥ (L *ᵥ x)) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm, Matrix.mulVec_transpose,
    ← Matrix.dotProduct_mulVec]

end MatrixAdjoints


section SplitMatrix

open Specs.Arithmetic.NontrialitarianSpinModels (adjoint hyperbolicGram hyperbolicProjection)

private def recoveredIndexEquiv (P : RecoveredForm (D := D) e) : Fin n ≃ I ⊕ I :=
  (Fintype.equivFinOfCardEq (by rw [Fintype.card_sum, P.rank, two_mul])).symm

private def recoveredSplitMatrix (P : RecoveredForm (D := D) e) :
    (K ⊗[F] ρ.fixedSubalgebra) ≃ₐ[K] Matrix (I ⊕ I) (I ⊕ I) K :=
  (testMatrix e (CommAlgCat.of F K)).trans
    (Matrix.reindexAlgEquiv K K (recoveredIndexEquiv e P))

private def recoveredSplitGram (P : RecoveredForm (D := D) e) :
    (Matrix (I ⊕ I) (I ⊕ I) K)ˣ :=
  Units.map (Matrix.reindexAlgEquiv K K (recoveredIndexEquiv e P)).toMonoidHom
    (Units.map (algebraMap F K).mapMatrix.toMonoidHom P.gram)

private theorem recoveredSplitMatrix_adjoint (P : RecoveredForm (D := D) e)
    (x : K ⊗[F] ρ.fixedSubalgebra) :
    recoveredSplitMatrix e P ((D.involution.baseChange K).toLinearMap x) =
      (recoveredSplitGram e P).inv * (recoveredSplitMatrix e P x).transpose *
        (recoveredSplitGram e P).val := by
  let R := CommAlgCat.of F K
  let indexMatrix := Matrix.reindexAlgEquiv K K (recoveredIndexEquiv e P)
  change indexMatrix (testMatrix e R ((D.involution.baseChange R).toLinearMap x)) = _
  rw [testMatrix_adjoint e P R, map_mul, map_mul]
  rfl

private def splitGramUnit : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ where
  val := hyperbolicGram I K
  inv := hyperbolicGram I K
  val_inv := by simp [hyperbolicGram, Matrix.fromBlocks_multiply]
  inv_val := by simp [hyperbolicGram, Matrix.fromBlocks_multiply]

private theorem splitGram_transpose :
    (hyperbolicGram I K).transpose = hyperbolicGram I K := by
  simp [hyperbolicGram, Matrix.fromBlocks_transpose]

/-- The two split matrix presentations of the pair differ by conjugation
on the matrix algebra, with proportional transported Gram matrices. -/
private theorem recoveredSplit_changeOfBasis (P : RecoveredForm (D := D) e) :
    ∃ (U : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) (d : Kˣ),
      (∀ x : K ⊗[F] ρ.fixedSubalgebra,
        D.splitting x = U.val * recoveredSplitMatrix e P x * U.inv) ∧
      (recoveredSplitGram e P).val = (d : K) •
        (U.val.transpose * hyperbolicGram I K * U.val) := by
  let : Nonempty (I ⊕ I) := splitIndex_nonempty (D := D)
  let E := recoveredSplitMatrix e P
  have hA := RM03.CSA.isCentralSimple_baseChange (L := K) D.centralSimple
  let := hA.2.1
  have hmat : RM03.CSA.IsCentralSimple K (Matrix (I ⊕ I) (I ⊕ I) K) :=
    ⟨IsSimpleRing.of_ringEquiv D.splitting.toRingEquiv hA.1,
      Algebra.IsCentral.of_algEquiv _ _ _ D.splitting, inferInstance⟩
  obtain ⟨U, hU⟩ := RM03.CSA.algEquiv_isInner hmat (E.symm.trans D.splitting)
  have hU' (x : K ⊗[F] ρ.fixedSubalgebra) : D.splitting x = U.val * E x * U.inv := by
    change _ = U.val * E x * (↑U⁻¹ : Matrix _ _ K)
    simpa only [AlgEquiv.trans_apply, E.symm_apply_apply] using hU (E x)
  let H := recoveredSplitGram e P
  let J : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ := splitGramUnit
  let C := transposeUnit U * J * U
  have hAdj (X : Matrix (I ⊕ I) (I ⊕ I) K) :
      H.inv * X.transpose * H.val = C.inv * X.transpose * C.val := by
    have hh := (hU' ((D.involution.baseChange K).toLinearMap (E.symm X))).symm.trans
      (D.splittingInvolution (E.symm X))
    rw [show E ((D.involution.baseChange K).toLinearMap (E.symm X)) =
      H.inv * X.transpose * H.val by
        rw [recoveredSplitMatrix_adjoint e P]
        rw [show recoveredSplitMatrix e P (E.symm X) = X from E.apply_symm_apply X]] at hh
    rw [hU', E.apply_symm_apply] at hh
    have hh' := congrArg (fun X : Matrix (I ⊕ I) (I ⊕ I) K => U.inv * X * U.val) hh
    have hleft :
        U.inv * (U.val * (H.inv * X.transpose * H.val) * U.inv) * U.val =
          H.inv * X.transpose * H.val := by
      calc
        _ = (U.inv * U.val) * (H.inv * X.transpose * H.val) * (U.inv * U.val) := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [U.inv_val, one_mul, mul_one]
    rw [hleft] at hh'
    change _ = (U.inv * (J.inv * (transposeUnit U).inv)) * X.transpose *
      (U.val.transpose * hyperbolicGram I K * U.val)
    simpa only [J, adjoint, splitGramUnit, transposeUnit, Matrix.transpose_mul,
      Matrix.mul_assoc] using hh'
  obtain ⟨d, hd⟩ := gram_scalar H C hAdj
  exact ⟨U, d, hU', hd⟩


private theorem splitRankOne_selfAdjoint (y : I ⊕ I → K) :
    adjoint (hyperbolicGram I K) (Matrix.vecMulVec y (hyperbolicGram I K *ᵥ y)) =
      Matrix.vecMulVec y (hyperbolicGram I K *ᵥ y) := by
  let J : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ := splitGramUnit
  unfold adjoint
  rw [Matrix.transpose_vecMulVec, Matrix.mul_vecMulVec, Matrix.mulVec_mulVec]
  change Matrix.vecMulVec ((J.val * J.inv) *ᵥ y) y * J.val = _
  rw [J.val_inv, Matrix.one_mulVec, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose]
  change Matrix.vecMulVec y ((hyperbolicGram I K).transpose *ᵥ y) = _
  rw [splitGram_transpose]

private theorem splitRankOne_semitrace (y : I ⊕ I → K) :
    (hyperbolicProjection I K *
      Matrix.vecMulVec y (hyperbolicGram I K *ᵥ y)).trace =
      Specs.Arithmetic.OddSpinModels.hyperbolicForm I K y := by
  rw [← splitGram_transpose (I := I) (K := K), trace_rankOne]
  rw [Matrix.mulVec_mulVec]
  have h : hyperbolicGram I K * hyperbolicProjection I K =
      Matrix.fromBlocks 0 1 0 0 := by
    simp [hyperbolicGram, hyperbolicProjection, Matrix.fromBlocks_multiply]
  rw [h]
  exact (Matrix.toLinearMap₂'_apply' _ _ _).symm

/-- Equality of the semitraces on rank-one operators identifies the
quadratic forms, including the Gram matrix's multiplier. -/
private theorem recoveredSplit_similarity (P : RecoveredForm (D := D) e) :
    ∃ (U : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) (d : Kˣ),
      (∀ x : K ⊗[F] ρ.fixedSubalgebra,
        D.splitting x = U.val * recoveredSplitMatrix e P x * U.inv) ∧
      ∀ x : I ⊕ I → K, x ⬝ᵥ ((recoveredSplitGram e P).val *ᵥ
        (recoveredSplitMatrix e P (1 ⊗ₜ[F] P.representative) *ᵥ x)) =
        (d : K) * Specs.Arithmetic.OddSpinModels.hyperbolicForm I K (U.val *ᵥ x) := by
  obtain ⟨U, d, hU, hd⟩ := recoveredSplit_changeOfBasis e P
  refine ⟨U, d, hU, fun x => ?_⟩
  let L := recoveredSplitMatrix e P (1 ⊗ₜ[F] P.representative)
  let J := hyperbolicGram I K
  let y := U.val *ᵥ x
  have htrace := splitSemitrace_eq e P (Matrix.vecMulVec y (J *ᵥ y))
    (splitRankOne_selfAdjoint y)
  rw [hU, splitRankOne_semitrace] at htrace
  rw [← show J.transpose = J from splitGram_transpose, trace_rankOne] at htrace
  have hcolumn : (U.val * L * U.inv) *ᵥ y = U.val *ᵥ (L *ᵥ x) := by
    change (U.val * L * U.inv) *ᵥ (U.val *ᵥ x) = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc _ U.inv U.val, U.inv_val, mul_one,
      ← Matrix.mulVec_mulVec]
  rw [hcolumn] at htrace
  change (U.val *ᵥ x) ⬝ᵥ (J *ᵥ (U.val *ᵥ (L *ᵥ x))) = _ at htrace
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec] at htrace
  have hx : x ⬝ᵥ ((U.val.transpose * J * U.val) *ᵥ (L *ᵥ x)) =
      Specs.Arithmetic.OddSpinModels.hyperbolicForm I K y := by
    simpa only [Matrix.mul_assoc] using htrace
  change x ⬝ᵥ ((recoveredSplitGram e P).val *ᵥ (L *ᵥ x)) = _
  rw [hd, Matrix.smul_mulVec, dotProduct_smul, hx]
  rfl


/-- The change of matrix coordinates is compatible with the comparison
of the actual model on every test algebra over the splitting field. -/
private theorem recoveredTestMatrix_changeOfBasis (P : RecoveredForm (D := D) e)
    (U : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ)
    (hU : ∀ x : K ⊗[F] ρ.fixedSubalgebra,
      D.splitting x = U.val * recoveredSplitMatrix e P x * U.inv)
    (S : TestAlgebra K)
    (E : (((restrictTestAlgebra F K).obj S) ⊗[F] ρ.fixedSubalgebra) ≃ₐ[S]
      Matrix (I ⊕ I) (I ⊕ I) S)
    (hE : ∀ (s : S) (a : ρ.fixedSubalgebra),
      E (s ⊗ₜ[F] a) = s • a.val.map (algebraMap K S))
    (x : ((restrictTestAlgebra F K).obj S) ⊗[F] ρ.fixedSubalgebra) :
    E x = U.val.map (algebraMap K S) *
      Matrix.reindex (recoveredIndexEquiv e P) (recoveredIndexEquiv e P)
        (testMatrix e ((restrictTestAlgebra F K).obj S) x) *
      U.inv.map (algebraMap K S) := by
  let indexEquiv := recoveredIndexEquiv e P
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    have he := hU (1 ⊗ₜ[F] a)
    change D.splitting (1 ⊗ₜ[F] a) = U.val *
      Matrix.reindex indexEquiv indexEquiv
        (testMatrix e (CommAlgCat.of F K) (1 ⊗ₜ[F] a)) * U.inv at he
    rw [D.splittingFormula, one_smul, testMatrix_tmul, one_smul] at he
    have hs := congrArg (fun A : Matrix (I ⊕ I) (I ⊕ I) K => A.map (algebraMap K S)) he
    rw [hE, testMatrix_tmul]
    have hr (A : Matrix (Fin n) (Fin n) ((restrictTestAlgebra F K).obj S)) :
        Matrix.reindex indexEquiv indexEquiv (r • A) =
          r • Matrix.reindex indexEquiv indexEquiv A := rfl
    rw [hr, mul_smul_comm, smul_mul_assoc]
    apply congrArg (r • ·)
    have hmap :
        (Matrix.reindex indexEquiv indexEquiv ((e a).map (algebraMap F K))).map
          (algebraMap K S) =
        Matrix.reindex indexEquiv indexEquiv ((e a).map
          (algebraMap F ((restrictTestAlgebra F K).obj S))) := by
      ext i j
      rfl
    simpa only [Matrix.map_mul, hmap] using hs
  | add x y hx hy =>
    let indexMatrix := Matrix.reindexLinearEquiv S S indexEquiv indexEquiv
    change E (x + y) = U.val.map (algebraMap K S) *
      indexMatrix (testMatrix e ((restrictTestAlgebra F K).obj S) (x + y)) *
      U.inv.map (algebraMap K S)
    simp only [map_add, mul_add, add_mul]
    exact congrArg₂ (· + ·) hx hy

end SplitMatrix



section SplitPoints

open Specs.Arithmetic.NontrialitarianSpinModels (SplitSpinVectorImage)
open Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open Albert.SpinSpecification (IsVectorAction spinUnits coefficientMap)

private def pointComparison (M : SpinModel G D) (S : TestAlgebra K) :
    Points G.val.X ((restrictTestAlgebra F K).obj S) ≃*
      Points M.splitCover.spin.val.X S :=
  (baseChangePointGroupEquiv K G.val S).symm.trans
    (((groupPointsFunctor K).mapIso M.splitSource).app S).groupIsoToMulEquiv

private theorem pointComparison_apply (M : SpinModel G D) (S : TestAlgebra K)
    (p : Points G.val.X ((restrictTestAlgebra F K).obj S)) :
    pointComparison M S p = ((baseChangePointGroupEquiv K G.val S).symm p) ≫
      M.splitSource.hom.hom.hom := rfl

private theorem pointComparison_natural (M : SpinModel G D) {S T : TestAlgebra K}
    (f : S ⟶ T) (p : Points G.val.X ((restrictTestAlgebra F K).obj S)) :
    pointComparison M T (mapPoints ((restrictTestAlgebra F K).map f) p) =
      mapPoints f (pointComparison M S p) := by
  let pK := (baseChangePointGroupEquiv K G.val S).symm p
  have h : (baseChangePointGroupEquiv K G.val T).symm
      (mapPoints ((restrictTestAlgebra F K).map f) p) = mapPoints f pK := by
    apply (baseChangePointGroupEquiv K G.val T).injective
    rw [MulEquiv.apply_symm_apply]
    change _ = baseChangePoint F K G.val.X T (mapPoints f pK)
    rw [baseChangePointsNaturality]
    exact congrArg (mapPoints ((restrictTestAlgebra F K).map f))
      ((baseChangePointGroupEquiv K G.val S).apply_symm_apply p).symm
  rw [pointComparison_apply, pointComparison_apply, h]
  exact Category.assoc _ _ _

private def originalSplitPoints (M : SpinModel G D) (S : TestAlgebra K) :
    Points G.val.X ((restrictTestAlgebra F K).obj S) →*
      (ScalarClifford (hyperbolicForm I K) S)ˣ :=
  (M.splitCover.spinPoints S).comp (pointComparison M S).toMonoidHom

private theorem originalSplitPoints_natural (M : SpinModel G D) {S T : TestAlgebra K}
    (f : S ⟶ T) (p : Points G.val.X ((restrictTestAlgebra F K).obj S)) :
    originalSplitPoints M T (mapPoints ((restrictTestAlgebra F K).map f) p) =
      Units.map (coefficientMap (hyperbolicForm I K) S f.hom).toMonoidHom
        (originalSplitPoints M S p) := by
  change M.splitCover.spinPoints T
      (pointComparison M T (mapPoints ((restrictTestAlgebra F K).map f) p)) = _
  rw [pointComparison_natural M f p]
  exact M.splitCover.spinRepresents.2 f (pointComparison M S p)

private theorem originalSplitPoints_range (M : SpinModel G D) (S : TestAlgebra K) :
    Function.Injective (originalSplitPoints M S) ∧
      Set.range (originalSplitPoints M S) = spinUnits (hyperbolicForm I K) S := by
  have h := M.splitCover.spinRepresents.1 S
  refine ⟨h.1.comp (pointComparison M S).injective, ?_⟩
  rw [← h.2]
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨pointComparison M S p, rfl⟩
  · rintro ⟨p, rfl⟩
    obtain ⟨p₀, hp₀⟩ := (pointComparison M S).surjective p
    exact ⟨p₀, congrArg (M.splitCover.spinPoints S) hp₀⟩

/-- The split Clifford representation on the original points has the vector
matrix obtained by conjugating the recovered matrix coordinates. -/
private theorem originalSplitPoints_vector (M : SpinModel G D) (P : RecoveredForm (D := D) e)
    (U : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ)
    (hU : ∀ x : K ⊗[F] ρ.fixedSubalgebra,
      D.splitting x = U.val * recoveredSplitMatrix e P x * U.inv)
    (S : TestAlgebra K) (p : Points G.val.X ((restrictTestAlgebra F K).obj S)) :
    ∃ g : (S ⊗[K] (I ⊕ I → K)) ≃ₗ[S] (S ⊗[K] (I ⊕ I → K)),
      IsVectorAction (hyperbolicForm I K) S (originalSplitPoints M S p) g ∧
      let b := (Pi.basisFun K (I ⊕ I)).baseChange S
      let R := (restrictTestAlgebra F K).obj S
      LinearMap.toMatrix b b g.toLinearMap = U.val.map (algebraMap K S) *
        Matrix.reindex (recoveredIndexEquiv e P) (recoveredIndexEquiv e P)
          (testMatrix e R (M.fullPoints R
            (p ≫ (M.projection ≫ M.inclusion).hom.hom)).val) * U.inv.map (algebraMap K S) := by
  let pK := (baseChangePointGroupEquiv K G.val S).symm p
  let a := pointComparison M S p
  let f := M.projection ≫ M.inclusion
  let pFull := pK ≫ ((groupBaseChange F K).map f).hom.hom
  obtain ⟨g, hg, hm⟩ := M.splitCover.vector S a
  refine ⟨g, hg, ?_⟩
  have hcomp : (groupBaseChange F K).map f ≫ M.splitFull.hom =
      M.splitSource.hom ≫ M.splitCover.projection ≫ M.splitCover.inclusion := by
    dsimp only [f]
    rw [Functor.map_comp, Category.assoc, M.inclusionComparison, ← Category.assoc,
      M.projectionComparison, Category.assoc]
  have hpFull : pFull ≫ M.splitFull.hom.hom.hom =
      a ≫ (M.splitCover.projection ≫ M.splitCover.inclusion).hom.hom := by
    rw [show a = pK ≫ M.splitSource.hom.hom.hom from pointComparison_apply M S p]
    change (pK ≫ ((groupBaseChange F K).map f).hom.hom) ≫ M.splitFull.hom.hom.hom =
      (pK ≫ M.splitSource.hom.hom.hom) ≫ (M.splitCover.projection ≫ M.splitCover.inclusion).hom.hom
    rw [Category.assoc, Category.assoc]
    congr 1
    exact congrArg (fun gh => gh.hom.hom) hcomp
  have hpbase : baseChangePoint F K M.full.val.X S pFull = p ≫ f.hom.hom := by
    exact (baseChangePointsSchemeNaturality F K f.hom.hom S pK).trans
      (congrArg (· ≫ f.hom.hom) ((baseChangePointGroupEquiv K G.val S).apply_symm_apply p))
  obtain ⟨E, hE, hpoints⟩ := M.matrixComparison S
  have hX := hpoints pFull
  rw [hpFull, hpbase] at hX
  dsimp only
  rw [hm]
  change (M.splitCover.orthogonal.points S
    (a ≫ (M.splitCover.projection ≫ M.splitCover.inclusion).hom.hom)).val.val = _
  rw [← hX]
  exact recoveredTestMatrix_changeOfBasis e P U hU S E hE _

end SplitPoints

section ScalarCoordinates

open Albert.CliffordSpecification (coefficientForm)

variable {k S J : Type*} [CommRing k] [CommRing S] [Algebra k S]
  [Fintype J] [DecidableEq J]

private def columnCoordinates : (S ⊗[k] (J → k)) ≃ₗ[S] (J → S) :=
  ((Pi.basisFun k J).baseChange S).equivFun

omit [DecidableEq J] in
private theorem columnCoordinates_one_tmul (x : J → k) :
    columnCoordinates (k := k) (S := S) (1 ⊗ₜ[k] x) = algebraMap k S ∘ x := by
  funext j
  change ((Pi.basisFun k J).baseChange S).repr (1 ⊗ₜ[k] x) j = _
  simp [Module.Basis.baseChange_repr_tmul, Algebra.smul_def]

private def matrixQuadratic (A : Matrix J J k) : QuadraticForm k (J → k) :=
  LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' k A)

private theorem matrixQuadratic_apply (A : Matrix J J k) (x : J → k) :
    matrixQuadratic A x = x ⬝ᵥ (A *ᵥ x) :=
  Matrix.toLinearMap₂'_apply' _ _ _

private theorem matrixQuadratic_map (A : Matrix J J k) (x : J → k) :
    matrixQuadratic (A.map (algebraMap k S)) (algebraMap k S ∘ x) =
      algebraMap k S (matrixQuadratic A x) := by
  simp only [matrixQuadratic_apply, RingHom.map_dotProduct]
  congr 1
  funext j
  exact ((algebraMap k S).map_mulVec A x j).symm

private theorem coefficientForm_matrixQuadratic [LinearOrder J] (A : Matrix J J k) :
    coefficientForm S (matrixQuadratic A) (Pi.basisFun k J) =
      (matrixQuadratic (A.map (algebraMap k S))).comp
        (columnCoordinates (k := k) (S := S)).toLinearMap := by
  symm
  apply (Albert.CliffordModel.coefficient_form_unique S (matrixQuadratic A) (Pi.basisFun k J) _).2
  intro x
  change matrixQuadratic (A.map (algebraMap k S))
    (columnCoordinates (1 ⊗ₜ[k] x)) = _
  rw [columnCoordinates_one_tmul, matrixQuadratic_map]

/-- A matrix similarity of quadratic forms remains a similarity after
extension to an arbitrary commutative algebra. -/
private theorem matrixSimilarity_baseChange
    (A B U : Matrix J J k) (d : k)
    (h : ∀ x, matrixQuadratic A x = d * matrixQuadratic B (U *ᵥ x)) :
    ∀ x : J → S, matrixQuadratic (A.map (algebraMap k S)) x =
      algebraMap k S d * matrixQuadratic (B.map (algebraMap k S))
        (U.map (algebraMap k S) *ᵥ x) := by
  let C : (S ⊗[k] (J → k)) ≃ₗ[S] (J → S) := columnCoordinates
  let Q₁ := (matrixQuadratic (A.map (algebraMap k S))).comp C.toLinearMap
  let Q₂ := algebraMap k S d • ((matrixQuadratic (B.map (algebraMap k S))).comp
    ((U.map (algebraMap k S)).mulVecLin.comp C.toLinearMap))
  have hQ : Q₁ = Q₂ := by
    apply baseChange_ext
    intro x
    change matrixQuadratic (A.map (algebraMap k S)) (C (1 ⊗ₜ[k] x)) =
      algebraMap k S d * matrixQuadratic (B.map (algebraMap k S))
        (U.map (algebraMap k S) *ᵥ C (1 ⊗ₜ[k] x))
    have hmul : U.map (algebraMap k S) *ᵥ (algebraMap k S ∘ x) =
        algebraMap k S ∘ (U *ᵥ x) := by
      funext j
      exact ((algebraMap k S).map_mulVec U x j).symm
    rw [show C (1 ⊗ₜ[k] x) = algebraMap k S ∘ x from columnCoordinates_one_tmul x,
      hmul, matrixQuadratic_map, matrixQuadratic_map, h, map_mul]
  intro x
  have hx := congrArg (fun Q : QuadraticForm S (S ⊗[k] (J → k)) => Q (C.symm x)) hQ
  change matrixQuadratic (A.map (algebraMap k S)) (C (C.symm x)) =
    algebraMap k S d * matrixQuadratic (B.map (algebraMap k S))
      (U.map (algebraMap k S) *ᵥ C (C.symm x)) at hx
  simpa only [C.apply_symm_apply] using hx


private theorem matrixQuadratic_reindex {L : Type*} [Fintype L] [DecidableEq L]
    (f : J ≃ L) (A : Matrix J J k) (x : J → k) :
    matrixQuadratic (Matrix.reindex f f A) (x ∘ f.symm) = matrixQuadratic A x := by
  rw [matrixQuadratic_apply, matrixQuadratic_apply, Matrix.reindex_apply,
    Matrix.submatrix_mulVec_equiv]
  have hx : (x ∘ f.symm) ∘ f = x := by
    funext i
    exact congrArg x (f.symm_apply_apply i)
  simp only [Equiv.symm_symm, hx, comp_equiv_dotProduct_comp_equiv]

private theorem columnEquiv_apply {k' J' : Type u} [CommRing k'] [Fintype J']
    [DecidableEq J'] (U : (Matrix J' J' k')ˣ) (x : J' → k') :
    Specs.Arithmetic.NontrialitarianSpinModels.matrixColumnEquiv U x = U.val *ᵥ x := rfl

end ScalarCoordinates


section TestSimilarity

open Albert.CliffordSpecification (coefficientForm)
open Specs.Arithmetic.NontrialitarianSpinModels (hyperbolicGram matrixColumnEquiv)
open Specs.Arithmetic.OddSpinModels (hyperbolicForm)

private def testVectorSimilarity (P : RecoveredForm (D := D) e)
    (U : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) (S : TestAlgebra K) :
    (((restrictTestAlgebra F K).obj S) ⊗[F] (Fin n → F)) ≃ₗ[S] (S ⊗[K] (I ⊕ I → K)) :=
  let R := (restrictTestAlgebra F K).obj S
  (columnCoordinates (k := F) (S := R)).trans <|
    (LinearEquiv.funCongrLeft S S (recoveredIndexEquiv e P).symm).trans <|
    (matrixColumnEquiv (Units.map (algebraMap K S).mapMatrix.toMonoidHom U)).trans
      (columnCoordinates (k := K) (S := S)).symm

/-- The similarity over the splitting field gives the actual coefficient
forms an invertible-multiplier comparison on each test algebra. -/
private theorem testVectorSimilarity_quadratic [LinearOrder (I ⊕ I)]
    (P : RecoveredForm (D := D) e) (U : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) (d : Kˣ)
    (h : ∀ x : I ⊕ I → K, x ⬝ᵥ ((recoveredSplitGram e P).val *ᵥ
        (recoveredSplitMatrix e P (1 ⊗ₜ[F] P.representative) *ᵥ x)) =
        (d : K) * hyperbolicForm I K (U.val *ᵥ x))
    (S : TestAlgebra K) (x : ((restrictTestAlgebra F K).obj S) ⊗[F] (Fin n → F)) :
    let R := (restrictTestAlgebra F K).obj S
    algebraMap K S d.val *
      coefficientForm S (hyperbolicForm I K) (Pi.basisFun K (I ⊕ I))
        (testVectorSimilarity e P U S x) = coefficientForm R P.form (Pi.basisFun F (Fin n)) x := by
  let R := (restrictTestAlgebra F K).obj S
  let indexEquiv := recoveredIndexEquiv e P
  let A := P.gram.val * e P.representative
  let B : Matrix (I ⊕ I) (I ⊕ I) K := Matrix.fromBlocks 0 1 0 0
  let A' := Matrix.reindex indexEquiv indexEquiv (A.map (algebraMap F K))
  have hP : P.form = matrixQuadratic A := by
    ext y
    rw [P.diagonal, matrixQuadratic_apply, Matrix.mulVec_mulVec]
  have hB : hyperbolicForm I K = matrixQuadratic B := rfl
  have hA' : A' = (recoveredSplitGram e P).val *
      recoveredSplitMatrix e P (1 ⊗ₜ[F] P.representative) := by
    let indexMat := Matrix.reindexAlgEquiv K K indexEquiv
    change indexMat (A.map (algebraMap F K)) =
      indexMat (P.gram.val.map (algebraMap F K)) *
        indexMat (testMatrix e (CommAlgCat.of F K) (1 ⊗ₜ[F] P.representative))
    rw [testMatrix_tmul, one_smul, ← map_mul]
    congr 1
    exact Matrix.map_mul
  have h' (z : I ⊕ I → K) : matrixQuadratic A' z =
      d.val * matrixQuadratic B (U.val *ᵥ z) := by
    rw [matrixQuadratic_apply, hA', ← Matrix.mulVec_mulVec, ← hB]
    exact h z
  have hext := matrixSimilarity_baseChange (S := S) A' B U.val d.val h'
  let v := columnCoordinates (k := F) (S := R) x
  let w := v ∘ indexEquiv.symm
  have hw :
      columnCoordinates (k := K) (S := S) (testVectorSimilarity e P U S x) =
        U.val.map (algebraMap K S) *ᵥ w := by
    change columnCoordinates (k := K) (S := S)
      ((columnCoordinates (k := K) (S := S)).symm
        (matrixColumnEquiv (Units.map (algebraMap K S).mapMatrix.toMonoidHom U) w)) = _
    rw [LinearEquiv.apply_symm_apply, columnEquiv_apply]
    rfl
  change _ = coefficientForm R P.form (Pi.basisFun F (Fin n)) x
  rw [hB, hP, coefficientForm_matrixQuadratic, coefficientForm_matrixQuadratic]
  change algebraMap K S d.val * matrixQuadratic (B.map (algebraMap K S))
    (columnCoordinates (testVectorSimilarity e P U S x)) =
      matrixQuadratic (A.map (algebraMap F R)) v
  rw [hw, ← hext w]
  have hm : A'.map (algebraMap K S) =
      Matrix.reindex indexEquiv indexEquiv (A.map (algebraMap F R)) := by
    ext i j
    rfl
  rw [hm]
  exact matrixQuadratic_reindex indexEquiv (A.map (algebraMap F R)) v

end TestSimilarity

section CliffordSimilarity

open CliffordAlgebra

variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]
  {q : QuadraticForm R V} {Q : QuadraticForm R W}
  (U : V ≃ₗ[R] W) (d : Rˣ) (h : ∀ x, (d : R) * Q (U x) = q x)

/-- The even Clifford map for a similarity scales each product of two
vectors by the inverse multiplier. -/
private def evenSimilarity : even q →ₐ[R] even Q :=
  even.lift q
    { bilin := LinearMap.mk₂ R
        (fun x y => (d : R) • (even.ι Q).bilin (U x) (U y))
        (fun x y z => by simp [smul_add])
        (fun r x y => by simp [smul_comm (d : R) r])
        (fun x y z => by simp [smul_add])
        (fun r x y => by simp [smul_comm (d : R) r])
      contract := fun x => by
        change (d : R) • (even.ι Q).bilin (U x) (U x) = _
        rw [(even.ι Q).contract, Algebra.smul_def, ← map_mul, h]
      contract_mid := fun x y z => by
        change ((d : R) • (even.ι Q).bilin (U x) (U y)) *
          ((d : R) • (even.ι Q).bilin (U y) (U z)) = _
        rw [smul_mul_assoc, mul_smul_comm, (even.ι Q).contract_mid,
          smul_smul (d : R) (Q (U y)), h]
        exact smul_comm (d : R) (q y) _ }

private theorem evenSimilarity_pair (x y : V) :
    evenSimilarity U d h ((even.ι q).bilin x y) =
      (d : R) • (even.ι Q).bilin (U x) (U y) := by
  apply even.lift_ι

include h in
private theorem inverseSimilarity (x : W) : (↑d⁻¹ : R) * q (U.symm x) = Q x := by
  rw [← h, U.apply_symm_apply, ← mul_assoc, Units.inv_mul, one_mul]

private def evenSimilarityEquiv : even q ≃ₐ[R] even Q := by
  let f := evenSimilarity U d h
  let g := evenSimilarity U.symm d⁻¹ (inverseSimilarity U d h)
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply even.algHom_ext
    apply EvenHom.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change f (g ((even.ι Q).bilin x y)) = (even.ι Q).bilin x y
    simp only [f, g, evenSimilarity_pair, map_smul, LinearEquiv.apply_symm_apply,
      smul_smul, Units.inv_mul, one_smul]
  · apply even.algHom_ext
    apply EvenHom.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change g (f ((even.ι q).bilin x y)) = (even.ι q).bilin x y
    simp only [f, g, evenSimilarity_pair, map_smul, LinearEquiv.symm_apply_apply,
      smul_smul, Units.mul_inv, one_smul]


private def reverseEven (x : even q) : even q :=
  ⟨reverse (x : CliffordAlgebra q), (reverse_mem_evenOdd_iff q).2 x.property⟩

private theorem reverseEven_add (a b : even q) :
    reverseEven (a + b) = reverseEven a + reverseEven b :=
  Subtype.ext (map_add reverse _ _)

private theorem reverseEven_mul (a b : even q) :
    reverseEven (a * b) = reverseEven b * reverseEven a :=
  Subtype.ext (reverse.map_mul _ _)

private theorem reverseEven_scalar (r : R) :
    reverseEven (algebraMap R (even q) r) = algebraMap R (even q) r :=
  Subtype.ext (reverse.commutes r)

private theorem reverseEven_pair (x y : V) :
    reverseEven ((even.ι q).bilin x y) = (even.ι q).bilin y x := by
  apply Subtype.ext
  change reverse (CliffordAlgebra.ι q x * CliffordAlgebra.ι q y) = _
  simp [reverse.map_mul, even.ι]

private theorem reverseEven_smul (r : R) (a : even q) :
    reverseEven (r • a) = r • reverseEven a :=
  Subtype.ext (map_smul reverse r a.val)

private theorem evenSimilarity_reverse (x : even q) :
    evenSimilarity U d h (reverseEven x) = reverseEven (evenSimilarity U d h x) := by
  obtain ⟨x, hx⟩ := x
  induction x, hx using even_induction q with
  | algebraMap r =>
    change evenSimilarity U d h (reverseEven (algebraMap R (even q) r)) =
      reverseEven (evenSimilarity U d h (algebraMap R (even q) r))
    rw [reverseEven_scalar, AlgHom.commutes, reverseEven_scalar]
  | add x y hx hy ihx ihy =>
    let a : even q := ⟨x, hx⟩
    let b : even q := ⟨y, hy⟩
    change evenSimilarity U d h (reverseEven (a + b)) =
      reverseEven (evenSimilarity U d h (a + b))
    rw [reverseEven_add, map_add, map_add, reverseEven_add, ihx, ihy]
  | ι_mul_ι_mul x y z hz ih =>
    let a : even q := (even.ι q).bilin x y
    let b : even q := ⟨z, hz⟩
    change evenSimilarity U d h (reverseEven (a * b)) =
      reverseEven (evenSimilarity U d h (a * b))
    rw [reverseEven_mul, map_mul, map_mul, reverseEven_mul, ih]
    congr 1
    change evenSimilarity U d h (reverseEven ((even.ι q).bilin x y)) =
      reverseEven (evenSimilarity U d h ((even.ι q).bilin x y))
    rw [reverseEven_pair, evenSimilarity_pair, evenSimilarity_pair, reverseEven_smul, reverseEven_pair]

private def similarityMatrix {A : Type*} [Zero A] [SMul R A] (x : A) :
    Matrix (Fin 2) (Fin 2) A :=
  !![0, (d : R) • x; x, 0]

/-- Represent a Clifford vector by an off-diagonal matrix. The two products
on its diagonal both have the required quadratic value. -/
private def similarityBlockMap : CliffordAlgebra q →ₐ[R] Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) :=
  CliffordAlgebra.lift q
    ⟨{ toFun := fun x => similarityMatrix d (CliffordAlgebra.ι Q (U x))
       map_add' := fun x y => by
         ext i j
         fin_cases i <;> fin_cases j <;> simp [similarityMatrix, smul_add]
       map_smul' := fun r x => by
         ext i j
         fin_cases i <;> fin_cases j <;>
           simp [similarityMatrix, smul_comm (d : R) r] },
      fun x => by
        have hx : (d : R) • algebraMap R (CliffordAlgebra Q) (Q (U x)) =
            algebraMap R (CliffordAlgebra Q) (q x) := by
          rw [Algebra.smul_def, ← map_mul, h]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [similarityMatrix, Matrix.mul_apply, Fin.sum_univ_two, hx,
            Matrix.algebraMap_matrix_apply]⟩

private theorem similarityBlockMap_vector (x : V) :
    similarityBlockMap U d h (CliffordAlgebra.ι q x) = similarityMatrix d (CliffordAlgebra.ι Q (U x)) :=
  CliffordAlgebra.lift_ι_apply _ _ _

private theorem similarityBlockMap_even (x : even q) :
    similarityBlockMap U d h (x : CliffordAlgebra q) =
      Matrix.scalar (Fin 2) (evenSimilarity U d h x : CliffordAlgebra Q) := by
  obtain ⟨x, hx⟩ := x
  induction x, hx using even_induction q with
  | algebraMap r =>
    change similarityBlockMap U d h (algebraMap R (CliffordAlgebra q) r) =
      Matrix.scalar (Fin 2) (evenSimilarity U d h (algebraMap R (even q) r) : CliffordAlgebra Q)
    rw [AlgHom.commutes, AlgHom.commutes]
    rfl
  | add x y hx hy ihx ihy =>
    let a : even q := ⟨x, hx⟩
    let b : even q := ⟨y, hy⟩
    change similarityBlockMap U d h (x + y) =
      Matrix.scalar (Fin 2) (evenSimilarity U d h (a + b) : CliffordAlgebra Q)
    rw [map_add, ihx, ihy, map_add]
    exact ((Matrix.scalar (Fin 2)).map_add _ _).symm
  | ι_mul_ι_mul x y z hz ih =>
    let a : even q := (even.ι q).bilin x y
    let b : even q := ⟨z, hz⟩
    change similarityBlockMap U d h (CliffordAlgebra.ι q x * CliffordAlgebra.ι q y * z) =
      Matrix.scalar (Fin 2) (evenSimilarity U d h (a * b) : CliffordAlgebra Q)
    rw [map_mul, map_mul, similarityBlockMap_vector, similarityBlockMap_vector, ih, map_mul]
    have ha : similarityMatrix d (CliffordAlgebra.ι Q (U x)) * similarityMatrix d (CliffordAlgebra.ι Q (U y)) =
        Matrix.scalar (Fin 2) (evenSimilarity U d h a : CliffordAlgebra Q) := by
      change _ = Matrix.scalar (Fin 2) (evenSimilarity U d h ((even.ι q).bilin x y) : CliffordAlgebra Q)
      rw [evenSimilarity_pair]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [similarityMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, even.ι]
    rw [ha]
    exact ((Matrix.scalar (Fin 2)).map_mul _ _).symm

/-- The inverse multiplier correction on even elements transports their
intertwining equation with the two Clifford vectors. -/
private theorem evenSimilarity_intertwines (a : even q) (x y : V)
    (ha : (a : CliffordAlgebra q) * CliffordAlgebra.ι q x = CliffordAlgebra.ι q y * (a : CliffordAlgebra q)) :
    (evenSimilarity U d h a : CliffordAlgebra Q) * CliffordAlgebra.ι Q (U x) =
      CliffordAlgebra.ι Q (U y) * (evenSimilarity U d h a : CliffordAlgebra Q) := by
  have hm := congrArg (similarityBlockMap U d h) ha
  rw [map_mul, map_mul, similarityBlockMap_vector, similarityBlockMap_vector,
    similarityBlockMap_even] at hm
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, similarityMatrix] using
    congrArg (fun m : Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) => m 1 0) hm

end CliffordSimilarity


section EvenSpinPoints

open CliffordAlgebra
open Albert.CliffordSpecification (coefficientForm)
open Albert.SpinSpecification (vectors reversion spinUnits IsVectorAction conjugate)
open Albert.SpinFunctor (Spin)
open private cliffordEquiv_vector cliffordEquiv_even reversion_even reverse_eq_inverse
  conjugate_inverse from LinearAlgebraicGroups.Albert.SpinFunctor
open private baseChangeEquiv_reverse from LinearAlgebraicGroups.Albert.CliffordModel

variable {k V J S : Type*} [CommRing k] [AddCommGroup V] [Module k V]
  [CommRing S] [Algebra k S] [LinearOrder J]
  (q : QuadraticForm k V) (b : Module.Basis J k V)

private def spinToEvenUnit (a : Spin q S b) : (even (coefficientForm S q b))ˣ := by
  let E := Albert.CliffordModel.baseChangeEquiv S q b
  let z := Units.map E.toMonoidHom a.val
  have h := a.property
  change a.val ∈ spinUnits q S at h
  have he : z.val ∈ even (coefficientForm S q b) :=
    (cliffordEquiv_even q S b a.val.val).2 h.1
  have hi : z.inv ∈ even (coefficientForm S q b) := by
    apply (cliffordEquiv_even q S b ↑a.val⁻¹).2
    rw [← reverse_eq_inverse q S h.2.1]
    exact reversion_even q S b h.1
  exact ⟨⟨z.val, he⟩, ⟨z.inv, hi⟩, Subtype.ext z.val_inv, Subtype.ext z.inv_val⟩

private def spinToEven : Spin q S b →* (even (coefficientForm S q b))ˣ where
  toFun := spinToEvenUnit q b
  map_one' := Units.ext (Subtype.ext (map_one (Albert.CliffordModel.baseChangeEquiv S q b)))
  map_mul' a c := Units.ext (Subtype.ext
    (map_mul (Albert.CliffordModel.baseChangeEquiv S q b) a.val.val c.val.val))

private theorem spinToEven_norm (a : Spin q S b) :
    reverseEven (spinToEven q b a).val * (spinToEven q b a).val = 1 := by
  let E := Albert.CliffordModel.baseChangeEquiv S q b
  have h := a.property
  change a.val ∈ spinUnits q S at h
  apply Subtype.ext
  change reverse (E a.val.val) * E a.val.val = 1
  rw [← show E (reversion q S a.val.val) = _ from baseChangeEquiv_reverse S q b _,
    ← map_mul, h.2.1, map_one]

private theorem spinToEven_intertwines (a : Spin q S b)
    (g : (S ⊗[k] V) ≃ₗ[S] (S ⊗[k] V)) (hg : IsVectorAction q S a.val g)
    (x : S ⊗[k] V) :
    (spinToEven q b a).val.val * CliffordAlgebra.ι (coefficientForm S q b) x =
      CliffordAlgebra.ι (coefficientForm S q b) (g x) * (spinToEven q b a).val.val := by
  have hx := hg x
  unfold conjugate at hx
  have eq := congrArg (fun z : ScalarClifford q S => z * a.val.val) hx
  change vectors q S (g x) * a.val.val =
    (a.val.val * vectors q S x * a.val.inv) * a.val.val at eq
  rw [mul_assoc _ _ a.val.val, a.val.inv_val, mul_one] at eq
  let E := Albert.CliffordModel.baseChangeEquiv S q b
  have hE := congrArg E eq.symm
  rw [map_mul, map_mul] at hE
  rw [show E (vectors q S x) = _ from cliffordEquiv_vector q S b x,
    show E (vectors q S (g x)) = _ from cliffordEquiv_vector q S b (g x)] at hE
  exact hE

private def evenToClifford : (even (coefficientForm S q b))ˣ →* (ScalarClifford q S)ˣ :=
  Units.map (((Albert.CliffordModel.baseChangeEquiv S q b).symm.toAlgHom).comp
    (even (coefficientForm S q b)).val).toMonoidHom

private theorem evenToClifford_spinToEven (a : Spin q S b) :
    evenToClifford q b (spinToEven q b a) = a.val := by
  apply Units.ext
  exact (Albert.CliffordModel.baseChangeEquiv S q b).symm_apply_apply a.val.val

private theorem evenToClifford_injective :
    Function.Injective (evenToClifford q b (S := S)) := by
  intro a c hac
  apply Units.ext
  apply Subtype.ext
  exact (Albert.CliffordModel.baseChangeEquiv S q b).symm.injective (congrArg Units.val hac)

private theorem evenToClifford_vector (a : (even (coefficientForm S q b))ˣ)
    (g : (S ⊗[k] V) ≃ₗ[S] (S ⊗[k] V))
    (hg : ∀ x, a.val.val * CliffordAlgebra.ι (coefficientForm S q b) x =
      CliffordAlgebra.ι (coefficientForm S q b) (g x) * a.val.val) :
    IsVectorAction q S (evenToClifford q b a) g := by
  intro x
  let E := Albert.CliffordModel.baseChangeEquiv S q b
  apply E.injective
  unfold conjugate
  rw [map_mul, map_mul]
  rw [show E (vectors q S (g x)) = _ from cliffordEquiv_vector q S b (g x),
    show E (vectors q S x) = _ from cliffordEquiv_vector q S b x]
  change CliffordAlgebra.ι _ (g x) =
    E (E.symm a.val.val) * CliffordAlgebra.ι _ x * E (E.symm a.inv.val)
  rw [E.apply_symm_apply, E.apply_symm_apply, hg, mul_assoc]
  have ha := congrArg Subtype.val a.val_inv
  change a.val.val * a.inv.val = 1 at ha
  rw [ha, mul_one]

private theorem evenToClifford_mem (a : (even (coefficientForm S q b))ˣ)
    (ha : reverseEven a.val * a.val = 1)
    (g : (S ⊗[k] V) ≃ₗ[S] (S ⊗[k] V))
    (hg : IsVectorAction q S (evenToClifford q b a) g) :
    evenToClifford q b a ∈ spinUnits q S := by
  let E := Albert.CliffordModel.baseChangeEquiv S q b
  let A := evenToClifford q b a
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (cliffordEquiv_even q S b A.val).1
    change E (E.symm a.val.val) ∈ _
    rw [E.apply_symm_apply]
    exact a.val.property
  · change reversion q S A.val * A.val = 1
    apply E.injective
    rw [map_mul, map_one, baseChangeEquiv_reverse]
    change reverse (E (E.symm a.val.val)) * E (E.symm a.val.val) = 1
    rw [E.apply_symm_apply]
    exact congrArg Subtype.val ha
  · rintro _ ⟨x, rfl⟩
    exact ⟨g x, hg x⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨g.symm x, ?_⟩
    have h := hg (g.symm x)
    rw [g.apply_symm_apply] at h
    rw [h]
    exact (conjugate_inverse q S A⁻¹ _).symm

end EvenSpinPoints

section SimilarityPoints

open CliffordAlgebra
open Albert.CliffordSpecification (coefficientForm)
open Albert.SpinSpecification (IsVectorAction ScalarClifford vectors)
open Albert.SpinFunctor (Spin vectorAction vectorAction_characterization)
open private cliffordEquiv_vector from LinearAlgebraicGroups.Albert.SpinFunctor

variable {k l S V W J L : Type*} [CommRing k] [CommRing l] [CommRing S]
  [Algebra k S] [Algebra l S] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module l W]
  [LinearOrder J] [LinearOrder L]
  (q : QuadraticForm k V) (b : Module.Basis J k V)
  (Q : QuadraticForm l W) (B : Module.Basis L l W)
  (U : S ⊗[k] V ≃ₗ[S] S ⊗[l] W) (d : Sˣ)
  (h : ∀ x, d.val * coefficientForm S Q B (U x) = coefficientForm S q b x)

private def similarityOnUnits :
    Spin q S b →* (ScalarClifford Q S)ˣ :=
  (evenToClifford Q B).comp
    ((Units.map (evenSimilarityEquiv U d h).toMonoidHom).comp (spinToEven q b))

private theorem similarityOnUnits_vector (a : Spin q S b)
    (g : (S ⊗[k] V) ≃ₗ[S] (S ⊗[k] V)) (hg : IsVectorAction q S a.val g) :
    IsVectorAction Q S (similarityOnUnits q b Q B U d h a)
      (U.symm.trans (g.trans U)) := by
  apply evenToClifford_vector
  intro x
  obtain ⟨y, rfl⟩ := U.surjective x
  change (evenSimilarity U d h (spinToEven q b a).val : CliffordAlgebra (coefficientForm S Q B)) *
      CliffordAlgebra.ι _ (U y) = CliffordAlgebra.ι _ (U (g (U.symm (U y)))) *
      (evenSimilarity U d h (spinToEven q b a).val : CliffordAlgebra (coefficientForm S Q B))
  rw [U.symm_apply_apply]
  exact evenSimilarity_intertwines U d h _ y (g y) (spinToEven_intertwines q b a g hg y)

private def similarityOnSpin : Spin q S b →* Spin Q S B where
  toFun a := ⟨similarityOnUnits q b Q B U d h a, by
    let f := evenSimilarityEquiv U d h
    let z := spinToEven q b a
    apply evenToClifford_mem Q B (Units.map f.toMonoidHom z)
    · change reverseEven (f z.val) * f z.val = 1
      change reverseEven (evenSimilarity U d h z.val) * evenSimilarity U d h z.val = 1
      rw [← evenSimilarity_reverse, ← map_mul, spinToEven_norm, map_one]
    · exact similarityOnUnits_vector q b Q B U d h a (vectorAction q S b a)
        (vectorAction_characterization q S b a)⟩
  map_one' := Subtype.ext (map_one (similarityOnUnits q b Q B U d h))
  map_mul' a a' := Subtype.ext (map_mul (similarityOnUnits q b Q B U d h) a a')

private theorem spinToEven_evenToClifford (a : (even (coefficientForm S q b))ˣ)
    (ha : evenToClifford q b a ∈ Albert.SpinSpecification.spinUnits q S) :
    spinToEven q b (⟨evenToClifford q b a, ha⟩ : Spin q S b) = a := by
  apply evenToClifford_injective q b
  exact evenToClifford_spinToEven q b _

private theorem similarityOnSpin_leftInverse :
    Function.LeftInverse (similarityOnSpin Q B q b U.symm d⁻¹ (inverseSimilarity U d h))
      (similarityOnSpin q b Q B U d h) := by
  intro a
  apply Subtype.ext
  let f := evenSimilarityEquiv U d h
  let z := spinToEven q b a
  have hz : spinToEven Q B (similarityOnSpin q b Q B U d h a) = Units.map f.toMonoidHom z :=
    spinToEven_evenToClifford Q B _ (similarityOnSpin q b Q B U d h a).property
  change evenToClifford q b
    (Units.map f.symm.toMonoidHom (spinToEven Q B (similarityOnSpin q b Q B U d h a))) = a.val
  rw [hz, show Units.map f.symm.toMonoidHom (Units.map f.toMonoidHom z) = z from
    (Units.mapEquiv f.toMulEquiv).symm_apply_apply z]
  exact evenToClifford_spinToEven q b a

/-- Multiplier-corrected transport of spin points over a commutative algebra. -/
private def similaritySpinEquiv : Spin q S b ≃* Spin Q S B :=
  MulEquiv.ofBijective (similarityOnSpin q b Q B U d h)
    ⟨(similarityOnSpin_leftInverse q b Q B U d h).injective,
     (similarityOnSpin_leftInverse Q B q b U.symm d⁻¹ (inverseSimilarity U d h)).surjective⟩

private def scalarSimilarityBlock :
    ScalarClifford q S →ₐ[S] Matrix (Fin 2) (Fin 2) (ScalarClifford Q S) :=
  (Albert.CliffordModel.baseChangeEquiv S Q B).symm.toAlgHom.mapMatrix.comp
    ((similarityBlockMap U d h).comp (Albert.CliffordModel.baseChangeEquiv S q b).toAlgHom)

private theorem scalarSimilarityBlock_vector (x : S ⊗[k] V) :
    scalarSimilarityBlock q b Q B U d h (vectors q S x) =
      similarityMatrix d (vectors Q S (U x)) := by
  change (similarityBlockMap U d h (Albert.CliffordModel.baseChangeEquiv S q b
    (vectors q S x))).map (Albert.CliffordModel.baseChangeEquiv S Q B).symm = _
  rw [show Albert.CliffordModel.baseChangeEquiv S q b (vectors q S x) =
    CliffordAlgebra.ι (coefficientForm S q b) x from cliffordEquiv_vector q S b x,
    similarityBlockMap_vector]
  have hv : (Albert.CliffordModel.baseChangeEquiv S Q B).symm
      (CliffordAlgebra.ι (coefficientForm S Q B) (U x)) = vectors Q S (U x) :=
    (Albert.CliffordModel.baseChangeEquiv S Q B).symm_apply_eq.mpr
      (cliffordEquiv_vector Q S B (U x)).symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [similarityMatrix, hv]

private theorem scalarSimilarityBlock_spin (a : Spin q S b) (i : Fin 2) :
    scalarSimilarityBlock q b Q B U d h a.val.val i i =
      (similarityOnUnits q b Q B U d h a).val := by
  change ((similarityBlockMap U d h (Albert.CliffordModel.baseChangeEquiv S q b a.val.val)).map
    (Albert.CliffordModel.baseChangeEquiv S Q B).symm) i i = _
  let z := (spinToEven q b a).val
  change ((similarityBlockMap U d h z.val).map
    (Albert.CliffordModel.baseChangeEquiv S Q B).symm) i i = _
  rw [similarityBlockMap_even]
  change (Albert.CliffordModel.baseChangeEquiv S Q B).symm
    (Matrix.scalar (Fin 2) (evenSimilarity U d h z : CliffordAlgebra _) i i) = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
  rfl

end SimilarityPoints


section SimilarityNaturality

open CliffordAlgebra
open Albert.CliffordSpecification (coefficientForm)
open Albert.SpinSpecification (ScalarClifford vectors coefficientMap)
open Albert.SpinFunctor (Spin)
open private changeModule changeCoefficients_vector
  from LinearAlgebraicGroups.Albert.SpinFunctor

variable {k l S T V W J L : Type*} [CommRing k] [CommRing l] [CommRing S] [CommRing T]
  [Algebra k S] [Algebra l S] [Algebra k T] [Algebra l T]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module l W] [LinearOrder J] [LinearOrder L]
  (q : QuadraticForm k V) (b : Module.Basis J k V)
  (Q : QuadraticForm l W) (B : Module.Basis L l W)
  {U : S ⊗[k] V ≃ₗ[S] S ⊗[l] W} {d : Sˣ}
  {U' : T ⊗[k] V ≃ₗ[T] T ⊗[l] W} {d' : Tˣ}
  (h : ∀ x, d.val * coefficientForm S Q B (U x) = coefficientForm S q b x)
  (h' : ∀ x, d'.val * coefficientForm T Q B (U' x) = coefficientForm T q b x)
  (f : S →ₐ[k] T) (g : S →ₐ[l] T) (hfg : ∀ r, f r = g r)
  (hd : g d.val = d'.val)
  (hU : ∀ x, U' (changeModule f x) = changeModule g (U x))

private theorem cliffordCoefficient_scalar {k' S' T' V' : Type*}
    [CommRing k'] [CommRing S'] [CommRing T'] [Algebra k' S'] [Algebra k' T']
    [AddCommGroup V'] [Module k' V'] (q' : QuadraticForm k' V')
    (f' : S' →ₐ[k'] T') (r : S') :
    coefficientMap q' S' f' (algebraMap S' (ScalarClifford q' S') r) =
      algebraMap T' (ScalarClifford q' T') (f' r) := by
  change coefficientMap q' S' f' (r ⊗ₜ[k'] (1 : CliffordAlgebra q')) =
    f' r ⊗ₜ[k'] (1 : CliffordAlgebra q')
  rfl

include hfg hd hU in
private theorem scalarSimilarityBlock_natural (z : ScalarClifford q S) :
    scalarSimilarityBlock q b Q B U' d' h' (coefficientMap q S f z) =
      (scalarSimilarityBlock q b Q B U d h z).map (coefficientMap Q S g) := by
  let A := scalarSimilarityBlock q b Q B U' d' h'
  let E := scalarSimilarityBlock q b Q B U d h
  let P := A.toRingHom.comp (coefficientMap q S f).toRingHom
  let N := (coefficientMap Q S g).toRingHom.mapMatrix.comp E.toRingHom
  have hs (r : S) : P (algebraMap S (ScalarClifford q S) r) =
      N (algebraMap S (ScalarClifford q S) r) := by
    change A (coefficientMap q S f (algebraMap S (ScalarClifford q S) r)) =
      (E (algebraMap S (ScalarClifford q S) r)).map (coefficientMap Q S g)
    rw [cliffordCoefficient_scalar, A.commutes, E.commutes]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.algebraMap_matrix_apply, coefficientMap, hfg]
    · simp [Matrix.algebraMap_matrix_apply, hij]
  have hv (x : S ⊗[k] V) : P (vectors q S x) = N (vectors q S x) := by
    change A (coefficientMap q S f (vectors q S x)) =
      (E (vectors q S x)).map (coefficientMap Q S g)
    change A (Albert.SpinFunctor.changeCoefficients q f (vectors q S x)) = _
    rw [changeCoefficients_vector, scalarSimilarityBlock_vector, scalarSimilarityBlock_vector, hU]
    have hg (y : S ⊗[l] W) :
        coefficientMap Q S g (vectors Q S y) = vectors Q T (changeModule g y) :=
      changeCoefficients_vector Q g y
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [similarityMatrix, Algebra.smul_def, hg]
    change (d'.val ⊗ₜ[l] (1 : CliffordAlgebra Q)) * _ =
      (g d.val ⊗ₜ[l] (1 : CliffordAlgebra Q)) * _
    rw [hd]
  have hPN : P = N := by
    apply Algebra.TensorProduct.ringHom_ext
    · exact RingHom.ext hs
    · apply RingHom.ext
      intro a
      change P (1 ⊗ₜ[k] a) = N (1 ⊗ₜ[k] a)
      induction a using CliffordAlgebra.induction with
      | algebraMap r =>
        have hm : ((1 : S) ⊗ₜ[k] algebraMap k (CliffordAlgebra q) r) =
            algebraMap S (ScalarClifford q S) (algebraMap k S r) := by
          simp [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
            Algebra.TensorProduct.one_def]
        rw [hm]
        exact hs _
      | «ι» x => exact hv (1 ⊗ₜ[k] x)
      | mul a c ha hc =>
        have hmul : ((1 : S) ⊗ₜ[k] (a * c)) = (1 ⊗ₜ[k] a) * (1 ⊗ₜ[k] c) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rw [hmul, map_mul, map_mul, ha, hc]
      | add a c ha hc => rw [TensorProduct.tmul_add, map_add, map_add, ha, hc]
  exact DFunLike.congr_fun hPN z

include hfg hd hU in
private theorem similarityOnUnits_natural (a : Spin q S b) :
    similarityOnUnits q b Q B U' d' h' (Albert.SpinFunctor.map q b f a) =
      Units.map (coefficientMap Q S g).toMonoidHom (similarityOnUnits q b Q B U d h a) := by
  apply Units.ext
  have hm := congrArg (fun X : Matrix (Fin 2) (Fin 2) (ScalarClifford Q T) => X 0 0)
    (scalarSimilarityBlock_natural q b Q B h h' f g hfg hd hU a.val.val)
  change scalarSimilarityBlock q b Q B U' d' h'
      (Albert.SpinFunctor.map q b f a).val.val 0 0 =
    coefficientMap Q S g (scalarSimilarityBlock q b Q B U d h a.val.val 0 0) at hm
  rw [scalarSimilarityBlock_spin, scalarSimilarityBlock_spin] at hm
  exact hm

end SimilarityNaturality


section VectorMatrices

open Specs.Arithmetic.NontrialitarianSpinModels (matrixColumnEquiv)
open Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open Albert.SpinSpecification (IsVectorAction)
open private changeModule changeModule_coord from LinearAlgebraicGroups.Albert.SpinFunctor

private theorem columnCoordinates_map {k : Type*} [CommRing k] {R S : Type*}
    [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    {J : Type*} [Fintype J] (f : R →ₐ[k] S) (x : R ⊗[k] (J → k)) :
    columnCoordinates (changeModule f x) = f ∘ columnCoordinates x := by
  funext j
  exact changeModule_coord (Pi.basisFun k J) f x j

private theorem vectorMatrix_iff_columns {k R J : Type*} [CommRing k] [CommRing R] [Algebra k R]
    [Fintype J] [DecidableEq J]
    (g : (R ⊗[k] (J → k)) ≃ₗ[R] (R ⊗[k] (J → k))) (A : Matrix J J R) :
    LinearMap.toMatrix ((Pi.basisFun k J).baseChange R) ((Pi.basisFun k J).baseChange R)
      g.toLinearMap = A ↔ ∀ x, columnCoordinates (g x) = A *ᵥ columnCoordinates x := by
  let b := (Pi.basisFun k J).baseChange R
  have hf (x : R ⊗[k] (J → k)) :
      columnCoordinates (g x) = (LinearMap.toMatrix b b g.toLinearMap) *ᵥ columnCoordinates x :=
    (LinearMap.toMatrix_mulVec_repr b b g.toLinearMap x).symm
  constructor
  · intro h x
    exact h ▸ hf x
  · intro h
    apply (Matrix.toLin b b).injective
    rw [Matrix.toLin_toMatrix]
    apply LinearMap.ext
    intro x
    apply b.repr.injective
    exact DFunLike.ext _ _ (fun j => (congrFun (h x) j).trans
      (congrFun (Matrix.repr_toLin b b A x) j).symm)

private def pairVector (M : SpinModel G D) (R : TestAlgebra F) (p : Points G.val.X R) :
    (R ⊗[F] (Fin n → F)) ≃ₗ[R] (R ⊗[F] (Fin n → F)) :=
  let z := Units.map (testMatrix e R).toMonoidHom
    (M.fullPoints R (p ≫ (M.projection ≫ M.inclusion).hom.hom))
  columnCoordinates.trans <|
    (Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv R (Fin n → R)) z).trans
    columnCoordinates.symm

private theorem pairVector_column (M : SpinModel G D) (R : TestAlgebra F) (p : Points G.val.X R)
    (x : R ⊗[F] (Fin n → F)) :
    columnCoordinates (pairVector e M R p x) =
      testMatrix e R (M.fullPoints R (p ≫ (M.projection ≫ M.inclusion).hom.hom)).val *ᵥ
        columnCoordinates x := by
  unfold pairVector
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

private theorem pairVector_natural (M : SpinModel G D) {R S : TestAlgebra F}
    (f : R ⟶ S) (p : Points G.val.X R) (x : R ⊗[F] (Fin n → F)) :
    pairVector e M S (mapPoints f p) (changeModule f.hom x) =
      changeModule f.hom (pairVector e M R p x) := by
  apply (columnCoordinates (k := F) (S := S)).injective
  rw [pairVector_column, columnCoordinates_map, columnCoordinates_map, pairVector_column]
  rw [Category.assoc, M.fullNatural, Units.coe_map]
  let z := (M.fullPoints R (p ≫ (M.projection ≫ M.inclusion).hom.hom)).val
  change testMatrix e S (tensorMap f z) *ᵥ _ = f.hom ∘ (testMatrix e R z *ᵥ _)
  rw [testMatrix_natural]
  funext j
  exact (f.hom.toRingHom.map_mulVec _ _ j).symm

private theorem testVectorSimilarity_column (P : RecoveredForm (D := D) e)
    (U : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) (S : TestAlgebra K)
    (x : ((restrictTestAlgebra F K).obj S) ⊗[F] (Fin n → F)) :
    columnCoordinates (testVectorSimilarity e P U S x) =
      U.val.map (algebraMap K S) *ᵥ
        (columnCoordinates (S := (restrictTestAlgebra F K).obj S) x ∘ (recoveredIndexEquiv e P).symm) := by
  unfold testVectorSimilarity
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, columnEquiv_apply]
  rfl

private theorem testVectorSimilarity_natural (P : RecoveredForm (D := D) e)
    (U : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) {S T : TestAlgebra K} (f : S ⟶ T)
    (x : ((restrictTestAlgebra F K).obj S) ⊗[F] (Fin n → F)) :
    testVectorSimilarity e P U T (changeModule ((restrictTestAlgebra F K).map f).hom x) =
      changeModule f.hom (testVectorSimilarity e P U S x) := by
  apply (columnCoordinates (k := K) (S := T)).injective
  rw [testVectorSimilarity_column, columnCoordinates_map, columnCoordinates_map,
    testVectorSimilarity_column]
  have hm : (U.val.map (algebraMap K S)).map f.hom.toRingHom = U.val.map (algebraMap K T) := by
    ext i j
    exact f.hom.commutes _
  funext j
  let v := columnCoordinates (S := (restrictTestAlgebra F K).obj S) x ∘
    (recoveredIndexEquiv e P).symm
  change (U.val.map (algebraMap K T) *ᵥ (f.hom ∘ v)) j =
    f.hom.toRingHom ((U.val.map (algebraMap K S) *ᵥ v) j)
  rw [f.hom.toRingHom.map_mulVec, hm]
  rfl

set_option maxRecDepth 1800 in
private theorem testVectorSimilarity_intertwines (M : SpinModel G D) (P : RecoveredForm (D := D) e)
    (U : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) (S : TestAlgebra K)
    (p : Points G.val.X ((restrictTestAlgebra F K).obj S))
    (g : (S ⊗[K] (I ⊕ I → K)) ≃ₗ[S] (S ⊗[K] (I ⊕ I → K)))
    (hg : let b := (Pi.basisFun K (I ⊕ I)).baseChange S
      let R := (restrictTestAlgebra F K).obj S
      LinearMap.toMatrix b b g.toLinearMap = U.val.map (algebraMap K S) *
        Matrix.reindex (recoveredIndexEquiv e P) (recoveredIndexEquiv e P)
          (testMatrix e R (M.fullPoints R
            (p ≫ (M.projection ≫ M.inclusion).hom.hom)).val) * U.inv.map (algebraMap K S)) :
    (testVectorSimilarity e P U S).trans (g.trans (testVectorSimilarity e P U S).symm) =
      pairVector e M ((restrictTestAlgebra F K).obj S) p := by
  let R := (restrictTestAlgebra F K).obj S
  let i := recoveredIndexEquiv e P
  let V := testVectorSimilarity e P U S
  let X := testMatrix e R (M.fullPoints R (p ≫ (M.projection ≫ M.inclusion).hom.hom)).val
  let A := Units.map (algebraMap K S).mapMatrix.toMonoidHom U
  apply LinearEquiv.ext
  intro x
  apply V.injective
  change V (V.symm (g (V x))) = V (pairVector e M R p x)
  rw [V.apply_symm_apply]
  apply (columnCoordinates (k := K) (S := S)).injective
  have hc := (vectorMatrix_iff_columns g (A.val * Matrix.reindex i i X * A.inv)).1 hg (V x)
  rw [hc]
  change _ = columnCoordinates (testVectorSimilarity e P U S (pairVector e M R p x))
  have hcol := testVectorSimilarity_column e P U S (pairVector e M R p x)
  have hpair := pairVector_column e M R p x
  change columnCoordinates (V (pairVector e M R p x)) =
    A.val *ᵥ (columnCoordinates (S := R) (pairVector e M R p x) ∘ i.symm) at hcol
  rw [hpair] at hcol
  rw [hcol]
  have hx : columnCoordinates (V x) = A.val *ᵥ (columnCoordinates (S := R) x ∘ i.symm) :=
    testVectorSimilarity_column e P U S x
  rw [hx, Matrix.mulVec_mulVec, Matrix.mul_assoc (_ * _) A.inv A.val, A.inv_val, mul_one,
    ← Matrix.mulVec_mulVec, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  congr 1
  funext j
  simp [Function.comp_def, X]

end VectorMatrices

section SplitRepresentation

open Albert.SpinFunctor (Spin)
open Albert.SpinSpecification (spinUnits IsVectorAction)
open Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open private changeModule from LinearAlgebraicGroups.Albert.SpinFunctor

private def representedSpinEquiv {k S V J H : Type*} [CommRing k] [CommRing S]
    [Algebra k S] [AddCommGroup V] [Module k V] [LinearOrder J] [Group H]
    (q : QuadraticForm k V) (b : Module.Basis J k V) (a : H →* (ScalarClifford q S)ˣ)
    (ha : Function.Injective a ∧ Set.range a = spinUnits q S) : H ≃* Spin q S b := by
  let f : H →* Spin q S b := {
    toFun := fun p => ⟨a p, show a p ∈ spinUnits q S from ha.2 ▸ Set.mem_range_self p⟩
    map_one' := Subtype.ext (map_one a)
    map_mul' := fun p r => Subtype.ext (map_mul a p r) }
  apply MulEquiv.ofBijective f
  refine ⟨fun x y h => ha.1 (congrArg Subtype.val h), ?_⟩
  intro z
  have hz : z.val ∈ Set.range a := ha.2.symm ▸ (show z.val ∈ spinUnits q S from z.property)
  obtain ⟨p, hp⟩ := hz
  exact ⟨p, Subtype.ext hp⟩

/-- A comparison on the splitting field's test algebras, with the vector
action in the original matrix coordinates. -/
private structure SplitRepresentation (M : SpinModel G D) (P : RecoveredForm (D := D) e) where
  points : ∀ S : TestAlgebra K, Points G.val.X ((restrictTestAlgebra F K).obj S) ≃*
    Spin P.form ((restrictTestAlgebra F K).obj S) (Pi.basisFun F (Fin n))
  natural : ∀ {S T : TestAlgebra K} (f : S ⟶ T)
    (p : Points G.val.X ((restrictTestAlgebra F K).obj S)),
    points T (mapPoints ((restrictTestAlgebra F K).map f) p) =
      Albert.SpinFunctor.map P.form (Pi.basisFun F (Fin n))
        ((restrictTestAlgebra F K).map f).hom (points S p)
  vector : ∀ (S : TestAlgebra K) (p : Points G.val.X ((restrictTestAlgebra F K).obj S)),
    IsVectorAction P.form ((restrictTestAlgebra F K).obj S) (points S p).val
      (pairVector e M ((restrictTestAlgebra F K).obj S) p)

set_option maxHeartbeats 600000 in
private theorem splitRepresentation_nonempty (M : SpinModel G D) (P : RecoveredForm (D := D) e) :
    Nonempty (SplitRepresentation e M P) := by
  let : LinearOrder (I ⊕ I) := LinearOrder.lift' (Fintype.equivFin (I ⊕ I))
    (Fintype.equivFin (I ⊕ I)).injective
  obtain ⟨U, d, hU, hq⟩ := recoveredSplit_similarity e P
  let q₀ := hyperbolicForm I K
  let b₀ := Pi.basisFun K (I ⊕ I)
  let b := Pi.basisFun F (Fin n)
  let V (S : TestAlgebra K) := testVectorSimilarity e P U S
  let c (S : TestAlgebra K) := Units.map (algebraMap K S).toMonoidHom d
  let h (S : TestAlgebra K) := testVectorSimilarity_quadratic e P U d hq S
  let hInv (S : TestAlgebra K) := inverseSimilarity (V S) (c S) (h S)
  let A (S : TestAlgebra K) := representedSpinEquiv q₀ b₀ (originalSplitPoints M S)
    (originalSplitPoints_range M S)
  let E (S : TestAlgebra K) :=
    letI : Algebra F S := inferInstanceAs (Algebra F ((restrictTestAlgebra F K).obj S))
    similaritySpinEquiv q₀ b₀ P.form b (V S).symm (c S)⁻¹ (hInv S)
  have hA {S T : TestAlgebra K} (f : S ⟶ T)
      (p : Points G.val.X ((restrictTestAlgebra F K).obj S)) :
      A T (mapPoints ((restrictTestAlgebra F K).map f) p) =
        Albert.SpinFunctor.map q₀ b₀ f.hom (A S p) := by
    apply Subtype.ext
    exact originalSplitPoints_natural M f p
  refine ⟨⟨fun S => (A S).trans (E S), ?_, ?_⟩⟩
  · intro S T f p
    let : Algebra F S := inferInstanceAs (Algebra F ((restrictTestAlgebra F K).obj S))
    let : Algebra F T := inferInstanceAs (Algebra F ((restrictTestAlgebra F K).obj T))
    change E T (A T (mapPoints ((restrictTestAlgebra F K).map f) p)) =
      Albert.SpinFunctor.map P.form b ((restrictTestAlgebra F K).map f).hom (E S (A S p))
    rw [hA f p]
    apply Subtype.ext
    apply similarityOnUnits_natural q₀ b₀ P.form b (hInv S) (hInv T) f.hom
      ((restrictTestAlgebra F K).map f).hom (fun _ => rfl)
    · change f.hom (algebraMap K S d.inv) = algebraMap K T d.inv
      exact f.hom.commutes _
    · intro x
      apply (V T).injective
      rw [LinearEquiv.apply_symm_apply]
      have hv := testVectorSimilarity_natural e P U f ((V S).symm x)
      change V T (changeModule ((restrictTestAlgebra F K).map f).hom ((V S).symm x)) =
        changeModule f.hom (V S ((V S).symm x)) at hv
      rw [LinearEquiv.apply_symm_apply] at hv
      exact hv.symm
  · intro S p
    let : Algebra F S := inferInstanceAs (Algebra F ((restrictTestAlgebra F K).obj S))
    obtain ⟨g, hg, hm⟩ := originalSplitPoints_vector e M P U hU S p
    have hv := similarityOnUnits_vector q₀ b₀ P.form b (V S).symm (c S)⁻¹ (hInv S) (A S p) g hg
    rw [LinearEquiv.symm_symm, testVectorSimilarity_intertwines e M P U S p g hm] at hv
    exact hv

end SplitRepresentation

end SplitComparison

section AffineCoordinates

variable {k : Type u} [Field k] {A : TestAlgebra k} {X : SchemeOver k}

private def affinePointsEquiv (p : (testSpec k).obj (op A) ≅ X) (S : TestAlgebra k) :
    (A →ₐ[k] S) ≃ Points X S where
  toFun f := mapPoints (CommAlgCat.ofHom f) p.hom
  invFun x := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage (x ≫ p.inv)).unop.hom
  left_inv f := by
    have h : (mapPoints (CommAlgCat.ofHom f) p.hom) ≫ p.inv =
        (testSpec k).map (CommAlgCat.ofHom f).op := by
      change ((testSpec k).map (CommAlgCat.ofHom f).op ≫ p.hom) ≫ p.inv = _
      simp
    change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      (mapPoints (CommAlgCat.ofHom f) p.hom ≫ p.inv)).unop.hom = f
    rw [h, Functor.FullyFaithful.preimage_map]
    rfl
  right_inv x := by
    change (testSpec k).map ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      (x ≫ p.inv)) ≫ p.hom = x
    rw [Functor.FullyFaithful.map_preimage]
    simp

private theorem affinePointsEquiv_natural (p : (testSpec k).obj (op A) ≅ X)
    {S T : TestAlgebra k} (f : S ⟶ T) (a : A →ₐ[k] S) :
    affinePointsEquiv p T (f.hom.comp a) = mapPoints f (affinePointsEquiv p S a) := by
  change (testSpec k).map ((CommAlgCat.ofHom a ≫ f).op) ≫ p.hom =
    (testSpec k).map f.op ≫ (testSpec k).map (CommAlgCat.ofHom a).op ≫ p.hom
  rw [op_comp, Functor.map_comp, Category.assoc]

end AffineCoordinates

section Algebras

variable {k : Type u} [Field k] {A B : Type u}
  [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

private theorem naturalAlgHom_apply
    (E : ∀ S : TestAlgebra k, (A →ₐ[k] S) → (B →ₐ[k] S))
    (hE : ∀ {S T : TestAlgebra k} (f : S ⟶ T) (a : A →ₐ[k] S),
      E T (f.hom.comp a) = f.hom.comp (E S a))
    (S : TestAlgebra k) (a : A →ₐ[k] S) :
    E S a = a.comp (E (CommAlgCat.of k A) (AlgHom.id k A)) := by
  let f : CommAlgCat.of k A ⟶ S := ConcreteCategory.ofHom (C := CommAlgCat k) a
  have h := hE f (AlgHom.id k A)
  change E S (a.comp (AlgHom.id k A)) = a.comp (E (CommAlgCat.of k A) (AlgHom.id k A)) at h
  rwa [AlgHom.comp_id] at h

private def naturalAlgEquiv
    (E : ∀ S : TestAlgebra k, (A →ₐ[k] S) ≃ (B →ₐ[k] S))
    (hE : ∀ {S T : TestAlgebra k} (f : S ⟶ T) (a : A →ₐ[k] S),
      E T (f.hom.comp a) = f.hom.comp (E S a)) : B ≃ₐ[k] A := by
  let f := E (CommAlgCat.of k A) (AlgHom.id k A)
  let g := (E (CommAlgCat.of k B)).symm (AlgHom.id k B)
  have hg : E (CommAlgCat.of k B) g = AlgHom.id k B := (E _).apply_symm_apply _
  have hgf : g.comp f = AlgHom.id k B :=
    (naturalAlgHom_apply (fun S => E S) hE (CommAlgCat.of k B) g).symm.trans hg
  refine AlgEquiv.ofAlgHom f g ?_ hgf
  apply (E (CommAlgCat.of k A)).injective
  rw [naturalAlgHom_apply (fun S => E S) hE _ (f.comp g), AlgHom.comp_assoc, hgf,
    AlgHom.comp_id]

private theorem naturalAlgEquiv_apply
    (E : ∀ S : TestAlgebra k, (A →ₐ[k] S) ≃ (B →ₐ[k] S))
    (hE : ∀ {S T : TestAlgebra k} (f : S ⟶ T) (a : A →ₐ[k] S),
      E T (f.hom.comp a) = f.hom.comp (E S a)) :
    (naturalAlgEquiv E hE).toAlgHom = E (CommAlgCat.of k A) (AlgHom.id k A) := rfl

end Algebras

section Extension

open Algebra.TensorProduct

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private abbrev extendTest (K : Type u) [Field K] [Algebra k K] (A : TestAlgebra k) :
    TestAlgebra K :=
  CommAlgCat.of K (K ⊗[k] A)

private def testHomOfRingHom {A B : TestAlgebra k} (f : A →+* B)
    (hf : ∀ r, f (algebraMap k A r) = algebraMap k B r) : A ⟶ B :=
  ConcreteCategory.ofHom (C := CommAlgCat k) { toRingHom := f, commutes' := hf }

private def extensionInclusion (A : TestAlgebra k) :
    A ⟶ (restrictTestAlgebra k K).obj (extendTest K A) := by
  let f : A →+* K ⊗[k] A := (includeRight (R := k) (A := K) (B := A)).toRingHom
  refine testHomOfRingHom f (fun r => ?_)
  change (1 : K) ⊗ₜ[k] algebraMap k A r = algebraMap k K r ⊗ₜ[k] (1 : A)
  rw [Algebra.algebraMap_eq_smul_one (A := ↑A), TensorProduct.tmul_smul,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul']

private theorem extensionInclusion_injective (A : TestAlgebra k) :
    Function.Injective (extensionInclusion (K := K) A).hom :=
  includeRight_injective (R := k) (A := K) (B := A) (algebraMap k K).injective

private theorem tensorLift_natural {R L A S T : Type*}
    [CommRing R] [CommRing L] [Algebra R L] [CommRing A] [Algebra R A]
    [CommRing S] [Algebra R S] [Algebra L S] [IsScalarTower R L S]
    [CommRing T] [Algebra R T] [Algebra L T] [IsScalarTower R L T]
    (f : S →ₐ[L] T) (g : A →ₐ[R] S) :
    liftEquivRight R L A T ((f.restrictScalars R).comp g) =
      f.comp (liftEquivRight R L A S g) := by
  apply Algebra.TensorProduct.ext
  · ext
  · ext a
    simp [liftEquivRight]

private theorem tensorRestrict_natural {R L A S T : Type*}
    [CommRing R] [CommRing L] [Algebra R L] [CommRing A] [Algebra R A]
    [CommRing S] [Algebra R S] [Algebra L S] [IsScalarTower R L S]
    [CommRing T] [Algebra R T] [Algebra L T] [IsScalarTower R L T]
    (f : S →ₐ[L] T) (g : (L ⊗[R] A) →ₐ[L] S) :
    (liftEquivRight R L A T).symm (f.comp g) =
      (f.restrictScalars R).comp ((liftEquivRight R L A S).symm g) := by
  apply (liftEquivRight R L A T).injective
  rw [Equiv.apply_symm_apply, tensorLift_natural, Equiv.apply_symm_apply]

end Extension

section SplitCoordinateRing

open Algebra.TensorProduct (liftEquivRight)
open private SpinCoordinates integralSpin_algebraSmooth spinCoordinatePointEquiv
  spinCoordinatePointEquiv_natural from LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels
open private SpinRing from LinearAlgebraicGroups.Albert.SplitSpin
open private isReduced_of_smooth_algebra from LinearAlgebraicGroups.Affine.SmoothnessCriteria

section ExtendedPoints

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  {A : TestAlgebra F} {X : SchemeOver F}

private def extendedAffinePointsEquiv (p : (testSpec F).obj (op A) ≅ X) (S : TestAlgebra K) :
    ((K ⊗[F] A) →ₐ[K] S) ≃ Points X ((restrictTestAlgebra F K).obj S) := by
  letI : Algebra F S := inferInstanceAs (Algebra F ((restrictTestAlgebra F K).obj S))
  letI : IsScalarTower F K S := IsScalarTower.of_algebraMap_eq' rfl
  exact (liftEquivRight F K A S).symm.trans (affinePointsEquiv p ((restrictTestAlgebra F K).obj S))

private theorem extendedAffinePointsEquiv_natural (p : (testSpec F).obj (op A) ≅ X)
    {S T : TestAlgebra K} (f : S ⟶ T) (a : (K ⊗[F] A) →ₐ[K] S) :
    extendedAffinePointsEquiv p T (f.hom.comp a) =
      mapPoints ((restrictTestAlgebra F K).map f) (extendedAffinePointsEquiv p S a) := by
  let : Algebra F S := inferInstanceAs (Algebra F ((restrictTestAlgebra F K).obj S))
  let : Algebra F T := inferInstanceAs (Algebra F ((restrictTestAlgebra F K).obj T))
  let : IsScalarTower F K S := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F K T := IsScalarTower.of_algebraMap_eq' rfl
  change affinePointsEquiv p ((restrictTestAlgebra F K).obj T)
      ((liftEquivRight F K A T).symm (f.hom.comp a)) = _
  rw [tensorRestrict_natural]
  exact affinePointsEquiv_natural p ((restrictTestAlgebra F K).map f)
    ((liftEquivRight F K A S).symm a)

end ExtendedPoints

section Reducedness

variable {F K I : Type u} [Field F] [Field K] [Algebra F K] [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ} {G : Specs.AffineAlgebraicGroup F}

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 1000000 in
/-- The universal test ring over the splitting field is reduced by the
smooth integral hyperbolic spin charts. -/
private theorem splitCoordinate_isReduced (M : SpinModel G D)
    {A : TestAlgebra F} (p : (testSpec F).obj (op A) ≅ G.val.X) :
    IsReduced (K ⊗[F] A) := by
  let m := Fintype.card I
  let d : Fin m ≃ I := (Fintype.equivFin I).symm
  let : LinearOrder (I ⊕ I) := LinearOrder.lift' (Fintype.equivFin (I ⊕ I))
    (Fintype.equivFin (I ⊕ I)).injective
  let C := SpinCoordinates K m
  let E (S : TestAlgebra K) : ((K ⊗[F] A) →ₐ[K] S) ≃ (C →ₐ[K] S) :=
    (extendedAffinePointsEquiv p S).trans
      ((pointComparison M S).toEquiv.trans (spinCoordinatePointEquiv M.splitCover d S))
  have hE {S T : TestAlgebra K} (f : S ⟶ T) (a : (K ⊗[F] A) →ₐ[K] S) :
      E T (f.hom.comp a) = f.hom.comp (E S a) := by
    change spinCoordinatePointEquiv M.splitCover d T
      (pointComparison M T (extendedAffinePointsEquiv p T (f.hom.comp a))) = _
    rw [extendedAffinePointsEquiv_natural, pointComparison_natural,
      spinCoordinatePointEquiv_natural]
    rfl
  have hm : 0 < m := by
    have h := RM03.CSA.degree_pos D.centralSimple
    change 0 < _root_.Specs.RM03.CSA.degree F ρ.fixedSubalgebra at h
    rw [D.degree] at h
    dsimp only [m]
    omega
  let : Algebra.Smooth ℤ (SpinRing m) := integralSpin_algebraSmooth m hm
  let : Algebra.Smooth K C := Algebra.Smooth.baseChange ℤ (SpinRing m) K
  let e : C ≃ₐ[K] (K ⊗[F] A) :=
    naturalAlgEquiv (k := K) (A := K ⊗[F] A) (B := C) E hE
  let : IsReduced C := isReduced_of_smooth_algebra K C
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

end Reducedness

end SplitCoordinateRing

section GaloisDescentTools
open Albert.SpinFunctor (Spin vectorAction regular_vectorKernel)
open Albert.SpinSpecification (coefficientMap)
open private changeModule from LinearAlgebraicGroups.Albert.SpinFunctor

section FixedTensors

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private def tensorGalois (A : Type u) [CommRing A] [Algebra F A] (s : Gal(K/F)) :
    (K ⊗[F] A) ≃ₐ[F] (K ⊗[F] A) :=
  Algebra.TensorProduct.congr s (AlgEquiv.refl : A ≃ₐ[F] A)

private def extensionAutomorphism (A : TestAlgebra F) (s : Gal(K/F)) :
    (restrictTestAlgebra F K).obj (extendTest K A) ⟶
      (restrictTestAlgebra F K).obj (extendTest K A) :=
  testHomOfRingHom (tensorGalois A s).toRingHom (fun r => by
    change tensorGalois A s (algebraMap F K r ⊗ₜ[F] (1 : A)) =
      algebraMap F K r ⊗ₜ[F] (1 : A)
    simp [tensorGalois])

private theorem testHom_ext {A B : TestAlgebra F} {f g : A ⟶ B}
    (h : ∀ x, f.hom x = g.hom x) : f = g :=
  CommAlgCat.hom_ext (AlgHom.ext h)

private theorem extensionInclusion_comp_automorphism (A : TestAlgebra F) (s : Gal(K/F)) :
    extensionInclusion A ≫ extensionAutomorphism A s = extensionInclusion A := by
  apply testHom_ext
  intro a
  change tensorGalois A s (1 ⊗ₜ[F] a) = (1 : K) ⊗ₜ[F] a
  simp [tensorGalois]

private theorem extensionAutomorphism_surjective (A : TestAlgebra F) (s : Gal(K/F)) :
    Function.Surjective (extensionAutomorphism A s).hom :=
  (tensorGalois A s).surjective

private theorem fixedTensor_mem_range [FiniteDimensional F K] [IsGalois F K]
    (A : TestAlgebra F) (x : K ⊗[F] A) (hx : ∀ s : Gal(K/F), tensorGalois A s x = x) :
    x ∈ Set.range (extensionInclusion (K := K) A).hom := by
  let b := Module.Free.chooseBasis F A
  let c := b.baseChange K
  have hcoord (s : Gal(K/F)) (y : K ⊗[F] A) (i : Module.Free.ChooseBasisIndex F A) :
      c.repr (tensorGalois A s y) i = s (c.repr y i) := by
    induction y with
    | tmul a v => simp [c, tensorGalois, Algebra.smul_def]
    | add y z hy hz => simp [hy, hz]
  have hscalar (i : Module.Free.ChooseBasisIndex F A) :
      c.repr x i ∈ Set.range (algebraMap F K) :=
    (IsGalois.mem_range_algebraMap_iff_fixed (F := F) _).2
      (fun s => (hcoord s x i).symm.trans (congrArg (fun y => c.repr y i) (hx s)))
  choose a ha using hscalar
  classical
  let d := (c.repr x).support
  refine ⟨∑ i ∈ d, a i • b i, ?_⟩
  change (1 : K) ⊗ₜ[F] (∑ i ∈ d, a i • b i) = x
  calc
    _ = ∑ i ∈ d, c.repr x i • c i := by
      rw [TensorProduct.tmul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← ha i, show c i = (1 : K) ⊗ₜ[F] b i from b.baseChange_apply K i,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.smul_def, mul_one]
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = x := by
      simpa only [Finsupp.linearCombination_apply, Finsupp.sum, d] using c.linearCombination_repr x

private theorem factorThroughInclusion {A B R : TestAlgebra F} (j : A ⟶ R)
    (hj : Function.Injective j.hom) (f : B ⟶ R) (hf : ∀ b, f.hom b ∈ Set.range j.hom) :
    ∃ f₀ : B ⟶ A, f₀ ≫ j = f := by
  let e := AlgEquiv.ofInjective j.hom hj
  let f₀ := e.symm.toAlgHom.comp (f.hom.codRestrict j.hom.range hf)
  refine ⟨ConcreteCategory.ofHom (C := CommAlgCat F) f₀, ?_⟩
  apply testHom_ext
  intro b
  exact congrArg Subtype.val (e.apply_symm_apply ⟨f.hom b, hf b⟩)

/-- Restriction of a Galois-invariant algebra map to the original coefficients. -/
private theorem descend_algebraHom [FiniteDimensional F K] [IsGalois F K]
    {A B : TestAlgebra F}
    (f : B ⟶ (restrictTestAlgebra F K).obj (extendTest K A))
    (hf : ∀ s : Gal(K/F), f ≫ extensionAutomorphism A s = f) :
    ∃ f₀ : B ⟶ A, f₀ ≫ extensionInclusion (K := K) A = f := by
  apply factorThroughInclusion _ (extensionInclusion_injective A) f
  intro b
  apply fixedTensor_mem_range A
  intro s
  exact congrArg (fun g : B ⟶ _ => g.hom b) (hf s)

end FixedTensors

section ReducedSpin

variable {F : Type u} [Field F] {V : Type u} {J : Type w} [AddCommGroup V] [Module F V]
  [Fintype J] [LinearOrder J]
  (q : QuadraticForm F V) (b : Module.Basis J F V)

private theorem spin_eq_of_vectorAction [CharP F 2] (R : TestAlgebra F) [IsReduced R]
    (hq : LinearMap.ker q.polarBilin = ⊥)
    (a t : Spin q R b) (h : vectorAction q R b a = vectorAction q R b t) : a = t := by
  have hker : vectorAction q R b (a * t⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨z, ⟨hz, hval⟩, _⟩ := (regular_vectorKernel q R b (Or.inl hq) (a * t⁻¹)).1 hker
  have two : (2 : R) = 0 := by
    have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
    simpa only [map_ofNat, map_zero] using congrArg (algebraMap F R) htwo
  have hz' : z = 1 := by
    apply eq_of_sub_eq_zero
    apply IsNilpotent.eq_zero
    refine ⟨2, ?_⟩
    rw [sub_sq, pow_two z, hz, two]
    simpa [one_add_one_eq_two] using two
  apply mul_inv_eq_one.mp
  apply Subtype.ext
  apply Units.ext
  rw [hval, hz', map_one]
  rfl

private theorem changeModule_surjective {R S : TestAlgebra F} (f : R ⟶ S)
    (hf : Function.Surjective f.hom) :
    Function.Surjective (changeModule (M := V) f.hom) := by
  exact TensorProduct.map_surjective hf (fun x => ⟨x, rfl⟩)

private theorem coefficientMap_injective {R S : TestAlgebra F} (f : R ⟶ S)
    (hf : Function.Injective f.hom) :
    Function.Injective (coefficientMap q R f.hom) := by
  exact Module.Flat.rTensor_preserves_injective_linearMap
    (M := CliffordAlgebra q) f.hom.toLinearMap hf

end ReducedSpin

end GaloisDescentTools

section DescendingSpinRepresentation
open Albert.SpinFunctor (Spin pointEquiv pointEquiv_natural CoordinateRing vectorAction
  vectorAction_naturality vectorAction_characterization)
open Albert.SpinSpecification (spinUnits IsVectorAction coefficientMap vectors)
open Algebra.TensorProduct (liftEquivRight)
open private changeModule vectorAction_unique from LinearAlgebraicGroups.Albert.SpinFunctor

variable {F K I : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ} {G : Specs.AffineAlgebraicGroup F}
  {n : ℕ} {e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) F}
  {M : SpinModel G D} {P : RecoveredForm (D := D) e}
  {A : TestAlgebra F} (p₀ : (testSpec F).obj (op A) ≅ G.val.X)
  (E : SplitRepresentation e M P)

local notation "b" => Pi.basisFun F (Fin n)

private abbrev recoveredSpinRing (P : RecoveredForm (D := D) e) := CoordinateRing P.form b

private def compareSpinAlgebras (S : TestAlgebra K) :
    let R := (restrictTestAlgebra F K).obj S
    (A →ₐ[F] R) ≃ (recoveredSpinRing P →ₐ[F] R) :=
  let R := (restrictTestAlgebra F K).obj S
  (affinePointsEquiv p₀ R).trans <|
    (E.points S).toEquiv.trans (pointEquiv P.form b R).symm

private theorem compareSpinAlgebras_point (S : TestAlgebra K)
    (a : A →ₐ[F] (restrictTestAlgebra F K).obj S) :
    let R := (restrictTestAlgebra F K).obj S
    pointEquiv P.form b R (compareSpinAlgebras p₀ E S a) =
      E.points S (affinePointsEquiv p₀ R a) :=
  (pointEquiv P.form b ((restrictTestAlgebra F K).obj S)).apply_symm_apply _

private theorem compareSpinAlgebras_natural {S T : TestAlgebra K} (f : S ⟶ T)
    (a : A →ₐ[F] (restrictTestAlgebra F K).obj S) :
    let g := ((restrictTestAlgebra F K).map f).hom
    compareSpinAlgebras p₀ E T (g.comp a) = g.comp (compareSpinAlgebras p₀ E S a) := by
  dsimp only
  let R := (restrictTestAlgebra F K).obj T
  apply (pointEquiv P.form b R).injective
  rw [compareSpinAlgebras_point, pointEquiv_natural, compareSpinAlgebras_point,
    affinePointsEquiv_natural p₀ ((restrictTestAlgebra F K).map f) a]
  exact E.natural f _

private def compareExtendedSpinAlgebras (S : TestAlgebra K) :
    ((K ⊗[F] A) →ₐ[K] S) ≃ ((K ⊗[F] recoveredSpinRing P) →ₐ[K] S) := by
  letI : Algebra F S := inferInstanceAs (Algebra F ((restrictTestAlgebra F K).obj S))
  letI : IsScalarTower F K S := IsScalarTower.of_algebraMap_eq' rfl
  exact (liftEquivRight F K A S).symm.trans
    ((compareSpinAlgebras p₀ E S).trans (liftEquivRight F K (recoveredSpinRing P) S))

private theorem compareExtendedSpinAlgebras_natural {S T : TestAlgebra K} (f : S ⟶ T)
    (a : (K ⊗[F] A) →ₐ[K] S) :
    compareExtendedSpinAlgebras p₀ E T (f.hom.comp a) =
      f.hom.comp (compareExtendedSpinAlgebras p₀ E S a) := by
  let : Algebra F S := inferInstanceAs (Algebra F ((restrictTestAlgebra F K).obj S))
  let : Algebra F T := inferInstanceAs (Algebra F ((restrictTestAlgebra F K).obj T))
  let : IsScalarTower F K S := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F K T := IsScalarTower.of_algebraMap_eq' rfl
  change liftEquivRight F K (recoveredSpinRing P) T
      (compareSpinAlgebras p₀ E T ((liftEquivRight F K A T).symm (f.hom.comp a))) =
    f.hom.comp (liftEquivRight F K (recoveredSpinRing P) S
      (compareSpinAlgebras p₀ E S ((liftEquivRight F K A S).symm a)))
  rw [tensorRestrict_natural]
  have h := compareSpinAlgebras_natural p₀ E f ((liftEquivRight F K A S).symm a)
  change compareSpinAlgebras p₀ E T
    ((f.hom.restrictScalars F).comp ((liftEquivRight F K A S).symm a)) = _ at h
  rw [h]
  exact tensorLift_natural f.hom _

private theorem compareExtendedSpinAlgebras_tmul_one {S : TestAlgebra K}
    (a : extendTest K A ⟶ S) (x : recoveredSpinRing P) :
    compareExtendedSpinAlgebras p₀ E S a.hom (1 ⊗ₜ[F] x) =
      compareSpinAlgebras p₀ E S
        (extensionInclusion (K := K) A ≫ (restrictTestAlgebra F K).map a).hom x := by
  let : Algebra F S := ((restrictTestAlgebra F K).obj S).algebra
  let : IsScalarTower F K S := IsScalarTower.of_algebraMap_eq' rfl
  change liftEquivRight F K (recoveredSpinRing P) S
    (compareSpinAlgebras p₀ E S ((liftEquivRight F K A S).symm a.hom)) (1 ⊗ₜ[F] x) = _
  have h : (liftEquivRight F K A S).symm a.hom =
      (extensionInclusion (K := K) A ≫ (restrictTestAlgebra F K).map a).hom := by
    apply AlgHom.ext
    intro y
    rfl
  rw [h]
  simp [liftEquivRight]

private theorem recoveredPolarKer (P : RecoveredForm (D := D) e) :
    LinearMap.ker P.form.polarBilin = ⊥ := by
  exact LinearMap.BilinForm.Nondegenerate.ker_eq_bot P.regular

private theorem spinAlgebraMap_fixed [CharP F 2] {R : TestAlgebra F} [IsReduced R]
    (t : R ⟶ R) (ht : Function.Surjective t.hom)
    (p : Points G.val.X R) (hp : mapPoints t p = p)
    (f : recoveredSpinRing P →ₐ[F] R)
    (hf : IsVectorAction P.form R (pointEquiv P.form b R f).val (pairVector e M R p)) :
    t.hom.comp f = f := by
  let z := pointEquiv P.form b R f
  apply (pointEquiv P.form b R).injective
  rw [pointEquiv_natural]
  apply spin_eq_of_vectorAction P.form b R (recoveredPolarKer P)
  have hv : pairVector e M R p = vectorAction P.form R b z :=
    vectorAction_unique P.form R b z _ hf
  apply LinearEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := changeModule_surjective (V := Fin n → F) t ht x
  rw [← vectorAction_naturality, ← hv, ← pairVector_natural e M t p y, hp]

set_option maxHeartbeats 600000 in
private theorem universalSpinMap_fixed [CharP F 2] [IsReduced (K ⊗[F] A)]
    (s : Gal(K/F)) :
    let S := extendTest K A
    let R := (restrictTestAlgebra F K).obj S
    let j := extensionInclusion (K := K) A
    let f : CommAlgCat.of F (recoveredSpinRing P) ⟶ R :=
      ConcreteCategory.ofHom (C := CommAlgCat F) (compareSpinAlgebras p₀ E S j.hom)
    f ≫ extensionAutomorphism A s = f := by
  intro S R j f
  let t := extensionAutomorphism A s
  let p := affinePointsEquiv p₀ R j.hom
  have hfix : mapPoints t p = p := by
    rw [← affinePointsEquiv_natural p₀ t j.hom]
    exact congrArg (fun a : A ⟶ R => affinePointsEquiv p₀ R a.hom)
      (extensionInclusion_comp_automorphism A s)
  let : IsReduced R := inferInstanceAs (IsReduced (K ⊗[F] A))
  have h := spinAlgebraMap_fixed (P := P) (M := M) (R := R) t
    (extensionAutomorphism_surjective A s) p hfix f.hom (by
      have hz := compareSpinAlgebras_point p₀ E S j.hom
      have hv := E.vector S p
      rw [← hz] at hv
      exact hv)
  apply testHom_ext
  intro x
  exact DFunLike.congr_fun h x

private def spinPointForAlgebra (f : recoveredSpinRing P →ₐ[F] A) (R : TestAlgebra F)
    (p : Points G.val.X R) : Spin P.form R b :=
  pointEquiv P.form b R (((affinePointsEquiv p₀ R).symm p).comp f)

private theorem spinPointForAlgebra_natural (f : recoveredSpinRing P →ₐ[F] A)
    {R S : TestAlgebra F} (g : R ⟶ S) (p : Points G.val.X R) :
    spinPointForAlgebra p₀ f S (mapPoints g p) =
      Albert.SpinFunctor.map P.form b g.hom (spinPointForAlgebra p₀ f R p) := by
  let a := (affinePointsEquiv p₀ R).symm p
  have ha : (affinePointsEquiv p₀ S).symm (mapPoints g p) = g.hom.comp a := by
    apply (affinePointsEquiv p₀ S).injective
    rw [Equiv.apply_symm_apply, affinePointsEquiv_natural]
    change _ = mapPoints g ((affinePointsEquiv p₀ R) ((affinePointsEquiv p₀ R).symm p))
    rw [Equiv.apply_symm_apply]
  unfold spinPointForAlgebra
  rw [ha, AlgHom.comp_assoc, pointEquiv_natural]

private theorem spinPointForAlgebra_bijective (f : recoveredSpinRing P →ₐ[F] A)
    (hf : Function.Bijective f) (R : TestAlgebra F) :
    Function.Bijective (spinPointForAlgebra p₀ f R) := by
  let c := AlgEquiv.ofBijective f hf
  let H : (A →ₐ[F] R) ≃ (recoveredSpinRing P →ₐ[F] R) :=
    ⟨(·.comp c.toAlgHom), (·.comp c.symm.toAlgHom),
      fun a => by simp [AlgHom.comp_assoc],
      fun a => by simp [AlgHom.comp_assoc]⟩
  exact (pointEquiv P.form b R).bijective.comp
    (H.bijective.comp (affinePointsEquiv p₀ R).symm.bijective)

set_option maxHeartbeats 700000 in
private theorem spinPoint_descent [CharP F 2] [FiniteDimensional F K] [IsGalois F K] :
    ∃ (f : recoveredSpinRing P →ₐ[F] A), Function.Bijective f ∧
      ∀ (S : TestAlgebra K) (p : Points G.val.X ((restrictTestAlgebra F K).obj S)),
        spinPointForAlgebra p₀ f ((restrictTestAlgebra F K).obj S) p = E.points S p := by
  let S₀ := extendTest K A
  let R₀ := (restrictTestAlgebra F K).obj S₀
  let j := extensionInclusion (K := K) A
  let B := CommAlgCat.of F (recoveredSpinRing P)
  let f : B ⟶ R₀ :=
    ConcreteCategory.ofHom (C := CommAlgCat F) (compareSpinAlgebras p₀ E S₀ j.hom)
  let : IsReduced (K ⊗[F] A) := splitCoordinate_isReduced M p₀
  obtain ⟨f₀, hf₀⟩ := descend_algebraHom f (universalSpinMap_fixed p₀ E)
  have hcoeff (x : B) : j.hom (f₀.hom x) = (compareSpinAlgebras p₀ E S₀ j.hom) x :=
    congrArg (fun g : B ⟶ R₀ => g.hom x) hf₀
  refine ⟨f₀.hom, ?_, ?_⟩
  · let H : (K ⊗[F] B) ≃ₐ[K] (K ⊗[F] A) :=
      naturalAlgEquiv (k := K) (A := K ⊗[F] A) (B := K ⊗[F] B)
        (compareExtendedSpinAlgebras p₀ E) (compareExtendedSpinAlgebras_natural p₀ E)
    have hH : H.toAlgHom = Algebra.TensorProduct.map (AlgHom.id K K) f₀.hom := by
      apply Algebra.TensorProduct.ext
      · ext
      · apply AlgHom.ext
        intro x
        change H (1 ⊗ₜ[F] x) = (1 : K) ⊗ₜ[F] f₀.hom x
        have h := naturalAlgEquiv_apply (k := K) (A := K ⊗[F] A) (B := K ⊗[F] B)
          (compareExtendedSpinAlgebras p₀ E) (compareExtendedSpinAlgebras_natural p₀ E)
        rw [show H (1 ⊗ₜ[F] x) =
          compareExtendedSpinAlgebras p₀ E S₀ (AlgHom.id K (K ⊗[F] A)) (1 ⊗ₜ[F] x)
            from DFunLike.congr_fun h _]
        change _ = j.hom (f₀.hom x)
        rw [hcoeff]
        have h := compareExtendedSpinAlgebras_tmul_one p₀ E (𝟙 S₀) x
        rw [CategoryTheory.Functor.map_id, Category.comp_id] at h
        exact h
    apply (Module.FaithfullyFlat.lTensor_bijective_iff_bijective F K f₀.hom.toLinearMap).mp
    have hh : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id K K) f₀.hom) :=
      hH ▸ H.bijective
    exact hh
  · intro S p
    let R := (restrictTestAlgebra F K).obj S
    let : Algebra F S := R.algebra
    let : IsScalarTower F K S := IsScalarTower.of_algebraMap_eq' rfl
    let a := (affinePointsEquiv p₀ R).symm p
    let g : S₀ ⟶ S := ConcreteCategory.ofHom (C := CommAlgCat K) (liftEquivRight F K A S a)
    let k := (restrictTestAlgebra F K).map g
    have hgj : j ≫ k = ConcreteCategory.ofHom (C := CommAlgCat F) a := by
      apply testHom_ext
      intro x
      change liftEquivRight F K A S a (1 ⊗ₜ[F] x) = a x
      simp [liftEquivRight]
      rfl
    have hg := compareSpinAlgebras_natural p₀ E g j.hom
    change compareSpinAlgebras p₀ E S (j ≫ k).hom = (f ≫ k).hom at hg
    rw [hgj, ← hf₀, Category.assoc, hgj] at hg
    have ha : compareSpinAlgebras p₀ E S a = a.comp f₀.hom := hg
    exact (congrArg (pointEquiv P.form b R) ha.symm).trans <|
      (compareSpinAlgebras_point p₀ E S a).trans
        (congrArg (E.points S) ((affinePointsEquiv p₀ R).apply_symm_apply p))

end DescendingSpinRepresentation

section Representation
open Albert.SpinFunctor (Spin vectorAction vectorAction_naturality vectorAction_characterization)
open Albert.SpinSpecification (spinUnits IsVectorAction coefficientMap)
open private changeModule vectorAction_unique from LinearAlgebraicGroups.Albert.SpinFunctor

section Realization

variable {F K I : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ} {G : Specs.AffineAlgebraicGroup F}
  {n : ℕ} {e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) F}
  {M : SpinModel G D} {P : RecoveredForm (D := D) e}
  {A : TestAlgebra F} (p₀ : (testSpec F).obj (op A) ≅ G.val.X)
  (E : SplitRepresentation e M P)

local notation "b" => Pi.basisFun F (Fin n)

private theorem spinPointMap_injective {R S : TestAlgebra F} (g : R ⟶ S)
    (hg : Function.Injective g.hom) :
    Function.Injective (Albert.SpinFunctor.map P.form b g.hom) := by
  intro a t h
  apply Subtype.ext
  apply Units.ext
  apply coefficientMap_injective P.form g hg
  exact congrArg (fun z : Spin P.form S b => z.val.val) h

private theorem splitPoints_vectorAction (S : TestAlgebra K)
    (p : Points G.val.X ((restrictTestAlgebra F K).obj S)) :
    let R := (restrictTestAlgebra F K).obj S
    vectorAction P.form R b (E.points S p) = pairVector e M R p :=
  (vectorAction_unique P.form ((restrictTestAlgebra F K).obj S) b _ _ (E.vector S p)).symm

private theorem vectorAction_of_extension {R T : TestAlgebra F} (f : R ⟶ T)
    (hf : Function.Injective f.hom) (p : Points G.val.X R) (z : Spin P.form R b)
    (hz : vectorAction P.form T b (Albert.SpinFunctor.map P.form b f.hom z) =
      pairVector e M T (mapPoints f p)) :
    vectorAction P.form R b z = pairVector e M R p := by
  apply LinearEquiv.ext
  intro x
  have hinj : Function.Injective (changeModule (M := Fin n → F) f.hom) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := Fin n → F) f.hom.toLinearMap hf
  apply hinj
  rw [vectorAction_naturality, hz, pairVector_natural e M f p x]

set_option maxRecDepth 1800 in
set_option maxHeartbeats 650000 in
private theorem representationFromAlgebra (f : recoveredSpinRing P →ₐ[F] A)
    (hf : Function.Bijective f)
    (hE : ∀ (S : TestAlgebra K) (p : Points G.val.X ((restrictTestAlgebra F K).obj S)),
      spinPointForAlgebra p₀ f ((restrictTestAlgebra F K).obj S) p = E.points S p) :
    ∃ a, CompatibleRepresentation e M P a := by
  let z := spinPointForAlgebra p₀ f
  have hz {R S : TestAlgebra F} (g : R ⟶ S) (p : Points G.val.X R) :
      z S (mapPoints g p) = Albert.SpinFunctor.map P.form b g.hom (z R p) :=
    spinPointForAlgebra_natural p₀ f g p
  let j (R : TestAlgebra F) := extensionInclusion (K := K) R
  have hext (R : TestAlgebra F) (p : Points G.val.X R) :
      z ((restrictTestAlgebra F K).obj (extendTest K R)) (mapPoints (j R) p) =
        E.points (extendTest K R) (mapPoints (j R) p) :=
    hE (extendTest K R) _
  let zMonoid (R : TestAlgebra F) : Points G.val.X R →* Spin P.form R b := {
    toFun := z R
    map_one' := by
      apply spinPointMap_injective (j R) (extensionInclusion_injective R)
      rw [← hz (j R) 1, hext R 1, map_one]
      have h : mapPoints (j R) (1 : Points G.val.X R) = 1 :=
        MonObj.comp_one ((testSpec F).map (j R).op)
      rw [h, map_one]
    map_mul' := by
      intro p t
      apply spinPointMap_injective (j R) (extensionInclusion_injective R)
      rw [← hz (j R) (p * t), hext R (p * t), map_mul,
        ← hz (j R) p, ← hz (j R) t, hext R p, hext R t]
      have h : mapPoints (j R) (p * t) = mapPoints (j R) p * mapPoints (j R) t :=
        MonObj.comp_mul ((testSpec F).map (j R).op) p t
      rw [h, map_mul] }
  let a (R : TestAlgebra F) : Points G.val.X R →* (ScalarClifford P.form R)ˣ :=
    (Spin P.form R b).subtype.comp (zMonoid R)
  refine ⟨a, ⟨?_, ?_⟩, ?_⟩
  · intro R
    have hbij := spinPointForAlgebra_bijective p₀ f hf R
    refine ⟨fun p t h => hbij.1 (Subtype.ext h), ?_⟩
    ext t
    constructor
    · rintro ⟨p, rfl⟩
      exact (z R p).property
    · intro ht
      obtain ⟨p, hp⟩ := hbij.2 (⟨t, ht⟩ : Spin P.form R b)
      exact ⟨p, congrArg Subtype.val hp⟩
  · intro R S g p
    exact congrArg Subtype.val (hz g p)
  · intro R p
    let S := extendTest K R
    let g := pairVector e M R p
    let X := testMatrix e R (M.fullPoints R (p ≫ (M.projection ≫ M.inclusion).hom.hom)).val
    have hm := (vectorMatrix_iff_columns (k := F) (R := R) (J := Fin n) g X).2
      (pairVector_column e M R p)
    refine ⟨g, ?_, hm⟩
    have hv : vectorAction P.form R b (z R p) = g := by
      apply vectorAction_of_extension (M := M) (j R) (extensionInclusion_injective R) p (z R p)
      rw [← hz (j R) p, hext R p]
      exact splitPoints_vectorAction E S (mapPoints (j R) p)
    change IsVectorAction P.form R (z R p).val g
    rw [← hv]
    exact vectorAction_characterization P.form R b (z R p)

end Realization

/-- The Clifford representation of the original group for the scalar form recovered
from the descended semitrace. -/
theorem splitSpinComparison : SplitSpinComparison.{u} := by
  intro F K I _ _ _ _ _ _ _ _ ρ D G M n e P
  obtain ⟨E⟩ := splitRepresentation_nonempty e M P
  obtain ⟨A, ⟨p₀⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.property.1
  obtain ⟨f, hf, hE⟩ := spinPoint_descent (A := A.unop) p₀ E
  exact representationFromAlgebra p₀ E f hf hE

/-- The two opposite parabolic radicals of the recovered form generate the original
spin group over the local field. -/
theorem localSplitSpinGeneration : LocalSplitSpinGeneration.{u} :=
  localSplitSpinGeneration_of_comparison.{u}
    CharacteristicTwoQuadraticPairs.arithmeticSplitIsotropy splitSpinComparison.{u}

end Representation

end
end LinearAlgebraicGroups.Arithmetic.SplitQuadraticPairSpinComparison
