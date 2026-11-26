import Specs.LinearAlgebraicGroups.Arithmetic.ScalarEvenSpinLocalDensity
import LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
import LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels
import LinearAlgebraicGroups.Arithmetic.OddSpinInnerDescent
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Degree
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.SkolemNoether
import Mathlib.RingTheory.MatrixAlgebra

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct Matrix CategoryTheory.MonObj
open WithConv

universe u

namespace LinearAlgebraicGroups.Arithmetic.ScalarEvenSpinLocalDensity

set_option linter.style.haveILetI false

open LinearAlgebraicGroups.Specs
open Specs.AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open Specs.Arithmetic.IsotropicSpinGeneration (IsRegular)
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.Arithmetic.OppositeRadicals (IsNoncentral)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.IntegralModels (MatrixRealization)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn)
open LinearAlgebraicGroups.Albert.CliffordSpecification (coefficientForm)
open LinearAlgebraicGroups.Albert.SpinSpecification (IsSpinPointRepresentation ScalarClifford)
open LinearAlgebraicGroups.CocharacterDynamics (oppositeCocharacter existsLimitDecomposition)

open private testPointSections from LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration

private theorem absolutelyAlmostSimpleForRadicals {F : Type u} [Field F]
    {G : AffineAlgebraicGroup F} (h : IsAbsolutelyAlmostSimple G) :
    Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G := by
  refine ⟨h.1, ?_, ?_⟩
  · rintro ⟨e⟩
    exact h.2.1 ((Grp.isZero_trivial _).of_iso e)
  · intro N hN
    rcases h.2.2 N hN with hzero | hiso
    · exact Or.inl ⟨hzero.iso (Grp.isZero_trivial _)⟩
    · exact Or.inr hiso

/-- Once the original group represents the intrinsic spin functor of a regular
form, its given noncentral cocharacter supplies the isotropy needed for generation. -/
private theorem radicalGenerationOfSpinRepresentation
    {F V J : Type u} [Field F] [Infinite F] [AddCommGroup V] [Module F V]
    [Fintype J] [LinearOrder J] {G : AffineAlgebraicGroup F}
    (hG : IsAbsolutelyAlmostSimple G) (q : QuadraticForm F V) (b : Module.Basis J F V)
    (e : ∀ R : TestAlgebra F, GroupPoints G.val R →* (ScalarClifford q R)ˣ)
    (hq : IsRegular q) (he : IsSpinPointRepresentation q G.val e)
    (c : Cocharacter G.val) (hc : IsNoncentral c) :
    unipotentGenerated G = ⊤ := by
  have hsimple := absolutelyAlmostSimpleForRadicals hG
  obtain ⟨v, hv, hvq⟩ := OddSpinInnerDescent.spinCocharacterIsotropy q b G e hq he c hc
  obtain ⟨h, _⟩ := IsotropicSpinGeneration.hyperbolicPairExistence q hq v hv hvq
  obtain ⟨a, _, ha, _, hgen⟩ := IsotropicSpinGeneration.localSpinGeneration q b G e he hq hsimple h
  obtain ⟨P⟩ := existsLimitDecomposition G a
  obtain ⟨Q⟩ := existsLimitDecomposition G (oppositeCocharacter a)
  exact (RelativeRayGeneration.twoRadicalsGenerate G hsimple a ha P Q).symm.trans
    (hgen P Q).2.2

private theorem densityOfRadicalGeneration {F : Type u} [Field F] [TopologicalSpace F]
    {G : AffineAlgebraicGroup F} (hgen : unipotentGenerated G = ⊤)
    (i : MatrixRealization G) :
    Dense {g : PointsIn i F | ∃ p ∈ unipotentGenerated G,
      toUnit ((testSpec F).obj (op (CommAlgCat.of F F))) ≫ p = g} := by
  have hset : {g : PointsIn i F | ∃ p ∈ unipotentGenerated G,
      toUnit ((testSpec F).obj (op (CommAlgCat.of F F))) ≫ p = g} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro g
    let p := testPointSections G.val g
    refine ⟨p, ?_, ?_⟩
    · rw [hgen]
      exact Subgroup.mem_top p
    · have hp := (testPointSections G.val).symm_apply_apply g
      change _ ≫ p = g at hp
      exact (congrArg (· ≫ p) (toUnit_unique _ _)).trans hp
  rw [hset]
  exact dense_univ

open RM03.Brauer.SemilinearDescent (AlgebraAction)
open Specs.SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)

section MatrixComparison

variable {F : Type u} [Field F] {R : Type u} [CommRing R] [Algebra F R]
variable {n : Type*} [Fintype n] [DecidableEq n]

private noncomputable def matrixScalarExtension :
    R ⊗[F] Matrix n n F ≃ₐ[R] Matrix n n R :=
  let E := (matrixEquivTensor n F R).symm
  { E.toRingEquiv with
    commutes' := fun r => by
      change E (r ⊗ₜ[F] 1) = algebraMap R (Matrix n n R) r
      dsimp only [E]
      rw [matrixEquivTensor_apply_symm, Matrix.map_one _ (map_zero _) (map_one _),
        Algebra.algebraMap_eq_smul_one] }

private theorem matrixScalarExtension_tmul (a : R) (x : Matrix n n F) :
    matrixScalarExtension (a ⊗ₜ[F] x) = a • x.map (algebraMap F R) :=
  matrixEquivTensor_apply_symm n F R a x

private noncomputable def scalarMatrixPresentation {A : Type u} [Ring A] [Algebra F A]
    (e : A ≃ₐ[F] Matrix n n F) : R ⊗[F] A ≃ₐ[R] Matrix n n R :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e).trans matrixScalarExtension

private theorem scalarMatrixPresentation_tmul {A : Type u} [Ring A] [Algebra F A]
    (e : A ≃ₐ[F] Matrix n n F) (a : R) (x : A) :
    scalarMatrixPresentation e (a ⊗ₜ[F] x) = a • (e x).map (algebraMap F R) := by
  rw [scalarMatrixPresentation, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  exact matrixScalarExtension_tmul a (e x)

private def extendMatrixUnit (H : (Matrix n n F)ˣ) : (Matrix n n R)ˣ :=
  Units.map (algebraMap F R).mapMatrix.toMonoidHom H

private theorem scalarMatrixPresentation_adjoint {A : Type u} [Ring A] [Algebra F A]
    (s : LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent.Involution F A)
    (e : A ≃ₐ[F] Matrix n n F) (H : (Matrix n n F)ˣ)
    (hs : ∀ x, e (s.toLinearMap x) = gramAdjoint H (e x))
    (x : R ⊗[F] A) :
    scalarMatrixPresentation e ((s.baseChange R).toLinearMap x) =
      gramAdjoint (extendMatrixUnit H) (scalarMatrixPresentation e x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rw [LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent.Involution.baseChange_tmul,
      scalarMatrixPresentation_tmul, scalarMatrixPresentation_tmul, hs]
    simp [gramAdjoint, extendMatrixUnit, Matrix.transpose_smul, Matrix.map_mul, Matrix.transpose_map]
  | add x y hx hy =>
    simp [map_add, hx, hy, gramAdjoint, Matrix.transpose_add, mul_add, add_mul]

private theorem scalarMatrixPresentation_natural {A : Type u} [Ring A] [Algebra F A]
    {S : Type u} [CommRing S] [Algebra F S] (e : A ≃ₐ[F] Matrix n n F)
    (f : R →ₐ[F] S) (x : R ⊗[F] A) :
    scalarMatrixPresentation e (Algebra.TensorProduct.map f (AlgHom.id F A) x) =
      f.toRingHom.mapMatrix (scalarMatrixPresentation e x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, scalarMatrixPresentation_tmul,
      scalarMatrixPresentation_tmul]
    ext i j
    change f a * algebraMap F S (e x i j) = f (a * algebraMap F R (e x i j))
    rw [map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

end MatrixComparison

private theorem gramProportional {K : Type u} [Field K] {n : Type*}
    [Fintype n] [DecidableEq n] [Nonempty n]
    (H J : (Matrix n n K)ˣ)
    (h : ∀ x, gramAdjoint H x = gramAdjoint J x) :
    ∃ c : Kˣ, J.val = (c : K) • H.val := by
  classical
  have hcomm (x : Matrix n n K) : Commute x (J.val * H.inv) := by
    have he := h x.transpose
    simp only [gramAdjoint, Matrix.transpose_transpose] at he
    calc
      x * (J.val * H.inv) = J.val * (J.inv * x * J.val) * H.inv := by
        rw [mul_assoc J.inv x J.val, ← mul_assoc J.val J.inv (x * J.val),
          J.val_inv, one_mul, mul_assoc]
      _ = J.val * (H.inv * x * H.val) * H.inv := by rw [he]
      _ = (J.val * H.inv) * x := by
        rw [mul_assoc J.val (H.inv * x * H.val) H.inv, mul_assoc (H.inv * x) H.val H.inv,
          H.val_inv, mul_one, ← mul_assoc]
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (fun i j _ => hcomm (Matrix.single i j 1))
  have hne : c ≠ 0 := by
    intro hzero
    have hz : ((J * H⁻¹ : (Matrix n n K)ˣ) : Matrix n n K) = 0 := by
      change J.val * H.inv = _
      rw [← hc, hzero, map_zero]
    exact (J * H⁻¹).ne_zero hz
  refine ⟨Units.mk0 c hne, ?_⟩
  calc
    J.val = (J.val * H.inv) * H.val := by rw [mul_assoc, H.inv_val, mul_one]
    _ = (c : K) • H.val := by
      rw [← hc]
      change algebraMap K (Matrix n n K) c * H.val = _
      rw [Algebra.smul_def]

section Splitting

open LinearMap (BilinForm)
open private polar_baseChange_tmul from LinearAlgebraicGroups.Albert.SpinFunctor

variable {F K I : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [Nonempty I]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}

omit [Nonempty I] in
private theorem matrixIndexEquiv (D : DescendedQuadraticPair ρ) {r : ℕ}
    (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin r) (Fin r) F) :
    Nonempty (Fin r ≃ I ⊕ I) := by
  have ha : _root_.RM03.CSA.IsCentralSimple F ρ.fixedSubalgebra := D.centralSimple
  have hr : _root_.Specs.RM03.CSA.degree F ρ.fixedSubalgebra = r :=
    _root_.RM03.CSA.degree_eq_matrix_size ha (scalarMatrixPresentation (R := F) e)
  apply Fintype.card_eq.mp
  rw [Fintype.card_fin, ← hr, D.degree, Fintype.card_sum, two_mul]

omit [Nonempty I] in
private theorem reindexGramAdjoint {L : Type*} [Fintype L] [DecidableEq L]
    (j : L ≃ I ⊕ I) (H : (Matrix L L F)ˣ) (x : Matrix L L F) :
    let E := Matrix.reindexAlgEquiv F F j
    E (gramAdjoint H x) = gramAdjoint (Units.map E.toMonoidHom H) (E x) := by
  intro E
  simp [gramAdjoint, Matrix.coe_reindexAlgEquiv, E]

omit [Nonempty I] in
private theorem recoverOrthogonalForm (fieldModel : FieldOrthogonalModel.{u})
    [LinearOrder (I ⊕ I)] (D : DescendedQuadraticPair ρ) (h₂ : (2 : F) ≠ 0)
    (horth : IsOrthogonal (toDivisionInvolution D.involution))
    {r : ℕ} (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin r) (Fin r) F) :
    ∃ (E : ρ.fixedSubalgebra ≃ₐ[F] Matrix (I ⊕ I) (I ⊕ I) F)
      (H : (Matrix (I ⊕ I) (I ⊕ I) F)ˣ) (q : QuadraticForm F (Fin r → F))
      (b : Module.Basis (I ⊕ I) F (Fin r → F)),
      IsRegular q ∧ BilinForm.toMatrix b q.polarBilin = H.val ∧
      ∀ x, E (D.involution.toLinearMap x) = gramAdjoint H (E x) := by
  obtain ⟨j⟩ := matrixIndexEquiv D e
  obtain ⟨H, q, _, hpolar, hnd, hadj⟩ := fieldModel r h₂ D.centralSimple _ horth e
  let E := Matrix.reindexAlgEquiv F F j
  refine ⟨e.trans E, Units.map E.toMonoidHom H, q, (Pi.basisFun F (Fin r)).reindex j,
    Or.inl (LinearMap.separatingLeft_iff_ker_eq_bot.mp hnd.1), ?_, ?_⟩
  · rw [hpolar]
    ext i l
    rw [BilinForm.toMatrix_apply, Module.Basis.reindex_apply, Module.Basis.reindex_apply,
      ← Matrix.toLinearMap₂_basisFun, Matrix.toLinearMap₂_apply_basis]
    rfl
  · intro x
    change E (e (D.involution.toLinearMap x)) = _
    rw [show e (D.involution.toLinearMap x) = gramAdjoint H (e x) from hadj x]
    exact reindexGramAdjoint j H (e x)

private def splitGramUnit (I R : Type u) [Fintype I] [DecidableEq I] [CommRing R] :
    (Matrix (I ⊕ I) (I ⊕ I) R)ˣ := by
  have h : hyperbolicGram I R * hyperbolicGram I R = 1 := by
    rw [hyperbolicGram, Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]
  exact ⟨hyperbolicGram I R, hyperbolicGram I R, h, h⟩

omit [Nonempty I] in
private theorem hyperbolicPolarGram :
    (Specs.Arithmetic.OddSpinModels.hyperbolicForm I K).polarBilin =
      Matrix.toLinearMap₂' K (hyperbolicGram I K) := by
  let b := Pi.basisFun K (I ⊕ I)
  rw [Specs.Arithmetic.OddSpinModels.hyperbolicForm, LinearMap.BilinMap.polarBilin_toQuadraticMap]
  apply b.ext
  intro i
  apply b.ext
  intro j
  simp only [LinearMap.add_apply, LinearMap.flip_apply]
  rw [← Matrix.toLinearMap₂_basisFun]
  simp only [b, Matrix.toLinearMap₂_apply_basis]
  cases i <;> cases j <;> simp [hyperbolicGram, Matrix.one_apply, eq_comm]

private def transposeUnit {L R : Type u} [Fintype L] [DecidableEq L] [CommRing R]
    (g : (Matrix L L R)ˣ) : (Matrix L L R)ˣ where
  val := g.val.transpose
  inv := g.inv.transpose
  val_inv := by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]

private theorem gramAdjoint_conjugate
    {L R : Type u} [Fintype L] [DecidableEq L] [CommRing R]
    (g J : (Matrix L L R)ˣ) (x : Matrix L L R) :
    (matrixInner g).symm (gramAdjoint J (matrixInner g x)) =
      gramAdjoint (transposeUnit g * J * g) x := by
  change g.inv * (J.inv * (g.val * x * g.inv).transpose * J.val) * g.val =
    (g.inv * (J.inv * g.inv.transpose)) * x.transpose * (g.val.transpose * J.val * g.val)
  simp only [Matrix.transpose_mul, mul_assoc]

private theorem splitMatrixComparison
    (D : DescendedQuadraticPair ρ)
    (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (I ⊕ I) (I ⊕ I) F)
    (H : (Matrix (I ⊕ I) (I ⊕ I) F)ˣ)
    (he : ∀ x, e (D.involution.toLinearMap x) = gramAdjoint H (e x)) :
    ∃ (g : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) (c : Kˣ),
      (∀ x, D.splitting x = matrixInner g (scalarMatrixPresentation e x)) ∧
      g.val.transpose * hyperbolicGram I K * g.val = (c : K) • (extendMatrixUnit H).val := by
  let E := scalarMatrixPresentation (R := K) e
  have hcs : _root_.RM03.CSA.IsCentralSimple K (K ⊗[F] ρ.fixedSubalgebra) :=
    _root_.RM03.CSA.isCentralSimple_baseChange D.centralSimple
  obtain ⟨z, hz⟩ := _root_.RM03.CSA.algEquiv_isInner hcs (E.trans D.splitting.symm)
  let g := (Units.map D.splitting.toMonoidHom z)⁻¹
  have hs (x : K ⊗[F] ρ.fixedSubalgebra) : D.splitting x = matrixInner g (E x) := by
    have h := congrArg D.splitting (hz x)
    simp only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply, map_mul] at h
    let U := Units.map D.splitting.toMonoidHom z
    change E x = U.val * D.splitting x * U.inv at h
    change D.splitting x = U.inv * E x * U.val
    rw [h, mul_assoc U.val, ← mul_assoc U.inv, U.inv_val, one_mul,
      mul_assoc, U.inv_val, mul_one]
  let J := splitGramUnit I K
  have hadj (x : Matrix (I ⊕ I) (I ⊕ I) K) :
      gramAdjoint (extendMatrixUnit H) x = gramAdjoint (transposeUnit g * J * g) x := by
    obtain ⟨y, rfl⟩ := E.surjective x
    rw [← gramAdjoint_conjugate, ← hs,
      ← show D.splitting ((D.involution.baseChange K).toLinearMap y) =
        gramAdjoint J (D.splitting y) from D.splittingInvolution y, hs,
      AlgEquiv.symm_apply_apply]
    exact (scalarMatrixPresentation_adjoint D.involution e H he y).symm
  obtain ⟨c, hc⟩ := gramProportional (extendMatrixUnit H) (transposeUnit g * J * g) hadj
  exact ⟨g, c, hs, hc⟩

omit [Nonempty I] in
private theorem coefficientPolarMatrix
    {V : Type u} [AddCommGroup V] [Module F V] [LinearOrder (I ⊕ I)]
    (q : QuadraticForm F V) (b : Module.Basis (I ⊕ I) F V) :
    BilinForm.toMatrix (b.baseChange K) (coefficientForm K q b).polarBilin =
      (BilinForm.toMatrix b q.polarBilin).map (algebraMap F K) := by
  ext i j
  simp only [BilinForm.toMatrix_apply, Module.Basis.baseChange_apply, Matrix.map_apply]
  exact polar_baseChange_tmul q K b (b i) (b j)

omit [Nonempty I] in
private theorem matrixSimilarity
    {V : Type u} [AddCommGroup V] [Module F V] [LinearOrder (I ⊕ I)]
    (q : QuadraticForm F V) (b : Module.Basis (I ⊕ I) F V)
    (H : (Matrix (I ⊕ I) (I ⊕ I) F)ˣ) (hH : BilinForm.toMatrix b q.polarBilin = H.val)
    (g : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) (c : Kˣ)
    (hg : g.val.transpose * hyperbolicGram I K * g.val = (c : K) • (extendMatrixUnit H).val)
    (h₂ : (2 : F) ≠ 0) :
    ∀ x : K ⊗[F] V,
      Specs.Arithmetic.OddSpinModels.hyperbolicForm I K
        (matrixColumnEquiv g ((b.baseChange K).equivFun x)) =
      (c : K) * coefficientForm K q b x := by
  intro x
  have h₂K : (2 : K) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap F K)).mpr h₂
  let v := (b.baseChange K).equivFun x
  have h : (Specs.Arithmetic.OddSpinModels.hyperbolicForm I K).polarBilin
      (g.val *ᵥ v) (g.val *ᵥ v) = (c : K) * (coefficientForm K q b).polarBilin x x := by
    rw [hyperbolicPolarGram, Matrix.toLinearMap₂'_apply',
      LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec (b := b.baseChange K),
      coefficientPolarMatrix, hH, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hg,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    rfl
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul] at h
  change (2 : K) * _ = (c : K) * ((2 : K) * _) at h
  rw [mul_left_comm (c : K)] at h
  exact mul_left_cancel₀ h₂K h

end Splitting

section Descent

open AlgebraicGeometry CategoryTheory.Limits
open Specs.RelativeFormComparison (fieldTest fieldMap)
open Specs.AutomorphismSequence (relativePoints restrictIso)
open Specs.Arithmetic.SpinScalarExtension (restricted)
open LinearAlgebraicGroups.Albert.SpinFunctor (vectorAction regular_vectorKernel)
open LinearAlgebraicGroups.Albert.SpinSpecification (coefficientMap)
open private spinOfPoint spinOfPoint_natural baseChange_repr_map
  coordinateTest coordinateUniversalIso coordinateGaloisMap
  coordinateUniversal_fixed coordinateSliceGalois fieldAlgebraSlice fieldAlgebraInclusion
  relativeHom_ext_of_iso relativeComparison_apply
  from LinearAlgebraicGroups.Arithmetic.OddSpinInnerDescent
open private schemeIsoEquiv from LinearAlgebraicGroups.Descent.RelativeFormComparison
open private geomConnected_baseChangedGroup smooth_baseChangedGroup
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private irreducible_of_geometricallyConnected
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private scalar_tensor_injective changeModule from LinearAlgebraicGroups.Albert.SpinFunctor
open private relativeSectionEquiv from LinearAlgebraicGroups.Descent.AutomorphismSequence

variable {F K I : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ} {G H : AffineAlgebraicGroup F}

private noncomputable def modelMatrix (M : SpinModel G D)
    (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (I ⊕ I) (I ⊕ I) F)
    (R : TestAlgebra F) (x : GroupPoints G.val R) : Matrix (I ⊕ I) (I ⊕ I) R :=
  scalarMatrixPresentation e (M.fullPoints R
    (x ≫ (M.projection ≫ M.inclusion).hom.hom)).val

set_option backward.isDefEq.respectTransparency false in
private theorem modelMatrix_natural (M : SpinModel G D)
    (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (I ⊕ I) (I ⊕ I) F)
    {R T : TestAlgebra F} (f : R ⟶ T) (x : GroupPoints G.val R) :
    modelMatrix M e T (mapPoints f x) = f.hom.toRingHom.mapMatrix (modelMatrix M e R x) := by
  change scalarMatrixPresentation e (M.fullPoints T
    (((testSpec F).map f.op ≫ x) ≫ (M.projection ≫ M.inclusion).hom.hom)).val = _
  rw [Category.assoc]
  change scalarMatrixPresentation e (M.fullPoints T
    (mapPoints f (x ≫ (M.projection ≫ M.inclusion).hom.hom))).val = _
  rw [M.fullNatural]
  exact scalarMatrixPresentation_natural e f.hom _

variable {V : Type u} [AddCommGroup V] [Module F V] [LinearOrder (I ⊕ I)]
  {q : QuadraticForm F V} (b : Module.Basis (I ⊕ I) F V)
  {h : ∀ R : TestAlgebra F, GroupPoints H.val R →* (ScalarClifford q R)ˣ}
  (hh : IsSpinPointRepresentation q H.val h)

private noncomputable def spinMatrix (R : TestAlgebra F) (x : GroupPoints H.val R) :
    Matrix (I ⊕ I) (I ⊕ I) R :=
  LinearMap.toMatrix (b.baseChange R) (b.baseChange R)
    (vectorAction q R b (spinOfPoint b hh R x)).toLinearMap

private theorem spinMatrix_natural {R T : TestAlgebra F} (f : R ⟶ T)
    (x : GroupPoints H.val R) :
    spinMatrix b hh T (mapPoints f x) = f.hom.toRingHom.mapMatrix (spinMatrix b hh R x) := by
  ext i j
  simp only [spinMatrix, RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
    Module.Basis.baseChange_apply, LinearEquiv.coe_coe]
  change _ = f.hom _
  rw [spinOfPoint_natural, ← baseChange_repr_map b f]
  have hOne : changeModule f.hom ((1 : R) ⊗ₜ[F] b j) = (1 : T) ⊗ₜ[F] b j := by
    change f.hom 1 ⊗ₜ[F] b j = _
    rw [map_one]
  rw [← hOne, ← Albert.SpinFunctor.vectorAction_naturality]

private theorem spin_eq_of_vector_and_specialization (hq : IsRegular q)
    {R T : TestAlgebra F} [IsDomain R] (f : R ⟶ T) (h₂ : (2 : T) ≠ 0)
    (x y : GroupPoints H.val R)
    (hv : spinMatrix b hh R x = spinMatrix b hh R y)
    (hf : mapPoints f x = mapPoints f y) : x = y := by
  let d := x / y
  let action := (vectorAction q R b).comp (spinOfPoint b hh R)
  have hd : vectorAction q R b (spinOfPoint b hh R d) = 1 := by
    change action (x / y) = 1
    have hxy : action x = action y := LinearEquiv.toLinearMap_injective
      ((LinearMap.toMatrix (b.baseChange R) (b.baseChange R)).injective hv)
    rw [map_div, hxy, div_self']
  obtain ⟨t, ⟨ht, hscalar⟩, _⟩ := (regular_vectorKernel q R b hq _).mp hd
  change (h R d).val = algebraMap R _ t at hscalar
  have hb : mapPoints f d = (1 : GroupPoints H.val T) := by
    change (((groupPointsFunctor F).obj H.val).map f).hom (x / y) = 1
    rw [map_div, show (((groupPointsFunctor F).obj H.val).map f).hom x =
        (((groupPointsFunctor F).obj H.val).map f).hom y from hf, div_self']
  have ht' : f.hom t = 1 := by
    have hnat := congrArg Units.val (hh.2 f d)
    change (h T (mapPoints f d)).val = coefficientMap q R f.hom (h R d).val at hnat
    rw [hb, map_one, Units.val_one] at hnat
    rw [hscalar] at hnat
    apply scalar_tensor_injective q T b
    change (f.hom t) ⊗ₜ[F] (1 : CliffordAlgebra q) = (1 : T) ⊗ₜ[F] 1
    exact hnat.symm
  have ht1 : t = 1 := by
    rcases sq_eq_one_iff.mp (show t ^ 2 = 1 by simpa only [pow_two] using ht) with ht1 | ht1
    · exact ht1
    · rw [ht1, map_neg, map_one] at ht'
      exact (h₂ (by linear_combination -ht')).elim
  have hd1 : d = 1 := by
    apply (hh.1 R).1
    apply Units.ext
    change (h R d).val = (h R 1).val
    rw [hscalar, ht1, map_one, map_one, Units.val_one]
  exact div_eq_one.mp hd1

open Specs.Unipotent (baseChangedAlgebraicGroup)
set_option backward.isDefEq.respectTransparency false in
private theorem coordinateTest_isDomain (hs : Smooth G.val.X.hom)
    (hc : GeometricallyConnected G.val.X.hom) :
    IsDomain (coordinateTest (S := K) (Specs.AdjointCocharacters.coordinateHopf G)) := by
  let G' := baseChangedAlgebraicGroup K G
  letI : Smooth G'.val.X.hom := smooth_baseChangedGroup hs
  letI : GeometricallyConnected G'.val.X.hom := geomConnected_baseChangedGroup hc
  letI := G'.property.2.1
  letI := G'.property.2.2
  letI := irreducible_of_geometricallyConnected G'.val
  letI := isReduced_of_smooth_over_field G'.val.X.hom
  letI : IsIntegral G'.val.X.left := isIntegral_of_irreducibleSpace_of_isReduced _
  let p := coordinateUniversalIso (S := K) G
  let R := coordinateTest (S := K) (Specs.AdjointCocharacters.coordinateHopf G)
  let p' : Spec (CommRingCat.of R) ≅ G'.val.X.left := (Over.forget _).mapIso p
  letI : Nonempty (Spec (CommRingCat.of R)) := Nonempty.map p'.inv inferInstance
  exact (affine_isIntegral_iff _).mp (isIntegral_of_isOpenImmersion p'.hom)

set_option backward.isDefEq.respectTransparency false in
private theorem relativeIdentitySpecialization
    (m n : relativePoints G.val (fieldTest F K) ⟶ relativePoints H.val (fieldTest F K)) :
    let R := coordinateTest (S := K) (Specs.AdjointCocharacters.coordinateHopf G)
    let U := fieldAlgebraSlice R
    let x := relativeSectionEquiv U G.val.X (coordinateUniversalIso G).hom
    ∃ f : restricted F R ⟶ restricted F (CommAlgCat.of K K),
      mapPoints f ((m.app (op U)).hom x) = mapPoints f ((n.app (op U)).hom x) := by
  intro R U x
  let p := coordinateUniversalIso (S := K) G
  let T := CommAlgCat.of K K
  let t : Points ((groupBaseChange F K).obj G.val).X T := 1
  let f₀ : (testSpec K).obj (op T) ⟶ (testSpec K).obj (op R) := t ≫ p.inv
  let ff := algSpec.fullyFaithful (R := CommRingCat.of K)
  let f : R ⟶ T := (ff.preimage f₀).unop
  have hf : (testSpec K).map f.op = f₀ := ff.map_preimage _
  let f' := (restrictTestAlgebra F K).map f
  let a : fieldAlgebraSlice T ⟶ U := Over.homMk ((testSpec F).map f'.op) (by
    change (testSpec F).map f'.op ≫ (testSpec F).map (fieldAlgebraInclusion R).op =
      (testSpec F).map (fieldAlgebraInclusion T).op
    rw [← (testSpec F).map_comp, ← op_comp]
    have hcf : fieldAlgebraInclusion R ≫ f' = fieldAlgebraInclusion T := by
      apply ConcreteCategory.hom_ext
      exact f.hom.commutes
    rw [hcf])
  have hx : mapPoints f' x = 1 := by
    change mapPoints f' (baseChangePoint F K G.val.X R p.hom) = _
    rw [← baseChangePointsNaturality, show mapPoints f p.hom = t by
      change (testSpec K).map f.op ≫ p.hom = t
      rw [hf, Category.assoc, p.inv_hom_id]
      exact Category.comp_id t]
    exact (baseChangePointGroupEquiv K G.val T).map_one
  refine ⟨f', ?_⟩
  have hm := ConcreteCategory.congr_hom (m.naturality a.op) x
  have hn := ConcreteCategory.congr_hom (n.naturality a.op) x
  change (m.app (op (fieldAlgebraSlice T))).hom (mapPoints f' x) =
    mapPoints f' ((m.app (op U)).hom x) at hm
  change (n.app (op (fieldAlgebraSlice T))).hom (mapPoints f' x) =
    mapPoints f' ((n.app (op U)).hom x) at hn
  rw [hx, map_one] at hm hn
  exact hm.symm.trans hn

set_option backward.isDefEq.respectTransparency false in
/-- A comparison compatible with the ground-field vector action is invariant under Galois.
On the universal point, its possible scalar discrepancy is determined by the identity point. -/
private theorem descendVectorCompatibleComparison [IsGalois F K]
    (M : SpinModel G D) (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (I ⊕ I) (I ⊕ I) F)
    (hG : IsAbsolutelyAlmostSimple G) (hq : IsRegular q) (h₂ : (2 : F) ≠ 0)
    (j : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val)
    (hj : ∀ (R : TestAlgebra K) (p : GroupPoints ((groupBaseChange F K).obj G.val) R),
      spinMatrix b hh (restricted F R) (baseChangePoint F K H.val.X R (p ≫ j.hom.hom.hom)) =
        modelMatrix M e (restricted F R) (baseChangePoint F K G.val.X R p)) :
    ∃ g : ∀ R : TestAlgebra F, GroupPoints G.val R →* (ScalarClifford q R)ˣ,
      IsSpinPointRepresentation q G.val g := by
  let r := schemeIsoEquiv K G.val H.val j
  have hr (σ : Gal(K/F)) : restrictIso (fieldMap F K σ) r = r := by
    let P := Specs.AdjointCocharacters.coordinateHopf G
    let R := coordinateTest (S := K) P
    let U := fieldAlgebraSlice (k := F) R
    let x := relativeSectionEquiv U G.val.X (coordinateUniversalIso G).hom
    let z := coordinateGaloisMap (k := F) (S := K) P σ
    let m := (restrictIso (fieldMap F K σ) r).hom
    let y := (r.hom.app (op U)).hom x
    apply Iso.ext
    apply relativeHom_ext_of_iso U (coordinateUniversalIso G) m r.hom
    have hx : mapPoints z x = x := coordinateUniversal_fixed G σ
    have hn := ConcreteCategory.congr_hom (r.hom.naturality (coordinateSliceGalois P σ).op) x
    change (m.app (op U)).hom (mapPoints z x) = mapPoints z y at hn
    rw [hx] at hn
    have hy : spinMatrix b hh (restricted F R) y = modelMatrix M e (restricted F R) x := by
      have hrel := relativeComparison_apply j R (coordinateUniversalIso G).hom
      change y = _ at hrel
      rw [hrel]
      exact hj R (coordinateUniversalIso G).hom
    have hv : spinMatrix b hh (restricted F R) ((m.app (op U)).hom x) =
        spinMatrix b hh (restricted F R) y := by
      rw [hn, spinMatrix_natural, hy, ← modelMatrix_natural, hx]
    letI : IsDomain (restricted F R) := coordinateTest_isDomain hG.1.1 hG.1.2.1
    obtain ⟨f, hf⟩ := relativeIdentitySpecialization m r.hom
    have h₂K : (2 : restricted F (CommAlgCat.of K K)) ≠ 0 := by
      simpa only [map_ofNat] using (map_ne_zero (algebraMap F K)).mpr h₂
    exact spin_eq_of_vector_and_specialization b hh hq f h₂K _ _ hv hf
  have hri (σ : Gal(K/F)) : restrictIso (fieldMap F K σ) r.symm = r.symm := by
    change (restrictIso (fieldMap F K σ) r).symm = r.symm
    exact congrArg Iso.symm (hr σ)
  obtain ⟨_, g, hg, _⟩ := OddSpinInnerDescent.descendCompatibleSpinComparison q H G h hh r.symm hri
  exact ⟨g, hg⟩

end Descent

section SpinComparison

open Specs.Arithmetic.SpinScalarExtension (restricted vectorComparison)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open LinearAlgebraicGroups.Albert.SpinFunctor (vectorAction vectorAction_characterization)
open LinearAlgebraicGroups.Albert.SpinSpecification (IsVectorAction vectors)
open private vectors_injective from LinearAlgebraicGroups.Albert.SpinFunctor
open private spinOfPoint spin_scheme_of_form scalarIsometryClifford
  scalarIsometryClifford_vectors vectorComparison_one fieldAlgebraInclusion
  from LinearAlgebraicGroups.Arithmetic.OddSpinInnerDescent

variable {F K I : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [Nonempty I]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ} {G H : AffineAlgebraicGroup F}

omit [Nonempty I] in
private theorem splitMatrixAt (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (I ⊕ I) (I ⊕ I) F)
    (g : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ)
    (hg : ∀ x, D.splitting x = matrixInner g (scalarMatrixPresentation e x))
    (S : TestAlgebra K)
    (E : (restricted F S ⊗[F] ρ.fixedSubalgebra) ≃ₐ[S] Matrix (I ⊕ I) (I ⊕ I) S)
    (hE : ∀ (s : S) (x : ρ.fixedSubalgebra),
      E (s ⊗ₜ[F] x) = s • x.val.map (algebraMap K S))
    (x : restricted F S ⊗[F] ρ.fixedSubalgebra) :
    E x = matrixInner (extendMatrixUnit g) (scalarMatrixPresentation e x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    have hx := hg ((1 : K) ⊗ₜ[F] x)
    rw [D.splittingFormula, scalarMatrixPresentation_tmul, one_smul, one_smul] at hx
    rw [hE, scalarMatrixPresentation_tmul, hx, map_smul]
    congr 1
    change (g.val * (e x).map (algebraMap F K) * g.inv).map (algebraMap K S) =
      g.val.map (algebraMap K S) * (e x).map (algebraMap F (restricted F S)) *
        g.inv.map (algebraMap K S)
    simp only [Matrix.map_mul, Matrix.map_map]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Nonempty I] in
set_option backward.isDefEq.respectTransparency false in
private theorem splitVectorMatrix (M : SpinModel G D)
    (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (I ⊕ I) (I ⊕ I) F)
    (g : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ)
    (hg : ∀ x, D.splitting x = matrixInner g (scalarMatrixPresentation e x))
    (S : TestAlgebra K) (p : GroupPoints ((groupBaseChange F K).obj G.val) S) :
    let P := M.splitCover
    let x := p ≫ M.splitSource.hom.hom.hom
    let y := ((groupPointsFunctor K).map (P.projection ≫ P.inclusion)).app S x
    (P.orthogonal.points S y).val.val =
      matrixInner (extendMatrixUnit g) (modelMatrix M e (restricted F S)
        (baseChangePoint F K G.val.X S p)) := by
  intro P x y
  obtain ⟨E, hE, hm⟩ := M.matrixComparison S
  let f := M.projection ≫ M.inclusion
  let a := p ≫ ((groupBaseChange F K).map f).hom.hom
  have hb : baseChangePoint F K M.full.val.X S a =
      baseChangePoint F K G.val.X S p ≫ f.hom.hom :=
    baseChangePointsSchemeNaturality F K f.hom.hom S p
  have hf : (groupBaseChange F K).map f ≫ M.splitFull.hom =
      M.splitSource.hom ≫ (P.projection ≫ P.inclusion) := by
    change (groupBaseChange F K).map (M.projection ≫ M.inclusion) ≫ _ = _
    rw [Functor.map_comp, Category.assoc, M.inclusionComparison, ← Category.assoc,
      M.projectionComparison, Category.assoc]
  have hy : a ≫ M.splitFull.hom.hom.hom = y := by
    have h := congrArg (fun f : (groupBaseChange F K).obj G.val ⟶ P.orthogonal.group.val =>
      p ≫ f.hom.hom) hf
    change (p ≫ ((groupBaseChange F K).map f).hom.hom) ≫ M.splitFull.hom.hom.hom =
      (p ≫ M.splitSource.hom.hom.hom) ≫ (P.projection ≫ P.inclusion).hom.hom
    simpa only [Grp.comp_hom_hom, Category.assoc] using h
  rw [← hy, ← hm, hb]
  exact splitMatrixAt e g hg S E hE _

omit [Nonempty I] in
private theorem hyperbolicRescale (s : Kˣ) :
    ∃ d : quadraticSimilitudes (Specs.Arithmetic.OddSpinModels.hyperbolicForm I K), d.val.2 = s := by
  let t : (I ⊕ I) → (K ≃ₗ[K] K) :=
    Sum.elim (fun _ => LinearEquiv.smulOfUnit s) (fun _ => LinearEquiv.refl K K)
  let f := LinearEquiv.piCongrRight t
  refine ⟨⟨(f, s), ?_⟩, rfl⟩
  intro x
  have hn (v : I ⊕ I → K) : Specs.Arithmetic.OddSpinModels.hyperbolicForm I K v =
      ∑ i, v (.inl i) * v (.inr i) := by
    rw [Specs.Arithmetic.OddSpinModels.hyperbolicForm, LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply']
    simp [dotProduct, Fintype.sum_sum_type, Matrix.mulVec, Matrix.one_apply]
  change Specs.Arithmetic.OddSpinModels.hyperbolicForm I K (f x) =
    (s : K) * Specs.Arithmetic.OddSpinModels.hyperbolicForm I K x
  rw [hn, hn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (s.val * x (.inl i)) * x (.inr i) = s.val * (x (.inl i) * x (.inr i))
  exact mul_assoc _ _ _

omit [Nonempty I] in
private theorem matrixColumnEquiv_apply (g : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) (x : I ⊕ I → K) :
    matrixColumnEquiv g x = g.val *ᵥ x := rfl

variable {V : Type u} [AddCommGroup V] [Module F V] [LinearOrder (I ⊕ I)]
  {q : QuadraticForm F V} (b : Module.Basis (I ⊕ I) F V)

private noncomputable def splitVectorEquiv (g : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) :
    (K ⊗[F] V) ≃ₗ[K] (I ⊕ I → K) :=
  (b.baseChange K).equivFun.trans (matrixColumnEquiv g)

omit [Nonempty I] [LinearOrder (I ⊕ I)] in
private theorem splitVectorEquiv_matrix (g : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ)
    (S : TestAlgebra K) :
    let R := restricted F S
    let L := (vectorComparison (K := F) S).symm.trans
      (LinearEquiv.baseChange K S (K ⊗[F] V) (I ⊕ I → K) (splitVectorEquiv b g))
    LinearMap.toMatrix (b.baseChange R) ((Pi.basisFun K (I ⊕ I)).baseChange S) L.toLinearMap =
      g.val.map (algebraMap K S) := by
  intro R L
  ext i j
  have hj : vectorComparison (K := F) S (1 ⊗ₜ[K] (1 ⊗ₜ[F] b j : K ⊗[F] V)) =
      (1 : R) ⊗ₜ[F] b j := by
    rw [vectorComparison_one]
    change (fieldAlgebraInclusion (k := F) S).hom (1 : K) ⊗ₜ[F] b j = _
    rw [map_one]
  rw [LinearMap.toMatrix_apply, Module.Basis.baseChange_apply]
  change (((Pi.basisFun K (I ⊕ I)).baseChange S).repr
    (LinearEquiv.baseChange K S (K ⊗[F] V) (I ⊕ I → K) (splitVectorEquiv b g)
      ((vectorComparison (K := F) S).symm ((1 : R) ⊗ₜ[F] b j)))) i = _
  rw [← hj, LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul,
    Module.Basis.baseChange_repr_tmul]
  have hbj : (b.baseChange K).equivFun ((1 : K) ⊗ₜ[F] b j) = Pi.single j 1 := by
    rw [← Module.Basis.baseChange_apply]
    funext k
    by_cases h : j = k
    · subst k
      simp
    · simp [Ne.symm h]
  simp only [Matrix.map_apply, splitVectorEquiv, LinearEquiv.trans_apply, hbj,
    matrixColumnEquiv_apply, Matrix.mulVec_single_one, Pi.basisFun_repr, Matrix.col_apply,
    Algebra.smul_def, mul_one]

private theorem transportedVectorAction
    {W : Type u} [AddCommGroup W] [Module K W]
    {Q : QuadraticForm K W} (S : TestAlgebra K)
    (A : ScalarClifford q (restricted F S) ≃ₐ[S] ScalarClifford Q S)
    (U : (restricted F S ⊗[F] V) ≃ₗ[S] (S ⊗[K] W))
    (hA : ∀ x, A (vectors q (restricted F S) x) = vectors Q S (U x))
    (a : (ScalarClifford q (restricted F S))ˣ) (a' : (ScalarClifford Q S)ˣ)
    (ha' : a' = Units.map A.toMonoidHom a)
    (v : (restricted F S ⊗[F] V) ≃ₗ[S] (restricted F S ⊗[F] V))
    (v' : (S ⊗[K] W) ≃ₗ[S] (S ⊗[K] W))
    (hv : IsVectorAction q (restricted F S) a v) (hv' : IsVectorAction Q S a' v')
    (hinj : Function.Injective (vectors Q S)) :
    ∀ x, v' (U x) = U (v x) := by
  intro x
  apply hinj
  rw [hv', ← hA, ← hA, hv, ha']
  simp only [Albert.SpinSpecification.conjugate, Units.coe_map, Units.coe_map_inv, map_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Correct the isometry by a projective similitude on the split spin scheme so
that the comparison induces the original vector map in the recovered coordinates. -/
private theorem splitSpinComparison (projectiveAction : SplitProjectiveSpinAction.{u})
    (M : SpinModel G D) (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (I ⊕ I) (I ⊕ I) F)
    (g : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) (c : Kˣ)
    (hg : ∀ x, D.splitting x = matrixInner g (scalarMatrixPresentation e x))
    (hc : ∀ x, Specs.Arithmetic.OddSpinModels.hyperbolicForm I K (splitVectorEquiv b g x) =
      (c : K) * coefficientForm K q b x)
    (h : ∀ R : TestAlgebra F, GroupPoints H.val R →* (ScalarClifford q R)ˣ)
    (hh : IsSpinPointRepresentation q H.val h) :
    ∃ j : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val,
      ∀ (S : TestAlgebra K) (p : GroupPoints ((groupBaseChange F K).obj G.val) S),
        spinMatrix b hh (restricted F S) (baseChangePoint F K H.val.X S (p ≫ j.hom.hom.hom)) =
          modelMatrix M e (restricted F S) (baseChangePoint F K G.val.X S p) := by
  let Q := coefficientForm K q b
  let q₀ := Specs.Arithmetic.OddSpinModels.hyperbolicForm I K
  let P := M.splitCover
  obtain ⟨d, hd⟩ := hyperbolicRescale (I := I) c⁻¹
  let T : Q.IsometryEquiv q₀ :=
    ⟨(splitVectorEquiv b g).trans d.val.1, fun x => by
      change q₀ (d.val.1 (splitVectorEquiv b g x)) = Q x
      have hform (v : I ⊕ I → K) : q₀ (d.val.1 v) = (d.val.2 : K) * q₀ v := d.property v
      rw [hform, hd, hc, ← mul_assoc, Units.inv_mul, one_mul]⟩
  obtain ⟨B, hK, hB, _, _, _, _, hpoint, hhK, _⟩ :=
    SpinScalarExtension.spinRepresentationExtension (F := K) q b H h hh
  obtain ⟨j₀, hj₀⟩ := OddSpinInnerDescent.spinIsometryGroupComparison Q q₀ T
    (baseChangedAlgebraicGroup K H) P.spin hK P.spinPoints hhK P.spinRepresents
  obtain ⟨_, A, _, _, _, _, hvA, _⟩ := projectiveAction K I P
  let j := M.splitSource ≪≫ A d ≪≫ j₀.symm
  refine ⟨j, ?_⟩
  intro S p
  let R := restricted F S
  let x := p ≫ M.splitSource.hom.hom.hom
  let y := x ≫ (A d).hom.hom.hom
  let t := y ≫ j₀.inv.hom.hom
  let z := baseChangePoint F K H.val.X S t
  have he : p ≫ j.hom.hom.hom = t := by
    simp only [j, t, y, x, Iso.trans_hom, Iso.symm_hom, Grp.comp_hom_hom,
      Category.assoc]
  rw [he]
  obtain ⟨v, hv, hm⟩ := P.vector S x
  let b₀ := Pi.basisFun K (I ⊕ I)
  let u := LinearEquiv.baseChange K S (I ⊕ I → K) (I ⊕ I → K) d.val.1
  have hy : IsVectorAction q₀ S (P.spinPoints S y) (u * v * u⁻¹) := hvA S d x v hv
  have ht : t ≫ j₀.hom.hom.hom = y := by
    have hid := congrArg (fun f : P.spin.val ⟶ P.spin.val => f.hom.hom) j₀.inv_hom_id
    change _ ≫ _ = _ at hid
    change (y ≫ j₀.inv.hom.hom) ≫ j₀.hom.hom.hom = y
    rw [Category.assoc, hid]
    exact Category.comp_id y
  let C := (B S).trans (scalarIsometryClifford T S)
  have hpointC : P.spinPoints S y = Units.map C.toMonoidHom (h R z) := by
    have h₁ := congrArg Units.val (hj₀ S t)
    rw [ht] at h₁
    have h₂ := congrArg Units.val (hpoint S t)
    apply Units.ext
    change (P.spinPoints S y).val = scalarIsometryClifford T S (B S (h R z).val)
    exact h₁.trans (congrArg (scalarIsometryClifford T S) h₂)
  let U := (vectorComparison (K := F) S).symm.trans
    (LinearEquiv.baseChange K S (K ⊗[F] V) (I ⊕ I → K) T.toLinearEquiv)
  have hC (a : R ⊗[F] V) : C (vectors q R a) = vectors q₀ S (U a) := by
    obtain ⟨a, rfl⟩ := (vectorComparison (K := F) S).surjective a
    change scalarIsometryClifford T S (B S (vectors q R (vectorComparison (K := F) S a))) =
      vectors q₀ S (U (vectorComparison (K := F) S a))
    rw [hB, scalarIsometryClifford_vectors]
    simp only [U, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  let w := vectorAction q R b (spinOfPoint b hh R z)
  have hw : IsVectorAction q R (h R z) w :=
    vectorAction_characterization q R b (spinOfPoint b hh R z)
  have hcomm := transportedVectorAction (q := q) S C U hC (h R z) (P.spinPoints S y)
    hpointC w (u * v * u⁻¹) hw hy (vectors_injective q₀ S b₀)
  let L := (vectorComparison (K := F) S).symm.trans
    (LinearEquiv.baseChange K S (K ⊗[F] V) (I ⊕ I → K) (splitVectorEquiv b g))
  have hU (a : R ⊗[F] V) : U a = u (L a) := by
    change ((splitVectorEquiv b g).trans d.val.1).baseChange K S _ _
        ((vectorComparison (K := F) S).symm a) = _
    rw [LinearEquiv.baseChange_trans]
    rfl
  have hcomm' : L.toLinearMap.comp w.toLinearMap = v.toLinearMap.comp L.toLinearMap := by
    apply LinearMap.ext
    intro a
    apply u.injective
    have h' := hcomm a
    rw [hU, hU] at h'
    change u (v (u.symm (u (L a)))) = u (L (w a)) at h'
    rw [LinearEquiv.symm_apply_apply] at h'
    exact h'.symm
  let bR := b.baseChange R
  let bS := b₀.baseChange S
  have hLm : LinearMap.toMatrix bR bS L.toLinearMap = (extendMatrixUnit g).val :=
    splitVectorEquiv_matrix b g S
  have hvm : LinearMap.toMatrix bS bS v.toLinearMap =
      matrixInner (extendMatrixUnit g) (modelMatrix M e R (baseChangePoint F K G.val.X S p)) := by
    exact hm.trans (splitVectorMatrix M e g hg S p)
  have hprod := congrArg (LinearMap.toMatrix bR bS) hcomm'
  rw [LinearMap.toMatrix_comp bR bR bS, LinearMap.toMatrix_comp bR bS bS,
    hLm, hvm] at hprod
  let a := extendMatrixUnit (R := S) g
  let m := modelMatrix M e R (baseChangePoint F K G.val.X S p)
  change a.val * spinMatrix b hh R z = (a.val * m * a.inv) * a.val at hprod
  rw [mul_assoc (a.val * m), a.inv_val, mul_one] at hprod
  exact a.isUnit.mul_left_cancel hprod

set_option backward.isDefEq.respectTransparency false in
private theorem scalarSpinRepresentation [IsGalois F K]
    (projectiveAction : SplitProjectiveSpinAction.{u})
    (M : SpinModel G D) (hG : IsAbsolutelyAlmostSimple G) (h₂ : (2 : F) ≠ 0)
    (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (I ⊕ I) (I ⊕ I) F)
    (H₀ : (Matrix (I ⊕ I) (I ⊕ I) F)ˣ)
    (hH : LinearMap.BilinForm.toMatrix b q.polarBilin = H₀.val)
    (he : ∀ x, e (D.involution.toLinearMap x) = gramAdjoint H₀ (e x))
    (hq : IsRegular q) :
    ∃ h : ∀ R : TestAlgebra F, GroupPoints G.val R →* (ScalarClifford q R)ˣ,
      IsSpinPointRepresentation q G.val h := by
  obtain ⟨g, c, hg, hc⟩ := splitMatrixComparison D e H₀ he
  obtain ⟨H, h, hh⟩ := spin_scheme_of_form q b
  have hc' (x : K ⊗[F] V) :=
    matrixSimilarity (K := K) q b H₀ hH g c hc h₂ x
  obtain ⟨j, hj⟩ := splitSpinComparison b projectiveAction M e g c hg hc' h hh
  exact descendVectorCompatibleComparison b hh M e hG hq h₂ j hj

end SpinComparison


private theorem densityFromScalarModel (fieldModel : FieldOrthogonalModel.{u})
    (projectiveAction : SplitProjectiveSpinAction.{u}) :
    Specs.Arithmetic.ScalarEvenSpinLocalDensity.Statement.{u} := by
  classical
  intro F K I _ _ _ _ _ _ _ _ _ h₂ hrank G hG _ ρ D M horth r e c hc i
  letI : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  letI : LinearOrder (I ⊕ I) :=
    LinearOrder.lift' (Fintype.equivFin (I ⊕ I)) (Fintype.equivFin (I ⊕ I)).injective
  obtain ⟨E, H, q, b, hq, hH, hE⟩ := recoverOrthogonalForm fieldModel D h₂ horth e
  obtain ⟨spin, hspin⟩ := scalarSpinRepresentation b projectiveAction M hG h₂ E H hH hE hq
  exact densityOfRadicalGeneration (radicalGenerationOfSpinRepresentation hG q b spin hq hspin c hc) i

theorem scalarEvenSpinLocalDensity : Specs.Arithmetic.ScalarEvenSpinLocalDensity.Statement.{u} :=
  densityFromScalarModel NontrialitarianSpinModels.fieldOrthogonalModel
    NontrialitarianSpinModels.splitProjectiveSpinAction

end LinearAlgebraicGroups.Arithmetic.ScalarEvenSpinLocalDensity
