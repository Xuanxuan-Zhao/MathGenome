import Specs.LinearAlgebraicGroups.Arithmetic.LocalMixingHermitianRankOne
import LinearAlgebraicGroups.Arithmetic.IsotropicOuterTypeA
import LinearAlgebraicGroups.Relative.RelativeChambers
import LinearAlgebraicGroups.Reductive.NontrivialRationalTorus
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct Matrix LaurentPolynomial

universe u

namespace LinearAlgebraicGroups.Arithmetic.LocalMixingHermitianRankOne

open LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Arithmetic.LocalMixingHermitianRankOne
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open Specs.Arithmetic.OuterTypeALocalModels (RepresentsHermitian)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (IsReductive)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Specs.Relative.RelativeChambers (IsRegular)
open CocharacterDynamics
open Specs.Arithmetic.HermitianRadicalComparison
open Specs.HermitianMatrixGeneration (Space)
open Specs.UnitaryRankOne (quadraticConjugation)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters diagonalGroup)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open IsotropicOuterTypeA.Spec (hyperbolicMatrix hyperbolicComparison)
open LinearAlgebraicGroups.StandardGroups (specialLinearGroup specialLinearGroupPointsIso)
open private opposite_point centralizes_onAlgebras from
  LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open LinearAlgebraicGroups.StandardGroups (generalLinearGroup generalLinearGroupPointsIso)
open RationalRepresentations
open private coactionOperator coactionOperator_apply_tmul coactionOperator_toMatrix
  representation_point_matrix from LinearAlgebraicGroups.Reductive.NontrivialRationalTorus
open private factorAt firstFactor_natural from LinearAlgebraicGroups.Arithmetic.IsotropicOuterTypeA
open private liftSpecialLinear from LinearAlgebraicGroups.Descent.InnerTypeA
open private unitEquiv unitEquiv_unitPoint unitPointHom unitPointHom_apply from
  LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private change_tmul weight_swap swap_pair regular_iff_stabilizes matrix_injective matrix_mul matrix_one
  from LinearAlgebraicGroups.Arithmetic.HermitianRadicalComparison

open private formOfMatrix formOfMatrix_nondegenerate adjointMatrix hyperbolicPartner
  adaptedModel AdaptedBasis AdaptedBasis.mk gram_of_adapted_basis
  matricesOfEquiv_mul matrixPairing matrixPairing_change ground_conjugation
  changedGram changedGram_hermitian modelInBasis AdaptedBasis.first AdaptedBasis.last
  from LinearAlgebraicGroups.Arithmetic.IsotropicOuterTypeA
open LocalAlgebraicTransport (pointTopology)
open private splitTorusImage splitTorusUpperBound from LinearAlgebraicGroups.Relative.MaximalSplitTori
open private factor_group_through_subgroup subgroupOf_trans
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private gm_split reductive_of_semisimple from LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
open private conj_conj from LinearAlgebraicGroups.Arithmetic.UnitaryRankOne

open private testPointSections from LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private rationalSourceIso from LinearAlgebraicGroups.Relative.RationalDensity

noncomputable section

set_option maxHeartbeats 90000
set_option backward.isDefEq.respectTransparency false

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable {G : AffineAlgebraicGroup F}

private abbrev groundAlgebra (F : Type u) [Field F] : TestAlgebra F := CommAlgCat.of F F

private theorem rational_limit_mem {a : Cocharacter G.val} (D : LimitDecomposition a)
    (y : (𝟙_ (SchemeOver F)) ⟶ G.val.X)
    (hy : y ∈ SubgroupSections D.contracting (𝟙_ (SchemeOver F))) :
    HasLimit a ((testPointSections G.val).symm y) 1 := by
  obtain ⟨s, hs⟩ := hy
  change s ≫ D.contracting.inclusion.hom.hom = y at hs
  subst y
  let R := groundAlgebra F
  let q : GroupPoints D.contracting.group R := (rationalSourceIso F).inv ≫ s
  apply (D.contracting_points R _).2
  refine ⟨q, ?_⟩
  change ((rationalSourceIso F).inv ≫ s) ≫ D.contracting.inclusion.hom.hom =
    (rationalSourceIso F).inv ≫ (s ≫ D.contracting.inclusion.hom.hom)
  exact Category.assoc _ _ _

private theorem subgroup_closure_eq_top {K L : Type*} [Group K] [Group L]
    (e : K ≃* L) (U V : Subgroup K) (hgen : U ⊔ V = ⊤) (s t : Set L)
    (hs : ∀ x ∈ U, e x ∈ s) (ht : ∀ x ∈ V, e x ∈ t) :
    Subgroup.closure (s ∪ t) = ⊤ := by
  let B := Subgroup.closure (s ∪ t)
  have hU : U ≤ B.comap e.toMonoidHom :=
    fun h hx => Subgroup.subset_closure (Or.inl (hs h hx))
  have hV : V ≤ B.comap e.toMonoidHom :=
    fun h hx => Subgroup.subset_closure (Or.inr (ht h hx))
  have hUV : U ⊔ V ≤ B.comap e.toMonoidHom := sup_le hU hV
  rw [hgen] at hUV
  apply (Subgroup.eq_top_iff' B).2
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  exact hUV (Subgroup.mem_top y)

set_option maxHeartbeats 110000 in
private theorem limitSubgroups_generate [Infinite F]
    (hG : IsAbsolutelyAlmostSimple G)
    (hgen : unipotentGenerated G = ⊤)
    (d : Cocharacter G.val)
    (hd : ∃ (X : SchemeOver F) (g : X ⟶ G.val.X), ¬ Centralizes d g)
    (D : LimitDecomposition d) (D' : LimitDecomposition (oppositeCocharacter d)) :
    let R := CommAlgCat.of F F
    Subgroup.closure ({g : GroupPoints G.val R | HasLimit d g 1} ∪
      {g : GroupPoints G.val R | HasLimit (oppositeCocharacter d) g 1}) = ⊤ := by
  dsimp only
  let R := groundAlgebra F
  let T := 𝟙_ (SchemeOver F)
  let U := SubgroupSections D.contracting T
  let V := SubgroupSections D'.contracting T
  have htwo : U ⊔ V = unipotentGenerated G := RelativeRayGeneration.twoRadicalsGenerate (k := F) G hG d hd D D'
  have htop : U ⊔ V = ⊤ := htwo.trans hgen
  let e : (T ⟶ G.val.X) ≃* GroupPoints G.val R := (testPointSections G.val).symm
  exact subgroup_closure_eq_top e U V htop
    {x : GroupPoints G.val R | HasLimit d x 1}
    {x : GroupPoints G.val R | HasLimit (oppositeCocharacter d) x 1}
    (rational_limit_mem D) (rational_limit_mem D')


section HyperbolicModel

variable [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
variable {G : AffineAlgebraicGroup F}

local notation "σ" => quadraticConjugation F E

private abbrev PlaneCoordinates (m : ℕ) := Fin 2 ⊕ ULift.{u} (Fin m)

private def hyperbolicBasis (W : Type u) [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] :
    Module.Basis (PlaneCoordinates.{u} (Module.finrank E W)) E (Space E W) :=
  let e : ((E × E) × W) ≃ₗ[E] Space E W :=
    (LinearEquiv.prodAssoc E E E W).trans
      ((LinearEquiv.refl E E).prodCongr (LinearEquiv.prodComm E E W))
  (((Module.Basis.finTwoProd E).prod (Module.finBasis E W)).map e).reindex
    (Equiv.sumCongr (Equiv.refl _) Equiv.ulift.symm)

private theorem hyperbolicBasis_adapted (W : Type u) [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] :
    AdaptedBasis (hyperbolicBasis (E := E) W)
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)) := by
  refine AdaptedBasis.mk (fun h => (show (0 : Fin 2) ≠ 1 by decide) (Sum.inl.inj h)) ?_ ?_ ?_
  · simp [hyperbolicBasis, Module.Basis.finTwoProd_zero]
  · simp [hyperbolicBasis, Module.Basis.finTwoProd_one]
  · rintro (i | ⟨j⟩) h0 h1
    · fin_cases i <;> contradiction
    · exact ⟨Module.finBasis E W j.down, by simp [hyperbolicBasis]⟩

private theorem exists_hyperbolic_model {n : ℕ}
    (H : (Matrix (Fin n) (Fin n) E)ˣ)
    (hH : (H.val.map σ).transpose = H.val)
    (hisotropic : ∃ x : Fin n → E, x ≠ 0 ∧ dotProduct (σ ∘ x) (H.val.mulVec x) = 0)
    (hmodel : RepresentsHermitian σ H.val G) :
    ∃ (m : ℕ) (B : (Matrix (PlaneCoordinates.{u} m) (PlaneCoordinates.{u} m) E)ˣ)
      (_ : Model G σ B.val),
      (B.val.map σ).transpose = B.val ∧
        HyperbolicPair B.val (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)) := by
  obtain ⟨e, he, hee⟩ := hisotropic
  let h := formOfMatrix H.val hH
  have hnondeg := formOfMatrix_nondegenerate H hH
  obtain ⟨f, hef, hff⟩ := hyperbolicPartner h e he hee hnondeg
  let W := h.hyperbolicComplement e f
  obtain ⟨_, c, _, hc⟩ := HermitianMatrixGeneration.hyperbolicCoordinates h e f hee hff hef
  let b := hyperbolicBasis (E := E) W
  obtain ⟨B, M, hB, hcoords⟩ := adaptedModel H hH hmodel (h.restrict W) c hc b
  exact ⟨Module.finrank E W, B, M, hB, gram_of_adapted_basis (hyperbolicBasis_adapted W) hcoords⟩

end HyperbolicModel

private def diagonalEntry {R : TestAlgebra F} (t : Rˣ) (i : RankOneIndex.{u}) : R :=
  if i.down = 0 then (t : R) else (↑t⁻¹ : R)

private def specialLinearDiagonal (R : TestAlgebra F) :
    Rˣ →* Matrix.SpecialLinearGroup RankOneIndex.{u} R :=
  MonoidHom.mk' (fun t => ⟨Matrix.diagonal (diagonalEntry t), by
    rw [Matrix.det_diagonal]
    let a (i : Fin 2) : R := if i = 0 then (t : R) else (↑t⁻¹ : R)
    rw [Fintype.prod_equiv (Equiv.ulift : RankOneIndex.{u} ≃ Fin 2)
      (diagonalEntry t) a (fun _ => rfl), Fin.prod_univ_two]
    exact t.val_inv⟩) (fun t s => Subtype.ext (by
      change Matrix.diagonal (diagonalEntry (t * s)) =
        Matrix.diagonal (diagonalEntry t) * Matrix.diagonal (diagonalEntry s)
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      by_cases hi : i.down = 0 <;> simp [diagonalEntry, hi, mul_comm]))

private abbrev MultiplicativeGroup (F : Type u) [Field F] :=
  specGroup (groupAlgebra F IntegerCharacters)

private theorem exists_rankOneDiagonal :
    ∃ b : Cocharacter (specialLinearGroup F RankOneIndex.{u}).val,
      ∀ (R : TestAlgebra F) (t : Rˣ),
        (show Matrix.SpecialLinearGroup RankOneIndex.{u} R from
          (specialLinearGroupPointsIso F RankOneIndex.{u}).hom.app R (cocharacterPoint b R t)).val =
          Matrix.diagonal (diagonalEntry t) := by
  let L := specialLinearGroup F RankOneIndex.{u}
  let e := specialLinearGroupPointsIso F RankOneIndex.{u}
  let A := MultiplicativeGroup F
  let δ : (groupPointsFunctor F).obj A ⟶ Specs.StandardGroups.specialLinearPoints F RankOneIndex.{u} :=
    { app := fun R => show GrpCat.of (GroupPoints A R) ⟶
        GrpCat.of (Matrix.SpecialLinearGroup RankOneIndex.{u} R) from
          GrpCat.ofHom ((specialLinearDiagonal R).comp (unitEquiv R).toMonoidHom)
      naturality := by
        intro R S a
        apply GrpCat.ext
        intro x
        obtain ⟨t, rfl⟩ : ∃ t : Rˣ, unitPoint R t = x :=
          ⟨unitEquiv R x, (unitEquiv R).injective (unitEquiv_unitPoint R _)⟩
        change specialLinearDiagonal S (unitEquiv S (mapPoints a (unitPoint R t))) =
          Matrix.SpecialLinearGroup.map a.hom.toRingHom
            (specialLinearDiagonal R (unitEquiv R (unitPoint R t)))
        rw [mapPoints_unitPoint, unitEquiv_unitPoint, unitEquiv_unitPoint]
        apply Subtype.ext
        change Matrix.diagonal (diagonalEntry (Units.map a.hom.toMonoidHom t)) =
          (Matrix.diagonal (diagonalEntry t)).map a.hom
        rw [Matrix.diagonal_map (map_zero a.hom)]
        congr 1
        funext i
        by_cases hi : i.down = 0 <;> simp [diagonalEntry, hi] }
  obtain ⟨b, hb⟩ := (groupHomComparison F A L.val (inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (MonoidAlgebra F IntegerCharacters)))))).2 (δ ≫ e.inv)
  refine ⟨b, fun R t => ?_⟩
  have h : (groupPointsFunctor F).map b ≫ e.hom = δ := by
    change (groupPointsFunctor F).map b = δ ≫ e.inv at hb
    exact (congrArg (· ≫ e.hom) hb).trans (by simp)
  have he := DFunLike.congr_fun (congrArg (fun n => (n.app R).hom) h) (unitPoint R t)
  change e.hom.app R (cocharacterPoint b R t) =
    specialLinearDiagonal R (unitEquiv R (unitPoint R t)) at he
  rw [he, unitEquiv_unitPoint]
  rfl

section Contraction

variable {A : AffineAlgebraicGroup F}

private def transvectionHom {R : TestAlgebra F}
    (j : A.val ⟶ G.val)
    (e : (groupPointsFunctor F).obj A.val ≅ Specs.StandardGroups.specialLinearPoints F RankOneIndex.{u}) :
    Matrix.SpecialLinearGroup RankOneIndex.{u} R →* GroupPoints G.val R :=
  (((groupPointsFunctor F).map j).app R).hom.comp (e.inv.app R).hom

private theorem map_transvection {R T : TestAlgebra F} (a : R ⟶ T)
    {i k : RankOneIndex.{u}} (hik : i ≠ k) (x : R) :
    Matrix.SpecialLinearGroup.map a.hom.toRingHom (Matrix.SpecialLinearGroup.transvection hik x) =
      Matrix.SpecialLinearGroup.transvection hik (a.hom x) := by
  apply Subtype.ext
  change (1 + Matrix.single i k x : Matrix RankOneIndex.{u} RankOneIndex.{u} R).map a.hom =
    1 + Matrix.single i k (a.hom x)
  rw [Matrix.map_add a.hom a.hom.map_add, Matrix.map_one a.hom a.hom.map_zero a.hom.map_one,
    Matrix.map_single i k x a.hom]

private theorem transvectionPoint_natural
    (j : A.val ⟶ G.val)
    (e : (groupPointsFunctor F).obj A.val ≅ Specs.StandardGroups.specialLinearPoints F RankOneIndex.{u})
    {R T : TestAlgebra F} (a : R ⟶ T) {i k : RankOneIndex.{u}} (hik : i ≠ k) (x : R) :
    (mapPoints a (transvectionPoint j e R hik x) : GroupPoints G.val T) =
      transvectionPoint j e T hik (a.hom x) := by
  let δ' := e.inv ≫ (groupPointsFunctor F).map j
  have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (δ'.naturality a))
    (Matrix.SpecialLinearGroup.transvection hik x)
  have h' := map_transvection a hik x
  exact ((congrArg ((δ'.app T).hom) h').symm.trans h).symm

private theorem transvectionPoint_zero
    (j : A.val ⟶ G.val)
    (e : (groupPointsFunctor F).obj A.val ≅ Specs.StandardGroups.specialLinearPoints F RankOneIndex.{u})
    (R : TestAlgebra F) {i k : RankOneIndex.{u}} (hik : i ≠ k) :
    transvectionPoint j e R hik 0 = 1 := by
  change transvectionHom j e (Matrix.SpecialLinearGroup.transvection hik (0 : R)) = 1
  rw [Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one]

private theorem transvection_hasLimit_of_scaling
    (j : A.val ⟶ G.val)
    (e : (groupPointsFunctor F).obj A.val ≅ Specs.StandardGroups.specialLinearPoints F RankOneIndex.{u})
    (c : Cocharacter G.val) {i k : RankOneIndex.{u}} (hik : i ≠ k) {m : ℕ} (hm : 0 < m)
    (hscale : ∀ (R : TestAlgebra F) (t : Rˣ) (x : R),
      cocharacterPoint c R t * transvectionPoint j e R hik x * (cocharacterPoint c R t)⁻¹ =
        transvectionPoint j e R hik ((t ^ m).val * x))
    (R : TestAlgebra F) (x : R) : HasLimit c (transvectionPoint j e R hik x) 1 := by
  let p : polynomialAlgebra R := Polynomial.X ^ m * Polynomial.C x
  refine ⟨transvectionPoint j e (polynomialAlgebra R) hik p, ?_, ?_⟩
  · rw [transvectionPoint_natural]
    unfold orbit
    rw [transvectionPoint_natural, hscale]
    congr 1
    change Polynomial.toLaurent p =
      ((laurentParameter R) ^ m).val * LaurentPolynomial.C x
    rw [show ((laurentParameter R) ^ m).val =
        (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial R) ^ m from (Units.val_pow_eq_pow_val ..),
      LaurentPolynomial.T_pow]
    simp [p, Polynomial.toLaurent_X_pow]
  · rw [transvectionPoint_natural, ← transvectionPoint_zero j e R hik]
    congr 1
    change (Polynomial.aevalTower (AlgHom.id F R) (0 : R)) p = 0
    simp [p, hm.ne']

private theorem localField_infinite (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : Infinite F := by
  obtain ⟨v, hv, hv1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := F)
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective v
  apply Infinite.of_injective (fun n : ℕ => a ^ n)
  intro m n hmn
  apply pow_right_injective₀ hv hv1.ne
  simpa only [map_pow, ha] using congrArg (ValuativeRel.valuation F) hmn

end Contraction

section Plane

open Matrix hiding gram diagonal
open IsotropicOuterTypeA
variable [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
variable {J : Type u} [Fintype J] [DecidableEq J]

local notation "σ" => quadraticConjugation F E
local notation "i₀" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ J)
local notation "i₁" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ J)

/-- Place the determinant-one matrix on the trace-zero rescaled plane and
act by the identity on its perpendicular complement. The two diagonal
basis changes with entries `(α, 1)` and `(1, α⁻¹)` differ by a scalar on
the plane, so their conjugation of the plane matrix agrees. -/
private def planeMatrix (α : Eˣ) {R : TestAlgebra F} (X : Matrix RankOneIndex.{u}
    RankOneIndex.{u} R) : Matrix (Fin 2 ⊕ J) (Fin 2 ⊕ J) (Coeff E R) :=
  fromBlocks (hyperbolicComparison α (X.submatrix ULift.up ULift.up)) 0 0 1

omit [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [Fintype J] in
private theorem gram_blocks {H : Matrix (Fin 2 ⊕ J) (Fin 2 ⊕ J) E}
    (h : HyperbolicPair H i₀ i₁) (R : TestAlgebra F) :
    gram H R = fromBlocks (hyperbolicMatrix (Coeff E R)) 0 0
      ((gram H R).submatrix Sum.inr Sum.inr) := by
  ext (i | i) (j | j)
  · fin_cases i <;> fin_cases j <;> simp [gram, h.row_e, h.row_f, hyperbolicMatrix, ← Algebra.TensorProduct.one_def]
  · fin_cases i <;> simp [gram, h.row_e, h.row_f]
  · fin_cases j <;> simp [gram, h.col_e, h.col_f]
  · rfl

private theorem planeMatrix_det_preserves
    {H : Matrix (Fin 2 ⊕ J) (Fin 2 ⊕ J) E} (h : HyperbolicPair H i₀ i₁)
    {α : Eˣ}
    (hcmp : ∀ (R : TestAlgebra F) (B : Matrix (Fin 2) (Fin 2) R), B.det = 1 →
      let X := hyperbolicComparison α B
      X.det = 1 ∧ (X.map (conjugation σ R)).transpose *
        hyperbolicMatrix (Coeff E R) * X = hyperbolicMatrix (Coeff E R))
    (R : TestAlgebra F) (X : Matrix.SpecialLinearGroup RankOneIndex.{u} R) :
    (planeMatrix (J := J) α X.val).det = 1 ∧ Preserves σ H (planeMatrix α X.val) := by
  have hd : (X.val.submatrix ULift.up ULift.up).det = 1 :=
    (det_submatrix_equiv_self Equiv.ulift.symm X.val).trans X.property
  obtain ⟨hdet, hpres⟩ := hcmp R _ hd
  constructor
  · rw [planeMatrix, det_fromBlocks_zero₂₁, det_one, mul_one, hdet]
  · unfold Preserves planeMatrix
    rw [gram_blocks h, fromBlocks_map]
    simp only [Matrix.map_zero, Matrix.map_one, map_zero, map_one,
      fromBlocks_transpose, transpose_zero, transpose_one]
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, one_mul,
      mul_one, hpres]

omit [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] in
private theorem planeMatrix_mul {α : Eˣ}
    (hcmp : ∀ (R : TestAlgebra F) (B D : Matrix (Fin 2) (Fin 2) R),
      hyperbolicComparison (F := F) α (B * D) = hyperbolicComparison α B * hyperbolicComparison α D)
    (R : TestAlgebra F) (X Y : Matrix RankOneIndex.{u} RankOneIndex.{u} R) :
    planeMatrix (J := J) α (X * Y) = planeMatrix α X * planeMatrix α Y := by
  unfold planeMatrix
  rw [← submatrix_mul_equiv X Y ULift.up Equiv.ulift.symm ULift.up, hcmp]
  simp only [fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, one_mul]
  rfl

omit [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [Fintype J] in
private theorem planeMatrix_injective {α : Eˣ} (R : TestAlgebra F)
    (hcmp : Function.Injective (hyperbolicComparison (F := F) (R := R) α)) :
    Function.Injective (planeMatrix (J := J) (R := R) α) := by
  intro X Y h
  exact (Matrix.reindex Equiv.ulift Equiv.ulift).injective
    (hcmp (Matrix.fromBlocks_inj.mp h).1)

private theorem rankOneEmbedding
    {H : Matrix (Fin 2 ⊕ J) (Fin 2 ⊕ J) E} (h : HyperbolicPair H i₀ i₁) (M : Model G σ H) :
    ∃ (α : Eˣ)
      (j : (specialLinearGroup F RankOneIndex.{u}).val ⟶ G.val),
      IsClosedImmersion j.hom.hom.left ∧
      ∀ (R : TestAlgebra F) (x : GroupPoints (specialLinearGroup F RankOneIndex.{u}).val R),
        M.matrix (((groupPointsFunctor F).map j).app R x) =
          planeMatrix α
            (show Matrix.SpecialLinearGroup RankOneIndex.{u} R from
              (specialLinearGroupPointsIso F RankOneIndex.{u}).hom.app R x).val := by
  obtain ⟨α, _, hcmp, hnatural⟩ := IsotropicOuterTypeA.hyperbolicSpecialUnitary (F := F) (E := E)
  let S := specialLinearGroup F RankOneIndex.{u}
  let P := Specs.StandardGroups.specialLinearPoints F RankOneIndex.{u}
  let e := specialLinearGroupPointsIso F RankOneIndex.{u}
  have hgood (R : TestAlgebra F) (B : Matrix.SpecialLinearGroup RankOneIndex.{u} R) :=
    planeMatrix_det_preserves h (α := α) (fun T X hX =>
      ((hcmp T).2.2.2.1 (hyperbolicComparison α X)).2 ⟨X, hX, rfl⟩) R B
  let liftPoint (R : TestAlgebra F) (B : Matrix.SpecialLinearGroup RankOneIndex.{u} R) :
      GroupPoints G.val R :=
    (M.point R).symm ⟨⟨planeMatrix (J := J) α B.val, (hgood R B).1⟩, (hgood R B).2⟩
  have hlift (R : TestAlgebra F) (B : Matrix.SpecialLinearGroup RankOneIndex.{u} R) :
      M.matrix (liftPoint R B) = planeMatrix α B.val :=
    congrArg (fun y => y.val.val) ((M.point R).apply_symm_apply _)
  let f (R : TestAlgebra F) :
      Matrix.SpecialLinearGroup RankOneIndex.{u} R →* GroupPoints G.val R :=
    MonoidHom.mk' (liftPoint R) (fun X Y => by
      apply matrix_injective M _
      rw [matrix_mul, hlift, hlift, hlift]
      exact planeMatrix_mul (fun T => (hcmp T).2.2.1) R X.val Y.val)
  let δ : P ⟶ (groupPointsFunctor F).obj G.val :=
    { app := fun R =>
        show GrpCat.of (Matrix.SpecialLinearGroup RankOneIndex.{u} R) ⟶
          GrpCat.of (GroupPoints G.val R) from GrpCat.ofHom (f R)
      naturality := by
        intro R T a
        apply GrpCat.ext
        intro B
        change liftPoint T (Matrix.SpecialLinearGroup.map a.hom.toRingHom B) =
          (mapPoints a (liftPoint R B) : GroupPoints G.val T)
        apply matrix_injective M _
        rw [show M.matrix (mapPoints a (liftPoint R B)) =
          (M.matrix (liftPoint R B)).map (changeCoefficients a) from M.natural a _,
          hlift, hlift]
        unfold planeMatrix
        rw [fromBlocks_map]
        simp only [Matrix.map_zero, Matrix.map_one, map_zero, map_one]
        congr 1
        change hyperbolicComparison α ((B.val.submatrix ULift.up ULift.up).map a.hom) =
          (hyperbolicComparison α (B.val.submatrix ULift.up ULift.up)).map
            (Algebra.TensorProduct.map a.hom (AlgHom.id F E))
        exact (hnatural a.hom (B.val.submatrix ULift.up ULift.up)).symm }
  obtain ⟨j, hj⟩ := (groupHomComparison F S.val G.val S.property.1).2 (e.hom ≫ δ)
  have hjR (R : TestAlgebra F) (x : GroupPoints S.val R) :
      ((groupPointsFunctor F).map j).app R x = liftPoint R (e.hom.app R x) := by
    change (groupPointsFunctor F).map j = e.hom ≫ δ at hj
    rw [hj]
    rfl
  refine ⟨α, j, ?_, fun R x => (congrArg M.matrix (hjR R x)).trans (hlift R _)⟩
  apply RootData.RootGroups.isClosedImmersion_of_injectivePoints S G j
  intro R x y hxy
  apply ((e.app R).groupIsoToMulEquiv).injective
  apply Subtype.ext
  apply planeMatrix_injective R (hcmp R).1 (α := α) (J := J)
  exact (hlift R _).symm.trans ((congrArg (M.matrix (R := R))
    ((hjR R x).symm.trans (hxy.trans (hjR R y)))).trans (hlift R _))

omit [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] in
private theorem planeMatrix_diagonal {J : Type u} [DecidableEq J]
    (α : Eˣ) (R : TestAlgebra F) (t : Rˣ) :
    planeMatrix (J := J) α (Matrix.diagonal (diagonalEntry t)) =
      diagonal (E := E) (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)) t := by
  let a := Algebra.TensorProduct.includeRight (R := F) (A := R) (B := E)
  let C := Coeff E R
  let w (i : Fin 2) : R := if i = 0 then (t : R) else (↑t⁻¹ : R)
  have hw : (Matrix.diagonal (diagonalEntry t)).submatrix ULift.up ULift.up =
      Matrix.diagonal w := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [diagonalEntry, w]
    · have h : (ULift.up i : RankOneIndex.{u}) ≠ ULift.up j := fun e => hij (congrArg ULift.down e)
      simp [Matrix.submatrix_apply, Matrix.diagonal_apply_ne, hij, h]
  have hcomp : hyperbolicComparison α (Matrix.diagonal w) =
      Matrix.diagonal (fun i => algebraMap R C (w i)) := by
    unfold hyperbolicComparison
    dsimp only
    rw [Matrix.diagonal_map (map_zero (algebraMap R C)), Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    have hα : a (α : E) * a (↑α⁻¹ : E) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    fin_cases i
    · change a (α : E) * algebraMap R C (w 0) * a (↑α⁻¹ : E) = algebraMap R C (w 0)
      rw [mul_right_comm, hα, one_mul]
    · change (1 : C) * algebraMap R C (w 1) * 1 = algebraMap R C (w 1)
      simp
  rw [planeMatrix, hw, hcomp]
  ext (i | i) (j | j)
  · fin_cases i <;> fin_cases j <;>
      simp [diagonal, weight, w, show (1 : Fin 2) ≠ 0 by decide] <;> rfl
  · simp [diagonal]
  · simp [diagonal]
  · by_cases hij : i = j
    · subst j
      simp [diagonal, weight, ← Algebra.TensorProduct.one_def]
    · simp [diagonal, hij]

omit [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [Fintype J] in
private theorem planeMatrix_transvection
    (α : Eˣ) (R : TestAlgebra F) {i k : Fin 2} (hik : i ≠ k) (x : R) :
    let a := Algebra.TensorProduct.includeRight (R := F) (A := R) (B := E)
    let w : Fin 2 → Coeff E R := ![a (α : E), 1]
    let v : Fin 2 → Coeff E R := ![a (↑α⁻¹ : E), 1]
    planeMatrix (J := J) α
      (Matrix.SpecialLinearGroup.transvection
        (fun h : (ULift.up i : RankOneIndex.{u}) = ULift.up k => hik (congrArg ULift.down h)) x).val =
      1 + Matrix.single (Sum.inl i) (Sum.inl k) (w i * algebraMap R (Coeff E R) x * v k) := by
  dsimp only
  let a := Algebra.TensorProduct.includeRight (R := F) (A := R) (B := E)
  let C := Coeff E R
  let w : Fin 2 → C := ![a (α : E), 1]
  let v : Fin 2 → C := ![a (↑α⁻¹ : E), 1]
  let X := Matrix.single i k (algebraMap R C x)
  let z := w i * algebraMap R C x * v k
  have hs : ((1 : Matrix RankOneIndex.{u} RankOneIndex.{u} R) +
      Matrix.single (ULift.up i) (ULift.up k) x).submatrix ULift.up ULift.up =
      1 + Matrix.single i k x := by
    ext p q
    simp only [Matrix.add_apply, Matrix.submatrix_apply, Matrix.one_apply, Matrix.single_apply,
      ULift.up.injEq]
  have hd : Matrix.diagonal w * Matrix.diagonal v = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have hα : a (α : E) * a (↑α⁻¹ : E) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    fin_cases i
    · exact hα
    · exact one_mul 1
  have hX : Matrix.diagonal w * X * Matrix.diagonal v = Matrix.single i k z := by
    ext p q
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases h : i = p ∧ k = q
    · obtain ⟨rfl, rfl⟩ := h
      simp [X, z]
    · simp [X, h]
  have hcmp : hyperbolicComparison α (1 + Matrix.single i k x) =
      1 + Matrix.single i k z := by
    change Matrix.diagonal w *
      (1 + Matrix.single i k x).map (algebraMap R C) * Matrix.diagonal v = _
    let aR : R →+* C := algebraMap R C
    change Matrix.diagonal w * (1 + Matrix.single i k x).map aR * Matrix.diagonal v = _
    rw [Matrix.map_add aR aR.map_add, Matrix.map_one aR aR.map_zero aR.map_one,
      Matrix.map_single i k x aR, mul_add, add_mul, mul_one, hd, hX]
  rw [planeMatrix, Matrix.SpecialLinearGroup.transvection_coe, hs, hcmp]
  have hmain : fromBlocks (Matrix.single i k z) 0 0 (0 : Matrix J J C) =
      Matrix.single (Sum.inl i) (Sum.inl k) z := by
    ext (p | p) (q | q) <;> simp [Matrix.single_apply]
  rw [← hmain, ← fromBlocks_one, fromBlocks_add]
  simp

end Plane

private theorem unitriangular_single {I C : Type*} [DecidableEq I] [Semiring C] {e f : I}
    (hef : e ≠ f) (x : C) :
    Unitriangular e f (1 + Matrix.single e f x) := by
  have hne : weight e f e ≠ weight e f f := by simp [weight, hef.symm]
  have hlt : weight e f f < weight e f e := by simp [weight, hef.symm]
  constructor
  · intro i j hij
    have hij' : i ≠ j := fun he => lt_irrefl _ (he ▸ hij)
    have h : ¬ (e = i ∧ f = j) := by
      rintro ⟨rfl, rfl⟩
      exact (not_lt_of_ge hlt.le) hij
    simp [Matrix.add_apply, Matrix.one_apply_ne hij', Matrix.single_apply_of_ne _ _ _ _ _ h]
  · ext i j
    by_cases he : weight e f i = weight e f j
    · have h : ¬ (e = i ∧ f = j) := by
        rintro ⟨rfl, rfl⟩
        exact hne he
      simp [zeroWeight, he, Matrix.add_apply, Matrix.single_apply_of_ne _ _ _ _ _ h]
    · have hij : i ≠ j := fun h => he (h ▸ rfl)
      simp [zeroWeight, he, Matrix.one_apply_ne hij]

private theorem transvection_limit_in_plane
    {J : Type u} [Fintype J] [DecidableEq J] {A : AffineAlgebraicGroup F}
    {H : Matrix (Fin 2 ⊕ J) (Fin 2 ⊕ J) E} {τ : E ≃ₐ[F] E} (M : Model G τ H)
    (α : Eˣ) (j : A.val ⟶ G.val)
    (e : (groupPointsFunctor F).obj A.val ≅ Specs.StandardGroups.specialLinearPoints F RankOneIndex.{u})
    (hmatrix : ∀ (R : TestAlgebra F) (x : GroupPoints A.val R),
      M.matrix (((groupPointsFunctor F).map j).app R x) =
        planeMatrix α (show Matrix.SpecialLinearGroup RankOneIndex.{u} R from e.hom.app R x).val)
    (d : Cocharacter G.val) {i k : Fin 2} (hik : i ≠ k)
    (hd : DescribesLimits M d (Sum.inl i) (Sum.inl k)) (R : TestAlgebra F) (x : R) :
    HasLimit d (transvectionPoint j e R
      (fun h : (ULift.up i : RankOneIndex.{u}) = ULift.up k => hik (congrArg ULift.down h)) x) 1 := by
  let p := Matrix.SpecialLinearGroup.transvection
    (fun h : (ULift.up i : RankOneIndex.{u}) = ULift.up k => hik (congrArg ULift.down h)) x
  let g := transvectionPoint j e R
    (fun h : (ULift.up i : RankOneIndex.{u}) = ULift.up k => hik (congrArg ULift.down h)) x
  have hpoint : e.hom.app R (e.inv.app R p) = p :=
    ((e.app R).groupIsoToMulEquiv).apply_symm_apply p
  have hp : M.matrix g = planeMatrix α p.val := by
    unfold g transvectionPoint
    change M.matrix (((groupPointsFunctor F).map j).app R (e.inv.app R p)) = _
    rw [hmatrix, hpoint]
  have ht : Unitriangular (Sum.inl i) (Sum.inl k) (M.matrix g) := by
    rw [hp, planeMatrix_transvection α R hik]
    exact unitriangular_single (fun h => hik (Sum.inl.inj h)) _
  exact (hd R g 1).2 ⟨ht.1, (matrix_one M).trans ht.2.symm⟩

/-- The regular centralizer is the centralizer of the split torus. A
commuting split cocharacter enlarges the torus only if it fails to factor
through it, by the split torus image and multiplication constructions. -/
private theorem regularCentralizingCocharacter_factors
    (hG : IsReductive G) (S : ClosedSubgroup G.val) (hS : IsMaximalSplitTorus S)
    (c : Cocharacter S.group) (hc : IsRegular S c) (d : Cocharacter G.val)
    (hd : Centralizes (c ≫ S.inclusion) d.hom.hom) :
    ∃ s : Cocharacter S.group, s ≫ S.inclusion = d := by
  obtain ⟨D⟩ := existsLimitDecomposition G (c ≫ S.inclusion)
  have hC := Relative.RelativeChambers.regularLevi G hG S hS.1 c D hc
  obtain ⟨i, hi⟩ := (D.centralizer_points _ _).1 hd
  obtain ⟨d₁, hd₁⟩ := factor_group_through_subgroup D.centralizer d i hi
  let z : IntegerCharacters.{u} ≃* Multiplicative ℤ := MulEquiv.ulift
  let : Group.FG IntegerCharacters.{u} :=
    Group.fg_of_surjective (f := z.symm.toMonoidHom) z.symm.surjective
  let M := diagonalGroup F IntegerCharacters.{u}
  let L := closedSubgroupAlgebraicGroup (G := G) D.centralizer
  obtain ⟨R, p, hR, hp⟩ := splitTorusImage M L (gm_split F) d₁
  let Rg := subgroupOfSubgroup D.centralizer R
  obtain ⟨T, hT, hST, hRT⟩ := splitTorusUpperBound G S Rg hS.1 hR (fun Y a b ↦ by
    have hb : Centralizes S.inclusion ((b ≫ R.inclusion.hom.hom) ≫ D.centralizer.inclusion.hom.hom) :=
      (hC Y _).mpr ⟨b ≫ R.inclusion.hom.hom, rfl⟩
    change Commute (a ≫ S.inclusion.hom.hom)
      (b ≫ R.inclusion.hom.hom ≫ D.centralizer.inclusion.hom.hom)
    rw [← Category.assoc b]
    simpa only [Category.id_comp] using ((centralizes_iff _ _).mp hb Y (𝟙 _) a).symm)
  obtain ⟨f, hf⟩ := subgroupOf_trans hRT (hS.2 T hT hST)
  refine ⟨p ≫ f, ?_⟩
  rw [Category.assoc, hf]
  change p ≫ R.inclusion ≫ D.centralizer.inclusion = d
  rw [← Category.assoc, hp.1, hd₁]

private theorem regularCocharacter_noncentral
    (hG : IsReductive G) (S : ClosedSubgroup G.val) (hS : IsMaximalSplitTorus S)
    (c : Cocharacter S.group) (hc : IsRegular S c) (d : Cocharacter G.val)
    (hd : ∃ (X : SchemeOver F) (g : X ⟶ G.val.X), ¬ Centralizes d g) :
    ∃ (X : SchemeOver F) (g : X ⟶ G.val.X), ¬ Centralizes (c ≫ S.inclusion) g := by
  by_contra! h
  obtain ⟨D⟩ := existsLimitDecomposition G (c ≫ S.inclusion)
  have hC := Relative.RelativeChambers.regularLevi G hG S hS.1 c D hc
  have hScentral (X : SchemeOver F) (g : X ⟶ G.val.X) : Centralizes S.inclusion g :=
    (hC X g).2 ((D.centralizer_points X g).1 (h X g))
  obtain ⟨s, hs⟩ := regularCentralizingCocharacter_factors hG S hS c hc d (h _ _)
  obtain ⟨X, g, hg⟩ := hd
  apply hg
  rw [← hs]
  apply (centralizes_iff _ _).2
  intro Y a t
  exact (centralizes_iff _ _).1 (hScentral X g) Y a (t ≫ s.hom.hom)

private theorem cocharacterPoint_comp {A B : GroupScheme F} (b : Cocharacter A)
    (j : A ⟶ B) (R : TestAlgebra F) (t : Rˣ) :
    cocharacterPoint (b ≫ j) R t =
      ((groupPointsFunctor F).map j).app R (cocharacterPoint b R t) := by
  unfold cocharacterPoint
  rw [Functor.map_comp]
  rfl

private theorem cocharacter_eq_of_point_eq {B : GroupScheme F} (d c : Cocharacter B)
    (he : ∀ (R : TestAlgebra F) (t : Rˣ), cocharacterPoint d R t = cocharacterPoint c R t) :
    d = c := by
  let A := MultiplicativeGroup F
  apply (groupHomComparison F A B (inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (MonoidAlgebra F IntegerCharacters)))))).1
  apply NatTrans.ext
  funext R
  apply GrpCat.ext
  intro x
  obtain ⟨t, rfl⟩ : ∃ t : Rˣ, unitPoint R t = x :=
    ⟨unitEquiv R x, (unitEquiv R).injective (unitEquiv_unitPoint R _)⟩
  exact he R t

section OppositeRadicals

variable [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
variable {J : Type u} [Fintype J] [DecidableEq J]

local notation "σ" => quadraticConjugation F E
local notation "i₀" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ J)
local notation "i₁" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ J)

private theorem rankOneWithGeneratingRadicals [Infinite F] [TopologicalSpace F]
    (hG : IsAbsolutelyAlmostSimple G) (hgen : unipotentGenerated G = ⊤)
    (H : (Matrix (Fin 2 ⊕ J) (Fin 2 ⊕ J) E)ˣ)
    (hH : (H.val.map σ).transpose = H.val) (h : HyperbolicPair H.val i₀ i₁)
    (M : Model G σ H.val) :
    ∃ (α : Eˣ) (j : (specialLinearGroup F RankOneIndex.{u}).val ⟶ G.val)
      (b : Cocharacter (specialLinearGroup F RankOneIndex.{u}).val),
      IsClosedImmersion j.hom.hom.left ∧
      (∀ (R : TestAlgebra F) (t : Rˣ),
        (show Matrix.SpecialLinearGroup RankOneIndex.{u} R from
          (specialLinearGroupPointsIso F RankOneIndex.{u}).hom.app R (cocharacterPoint b R t)).val =
          Matrix.diagonal (diagonalEntry t)) ∧
      (∀ (R : TestAlgebra F) (x : GroupPoints (specialLinearGroup F RankOneIndex.{u}).val R),
        M.matrix (((groupPointsFunctor F).map j).app R x) =
          planeMatrix α
            (show Matrix.SpecialLinearGroup RankOneIndex.{u} R from
              (specialLinearGroupPointsIso F RankOneIndex.{u}).hom.app R x).val) ∧
      let d := b ≫ j
      (∃ (X : SchemeOver F) (g : X ⟶ G.val.X), ¬ Centralizes d g) ∧
      DescribesLimits M d i₀ i₁ ∧
      DescribesLimits M (oppositeCocharacter d) i₁ i₀ ∧
      let R := groundAlgebra F
      @Dense (GroupPoints G.val R) (pointTopology G.val.X) (Subgroup.closure
        ({g : GroupPoints G.val R | HasLimit d g 1} ∪
          {g : GroupPoints G.val R | HasLimit (oppositeCocharacter d) g 1}) :
        Set (GroupPoints G.val R)) := by
  obtain ⟨α, j, hj, hmatrix⟩ := rankOneEmbedding h M
  obtain ⟨b, hb⟩ := exists_rankOneDiagonal (F := F)
  let d := b ≫ j
  obtain ⟨c, hc, hn, hpos, hneg, _⟩ := HermitianRadicalComparison.matrixComparison
    σ (Specs.UnitaryRankOne.quadraticConjugation_ne_one F E) (fun a => conj_conj a) H hH i₀ i₁ h G M
  have hd : d = c := by
    apply cocharacter_eq_of_point_eq
    intro R t
    apply matrix_injective M (R := R)
    rw [cocharacterPoint_comp, hmatrix, hb, planeMatrix_diagonal, hc]
  refine ⟨α, j, b, hj, hb, hmatrix, ?_⟩
  change (∃ (X : SchemeOver F) (g : X ⟶ G.val.X), ¬ Centralizes d g) ∧
    DescribesLimits M d i₀ i₁ ∧ DescribesLimits M (oppositeCocharacter d) i₁ i₀ ∧ _
  rw [hd]
  refine ⟨hn, hpos, hneg, ?_⟩
  obtain ⟨D⟩ := existsLimitDecomposition G c
  obtain ⟨D'⟩ := existsLimitDecomposition G (oppositeCocharacter c)
  let R := groundAlgebra F
  have heq := limitSubgroups_generate hG hgen c hn D D'
  have hdense : @Dense (GroupPoints G.val R) (pointTopology G.val.X)
      ((⊤ : Subgroup (GroupPoints G.val R)) : Set (GroupPoints G.val R)) :=
    @dense_univ _ (pointTopology G.val.X)
  have hDense := (congrArg (fun U : Subgroup (GroupPoints G.val R) =>
    @Dense (GroupPoints G.val R) (pointTopology G.val.X) (U : Set (GroupPoints G.val R))) heq).mpr hdense
  exact (congrArg (fun q : Cocharacter G.val =>
    @Dense (GroupPoints G.val R) (pointTopology G.val.X)
      (Subgroup.closure ({g : GroupPoints G.val R | HasLimit q g 1} ∪
        {g : GroupPoints G.val R | HasLimit (oppositeCocharacter q) g 1}) :
          Set (GroupPoints G.val R))) hd).mpr hDense

end OppositeRadicals

section IsotropicRankOne

variable [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]

local notation "σ" => quadraticConjugation F E

private theorem noncentralCocharacter_of_isotropic
    {n : ℕ} (H : (Matrix (Fin n) (Fin n) E)ˣ)
    (hH : (H.val.map σ).transpose = H.val)
    (hisotropic : ∃ x : Fin n → E, x ≠ 0 ∧ dotProduct (σ ∘ x) (H.val.mulVec x) = 0)
    (hmodel : RepresentsHermitian σ H.val G) :
    ∃ (d : Cocharacter G.val) (X : SchemeOver F) (g : X ⟶ G.val.X), ¬ Centralizes d g := by
  obtain ⟨r, B, M, hB, hp⟩ := exists_hyperbolic_model H hH hisotropic hmodel
  obtain ⟨d, _, hn, _, _, _⟩ := HermitianRadicalComparison.matrixComparison σ
    (Specs.UnitaryRankOne.quadraticConjugation_ne_one F E) (fun a => conj_conj a) B hB _ _ hp G M
  exact ⟨d, hn⟩

end IsotropicRankOne

section LinearWeights

variable {K : Type u} [Field K]
variable {I : Type u} [Fintype I] [DecidableEq I]

/-- Coaction weight vectors are simultaneous eigenvectors on every test algebra. -/
private theorem cocharacter_weightBasis {L : GroupScheme K}
    (l : (groupPointsFunctor K).obj L ≅ Specs.StandardGroups.generalLinearPoints K I)
    (c : Cocharacter L) :
    ∃ (J : Type u) (_ : Fintype J) (b : Module.Basis J K (I → K)) (w : J → ℤ),
      ∀ (R : TestAlgebra K) (t : Rˣ) (j : J),
        let D := (show Matrix.GeneralLinearGroup I R from l.hom.app R (cocharacterPoint c R t)).val
        D.mulVec (fun i => algebraMap K R (b j i)) =
          fun i => (t ^ w j).val * algebraMap K R (b j i) := by
  let A := groupAlgebra K IntegerCharacters.{u}
  let D : AffineGroupCategory K := ⟨specGroup A, inferInstanceAs
    (IsAffine (Spec (CommRingCat.of A)))⟩
  let e := hopfSpecPointIso A
  let b := Pi.basisFun K I
  obtain ⟨P, hP⟩ := representationCoactionComparison A b D L e l
  let ρ := P c
  obtain ⟨J, hJ, d, w, hw⟩ := DiagonalizableFixedLocus.existsWeightBasis ρ
  let : Fintype J := Fintype.ofFinite J
  let z : IntegerCharacters.{u} ≃* Multiplicative ℤ := MulEquiv.ulift
  refine ⟨J, inferInstance, d, fun j => Multiplicative.toAdd (z (w j)), ?_⟩
  intro R t j
  let q := unitCoordinates R t
  let v := coactionOperator A ρ R q.toLinearMap
  have hmatrix : (show Matrix.GeneralLinearGroup I R from l.hom.app R (cocharacterPoint c R t)).val =
      LinearMap.toMatrix (b.baseChange R) (b.baseChange R) v := by
    rw [coactionOperator_toMatrix]
    exact representation_point_matrix A b D L e l c ρ (hP c) R q
  have hweight : v (1 ⊗ₜ[K] d j) = q (MonoidAlgebra.of K IntegerCharacters (w j)) ⊗ₜ[K] d j :=
    coactionOperator_apply_tmul A ρ q.toLinearMap (WeightDecomposition.mem_weightSpace.mp (hw j))
  have hq : q (MonoidAlgebra.of K IntegerCharacters (w j)) =
      (t ^ Multiplicative.toAdd (z (w j))).val := by
    change (MonoidAlgebra.lift K R IntegerCharacters _)
      (MonoidAlgebra.of K IntegerCharacters (w j)) = _
    rw [MonoidAlgebra.lift_of]
    rfl
  have hb (r : R) (x : I → K) : (b.baseChange R).repr (r ⊗ₜ[K] x) =
      fun i => r * algebraMap K R (x i) := by
    funext i
    rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_comm]
    rfl
  dsimp only
  rw [hmatrix]
  have hm := LinearMap.toMatrix_mulVec_repr (b.baseChange R) (b.baseChange R) v
    (1 ⊗ₜ[K] d j)
  change (LinearMap.toMatrix (b.baseChange R) (b.baseChange R) v).mulVec
    ((b.baseChange R).repr (1 ⊗ₜ[K] d j)) = (b.baseChange R).repr (v (1 ⊗ₜ[K] d j)) at hm
  rw [hweight, hq, hb, hb] at hm
  simpa only [one_mul] using hm

end LinearWeights

section UnitaryWeights

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
variable {G : AffineAlgebraicGroup F} {n : ℕ}

private abbrev tensorTest (R : TestAlgebra F) : TestAlgebra E :=
  letI : Algebra E (R ⊗[F] E) := Algebra.TensorProduct.rightAlgebra
  CommAlgCat.of E (R ⊗[F] E)

private def extendCoefficients (R : TestAlgebra F) :
    R ⟶ restrictTestAlgebraObj F E (tensorTest (E := E) R) := by
  let S := restrictTestAlgebraObj F E (tensorTest (E := E) R)
  letI : Algebra F S := S.algebra
  let a : R →ₐ[F] S :=
    { toRingHom := Algebra.TensorProduct.includeLeftRingHom
      commutes' := fun f => Algebra.TensorProduct.algebraMap_apply' f }
  exact CommAlgCat.ofHom a

omit [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] in
private theorem extendCoefficients_factor (R : TestAlgebra F) (x : R ⊗[F] E) :
    factorAt (F := F) (tensorTest (E := E) R)
      (changeCoefficients (E := E) (extendCoefficients (E := E) R) x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [change_tmul]
    change (a ⊗ₜ[F] (1 : E)) * ((1 : R) ⊗ₜ[F] b) = a ⊗ₜ[F] b
    simp
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Project to the first matrix factor over the quadratic field, decompose
the split multiplicative group action into weights, and read the resulting
eigenvectors over each original test algebra via its coefficient extension. -/
private theorem unitaryCocharacter_hasWeightBasis
    {H : Matrix (Fin n) (Fin n) E} (M : RepresentsHermitian (quadraticConjugation F E) H G)
    (c : Cocharacter G.val) :
    ∃ (J : Type u) (_ : Fintype J) (b : Module.Basis J E (Fin n → E)) (w : J → ℤ),
      ∀ (R : TestAlgebra F) (t : Rˣ) (j : J),
        let X := ((Classical.choose M) R (cocharacterPoint c R t)).val.val
        let v (i : Fin n) := Algebra.TensorProduct.includeRight (R := F) (A := R) (b j i)
        X.mulVec v = fun i => algebraMap R (R ⊗[F] E) (t ^ w j).val * v i := by
  let I := ULift.{u} (Fin n)
  let A := specGroup (groupAlgebra E IntegerCharacters)
  let L := generalLinearGroup E I
  let p := generalLinearGroupPointsIso E I
  let point := Classical.choose M
  have hmodel := Classical.choose_spec M
  let toMatrix (R : TestAlgebra E) :
      GroupPoints G.val (restrictTestAlgebraObj F E R) →* Matrix.GeneralLinearGroup I R :=
    Matrix.SpecialLinearGroup.toGL.comp ((liftSpecialLinear n).toMonoidHom.comp
      ((Matrix.SpecialLinearGroup.map (factorAt R)).comp
        (MonoidHom.mk' (fun x => (point _ x).val) (hmodel.1 _))))
  let f (R : TestAlgebra E) : GroupPoints A R →* Matrix.GeneralLinearGroup I R :=
    (toMatrix R).comp (((((groupPointsFunctor F).map c).app
      (restrictTestAlgebraObj F E R)).hom).comp
        ((unitPointHom (restrictTestAlgebraObj F E R)).comp (unitEquiv R).toMonoidHom))
  have hf (R : TestAlgebra E) (t : Rˣ) (i j : I) :
      (f R (unitPoint R t)).val i j =
        factorAt R ((point _ (cocharacterPoint c (restrictTestAlgebraObj F E R) t)).val.val i.down j.down) := by
    change (toMatrix R ( (((groupPointsFunctor F).map c).app _)
      (unitPointHom _ (unitEquiv R (unitPoint R t))))).val i j = _
    rw [unitEquiv_unitPoint, unitPointHom_apply]
    rfl
  let δ : (groupPointsFunctor E).obj A ⟶ Specs.StandardGroups.generalLinearPoints E I :=
    { app := fun R => show GrpCat.of (GroupPoints A R) ⟶
        GrpCat.of (Matrix.GeneralLinearGroup I R) from GrpCat.ofHom (f R)
      naturality := by
        intro R T a
        apply GrpCat.ext
        intro x
        obtain ⟨t, rfl⟩ : ∃ t : Rˣ, unitPoint R t = x :=
          ⟨unitEquiv R x, (unitEquiv R).injective (unitEquiv_unitPoint R _)⟩
        symm
        change Matrix.GeneralLinearGroup.map a.hom.toRingHom (f R (unitPoint R t)) =
          f T (mapPoints a (unitPoint R t))
        rw [mapPoints_unitPoint]
        apply Units.ext
        ext i j
        change a.hom ((f R (unitPoint R t)).val i j) =
          (f T (unitPoint T (Units.map a.hom.toMonoidHom t))).val i j
        rw [hf, hf]
        let a₀ := (restrictTestAlgebra F E).map a
        change a.hom (factorAt R ((point _ (cocharacterPoint c _ t)).val.val i.down j.down)) =
          factorAt T ((point _ (cocharacterPoint c _ (Units.map a₀.hom.toMonoidHom t))).val.val i.down j.down)
        rw [← mapPoints_cocharacterPoint a₀, hmodel.2]
        exact (firstFactor_natural a _).symm }
  obtain ⟨q, hq⟩ := (groupHomComparison E A L.val (inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (MonoidAlgebra E IntegerCharacters)))))).2 (δ ≫ p.inv)
  have he : (groupPointsFunctor E).map q ≫ p.hom = δ := by
    change (groupPointsFunctor E).map q = δ ≫ p.inv at hq
    exact (congrArg (· ≫ p.hom) hq).trans (by simp)
  have hcochar (R : TestAlgebra E) (t : Rˣ) :
      p.hom.app R (cocharacterPoint q R t) = f R (unitPoint R t) :=
    DFunLike.congr_fun (congrArg (fun u => (u.app R).hom) he) (unitPoint R t)
  obtain ⟨J, hJ, b, w, hweight⟩ := cocharacter_weightBasis p q
  let : Fintype J := hJ
  let lin : (I → E) ≃ₗ[E] (Fin n → E) := LinearEquiv.funCongrLeft E E Equiv.ulift.symm
  refine ⟨J, hJ, b.map lin, w, ?_⟩
  intro R t j
  let a := extendCoefficients (E := E) R
  let T := tensorTest (E := E) R
  letI : Algebra E T := T.algebra
  let t' : Tˣ := Units.map a.hom.toMonoidHom t
  have hm (i k : I) :
      (f T (unitPoint T t')).val i k = (point R (cocharacterPoint c R t)).val.val i.down k.down := by
    rw [hf]
    change factorAt (F := F) T ((point _ (cocharacterPoint c _ (Units.map a.hom.toMonoidHom t))).val.val i.down k.down) = _
    rw [← mapPoints_cocharacterPoint a, hmodel.2]
    exact extendCoefficients_factor (E := E) R _
  dsimp only
  funext i
  have hw := hweight T t' j
  dsimp only at hw
  rw [hcochar] at hw
  have hi := congrFun hw (ULift.up i)
  change Matrix.mulVec _ _ (ULift.up i) = _ at hi
  simp only [Matrix.mulVec, dotProduct, hm] at hi ⊢
  have hs := Fintype.sum_equiv (Equiv.ulift : I ≃ Fin n)
    (fun k : I => (point R (cocharacterPoint c R t)).val.val i k.down *
      (algebraMap E T) (b j k))
    (fun k : Fin n => (point R (cocharacterPoint c R t)).val.val i k *
      (algebraMap E T) (b j (ULift.up k))) (fun _ => rfl)
  rw [hs] at hi
  dsimp only [t'] at hi
  rw [← map_zpow] at hi
  exact hi

end UnitaryWeights

section PairedWeights

variable [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
variable {n : ℕ}

local notation "σ" => quadraticConjugation F E

private def hermitianMatrixAt {H : Matrix (Fin n) (Fin n) E}
    (M : RepresentsHermitian σ H G) (R : TestAlgebra F) (x : GroupPoints G.val R) :
    Matrix (Fin n) (Fin n) (Coeff E R) :=
  ((Classical.choose M) R x).val.val

private abbrev coefficientVector (R : TestAlgebra F) (v : Fin n → E) : Fin n → Coeff E R :=
  Algebra.TensorProduct.includeRight (R := F) (A := R) ∘ v

private def HasWeight {H : Matrix (Fin n) (Fin n) E}
    (M : RepresentsHermitian σ H G) (c : Cocharacter G.val) (m : ℤ) (x : Fin n → E) : Prop :=
  ∀ (R : TestAlgebra F) (t : Rˣ),
    (hermitianMatrixAt M R (cocharacterPoint c R t)).mulVec (coefficientVector R x) =
      (algebraMap R (Coeff E R) (t ^ m).val) • coefficientVector R x

private theorem centralizes_of_trivial_points (c : Cocharacter G.val)
    (h : ∀ (R : TestAlgebra F) (t : Rˣ), cocharacterPoint c R t = 1)
    (X : SchemeOver F) (g : X ⟶ G.val.X) : Centralizes c g := by
  let R := CommAlgCat.of F (MonoidAlgebra F IntegerCharacters)
  let p : GroupPoints (MultiplicativeGroup F) R := 𝟙 _
  have hp : unitPoint R (unitEquiv R p) = p :=
    (unitEquiv R).injective (unitEquiv_unitPoint R _)
  have ht := h R (unitEquiv R p)
  change unitPoint R (unitEquiv R p) ≫ c.hom.hom = 1 at ht
  rw [hp] at ht
  have hh : c.hom.hom = 1 := by
    simpa only [p, Category.id_comp] using ht
  apply (centralizes_iff _ _).2
  intro Y a t
  rw [hh, MonObj.comp_one]
  exact Commute.one_right _

private theorem weightBasis_has_nonzero_weight {H : Matrix (Fin n) (Fin n) E}
    (M : RepresentsHermitian σ H G) (c : Cocharacter G.val)
    (hc : ∃ (X : SchemeOver F) (g : X ⟶ G.val.X), ¬ Centralizes c g)
    {J : Type u} [Fintype J] (b : Module.Basis J E (Fin n → E)) (w : J → ℤ)
    (hw : ∀ j, HasWeight M c (w j) (b j)) : ∃ j, w j ≠ 0 := by
  classical
  by_contra! h
  obtain ⟨X, g, hg⟩ := hc
  apply hg (centralizes_of_trivial_points c ?_ X g)
  intro R t
  let T := LinearMap.toMatrix' b.equivFun.symm.toLinearMap
  let U := LinearMap.toMatrix' b.equivFun.toLinearMap
  let a : E →+* Coeff E R := (Algebra.TensorProduct.includeRight (R := F) (A := R)).toRingHom
  let Y := hermitianMatrixAt M R (cocharacterPoint c R t)
  have hT (i : Fin n) (j : J) : T i j = b j i := by
    rw [show T = LinearMap.toMatrix' b.equivFun.symm.toLinearMap from rfl, LinearMap.toMatrix'_apply]
    change (b.equivFun.symm (Pi.single j 1)) i = _
    have he : b.equivFun (b j) = Pi.single j 1 := by
      funext k
      simp [Pi.single_apply, eq_comm]
    rw [← he, LinearEquiv.symm_apply_apply]
  have hTU' : T * U = 1 := matricesOfEquiv_mul b.equivFun.symm
  have hTU : T.map a * U.map a = 1 := by
    rw [← Matrix.map_mul, hTU', Matrix.map_one a a.map_zero a.map_one]
  have hY : Y * T.map a = T.map a := by
    ext i j
    have hv := congrFun (hw j R t) i
    rw [h j, zpow_zero, Units.val_one, map_one, one_smul] at hv
    change (Y.mulVec (coefficientVector R (b j))) i = a (b j i) at hv
    simp only [Matrix.mul_apply, Matrix.map_apply, hT]
    exact hv
  have hOne : Y = 1 := by
    calc
      Y = Y * (T.map a * U.map a) := by rw [hTU, mul_one]
      _ = 1 := by rw [← Matrix.mul_assoc, hY, hTU]
  apply (Classical.choose M R).injective
  apply Subtype.ext
  apply Subtype.ext
  have hone : hermitianMatrixAt M R (1 : GroupPoints G.val R) = 1 := by
    let φ : GroupPoints G.val R →* Matrix.SpecialLinearGroup (Fin n) (Coeff E R) :=
      MonoidHom.mk' (fun x => ((Classical.choose M) R x).val) ((Classical.choose_spec M).1 R)
    exact congrArg Subtype.val φ.map_one
  exact hOne.trans hone.symm

private theorem matrixPairing_smul {I : Type*} [Fintype I]
    (P : Matrix I I E) (a b : E) (x y : I → E) :
    matrixPairing (σ).toRingHom P (a • x) (b • y) =
      (σ a * b) * matrixPairing (σ).toRingHom P x y := by
  unfold matrixPairing
  have hx : (σ).toRingHom ∘ (a • x) = σ a • ((σ).toRingHom ∘ x) := by
    funext i
    change σ (a * x i) = σ a * σ (x i)
    exact map_mul σ a (x i)
  rw [hx, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  exact (mul_assoc _ _ _).symm

private theorem exists_unit_with_injective_powers
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    ∃ t : Fˣ, Function.Injective (fun m : ℤ => t ^ m) := by
  obtain ⟨v, hv, hv1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := F)
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective v
  have hane : a ≠ 0 := by
    intro he
    rw [he, map_zero] at ha
    exact (ne_of_gt hv) ha.symm
  let t := Units.mk0 a hane
  refine ⟨t, fun i j h => ?_⟩
  apply zpow_right_injective₀ hv hv1.ne
  have he : (t ^ i).val = (t ^ j).val := congrArg Units.val h
  simpa only [Units.val_zpow_eq_zpow_val, map_zpow₀, t, Units.val_mk0, ha] using
    congrArg (ValuativeRel.valuation F) he

/-- Evaluating at a unit of nontrivial valuation detects the sum of the
two integer weights of a nonorthogonal pair. -/
private theorem opposite_weights_of_paired
    {H : (Matrix (Fin n) (Fin n) E)ˣ} (hH : (H.val.map σ).transpose = H.val)
    (M : RepresentsHermitian σ H.val G) (c : Cocharacter G.val) {m l : ℤ}
    {x y : Fin n → E} (hx : HasWeight M c m x) (hy : HasWeight M c l y)
    (t : Fˣ) (ht : Function.Injective (fun m : ℤ => t ^ m))
    (hxy : (formOfMatrix H.val hH).pairing x y ≠ 0) : m + l = 0 := by
  let R := groundAlgebra F
  let B := hermitianMatrixAt M R (cocharacterPoint c R t)
  let a := (Algebra.TensorProduct.lid F E).toRingEquiv
  let D := B.map a
  let tau := Specs.Arithmetic.OuterTypeALocalModels.conjugationAt σ R
  let H' := H.val.map (Algebra.TensorProduct.includeRight (R := F) (A := R))
  have hB : (B.map tau).transpose * H' * B = H' :=
    ((Classical.choose M) R (cocharacterPoint c R t)).property
  have hHd : H'.map a = H.val := by
    ext i j
    change (Algebra.TensorProduct.lid F E) ((1 : F) ⊗ₜ[F] H.val i j) = _
    simp
  have hC : (B.map tau).transpose.map a = adjointMatrix (σ).toRingHom D :=
    Matrix.ext fun i j => ground_conjugation («σ» := σ) (B j i)
  have hD' := congrArg (fun X : Matrix (Fin n) (Fin n) (Coeff E R) => X.map a) hB
  rw [Matrix.map_mul, Matrix.map_mul, hC, hHd] at hD'
  have hD : adjointMatrix (σ).toRingHom D * H.val * D = H.val := hD'
  have he {k : ℤ} {z : Fin n → E} (hz : HasWeight M c k z) :
      D.mulVec z = (algebraMap F E (t ^ k).val) • z := by
    funext i
    have hh := congrArg a (congrFun (hz R t) i)
    change a ((B.mulVec (coefficientVector R z)) i) =
      a (algebraMap R (Coeff E R) (t ^ k).val * coefficientVector R z i) at hh
    have hvec := a.toRingHom.map_mulVec B (coefficientVector R z) i
    change a ((B.mulVec (coefficientVector R z)) i) =
      (D.mulVec (a ∘ coefficientVector R z)) i at hvec
    have ha : a ∘ coefficientVector R z = z := by
      funext j
      change (Algebra.TensorProduct.lid F E) ((1 : F) ⊗ₜ[F] z j) = z j
      simp
    rw [ha] at hvec
    refine hvec.symm.trans (hh.trans ?_)
    change a (algebraMap R (Coeff E R) (t ^ k).val * coefficientVector R z i) =
      algebraMap F E (t ^ k).val * z i
    rw [map_mul]
    change (Algebra.TensorProduct.lid F E) ((t ^ k).val ⊗ₜ[F] (1 : E)) *
      (Algebra.TensorProduct.lid F E) ((1 : F) ⊗ₜ[F] z i) = _
    simp [Algebra.smul_def]
  have hpair := matrixPairing_change (σ).toRingHom H.val D x y
  rw [hD, he hx, he hy, matrixPairing_smul, AlgEquiv.commutes, ← map_mul, ← Units.val_mul, ← zpow_add] at hpair
  have hscalar : algebraMap F E (t ^ (m + l)).val = 1 := by
    apply mul_right_cancel₀ hxy
    exact hpair.symm.trans (one_mul _).symm
  apply ht
  apply Units.ext
  simpa only [zpow_zero, Units.val_one, map_one] using
    (algebraMap F E).injective (hscalar.trans (map_one _).symm)

private theorem HasWeight.smul {H : Matrix (Fin n) (Fin n) E}
    {M : RepresentsHermitian σ H G} {c : Cocharacter G.val} {m : ℤ} {x : Fin n → E}
    (hx : HasWeight M c m x) (s : E) :
    HasWeight M c m (s • x) := by
  intro R t
  let a := Algebra.TensorProduct.includeRight (R := F) (A := R) (B := E)
  have hr : coefficientVector R (s • x) = a s • coefficientVector R x := by
    funext i
    exact map_mul a s (x i)
  rw [hr, Matrix.mulVec_smul, hx R t, smul_comm]

private theorem exists_weighted_hyperbolic_pair
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (H : (Matrix (Fin n) (Fin n) E)ˣ) (hH : (H.val.map σ).transpose = H.val)
    (M : RepresentsHermitian σ H.val G) (c : Cocharacter G.val)
    (hc : ∃ (X : SchemeOver F) (g : X ⟶ G.val.X), ¬ Centralizes c g) :
    ∃ (m : ℤ) (e f : Fin n → E), m ≠ 0 ∧
      let h := formOfMatrix H.val hH
      h.pairing e e = 0 ∧ h.pairing f f = 0 ∧ h.pairing e f = 1 ∧
        HasWeight M c m e ∧ HasWeight M c (-m) f := by
  obtain ⟨J, hJ, b, w, hw⟩ := unitaryCocharacter_hasWeightBasis M c
  let : Fintype J := hJ
  have hW (j : J) : HasWeight M c (w j) (b j) := fun R t => hw R t j
  obtain ⟨i, hi⟩ := weightBasis_has_nonzero_weight M c hc b w hW
  obtain ⟨t, ht⟩ := exists_unit_with_injective_powers (F := F)
  let h := formOfMatrix H.val hH
  have hn := formOfMatrix_nondegenerate H hH
  obtain ⟨j, hj⟩ : ∃ j, h.pairing (b i) (b j) ≠ 0 := by
    by_contra! hz
    have hl : h.linear (b i) = 0 := b.ext fun j => hz j
    apply b.ne_zero i (hn _ fun y => ?_)
    rw [← h.hermitian]
    have hv := congrArg (fun g : (Fin n → E) →ₗ[E] E => g y) hl
    change h.pairing (b i) y = 0 at hv
    rw [hv, map_zero]
  have hneg : w j = -w i := by
    have hp := opposite_weights_of_paired hH M c (hW i) (hW j) t ht hj
    omega
  have hf : HasWeight M c (-w i) (b j) := hneg ▸ hW j
  let z := (h.pairing (b i) (b j))⁻¹ • b j
  have hz : HasWeight M c (-w i) z := hf.smul _
  have hiso {m : ℤ} {x : Fin n → E} (hm : m ≠ 0) (hx : HasWeight M c m x) :
      h.pairing x x = 0 := by
    by_contra hn'
    have hp := opposite_weights_of_paired hH M c hx hx t ht hn'
    omega
  refine ⟨w i, b i, z, hi, hiso hi (hW i), hiso (neg_ne_zero.mpr hi) hz, ?_, hW i, hz⟩
  change (h.linear (b i)) ((h.pairing (b i) (b j))⁻¹ • b j) = 1
  rw [map_smul]
  exact inv_mul_cancel₀ hj

end PairedWeights

section AlignedModel

variable [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]

local notation "σ" => quadraticConjugation F E

/-- In these coordinates the given cocharacter acts on the two hyperbolic lines
with the indicated weights. -/
private def ScalesHyperbolicLines {J : Type u} [Fintype J] [DecidableEq J]
    {H : Matrix (Fin 2 ⊕ J) (Fin 2 ⊕ J) E} (M : Model G σ H)
    (c : Cocharacter G.val) (m : ℤ) : Prop :=
  ∀ (R : TestAlgebra F) (t : Rˣ) (i : Fin 2 ⊕ J) (j : Fin 2),
    M.matrix (cocharacterPoint c R t) i (Sum.inl j) =
      if i = Sum.inl j then algebraMap R (Coeff E R) (t ^ (if j = 0 then m else -m)).val else 0

private theorem adapted_weight_column {n : ℕ}
    {H : (Matrix (Fin n) (Fin n) E)ˣ} (hmodel : RepresentsHermitian σ H.val G)
    (c : Cocharacter G.val) {m : ℤ} {x : Fin n → E} (hx : HasWeight hmodel c m x)
    {I : Type u} [Fintype I] [DecidableEq I]
    (T : Matrix (Fin n) I E) (U : Matrix I (Fin n) E) (hTU : T * U = 1) (hUT : U * T = 1)
    (j : I) (hj : ∀ i, T i j = x i) (R : TestAlgebra F) (t : Rˣ) (i : I) :
    (modelInBasis hmodel T U hTU hUT).matrix (cocharacterPoint c R t) i j =
      if i = j then algebraMap R (Coeff E R) (t ^ m).val else 0 := by
  let a : E →+* Coeff E R := (Algebra.TensorProduct.includeRight (R := F) (A := R)).toRingHom
  let Y := hermitianMatrixAt hmodel R (cocharacterPoint c R t)
  let y : I → Coeff E R := Pi.single j 1
  let s : Coeff E R := algebraMap R (Coeff E R) (t ^ m).val
  have hT : (T.map a).mulVec y = coefficientVector R x := by
    unfold y
    rw [Matrix.mulVec_single_one]
    funext i
    change a (T i j) = a (x i)
    rw [hj]
  have hU : U.map a * T.map a = 1 := by
    rw [← Matrix.map_mul, hUT, Matrix.map_one a a.map_zero a.map_one]
  have hY : (U.map a * Y * T.map a).mulVec y = s • y := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hT]
    change (U.map a).mulVec (Y.mulVec (coefficientVector R x)) = _
    rw [show Y.mulVec (coefficientVector R x) = s • coefficientVector R x from hx R t,
      Matrix.mulVec_smul, ← hT, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  have he := congrFun hY i
  rw [show (U.map a * Y * T.map a).mulVec y i = (U.map a * Y * T.map a) i j from by
    unfold y
    rw [Matrix.mulVec_single_one]
    rfl] at he
  change (U.map a * Y * T.map a) i j = _
  rw [he]
  by_cases hi : i = j <;> simp [y, s, hi]

private theorem exists_aligned_hyperbolic_model
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {n : ℕ} (H : (Matrix (Fin n) (Fin n) E)ˣ)
    (hH : (H.val.map σ).transpose = H.val) (hmodel : RepresentsHermitian σ H.val G)
    (c : Cocharacter G.val) (hc : ∃ (X : SchemeOver F) (g : X ⟶ G.val.X), ¬ Centralizes c g) :
    ∃ (m : ℤ) (r : ℕ)
      (B : (Matrix (PlaneCoordinates.{u} r) (PlaneCoordinates.{u} r) E)ˣ) (M : Model G σ B.val),
      m ≠ 0 ∧ (B.val.map σ).transpose = B.val ∧
        HyperbolicPair B.val (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)) ∧
        ScalesHyperbolicLines M c m := by
  obtain ⟨m, e, f, hm, hee, hff, hef, he, hf⟩ := exists_weighted_hyperbolic_pair H hH hmodel c hc
  let h := formOfMatrix H.val hH
  let W := h.hyperbolicComplement e f
  obtain ⟨_, l, hl, hlform⟩ := HermitianMatrixGeneration.hyperbolicCoordinates h e f hee hff hef
  let b := hyperbolicBasis (E := E) W
  have hb := hyperbolicBasis_adapted (E := E) W
  let d := b.equivFun.symm.trans l
  let T := LinearMap.toMatrix' d.toLinearMap
  let U := LinearMap.toMatrix' d.symm.toLinearMap
  have hTU : T * U = 1 := matricesOfEquiv_mul d
  have hUT : U * T = 1 := matricesOfEquiv_mul d.symm
  let B := changedGram (σ).toRingHom H T U hTU hUT
  let M := modelInBasis hmodel T U hTU hUT
  have hB : (B.val.map σ).transpose = B.val :=
    changedGram_hermitian (σ).toRingHom (fun a => conj_conj a) H hH T U hTU hUT
  have hcoords (x y : Space E W) :
      matrixPairing (σ).toRingHom B.val (b.equivFun x) (b.equivFun y) =
        Specs.HermitianMatrixGeneration.hyperbolicPairing (h.restrict W) x y := by
    change matrixPairing (σ).toRingHom (adjointMatrix (σ).toRingHom T * H.val * T)
      (b.equivFun x) (b.equivFun y) = _
    rw [matrixPairing_change]
    have hlxy : matrixPairing (σ).toRingHom H.val (l x) (l y) =
        Specs.HermitianMatrixGeneration.hyperbolicPairing (h.restrict W) x y := hlform x y
    simpa only [T, d, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply] using hlxy
  have hT (i : Fin n) (j : PlaneCoordinates.{u} (Module.finrank E W)) :
      T i j = l (b j) i := by
    rw [show T = LinearMap.toMatrix' d.toLinearMap from rfl, LinearMap.toMatrix'_apply]
    change l (b.equivFun.symm (Pi.single j 1)) i = _
    have he : b.equivFun (b j) = Pi.single j 1 := by
      funext k
      simp [Pi.single_apply, eq_comm]
    rw [← he, LinearEquiv.symm_apply_apply]
  have hecol (i : Fin n) : T i (Sum.inl 0) = e i := by
    rw [hT]
    have hbk : b (Sum.inl 0) = (1, 0, 0) := AdaptedBasis.first hb
    rw [hbk, hl]
    simp
  have hfcol (i : Fin n) : T i (Sum.inl 1) = f i := by
    rw [hT]
    have hbk : b (Sum.inl 1) = (0, 0, 1) := AdaptedBasis.last hb
    rw [hbk, hl]
    simp
  refine ⟨m, Module.finrank E W, B, M, hm, hB, gram_of_adapted_basis hb hcoords, ?_⟩
  intro R t i j
  fin_cases j
  · simpa using adapted_weight_column hmodel c he T U hTU hUT (Sum.inl 0) hecol R t i
  · simpa using adapted_weight_column hmodel c hf T U hTU hUT (Sum.inl 1) hfcol R t i

end AlignedModel

section HyperbolicAction

variable [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
variable {J : Type u} [Fintype J] [DecidableEq J]

local notation "σ" => quadraticConjugation F E
local notation "i₀" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ J)
local notation "i₁" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ J)

private theorem scalesHyperbolicLines_opposite
    {H : Matrix (Fin 2 ⊕ J) (Fin 2 ⊕ J) E} {M : Model G (quadraticConjugation F E) H}
    {c : Cocharacter G.val} {m : ℤ} (h : ScalesHyperbolicLines M c m) :
    ScalesHyperbolicLines M (oppositeCocharacter c) (-m) := by
  intro R t i j
  rw [opposite_point, h]
  by_cases hj : j = 0 <;> simp [hj, zpow_neg]

private theorem scalesHyperbolicLines_off_weight_zero
    {H : Matrix (Fin 2 ⊕ J) (Fin 2 ⊕ J) E} {M : Model G (quadraticConjugation F E) H}
    {c : Cocharacter G.val} {m : ℤ} (h : ScalesHyperbolicLines M c m)
    (hp : HyperbolicPair H i₀ i₁) (R : TestAlgebra F) (t : Rˣ)
    (i j : Fin 2 ⊕ J) (hne : weight i₀ i₁ i ≠ weight i₀ i₁ j) :
    M.matrix (cocharacterPoint c R t) i j = 0 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply (regular_iff_stabilizes hp M (cocharacterPoint c R t)).2 _ i j hlt
    intro k hk
    rw [h R t k 0, ite_eq_right hk]
  · apply (regular_iff_stabilizes (swap_pair hp) M (cocharacterPoint c R t)).2 _ i j _
    · intro k hk
      rw [h R t k 1, ite_eq_right hk]
    · rw [weight_swap hp.distinct, weight_swap hp.distinct]
      exact neg_lt_neg hgt

omit [Fintype J] in
private theorem pair_weight_injective (k : Fin 2) (j : Fin 2 ⊕ J) :
    weight i₀ i₁ (Sum.inl k) = weight i₀ i₁ j ↔ j = Sum.inl k := by
  rcases j with j | j
  · fin_cases k <;> fin_cases j <;>
      simp [weight, show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide]
  · fin_cases k <;> simp [weight]

private theorem scalesHyperbolicLines_row
    {H : Matrix (Fin 2 ⊕ J) (Fin 2 ⊕ J) E} {M : Model G (quadraticConjugation F E) H}
    {c : Cocharacter G.val} {m : ℤ} (h : ScalesHyperbolicLines M c m)
    (hp : HyperbolicPair H i₀ i₁) (R : TestAlgebra F) (t : Rˣ) (k : Fin 2) (j : Fin 2 ⊕ J) :
    M.matrix (cocharacterPoint c R t) (Sum.inl k) j =
      if j = Sum.inl k then algebraMap R (Coeff E R) (t ^ (if k = 0 then m else -m)).val else 0 := by
  by_cases hj : j = Sum.inl k
  · subst j
    simpa only [ite_true] using h R t (Sum.inl k) k
  · rw [ite_eq_right hj]
    exact scalesHyperbolicLines_off_weight_zero h hp R t _ _ (fun he => hj ((pair_weight_injective k j).1 he))

private theorem rankOneDiagonal_centralizes
    {H : Matrix (Fin 2 ⊕ J) (Fin 2 ⊕ J) E} {M : Model G (quadraticConjugation F E) H}
    {c : Cocharacter G.val} {m : ℤ}
    (h : ScalesHyperbolicLines M c m) (hp : HyperbolicPair H i₀ i₁)
    (d : Cocharacter G.val)
    (hd : ∀ (R : TestAlgebra F) (t : Rˣ),
      M.matrix (cocharacterPoint d R t) = diagonal i₀ i₁ t) :
    Centralizes c d.hom.hom := by
  let R₀ := CommAlgCat.of F (MonoidAlgebra F IntegerCharacters)
  let q : GroupPoints G.val R₀ := d.hom.hom
  apply (centralizes_onAlgebras c q).2
  intro R a t
  let p : GroupPoints (MultiplicativeGroup F) R := (testSpec F).map a.op
  let s := unitEquiv R p
  have hs : unitPoint R s = p := (unitEquiv R).injective (unitEquiv_unitPoint R _)
  change Commute (p ≫ d.hom.hom) (cocharacterPoint c R t)
  rw [← hs]
  change Commute (cocharacterPoint d R s) (cocharacterPoint c R t)
  apply matrix_injective M (R := R)
  rw [matrix_mul, matrix_mul, hd, diagonal]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases he : weight i₀ i₁ i = weight i₀ i₁ j
  · rw [he, mul_comm]
  · rw [scalesHyperbolicLines_off_weight_zero h hp R t i j he, mul_zero, zero_mul]

private theorem matrix_transvection_conj {I C : Type*} [Fintype I] [DecidableEq I] [CommRing C]
    (X : Matrix I I C) (i j : I) (a b r y : C)
    (hc : ∀ k, X k i = if k = i then a else 0)
    (hr : ∀ k, X j k = if k = j then b else 0)
    (hab : r * b = a) :
    X * (1 + Matrix.single i j y) = (1 + Matrix.single i j (r * y)) * X := by
  rw [mul_add, add_mul, mul_one, one_mul]
  congr 1
  ext k l
  by_cases hk : k = i <;> by_cases hl : l = j
  · subst k
    subst l
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same, hc i, hr j, ite_eq_left rfl,
      ite_eq_left rfl, ← hab]
    ring
  · subst k
    rw [Matrix.mul_single_apply_of_ne y i j i l hl X, Matrix.single_mul_apply_same, hr l,
      ite_eq_right hl, mul_zero]
  · subst l
    rw [Matrix.single_mul_apply_of_ne (r * y) i j k j hk X, Matrix.mul_single_apply_same, hc k,
      ite_eq_right hk, zero_mul]
  · rw [Matrix.mul_single_apply_of_ne y i j k l hl X,
      Matrix.single_mul_apply_of_ne (r * y) i j k l hk X]

private theorem transvection_scaling_on_hyperbolic_pair
    {H : Matrix (Fin 2 ⊕ J) (Fin 2 ⊕ J) E} {M : Model G (quadraticConjugation F E) H}
    {c : Cocharacter G.val} {m : ℤ}
    (h : ScalesHyperbolicLines M c m) (hp : HyperbolicPair H i₀ i₁)
    {A : AffineAlgebraicGroup F} (j : A.val ⟶ G.val)
    (e : (groupPointsFunctor F).obj A.val ≅ Specs.StandardGroups.specialLinearPoints F RankOneIndex.{u})
    (α : Eˣ)
    (hmatrix : ∀ (R : TestAlgebra F) (x : GroupPoints A.val R),
      M.matrix (((groupPointsFunctor F).map j).app R x) =
        planeMatrix α (show Matrix.SpecialLinearGroup RankOneIndex.{u} R from e.hom.app R x).val)
    {i k : Fin 2} (hik : i ≠ k)
    (R : TestAlgebra F) (t : Rˣ) (x : R) :
    let tr := transvectionPoint j e R
      (fun hu : (ULift.up i : RankOneIndex.{u}) = ULift.up k => hik (congrArg ULift.down hu))
    let n : ℤ := (if i = 0 then m else -m) - (if k = 0 then m else -m)
    cocharacterPoint c R t * tr x * (cocharacterPoint c R t)⁻¹ = tr ((t ^ n).val * x) := by
  dsimp only
  let tr := transvectionPoint j e R
    (fun hu : (ULift.up i : RankOneIndex.{u}) = ULift.up k => hik (congrArg ULift.down hu))
  let wt (j : Fin 2) : ℤ := if j = 0 then m else -m
  let n := wt i - wt k
  let T := cocharacterPoint c R t
  let C := Coeff E R
  let a := Algebra.TensorProduct.includeRight (R := F) (A := R) (B := E)
  let w : Fin 2 → C := ![a (α : E), 1]
  let v : Fin 2 → C := ![a (↑α⁻¹ : E), 1]
  let entry (x : R) := w i * algebraMap R C x * v k
  have htr (x : R) : M.matrix (tr x) = 1 + Matrix.single (Sum.inl i) (Sum.inl k) (entry x) := by
    let p := Matrix.SpecialLinearGroup.transvection
      (fun hu : (ULift.up i : RankOneIndex.{u}) = ULift.up k => hik (congrArg ULift.down hu)) x
    have hpoint : e.hom.app R (e.inv.app R p) = p :=
      ((e.app R).groupIsoToMulEquiv).apply_symm_apply p
    change M.matrix (((groupPointsFunctor F).map j).app R (e.inv.app R p)) = _
    rw [hmatrix, hpoint, planeMatrix_transvection α R hik]
  let r := algebraMap R C (t ^ n).val
  have hentry : entry ((t ^ n).val * x) = r * entry x := by
    dsimp only [entry, r]
    rw [map_mul]
    ring
  have hab : r * algebraMap R C (t ^ wt k).val = algebraMap R C (t ^ wt i).val := by
    dsimp only [r, n]
    rw [← map_mul, ← Units.val_mul, ← zpow_add, sub_add_cancel]
  change T * tr x * T⁻¹ = tr ((t ^ n).val * x)
  apply mul_inv_eq_iff_eq_mul.2
  apply matrix_injective M (R := R)
  rw [matrix_mul, matrix_mul, htr, htr, hentry]
  exact matrix_transvection_conj (M.matrix T) _ _ _ _ r (entry x)
    (fun a => h R t a i) (scalesHyperbolicLines_row h hp R t k) hab

end HyperbolicAction

section Finish

variable [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
variable {J : Type u} [Fintype J] [DecidableEq J]

local notation "σ" => quadraticConjugation F E
local notation "i₀" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ J)
local notation "i₁" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ J)

private theorem hasLimit_transvection_of_positive_weight
    {H : Matrix (Fin 2 ⊕ J) (Fin 2 ⊕ J) E} {M : Model G σ H}
    {c : Cocharacter G.val} {m : ℤ}
    (h : ScalesHyperbolicLines M c m) (hp : HyperbolicPair H i₀ i₁)
    {A : AffineAlgebraicGroup F} (j : A.val ⟶ G.val)
    (e : (groupPointsFunctor F).obj A.val ≅ Specs.StandardGroups.specialLinearPoints F RankOneIndex.{u})
    (α : Eˣ)
    (hmatrix : ∀ (R : TestAlgebra F) (x : GroupPoints A.val R),
      M.matrix (((groupPointsFunctor F).map j).app R x) =
        planeMatrix α (show Matrix.SpecialLinearGroup RankOneIndex.{u} R from e.hom.app R x).val)
    {i k : Fin 2} (hik : i ≠ k)
    (hpos : 0 < (if i = 0 then m else -m) - (if k = 0 then m else -m))
    (R : TestAlgebra F) (x : R) :
    HasLimit c (transvectionPoint j e R
      (fun hu : (ULift.up i : RankOneIndex.{u}) = ULift.up k => hik (congrArg ULift.down hu)) x) 1 := by
  let n : ℤ := (if i = 0 then m else -m) - (if k = 0 then m else -m)
  have hn : 0 < n := hpos
  apply transvection_hasLimit_of_scaling j e c _ (m := n.toNat) (by omega) _ R x
  intro T t y
  have hs := transvection_scaling_on_hyperbolic_pair h hp j e α hmatrix hik T t y
  dsimp only at hs
  change _ = transvectionPoint j e T _ ((t ^ n).val * y) at hs
  have he : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
  rw [← he, zpow_natCast] at hs
  exact hs

end Finish

set_option maxHeartbeats 150000 in
/-- The rank-one subgroup of the isotropic Hermitian model, marked relative
to the original regular cocharacter and maximal split torus. -/
theorem hermitianRankOne : Specs.Arithmetic.LocalMixingHermitianRankOne.Statement.{u} := by
  intro F _ _ _ _ G hG E _ _ _ _ n H
  dsimp only
  intro hH hisotropic hmodel S hS c hc
  let : Infinite F := localField_infinite F
  have hgen := IsotropicOuterTypeA.hermitianLocalGeneration H hH hisotropic G hmodel
  have hred := reductive_of_semisimple G hG.1
  obtain ⟨d₀, hnoncentral⟩ := noncentralCocharacter_of_isotropic H hH hisotropic hmodel
  let a := c ≫ S.inclusion
  have ha : ∃ (Y : SchemeOver F) (g : Y ⟶ G.val.X), ¬ Centralizes a g :=
    regularCocharacter_noncentral hred S hS c hc d₀ hnoncentral
  obtain ⟨m, r, B, M, hm, hB, hp, hscale⟩ := exists_aligned_hyperbolic_model H hH hmodel a ha
  obtain ⟨α, j, b, hj, hb, hmat, _, hpos, hneg, hDense⟩ :=
    rankOneWithGeneratingRadicals hG hgen B hB hp M
  let A := specialLinearGroup F RankOneIndex.{u}
  let e := specialLinearGroupPointsIso F RankOneIndex.{u}
  let d := b ≫ j
  have hdiagonal (R : TestAlgebra F) (t : Rˣ) :
      M.matrix (cocharacterPoint d R t) =
        diagonal (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)) t := by
    change M.matrix (cocharacterPoint (b ≫ j) R t) = _
    rw [cocharacterPoint_comp, hmat, hb, planeMatrix_diagonal]
  have hd := rankOneDiagonal_centralizes hscale hp d hdiagonal
  obtain ⟨s, hs⟩ := regularCentralizingCocharacter_factors hred S hS c hc d hd
  refine ⟨A, j, e, b, hj, hb, ⟨s, hs⟩, ?_, ?_, hDense⟩
  · intro R x
    exact ⟨transvection_limit_in_plane M α j e hmat d (by decide) hpos R x,
      transvection_limit_in_plane M α j e hmat (oppositeCocharacter d) (by decide) hneg R x⟩
  · have h := scalesHyperbolicLines_opposite hscale
    rcases lt_or_gt_of_ne hm with hlt | hgt
    · left
      intro x
      apply hasLimit_transvection_of_positive_weight h hp j e α hmat (i := 0) (k := 1) (by decide)
      simp only [ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false, neg_neg]
      omega
    · right
      intro x
      apply hasLimit_transvection_of_positive_weight h hp j e α hmat (i := 1) (k := 0) (by decide)
      simp only [ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false, neg_neg]
      omega

end

end LinearAlgebraicGroups.Arithmetic.LocalMixingHermitianRankOne
