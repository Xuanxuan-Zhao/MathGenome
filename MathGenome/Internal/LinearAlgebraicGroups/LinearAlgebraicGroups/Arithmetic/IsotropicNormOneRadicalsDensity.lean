import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.IsotropicNormOneRadicalsDensity
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OuterTypeAModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.InnerTypeALocalGeneration
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OppositeRadicals
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Topology
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct

universe u v

namespace LinearAlgebraicGroups.Arithmetic.IsotropicNormOneRadicalsDensity

open Specs.Arithmetic.IsotropicNormOneRadicalsDensity
open Specs.OuterTypeAModels (RepresentsNormOne)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.IntegralModels (MatrixRealization)
open AdelicGroups (PointsIn asMatrix)
open LocalNormOneCommutators.Spec (coordinateTopology elementary elementaryGroup)
open InnerTypeALocalGeneration.Spec (BlockDensity matrixCentralSimple)
open _root_.RM03.CSA
open _root_.RM03.CSA.NormOneGroup (normOneFunctor)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)
open _root_.LinearAlgebraicGroups.Descent.InnerTypeA.Specification (NormOneCoordinates normOneIdeal)

open private normOneEvaluate normOneEvaluate_coord normOneEvaluationHom normOneEvaluationHom_coord
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.InnerTypeA
open private coord_change from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.NormOneGroup
open private glVal_isEmbedding from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private continuous_linear_coordinate norm_algEquiv
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalNormOneCommutators

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

section Topology

variable {F A : Type u} [Field F] [Ring A] [Algebra F A] {ι : Type u} [Fintype ι]
variable {G : AffineAlgebraicGroup F}
variable (hA : IsCentralSimple F A) (b : Module.Basis ι F A)

private theorem normAt_ground (x : F ⊗[F] A) :
    normAt hA b x = reducedNorm hA (Algebra.TensorProduct.lid F A x) := by
  obtain ⟨a, rfl⟩ := (Algebra.TensorProduct.lid F A).symm.surjective x
  rw [AlgEquiv.apply_symm_apply, Algebra.TensorProduct.lid_symm_apply]
  change MvPolynomial.eval₂ (algebraMap F F) _ _ = _
  have he : (fun j => (b.baseChange F).repr ((1 : F) ⊗ₜ[F] a) j) = fun j => b.repr a j := by
    funext j
    simp only [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
    rfl
  rw [he]
  rw [show (algebraMap F F : F →+* F) = RingHom.id F from rfl, MvPolynomial.eval₂_id]
  exact reducedNorm_basis_eval hA b a

private theorem normOne_universal_evaluation (R : TestAlgebra F)
    (x : (normOneFunctor hA b).obj R) :
    let Q := NormOneCoordinates hA b
    let S := CommAlgCat.of F Q
    Algebra.TensorProduct.map (normOneEvaluationHom hA b R x) (AlgHom.id F A)
      (normOneEvaluate hA b S (AlgHom.id F Q)).val = x.val := by
  classical
  dsimp
  apply (b.baseChange R).equivFun.injective
  funext j
  change (b.baseChange R).repr _ j = (b.baseChange R).repr _ j
  let Q := NormOneCoordinates hA b
  let S := CommAlgCat.of F Q
  let f := normOneEvaluationHom hA b R x
  let gen := normOneEvaluate hA b S (AlgHom.id F Q)
  change (b.baseChange R).repr (_root_.RM03.CSA.NormOneGroup.changeCoefficients f gen.val) j = _
  exact (coord_change b f gen.val j).trans <|
    (congrArg f (normOneEvaluate_coord hA b S (AlgHom.id F Q) j)).trans
      (normOneEvaluationHom_coord hA b R x j)

private theorem asMatrix_natural (i : MatrixRealization G) {R S : TestAlgebra F} (f : R ⟶ S)
    (x : Points G.val.X R) :
    asMatrix i S (mapPoints f x) =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom (asMatrix i R x) := by
  let α := ((groupPointsFunctor F).map i.embedding) ≫ i.matrix.hom
  exact DFunLike.congr_fun (congrArg GrpCat.Hom.hom (α.naturality f)) x

omit [Fintype ι] in
private theorem continuous_polynomial {X : Type*} [TopologicalSpace X]
    [TopologicalSpace F] [IsTopologicalRing F]
    {c : X → ι → F} (hc : ∀ j, Continuous fun x => c x j) (p : MvPolynomial ι F) :
    Continuous fun x => MvPolynomial.aeval (c x) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa only [MvPolynomial.aeval_C] using (continuous_const (y := algebraMap F F a))
  | add p q hp hq =>
    simp only [map_add]
    exact continuous_add.comp (hp.prodMk hq)
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact continuous_mul.comp (hp.prodMk (hc j))

private theorem continuous_of_polynomial_coordinates
    [TopologicalSpace F] [IsTopologicalDivisionRing F]
    (point : ∀ R : TestAlgebra F, Points G.val.X R ≃ {x : R ⊗[F] A // normAt hA b x = 1})
    (natural : ∀ {R S : TestAlgebra F} (f : R ⟶ S) (x : Points G.val.X R),
      (point S (mapPoints f x)).val =
        Algebra.TensorProduct.map f.hom (.id F A) (point R x).val)
    (i : MatrixRealization G) {X : Type*} [TopologicalSpace X]
    (x : X → (normOneFunctor hA b).obj (CommAlgCat.of F F))
    (hx : ∀ j, Continuous fun z => (b.baseChange F).repr (x z).val j) :
    Continuous (show X → PointsIn i F from fun z => (point (CommAlgCat.of F F)).symm (x z)) := by
  classical
  let Q := NormOneCoordinates hA b
  let S := CommAlgCat.of F Q
  let gen := normOneEvaluate hA b S (AlgHom.id F Q)
  let g := (point S).symm gen
  let mat := asMatrix i S g
  let f (z : X) : S ⟶ CommAlgCat.of F F := CommAlgCat.ofHom (normOneEvaluationHom hA b _ (x z))
  have h (z : X) : mapPoints (f z) g = (point (CommAlgCat.of F F)).symm (x z) := by
    apply (point _).injective
    apply Subtype.ext
    rw [Equiv.apply_symm_apply, natural]
    simp only [g, Equiv.apply_symm_apply]
    exact normOne_universal_evaluation hA b _ (x z)
  apply (IsInducing.induced (asMatrix i F)).continuous_iff.mpr
  apply (glVal_isEmbedding (R := F) (ι := Specs.Unipotent.Index.{u} i.size)).isInducing.continuous_iff.mpr
  refine continuous_matrix fun j k => ?_
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (mat.val j k)
  have he (z : X) :
      ((asMatrix i F ((point (CommAlgCat.of F F)).symm (x z))).val j k) =
        MvPolynomial.aeval (fun l => (b.baseChange F).repr (x z).val l) p := by
    rw [← h z]
    have hm := asMatrix_natural i (f z) g
    rw [show asMatrix i F (mapPoints (f z) g) =
      Matrix.GeneralLinearGroup.map (f z).hom.toRingHom (asMatrix i S g) from hm]
    change (f z).hom (mat.val j k) = _
    rw [← hp]
    rfl
  change Continuous (fun z => (asMatrix i F ((point _).symm (x z))).val j k)
  simp_rw [he]
  exact continuous_polynomial hx p

end Topology

section Division

open Specs.Arithmetic.OppositeRadicals (MultiplicativeGroup IsNoncentral)
open Specs.DiagonalizableGroups (IntegerCharacters integerGenerator)
open CocharacterDynamics (unitPoint unitCoordinates cocharacterPoint)
open GrassmannianCharts (hom_ext_on_affines)
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private unitEquiv unitEquiv_unitPoint cocharacterPoint_mul
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

variable {F B : Type u} [Field F] [Ring B] [Algebra F B]

private abbrev tensorCoefficients (M : Type u) [DecidableEq M] :
    MonoidAlgebra F M ⊗[F] B ≃ₗ[F] M →₀ B :=
  TensorProduct.equivFinsuppOfBasisLeft (MonoidAlgebra.basis M F)

private theorem tensorCoefficients_monomial {M : Type u} [DecidableEq M]
    (m n : M) (b : B) :
    tensorCoefficients M ((MonoidAlgebra.single m (1 : F)) ⊗ₜ[F] b) n =
      if m = n then b else 0 := by
  unfold tensorCoefficients
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  by_cases h : m = n <;> simp [MonoidAlgebra.basis, h]

private theorem sum_monomial_tensor {M : Type u} [DecidableEq M]
    (x : MonoidAlgebra F M ⊗[F] B) :
    ∑ m ∈ (tensorCoefficients M x).support,
      (MonoidAlgebra.single m (1 : F)) ⊗ₜ[F] tensorCoefficients M x m = x := by
  calc
    _ = (tensorCoefficients M).symm (tensorCoefficients M x) := by
      conv_rhs => unfold tensorCoefficients
      rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
      rfl
    _ = x := (tensorCoefficients M).symm_apply_apply x

private abbrev changeMonomials {M N : Type u} [CommMonoid M] [CommMonoid N] (f : M →* N) :
    MonoidAlgebra F M ⊗[F] B →ₐ[F] MonoidAlgebra F N ⊗[F] B :=
  Algebra.TensorProduct.map (MonoidAlgebra.mapDomainAlgHom F F f) (.id F B)

private theorem changeMonomials_tmul {M N : Type u} [CommMonoid M] [CommMonoid N]
    (f : M →* N) (m : M) (b : B) :
    changeMonomials f (MonoidAlgebra.single m (1 : F) ⊗ₜ[F] b) =
      MonoidAlgebra.single (f m) (1 : F) ⊗ₜ[F] b := by
  simp [changeMonomials, MonoidAlgebra.mapDomainAlgHom_apply]

private theorem tensorCoefficients_sum {M : Type u} [DecidableEq M] {J : Type*}
    (s : Finset J) (y : J → MonoidAlgebra F M ⊗[F] B) (m : M) :
    tensorCoefficients M (∑ j ∈ s, y j) m =
      ∑ j ∈ s, tensorCoefficients M (y j) m :=
  (congrArg (fun f : M →₀ B => f m) (map_sum (tensorCoefficients M) y s)).trans
    (Finsupp.finsetSum_apply s (fun j => tensorCoefficients M (y j)) m)

set_option maxHeartbeats 700000 in
private theorem diagonal_tensor_coefficients {M : Type u} [CommMonoid M] [DecidableEq M]
    (x : MonoidAlgebra F M ⊗[F] B) (i j : M) :
    tensorCoefficients (M × M) (changeMonomials ((MonoidHom.id M).prod (MonoidHom.id M)) x)
      (i, j) = if i = j then tensorCoefficients M x i else 0 := by
  let c := tensorCoefficients M x
  conv_lhs => rw [← sum_monomial_tensor x]
  rw [map_sum (changeMonomials ((MonoidHom.id M).prod (MonoidHom.id M))), tensorCoefficients_sum]
  simp only [changeMonomials_tmul, tensorCoefficients_monomial,
    MonoidHom.prod_apply, MonoidHom.id_apply, Prod.mk.injEq]
  change (∑ m ∈ c.support, if m = i ∧ m = j then c m else 0) =
    if i = j then c i else 0
  by_cases hij : i = j
  · subst j
    simp only [and_self, ite_true, Finset.sum_ite_eq']
    split
    · rfl
    · rename_i hi
      exact (Finsupp.notMem_support_iff.mp hi).symm
  · rw [ite_eq_right hij]
    apply Finset.sum_eq_zero
    intro m _
    exact ite_eq_right (fun h => hij (h.1.symm.trans h.2))

set_option maxHeartbeats 700000 in
private theorem separate_tensor_coefficients {M : Type u} [CommMonoid M] [DecidableEq M]
    (x : MonoidAlgebra F M ⊗[F] B) (i j : M) :
    tensorCoefficients (M × M)
      (changeMonomials (MonoidHom.inl M M) x * changeMonomials (MonoidHom.inr M M) x) (i, j) =
      tensorCoefficients M x i * tensorCoefficients M x j := by
  let c := tensorCoefficients M x
  conv_lhs => rw [← sum_monomial_tensor x]
  rw [map_sum (changeMonomials (MonoidHom.inl M M)),
    map_sum (changeMonomials (MonoidHom.inr M M)), Finset.sum_mul, tensorCoefficients_sum]
  simp_rw [Finset.mul_sum, tensorCoefficients_sum]
  simp only [changeMonomials_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    MonoidAlgebra.single_mul_single, MonoidHom.inl_apply, MonoidHom.inr_apply,
    Prod.mk_mul_mk, mul_one, one_mul, tensorCoefficients_monomial, Prod.mk.injEq]
  change (∑ l ∈ c.support, ∑ k ∈ c.support,
    if l = i ∧ k = j then c l * c k else 0) = c i * c j
  have hc (l : M) : (if l ∈ c.support then c l else 0) = c l := by
    split
    · rfl
    · rename_i hl
      exact (Finsupp.notMem_support_iff.mp hl).symm
  have he (l k : M) :
      (if l = i ∧ k = j then c l * c k else 0) =
      (if l = i then c l else 0) * (if k = j then c k else 0) := by
    by_cases hl : l = i <;> by_cases hk : k = j <;> simp [hl, hk]
  simp_rw [he, ← Finset.mul_sum, Finset.sum_ite_eq', hc, ← Finset.sum_mul]
  rw [Finset.sum_ite_eq', hc]

private def characterUnit (M : Type u) [CommGroup M] (m : M) : (MonoidAlgebra F M)ˣ :=
  (MonoidAlgebra.of F M).toHomUnits m

private theorem map_characterUnit {M N : Type u} [CommGroup M] [CommGroup N]
    (f : M →* N) (m : M) :
    Units.map (MonoidAlgebra.mapDomainAlgHom F F f).toMonoidHom
      (characterUnit M m) = characterUnit N (f m) := by
  apply Units.ext
  change (MonoidAlgebra.mapDomainAlgHom F F f) (MonoidAlgebra.single m 1) =
    MonoidAlgebra.single (f m) 1
  simp [MonoidAlgebra.mapDomainAlgHom_apply]

private theorem map_unitPoint {R S : TestAlgebra F} (f : R ⟶ S) (t : Rˣ) :
    mapPoints f (unitPoint R t) = unitPoint S (Units.map f.hom.toMonoidHom t) := by
  change (testSpec F).map (CommAlgCat.ofHom f.hom).op ≫
    (testSpec F).map (CommAlgCat.ofHom (unitCoordinates R t)).op = _
  rw [← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply MonoidAlgebra.algHom_ext
  · intro m
    change f.hom (unitCoordinates R t (MonoidAlgebra.single m 1)) =
      unitCoordinates S (Units.map f.hom.toMonoidHom t) (MonoidAlgebra.single m 1)
    simp only [unitCoordinates, MonoidAlgebra.lift_single, one_smul, MonoidHom.comp_apply,
      Units.coeHom_apply, zpowersHom_apply]
    exact congrArg Units.val (map_zpow (Units.map f.hom.toMonoidHom) t _ )
  · ext

private theorem cocharacter_image_natural {G : GroupScheme F}
    (c : Specs.CharacterDescent.Cocharacter G)
    {R S : TestAlgebra F} (f : R ⟶ S) (t : Rˣ) :
    mapPoints f (cocharacterPoint c R t) =
      cocharacterPoint c S (Units.map f.hom.toMonoidHom t) := by
  change _ ≫ (unitPoint R t ≫ c.hom.hom) = unitPoint S _ ≫ c.hom.hom
  rw [← Category.assoc]
  congr 1
  exact map_unitPoint f t

private theorem universal_cocharacter_is_scalar {D : Type u} [DivisionRing D] [Algebra F D]
    (act : ∀ R : TestAlgebra F, Rˣ → R ⊗[F] D)
    (mul : ∀ (R : TestAlgebra F) (s t : Rˣ), act R (s * t) = act R s * act R t)
    (natural : ∀ {R S : TestAlgebra F} (f : R ⟶ S) (t : Rˣ),
      act S (Units.map f.hom.toMonoidHom t) =
        Algebra.TensorProduct.map f.hom (.id F D) (act R t)) :
    ∀ (R : TestAlgebra F) (t : Rˣ), ∃ z : R, act R t = z ⊗ₜ[F] (1 : D) := by
  classical
  let M := IntegerCharacters.{u}
  let T := CommAlgCat.of F (MonoidAlgebra F M)
  let S := CommAlgCat.of F (MonoidAlgebra F (M × M))
  let z := characterUnit (F := F) M integerGenerator
  let x := act T z
  let d := (MonoidHom.id M).prod (MonoidHom.id M)
  let l := MonoidHom.inl M M
  let r := MonoidHom.inr M M
  have hn (f : M →* M × M) : act S (characterUnit (M × M) (f integerGenerator)) =
      changeMonomials f x := by
    have h := natural (CommAlgCat.ofHom (MonoidAlgebra.mapDomainAlgHom F F f)) z
    change act S (Units.map (MonoidAlgebra.mapDomainAlgHom F F f).toMonoidHom z) = _ at h
    rw [map_characterUnit f integerGenerator] at h
    exact h
  have hm : changeMonomials d x = changeMonomials l x * changeMonomials r x := by
    rw [← hn d, ← hn l, ← hn r, ← mul]
    congr 1
    have he : d integerGenerator = l integerGenerator * r integerGenerator := by
      change (integerGenerator, integerGenerator) = (integerGenerator * 1, 1 * integerGenerator)
      simp
    rw [he]
    exact map_mul (MonoidAlgebra.of F (M × M)).toHomUnits _ _
  let a := tensorCoefficients M x
  have he (i j : M) : (if i = j then a i else 0) = a i * a j :=
    (diagonal_tensor_coefficients x i j).symm.trans <|
      (congrArg (fun t => tensorCoefficients (M × M) t (i, j)) hm).trans
        (separate_tensor_coefficients x i j)
  have hs : ∃ p : MonoidAlgebra F M, x = p ⊗ₜ[F] (1 : D) := by
    by_cases hz : ∀ i, a i = 0
    · refine ⟨0, ?_⟩
      apply (tensorCoefficients M).injective
      ext i
      simpa only [TensorProduct.zero_tmul, map_zero, Finsupp.zero_apply] using hz i
    · obtain ⟨i, hi⟩ := not_forall.mp hz
      have hii : a i * 1 = a i * a i := by simpa using he i i
      have hai : a i = 1 := (mul_left_cancel₀ hi hii).symm
      refine ⟨MonoidAlgebra.single i 1, ?_⟩
      apply (tensorCoefficients M).injective
      ext j
      rw [tensorCoefficients_monomial]
      change a j = _
      by_cases hij : i = j
      · subst j
        simp [hai]
      · simp [hij, show a j = 0 by simpa [hij, hai] using (he i j).symm]
  intro R t
  obtain ⟨p, hp⟩ := hs
  let f : T ⟶ R := CommAlgCat.ofHom (unitCoordinates R t)
  have hu : Units.map f.hom.toMonoidHom z = t := by
    apply Units.ext
    change unitCoordinates R t (MonoidAlgebra.single integerGenerator 1) = t.val
    simp only [unitCoordinates, MonoidAlgebra.lift_single, one_smul, MonoidHom.comp_apply,
      Units.coeHom_apply, zpowersHom_apply]
    exact congrArg Units.val (zpow_one t)
  refine ⟨f.hom p, ?_⟩
  have h := natural f z
  rw [hu] at h
  rw [h, show act T z = p ⊗ₜ[F] 1 from hp]
  rfl

private theorem cocharacter_central_of_division_presentation
    {A D : Type u} [Ring A] [Algebra F A] [DivisionRing D] [Algebra F D] (e : A ≃ₐ[F] D)
    (hA : IsCentralSimple F A) {ι : Type u} [Fintype ι] (b : Module.Basis ι F A)
    (G : AffineAlgebraicGroup F) (represent : RepresentsNormOne hA b G)
    (c : Specs.CharacterDescent.Cocharacter G.val) : ¬ IsNoncentral c := by
  obtain ⟨point, mul, natural⟩ := represent
  let E (R : TestAlgebra F) := Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[F] R) e
  let act (R : TestAlgebra F) (t : Rˣ) := E R (point R (cocharacterPoint c R t)).val
  have hem {R S : TestAlgebra F} (f : R ⟶ S) (x : R ⊗[F] A) :
      E S (Algebra.TensorProduct.map f.hom (.id F A) x) =
        Algebra.TensorProduct.map f.hom (.id F D) (E R x) := by
    induction x using TensorProduct.inductionOn with
    | tmul r a => rfl
    | add v w hv hw => simp only [map_add, hv, hw]
  have hscalar := universal_cocharacter_is_scalar act
    (fun R s t => by simp only [act, cocharacterPoint_mul, mul, map_mul])
    (fun f t => by
      dsimp only [act]
      rw [← cocharacter_image_natural, natural]
      exact hem f _)
  rintro ⟨X, g, hg⟩
  apply hg
  rw [centralizes_iff]
  intro Y y h
  apply hom_ext_on_affines
  intro R p
  simp only [MonObj.comp_mul]
  let t := unitEquiv R (p ≫ h)
  have ht : unitPoint R t = p ≫ h := (unitEquiv R).injective (unitEquiv_unitPoint R t)
  simp only [← Category.assoc (f := p) (g := h), ← ht]
  let w : GroupPoints G.val R := p ≫ y ≫ g
  change w * cocharacterPoint c R t = cocharacterPoint c R t * w
  apply (point R).injective
  apply Subtype.ext
  apply (E R).injective
  rw [mul, mul, map_mul, map_mul]
  obtain ⟨z, hz⟩ := hscalar R t
  rw [show E R (point R (cocharacterPoint c R t)).val = z ⊗ₜ[F] (1 : D) from hz]
  exact (Algebra.commutes (R := R) z _).symm

theorem divisionCocharactersCentral : DivisionCocharactersCentral.{u} := by
  intro F B _ _ _ hB ι _ b G represent c
  exact cocharacter_central_of_division_presentation (AlgEquiv.refl : B ≃ₐ[F] B)
    hB b G represent c

end Division

section Density

open scoped CategoryTheory.MonObj

open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open LocalNormOneCommutators.Spec (normOne)
open private testPointSections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration

variable {F A : Type u} [Field F] [Ring A] [Algebra F A]
variable {I : Type u} [Fintype I] {G : AffineAlgebraicGroup F}

private def normOnePointEquiv (hA : IsCentralSimple F A) (b : Module.Basis I F A)
    (R : TestAlgebra F)
    (point : GroupPoints G.val R ≃ {x : R ⊗[F] A // normAt hA b x = 1})
    (mul : ∀ x y, (point (x * y)).val = (point x).val * (point y).val) :
    GroupPoints G.val R ≃* (normOneFunctor hA b).obj R :=
  { point with map_mul' := fun x y => Subtype.ext (mul x y) }

private def pointMatrixHom {M : Type u} [Ring M] [Algebra F M]
    (hA : IsCentralSimple F A) (b : Module.Basis I F A)
    (point : GroupPoints G.val (CommAlgCat.of F F) ≃* (normOneFunctor hA b).obj (CommAlgCat.of F F))
    (e : A ≃ₐ[F] M) (i : MatrixRealization G) :
    PointsIn i F →* Mˣ :=
  let pointVal : (normOneFunctor hA b).obj (CommAlgCat.of F F) →* F ⊗[F] A :=
    { toFun := Subtype.val
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let f := e.toMonoidHom.comp ((Algebra.TensorProduct.lid F A).toMonoidHom.comp
      (pointVal.comp point.toMonoidHom))
  f.toHomUnits

private theorem inverse_point_continuous [TopologicalSpace F] [IsTopologicalDivisionRing F]
    (hA : IsCentralSimple F A) (b : Module.Basis I F A)
    (point : ∀ R : TestAlgebra F, Points G.val.X R ≃ {x : R ⊗[F] A // normAt hA b x = 1})
    (natural : ∀ {R S : TestAlgebra F} (f : R ⟶ S) (x : Points G.val.X R),
      (point S (mapPoints f x)).val = Algebra.TensorProduct.map f.hom (.id F A) (point R x).val)
    {M : Type u} [Ring M] [Algebra F M] (hM : IsCentralSimple F M) (e : A ≃ₐ[F] M)
    {J : Type*} [Fintype J] (basis : Module.Basis J F M) (i : MatrixRealization G) :
    letI := coordinateTopology basis
    ∃ f : {x : Mˣ // x ∈ normOne hM} → PointsIn i F,
      Continuous f ∧ ∀ x, e (Algebra.TensorProduct.lid F A
        (point (CommAlgCat.of F F) (f x)).val) = (x.val : M) := by
  letI := coordinateTopology basis
  let lift (z : {x : Mˣ // x ∈ normOne hM}) : (normOneFunctor hA b).obj (CommAlgCat.of F F) :=
    ⟨(1 : F) ⊗ₜ[F] e.symm (z.val : M), by
      change normAt hA b ((1 : F) ⊗ₜ[F] e.symm (z.val : M)) = 1
      rw [normAt_ground hA b, Algebra.TensorProduct.lid_tmul, one_smul,
        norm_algEquiv hA hM e, AlgEquiv.apply_symm_apply]
      exact z.property⟩
  let f : {x : Mˣ // x ∈ normOne hM} → PointsIn i F := fun z => (point _).symm (lift z)
  refine ⟨f, ?_, ?_⟩
  · apply continuous_of_polynomial_coordinates hA b point natural i lift
    intro j
    have he (z : {x : Mˣ // x ∈ normOne hM}) :
        (b.baseChange F).repr (lift z).val j = b.repr (e.symm (z.val : M)) j := by
      change (b.baseChange F).repr ((1 : F) ⊗ₜ[F] e.symm (z.val : M)) j = _
      rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
      rfl
    simp_rw [he]
    exact (continuous_linear_coordinate basis ((b.coord j).comp e.symm.toLinearMap)).comp
      (Units.continuous_val.comp continuous_subtype_val)
  · intro z
    change e (Algebra.TensorProduct.lid F A (point (CommAlgCat.of F F) ((point _).symm (lift z))).val) = _
    rw [Equiv.apply_symm_apply]
    change e (Algebra.TensorProduct.lid F A ((1 : F) ⊗ₜ[F] e.symm (z.val : M))) = _
    rw [Algebra.TensorProduct.lid_tmul, one_smul, AlgEquiv.apply_symm_apply]

private theorem density_from_blocks [TopologicalSpace F] [IsTopologicalDivisionRing F]
    (hA : IsCentralSimple F A) (b : Module.Basis I F A)
    (represent : RepresentsNormOne hA b G)
    {B : Type u} [DivisionRing B] [Algebra F B] (hB : IsCentralSimple F B)
    {m : ℕ} (hm : 2 ≤ m) (e : A ≃ₐ[F] Matrix (Fin m) (Fin m) B)
    (density : BlockDensity hB m hm) (radicals : ElementaryInRadicals.{u})
    (i : MatrixRealization G) : Dense (generatedPoints i) := by
  classical
  obtain ⟨point, mul, natural⟩ := represent
  let M := Matrix (Fin m) (Fin m) B
  let hM : IsCentralSimple F M := matrixCentralSimple hB (by omega : 0 < m)
  letI := hM.2.2
  let basis := Module.finBasis F M
  letI := coordinateTopology basis
  let xmap := pointMatrixHom hA b (normOnePointEquiv hA b _ (point _) (mul _)) e i
  have xmap_val (x : PointsIn i F) :
      (xmap x : M) = e (Algebra.TensorProduct.lid F A (point (CommAlgCat.of F F) x).val) := rfl
  have xmap_mem (x : PointsIn i F) : xmap x ∈ normOne hM := by
    change reducedNorm hM (xmap x : M) = 1
    rw [xmap_val, ← norm_algEquiv hA hM e, ← normAt_ground hA b]
    exact (point _ x).property
  have xmap_inj : Function.Injective xmap := by
    intro x y h
    apply (point _).injective
    apply Subtype.ext
    apply (Algebra.TensorProduct.lid F A).injective
    apply e.injective
    rw [← xmap_val, ← xmap_val, h]
  let H := (unipotentGenerated G).map (testPointSections G.val).symm.toMonoidHom
  have hH (x : PointsIn i F) : x ∈ H ↔ x ∈ generatedPoints i := by
    change (∃ p ∈ unipotentGenerated G, (testPointSections G.val).symm p = x) ↔ _
    simp only [generatedPoints, Set.mem_ofPred_eq]
    have he (p : 𝟙_ (SchemeOver F) ⟶ G.val.X) :
        (testPointSections G.val).symm p = toUnit _ ≫ p := by
      change _ ≫ p = _
      exact congrArg (· ≫ p) (toUnit_unique _ _)
    change (∃ p ∈ unipotentGenerated G, (testPointSections G.val).symm p = x) ↔
      (∃ p ∈ unipotentGenerated G, toUnit ((testSpec F).obj (op (CommAlgCat.of F F))) ≫ p = x)
    simp only [he]
    rfl
  let E := elementaryGroup (B := B) (Fin m)
  have hE : E ≤ H.map xmap := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨r, s, hrs, a, rfl⟩
    obtain ⟨x, hx, hval⟩ := radicals hA b G point mul natural e i r s hrs a
    exact ⟨x, (hH x).mpr hx, Units.ext ((xmap_val x).trans hval)⟩
  obtain ⟨f, hcont, hf⟩ := inverse_point_continuous hA b point natural hM e basis i
  have hinv (x : PointsIn i F) : f ⟨xmap x, xmap_mem x⟩ = x :=
    xmap_inj (Units.ext ((xmap_val _).trans (hf _)))
  let S : Set {y : Mˣ // y ∈ normOne hM} := {y | y.val ∈ E}
  have hS : Subtype.val '' S = (E : Set Mˣ) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, density.1 hy⟩, hy, rfl⟩
  intro x
  let y : {y : Mˣ // y ∈ normOne hM} := ⟨xmap x, xmap_mem x⟩
  have hy : y ∈ closure S := by
    rw [closure_subtype, hS]
    exact density.2 basis y.property
  have hmap : f '' S ⊆ generatedPoints i := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨x', hx', hval⟩ := hE hz
    apply (hH _).mp
    have : f z = x' := xmap_inj (Units.ext ((xmap_val _).trans
      ((hf z).trans (congrArg Units.val hval).symm)))
    rw [this]
    exact hx'
  rw [← hinv x]
  exact closure_mono hmap (image_closure_subset_closure_image hcont ⟨y, hy, rfl⟩)

end Density

section NormOneGeometry

open Specs.GeometricRadicals (IsReductive IsSemisimple)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open CocharacterDynamics
open _root_.RM03.CSA.NormOneGroup
  (normAt_natural extendSplitting_tmul normAt_eq_det normHom changeCoefficients)
open private splitNormOnePoints baseChangePointIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.InnerTypeA
open private connected_baseChange_iff smooth_baseChange_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private geometricallyConnected_of_connected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private reductive_of_semisimple
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility

variable {F A : Type u} [Field F] [Ring A] [Algebra F A] {I : Type u} [Fintype I]
variable {G : AffineAlgebraicGroup F}

private def normOnePointsIso (hA : IsCentralSimple F A) (b : Module.Basis I F A)
    (point : ∀ R : TestAlgebra F, Points G.val.X R ≃ {x : R ⊗[F] A // normAt hA b x = 1})
    (mul : ∀ R (x y : GroupPoints G.val R),
      (point R (x * y)).val = (point R x).val * (point R y).val)
    (natural : ∀ {R S : TestAlgebra F} (f : R ⟶ S) (x : Points G.val.X R),
      (point S (mapPoints f x)).val = Algebra.TensorProduct.map f.hom (.id F A) (point R x).val) :
    (groupPointsFunctor F).obj G.val ≅ normOneFunctor hA b :=
  NatIso.ofComponents (fun R => (normOnePointEquiv hA b R (point R) (mul R)).toGrpIso) (by
    intro R S f
    apply GrpCat.ext
    intro x
    exact Subtype.ext (natural f x))

private theorem normOne_reductive (hA : IsCentralSimple F A) (b : Module.Basis I F A)
    (model : (groupPointsFunctor F).obj G.val ≅ normOneFunctor hA b) : IsReductive G := by
  let K := AlgebraicClosure F
  obtain ⟨s⟩ := algEquiv_matrix_algebraicClosure hA
  let G' := baseChangedAlgebraicGroup K G
  let split := baseChangePointIso (K := K) G.val ≪≫
    (Functor.isoWhiskerLeft (restrictTestAlgebra F K) model) ≪≫ splitNormOnePoints hA b s
  have hn := degree_pos hA
  obtain ⟨n, en⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h : IsSemisimple G' := by
    have hs : Specs.GeneralLinearStructure.SpecialMatrixPoints G' (degree F A) := split
    rw [en] at hs
    exact RootData.SpecialLinearDatum.semisimple K n G' hs
  letI := h.2.1
  have hsm : Smooth G.val.X.hom := (smooth_baseChange_iff (K := K) G.val.X).mp h.1
  have hconn : ConnectedSpace G.val.X.left := (connected_baseChange_iff (K := K) G).mp
    (GeometricallyConnected.connectedSpace_of_subsingleton (f := G'.val.X.hom))
  exact (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) G hsm
    (geometricallyConnected_of_connected G)).mp (reductive_of_semisimple G' h)

private theorem normAt_one_add_square_zero (hA : IsCentralSimple F A) (b : Module.Basis I F A)
    {x : A} (hx : x * x = 0) (R : TestAlgebra F) (r : R) :
    normAt hA b (1 + r ⊗ₜ[F] x) = 1 := by
  classical
  let K := AlgebraicClosure F
  obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure hA
  let N := e (1 ⊗ₜ[F] x)
  have hN : N * N = 0 := by
    simp only [N, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, hx, TensorProduct.tmul_zero, map_zero]
  have hu : IsUnit (Matrix.charpolyRev (-N)) := by
    apply Matrix.isUnit_charpolyRev_of_isNilpotent
    refine ⟨2, ?_⟩
    rwa [pow_two, neg_mul_neg]
  obtain ⟨a, _, ha⟩ := Polynomial.isUnit_iff.mp hu
  have ha1 : a = 1 := by
    have he := congrArg (Polynomial.eval (0 : K)) ha
    change Polynomial.eval (0 : K) (Polynomial.C a) =
      Polynomial.eval (0 : K) (Matrix.charpolyRev (-N)) at he
    simpa using he
  subst a
  have hd : Matrix.det (1 + (Polynomial.X : Polynomial K) • N.map Polynomial.C) = 1 := by
    rw [Matrix.charpolyRev, ← Polynomial.C.mapMatrix_apply, map_neg,
      Polynomial.C.mapMatrix_apply, smul_neg, sub_neg_eq_add] at ha
    exact ha.symm
  let L := CommAlgCat.of F (Polynomial F)
  let M := CommAlgCat.of F (Polynomial K)
  let f : Polynomial F →ₐ[F] Polynomial K :=
    Polynomial.mapAlgHom (Algebra.ofId F K)
  let z : L ⊗[F] A := 1 + Polynomial.X ⊗ₜ[F] x
  have hz : normAt hA b z = 1 := by
    have hf : Function.Injective f := Polynomial.map_injective _ (algebraMap F K).injective
    apply hf
    rw [map_one]
    change f (_root_.RM03.CSA.NormOneGroup.normAt hA b z) = _
    rw [← normAt_natural hA b f z, normAt_eq_det hA b e]
    change Matrix.det (_root_.RM03.CSA.NormOneGroup.extendSplitting e
      (changeCoefficients f (1 + (Polynomial.X : Polynomial F) ⊗ₜ[F] x))) = _
    simp only [changeCoefficients, map_add, map_one, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, extendSplitting_tmul]
    change Matrix.det (1 + Polynomial.map (algebraMap F K) Polynomial.X • N.map Polynomial.C) = 1
    rw [Polynomial.map_X]
    exact hd
  let ev : Polynomial F →ₐ[F] R := Polynomial.aeval r
  have h := normAt_natural hA b ev z
  have hzr : _root_.RM03.CSA.NormOneGroup.normAt hA b z = 1 := hz
  rw [hzr, map_one] at h
  have hx' : ev Polynomial.X = r := Polynomial.aeval_X r
  change _root_.RM03.CSA.NormOneGroup.normAt hA b (1 + r ⊗ₜ[F] x) = 1
  simpa only [z, changeCoefficients, map_add, map_one, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, hx'] using h

end NormOneGeometry

section LocalDensity

open Specs.Arithmetic.OppositeRadicals (IsNoncentral)

private theorem density_over {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    (radicals : ElementaryInRadicals.{u})
    (blockDensity : ∀ {B : Type u} [DivisionRing B] [Algebra F B]
      (hB : IsCentralSimple F B) (m : ℕ) (hm : 2 ≤ m), BlockDensity hB m hm) :
    DensityOver (F := F) := by
  classical
  intro A _ _ hA I _ b G repr ⟨c, hc⟩ i
  obtain ⟨m, B, _, _, hB', hm, ⟨e⟩⟩ := MatrixDivision.exists_presentation F A hA
  have hB := isCentralSimple_of_isCentralDivision F B hB'
  have hm' : 2 ≤ m := by
    by_contra h
    have he : m = 1 := by omega
    subst m
    let oneEntry : Matrix (Fin 1) (Fin 1) B ≃ₐ[F] B :=
      { toFun := fun M => M 0 0
        invFun := fun a => Matrix.of fun _ _ => a
        left_inv := fun M => by ext r s; fin_cases r; fin_cases s; rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_mul' := fun M N => by simp [Matrix.mul_apply]
        commutes' := fun a => by simp [Matrix.algebraMap_matrix_apply] }
    exact cocharacter_central_of_division_presentation (e.trans oneEntry) hA b G repr c hc
  exact density_from_blocks hA b repr hB hm' e (blockDensity hB m hm') radicals i

private theorem local_density_of_elementary (radicals : ElementaryInRadicals.{u})
    (radicalsZero : ElementaryInRadicals.{0}) :
    LocalDensity.{u} := by
  have block := InnerTypeALocalGeneration.localBlockGeneration.{u,u}
  refine ⟨?_, ?_, ?_⟩
  · intro F _ _ _ _
    exact density_over radicals (fun hB m hm => block.1 hB m hm)
  · exact density_over radicalsZero (fun hB m hm =>
      InnerTypeALocalGeneration.localBlockGeneration.{0,0}.2.1 hB m hm)
  · exact density_over radicalsZero (fun hB m hm =>
      InnerTypeALocalGeneration.localBlockGeneration.{0,0}.2.2 hB m hm)

end LocalDensity

private abbrev BlockMatrix (m : ℕ) (R : Type*) := Matrix (Fin m) (Fin m) R

section BlockMatrices

open Matrix
open Algebra.TensorProduct (map_tmul tmul_mul_tmul)
open CocharacterDynamics
open Specs.Arithmetic.OppositeRadicals (MultiplicativeGroup)
open _root_.RM03.CSA.NormOneGroup (normHom)
open LocalNormOneCommutators (diagonalSlot val_diagonalSlot diagonal_pair_mem)
open private unitPointHom_apply unitPointHom
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

variable {F A B : Type u} [Field F] [Ring A] [Algebra F A] [Ring B] [Algebra F B]
variable {m : ℕ}

private theorem offDiagonalEntry_sq_zero (e : A ≃ₐ[F] BlockMatrix m B)
    (i j : Fin m) (hij : i ≠ j) (a : B) :
    e.symm (Matrix.single i j a) * e.symm (Matrix.single i j a) = 0 := by
  apply e.injective
  rw [map_mul, map_zero, AlgEquiv.apply_symm_apply,
    Matrix.single_mul_single_of_ne _ i j i hij.symm _]

private def blockTensor (R : TestAlgebra F) (e : A ≃ₐ[F] BlockMatrix m B) :
    R ⊗[F] A ≃ₐ[F] BlockMatrix m (R ⊗[F] B) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[F] R)
    (e.trans (matrixEquivTensor (Fin m) F B))).trans
    ((Algebra.TensorProduct.assoc F F F R B (BlockMatrix m F)).symm.trans
      (matrixEquivTensor (Fin m) F (R ⊗[F] B)).symm)

private theorem blockTensor_single (R : TestAlgebra F) (e : A ≃ₐ[F] BlockMatrix m B)
    (t : R) (i j : Fin m) (a : B) :
    blockTensor R e (t ⊗ₜ[F] e.symm (Matrix.single i j a)) =
      Matrix.single i j (t ⊗ₜ[F] a) := by
  simp only [blockTensor, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq,
    AlgEquiv.apply_symm_apply, matrixEquivTensor_apply_single, Algebra.TensorProduct.assoc_symm_tmul,
    matrixEquivTensor_apply_symm, Matrix.map_single, map_one, Matrix.smul_single,
    smul_eq_mul, mul_one]

private abbrev scalarMatrices (R : TestAlgebra F) :
    BlockMatrix m R →+* BlockMatrix m (R ⊗[F] B) :=
  (algebraMap R (R ⊗[F] B)).mapMatrix

private def diagonalPair (i j : Fin m) {R : Type u} [CommRing R] (t : Rˣ) : (BlockMatrix m R)ˣ :=
  diagonalSlot i t * diagonalSlot j t⁻¹

private theorem diagonalPair_val (i j : Fin m) (hij : i ≠ j)
    {R : Type u} [CommRing R] (t : Rˣ) :
    (diagonalPair i j t : BlockMatrix m R) =
      Matrix.diagonal (fun k => if k = i then t.val else if k = j then (t⁻¹).val else 1) := by
  simp only [diagonalPair, Units.val_mul, val_diagonalSlot, diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all

private theorem diagonalPair_mul (i j : Fin m) (hij : i ≠ j)
    {R : Type u} [CommRing R] (t s : Rˣ) :
    diagonalPair i j (t * s) = diagonalPair i j t * diagonalPair i j s := by
  apply Units.ext
  simp only [Units.val_mul, diagonalPair_val i j hij, diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases hi : k = i <;> by_cases hj : k = j <;> simp [hi, hj, hij.symm, mul_comm]

private def diagonalTensor (R : TestAlgebra F) (e : A ≃ₐ[F] BlockMatrix m B)
    (i j : Fin m) (t : Rˣ) : R ⊗[F] A :=
  1 + (t.val - 1) ⊗ₜ[F] e.symm (Matrix.single i i 1) +
    ((t⁻¹).val - 1) ⊗ₜ[F] e.symm (Matrix.single j j 1)

private theorem blockTensor_diagonal (R : TestAlgebra F) (e : A ≃ₐ[F] BlockMatrix m B)
    (i j : Fin m) (hij : i ≠ j) (t : Rˣ) :
    blockTensor R e (diagonalTensor R e i j t) =
      scalarMatrices (B := B) R (diagonalPair i j t : BlockMatrix m R) := by
  simp only [diagonalTensor, map_add, map_one, blockTensor_single, diagonalPair_val i j hij]
  ext k l
  change (_ : BlockMatrix m (R ⊗[F] B)) k l =
    algebraMap R (R ⊗[F] B) ((Matrix.diagonal _) k l)
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, Matrix.add_apply, Matrix.diagonal_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hk : k = l
  · subst l
    by_cases hi : k = i <;> by_cases hj : k = j <;>
      simp_all [eq_comm, Algebra.TensorProduct.one_def, ← TensorProduct.add_tmul]
  · have hi : ¬ (i = k ∧ i = l) := fun h => hk (h.1.symm.trans h.2)
    have hj : ¬ (j = k ∧ j = l) := fun h => hk (h.1.symm.trans h.2)
    simp [hk, hi, hj]

private theorem diagonalTensor_normOne {I : Type u} [Fintype I]
    (hA : IsCentralSimple F A) (b : Module.Basis I F A)
    (R : TestAlgebra F) (e : A ≃ₐ[F] BlockMatrix m B)
    (i j : Fin m) (hij : i ≠ j) (t : Rˣ) :
    normAt hA b (diagonalTensor R e i j t) = 1 := by
  let φ := (blockTensor R e).symm.toMonoidHom.comp (scalarMatrices (B := B) R).toMonoidHom
  let N := Units.map ((normHom (R := R) hA b).comp φ)
  have h : elementaryGroup (B := R) (Fin m) ≤ N.ker := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k, l, hkl, r, rfl⟩
    apply Units.ext
    change normAt hA b (φ (1 + Matrix.single k l r)) = 1
    have hφ : φ (1 + Matrix.single k l r) =
        1 + r ⊗ₜ[F] e.symm (Matrix.single k l (1 : B)) := by
      apply (blockTensor R e).injective
      have hsingle :
          scalarMatrices (B := B) R (Matrix.single k l r) =
            Matrix.single k l (r ⊗ₜ[F] (1 : B)) :=
        Matrix.map_single _ _ _ (algebraMap R (R ⊗[F] B))
      change blockTensor R e ((blockTensor R e).symm
        (scalarMatrices (B := B) R (1 + Matrix.single k l r))) = _
      rw [AlgEquiv.apply_symm_apply, map_add, map_one, hsingle, map_add, map_one,
        blockTensor_single]
    rw [hφ]
    exact normAt_one_add_square_zero hA b (offDiagonalEntry_sq_zero e k l hkl 1) R r
  have hdiag := h (diagonal_pair_mem i j hij t)
  have hn : normAt hA b (φ (diagonalPair i j t : BlockMatrix m R)) = 1 :=
    congrArg Units.val hdiag
  have hv : φ (diagonalPair i j t : BlockMatrix m R) = diagonalTensor R e i j t :=
    (blockTensor R e).symm_apply_eq.mpr (blockTensor_diagonal R e i j hij t).symm
  rw [hv] at hn
  exact hn

private theorem diagonalTensor_mul (R : TestAlgebra F) (e : A ≃ₐ[F] BlockMatrix m B)
    (i j : Fin m) (hij : i ≠ j) (s t : Rˣ) :
    diagonalTensor R e i j (s * t) =
      diagonalTensor R e i j s * diagonalTensor R e i j t := by
  apply (blockTensor R e).injective
  rw [map_mul, blockTensor_diagonal R e i j hij, blockTensor_diagonal R e i j hij,
    blockTensor_diagonal R e i j hij, diagonalPair_mul i j hij, Units.val_mul, map_mul]

private theorem diagonalTensor_natural {R S : TestAlgebra F} (f : R ⟶ S)
    (e : A ≃ₐ[F] BlockMatrix m B) (i j : Fin m) (t : Rˣ) :
    Algebra.TensorProduct.map f.hom (.id F A) (diagonalTensor R e i j t) =
      diagonalTensor S e i j (Units.map f.hom.toMonoidHom t) := by
  simp only [diagonalTensor, map_add, map_one, map_tmul, AlgHom.id_apply, map_sub, ← map_inv]
  rfl

private theorem diagonalTensor_conj (R : TestAlgebra F) (e : A ≃ₐ[F] BlockMatrix m B)
    (i j : Fin m) (hij : i ≠ j) (t : Rˣ) (a : B) :
    diagonalTensor R e i j t * (1 + (1 : R) ⊗ₜ[F] e.symm (Matrix.single i j a)) *
      diagonalTensor R e i j t⁻¹ =
      1 + (t.val ^ 2) ⊗ₜ[F] e.symm (Matrix.single i j a) := by
  let D := diagonalTensor R e i j t
  let D' := diagonalTensor R e i j t⁻¹
  have hone : D * D' = 1 := by
    change diagonalTensor R e i j t * diagonalTensor R e i j t⁻¹ = 1
    rw [← diagonalTensor_mul R e i j hij, mul_inv_cancel]
    simp [diagonalTensor]
  rw [mul_add, mul_one, add_mul, hone]
  congr 1
  apply (blockTensor R e).injective
  simp only [map_mul, blockTensor_diagonal R e i j hij, blockTensor_single, diagonalPair_val i j hij]
  let d (t : Rˣ) (k : Fin m) : R ⊗[F] B :=
    (if k = i then t.val else if k = j then (t⁻¹).val else 1) ⊗ₜ[F] (1 : B)
  have hmap (s : Rˣ) : scalarMatrices (B := B) R
      (Matrix.diagonal (fun k => if k = i then s.val else if k = j then (s⁻¹).val else 1)) =
      Matrix.diagonal (d s) := by
    ext k l
    change algebraMap R (R ⊗[F] B) (Matrix.diagonal _ k l) = _
    by_cases hkl : k = l <;> simp [d, hkl]
  rw [hmap t, hmap t⁻¹]
  ext k l
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hki : i = k <;> by_cases hlj : j = l
  · subst k
    subst l
    simp [d, hij.symm, pow_two, tmul_mul_tmul]
  · simp [hlj]
  · simp [hki]
  · simp [hki]

end BlockMatrices

section RadicalComparison

open scoped CategoryTheory.MonObj

open Specs.CharacterDescent (Cocharacter)
open Specs.Arithmetic.OppositeRadicals (MultiplicativeGroup)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open CocharacterDynamics
open private unitEquiv unitEquiv_unitPoint unitPointHom_apply unitPointHom
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private contracting_le_unipotentGenerated testPointSections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private rationalSourceIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalDensity

variable {F A B : Type u} [Field F] [Ring A] [Algebra F A] [Ring B] [Algebra F B]
variable {G : AffineAlgebraicGroup F} {I : Type u} [Fintype I]
variable {m : ℕ} (hA : IsCentralSimple F A) (b : Module.Basis I F A)

private theorem exists_diagonal_cocharacter
    (model : (groupPointsFunctor F).obj G.val ≅ normOneFunctor hA b)
    (e : A ≃ₐ[F] BlockMatrix m B) (i j : Fin m) (hij : i ≠ j) :
    ∃ c : Cocharacter G.val, ∀ (R : TestAlgebra F) (t : Rˣ),
      (model.hom.app R (cocharacterPoint c R t)).val = diagonalTensor R e i j t := by
  let d (R : TestAlgebra F) : Rˣ →* (normOneFunctor hA b).obj R :=
    { toFun t := ⟨diagonalTensor R e i j t, diagonalTensor_normOne hA b R e i j hij t⟩
      map_one' := by
        apply Subtype.ext
        change diagonalTensor R e i j 1 = 1
        simp [diagonalTensor]
      map_mul' s t := Subtype.ext (diagonalTensor_mul R e i j hij s t) }
  let α : (groupPointsFunctor F).obj (MultiplicativeGroup F) ⟶ normOneFunctor hA b :=
    { app := fun R => GrpCat.ofHom ((d R).comp (unitEquiv R).toMonoidHom)
      naturality := by
        intro R S f
        apply GrpCat.ext
        intro x
        apply Subtype.ext
        let t := unitEquiv R x
        have ht : unitPoint R t = x := (unitEquiv R).injective (unitEquiv_unitPoint R t)
        change diagonalTensor S e i j (unitEquiv S (mapPoints f x)) =
          Algebra.TensorProduct.map f.hom (.id F A) (diagonalTensor R e i j t)
        rw [← ht, map_unitPoint, unitEquiv_unitPoint]
        exact (diagonalTensor_natural f e i j t).symm }
  obtain ⟨c, hc⟩ := (groupHomComparison F (MultiplicativeGroup F) G.val (isAffine_Spec _)).2
    (α ≫ model.inv)
  refine ⟨c, fun R t => ?_⟩
  have h : (groupPointsFunctor F).map c ≫ model.hom = α := by
    change (groupPointsFunctor F).map c = α ≫ model.inv at hc
    rw [hc]
    simp
  have he := DFunLike.congr_fun (congrArg (fun τ => (τ.app R).hom) h) (unitPoint R t)
  change model.hom.app R (cocharacterPoint c R t) = α.app R (unitPoint R t) at he
  rw [he]
  change diagonalTensor R e i j (unitEquiv R (unitPoint R t)) = _
  rw [unitEquiv_unitPoint]

private theorem cocharacterPoint_inv (c : Cocharacter G.val)
    (R : TestAlgebra F) (t : Rˣ) :
    cocharacterPoint c R t⁻¹ = (cocharacterPoint c R t)⁻¹ := by
  simp only [cocharacterPoint, ← unitPointHom_apply, map_inv]

private theorem block_hasLimit
    (model : (groupPointsFunctor F).obj G.val ≅ normOneFunctor hA b)
    (e : A ≃ₐ[F] BlockMatrix m B) (i j : Fin m) (hij : i ≠ j) (a : B)
    (c : Cocharacter G.val)
    (hc : ∀ (R : TestAlgebra F) (t : Rˣ),
      (model.hom.app R (cocharacterPoint c R t)).val = diagonalTensor R e i j t)
    (x : GroupPoints G.val (CommAlgCat.of F F))
    (hx : (model.hom.app (CommAlgCat.of F F) x).val =
      1 + (1 : F) ⊗ₜ[F] e.symm (Matrix.single i j a)) :
    HasLimit c x 1 := by
  let R := CommAlgCat.of F F
  let P := polynomialAlgebra R
  let L := laurentAlgebra R
  let u := laurentParameter R
  let q := e.symm (Matrix.single i j a)
  have hq : q * q = 0 := offDiagonalEntry_sq_zero e i j hij a
  let p : (normOneFunctor hA b).obj P := ⟨1 + (Polynomial.X ^ 2 : P) ⊗ₜ[F] q,
    normAt_one_add_square_zero hA b hq P _⟩
  let f : GroupPoints G.val P := model.inv.app P p
  have hf : model.hom.app P f = p := GrpCat.hom_inv_apply (model.app P) p
  refine ⟨f, ?_, ?_⟩
  · apply (model.app L).groupIsoToMulEquiv.injective
    apply Subtype.ext
    change (model.hom.app L (mapPoints (polynomialToLaurent R) f)).val =
      (model.hom.app L (orbit c x)).val
    have hn := NatTrans.naturality_apply model.hom (polynomialToLaurent R) f
    have hn' := NatTrans.naturality_apply model.hom (laurentConstants R) x
    change model.hom.app L (mapPoints (polynomialToLaurent R) f) =
      (normOneFunctor hA b).map (polynomialToLaurent R) (model.hom.app P f) at hn
    change model.hom.app L (mapPoints (laurentConstants R) x) =
      (normOneFunctor hA b).map (laurentConstants R) (model.hom.app R x) at hn'
    have hl : ((normOneFunctor hA b).map (polynomialToLaurent R) p).val =
        1 + (u.val ^ 2) ⊗ₜ[F] q := by
      change Algebra.TensorProduct.map (polynomialToLaurent R).hom (.id F A)
        (1 + (Polynomial.X ^ 2 : P) ⊗ₜ[F] q) = _
      have hX : (polynomialToLaurent R).hom Polynomial.X = u.val :=
        Polynomial.toLaurent_X
      simp only [map_add, map_one, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_pow, hX]
    have hconst : (model.hom.app L (mapPoints (laurentConstants R) x)).val =
        1 + (1 : L) ⊗ₜ[F] q := by
      rw [hn']
      change Algebra.TensorProduct.map (laurentConstants R).hom (.id F A)
        (model.hom.app R x).val = _
      rw [hx]
      simp only [map_add, map_one, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rfl
    rw [hn, hf, hl]
    let xL : GroupPoints G.val L := mapPoints (laurentConstants R) x
    change (model.hom.app L xL).val = _ at hconst
    change _ = (model.hom.app L
      ((cocharacterPoint c L u * xL) * (cocharacterPoint c L u)⁻¹)).val
    rw [← cocharacterPoint_inv c L u]
    have hm (x y : GroupPoints G.val L) :
        (model.hom.app L (x * y)).val = (model.hom.app L x).val * (model.hom.app L y).val :=
      congrArg Subtype.val (map_mul (model.hom.app L).hom x y)
    rw [hm, hm, hc, hc, hconst]
    exact (diagonalTensor_conj L e i j hij u a).symm
  · apply (model.app R).groupIsoToMulEquiv.injective
    apply Subtype.ext
    have hn := NatTrans.naturality_apply model.hom (polynomialEvaluate R 0) f
    change model.hom.app R (mapPoints (polynomialEvaluate R 0) f) =
      (normOneFunctor hA b).map (polynomialEvaluate R 0) (model.hom.app P f) at hn
    rw [map_one]
    change (model.hom.app R (mapPoints (polynomialEvaluate R 0) f)).val = (1 : R ⊗[F] A)
    rw [hn, hf]
    change Algebra.TensorProduct.map (polynomialEvaluate R 0).hom (.id F A)
      (1 + (Polynomial.X ^ 2 : P) ⊗ₜ[F] q) = _
    have hv : (polynomialEvaluate R 0).hom Polynomial.X = 0 := Polynomial.aeval_X _
    simp only [map_add, map_one, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      map_pow, hv, zero_pow (by decide : 2 ≠ 0), TensorProduct.zero_tmul, add_zero]

private theorem section_of_contracting_point (hG : Specs.GeometricRadicals.IsReductive G)
    (i : MatrixRealization G) (c : Cocharacter G.val)
    (x : GroupPoints G.val (CommAlgCat.of F F)) (hx : HasLimit c x 1) :
    x ∈ generatedPoints i := by
  obtain ⟨D⟩ := CocharacterDynamics.existsLimitDecomposition G c
  obtain ⟨y, hy⟩ := (D.contracting_points (CommAlgCat.of F F) x).mp hx
  let z : (𝟙_ (SchemeOver F) ⟶ G.val.X) := testPointSections G.val x
  have hz : z ∈ Specs.SubgroupSections D.contracting (𝟙_ (SchemeOver F)) := by
    refine ⟨testPointSections D.contracting.group y, ?_⟩
    change ((rationalSourceIso F).hom ≫ y) ≫ D.contracting.inclusion.hom.hom =
      (rationalSourceIso F).hom ≫ x
    rw [Category.assoc]
    exact congrArg (fun p : Points G.val.X (CommAlgCat.of F F) =>
      (rationalSourceIso F).hom ≫ p) hy
  refine ⟨z, contracting_le_unipotentGenerated hG D hz, ?_⟩
  have h := (testPointSections G.val).symm_apply_apply x
  change (rationalSourceIso F).inv ≫ z = x at h
  exact (congrArg (· ≫ z) (toUnit_unique (rationalSourceIso F).inv _).symm).trans h

set_option maxHeartbeats 500000 in
theorem elementaryInRadicals : ElementaryInRadicals.{u} := by
  classical
  intro F A _ _ _ hA I _ b G point mul natural B _ _ m e i r s hrs a
  let model := normOnePointsIso hA b point mul natural
  have hG := normOne_reductive hA b model
  obtain ⟨c, hc⟩ := exists_diagonal_cocharacter hA b model e r s hrs
  let R := CommAlgCat.of F F
  let q := e.symm (Matrix.single r s a)
  have hq : q * q = 0 := offDiagonalEntry_sq_zero e r s hrs a
  let y : (normOneFunctor hA b).obj R :=
    ⟨1 + (1 : R) ⊗ₜ[F] q, normAt_one_add_square_zero hA b hq R 1⟩
  let x : PointsIn i F := (point R).symm y
  have hval : (point R x).val = y.val := congrArg Subtype.val ((point R).apply_symm_apply y)
  have hl := block_hasLimit hA b model e r s hrs a c hc x hval
  refine ⟨x, section_of_contracting_point hG i c x hl, ?_⟩
  rw [hval]
  change e (Algebra.TensorProduct.lid F A (1 + (1 : F) ⊗ₜ[F] q)) = 1 + Matrix.single r s a
  simp only [map_add, map_one, Algebra.TensorProduct.lid_tmul, one_smul, q, AlgEquiv.apply_symm_apply]

end RadicalComparison

theorem localDensity : LocalDensity.{u} :=
  local_density_of_elementary elementaryInRadicals.{u} elementaryInRadicals.{0}

section EquivalentLocalFields

open LocalNormOneCommutators.Spec (denseCommutators normOne)
open LocalNormOneCommutators (realDivision complexDivision matrixTransfer)

private theorem reducedNorm_over_equivalent_field {F : Type u} {L : Type v}
    [Field F] [Field L] {B : Type u} [DivisionRing B] [Algebra F B]
    (e : F ≃+* L) (hB : IsCentralSimple F B) :
    ∃ a : Algebra L B, letI := a
      ∃ h : IsCentralSimple L B, ∀ x : B, reducedNorm h x = e (reducedNorm hB x) := by
  letI : Algebra F L := e.toRingHom.toAlgebra
  let a : Algebra L B := Algebra.compHom B e.symm.toRingHom
  letI := a
  letI : IsScalarTower F L B := IsScalarTower.of_algebraMap_eq fun x => by
    change (algebraMap F B) x = (algebraMap F B) (e.symm (e x))
    rw [RingEquiv.symm_apply_apply]
  let φ : L ⊗[F] B →ₐ[L] B := Algebra.TensorProduct.lift
    (Algebra.ofId L B) (AlgHom.id F B) (fun l x => Algebra.commutes l x)
  have hφ (x : B) : φ ((1 : L) ⊗ₜ[F] x) = x := by
    simp [φ]
  have hr : Function.Surjective (Algebra.TensorProduct.includeRight : B →ₐ[F] L ⊗[F] B) :=
    Algebra.TensorProduct.includeRight_surjective B e.surjective
  let iso : L ⊗[F] B ≃ₐ[L] B := AlgEquiv.ofBijective φ ⟨by
    intro y z h
    obtain ⟨b, rfl⟩ := hr y
    obtain ⟨c, rfl⟩ := hr z
    change φ ((1 : L) ⊗ₜ[F] b) = φ ((1 : L) ⊗ₜ[F] c) at h
    rw [hφ, hφ] at h
    rw [h], fun b => ⟨_, hφ b⟩⟩
  let h' := isCentralSimple_baseChange (L := L) hB
  have central : Algebra.IsCentral L B := by
    constructor
    intro x hx
    obtain ⟨l, hl⟩ := Algebra.mem_bot.mp
      (h'.2.1.out ((MulEquivClass.apply_mem_center_iff iso.symm).mpr hx))
    exact Algebra.mem_bot.mpr ⟨l, by
      simpa only [AlgEquiv.commutes, AlgEquiv.apply_symm_apply] using congrArg iso hl⟩
  letI := h'.2.2
  let h : IsCentralSimple L B :=
    ⟨hB.1, central, Module.Finite.equiv iso.toLinearEquiv⟩
  refine ⟨a, h, fun x => ?_⟩
  have he : iso ((1 : L) ⊗ₜ[F] x) = x := hφ x
  calc
    reducedNorm h x = reducedNorm h (iso ((1 : L) ⊗ₜ[F] x)) := congrArg (reducedNorm h) he.symm
    _ = reducedNorm h' ((1 : L) ⊗ₜ[F] x) := (norm_algEquiv h' h iso _).symm
    _ = e (reducedNorm hB x) := reducedNorm_baseChange hB x h'

private theorem archimedean_density_over {F : Type u}
    [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    (arch : Nonempty (F ≃+* ℝ) ∨ Nonempty (F ≃+* ℂ)) : DensityOver (F := F) := by
  haveI : Infinite F := by
    rcases arch with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Infinite.of_surjective e e.surjective
    · exact Infinite.of_surjective e e.surjective
  apply density_over elementaryInRadicals
  intro B _ _ hB m hm
  have hd : denseCommutators hB := by
    intro b
    letI := coordinateTopology b
    intro x hx
    apply subset_closure
    rcases arch with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · obtain ⟨a, h, hn⟩ := reducedNorm_over_equivalent_field e hB
      letI := a
      have hx' : x ∈ normOne h := (hn _).trans (by rw [show reducedNorm hB (x : B) = 1 from hx, map_one])
      obtain ⟨y, z, rfl⟩ := realDivision h x hx'
      exact Subgroup.commutator_mem_commutator (by trivial) (by trivial)
    · obtain ⟨a, h, hn⟩ := reducedNorm_over_equivalent_field e hB
      letI := a
      have hx' : x ∈ normOne h := (hn _).trans (by rw [show reducedNorm hB (x : B) = 1 from hx, map_one])
      rw [complexDivision h x hx']
      exact (commutator Bˣ).one_mem
  exact (matrixTransfer hB hd m (by omega) (matrixCentralSimple hB (by omega))).2 hm

private theorem density_over_completion {K : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) (w : D.Place) : DensityOver (F := D.Completion w) := by
  cases w with
  | inl w =>
    change DensityOver (F := D.FiniteCompletion w)
    exact localDensity.{u}.1
  | inr w =>
    cases D with
    | number h =>
      change DensityOver (F := w.Completion)
      apply archimedean_density_over
      rcases w.isReal_or_isComplex with hr | hc
      · exact Or.inl ⟨NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hr⟩
      · exact Or.inr ⟨NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hc⟩
    | function F t => exact PEmpty.elim w

end EquivalentLocalFields

section SplitCentre

open Specs.OuterTypeAModels (RepresentsUnitary)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.Arithmetic.OppositeRadicals (localPlus)
open AdelicGroups (LocalPoints)
open private baseChangeMatrixPoints from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeneralLinearStructure
open private baseChangeGroupPointNaturality from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.InnerTypeA

private theorem splitCentre_density_over {L : Type u} [Field L] [TopologicalSpace L]
    (density : DensityOver (F := L)) : SplitCentreDensityOver (L := L) := by
  intro K E A _ _ _ _ _ _ _ _ _ _ _ _ hA I _ b star G hU
  dsimp only
  obtain ⟨hL, _, hM⟩ := OuterTypeAModels.splitCentreTypeAModel (L := L) hA b star hU
  exact density hL (b.baseChange L) _ hM

theorem splitCentreLocalDensity : SplitCentreLocalDensity.{u} :=
  ⟨fun {_} _ _ _ _ => splitCentre_density_over localDensity.{u}.1,
    splitCentre_density_over localDensity.{u}.2.1, splitCentre_density_over localDensity.{u}.2.2⟩

private def baseChangedRealization {K L : Type u} [Field K] [Field L] [Algebra K L]
    {G : AffineAlgebraicGroup K} (i : MatrixRealization G) :
    MatrixRealization (baseChangedAlgebraicGroup L G) where
  size := i.size
  ambient := baseChangedAlgebraicGroup L i.ambient
  matrix := baseChangeMatrixPoints L i.matrix
  embedding := (groupBaseChange K L).map i.embedding
  closed := baseChangeClosedSubgroup K L i.embedding i.closed

set_option maxHeartbeats 600000 in
theorem completionDensityTransfer : CompletionDensityTransfer.{u,v} := by
  intro K _ D G i w L G' density A _ _ hA I _ b model hc
  let i' : MatrixRealization G' := baseChangedRealization i
  have hd : Dense (generatedPoints i') := density hA b G' model hc i'
  let E : PointsIn i' L ≃* LocalPoints D i w :=
    baseChangePointGroupEquiv L G.val (CommAlgCat.of L L)
  have hmat (x : PointsIn i' L) : asMatrix i L (E x) = asMatrix i' L x := by
    change i.matrix.hom.app ((restrictTestAlgebra K L).obj (CommAlgCat.of L L))
      (baseChangePoint K L G.val.X (CommAlgCat.of L L) x ≫ i.embedding.hom.hom) =
      i.matrix.hom.app ((restrictTestAlgebra K L).obj (CommAlgCat.of L L))
        (baseChangePoint K L i.ambient.val.X (CommAlgCat.of L L)
          (x ≫ ((groupBaseChange K L).map i.embedding).hom.hom))
    rw [baseChangeGroupPointNaturality]
  have hcont : Continuous (E : PointsIn i' L → LocalPoints D i w) :=
    (IsInducing.induced (asMatrix i L)).continuous_iff.mpr (by
      change Continuous (fun x => asMatrix i L (E x))
      simp_rw [hmat]
      exact continuous_induced_dom)
  have hs : E '' generatedPoints i' ⊆ localPlus D i w := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨p, hp, hr⟩ := hx
    exact ⟨p, hp, congrArg E hr⟩
  intro y
  obtain ⟨x, rfl⟩ := E.surjective y
  exact closure_mono hs (image_closure_subset_closure_image hcont ⟨x, hd x, rfl⟩)

theorem splitCentreCompletionDensity : SplitCentreCompletionDensity.{u,v} := by
  intro K E A _ _ _ _ _ _ _ _ _ hA I _ b star G repr D i w L _ _ G' hc
  obtain ⟨hL, _, hM⟩ := OuterTypeAModels.splitCentreTypeAModel (L := L) hA b star repr
  exact completionDensityTransfer D G i w (density_over_completion D w) hL
    (b.baseChange L) hM hc

end SplitCentre

end LinearAlgebraicGroups.Arithmetic.IsotropicNormOneRadicalsDensity
