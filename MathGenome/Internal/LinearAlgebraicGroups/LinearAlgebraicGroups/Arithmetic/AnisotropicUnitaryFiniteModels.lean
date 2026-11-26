import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryFiniteModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AlmostEverywhereSplitAlgebras
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.DivisionOctonionOrthogonalTensors
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.FunctionFieldForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IsotropicOuterTypeA
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalCocharacterEvaluation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalQuadraticIsotropy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OuterTypeALocalModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.UnitaryRankOne
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SpecialLinearDatum
import Mathlib.RingTheory.Polynomial.Subring
import Mathlib.RingTheory.Trace.Basic
import Batteries.Tactic.OpenPrivate

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Filter Topology
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme)
open scoped CategoryTheory.MonObj Matrix MatrixGroups TensorProduct

universe u v

namespace LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryFiniteModels

open AdelicGroups (LocalPoints PointsIn asMatrix)
open CompactProductIsolation (Contracted)
open Specs.IntegralModels (MatrixRealization)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open Specs.OuterTypeAModels (RepresentsUnitary RepresentsNormOne)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open _root_.Specs.RM03.CSA (degree isCentralSimple)
open _root_.LinearAlgebraicGroups.UnitaryNormEquations (SecondKind)

open _root_.LinearAlgebraicGroups.Arithmetic.LocalOuterTypeAAlgebras (conjugateTranspose)
open Specs.DivisionOctonionOrthogonalTensors (quadraticPolynomial)
open private quadraticPolynomial_eval from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.DivisionOctonionOrthogonalTensors

private theorem localQuadraticIsotropy {F V : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : QuadraticForm F V) (hker : LinearMap.ker q.polarBilin = ⊥)
    (hdim : 5 ≤ Module.finrank F V) :
    ∃ x : V, x ≠ 0 ∧ q x = 0 := by
  by_cases h₂ : (2 : F) = 0
  · let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h₂
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    classical
    let b := Module.finBasis F V
    have hp : (quadraticPolynomial b q).IsHomogeneous 2 := by
      apply MvPolynomial.IsHomogeneous.sum
      intro i _
      apply MvPolynomial.IsHomogeneous.sum
      intro j _
      exact ((MvPolynomial.isHomogeneous_X F i).mul (MvPolynomial.isHomogeneous_X F j)).C_mul _
    obtain ⟨x, hx, hq⟩ := FunctionFieldForms.local_quadratic_bound F 2 _
      (by omega : 2 ^ 2 < Module.finrank F V) (quadraticPolynomial b q) hp
    refine ⟨b.equivFun.symm x, ?_, (quadraticPolynomial_eval b q x).symm.trans hq⟩
    intro hz
    exact hx (b.equivFun.symm.injective (hz.trans (map_zero b.equivFun.symm).symm))
  · exact LocalQuadraticIsotropy.local_isotropy h₂ q hker hdim

/-- A nondegenerate Hermitian form in at least three variables over a separable
quadratic extension of a nonarchimedean local field has an isotropic vector.
The polar form of its ground-field quadratic form is the trace pairing of
the Hermitian form. -/
theorem localHermitianIsotropy {F E : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] (hd : Module.finrank F E = 2) (σ : E ≃ₐ[F] E)
    (hσ : σ ≠ 1) {n : ℕ} (hn : 3 ≤ n)
    (H : (Matrix (Fin n) (Fin n) E)ˣ) (hH : conjugateTranspose σ H.val = H.val) :
    ∃ x : Fin n → E, x ≠ 0 ∧ dotProduct (σ ∘ x) (H.val *ᵥ x) = 0 := by
  classical
  let : Algebra.IsQuadraticExtension F E := ⟨hd⟩
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hd]
  have hall : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, σ} := by
    apply (Finset.eq_of_subset_of_card_le (Finset.subset_univ _ ) ?_).symm
    simp [hcard, Ne.symm hσ]
  have hcases (a : E ≃ₐ[F] E) : a = 1 ∨ a = σ := by
    have ha := Finset.mem_univ a
    simpa [hall] using ha
  have hinv (x : E) : σ (σ x) = x := by
    rcases hcases (σ * σ) with he | he
    · exact DFunLike.congr_fun he x
    · exact (hσ (mul_right_cancel (show σ * σ = 1 * σ by simpa using he))).elim
  have htrace (x : E) : algebraMap F E (Algebra.trace F E x) = x + σ x := by
    rw [trace_eq_sum_automorphisms, hall,
      Finset.sum_insert (by simpa [eq_comm] using hσ : (1 : E ≃ₐ[F] E) ∉ {σ}),
      Finset.sum_singleton]
    rfl
  obtain ⟨t, ht⟩ := Algebra.trace_surjective F E 1
  let V := Fin n → E
  let conj (x : V) : V := σ ∘ x
  let h (x y : V) : E := dotProduct (conj x) (H.val *ᵥ y)
  have hsym (x y : V) : σ (h x y) = h y x := by
    change σ.toRingHom (dotProduct (conj x) (H.val *ᵥ y)) = h y x
    rw [σ.toRingHom.map_dotProduct]
    have hxx : σ.toRingHom ∘ conj x = x := funext fun i => hinv (x i)
    have hmul : σ.toRingHom ∘ (H.val *ᵥ y) = H.val.map σ *ᵥ conj y :=
      funext fun i => σ.toRingHom.map_mulVec H.val y i
    have htranspose : H.val.map σ = H.val.transpose := by
      exact congrArg Matrix.transpose hH
    rw [hxx, hmul, htranspose, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      dotProduct_comm]
  have hadd (x y z : V) : h x (y + z) = h x y + h x z := by
    dsimp only [h]
    rw [Matrix.mulVec_add, dotProduct_add]
  have hsmul (a : E) (x y : V) : h x (a • y) = a * h x y := by
    dsimp only [h]
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have hscalar (a : F) (x : V) : a • x = (algebraMap F E a) • x := by
    funext i
    exact Algebra.smul_def a (x i)
  have haddLeft (x y z : V) : h (x + y) z = h x z + h y z := by
    rw [← hsym z (x + y), hadd, map_add, hsym, hsym]
  have hsmulLeft (a : F) (x y : V) : h (a • x) y = algebraMap F E a * h x y := by
    rw [← hsym y, hscalar, hsmul, map_mul, σ.commutes, hsym]
  let B : LinearMap.BilinForm F V :=
    LinearMap.mk₂ F (fun x y : V => Algebra.trace F E (t * h x y))
      (fun x y z => by rw [haddLeft, mul_add, map_add])
      (fun a x y => by
        rw [hsmulLeft, mul_left_comm, ← Algebra.smul_def, map_smul])
      (fun x y z => by rw [hadd, mul_add, map_add])
      (fun a x y => by
        rw [hscalar, hsmul, mul_left_comm, ← Algebra.smul_def, map_smul])
  let q : QuadraticForm F V := B.toQuadraticMap
  have hpolar (x y : V) : q.polarBilin x y = Algebra.trace F E (h x y) := by
    rw [show q = B.toQuadraticMap from rfl, LinearMap.BilinMap.polarBilin_toQuadraticMap]
    change Algebra.trace F E (t * h x y) + Algebra.trace F E (t * h y x) = _
    rw [← map_add, ← mul_add, ← hsym x y, ← htrace, mul_comm t,
      ← Algebra.smul_def, map_smul, ht, smul_eq_mul, mul_one]
  have hnondeg (x : V) (hx : ∀ y : V, h y x = 0) : x = 0 := by
    have hcoord : H.val *ᵥ x = 0 := by
      funext i
      have hi : conj (Pi.single i 1) = Pi.single i 1 := by
        funext j
        by_cases hj : j = i <;> simp [conj, hj]
      simpa [h, hi, single_dotProduct] using hx (Pi.single i 1)
    calc
      x = (↑H⁻¹ : Matrix (Fin n) (Fin n) E) *ᵥ (H.val *ᵥ x) := by
        rw [Matrix.mulVec_mulVec, H.inv_mul, Matrix.one_mulVec]
      _ = 0 := by rw [hcoord, Matrix.mulVec_zero]
  have hker : LinearMap.ker q.polarBilin = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hz (y : V) : Algebra.trace F E (h x y) = 0 :=
      (hpolar x y).symm.trans (LinearMap.congr_fun (LinearMap.mem_ker.mp hx) y)
    apply hnondeg x
    intro y
    by_contra hxy
    have hne : h x y ≠ 0 := fun he => hxy (by rw [← hsym, he, map_zero])
    have he := hz ((t / h x y) • y)
    rw [hsmul, div_mul_cancel₀ _ hne, ht] at he
    exact one_ne_zero he
  have hdim : 5 ≤ Module.finrank F V := by
    change 5 ≤ Module.finrank F (∀ _ : Fin n, E)
    simpa [Module.finrank_pi_fintype, hd] using (show 5 ≤ n * 2 by omega)
  obtain ⟨x, hx, hz⟩ := localQuadraticIsotropy q hker hdim
  refine ⟨x, hx, ?_⟩
  have hf : h x x ∈ Set.range (algebraMap F E) := by
    apply (IsGalois.mem_range_algebraMap_iff_fixed (h x x)).mpr
    intro a
    rcases hcases a with rfl | rfl
    · rfl
    · exact hsym x x
  obtain ⟨a, ha⟩ := hf
  change Algebra.trace F E (t * h x x) = 0 at hz
  rw [← ha, mul_comm t, ← Algebra.smul_def, map_smul, ht, smul_eq_mul, mul_one] at hz
  change h x x = 0
  rw [← ha, hz, map_zero]

open Specs.Arithmetic.OuterTypeALocalModels (NonsplitModel SplitModel)
open Specs.Arithmetic.LocalQuotientMixing (IsIsotropicSpecialUnitary MixingCases)
open Specs.UnitaryRankOne (quadraticConjugation)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open private quadraticAut from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.UnitaryRankOne

/-- At a finite completion where the quadratic centre is a field, the
original base-changed scheme is represented by an isotropic Hermitian form. -/
theorem nonsplitCompletionIsotropic {K E A F : Type u} [Field K] [Field E]
    [Algebra K E] [Field F] [Algebra K F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Ring A]
    [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    (s : SecondKind K E A) (G : AffineAlgebraicGroup K) (hn : 3 ≤ degree E A)
    (h : NonsplitModel (F := F) s G) :
    IsIsotropicSpecialUnitary (baseChangedAlgebraicGroup F G) := by
  obtain ⟨Q, hQ, hFQ, hsep, c, hdim, σ, H, hσ, _, hH, _, hmodel, _⟩ := h
  letI : Field Q := hQ
  letI : Algebra F Q := hFQ
  letI : Algebra.IsQuadraticExtension F Q := ⟨hdim⟩
  letI : Algebra.IsSeparable F Q := hsep
  have hσ' := (quadraticAut σ).resolve_left hσ
  subst σ
  have hIso := localHermitianIsotropy hdim (quadraticConjugation F Q) hσ hn H hH
  refine ⟨Q, hQ, hFQ, inferInstance, hsep, degree E A, H, ?_, hIso, hmodel⟩
  change (H.val.map (quadraticConjugation F Q)).transpose = H.val
  simpa only [conjugateTranspose, Matrix.transpose_map] using hH

/-- Every finite completion has either an isotropic Hermitian model or the
norm-one model from an embedding of the quadratic centre in that completion. -/
theorem finiteUnitaryModels {K E A : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    [Field E] [Algebra K E] [Algebra.IsSeparable K E] [Ring A]
    [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    (hKE : Module.finrank K E = 2)
    {I : Type u} [Fintype I] (hA : isCentralSimple E A) (hn : 3 ≤ degree E A)
    (b : Module.Basis I E A) (s : SecondKind K E A) (G : AffineAlgebraicGroup K)
    (hG : RepresentsUnitary hA b s G) (w : D.FinitePlace) :
    IsIsotropicSpecialUnitary (baseChangedAlgebraicGroup (D.Completion (.inl w)) G) ∨
      SplitModel (F := D.Completion (.inl w)) s hA b G := by
  letI : Algebra.IsQuadraticExtension K E := ⟨hKE⟩
  let F := D.Completion (.inl w)
  letI : ValuativeRel F := inferInstanceAs (ValuativeRel (D.FiniteCompletion w))
  haveI : IsNonarchimedeanLocalField F := D.finiteCompletion_isLocalField w
  exact (OuterTypeALocalModels.unitaryLocalModels hA b s G hG D (.inl w)).imp_left
    (nonsplitCompletionIsotropic (F := F) s G hn)

section Generation

open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.Arithmetic.IsotropicNormOneRadicalsDensity (generatedPoints)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.GeneralLinearStructure (SpecialMatrixPoints)
open Specs.GeometricRadicals (IsSplitReductive)
open Specs.Unipotent (Index)
open _root_.RM03.CSA.NormOneGroup (normOneSplit normOneSplit_natural normOneFunctor)
open private testPointSections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private rationalSourceIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalDensity
open private liftSpecialLinear from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.InnerTypeA
open private normOnePointsIso density_from_blocks from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IsotropicNormOneRadicalsDensity

private theorem testPointSections_symm_apply {F : Type u} [Field F]
    (G : AffineAlgebraicGroup F) (p : 𝟙_ (SchemeOver F) ⟶ G.val.X) :
    (testPointSections G.val).symm p =
      toUnit ((testSpec F).obj (.op (CommAlgCat.of F F))) ≫ p := by
  change (rationalSourceIso F).inv ≫ p = _
  exact congrArg (· ≫ p) (toUnit_unique _ _)

private theorem testPointSections_symm_comp {F : Type u} [Field F]
    {H G : GroupScheme F} (f : H ⟶ G) (p : 𝟙_ (SchemeOver F) ⟶ H.X) :
    (testPointSections G).symm (p ≫ f.hom.hom) =
      (testPointSections H).symm p ≫ f.hom.hom := by
  change (rationalSourceIso F).inv ≫ (p ≫ f.hom.hom) =
    ((rationalSourceIso F).inv ≫ p) ≫ f.hom.hom
  exact (Category.assoc _ _ _).symm

open private unipotentGenerated_le_of_contracting from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)
open Specs.CharacterDescent (Cocharacter)

private theorem section_image_at_groundField {F : Type u} [Field F] {G : GroupScheme F}
    (U : Specs.ClosedSubgroup G) (p : 𝟙_ (SchemeOver F) ⟶ G.X)
    (hp : p ∈ Specs.SubgroupSections U (𝟙_ (SchemeOver F))) :
    (testPointSections G).symm p ∈
      ((((groupPointsFunctor F).map U.inclusion).app (CommAlgCat.of F F)).hom).range := by
  obtain ⟨q, hq⟩ : ∃ q : 𝟙_ (SchemeOver F) ⟶ U.group.X,
      q ≫ U.inclusion.hom.hom = p := hp
  refine ⟨(testPointSections U.group).symm q, ?_⟩
  change (testPointSections U.group).symm q ≫ U.inclusion.hom.hom =
    (testPointSections G).symm p
  rw [← testPointSections_symm_comp, hq]

private theorem contracted_of_contractingPoint {F : Type u} [Field F] [TopologicalSpace F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F] (G : AffineAlgebraicGroup F)
    (i : MatrixRealization G) (c : Cocharacter G.val) (L : LimitDecomposition c)
    (x : PointsIn i F)
    (hx : x ∈ ((((groupPointsFunctor F).map L.contracting.inclusion).app
      (CommAlgCat.of F F)).hom).range) : Contracted x := by
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  let : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
  let hv := (inferInstance : ValuativeRel.IsRankLeOne F).nonempty.some
  let : (Valued.v (R := F)).RankOne :=
    { hom' := hv.emb.comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := hv.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField F := Valued.toNontriviallyNormedField F
    (ValuativeRel.ValueGroupWithZero F)
  obtain ⟨t, ht⟩ := LocalCocharacterEvaluation.contractingScalarExists (E := F)
  exact ⟨_, LocalCocharacterEvaluation.contractingEvaluation G i c L
      (show Continuous (algebraMap F F) from continuous_id) t ht x hx⟩

set_option backward.isDefEq.respectTransparency true in
private theorem generatedPoints_subset_of_comap {F : Type u} [Field F]
    (G : AffineAlgebraicGroup F) (i : MatrixRealization G)
    (H : Subgroup (PointsIn i F))
    (f : (𝟙_ (SchemeOver F) ⟶ G.val.X) →* PointsIn i F)
    (hf : ∀ p, f p = toUnit ((testSpec F).obj (.op (CommAlgCat.of F F))) ≫ p)
    (hle : unipotentGenerated G ≤ H.comap f) :
    generatedPoints i ⊆ (H : Set (PointsIn i F)) := by
  intro x hx
  obtain ⟨p, hp, hpx⟩ := hx
  have hm : f p ∈ H := hle hp
  exact Eq.mp (congrArg (fun z : PointsIn i F => z ∈ H) ((hf p).trans hpx)) hm

private theorem generatedPoints_subset_of_contractedSections {F : Type u} [Field F]
    [TopologicalSpace F] (G : AffineAlgebraicGroup F) (i : MatrixRealization G)
    (f : (𝟙_ (SchemeOver F) ⟶ G.val.X) →* PointsIn i F)
    (hf : ∀ p, f p = toUnit ((testSpec F).obj (.op (CommAlgCat.of F F))) ≫ p)
    (hc : ∀ (c : Cocharacter G.val) (L : LimitDecomposition c)
      (p : 𝟙_ (SchemeOver F) ⟶ G.val.X),
      p ∈ Specs.SubgroupSections L.contracting (𝟙_ (SchemeOver F)) → Contracted (f p)) :
    generatedPoints i ⊆
      (Subgroup.closure {x : PointsIn i F | Contracted x} : Set (PointsIn i F)) := by
  apply generatedPoints_subset_of_comap G i _ f hf
  apply unipotentGenerated_le_of_contracting (G := G)
  intro c L p hp
  change f p ∈ Subgroup.closure {x : PointsIn i F | Contracted x}
  exact Subgroup.subset_closure (hc c L p hp)

private theorem contractingSection_contracted {F : Type u} [Field F] [TopologicalSpace F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F] (G : AffineAlgebraicGroup F)
    (i : MatrixRealization G) (c : Cocharacter G.val) (L : LimitDecomposition c)
    (p : 𝟙_ (SchemeOver F) ⟶ G.val.X)
    (hp : p ∈ Specs.SubgroupSections L.contracting (𝟙_ (SchemeOver F))) :
    Contracted (show PointsIn i F from (testPointSections G.val).symm p) :=
  contracted_of_contractingPoint G i c L _ (section_image_at_groundField L.contracting p hp)

private theorem generatedPoints_le_contracted {F : Type u} [Field F] [TopologicalSpace F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F] (G : AffineAlgebraicGroup F)
    (i : MatrixRealization G) :
    generatedPoints i ⊆
      (Subgroup.closure {x : PointsIn i F | Contracted x} : Set (PointsIn i F)) := by
  let f : (𝟙_ (SchemeOver F) ⟶ G.val.X) →* PointsIn i F :=
    (testPointSections G.val).symm.toMonoidHom
  exact generatedPoints_subset_of_contractedSections G i f
    (testPointSections_symm_apply G) (contractingSection_contracted G i)

private theorem hermitian_generatedPoints_dense {F : Type u} [Field F]
    [TopologicalSpace F] [Infinite F] {G : AffineAlgebraicGroup F}
    (h : IsIsotropicSpecialUnitary G) (i : MatrixRealization G) : Dense (generatedPoints i) := by
  obtain ⟨E, _, _, _, _, n, H, hH, hIso, hG⟩ := h
  have hg := IsotropicOuterTypeA.hermitianLocalGeneration H hH hIso G hG
  suffices generatedPoints i = Set.univ by rw [this]; exact dense_univ
  apply Set.eq_univ_of_forall
  intro x
  refine ⟨testPointSections G.val x, by rw [hg]; trivial, ?_⟩
  exact (testPointSections_symm_apply G _).symm.trans
    ((testPointSections G.val).symm_apply_apply x)

private theorem contracted_of_dense_radicals {K : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) {G : AffineAlgebraicGroup K}
    (i : MatrixRealization G) (w : D.FinitePlace)
    (h : ∀ j : MatrixRealization (baseChangedAlgebraicGroup (D.Completion (.inl w)) G),
      Dense (generatedPoints j)) :
    Dense (Subgroup.closure {x : LocalPoints D i (.inl w) | Contracted x} :
      Set (LocalPoints D i (.inl w))) := by
  let F := D.Completion (.inl w)
  let : ValuativeRel F := inferInstanceAs (ValuativeRel (D.FiniteCompletion w))
  let : IsNonarchimedeanLocalField F := D.finiteCompletion_isLocalField w
  let J := baseChangedAlgebraicGroup F G
  obtain ⟨j, hj⟩ := LocalCocharacterEvaluation.completionPointTopology (F := F) G i
  let e : PointsIn j F ≃* LocalPoints D i (.inl w) :=
    baseChangePointGroupEquiv F G.val (CommAlgCat.of F F)
  have hc : Continuous e := (hj.homeomorph _).continuous
  let H : Subgroup (PointsIn j F) := Subgroup.closure {x : PointsIn j F | Contracted x}
  let H' : Subgroup (LocalPoints D i (.inl w)) := Subgroup.closure
    {x : LocalPoints D i (.inl w) | Contracted x}
  have hmap : H ≤ H'.comap e.toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨a, ha⟩
    apply Subgroup.subset_closure
    change Contracted (e x)
    refine ⟨e a, ?_⟩
    simpa only [Function.comp_def, map_mul, map_pow, map_inv, map_one] using
      (hc.tendsto 1).comp ha
  exact (e.surjective.denseRange.dense_image hc ((h j).mono (generatedPoints_le_contracted J j))).mono
    (by rintro _ ⟨x, hx, rfl⟩; exact hmap hx)

private def specialMatrixPointsOfSplit {F A I : Type u} [Field F] [Ring A] [Algebra F A]
    [Fintype I] (hA : isCentralSimple F A) (b : Module.Basis I F A)
    {G : AffineAlgebraicGroup F} (hG : (groupPointsFunctor F).obj G.val ≅ normOneFunctor hA b)
    (s : A ≃ₐ[F] Matrix (Fin (degree F A)) (Fin (degree F A)) F) :
    SpecialMatrixPoints G (degree F A) := by
  let e := (Algebra.TensorProduct.lid F A).trans s
  let m (R : TestAlgebra F) : (normOneFunctor hA b).obj R ≅
      (Specs.StandardGroups.specialLinearPoints F (Index.{u} (degree F A))).obj R :=
    ((normOneSplit (R := R) hA b e).trans (liftSpecialLinear (R := R) _)).toGrpIso
  refine hG ≪≫ NatIso.ofComponents m ?_
  intro R S f
  apply GrpCat.ext
  intro x
  apply Subtype.ext
  let l := liftSpecialLinear (R := S) (degree F A)
  exact congrArg (fun y => (l y).val) (normOneSplit_natural hA b e f.hom x)

private theorem split_mixing {F A I : Type u} [Field F] [TopologicalSpace F]
    [Ring A] [Algebra F A] [Fintype I] (hA : isCentralSimple F A)
    (b : Module.Basis I F A) {G : AffineAlgebraicGroup F} (hG : RepresentsNormOne hA b G)
    (s : A ≃ₐ[F] Matrix (Fin (degree F A)) (Fin (degree F A)) F)
    (hn : 2 ≤ degree F A) : MixingCases G := by
  obtain ⟨point, hmul, hnat⟩ := hG
  have m := specialMatrixPointsOfSplit hA b (normOnePointsIso hA b point hmul hnat) s
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (show degree F A ≠ 0 by omega)
  rw [hr] at m
  obtain ⟨T, L, M, B, Q, _, _, hsc⟩ := RootData.SpecialLinearDatum.matrixPinnedDatum F r G m
  exact Or.inl ⟨⟨B.reductive, T.subgroup, T.split, B.maximal⟩, hsc⟩

private theorem split_generatedPoints_dense {F A I : Type u} [Field F] [TopologicalSpace F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F] [Ring A] [Algebra F A] [Fintype I]
    (hA : isCentralSimple F A) (b : Module.Basis I F A) {G : AffineAlgebraicGroup F}
    (hG : RepresentsNormOne hA b G) {n : ℕ} (hn : 2 ≤ n)
    (s : A ≃ₐ[F] Matrix (Fin n) (Fin n) F) (i : MatrixRealization G) :
    Dense (generatedPoints i) := by
  have hF : isCentralSimple F F := ⟨inferInstance, inferInstance, inferInstance⟩
  exact density_from_blocks hA b hG hF hn s
    (InnerTypeALocalGeneration.localBlockGeneration.{u,u}.1 hF n hn)
    IsotropicNormOneRadicalsDensity.elementaryInRadicals i

end Generation

section CofiniteSplitting

open Module Polynomial
open private envelopingMatrix repr_of_basis_image envelopingMatrix_image enveloping_det_unit
  integralOrder integralOrder_basis extendOrder split_of_integral_order from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AlmostEverywhereSplitAlgebras

/-- A fixed algebraic element is integral at almost every base place, uniformly
over the embeddings of its field into the completion. -/
private theorem eventuallyIntegralEmbeddings {K E : Type u} [Field K] [Field E] [Algebra K E]
    (D : GlobalFieldData.{u,v} K) (x : E) (hx : IsIntegral K x) :
    ∀ᶠ w in cofinite, ∀ j : E →ₐ[K] D.Completion (.inl w), j x ∈ D.integers w := by
  classical
  let p := minpoly K x
  have hp : p.Monic := minpoly.monic hx
  have hcoeff : ∀ᶠ w in cofinite, ∀ a ∈ (p.coeffs : Set K),
      D.embedding (.inl w) a ∈ D.integers w :=
    (eventually_all_finite p.coeffs.finite_toSet).mpr fun a _ =>
      eventually_cofinite.mpr (D.finite_nonintegral a)
  filter_upwards [hcoeff] with w hw j
  let F := D.Completion (.inl w)
  let : ValuativeRel F := inferInstanceAs (ValuativeRel (D.FiniteCompletion w))
  let O : ValuationSubring F := (ValuativeRel.valuation F).valuationSubring
  have hOeq : D.integers w = O := D.integers_eq_valuationSubring w
  let q : Polynomial F := p.map (D.embedding (.inl w))
  have hq : q.Monic := hp.map _
  have hqcoeff : (↑q.coeffs : Set F) ⊆ O.toSubring := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := Polynomial.mem_coeffs_iff.mp ha
    have hn' : p.coeff n ≠ 0 := fun h => (Polynomial.mem_support_iff.mp hn) (by simp [q, h])
    change q.coeff n ∈ O
    rw [← hOeq]
    rw [show q = p.map (D.embedding (.inl w)) from rfl, coeff_map]
    exact hw _ (p.coeff_mem_coeffs hn')
  have hqeval : q.eval (j x) = 0 := by
    rw [show q = p.map (D.embedding (.inl w)) from rfl, eval_map]
    change p.eval₂ (algebraMap K F) (j x) = 0
    rw [← aeval_def, aeval_algHom_apply j, minpoly.aeval, map_zero]
  have hi : IsIntegral O (j x) := by
    refine ⟨q.toSubring O.toSubring hqcoeff, (monic_toSubring _ _ _).mpr hq, ?_⟩
    rw [← eval_map, show algebraMap O F = O.toSubring.subtype from rfl, map_toSubring]
    exact hqeval
  have hO : IsIntegrallyClosed O := Valuation.Integers.isIntegrallyClosed_integers _
  rw [hOeq]
  exact (Subring.isIntegrallyClosed_iff (S := O)).mp hO hi

private theorem splitOfIntegralCoefficients {E F A I : Type u}
    [Field E] [Field F] [Algebra E F] [TopologicalSpace F] [ValuativeRel F]
    [IsNonarchimedeanLocalField F] [Ring A] [Algebra E A]
    [Fintype I] [DecidableEq I] (hA : isCentralSimple E A) (b : Basis I E A)
    (h₁ : ∀ i, algebraMap E F (b.repr 1 i) ∈ (ValuativeRel.valuation F).valuationSubring)
    (hm : ∀ i j k, algebraMap E F (b.repr (b i * b j) k) ∈
      (ValuativeRel.valuation F).valuationSubring)
    (hδ : algebraMap E F ((envelopingMatrix b).det⁻¹) ∈
      (ValuativeRel.valuation F).valuationSubring) :
    Nonempty ((F ⊗[E] A) ≃ₐ[F] Matrix (Fin (degree E A)) (Fin (degree E A)) F) := by
  classical
  let : IsSimpleRing A := hA.1
  let : Nonempty I := b.index_nonempty
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  let : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
  let R := (ValuativeRel.valuation F).valuationSubring
  let : IsDiscreteValuationRing R := inferInstanceAs
    (IsDiscreteValuationRing ((ValuativeRel.valuation F).integer))
  let : IsAdicComplete (IsLocalRing.maximalIdeal R) R := inferInstanceAs
    (IsAdicComplete (IsLocalRing.maximalIdeal ((ValuativeRel.valuation F).integer))
      ((ValuativeRel.valuation F).integer))
  let : Finite (IsLocalRing.ResidueField R) := inferInstanceAs
    (Finite (IsLocalRing.ResidueField ((ValuativeRel.valuation F).integer)))
  let B := F ⊗[E] A
  let algebraRB : Algebra R B := Algebra.compHom B (algebraMap R F)
  let scalarTower : IsScalarTower R F B := IsScalarTower.of_algebraMap_eq' rfl
  let bF : Basis I F B := b.baseChange F
  have hf (i : I) : (Algebra.TensorProduct.includeRight : A →ₐ[E] B) (b i) = bF i :=
    (Basis.baseChange_apply _ _ _).symm
  have toRange (x : E) (hx : algebraMap E F x ∈ R) :
      algebraMap E F x ∈ (algebraMap R F).range := ⟨⟨_, hx⟩, rfl⟩
  have hc₁ (i : I) : bF.repr 1 i ∈ (algebraMap R F).range := by
    have h := repr_of_basis_image b bF Algebra.TensorProduct.includeRight hf (1 : A) i
    rw [map_one] at h
    rw [h]
    exact toRange _ (h₁ i)
  have hcm (i j k : I) : bF.repr (bF i * bF j) k ∈ (algebraMap R F).range := by
    have h := repr_of_basis_image b bF Algebra.TensorProduct.includeRight hf (b i * b j) k
    rw [map_mul, hf, hf] at h
    rw [h]
    exact toRange _ (hm i j k)
  let C := integralOrder (R := R) (S := F) (B := B)
    (algebraRB := algebraRB) (tower := scalarTower) bF hc₁ hcm
  have hRF : Function.Injective (algebraMap R F) := Subtype.val_injective
  obtain ⟨c, hc⟩ := integralOrder_basis (R := R) (S := F) (B := B)
    (algebraRB := algebraRB) (tower := scalarTower) bF hc₁ hcm hRF
  let e : F ⊗[R] C ≃ₐ[F] B :=
    extendOrder (algebraRB := algebraRB) (tower := scalarTower) bF C c hc
  have hcF := envelopingMatrix_image (algebraRB := algebraRB) (tower := scalarTower) c bF C.val hc
  have hbF := envelopingMatrix_image b bF Algebra.TensorProduct.includeRight hf
  have hdet : algebraMap R F (envelopingMatrix c).det =
      algebraMap E F (envelopingMatrix b).det := by
    rw [(algebraMap R F).map_det, (algebraMap E F).map_det]
    exact congrArg Matrix.det (hcF.symm.trans hbF)
  have hunit : IsUnit (envelopingMatrix c).det := by
    obtain ⟨a, ha⟩ := toRange _ hδ
    refine isUnit_iff_exists_inv.mpr ⟨a, hRF ?_⟩
    rw [map_mul, map_one, hdet, ha, ← map_mul, mul_inv_cancel₀, map_one]
    exact (enveloping_det_unit b (RM03.CSA.mulLeftRight_bijective hA)).ne_zero
  let : IsSimpleRing (F ⊗[R] C) := IsSimpleRing.of_ringEquiv e.symm.toRingEquiv
    (RM03.CSA.isCentralSimple_baseChange (L := F) hA).1
  obtain ⟨n, ⟨g⟩⟩ := split_of_integral_order (F := F) c hunit
  let g' := e.symm.trans g
  have hn : degree E A = n := RM03.CSA.degree_eq_matrix_size hA g'
  exact hn ▸ ⟨g'⟩

private def splitsAtEmbedding {K E A : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra E A] (D : GlobalFieldData.{u,v} K) (w : D.FinitePlace)
    (j : E →ₐ[K] D.Completion (.inl w)) : Prop :=
  let F := D.Completion (.inl w)
  letI : Algebra E F := j.toRingHom.toAlgebra
  Nonempty ((F ⊗[E] A) ≃ₐ[F] Matrix (Fin (degree E A)) (Fin (degree E A)) F)

private theorem splitAtCompletion {K E A I : Type u} [Field K] [Field E] [Algebra K E]
    [Ring A] [Algebra E A] [Fintype I] [DecidableEq I]
    (D : GlobalFieldData.{u,v} K) (hA : isCentralSimple E A) (b : Basis I E A)
    (w : D.FinitePlace) (j : E →ₐ[K] D.Completion (.inl w))
    (h₁ : ∀ i, j (b.repr 1 i) ∈ D.integers w)
    (hm : ∀ i l k, j (b.repr (b i * b l) k) ∈ D.integers w)
    (hδ : j ((envelopingMatrix b).det⁻¹) ∈ D.integers w) :
    splitsAtEmbedding (A := A) D w j := by
  let F := D.Completion (.inl w)
  let : Algebra E F := j.toRingHom.toAlgebra
  let : ValuativeRel F := inferInstanceAs (ValuativeRel (D.FiniteCompletion w))
  let : IsNonarchimedeanLocalField F := D.finiteCompletion_isLocalField w
  rw [D.integers_eq_valuationSubring w] at h₁ hm hδ
  exact splitOfIntegralCoefficients (F := F) hA b h₁ hm hδ

private theorem cofiniteSplitCentreAlgebra {K E A I : Type u} [Field K] [Field E]
    [Algebra K E] [Algebra.IsSeparable K E] [Ring A] [Algebra E A] [Fintype I]
    (D : GlobalFieldData.{u,v} K) (hA : isCentralSimple E A) (b : Basis I E A) :
    ∀ᶠ w in cofinite, ∀ j : E →ₐ[K] D.Completion (.inl w),
      splitsAtEmbedding (A := A) D w j := by
  classical
  let S₁ := Set.range fun i : I => b.repr 1 i
  let S₂ := Set.range fun p : I × I × I => b.repr (b p.1 * b p.2.1) p.2.2
  let δ := (envelopingMatrix b).det⁻¹
  let S := (S₁ ∪ S₂) ∪ {δ}
  have hS : S.Finite :=
    ((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_singleton _)
  have hInt : ∀ᶠ w in cofinite, ∀ x ∈ S,
      ∀ j : E →ₐ[K] D.Completion (.inl w), j x ∈ D.integers w :=
    (eventually_all_finite hS).mpr fun x _ =>
      eventuallyIntegralEmbeddings D x (Algebra.IsIntegral.isIntegral x)
  filter_upwards [hInt] with w hw j
  exact splitAtCompletion D hA b w j
    (fun i => hw _ (Or.inl (Or.inl ⟨i, rfl⟩)) j)
    (fun i l k => hw _ (Or.inl (Or.inr ⟨(i, l, k), rfl⟩)) j)
    (hw _ (Or.inr rfl) j)

end CofiniteSplitting

open Specs.Arithmetic.AnisotropicUnitaryFiniteModels (FiniteLocalModels)
open Specs.Arithmetic.IsotropicNormOneRadicalsDensity (generatedPoints)
open private globalField_infinite from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OppositeRadicals

private theorem splitCompletionModels {K E A I : Type u} [Field K] [Field E]
    [Algebra K E] [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    [Fintype I] (D : GlobalFieldData.{u,v} K) (w : D.FinitePlace)
    (hA : isCentralSimple E A) (hn : 3 ≤ degree E A) (b : Module.Basis I E A)
    (s : SecondKind K E A) (G : AffineAlgebraicGroup K)
    (h : SplitModel (F := D.Completion (.inl w)) s hA b G)
    (hgood : ∀ j : E →ₐ[K] D.Completion (.inl w), splitsAtEmbedding (A := A) D w j) :
    let J := baseChangedAlgebraicGroup (D.Completion (.inl w)) G
    MixingCases J ∧ ∀ i : MatrixRealization J, Dense (generatedPoints i) := by
  let F := D.Completion (.inl w)
  let : ValuativeRel F := inferInstanceAs (ValuativeRel (D.FiniteCompletion w))
  let : IsNonarchimedeanLocalField F := D.finiteCompletion_isLocalField w
  obtain ⟨j, _, hF, hd, hrep⟩ := h
  let : Algebra E F := j.toRingHom.toAlgebra
  obtain ⟨e⟩ := hgood j
  let bF := b.baseChange F
  have ef : (F ⊗[E] A) ≃ₐ[F] Matrix (Fin (degree F (F ⊗[E] A)))
      (Fin (degree F (F ⊗[E] A))) F := hd.symm ▸ e
  exact ⟨split_mixing hF bF hrep ef (by omega),
    split_generatedPoints_dense hF bF hrep (by omega) e⟩

/-- The finite completions have the required mixing models and contracted
generators away from finitely many places splitting the quadratic centre. -/
theorem finiteLocalModels : FiniteLocalModels.{u,v} := by
  classical
  intro K E A _ D _ _ _ _ _ _ _ hKE I _ hA hn b s G _ _ hrep i
  have hfin := eventually_cofinite.mp (cofiniteSplitCentreAlgebra D hA b)
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro w hw
    have hbad := hfin.mem_toFinset.mp hw
    by_contra he
    exact hbad (fun j => (he ⟨j⟩).elim)
  · intro w hw
    have hgood : ∀ j : E →ₐ[K] D.Completion (.inl w), splitsAtEmbedding (A := A) D w j :=
      not_not.mp (fun hbad => hw (hfin.mem_toFinset.mpr hbad))
    rcases finiteUnitaryModels D hKE hA hn b s G hrep w with hh | hs
    · let : Infinite K := globalField_infinite D
      let : Infinite (D.Completion (.inl w)) :=
        Infinite.of_injective _ (algebraMap K (D.Completion (.inl w))).injective
      exact ⟨Or.inr (Or.inl hh), contracted_of_dense_radicals D i w
        (hermitian_generatedPoints_dense hh)⟩
    · obtain ⟨hm, hg⟩ := splitCompletionModels D w hA hn b s G hs hgood
      exact ⟨hm, contracted_of_dense_radicals D i w hg⟩

end LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryFiniteModels
