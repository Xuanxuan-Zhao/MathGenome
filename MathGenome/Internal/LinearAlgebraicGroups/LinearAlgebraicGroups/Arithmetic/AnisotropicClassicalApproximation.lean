import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AnisotropicClassicalApproximation
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.DivisionOctonionOrthogonalTensors
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalQuadraticIsotropy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TrialitarianCliffordInvariants
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicDivisionApproximation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicOctonionApproximation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryApproximation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicSymplecticApproximation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalProjectedClosure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicSpinQuotients
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RealDefiniteSpin
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinIsotropy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RankEightSpinStructure
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Topology.Algebra.MvPolynomial
import Batteries.Tactic.OpenPrivate

noncomputable section

universe u v

namespace LinearAlgebraicGroups.Arithmetic.AnisotropicClassicalApproximation

open Specs.Arithmetic.AnisotropicClassicalApproximation
open Specs.Arithmetic.IsotropicSpinGeneration (IsIsotropic)
open Specs.DivisionOctonionOrthogonalTensors (quadraticPolynomial)
open private quadraticPolynomial_eval from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.DivisionOctonionOrthogonalTensors

/-- Regular quadratic forms of dimension at least five are isotropic over a
nonarchimedean local field. -/
theorem localSpinIsotropy : LocalSpinIsotropy.{u} := by
  intro F V _ _ _ _ _ _ _ q r hreg hdim
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
  · have hker : LinearMap.ker q.polarBilin = ⊥ := by
      cases r with
      | none => exact hreg
      | some r => exact (h₂ hreg.1).elim
    exact LocalQuadraticIsotropy.local_isotropy h₂ q hker hdim

open Specs.Arithmetic.TrialitarianCliffordInvariants (IsArtinSchreier normSubgroup)

private theorem artinSchreierPresentation {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] [CharP F 2] (hd : Module.finrank F E = 2) :
    ∃ d : F, ¬ IsArtinSchreier d ∧ Nonempty (QuadraticAlgebra F d 1 ≃ₐ[F] E) := by
  let : Algebra.IsQuadraticExtension F E := ⟨hd⟩
  obtain ⟨z, hz⟩ := Algebra.trace_surjective F E (1 : F)
  let d := -Algebra.norm F z
  have hzsq : z * z = d • (1 : E) + (1 : F) • z := by
    have h := Algebra.IsQuadraticExtension.sq_eq_trace_smul_sub_norm (R := F) z
    rw [hz] at h
    simpa [d, pow_two, sub_eq_add_neg, add_comm, Algebra.algebraMap_eq_smul_one] using h
  let f : QuadraticAlgebra F d 1 →ₐ[F] E := QuadraticAlgebra.lift ⟨z, hzsq⟩
  have htrace1 : Algebra.trace F E (1 : E) = 0 := by
    rw [← map_one (algebraMap F E), Algebra.trace_algebraMap, hd, nsmul_eq_mul,
      CharP.cast_eq_zero F 2, zero_mul]
  have hf : Function.Injective f := by
    apply (LinearMap.ker_eq_bot (f := f.toLinearMap)).mp
    rw [Submodule.eq_bot_iff]
    intro x hx
    change f x = 0 at hx
    change x.re • (1 : E) + x.im • z = 0 at hx
    have him : x.im = 0 := by
      simpa [map_add, map_smul, htrace1, hz] using congrArg (Algebra.trace F E) hx
    rw [him, zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one] at hx
    exact QuadraticAlgebra.ext ((algebraMap F E).injective (hx.trans (map_zero _).symm)) him
  let e : QuadraticAlgebra F d 1 ≃ₐ[F] E :=
    AlgEquiv.ofBijective f ⟨hf, (f.toLinearMap.linearEquivOfInjective hf
      ((QuadraticAlgebra.finrank_eq_two _ _).trans hd.symm)).surjective⟩
  refine ⟨d, ?_, ⟨e⟩⟩
  rintro ⟨a, ha⟩
  let x : QuadraticAlgebra F d 1 := ⟨a, 1⟩
  have hn : QuadraticAlgebra.norm x = 0 := by
    rw [QuadraticAlgebra.norm_def]
    change a * a + 1 * a * 1 - d * 1 * 1 = 0
    simp [← pow_two, ha.symm]
  have hm : x * star x = 0 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hn, map_zero]
  have he := congrArg e hm
  rw [map_mul, map_zero] at he
  rcases mul_eq_zero.mp he with hz₁ | hz₂
  · have h := congrArg QuadraticAlgebra.im (e.injective (hz₁.trans (map_zero e).symm))
    exact one_ne_zero h
  · have h := congrArg QuadraticAlgebra.im (e.injective (hz₂.trans (map_zero e).symm))
    exact (neg_ne_zero.mpr one_ne_zero) h

/-- The norm index for the field extension itself, transported from its
Artin–Schreier presentation. -/
theorem characteristicTwoQuadraticNormIndex :
    CharacteristicTwoQuadraticNormIndex.{u} := by
  intro F E _ _ _ _ _ _ _ _ hd
  obtain ⟨d, hns, ⟨e⟩⟩ := artinSchreierPresentation (F := F) hd
  obtain ⟨_, χ, hsurj, hker, hindex, _, _⟩ :=
    TrialitarianCliffordInvariants.localNormGroups d hns
  have hnorm (x : QuadraticAlgebra F d 1) :
      Algebra.norm F (e x) = QuadraticAlgebra.norm x := by
    rw [Algebra.norm_eq_of_algEquiv, Algebra.norm_apply]
    exact QuadraticAlgebra.det_toLinearMap_eq_norm x
  suffices (Units.map (Algebra.norm F : E →* F)).range = normSubgroup d by rwa [this]
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨Units.map e.symm.toMonoidHom a, Units.ext ?_⟩
    exact (hnorm (e.symm (a : E))).symm.trans
      (congrArg (Algebra.norm F) (e.apply_symm_apply (a : E)))
  · rintro ⟨a, rfl⟩
    exact ⟨Units.map e.toMonoidHom a, Units.ext (hnorm a)⟩

open scoped Matrix CategoryTheory.MonObj Classical

set_option backward.isDefEq.respectTransparency false in
/-- A nondegenerate Hermitian space of dimension at least three over a
quadratic extension of a nonarchimedean local field is isotropic. -/
theorem localUnitaryIsotropy : LocalUnitaryIsotropy.{u} := by
  classical
  intro F E _ _ _ _ _ _ _ hd σ hσ n hn H hH
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
  obtain ⟨x, hx, hz⟩ := localSpinIsotropy q none hker hdim
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

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct
open AdelicGroups (Adeles LocalPoints Outside PointsIn localPoint)
open ArithmeticLatticeProjection (FinitePoints diagonalSubgroup)
open CompactProductIsolation (Contracted)
open Specs.IntegralModels (MatrixRealization)
open Specs.Unipotent (Index baseChangedAlgebraicGroup)
open Specs.Arithmetic.LocalQuotientMixing (IsIsotropicQuadraticSpin)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open _root_.LinearAlgebraicGroups.Albert.SpinSpecification
open Specs.Arithmetic.AnisotropicSpinQuotients (RegularModel)
open AnisotropicDivisionApproximation (singletonLocalPoints strongApproximationOfLocalProjections)
open private completionMatrixComparison from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicDivisionApproximation

/-- The compactness theorem for the spin model uses the same rational diagonal
as the arithmetic projection theorem. -/
theorem compactSpinAdelicQuotient {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (D : GlobalFieldData.{u,v} K) (q : QuadraticForm K V) (r : Option V)
    (hreg : RegularModel q r) (ha : ∀ x, q x = 0 → x = 0) (hV : 5 ≤ Module.finrank K V)
    (G : AffineAlgebraicGroup K)
    (e : ∀ L : CommAlgCat.{u} K, SchemePoints G.val L →* (ScalarClifford q L)ˣ)
    (he : IsSpinPointRepresentation q G.val e) (i : MatrixRealization G) :
    CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i) := by
  let b : Module.Basis (Index.{u} (Module.finrank K V)) K V :=
    (Module.finBasis K V).reindex Equiv.ulift.symm
  let d := AdelicGroups.diagonal D i ∅
  have hd (g : Specs.IntegralModels.RationalPoints G) (w : Outside D ∅) :
      d g w = localPoint D i w.val g := AdelicGroups.diagonalCoordinates D i ∅ g w
  have h := AnisotropicSpinQuotients.anisotropicSpinCompactness D q r hreg ha _ b hV G e he i d hd
  have hs : d.range = diagonalSubgroup D i := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, hd g⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, RestrictedProduct.ext _ _ fun w => (hd g w).trans (hg w).symm⟩
  exact hs ▸ h

/-- At each finite completion the original spin model is regular and
isotropic, including when its polar form has a regular radical line. -/
theorem finiteSpinIsotropic {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (D : GlobalFieldData.{u,v} K) (q : QuadraticForm K V) (r : Option V)
    (hreg : RegularModel q r) (hV : 5 ≤ Module.finrank K V)
    (G : AffineAlgebraicGroup K)
    (e : ∀ L : CommAlgCat.{u} K, SchemePoints G.val L →* (ScalarClifford q L)ˣ)
    (he : IsSpinPointRepresentation q G.val e) (w : D.FinitePlace) :
    IsIsotropicQuadraticSpin (baseChangedAlgebraicGroup (D.Completion (.inl w)) G) := by
  let F := D.Completion (.inl w)
  let _ : Algebra K F := AdelicGroups.completionAlgebra D (.inl w)
  let _ : ValuativeRel F := inferInstanceAs (ValuativeRel (D.FiniteCompletion w))
  let : IsNonarchimedeanLocalField F := GlobalFieldData.finiteCompletion_isLocalField D w
  let b : Module.Basis (Index.{u} (Module.finrank K V)) K V :=
    (Module.finBasis K V).reindex Equiv.ulift.symm
  let Q := _root_.LinearAlgebraicGroups.Albert.CliffordSpecification.coefficientForm F q b
  have hVF : 5 ≤ Module.finrank F (F ⊗[K] V) := by
    rw [Module.finrank_eq_card_basis (b.baseChange F), ← Module.finrank_eq_card_basis b]
    exact hV
  obtain ⟨_, ρF, _, _, _, _, _, _, hrep, _⟩ :=
    SpinScalarExtension.spinRepresentationExtension (F := F) q b G e he
  obtain ⟨_, hrad, hline⟩ := SpinScalarExtension.polarRadicalExtension (F := F) q b
  have hrF : ∃ rF, RegularModel Q rF := by
    cases r with
    | none => exact ⟨none, hrad hreg⟩
    | some r =>
      obtain ⟨hr₂, hrq, hrker⟩ := hreg
      exact ⟨some (1 ⊗ₜ[K] r), by
        change (2 : F) = 0 ∧ _
        exact ⟨by rw [← map_ofNat (algebraMap K F), hr₂, map_zero], hline r hrq hrker⟩⟩
  obtain ⟨rF, hrF⟩ := hrF
  have hQR : Specs.Arithmetic.IsotropicSpinGeneration.IsRegular Q := by
    cases rF with
    | none => exact Or.inl hrF
    | some r => exact Or.inr ⟨r, hrF.2⟩
  have hIso := localSpinIsotropy Q rF hrF hVF
  exact ⟨F ⊗[K] V, inferInstance, inferInstance, inferInstance, Q, ρF, hVF, hQR, hIso, hrep⟩

open CategoryTheory.MonoidalCategory
open _root_.LinearAlgebraicGroups.Specs (SubgroupSections)
open Specs.CharacterDescent (Cocharacter)
open CocharacterDynamics (LimitDecomposition oppositeCocharacter)
open Specs.Arithmetic.IsotropicSpinGeneration (IsRegular)

open private fullProjectionOfFiniteCompletion contractionOverLocalField contractedGenerationOfEquiv from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicOctonionApproximation

open private testPointSections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private rationalSourceIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalDensity
open private globalField_infinite from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OppositeRadicals

private theorem topOfSupThroughEquiv {P Q : Type u} [Group P] [Group Q]
    (f : P ≃* Q) (H : Subgroup Q) (A B : Subgroup P)
    (hA : A ≤ H.comap f.toMonoidHom) (hB : B ≤ H.comap f.toMonoidHom) (h : A ⊔ B = ⊤) :
    H = ⊤ := by
  have htop : (⊤ : Subgroup P) ≤ H.comap f.toMonoidHom := by
    rw [← h]
    exact sup_le hA hB
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := f.surjective x
  exact htop (Subgroup.mem_top y)

private def matrixPointSections {F : Type u} [Field F] (G : AffineAlgebraicGroup F)
    (i : MatrixRealization G) : PointsIn i F ≃* (𝟙_ (SchemeOver F) ⟶ G.val.X) :=
  testPointSections G.val

private theorem contractingSectionImage {F : Type u} [Field F] (G : AffineAlgebraicGroup F)
    (i : MatrixRealization G) (d : Cocharacter G.val) (R : LimitDecomposition d)
    (x : 𝟙_ (SchemeOver F) ⟶ G.val.X)
    (hx : x ∈ SubgroupSections R.contracting (𝟙_ (SchemeOver F))) :
    (matrixPointSections G i).symm x ∈ ((((groupPointsFunctor F).map R.contracting.inclusion).app
      (CommAlgCat.of F F)).hom).range := by
  obtain ⟨p, hp⟩ := hx
  refine ⟨(testPointSections R.contracting.group).symm p, ?_⟩
  change ((rationalSourceIso F).inv ≫ p) ≫ R.contracting.inclusion.hom.hom =
    (rationalSourceIso F).inv ≫ x
  change p ≫ R.contracting.inclusion.hom.hom = x at hp
  exact (Category.assoc _ _ _).trans
    (congrArg (fun y => (rationalSourceIso F).inv ≫ y) hp)

private theorem spinOppositeSectionsGenerate {F V : Type u} [Field F] [Infinite F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : QuadraticForm F V) (hq : IsRegular q) (hi : IsIsotropic q)
    (G : AffineAlgebraicGroup F) (hg : IsAbsolutelyAlmostSimple G)
    (ρ : ∀ R : CommAlgCat.{u} F, SchemePoints G.val R →* (ScalarClifford q R)ˣ)
    (he : IsSpinPointRepresentation q G.val ρ) :
    ∃ (c : Cocharacter G.val) (P : LimitDecomposition c) (Q : LimitDecomposition (oppositeCocharacter c)),
      SubgroupSections P.contracting (𝟙_ (SchemeOver F)) ⊔
        SubgroupSections Q.contracting (𝟙_ (SchemeOver F)) = ⊤ := by
  let b : Module.Basis (ULift.{u} (Fin (Module.finrank F V))) F V :=
    (Module.finBasis F V).reindex Equiv.ulift.symm
  obtain ⟨e, he₀, heq⟩ := hi
  obtain ⟨h, _⟩ := IsotropicSpinGeneration.hyperbolicPairExistence q hq e he₀ heq
  obtain ⟨c, _, _, _, hgen⟩ := IsotropicSpinGeneration.localSpinGeneration q b G ρ he hq hg h
  obtain ⟨P⟩ := _root_.LinearAlgebraicGroups.CocharacterDynamics.existsLimitDecomposition G c
  obtain ⟨Q⟩ := _root_.LinearAlgebraicGroups.CocharacterDynamics.existsLimitDecomposition G (oppositeCocharacter c)
  exact ⟨c, P, Q, (hgen P Q).2.2⟩

private theorem leComapClosure {P Q : Type u} [Group P] [Group Q] (f : P →* Q)
    (B : Subgroup P) (C : Set Q) (hf : ∀ x ∈ B, f x ∈ C) :
    B ≤ (Subgroup.closure C).comap f :=
  fun x hx => Subgroup.subset_closure (hf x hx)

set_option maxHeartbeats 65000 in
private theorem contractingSectionsLeClosure {F : Type u} [Field F] [TopologicalSpace F]
    (G : AffineAlgebraicGroup F) (i : MatrixRealization G)
    (d : Cocharacter G.val) (R : LimitDecomposition d)
    (hcontract : ∀ x : PointsIn i F,
      x ∈ ((((groupPointsFunctor F).map R.contracting.inclusion).app
        (CommAlgCat.of F F)).hom).range → Contracted x) :
    SubgroupSections R.contracting (𝟙_ (SchemeOver F)) ≤
      (Subgroup.closure {x : PointsIn i F | Contracted x}).comap
        (matrixPointSections G i).symm.toMonoidHom := by
  apply leComapClosure
  intro x hx
  change Contracted ((matrixPointSections G i).symm x)
  exact hcontract _ (contractingSectionImage G i d R x hx)

private theorem oppositeSectionsGiveContracted {F : Type u} [Field F] [TopologicalSpace F]
    (G : AffineAlgebraicGroup F) (i : MatrixRealization G) (c : Cocharacter G.val)
    (P : LimitDecomposition c) (Q : LimitDecomposition (oppositeCocharacter c))
    (hgen : SubgroupSections P.contracting (𝟙_ (SchemeOver F)) ⊔
        SubgroupSections Q.contracting (𝟙_ (SchemeOver F)) = ⊤)
    (hcontract : ∀ (d : Cocharacter G.val) (R : LimitDecomposition d) (x : PointsIn i F),
      x ∈ ((((groupPointsFunctor F).map R.contracting.inclusion).app
        (CommAlgCat.of F F)).hom).range → Contracted x) :
    Subgroup.closure {x : PointsIn i F | Contracted x} = ⊤ :=
  topOfSupThroughEquiv (matrixPointSections G i).symm _
    (SubgroupSections P.contracting (𝟙_ (SchemeOver F)))
    (SubgroupSections Q.contracting (𝟙_ (SchemeOver F)))
    (contractingSectionsLeClosure G i c P (hcontract c P))
    (contractingSectionsLeClosure G i (oppositeCocharacter c) Q (hcontract _ Q)) hgen

/-- The opposite spin radicals generate the finite local factor by
elements contracted in its given matrix topology. -/
theorem finiteSpinContractedGeneration {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.FinitePlace)
    (hG : IsAbsolutelyAlmostSimple G)
    (hi : IsIsotropicQuadraticSpin (baseChangedAlgebraicGroup (D.Completion (.inl w)) G)) :
    Subgroup.closure {x : FinitePoints D i {Sum.inl w} | Contracted x} = ⊤ := by
  let F := D.Completion (.inl w)
  let _ : Algebra K F := AdelicGroups.completionAlgebra D (.inl w)
  let _ : ValuativeRel F := inferInstanceAs (ValuativeRel (D.FiniteCompletion w))
  let : IsNonarchimedeanLocalField F := GlobalFieldData.finiteCompletion_isLocalField D w
  let : Infinite K := globalField_infinite D
  let : Infinite F := Infinite.of_injective (algebraMap K F) (algebraMap K F).injective
  let L := baseChangedAlgebraicGroup F G
  have hL := OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G hG
  obtain ⟨j, ⟨e⟩⟩ := completionMatrixComparison D i (.inl w)
  change IsIsotropicQuadraticSpin L at hi
  obtain ⟨V, _, _, _, q, ρ, _, hq, hqiso, hρ⟩ := hi
  obtain ⟨c, P, Q, hsections⟩ := spinOppositeSectionsGenerate q hq hqiso L hL ρ hρ
  have hgen := oppositeSectionsGiveContracted L j c P Q hsections (contractionOverLocalField L j)
  exact contractedGenerationOfEquiv (e.trans (singletonLocalPoints D i (.inl w)).symm) hgen

private theorem finiteSpinContractedDense {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.FinitePlace)
    (hG : IsAbsolutelyAlmostSimple G)
    (hi : IsIsotropicQuadraticSpin (baseChangedAlgebraicGroup (D.Completion (.inl w)) G)) :
    Dense (Subgroup.closure {x : FinitePoints D i {Sum.inl w} | Contracted x} :
      Set (FinitePoints D i {Sum.inl w})) := by
  rw [finiteSpinContractedGeneration D i w hG hi, Subgroup.coe_top]
  exact dense_univ

open Specs.Arithmetic.ProjectiveRecurrence (cocharacterRadicalPoints localPointSet)

private theorem contractingSectionsLeRadicalClosure {F : Type u} [Field F]
    (G : AffineAlgebraicGroup F) (i : MatrixRealization G)
    (c : Cocharacter G.val) (R : LimitDecomposition c) :
    SubgroupSections R.contracting (𝟙_ (SchemeOver F)) ≤
      (Subgroup.closure (cocharacterRadicalPoints G)).comap
        (matrixPointSections G i).symm.toMonoidHom := by
  apply leComapClosure
  exact fun x hx => ⟨c, R, contractingSectionImage G i c R x hx⟩

/-- The opposite spin radicals generate the base-changed local group in the
point model used by the archimedean lattice projection. -/
theorem localSpinRadicalsGenerate {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.Place)
    (hG : IsAbsolutelyAlmostSimple G)
    (hi : IsIsotropicQuadraticSpin (baseChangedAlgebraicGroup (D.Completion w) G)) :
    Subgroup.closure (localPointSet D i w
      (cocharacterRadicalPoints (baseChangedAlgebraicGroup (D.Completion w) G))) = ⊤ := by
  let F := D.Completion w
  let _ : Algebra K F := AdelicGroups.completionAlgebra D w
  let : Infinite K := globalField_infinite D
  let : Infinite F := Infinite.of_injective (algebraMap K F) (algebraMap K F).injective
  let L := baseChangedAlgebraicGroup F G
  have hL := OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G hG
  obtain ⟨j, _⟩ := completionMatrixComparison D i w
  change IsIsotropicQuadraticSpin L at hi
  obtain ⟨V, _, _, _, q, ρ, _, hq, hqiso, hρ⟩ := hi
  obtain ⟨c, P, Q, hsections⟩ := spinOppositeSectionsGenerate q hq hqiso L hL ρ hρ
  have hgen : Subgroup.closure (cocharacterRadicalPoints L) = ⊤ :=
    topOfSupThroughEquiv (matrixPointSections L j).symm _ _ _
      (contractingSectionsLeRadicalClosure L j c P)
      (contractingSectionsLeRadicalClosure L j (oppositeCocharacter c) Q) hsections
  let e : Specs.IntegralModels.RationalPoints L ≃* LocalPoints D i w :=
    baseChangePointGroupEquiv F G.val (CommAlgCat.of F F)
  have hmap : (Subgroup.closure (cocharacterRadicalPoints L)).map e.toMonoidHom ≤
      Subgroup.closure (localPointSet D i w (cocharacterRadicalPoints L)) := by
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩
  rw [hgen, Subgroup.map_top_of_surjective _ e.surjective] at hmap
  exact top_unique hmap

private theorem denseProjectionToEmpty {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) :
    DenseRange (ArithmeticLatticeProjection.rationalProjection D i ∅) := by
  apply Function.Surjective.denseRange
  intro f
  refine ⟨1, funext fun w => ?_⟩
  exact (Finset.notMem_empty w.val w.property).elim

/-- The function-field spin case of the adelic conclusion. Every place
outside the omitted set is isolated using its finite-covolume projection. -/
theorem functionFieldSpinAdelicConclusions
    {K V : Type u} {C : Type v} [Field K] [Field C] [Finite C] [Algebra C K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (t : SeparatingParameter C K)
    (q : QuadraticForm K V) (r : Option V) (hreg : RegularModel q r)
    (ha : ∀ x, q x = 0 → x = 0) (hV : 5 ≤ Module.finrank K V)
    (G : AffineAlgebraicGroup K) (hG : IsAbsolutelyAlmostSimple G)
    (e : ∀ L : CommAlgCat.{u} K, SchemePoints G.val L →* (ScalarClifford q L)ˣ)
    (he : IsSpinPointRepresentation q G.val e) :
    AdelicConclusions (GlobalFieldData.function C t) G := by
  intro i
  let D : GlobalFieldData.{u,v} K := .function C t
  have hcompact := compactSpinAdelicQuotient D q r hreg ha hV G e he i
  refine ⟨hcompact, ?_⟩
  intro S _ hnc
  refine strongApproximationOfLocalProjections D i S ∅ (Finset.disjoint_empty_left S) ?_ hcompact hnc
    ?_ ?_ ?_
  · intro w
    exact w.elim
  · rintro ⟨w, hw⟩ _ H hc hn hμ
    cases w with
    | inl w =>
      refine fullProjectionOfFiniteCompletion LocalProjectedClosure.localProjectedClosure
        D i w hG ?_ H hc hn hμ
      exact Or.inr (Or.inr (Or.inl (finiteSpinIsotropic D q r hreg hV G e he w)))
    | inr w => exact w.elim
  · rintro ⟨w, hw⟩ _
    cases w with
    | inl w =>
      exact finiteSpinContractedDense D i w hG (finiteSpinIsotropic D q r hreg hV G e he w)
    | inr w => exact w.elim
  · exact denseProjectionToEmpty D i

/-- Openness of the diagonal closure gives density on a finite product of
connected local factors. -/
theorem denseProjectionOfConnectedFactors {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (T : Finset D.Place)
    (hconn : ∀ w : (↑T : Set D.Place), ConnectedSpace (LocalPoints D i w.1))
    (hopen : IsOpen (closure (Set.range (ArithmeticLatticeProjection.rationalProjection D i T)))) :
    DenseRange (ArithmeticLatticeProjection.rationalProjection D i T) := by
  let : ∀ w : (↑T : Set D.Place), ConnectedSpace (LocalPoints D i w.1) := hconn
  let : ConnectedSpace (FinitePoints D i T) := inferInstance
  let f := ArithmeticLatticeProjection.rationalProjection D i T
  exact dense_iff_closure_eq.mpr
    (IsClopen.eq_univ ⟨isClosed_closure, hopen⟩ ⟨f 1, subset_closure ⟨1, rfl⟩⟩)

section RealWords

open CliffordAlgebra Module Topology
open RealDefiniteSpinSpec
open private exists_sign innerCore norm_sq norm_eq_one_iff wordUnits wordUnits_cons
  vectorUnit word_det word_twists even_word_mem mem_spinSubgroup twists_mul twists_inv
  action_kernel Twists from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RealDefiniteSpin
open private orderedBasis from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Module.Finite ℝ E]

private abbrev orthogonalReflection (x : E) : E ≃ₗᵢ[ℝ] E := (ℝ ∙ x)ᗮ.reflection

private theorem normalizedReflectionWord (g : E ≃ₗᵢ[ℝ] E) :
    ∃ l : List E, l.length ≤ finrank ℝ E ∧ (∀ x ∈ l, ‖x‖ = 1) ∧
      g = (l.map orthogonalReflection).prod := by
  classical
  obtain ⟨l, hlen, hl⟩ := g.reflections_generate_dim
  let normalize (x : E) := ‖x‖⁻¹ • x
  let normalizeList (l : List E) := (l.filter (fun x => decide (x ≠ 0))).map normalize
  have hprod (l : List E) : (l.map orthogonalReflection).prod =
      ((normalizeList l).map orthogonalReflection).prod := by
    clear * - normalize normalizeList
    induction l with
    | nil => rfl
    | cons x l ih =>
      by_cases hx : x = 0
      · subst x
        have hz : orthogonalReflection (0 : E) = 1 := by
          ext y
          change orthogonalReflection (0 : E) y = y
          rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
          simp
        simpa [normalizeList, hz] using ih
      · have hspan : ℝ ∙ normalize x = ℝ ∙ x :=
          Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero (norm_ne_zero_iff.mpr hx))) x
        have h : orthogonalReflection (normalize x) = orthogonalReflection x :=
          congrArg (fun K : Submodule ℝ E => Kᗮ.reflection) hspan
        simpa [normalizeList, hx, h, Function.comp_def] using
          congrArg (fun z => orthogonalReflection x * z) ih
  let L := normalizeList l
  refine ⟨L, (List.length_map _).le.trans ((List.length_filter_le _ _).trans hlen), ?_,
    hl.trans (hprod l)⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  have hy₀ : y ≠ 0 := by simpa using (List.mem_filter.mp hy).2
  simp [normalize, norm_smul, norm_ne_zero_iff.mpr hy₀]

private theorem wordUnits_value (q : QuadraticForm ℝ E) (s : ℝ) (hs : s * s = 1)
    (l : List E) (hl : ∀ x ∈ l, q x = s) :
    (wordUnits q s hs l hl : CliffordAlgebra q) = (l.map (CliffordAlgebra.ι q)).prod := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [wordUnits_cons, Units.val_mul, ih]
    rfl

private theorem spinWordOfDefinite (q : QuadraticForm ℝ E) (hq : IsDefinite q)
    (s : ℝ) (hs : s * s = 1) (hinner : ∀ x y : E, inner ℝ x y = (s / 2) * q.polarBilin x y)
    (a : (CliffordAlgebra q)ˣ) (ha : a ∈ spinPoints q) :
    ∃ l : List E, l.length ≤ finrank ℝ E ∧ (∀ x ∈ l, ‖x‖ = 1) ∧ Even l.length ∧
      ((a : CliffordAlgebra q) = (l.map (CliffordAlgebra.ι q)).prod ∨
        (a : CliffordAlgebra q) = -(l.map (CliffordAlgebra.ι q)).prod) := by
  obtain ⟨⟨g, hg, -⟩, hg'⟩ := (RealDefiniteSpin.vectorAction q hq).1 a ha
  obtain ⟨hgq, hgd, _⟩ := hg' g hg
  let e : E ≃ₗᵢ[ℝ] E :=
    { g with
      norm_map' := fun x => by
        have h := norm_sq q s hinner (g x)
        rw [hgq, ← norm_sq q s hinner x] at h
        nlinarith [norm_nonneg (g x), norm_nonneg x] }
  obtain ⟨l, hlen, hnorm, hl⟩ := normalizedReflectionWord e
  have hlq (x : E) (hx : x ∈ l) : q x = s :=
    (norm_eq_one_iff q s hs hinner x).mp (hnorm x hx)
  have hlg : g = ((l.map orthogonalReflection).prod : E ≃ₗᵢ[ℝ] E).toLinearEquiv :=
    congrArg LinearIsometryEquiv.toLinearEquiv hl
  rw [hlg, word_det q s hs l hlq] at hgd
  have heven := (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hgd
  let b := wordUnits q s hs l hlq
  have hb := even_word_mem q s hs hinner l hlq heven
  have hat : Twists q a g := fun x => by simpa only [involute_eq_of_mem_even ha.1] using hg x
  have hbt : Twists q b g := hlg.symm ▸ word_twists q s hs hinner l hlq
  have hc : a * b⁻¹ ∈ spinPoints q := (mem_spinSubgroup q _).mp
    (mul_mem ((mem_spinSubgroup q _).mpr ha) (inv_mem ((mem_spinSubgroup q _).mpr hb)))
  have hct := twists_mul q hat (twists_inv q hbt)
  rw [mul_inv_cancel] at hct
  have hca : Acts q (a * b⁻¹) 1 := fun x => by
    simpa only [involute_eq_of_mem_even hc.1] using hct x
  have hbval := wordUnits_value q s hs l hlq
  refine ⟨l, hlen, hnorm, heven, ?_⟩
  rcases (action_kernel q hc hca hq).mp rfl with hp | hn
  · left
    rw [← hbval]
    simpa only [Units.val_mul, mul_assoc, Units.inv_mul, mul_one, one_mul] using
      congrArg (· * (b : CliffordAlgebra q)) hp
  · right
    rw [← hbval]
    simpa only [Units.val_mul, mul_assoc, Units.inv_mul, mul_one, neg_one_mul] using
      congrArg (· * (b : CliffordAlgebra q)) hn

omit [Module.Finite ℝ E] in
private theorem neg_mem_spinPoints (q : QuadraticForm ℝ E) {a : (CliffordAlgebra q)ˣ}
    (ha : a ∈ spinPoints q) : -a ∈ spinPoints q := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using neg_mem ha.1
  · simpa using ha.2.1
  · change Set.MapsTo (fun x => -(a : CliffordAlgebra q) * x * -(↑a⁻¹ : CliffordAlgebra q)) _ _
    simpa only [neg_mul, mul_neg, neg_neg] using ha.2.2.1
  · change Set.MapsTo (fun x => -(↑a⁻¹ : CliffordAlgebra q) * x * -(a : CliffordAlgebra q)) _ _
    simpa only [neg_mul, mul_neg, neg_neg] using ha.2.2.2

private def cliffordWord (q : QuadraticForm ℝ E) (n : ℕ)
    (x : Fin n → Metric.sphere (0 : E) 1) : CliffordAlgebra q :=
  (List.ofFn (fun j => CliffordAlgebra.ι q (x j).val)).prod

private theorem continuous_cliffordWord (q : QuadraticForm ℝ E) (n : ℕ) :
    @Continuous _ _ inferInstance (moduleTopology ℝ (CliffordAlgebra q)) (cliffordWord q n) := by
  let : TopologicalSpace (CliffordAlgebra q) := moduleTopology ℝ (CliffordAlgebra q)
  let : Module.Finite ℝ (CliffordAlgebra q) :=
    Module.Finite.of_basis (orderedBasis q (Module.finBasis ℝ _))
  let : IsTopologicalRing (CliffordAlgebra q) :=
    IsModuleTopology.isTopologicalRing ℝ (CliffordAlgebra q)
  have hι : Continuous (CliffordAlgebra.ι q) := LinearMap.continuous_of_finiteDimensional (CliffordAlgebra.ι q)
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hhead : Continuous (fun x : Fin (n + 1) → Metric.sphere (0 : E) 1 => CliffordAlgebra.ι q (x 0).val) :=
      hι.comp (continuous_subtype_val.comp (continuous_apply 0))
    have htail : Continuous (fun (x : Fin (n + 1) → Metric.sphere (0 : E) 1) (j : Fin n) => x j.succ) :=
      continuous_pi fun j => continuous_apply j.succ
    have heq : cliffordWord q (n + 1) = fun x =>
        CliffordAlgebra.ι q (x 0).val * cliffordWord q n (fun j => x j.succ) := by
      funext x
      unfold cliffordWord
      rw [List.ofFn_succ, List.prod_cons]
    rw [heq]
    exact hhead.mul (ih.comp htail)

/-- A definite real spin point is, up to sign, a word of bounded length in
unit vectors. Each allowed length gives a compact image of a product of
unit spheres. -/
private theorem isCompact_cliffordPoints_of_definite {V : Type*} [AddCommGroup V]
    [Module ℝ V] [Module.Finite ℝ V] (q : QuadraticForm ℝ V) (hq : IsDefinite q) :
    @IsCompact _ (moduleTopology ℝ (CliffordAlgebra q)) (cliffordPoints q) := by
  obtain ⟨s, hs, hpos⟩ := exists_sign q hq
  let core := innerCore q s hpos
  let := core.toNormedAddCommGroup
  let := InnerProductSpace.ofCore core.toCore
  have hinner (x y : V) : inner ℝ x y = (s / 2) * q.polarBilin x y := rfl
  let : TopologicalSpace (CliffordAlgebra q) := moduleTopology ℝ (CliffordAlgebra q)
  let : Module.Finite ℝ (CliffordAlgebra q) :=
    Module.Finite.of_basis (orderedBasis q (Module.finBasis ℝ _))
  let : IsTopologicalRing (CliffordAlgebra q) :=
    IsModuleTopology.isTopologicalRing ℝ (CliffordAlgebra q)
  let I := {n : Fin (finrank ℝ V + 1) // Even n.val}
  let C : Set (CliffordAlgebra q) := ⋃ n : I, Set.range (cliffordWord q n.val.val)
  let : CompactSpace (Metric.sphere (0 : V) 1) := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hC : IsCompact C := isCompact_iUnion (fun n : I =>
    isCompact_range (continuous_cliffordWord q n.val.val))
  have hsub : C ⊆ cliffordPoints q := by
    rintro _ hy
    obtain ⟨n, ⟨x, rfl⟩⟩ := Set.mem_iUnion.mp hy
    let l := List.ofFn (fun j => (x j).val)
    have hl (v : V) (hv : v ∈ l) : q v = s := by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
      exact (norm_eq_one_iff q s hs hinner _).mp (by simpa only [Metric.mem_sphere, dist_zero_right] using (x j).property)
    have heven : Even l.length := by simpa [l] using n.property
    refine ⟨wordUnits q s hs l hl, even_word_mem q s hs hinner l hl heven, ?_⟩
    rw [wordUnits_value q s hs l hl]
    simp [l, cliffordWord, List.map_ofFn, Function.comp_def]
  have hset : cliffordPoints q = C ∪ ((fun a : CliffordAlgebra q => -a) '' C) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨l, hlen, hnorm, heven, hval⟩ := spinWordOfDefinite q hq s hs hinner a ha
      let n : I := ⟨⟨l.length, Nat.lt_succ_of_le hlen⟩, heven⟩
      let x (j : Fin l.length) : Metric.sphere (0 : V) 1 :=
        ⟨l.get j, by simpa using hnorm _ (List.get_mem l j)⟩
      have hx : (l.map (CliffordAlgebra.ι q)).prod ∈ C := by
        apply Set.mem_iUnion.mpr
        refine ⟨n, x, ?_⟩
        simp [cliffordWord, x, n]
      rcases hval with h | h
      · exact Or.inl (h ▸ hx)
      · exact Or.inr ⟨_, hx, h.symm⟩
    · rintro _ (hc | ⟨a, ha, rfl⟩)
      · exact hsub hc
      · obtain ⟨b, hb, rfl⟩ := hsub ha
        exact ⟨-b, neg_mem_spinPoints q hb, Units.val_neg b⟩
  exact hset ▸ (hC.union (hC.image continuous_neg))

end RealWords

section RealCliffordPoints

open Opposite CliffordAlgebra Topology
open _root_.LinearAlgebraicGroups.Albert.CliffordSpecification (coefficientForm)
open _root_.LinearAlgebraicGroups.Albert.SpinFunctor (Spin CoordinateRing changeCoefficients pointEquiv)
open Specs.AdjointRepresentation (GroupPoints)
open AdelicGroups (asMatrix)
open RealDefiniteSpinSpec (spinPoints cliffordPoints)
open private cliffordSchemeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicSpinQuotients
open private glVal_isEmbedding from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private matrixTransformation matrix_naturality from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalCocharacterEvaluation
open private equationIdeal extendedBasis homFromPoint EvenIndex from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

open private coordinateMap coordinateMap_spec from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels

private theorem conjugation_image_eq {A : Type*} [Monoid A] (a : Aˣ) (S : Set A) :
    (fun z : A => (a : A) * z * (↑a⁻¹ : A)) '' S = S ↔
      Set.MapsTo (fun z : A => (a : A) * z * (↑a⁻¹ : A)) S S ∧
      Set.MapsTo (fun z : A => (↑a⁻¹ : A) * z * (a : A)) S S := by
  constructor
  · intro h
    refine ⟨fun z hz => h ▸ Set.mem_image_of_mem _ hz, ?_⟩
    intro z hz
    obtain ⟨x, hx, rfl⟩ := h.symm ▸ hz
    simpa only [mul_assoc, ← mul_assoc (↑a⁻¹ : A) (a : A), Units.inv_mul, one_mul,
      ← mul_assoc x (↑a⁻¹ : A), Units.inv_mul, mul_one] using hx
  · rintro ⟨hp, hm⟩
    refine Set.Subset.antisymm (Set.image_subset_iff.mpr hp) ?_
    intro z hz
    refine ⟨(↑a⁻¹ : A) * z * (a : A), hm hz, ?_⟩
    simp only [mul_assoc, Units.mul_inv, mul_one, ← mul_assoc (a : A) (↑a⁻¹ : A), one_mul]

private def realCliffordSpinEquiv {K V : Type u} [Field K] [Algebra K ℝ]
    [AddCommGroup V] [Module K V] {n : ℕ}
    (q : QuadraticForm K V) (b : Module.Basis (Index.{u} n) K V)
    (a : ScalarClifford q ℝ ≃ₐ[ℝ] CliffordAlgebra (coefficientForm ℝ q b))
    (ha : ∀ x : (ScalarClifford q ℝ)ˣ, x ∈ spinUnits q ℝ ↔
      Units.map a.toMonoidHom x ∈ spinPoints (coefficientForm ℝ q b)) :
    Spin q ℝ b ≃ cliffordPoints (coefficientForm ℝ q b) := by
  let f (x : Spin q ℝ b) : cliffordPoints (coefficientForm ℝ q b) :=
    ⟨a (x.val : ScalarClifford q ℝ), ⟨Units.map a.toMonoidHom x.val, (ha _).mp x.property, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    apply Units.ext
    exact a.injective (congrArg Subtype.val h)
  · rintro ⟨_, y, hy, rfl⟩
    let x := (Units.mapEquiv a.toMulEquiv).symm y
    have hx : Units.map a.toMonoidHom x = y := (Units.mapEquiv a.toMulEquiv).apply_symm_apply y
    exact ⟨⟨x, (ha x).mpr (hx.symm ▸ hy)⟩, Subtype.ext (congrArg Units.val hx)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The real Clifford locus parametrizes the given local points. Matrix entries of
the universal spin point specialize by evaluating polynomials in the even
Clifford coordinates. -/
private theorem continuousRealCliffordParametrization
    {K F V : Type u} [Field K] [Field F] [Algebra K F] [Algebra K ℝ]
    [TopologicalSpace F] [IsTopologicalDivisionRing F]
    [AddCommGroup V] [Module K V] {n : ℕ}
    (q : QuadraticForm K V) (b : Module.Basis (Index.{u} n) K V)
    (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (ρ : ∀ S : CommAlgCat.{u} K, SchemePoints G.val S →* (ScalarClifford q S)ˣ)
    (hρ : IsSpinPointRepresentation q G.val ρ)
    (e : F ≃ₐ[K] ℝ) (he : Continuous e.symm) :
    let P := coefficientForm ℝ q b
    letI : TopologicalSpace (CliffordAlgebra P) := moduleTopology ℝ (CliffordAlgebra P)
    ∃ f : cliffordPoints P → PointsIn i F, Continuous f ∧ Function.Surjective f := by
  classical
  let P := coefficientForm ℝ q b
  let : TopologicalSpace (CliffordAlgebra P) := moduleTopology ℝ (CliffordAlgebra P)
  let : IsModuleTopology ℝ (CliffordAlgebra P) := ⟨rfl⟩
  obtain ⟨a, _, ha⟩ := _root_.LinearAlgebraicGroups.Albert.SpinFunctor.intrinsicCriterion q b ℝ
  have hspin (x : (ScalarClifford q ℝ)ˣ) : x ∈ spinUnits q ℝ ↔
      Units.map a.toMonoidHom x ∈ spinPoints P := by
    rw [ha x]
    refine and_congr_right fun _ => and_congr_right fun _ => ?_
    exact conjugation_image_eq (Units.map a.toMonoidHom x) (LinearMap.range (CliffordAlgebra.ι P))
  let E := realCliffordSpinEquiv q b a hspin
  have hval (x : cliffordPoints P) : ((E.symm x).val : ScalarClifford q ℝ) = a.symm x.val := by
    apply a.injective
    exact (congrArg Subtype.val (E.apply_symm_apply x)).trans (a.apply_symm_apply _).symm
  let A := CommAlgCat.of K (CoordinateRing q b)
  let S := CommAlgCat.of K F
  let α := cliffordSchemeIso q b G ρ hρ
  let β : G.val.X ≅ (testSpec K).obj (op A) := (Grp.forget _).mapIso α
  let p : GroupPoints G.val A := β.inv
  let f (x : cliffordPoints P) : A ⟶ S :=
    CommAlgCat.ofHom (e.symm.toAlgHom.comp ((pointEquiv q b ℝ).symm (E.symm x)))
  let g (x : cliffordPoints P) : PointsIn i F := mapPoints (f x) p
  refine ⟨g, ?_, ?_⟩
  · have hcoord (s : Finset (Index.{u} n)) : Continuous (fun x : cliffordPoints P =>
        (extendedBasis q ℝ b).coord s (a.symm x.val)) :=
      (IsModuleTopology.continuous_of_linearMap
        ((extendedBasis q ℝ b).coord s ∘ₗ a.symm.toLinearMap)).comp continuous_subtype_val
    have hregular (z : A) : Continuous fun x : cliffordPoints P => (f x).hom z := by
      obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective (I := equationIdeal q b) z
      have hargs : Continuous (fun (x : cliffordPoints P) (s : EvenIndex (Index.{u} n)) =>
          (extendedBasis q ℝ b).coord s.1 (a.symm x.val)) := continuous_pi fun s => hcoord s.1
      have hcont := (MvPolynomial.continuous_eval (m.map (algebraMap K ℝ))).comp hargs
      simp only [MvPolynomial.eval_map] at hcont
      apply he.comp ?_
      convert hcont using 1
      funext x
      change homFromPoint q b ℝ (E.symm x) (Ideal.Quotient.mk _ m) = _
      change MvPolynomial.eval₂ (algebraMap K ℝ)
        (fun s => (extendedBasis q ℝ b).coord s.1 ((E.symm x).val : ScalarClifford q ℝ)) m = _
      simp only [hval x, Function.comp_apply]
    have hM : IsInducing (fun g : PointsIn i F => (asMatrix i F g).val) :=
      glVal_isEmbedding.isInducing.comp (show IsInducing (asMatrix i F) from ⟨rfl⟩)
    apply hM.continuous_iff.mpr
    apply continuous_matrix
    intro k l
    change Continuous (fun x : cliffordPoints P => (asMatrix i F (g x)).val k l)
    have h (x : cliffordPoints P) : (asMatrix i F (g x)).val k l =
        (f x).hom ((asMatrix i A p).val k l) :=
      matrix_naturality (matrixTransformation i) (f x) p k l
    simpa only [h] using hregular ((asMatrix i A p).val k l)
  · intro x
    let d := coordinateMap (x ≫ β.hom)
    let y := pointEquiv q b ℝ (e.toAlgHom.comp d.hom)
    refine ⟨E y, ?_⟩
    have hf : f (E y) = d := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro z
      change e.symm (((pointEquiv q b ℝ).symm (E.symm (E y))) z) = d.hom z
      rw [E.symm_apply_apply]
      rw [show (pointEquiv q b ℝ).symm y = e.toAlgHom.comp d.hom from
        (pointEquiv q b ℝ).symm_apply_apply _]
      exact e.symm_apply_apply _
    change mapPoints (f (E y)) p = x
    rw [hf]
    change (testSpec K).map d.op ≫ β.inv = x
    rw [show (testSpec K).map d.op = x ≫ β.hom from coordinateMap_spec (x ≫ β.hom),
      Category.assoc, β.hom_inv_id, Category.comp_id]

end RealCliffordPoints

section ArchimedeanSpin

open _root_.LinearAlgebraicGroups.Albert.CliffordSpecification (coefficientForm)
open AdelicGroups (StrongApproximation)
open RealDefiniteSpinSpec (cliffordPoints)
open private exists_isotropic_binary from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RankEightSpinStructure
open private definite_of_real_anisotropic from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinIsotropy
open private strongApproximationFromNumberFieldLocalModels numberApproximationOfSameUniverse from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryApproximation

private theorem isAlgClosed_of_complexEquiv {F : Type u} [Field F] (e : F ≃+* ℂ) :
    IsAlgClosed F := by
  apply IsAlgClosed.of_exists_root
  intro p _ hp
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_eval₂_eq_zero e.toRingHom p
    (Polynomial.degree_pos_of_irreducible hp).ne'
  refine ⟨e.symm z, e.injective ?_⟩
  rw [map_zero, Polynomial.eval]
  change e.toRingHom (p.eval₂ (RingHom.id F) (e.symm z)) = 0
  rw [Polynomial.hom_eval₂]
  change p.eval₂ e.toRingHom (e (e.symm z)) = 0
  rwa [e.apply_symm_apply]

private theorem isIsotropic_of_isAlgClosed {F W : Type u} [Field F] [IsAlgClosed F]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (Q : QuadraticForm F W) (hd : 2 ≤ Module.finrank F W) : IsIsotropic Q := by
  let d := Module.finBasis F W
  let i := Fin.castLEEmb hd
  let f : Fin 2 → W := d ∘ i
  let S := Submodule.span F (Set.range f)
  let b : Module.Basis (Fin 2) F S := Module.Basis.span (d.linearIndependent.comp i i.injective)
  obtain ⟨x, hx, hQ⟩ := exists_isotropic_binary (Q.comp S.subtype) b
  exact ⟨x.val, fun h => hx (Subtype.ext h), hQ⟩

private theorem archimedeanCompletionModels {K : Type u} [Field K] [NumberField K]
    (D : GlobalFieldData.{u,v} K) (hD : D = .number inferInstance) (w : D.InfinitePlace) :
    (∃ e : D.Completion (.inr w) ≃+* ℝ, Continuous e.symm) ∨
      IsAlgClosed (D.Completion (.inr w)) := by
  subst D
  open NumberField.InfinitePlace.Completion in
  rcases w.isReal_or_isComplex with hr | hc
  · exact Or.inl ⟨ringEquivRealOfIsReal hr, (isometryEquivRealOfIsReal hr).symm.continuous⟩
  · exact Or.inr (isAlgClosed_of_complexEquiv (F := w.Completion) (ringEquivComplexOfIsComplex hc))

private theorem archimedeanContractingScalars {K : Type u} [Field K] [NumberField K]
    (D : GlobalFieldData.{u,v} K) (hD : D = .number inferInstance) (w : D.InfinitePlace) :
    ∃ a : Algebra ℝ (D.Completion (.inr w)),
      letI := a
      Continuous (algebraMap ℝ (D.Completion (.inr w))) := by
  subst D
  change ∃ a : Algebra ℝ w.Completion, letI := a; Continuous (algebraMap ℝ w.Completion)
  obtain ⟨a, _, ha⟩ := LocalCocharacterEvaluation.archimedeanCompletionScalars w
  exact ⟨a, ha⟩

private theorem spinContractedGenerationOfRealScalars {K : Type u} [Field K]
    {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    (w : D.Place) [Algebra ℝ (D.Completion w)]
    (hscalar : Continuous (algebraMap ℝ (D.Completion w)))
    (hG : IsAbsolutelyAlmostSimple G)
    (hi : IsIsotropicQuadraticSpin (baseChangedAlgebraicGroup (D.Completion w) G)) :
    Subgroup.closure {x : LocalPoints D i w | Contracted x} = ⊤ := by
  let F := D.Completion w
  let _ : Algebra K F := AdelicGroups.completionAlgebra D w
  let : Infinite K := globalField_infinite D
  let : Infinite F := Infinite.of_injective (algebraMap K F) (algebraMap K F).injective
  let L := baseChangedAlgebraicGroup F G
  have hL := OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G hG
  obtain ⟨j, ⟨d⟩⟩ := completionMatrixComparison D i w
  change IsIsotropicQuadraticSpin L at hi
  obtain ⟨V, _, _, _, q, ρ, _, hq, hqiso, hρ⟩ := hi
  obtain ⟨c, P, Q, hsections⟩ := spinOppositeSectionsGenerate q hq hqiso L hL ρ hρ
  obtain ⟨t, ht⟩ := LocalCocharacterEvaluation.contractingScalarExists (E := ℝ)
  have hcont : Continuous (algebraMap ℝ F) := hscalar
  have hgen := oppositeSectionsGiveContracted L j c P Q hsections
    (fun e R x hx => ⟨_, LocalCocharacterEvaluation.contractingEvaluation L j e R hcont t ht x hx⟩)
  exact contractedGenerationOfEquiv d hgen

private theorem coefficientForm_throughRealEquiv {K F V : Type u} [Field K] [Field F]
    [Algebra K F] [Algebra K ℝ] [AddCommGroup V] [Module K V] {n : ℕ}
    (q : QuadraticForm K V) (b : Module.Basis (Index.{u} n) K V) (e : F ≃ₐ[K] ℝ)
    (x : F ⊗[K] V) :
    coefficientForm ℝ q b (TensorProduct.congr e.toLinearEquiv (.refl K V) x) =
      e (coefficientForm F q b x) := by
  let a := TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl K V)
  let B := q.toBilin b
  change (LinearMap.BilinForm.baseChange ℝ B) (a x) (a x) =
    e ((LinearMap.BilinForm.baseChange F B) x x)
  suffices h : ∀ (v w : F ⊗[K] V), (LinearMap.BilinForm.baseChange ℝ B) (a v) (a w) =
      e ((LinearMap.BilinForm.baseChange F B) v w) by exact h x x
  intro v w
  induction v using TensorProduct.inductionOn with
  | add v v' hv hv' => simp [hv, hv']
  | tmul f x =>
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp [hw, hw']
    | tmul g y =>
      simp [a, TensorProduct.congr_tmul, LinearMap.BilinForm.baseChange_tmul,
        Algebra.smul_def]

private theorem realCoefficientForm_definite {K F V : Type u} [Field K] [Field F]
    [Algebra K F] [Algebra K ℝ] [AddCommGroup V] [Module K V] {n : ℕ}
    (q : QuadraticForm K V) (b : Module.Basis (Index.{u} n) K V) (e : F ≃ₐ[K] ℝ)
    (hq : ¬ IsIsotropic (coefficientForm F q b)) :
    RealDefiniteSpinSpec.IsDefinite (coefficientForm ℝ q b) := by
  let a := TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl K V)
  rcases definite_of_real_anisotropic e.toRingEquiv (coefficientForm F q b) hq with h | h
  · left
    intro x hx
    obtain ⟨y, rfl⟩ := a.surjective x
    rw [coefficientForm_throughRealEquiv q b e y]
    exact h y (fun hy => hx (hy ▸ map_zero a))
  · right
    intro x hx
    obtain ⟨y, rfl⟩ := a.surjective x
    rw [coefficientForm_throughRealEquiv q b e y]
    exact h y (fun hy => hx (hy ▸ map_zero a))

/-- Compactness and connectedness transfer from the intrinsic real Clifford
locus to the actual matrix points of the original model. -/
private theorem compactConnectedRealSpin {K F V : Type u} [Field K] [Field F]
    [Algebra K F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    [AddCommGroup V] [Module K V] {n : ℕ}
    (q : QuadraticForm K V) (b : Module.Basis (Index.{u} n) K V) (hn : 2 ≤ n)
    (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (ρ : ∀ S : CommAlgCat.{u} K, SchemePoints G.val S →* (ScalarClifford q S)ˣ)
    (hρ : IsSpinPointRepresentation q G.val ρ)
    (e : F ≃+* ℝ) (he : Continuous e.symm)
    (hq : ¬ IsIsotropic (coefficientForm F q b)) :
    CompactSpace (PointsIn i F) ∧ ConnectedSpace (PointsIn i F) := by
  let : Algebra K ℝ := (e.toRingHom.comp (algebraMap K F)).toAlgebra
  let E : F ≃ₐ[K] ℝ := { toRingEquiv := e, commutes' := fun _ => rfl }
  let P := coefficientForm ℝ q b
  have hP := realCoefficientForm_definite q b E hq
  have hdim : 2 ≤ Module.finrank ℝ (ℝ ⊗[K] V) := by
    rw [Module.finrank_eq_card_basis (b.baseChange ℝ)]
    simpa [Index] using hn
  let : Module.Finite ℝ (ℝ ⊗[K] V) := Module.Finite.of_basis (b.baseChange ℝ)
  let : TopologicalSpace (CliffordAlgebra P) :=
    moduleTopology ℝ (CliffordAlgebra P)
  obtain ⟨f, hf, hs⟩ := continuousRealCliffordParametrization q b G i ρ hρ E he
  let : CompactSpace (cliffordPoints P) :=
    isCompact_iff_compactSpace.mp (isCompact_cliffordPoints_of_definite P hP)
  let : ConnectedSpace (cliffordPoints P) :=
    isConnected_iff_connectedSpace.mp (RealDefiniteSpin.pathConnected P hP hdim).isConnected
  exact ⟨Function.Surjective.compactSpace hf hs, hs.connectedSpace hf⟩

private theorem archimedeanSpinLocalModels {K V : Type u} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (D : GlobalFieldData.{u,v} K) (hD : D = .number inferInstance)
    (q : QuadraticForm K V) (hreg : LinearMap.ker q.polarBilin = ⊥)
    (hV : 5 ≤ Module.finrank K V) (G : AffineAlgebraicGroup K) (hG : IsAbsolutelyAlmostSimple G)
    (e : ∀ L : CommAlgCat.{u} K, SchemePoints G.val L →* (ScalarClifford q L)ˣ)
    (he : IsSpinPointRepresentation q G.val e) (i : MatrixRealization G)
    (w : D.InfinitePlace) :
    (CompactSpace (LocalPoints D i (.inr w)) ∧ ConnectedSpace (LocalPoints D i (.inr w))) ∨
    (Dense (Subgroup.closure (localPointSet D i (.inr w)
        (cocharacterRadicalPoints (baseChangedAlgebraicGroup (D.Completion (.inr w)) G))) :
        Set (LocalPoints D i (.inr w))) ∧
     Dense (Subgroup.closure {x : LocalPoints D i (.inr w) | Contracted x} :
        Set (LocalPoints D i (.inr w)))) := by
  let F := D.Completion (.inr w)
  let _ : Algebra K F := AdelicGroups.completionAlgebra D (.inr w)
  let b : Module.Basis (Index.{u} (Module.finrank K V)) K V :=
    (Module.finBasis K V).reindex Equiv.ulift.symm
  let Q := coefficientForm F q b
  by_cases hi : IsIsotropic Q
  · right
    have hVF : 5 ≤ Module.finrank F (F ⊗[K] V) := by
      rw [Module.finrank_eq_card_basis (b.baseChange F), ← Module.finrank_eq_card_basis b]
      exact hV
    obtain ⟨_, ρF, _, _, _, _, _, _, hrep, _⟩ :=
      SpinScalarExtension.spinRepresentationExtension (F := F) q b G e he
    obtain ⟨_, hrad, _⟩ := SpinScalarExtension.polarRadicalExtension (F := F) q b
    have hmodel : IsIsotropicQuadraticSpin (baseChangedAlgebraicGroup F G) :=
      ⟨F ⊗[K] V, inferInstance, inferInstance, inferInstance, Q, ρF, hVF,
        Or.inl (hrad hreg), hi, hrep⟩
    refine ⟨?_, ?_⟩
    · rw [localSpinRadicalsGenerate D i (.inr w) hG hmodel, Subgroup.coe_top]
      exact dense_univ
    · obtain ⟨a, ha⟩ := archimedeanContractingScalars D hD w
      let := a
      rw [spinContractedGenerationOfRealScalars D i (.inr w) ha hG hmodel, Subgroup.coe_top]
      exact dense_univ
  · left
    rcases archimedeanCompletionModels D hD w with ⟨f, hf⟩ | hC
    · exact compactConnectedRealSpin q b (by omega) G i e he f hf hi
    · let : IsAlgClosed F := hC
      have hVF : 2 ≤ Module.finrank F (F ⊗[K] V) := by
        rw [Module.finrank_eq_card_basis (b.baseChange F), ← Module.finrank_eq_card_basis b]
        omega
      exact (hi (isIsotropic_of_isAlgClosed Q hVF)).elim

private theorem numberFieldSpinStrongApproximation
    {K V : Type u} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (q : QuadraticForm K V) (hreg : LinearMap.ker q.polarBilin = ⊥)
    (ha : ∀ x, q x = 0 → x = 0) (hV : 5 ≤ Module.finrank K V)
    (G : AffineAlgebraicGroup K) (hG : IsAbsolutelyAlmostSimple G)
    (e : ∀ L : CommAlgCat.{u} K, SchemePoints G.val L →* (ScalarClifford q L)ˣ)
    (he : IsSpinPointRepresentation q G.val e) (i : MatrixRealization G)
    (S : Finset (NumberPlace K)) :
    ¬ CompactSpace (FinitePoints (.number.{u,v} inferInstance) i S) →
      StrongApproximation (.number.{u,v} inferInstance) i S := by
  apply numberApproximationOfSameUniverse i S
  let D : GlobalFieldData.{u,u} K := .number inferInstance
  intro hS
  have hc := compactSpinAdelicQuotient D q none hreg ha hV G e he i
  apply strongApproximationFromNumberFieldLocalModels LocalProjectedClosure.localProjectedClosure
    D rfl i S hG hc hS ∅
  · intro w _
    have hmodel := finiteSpinIsotropic D q none hreg hV G e he w
    refine ⟨Or.inr (Or.inr (Or.inl hmodel)), ?_⟩
    rw [contractedGenerationOfEquiv (singletonLocalPoints D i (.inl w))
      (finiteSpinContractedGeneration D i w hG hmodel), Subgroup.coe_top]
    exact dense_univ
  · exact archimedeanSpinLocalModels D rfl q hreg hV G hG e he i
  · intro J hJ
    have h : J = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun w hw => by
      obtain ⟨p, hp, _⟩ := hJ w hw
      exact Finset.notMem_empty p hp
    subst J
    exact denseProjectionToEmpty D i

/-- Strong approximation and compactness for the regular anisotropic spin
models over both kinds of global field. -/
theorem quadraticSpin : QuadraticSpin.{u,v} := by
  intro K V _ _ _ _ D q r hreg ha hV G e hG _ _ he
  cases D with
  | number hK =>
    let : NumberField K := hK
    have hreg₀ : LinearMap.ker q.polarBilin = ⊥ := by
      cases r with
      | none => exact hreg
      | some _ => exact (two_ne_zero hreg.1).elim
    intro i
    refine ⟨compactSpinAdelicQuotient (.number.{u,v} hK) q r hreg ha hV G e he i, ?_⟩
    intro S _
    exact numberFieldSpinStrongApproximation q hreg₀ ha hV G hG e he i S
  | function F t =>
    exact functionFieldSpinAdelicConclusions t q r hreg ha hV G hG e he

end ArchimedeanSpin

theorem innerTypeA : InnerTypeA.{u,v} := AnisotropicDivisionApproximation.innerTypeA

theorem rankOneQuadraticSpin : RankOneQuadraticSpin.{u,v} :=
  AnisotropicDivisionApproximation.rankOneQuadraticSpin

theorem outerTypeA : OuterTypeA.{u,v} := AnisotropicUnitaryApproximation.outerTypeA

theorem typeC : TypeC.{u,v} := AnisotropicSymplecticApproximation.typeC

theorem octonion : Octonion.{u,v} := AnisotropicOctonionApproximation.octonion

end LinearAlgebraicGroups.Arithmetic.AnisotropicClassicalApproximation
