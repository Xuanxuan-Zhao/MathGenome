import Specs.LinearAlgebraicGroups.Arithmetic.RankEightSpinStructure
import LinearAlgebraicGroups.Albert.SpinWeights
import LinearAlgebraicGroups.Arithmetic.OddSpinModels
import LinearAlgebraicGroups.Arithmetic.SpinHyperbolicDynamics
import LinearAlgebraicGroups.Reductive.RadicalBaseChange
import LinearAlgebraicGroups.RootData.BorelsAndChambers
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.LinearAlgebra.TensorProduct.Prod

namespace LinearAlgebraicGroups.Arithmetic.RankEightSpinStructure

open CategoryTheory AlgebraicGeometry Module
open scoped CategoryTheory.MonObj TensorProduct
open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricRadicals (IsReductive IsSplitReductive IsSplitTorus IsMaximalTorus
  baseChangedSubgroup)
open Specs.GeometricBorelConjugacy (IsBorel IsKBorel IsQuasiSplit)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.RankOneFlag (SameSubgroup IsGeometricallyMaximal)
open Specs.AdjointRepresentation (GroupPoints)
open Algebra.TensorProduct CliffordAlgebra
open Albert.SpinSpecification (ScalarClifford SchemePoints vectors reversion evenPart
  spinUnits coefficientMap IsSpinPointRepresentation conjugate)
open Albert.CliffordSpecification (coefficientForm)
open Albert.CliffordModel (baseChangeEquiv baseChangeEquiv_ι coefficientForm_tmul)
open Albert.SplitSpinSpecification (integralForm hyperbolicBasis hyperbolicNorm)
open Specs.SpinWeights (SpinPointPresentation)
open private transportSubgroup maximal_of_square
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private reductive_of_groupIso extendSubgroup
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private exists_regular_cocharacter
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private baseChangeEquiv_evenOdd baseChangeEquiv_reverse
  from LinearAlgebraicGroups.Albert.CliffordModel

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K]

private theorem borel_transport {G H : Specs.GroupScheme K} (e : G ≅ H)
    {B : ClosedSubgroup G} (hB : IsBorel B) :
    IsBorel (transportSubgroup e B) := by
  refine ⟨hB.1, ?_⟩
  intro C hC hBC
  obtain ⟨f, hf⟩ := hBC
  change f ≫ C.inclusion = B.inclusion ≫ e.hom at hf
  have h : IsSubgroupOf B (transportSubgroup e.symm C) := ⟨f, by
    change f ≫ C.inclusion ≫ e.inv = B.inclusion
    rw [← Category.assoc, hf, Category.assoc, e.hom_inv_id, Category.comp_id]⟩
  obtain ⟨g, hg⟩ := hB.2 _ hC h
  refine ⟨g, ?_⟩
  change g ≫ B.inclusion = C.inclusion ≫ e.inv at hg
  change g ≫ B.inclusion ≫ e.hom = C.inclusion
  rw [← Category.assoc, hg, Category.assoc, e.inv_hom_id, Category.comp_id]

private theorem split_and_quasiSplit_of_reference {G H : Specs.AffineAlgebraicGroup K}
    (e : G.val ≅ H.val) (hG : IsReductive G) (T : ClosedSubgroup G.val)
    (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T) :
    IsSplitReductive H ∧ IsQuasiSplit H := by
  have hH := reductive_of_groupIso e hG
  let Kbar := AlgebraicClosure K
  let E := (groupBaseChange K Kbar).mapIso e
  obtain ⟨c, hc⟩ := exists_regular_cocharacter G T hT
  obtain ⟨D⟩ := CocharacterDynamics.existsLimitDecomposition G (c ≫ T.inclusion)
  have hB := (RootData.BorelsAndChambers.regularCocharacterBorel G hG T hT hTm c hc D).2.1
  let T' := transportSubgroup e T
  let B' := transportSubgroup e D.parabolic
  refine ⟨⟨hH, T', hT, (extendSubgroup Kbar T').isClosedImmersion, ?_⟩,
    ⟨hH, B', (extendSubgroup Kbar B').isClosedImmersion, ?_⟩⟩
  · apply maximal_of_square E (extendSubgroup Kbar T) (extendSubgroup Kbar T') (Iso.refl _)
    · change 𝟙 _ ≫ (groupBaseChange K Kbar).map (T.inclusion ≫ e.hom) =
        (groupBaseChange K Kbar).map T.inclusion ≫ (groupBaseChange K Kbar).map e.hom
      rw [Category.id_comp, Functor.map_comp]
    · exact hTm.choose_spec
  · have H' := borel_transport E hB.choose_spec
    have he : baseChangedSubgroup Kbar B' (extendSubgroup Kbar B').isClosedImmersion =
        transportSubgroup E (extendSubgroup Kbar D.parabolic) := by
      change (⟨_, (groupBaseChange K Kbar).map (D.parabolic.inclusion ≫ e.hom), _⟩ :
        ClosedSubgroup _) = ⟨_, (groupBaseChange K Kbar).map D.parabolic.inclusion ≫
          (groupBaseChange K Kbar).map e.hom, _⟩
      congr 1
      exact Functor.map_comp _ _ _
    exact he ▸ H'


private abbrev modelForm (K : Type u) [Field K] :=
  coefficientForm K (integralForm 4) (hyperbolicBasis ℤ 4)

private def integralComparison (R : TestAlgebra K) :
    ScalarClifford (integralForm 4) R ≃ₐ[R] ScalarClifford (modelForm K) R := by
  let L := (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ K R R
    (CliffordAlgebra (integralForm 4))).symm
  let C : ScalarClifford (integralForm 4) R ≃ₐ[R]
      R ⊗[K] (K ⊗[ℤ] CliffordAlgebra (integralForm 4)) := by
    refine AlgEquiv.ofLinearEquiv L ?_ ?_
    · exact TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul ℤ K R 1 1
    · refine LinearMap.map_mul_of_map_mul_tmul (R := ℤ) (S := R) (A := R)
        (B := CliffordAlgebra (integralForm 4))
        (C := R ⊗[K] (K ⊗[ℤ] CliffordAlgebra (integralForm 4))) (f := L.toLinearMap) ?_
      intro r s a b
      simp only [LinearEquiv.coe_coe, L, Algebra.TensorProduct.tmul_mul_tmul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, one_mul]
  exact C.trans (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R)
    (baseChangeEquiv K (integralForm 4) (hyperbolicBasis ℤ 4)))

private theorem integralComparison_tmul (R : TestAlgebra K) (r : R)
    (a : CliffordAlgebra (integralForm 4)) :
    integralComparison R (r ⊗ₜ[ℤ] a) =
      r ⊗ₜ[K] baseChangeEquiv K (integralForm 4) (hyperbolicBasis ℤ 4) (1 ⊗ₜ[ℤ] a) := rfl

private abbrev integralVectorComparison (R : TestAlgebra K) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ K R R
    (Albert.SplitSpinSpecification.HyperbolicModule ℤ 4)).symm

private theorem integralComparison_vectors (R : TestAlgebra K)
    (x : Albert.SplitSpinSpecification.ExtendedModule 4 R) :
    integralComparison R (vectors (integralForm 4) R x) =
      vectors (modelForm K) R (integralVectorComparison R x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r v =>
    rw [LinearMap.baseChange_tmul, integralComparison_tmul, baseChangeEquiv_ι]
    simp [integralVectorComparison, LinearMap.baseChange_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem integralComparison_reversion (R : TestAlgebra K)
    (a : ScalarClifford (integralForm 4) R) :
    integralComparison R (reversion (integralForm 4) R a) =
      reversion (modelForm K) R (integralComparison R a) := by
  induction a using TensorProduct.inductionOn with
  | tmul r a =>
    simp only [LinearMap.baseChange_tmul, integralComparison_tmul]
    congr 1
    exact baseChangeEquiv_reverse K (integralForm 4) (hyperbolicBasis ℤ 4)
      (1 ⊗ₜ[ℤ] a)
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem integralComparison_even (R : TestAlgebra K) :
    (evenPart (integralForm 4) R).map (integralComparison R).toLinearMap =
      evenPart (modelForm K) R := by
  let A := baseChangeEquiv K (integralForm 4) (hyperbolicBasis ℤ 4)
  have h : evenOdd (modelForm K) 0 =
      Submodule.span K ((fun a : CliffordAlgebra (integralForm 4) => A (1 ⊗ₜ[ℤ] a)) ''
        (evenOdd (integralForm 4) 0 : Set _)) := by
    rw [← baseChangeEquiv_evenOdd K (integralForm 4) (hyperbolicBasis ℤ 4) 0,
      Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]
    rfl
  change ((evenOdd (integralForm 4) 0).baseChange R).map
    (integralComparison R).toLinearMap = (evenOdd (modelForm K) 0).baseChange R
  rw [Submodule.baseChange_eq_span, Submodule.map_span, h, Submodule.baseChange_span,
    Submodule.map_coe, Set.image_image, Set.image_image]
  apply congrArg (Submodule.span R)
  exact Set.image_congr (fun a _ => integralComparison_tmul R 1 a)

private theorem integralComparison_spin (R : TestAlgebra K)
    (a : (ScalarClifford (integralForm 4) R)ˣ) :
    Units.map (integralComparison R).toMonoidHom a ∈ spinUnits (modelForm K) R ↔
      a ∈ spinUnits (integralForm 4) R := by
  let E := integralComparison R
  let U := integralVectorComparison R
  have hr (x : ScalarClifford (integralForm 4) R) :
      E x ∈ LinearMap.range (vectors (modelForm K) R) ↔
        x ∈ LinearMap.range (vectors (integralForm 4) R) := by
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨z, rfl⟩ := U.surjective y
      exact ⟨z, E.injective ((integralComparison_vectors R z).trans hy)⟩
    · rintro ⟨z, rfl⟩
      exact ⟨U z, (integralComparison_vectors R z).symm⟩
  have hn (b : (ScalarClifford (integralForm 4) R)ˣ) :
      Set.MapsTo (conjugate (modelForm K) R (Units.map E.toMonoidHom b))
          (LinearMap.range (vectors (modelForm K) R)) (LinearMap.range (vectors (modelForm K) R)) ↔
        Set.MapsTo (conjugate (integralForm 4) R b)
          (LinearMap.range (vectors (integralForm 4) R)) (LinearMap.range (vectors (integralForm 4) R)) := by
    have hc (x : ScalarClifford (integralForm 4) R) :
        E (conjugate (integralForm 4) R b x) =
          conjugate (modelForm K) R (Units.map E.toMonoidHom b) (E x) := by
      simp only [conjugate, map_mul, Units.coe_map, Units.coe_map_inv]
      rfl
    constructor
    · intro h x hx
      exact (hr _).mp (hc x ▸ h ((hr x).mpr hx))
    · intro h y hy
      obtain ⟨x, rfl⟩ := E.surjective y
      rw [← hc]
      exact (hr _).mpr (h ((hr x).mp hy))
  have he : E a.val ∈ evenPart (modelForm K) R ↔
      a.val ∈ evenPart (integralForm 4) R := by
    rw [← integralComparison_even R]
    exact ⟨fun ⟨x, hx, hx'⟩ => E.injective hx' ▸ hx, fun h => ⟨a.val, h, rfl⟩⟩
  have hrev : reversion (modelForm K) R (E a.val) * E a.val = 1 ↔
      reversion (integralForm 4) R a.val * a.val = 1 := by
    rw [← integralComparison_reversion R, ← map_mul, ← E.map_one]
    exact E.injective.eq_iff
  change (E a.val ∈ evenPart (modelForm K) R ∧
    reversion (modelForm K) R (E a.val) * E a.val = 1 ∧ _ ∧
    Set.MapsTo (conjugate (modelForm K) R (Units.map E.toMonoidHom a)⁻¹) _ _) ↔ _
  rw [he, hrev, hn, ← map_inv, hn]
  rfl

private theorem integralComparison_natural {R S : TestAlgebra K} (f : R ⟶ S)
    (a : ScalarClifford (integralForm 4) R) :
    integralComparison S (coefficientMap (integralForm 4) R (f.hom.restrictScalars ℤ) a) =
      coefficientMap (modelForm K) R f.hom (integralComparison R a) := by
  induction a using TensorProduct.inductionOn with
  | tmul r a =>
    simp only [coefficientMap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      AlgHom.restrictScalars_apply, integralComparison_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

private def modelRepresentation (G : Specs.AffineAlgebraicGroup K)
    (p : ∀ R : TestAlgebra K, SchemePoints G.val R →*
      (ScalarClifford (integralForm 4) R)ˣ) (R : TestAlgebra K) :
    SchemePoints G.val R →* (ScalarClifford (modelForm K) R)ˣ :=
  (Units.map (integralComparison R).toMonoidHom).comp (p R)

private theorem modelRepresentation_valid (G : Specs.AffineAlgebraicGroup K)
    (p : ∀ R : TestAlgebra K, SchemePoints G.val R →*
      (ScalarClifford (integralForm 4) R)ˣ) (hp : SpinPointPresentation G p) :
    IsSpinPointRepresentation (modelForm K) G.val (modelRepresentation G p) := by
  constructor
  · intro R
    let E := Units.mapEquiv (integralComparison R).toMulEquiv
    refine ⟨E.injective.comp (hp.1 R).1, ?_⟩
    change Set.range (E ∘ p R) = _
    rw [Set.range_comp, (hp.1 R).2]
    ext a
    obtain ⟨b, rfl⟩ := E.surjective a
    rw [E.injective.mem_set_image]
    exact (integralComparison_spin R b).symm
  · intro R S f a
    apply Units.ext
    change integralComparison S (p S (mapPoints f a)).val =
      coefficientMap (modelForm K) R f.hom (integralComparison R (p R a).val)
    rw [hp.2 f a]
    exact integralComparison_natural f (p R a).val

private def hyperbolicModelIsometry :
    (Specs.Arithmetic.OddSpinModels.hyperbolicForm (ULift.{u} (Fin 4)) K).IsometryEquiv
      (modelForm K) where
  toLinearEquiv :=
    (LinearEquiv.funCongrLeft K K (Specs.Arithmetic.OddSpinModels.hyperbolicIndices 4).symm).trans
      ((hyperbolicBasis ℤ 4).baseChange K).equivFun.symm
  map_app' x := by
    rw [Albert.SplitSpin.vectorCoordinates]
    change hyperbolicNorm (((hyperbolicBasis ℤ 4).baseChange K).equivFun
      (((hyperbolicBasis ℤ 4).baseChange K).equivFun.symm
        (fun i => x ((Specs.Arithmetic.OddSpinModels.hyperbolicIndices 4).symm i)))) = _
    rw [LinearEquiv.apply_symm_apply, OddSpinModels.hyperbolicForm_apply]
    simp only [hyperbolicNorm, dotProduct, Specs.Arithmetic.OddSpinModels.hyperbolicIndices,
      Equiv.sumCongr_symm, Equiv.sumCongr_apply]
    exact Equiv.sum_comp (Equiv.ulift.symm : Fin 4 ≃ ULift.{u} (Fin 4))
      (fun i => x (Sum.inl i) * x (Sum.inr i))

theorem hyperbolicSpinStructure :
    Specs.Arithmetic.RankEightSpinStructure.HyperbolicSpinStructure.{u} := by
  intro K _ q H p _ hp hq
  obtain ⟨a⟩ := hq
  obtain ⟨G, e, he, hG, _, _, T, d, _, hT, hTm, _⟩ := Albert.SpinWeights.fieldStructure K
  obtain ⟨i, _⟩ := OddSpinInnerDescent.spinIsometryGroupComparison q (modelForm K)
    (a.trans hyperbolicModelIsometry) H G p (modelRepresentation G e) hp
    (modelRepresentation_valid G e he)
  exact split_and_quasiSplit_of_reference i.symm hG T hT hTm


section BinaryPlane

open Polynomial
open Specs.Arithmetic.IsotropicSpinGeneration (HyperbolicPair)

variable {W : Type u} [AddCommGroup W] [Module K W]

private theorem exists_isotropic_binary [IsAlgClosed K] (Q : QuadraticForm K W)
    (b : Basis (Fin 2) K W) : ∃ x : W, x ≠ 0 ∧ Q x = 0 := by
  by_cases h : Q (b 0) = 0
  · exact ⟨b 0, b.ne_zero 0, h⟩
  · let p := C (Q (b 0)) * X ^ 2 + C (Q.polarBilin (b 0) (b 1)) * X + C (Q (b 1))
    have hp : 0 < p.degree :=
      natDegree_pos_iff_degree_pos.mp (by dsimp only [p]; rw [natDegree_quadratic h]; decide)
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_root p hp.ne'
    refine ⟨t • b 0 + b 1, ?_, ?_⟩
    · intro he
      have hc := congrArg (b.coord 1) he
      simp at hc
    · have ht' : Q (b 0) * t ^ 2 + Q.polarBilin (b 0) (b 1) * t + Q (b 1) = 0 := by
        simpa [p, Polynomial.IsRoot] using ht
      rw [(QuadraticMap.map_add Q), QuadraticMap.map_smul, ← QuadraticMap.polarBilin_apply_apply]
      simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
      linear_combination ht'

private def binaryPlaneForm (K : Type u) [Field K] : QuadraticForm K (K × K) :=
  LinearMap.BilinMap.toQuadraticMap
    (LinearMap.mul K K |>.compl₁₂ (LinearMap.fst K K K) (LinearMap.snd K K K))

private theorem binaryPlaneForm_apply (x : K × K) : binaryPlaneForm K x = x.1 * x.2 := rfl

private def pairIsometry (Q : QuadraticForm K W) [Module.Finite K W]
    (hW : finrank K W = 2) (h : HyperbolicPair Q) :
    (binaryPlaneForm K).IsometryEquiv Q := by
  let f := (LinearMap.toSpanSingleton K W h.e).coprod (LinearMap.toSpanSingleton K W h.f)
  have hff : Q.polarBilin h.f h.f = 0 := by
    simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, h.q_f]
  have hee : Q.polarBilin h.e h.e = 0 := by
    simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, h.q_e]
  have hfe : Q.polarBilin h.f h.e = 1 :=
    (QuadraticMap.polar_comm Q _ _).trans h.polar_ef
  have hf_app (x : K × K) : f x = x.1 • h.e + x.2 • h.f := rfl
  have h₁ (x : K × K) : Q.polarBilin h.f (f x) = x.1 := by
    simp only [hf_app, map_add, map_smul, hfe, hff, smul_eq_mul, mul_one, mul_zero, add_zero]
  have h₂ (x : K × K) : Q.polarBilin h.e (f x) = x.2 := by
    simp only [hf_app, map_add, map_smul, hee, h.polar_ef, smul_eq_mul, mul_one, mul_zero, zero_add]
  have hi : Function.Injective f := by
    intro x y eq
    exact Prod.ext ((h₁ x).symm.trans (eq ▸ h₁ y)) ((h₂ x).symm.trans (eq ▸ h₂ y))
  have hs : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hW]) (f := f)).mp hi
  refine ⟨LinearEquiv.ofBijective f ⟨hi, hs⟩, fun x => ?_⟩
  change Q (f x) = _
  rw [hf_app, binaryPlaneForm_apply, (QuadraticMap.map_add Q), QuadraticMap.map_smul,
    QuadraticMap.map_smul, ← QuadraticMap.polarBilin_apply_apply]
  simp only [h.q_e, h.q_f, LinearMap.map_smul, LinearMap.smul_apply,
    h.polar_ef, smul_eq_mul, mul_one, mul_zero, zero_add]

private theorem binaryPlaneSplit [IsAlgClosed K] (Q : QuadraticForm K W)
    (b : Basis (Fin 2) K W) (hQ : LinearMap.ker Q.polarBilin = ⊥) :
    Q.Equivalent (binaryPlaneForm K) := by
  let : Module.Finite K W := Module.Finite.of_basis b
  obtain ⟨e, he, hq⟩ := exists_isotropic_binary Q b
  obtain ⟨h, _⟩ := IsotropicSpinGeneration.hyperbolicPairExistence Q (Or.inl hQ) e he hq
  exact ⟨(pairIsometry Q (by simpa using (Module.finrank_eq_card_basis b)) h).symm⟩

end BinaryPlane


section MarkedForm

open Specs.Arithmetic.OddSpinModels (hyperbolicForm standardVector)
open Specs.Arithmetic.SpinHyperbolicDynamics (HyperbolicPair)
open Specs.SymplecticMatrixStructure (Indices)

private abbrev HyperbolicCoordinates (n : ℕ) (K : Type u) :=
  Indices (ULift.{u} (Fin n)) → K

private abbrev productForm (q₀ : QuadraticForm K (Fin 2 → K)) :=
  (hyperbolicForm (ULift.{u} (Fin 3)) K).prod q₀

private abbrev productBasis (K : Type u) [Field K] :=
  ((Pi.basisFun K (Indices (ULift.{u} (Fin 3)))).prod
    (Pi.basisFun K (Fin 2))).reindex ((Fintype.equivFin _).trans Equiv.ulift.symm :
      (Indices (ULift.{u} (Fin 3)) ⊕ Fin 2) ≃ ULift.{u} (Fin _))

private abbrev productE (i : Fin 3) : HyperbolicCoordinates 3 K × (Fin 2 → K) :=
  (standardVector K (Sum.inl (ULift.up i)), 0)

private abbrev productF (i : Fin 3) : HyperbolicCoordinates 3 K × (Fin 2 → K) :=
  (standardVector K (Sum.inr (ULift.up i)), 0)

private theorem hyperbolic_polar {n : ℕ} (x y : HyperbolicCoordinates n K) :
    (hyperbolicForm (ULift.{u} (Fin n)) K).polarBilin x y =
      ∑ i, (x (Sum.inl i) * y (Sum.inr i) + y (Sum.inl i) * x (Sum.inr i)) := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    OddSpinModels.hyperbolicForm_apply, Pi.add_apply]
  simp_rw [add_mul, mul_add, Finset.sum_add_distrib]
  ring

private theorem product_polar (q₀ : QuadraticForm K (Fin 2 → K))
    (x : HyperbolicCoordinates 3 K) (y : HyperbolicCoordinates 3 K) :
    (productForm q₀).polarBilin (x, 0) (y, 0) =
      (hyperbolicForm _ K).polarBilin x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    QuadraticMap.prod_apply, Prod.fst_add, Prod.snd_add, add_zero, map_zero]

private theorem product_polar_E (q₀ : QuadraticForm K (Fin 2 → K)) (i : Fin 3)
    (x : HyperbolicCoordinates 3 K) :
    (productForm q₀).polarBilin (productE i) (x, 0) = x (Sum.inr (ULift.up i)) := by
  classical
  rw [product_polar, hyperbolic_polar]
  simp [standardVector, Pi.single_apply, ite_mul]

private theorem product_polar_F (q₀ : QuadraticForm K (Fin 2 → K)) (i : Fin 3)
    (x : HyperbolicCoordinates 3 K) :
    (productForm q₀).polarBilin (productF i) (x, 0) = x (Sum.inl (ULift.up i)) := by
  classical
  rw [product_polar, hyperbolic_polar]
  simp [standardVector, Pi.single_apply, mul_ite]

private def productPair (q₀ : QuadraticForm K (Fin 2 → K)) (i : Fin 3) :
    HyperbolicPair (productForm q₀) where
  e := productE i
  f := productF i
  q_e := by simp [productForm, OddSpinModels.hyperbolicForm_standardVector]
  q_f := by simp [productForm, OddSpinModels.hyperbolicForm_standardVector]
  polar_ef := by rw [product_polar_E]; simp [standardVector]

private theorem productPair_orthogonal (q₀ : QuadraticForm K (Fin 2 → K))
    {i j : Fin 3} (hij : i ≠ j) :
    let Q := productForm q₀
    let a := productPair q₀ i
    let b := productPair q₀ j
    Q.polarBilin a.e b.e = 0 ∧ Q.polarBilin a.e b.f = 0 ∧
      Q.polarBilin a.f b.e = 0 ∧ Q.polarBilin a.f b.f = 0 := by
  dsimp only [productPair]
  simp only [productE, productF, product_polar_E, product_polar_F]
  simp [standardVector, hij]

variable {F : Type u} [Field F] [Algebra K F]

private def extendIsometry {V W : Type u} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {I J : Type u} [LinearOrder I] [LinearOrder J]
    {q : QuadraticForm K V} {Q : QuadraticForm K W} (a : q.IsometryEquiv Q)
    (b : Basis I K V) (d : Basis J K W) :
    (coefficientForm F q b).IsometryEquiv (coefficientForm F Q d) where
  toLinearEquiv := LinearEquiv.baseChange K F V W a.toLinearEquiv
  map_app' x := by
    have hh : (coefficientForm F Q d).comp
        (LinearEquiv.baseChange K F V W a.toLinearEquiv).toLinearMap =
        coefficientForm F q b := by
      apply (Albert.CliffordModel.coefficient_form_unique F q b _).mpr
      intro v
      simp [LinearEquiv.baseChange, coefficientForm_tmul, a.map_app]
    exact DFunLike.congr_fun hh x

private abbrev binaryExtension (q₀ : QuadraticForm K (Fin 2 → K)) :=
  coefficientForm F q₀ (Pi.basisFun K (Fin 2))

private def productExtension (q₀ : QuadraticForm K (Fin 2 → K)) :
    (coefficientForm F (productForm q₀) (productBasis K)).IsometryEquiv
      ((hyperbolicForm (ULift.{u} (Fin 3)) F).prod (binaryExtension (F := F) q₀)) := by
  let b := Pi.basisFun K (Indices (ULift.{u} (Fin 3)))
  let l := (TensorProduct.prodRight K F F (HyperbolicCoordinates 3 K) (Fin 2 → K)).trans
    ((b.baseChange F).equivFun.prodCongr (LinearEquiv.refl F _))
  let Q := (hyperbolicForm (ULift.{u} (Fin 3)) F).prod (binaryExtension (F := F) q₀)
  refine ⟨l, fun x => ?_⟩
  have hh : Q.comp l.toLinearMap = coefficientForm F (productForm q₀) (productBasis K) := by
    apply (Albert.CliffordModel.coefficient_form_unique F (productForm q₀) (productBasis K) _).mpr
    intro v
    change Q (l (1 ⊗ₜ[K] v)) = _
    rcases v with ⟨v, w⟩
    simp only [l, LinearEquiv.trans_apply, TensorProduct.prodRight_tmul,
      LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, Q, QuadraticMap.prod_apply,
      coefficientForm_tmul, one_mul, productForm, map_add, binaryExtension]
    congr 1
    simp only [OddSpinModels.hyperbolicForm_apply, Basis.equivFun_apply,
      Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one, b, Pi.basisFun_repr, map_sum, map_mul]
  exact DFunLike.congr_fun hh x

private def productCoordinates :
    (HyperbolicCoordinates 3 K × (K × K)) ≃ₗ[K]
      (Albert.SplitSpinSpecification.PairIndex 4 → K) where
  toFun x := Sum.elim (Fin.cases x.2.1 (fun i => x.1 (Sum.inl (ULift.up i))))
    (Fin.cases x.2.2 (fun i => x.1 (Sum.inr (ULift.up i))))
  invFun x := (Sum.elim (fun i => x (Sum.inl i.down.succ))
    (fun i => x (Sum.inr i.down.succ)), (x (Sum.inl 0), x (Sum.inr 0)))
  left_inv x := by
    refine Prod.ext ?_ rfl
    funext i
    cases i <;> rfl
  right_inv x := by
    funext i
    cases i with
    | inl i => cases i using Fin.cases <;> rfl
    | inr i => cases i using Fin.cases <;> rfl
  map_add' x y := by
    funext i
    cases i with
    | inl i => cases i using Fin.cases <;> rfl
    | inr i => cases i using Fin.cases <;> rfl
  map_smul' c x := by
    funext i
    cases i with
    | inl i => cases i using Fin.cases <;> rfl
    | inr i => cases i using Fin.cases <;> rfl

private def productModelIsometry :
    ((hyperbolicForm (ULift.{u} (Fin 3)) K).prod (binaryPlaneForm K)).IsometryEquiv
      (modelForm K) where
  toLinearEquiv := productCoordinates.trans ((hyperbolicBasis ℤ 4).baseChange K).equivFun.symm
  map_app' x := by
    rw [Albert.SplitSpin.vectorCoordinates]
    change hyperbolicNorm (((hyperbolicBasis ℤ 4).baseChange K).equivFun
      (((hyperbolicBasis ℤ 4).baseChange K).equivFun.symm (productCoordinates x))) = _
    rw [LinearEquiv.apply_symm_apply, QuadraticMap.prod_apply, binaryPlaneForm_apply,
      OddSpinModels.hyperbolicForm_apply, hyperbolicNorm, dotProduct, Fin.sum_univ_succ]
    change x.2.1 * x.2.2 + (∑ i : Fin 3, x.1 (Sum.inl (ULift.up i)) * x.1 (Sum.inr (ULift.up i))) =
      (∑ i : ULift.{u} (Fin 3), x.1 (Sum.inl i) * x.1 (Sum.inr i)) + x.2.1 * x.2.2
    rw [add_comm]
    exact congrArg (· + x.2.1 * x.2.2) (Equiv.sum_comp (Equiv.ulift.symm : Fin 3 ≃ ULift.{u} (Fin 3))
      (fun i => x.1 (Sum.inl i) * x.1 (Sum.inr i)))


open Albert.SplitSpinSpecification (PairIndex)
open private splitE splitF splitBasis from LinearAlgebraicGroups.Albert.SplitSpin

private theorem productExtension_vector (q₀ : QuadraticForm K (Fin 2 → K))
    (j : Indices (ULift.{u} (Fin 3))) :
    productExtension (F := F) q₀ (1 ⊗ₜ[K] (standardVector K j, 0)) =
      (standardVector F j, 0) := by
  change ((TensorProduct.prodRight K F F _ _).trans
    (((Pi.basisFun K (Indices (ULift.{u} (Fin 3)))).baseChange F).equivFun.prodCongr
      (LinearEquiv.refl F _))) (1 ⊗ₜ[K] (standardVector K j, 0)) = _
  rw [LinearEquiv.trans_apply, TensorProduct.prodRight_tmul, LinearEquiv.prodCongr_apply]
  congr 1
  · change ((Pi.basisFun K (Indices (ULift.{u} (Fin 3)))).baseChange F).equivFun
      (1 ⊗ₜ[K] Pi.single j 1) = _
    rw [← Pi.basisFun_apply K (Indices (ULift.{u} (Fin 3))) j, ← Basis.baseChange_apply]
    funext i
    rw [Basis.equivFun_self]
    simp [standardVector, Pi.single_apply, eq_comm]
  · exact TensorProduct.tmul_zero _ _

private theorem productCoordinate_vector (j : PairIndex 3) :
    productCoordinates (K := K) (standardVector K (Sum.map ULift.up ULift.up j), 0) =
      Pi.single (Sum.map Fin.succ Fin.succ j) 1 := by
  classical
  funext k
  rcases k with k | k <;> cases k using Fin.cases <;> rcases j with j | j <;>
    simp [productCoordinates, standardVector, Pi.single_apply, eq_comm]

private theorem productModelIsometry_vector (j : PairIndex 3) :
    productModelIsometry (K := K) (standardVector K (Sum.map ULift.up ULift.up j), 0) =
      splitBasis 4 K (toLex (Sum.map Fin.succ Fin.succ j)) := by
  change ((hyperbolicBasis ℤ 4).baseChange K).equivFun.symm
      (productCoordinates (standardVector K (Sum.map ULift.up ULift.up j), 0)) = _
  rw [productCoordinate_vector]
  apply ((hyperbolicBasis ℤ 4).baseChange K).equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  let k : Lex (PairIndex 4) := toLex (Sum.map Fin.succ Fin.succ j)
  change (Pi.single k (1 : K) : Lex (PairIndex 4) → K) =
    ((hyperbolicBasis ℤ 4).baseChange K).equivFun (((hyperbolicBasis ℤ 4).baseChange K) k)
  funext i
  rw [Basis.equivFun_self]
  simp only [Pi.single_apply, eq_comm]

private theorem isometry_polar {V W : Type u} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {q : QuadraticForm K V} {Q : QuadraticForm K W}
    (a : q.IsometryEquiv Q) (x y : V) :
    Q.polarBilin (a x) (a y) = q.polarBilin x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, a.map_app]

private def pullbackPair {V W : Type u} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {q : QuadraticForm K V} {Q : QuadraticForm K W}
    (a : q.IsometryEquiv Q) (h : HyperbolicPair Q) : HyperbolicPair q where
  e := a.symm h.e
  f := a.symm h.f
  q_e := (a.symm.map_app h.e).trans h.q_e
  q_f := (a.symm.map_app h.f).trans h.q_f
  polar_ef := (isometry_polar a.symm h.e h.f).trans h.polar_ef

private theorem binaryModelIsometry [IsAlgClosed F]
    (q : QuadraticForm K (Fin 8 → K)) (q₀ : QuadraticForm K (Fin 2 → K))
    (b : Basis (ULift.{u} (Fin 8)) K (Fin 8 → K))
    (a : q.IsometryEquiv (productForm q₀)) (h₀ : LinearMap.ker q₀.polarBilin = ⊥) :
    ∃ f : (coefficientForm F q b).IsometryEquiv (modelForm F),
      ∀ i : Fin 3,
        f (1 ⊗ₜ[K] (pullbackPair a (productPair q₀ i)).e) = splitE i.succ ∧
        f (1 ⊗ₜ[K] (pullbackPair a (productPair q₀ i)).f) = splitF i.succ := by
  let b₀ := Pi.basisFun K (Fin 2)
  have hreg : LinearMap.ker (binaryExtension (F := F) q₀).polarBilin = ⊥ :=
    (SpinScalarExtension.polarRadicalExtension (F := F) q₀ b₀).2.1 h₀
  obtain ⟨e⟩ := binaryPlaneSplit _ (b₀.baseChange F) hreg
  let f₁ := extendIsometry (F := F) a b (productBasis K)
  let f₂ := productExtension (F := F) q₀
  let f₃ := (QuadraticMap.IsometryEquiv.refl (hyperbolicForm (ULift.{u} (Fin 3)) F)).prod e
  let f := f₁.trans (f₂.trans (f₃.trans productModelIsometry))
  refine ⟨f, fun i => ?_⟩
  have h (j : PairIndex 3) :
      f (1 ⊗ₜ[K] a.symm (standardVector K (Sum.map ULift.up ULift.up j), 0)) =
        splitBasis 4 F (toLex (Sum.map Fin.succ Fin.succ j)) := by
    change productModelIsometry (f₃ (f₂ (f₁ (1 ⊗ₜ[K]
      a.symm (standardVector K (Sum.map ULift.up ULift.up j), 0))))) = _
    have h₁ (v : HyperbolicCoordinates 3 K × (Fin 2 → K)) :
        f₁ (1 ⊗ₜ[K] a.symm v) = 1 ⊗ₜ[K] v := by
      change LinearEquiv.baseChange K F _ _ a.toLinearEquiv (1 ⊗ₜ[K] a.symm v) = _
      simp [LinearEquiv.baseChange, QuadraticMap.IsometryEquiv.apply_symm_apply]
    rw [h₁, show f₂ _ = (standardVector F (Sum.map ULift.up ULift.up j), 0) from
      productExtension_vector q₀ _]
    have hm (x : HyperbolicCoordinates 3 F) : f₃ (x, 0) = (x, 0) := by
      change (x, e 0) = (x, 0)
      rw [map_zero]
    rw [hm, productModelIsometry_vector]
  exact ⟨h (Sum.inl i), h (Sum.inr i)⟩

end MarkedForm


section Cocharacter

open Specs.CharacterDescent (Cocharacter)
open _root_.LinearAlgebraicGroups.CocharacterDynamics
  (unitPoint cocharacterPoint mapPoints_cocharacterPoint mapPoints_unitPoint)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.Arithmetic.SpinHyperbolicDynamics
  (HyperbolicPair diagonal perpendicularOver vectorOver)
open private unitPointHom unitPointHom_apply unitEquiv unitEquiv_unitPoint
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private diagonal_commutes_perpendicular polar_over
  from LinearAlgebraicGroups.Arithmetic.SpinHyperbolicDynamics

local notation "𝔾ₘ" k => specGroup (groupAlgebra k IntegerCharacters)

private def unitCocharacterHom {G : Specs.GroupScheme K} (c : Cocharacter G) (R : TestAlgebra K) :
    Rˣ →* GroupPoints G R :=
  (((groupPointsFunctor K).map c).app R).hom.comp (unitPointHom R)

private theorem unitCocharacterHom_apply {G : Specs.GroupScheme K} (c : Cocharacter G)
    (R : TestAlgebra K) (s : Rˣ) : unitCocharacterHom c R s = cocharacterPoint c R s := by
  change (((groupPointsFunctor K).map c).app R).hom (unitPointHom R s) = _
  rw [unitPointHom_apply]
  rfl

private theorem cocharacterOfCompatiblePoints {G : Specs.GroupScheme K}
    (g : ∀ R : TestAlgebra K, Rˣ →* GroupPoints G R)
    (hg : ∀ {R S : TestAlgebra K} (f : R ⟶ S) (s : Rˣ),
      g S (Units.map f.hom.toMonoidHom s) = mapPoints f (g R s)) :
    ∃ c : Cocharacter G, ∀ R s, cocharacterPoint c R s = g R s := by
  let φ : (groupPointsFunctor K).obj (𝔾ₘ K) ⟶ (groupPointsFunctor K).obj G :=
    { app := fun R => GrpCat.ofHom ((g R).comp (unitEquiv R).toMonoidHom)
      naturality := by
        intro R S f
        apply GrpCat.ext
        intro x
        obtain ⟨s, rfl⟩ := (unitEquiv R).symm.surjective x
        change g S (unitEquiv S (mapPoints f ((unitEquiv R).symm s))) =
          mapPoints f (g R (unitEquiv R ((unitEquiv R).symm s)))
        rw [show (unitEquiv R).symm s = unitPoint R s from unitPointHom_apply R s,
          mapPoints_unitPoint, unitEquiv_unitPoint, unitEquiv_unitPoint]
        exact hg f s }
  have hAffine : IsAffine (𝔾ₘ K).X.left := inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (MonoidAlgebra K IntegerCharacters))))
  obtain ⟨c, hc⟩ := (groupHomComparison K _ G hAffine).2 φ
  refine ⟨c, fun R s => ?_⟩
  change (((groupPointsFunctor K).map c).app R) (unitPoint R s) = _
  rw [show (groupPointsFunctor K).map c = φ from hc]
  change g R (unitEquiv R (unitPoint R s)) = _
  rw [unitEquiv_unitPoint]

private def multiplyHom {A B : Type u} [Monoid A] [Monoid B] (a b : A →* B)
    (comm : ∀ x y, Commute (b x) (a y)) : A →* B where
  toFun x := a x * b x
  map_one' := by rw [map_one, map_one, one_mul]
  map_mul' x y := by
    rw [map_mul, map_mul, (comm x y).mul_mul_mul_comm]

private abbrev planePower (i : Fin 3) : ℕ := 3 - i.val

private theorem orthogonal_diagonals_commute {V : Type u} [AddCommGroup V] [Module K V]
    (q : QuadraticForm K V) {I : Type u} [LinearOrder I] (b : Basis I K V)
    (a h : HyperbolicPair q)
    (ho : q.polarBilin a.e h.e = 0 ∧ q.polarBilin a.e h.f = 0 ∧
      q.polarBilin a.f h.e = 0 ∧ q.polarBilin a.f h.f = 0)
    (R : TestAlgebra K) (s t : Rˣ) :
    Commute (diagonal q a R s) (diagonal q h R t) := by
  have he : vectorOver R h.e ∈ perpendicularOver q a b R :=
    ⟨LinearMap.mem_ker.mpr (by rw [polar_over, ho.1, map_zero]),
      LinearMap.mem_ker.mpr (by rw [polar_over, ho.2.2.1, map_zero])⟩
  have hf : vectorOver R h.f ∈ perpendicularOver q a b R :=
    ⟨LinearMap.mem_ker.mpr (by rw [polar_over, ho.2.1, map_zero]),
      LinearMap.mem_ker.mpr (by rw [polar_over, ho.2.2.2, map_zero])⟩
  have ce := diagonal_commutes_perpendicular q a b R s ⟨_, he⟩
  have cf := diagonal_commutes_perpendicular q a b R s ⟨_, hf⟩
  exact ((ce.mul_right cf).smul_right (t : R)).add_right
    ((cf.mul_right ce).smul_right (↑t⁻¹ : R))

private theorem cocharacterOfThreePlanes {V : Type u} [AddCommGroup V] [Module K V]
    (q : QuadraticForm K V) {I : Type u} [LinearOrder I] (b : Basis I K V)
    (h : Fin 3 → HyperbolicPair q)
    (orth : ∀ i j : Fin 3, i ≠ j →
      q.polarBilin (h i).e (h j).e = 0 ∧ q.polarBilin (h i).e (h j).f = 0 ∧
      q.polarBilin (h i).f (h j).e = 0 ∧ q.polarBilin (h i).f (h j).f = 0)
    {G : Specs.GroupScheme K}
    (p : ∀ R : TestAlgebra K, SchemePoints G R →* (ScalarClifford q R)ˣ)
    (hp : IsSpinPointRepresentation q G p) :
    ∃ c : Cocharacter G, ∀ (R : TestAlgebra K) (s : Rˣ),
      (p R (cocharacterPoint c R s)).val =
        diagonal q (h 0) R (s ^ planePower 0) * diagonal q (h 1) R (s ^ planePower 1) *
          diagonal q (h 2) R (s ^ planePower 2) := by
  classical
  let ex (i : Fin 3) := SpinHyperbolicDynamics.cocharacterExists q b (h i) p hp
  let c (i : Fin 3) := (ex i).choose
  have hc (i : Fin 3) (R : TestAlgebra K) (s : Rˣ) :
      (p R (cocharacterPoint (c i) R s)).val = diagonal q (h i) R s :=
    (ex i).choose_spec R s
  let m (R : TestAlgebra K) (i : Fin 3) : Rˣ →* GroupPoints G R :=
    (unitCocharacterHom (c i) R).comp (powMonoidHom (planePower i))
  have hm (R : TestAlgebra K) (i : Fin 3) (s : Rˣ) :
      m R i s = cocharacterPoint (c i) R (s ^ planePower i) :=
    unitCocharacterHom_apply (c i) R (s ^ planePower i)
  have comm (R : TestAlgebra K) (i j : Fin 3) (hne : i ≠ j) (s t : Rˣ) :
      Commute (m R i s) (m R j t) := by
    apply (hp.1 R).1
    apply Units.ext
    simp only [map_mul, Units.val_mul, hm]
    rw [hc i, hc j]
    exact (orthogonal_diagonals_commute q b _ _ (orth i j hne) R _ _).eq
  let m01 (R : TestAlgebra K) :=
    multiplyHom (m R 0) (m R 1) (comm R 1 0 (by decide))
  let g (R : TestAlgebra K) :=
    multiplyHom (m01 R) (m R 2) (fun s t =>
      (comm R 2 0 (by decide) s t).mul_right (comm R 2 1 (by decide) s t))
  have hnat {R S : TestAlgebra K} (f : R ⟶ S) (s : Rˣ) :
      g S (Units.map f.hom.toMonoidHom s) = mapPoints f (g R s) := by
    change m S 0 _ * m S 1 _ * m S 2 _ =
      (((groupPointsFunctor K).obj G).map f).hom (m R 0 s * m R 1 s * m R 2 s)
    simp only [map_mul, hm, ← map_pow, ← mapPoints_cocharacterPoint]
    rfl
  obtain ⟨δ, hδ⟩ := cocharacterOfCompatiblePoints g hnat
  refine ⟨δ, fun R s => ?_⟩
  rw [hδ]
  change (p R (m R 0 s * m R 1 s * m R 2 s)).val = _
  simp only [map_mul, Units.val_mul, hm, hc]

end Cocharacter


section MarkedTorus

open Specs.SpinWeights (DiagonalPoints diagonalNorm scalar scales vectorPullback epsilon coordinate
  evaluate rootCharacters CharacterExponents evenSumLattice latticePairing
  TorusPointPresentation)
open Albert.SplitSpinSpecification (HasActionMatrix PairIndex middle)
open Specs.CharacterDescent (Cocharacter Character)
open Specs.CharacterPairing (absoluteRoots pairing characterValue)
open Specs.BorelsAndChambers (IsRegular)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open _root_.LinearAlgebraicGroups.CocharacterDynamics
  (cocharacterPoint unitPoint laurentAlgebra laurentParameter)
open private creation contraction contraction_creation occupation eBasis diagonalUnit diagonalLift
  diagonalUnit_wedge clifford_ext_wedges diagonalUnit_action middle_diagonal vectorEigenvalue
  latticePairing_vectorPullback coordinate_dot vectorRoots_signs dot_signed
  from LinearAlgebraicGroups.Albert.SpinWeights
open private action_matrix_unique from LinearAlgebraicGroups.Albert.SplitSpin
open private subgroupInclusionFactors unitPointHom unitPointHom_apply unitEquiv
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private laurentParameter_zpow monomial_coeff
  from LinearAlgebraicGroups.Reductive.CocharacterLieWeights

private def onePlaneParameter {R : Type u} [CommRing R] (i : Fin 4) (s : Rˣ) :
    DiagonalPoints R :=
  ⟨(fun j => if j = i then s ^ 2 else 1, s⁻¹), by
    change (s⁻¹) ^ 2 * (∏ j : Fin 4, if j = i then s ^ 2 else 1) = 1
    simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true, inv_pow, inv_mul_cancel]⟩

private def threePlaneParameter {R : Type u} [CommRing R] (s : Rˣ) : DiagonalPoints R :=
  onePlaneParameter (1 : Fin 4) (s ^ planePower 0) *
    onePlaneParameter (2 : Fin 4) (s ^ planePower 1) *
    onePlaneParameter (3 : Fin 4) (s ^ planePower 2)

private def vectorExponent (i : Fin 4) : ℤ :=
  if i = 0 then 0 else if i = 1 then 6 else if i = 2 then 4 else 2

private theorem threePlaneParameter_scales {R : Type u} [CommRing R] (s : Rˣ) (i : Fin 4) :
    scales (threePlaneParameter s) i = s ^ vectorExponent i := by
  change (if i = 1 then (s ^ planePower 0) ^ 2 else 1) *
      (if i = 2 then (s ^ planePower 1) ^ 2 else 1) *
      (if i = 3 then (s ^ planePower 2) ^ 2 else 1) = _
  fin_cases i <;> norm_num [vectorExponent, planePower, ← pow_mul]

private theorem onePlaneClifford {R : Type u} [CommRing R] [Algebra ℤ R]
    (i : Fin 4) (s : Rˣ) :
    (s : R) • (creation i * contraction i) + (↑s⁻¹ : R) • (contraction i * creation i) =
      (diagonalUnit (onePlaneParameter i s)).val.val := by
  apply clifford_ext_wedges
  intro I
  rw [diagonalUnit_wedge, contraction_creation]
  simp only [map_add, map_smul, map_sub, map_one, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.one_apply, occupation]
  have hs : s⁻¹ * s ^ 2 = s := by group
  change (s : R) • ((if i ∈ I then (1 : R) else 0) • eBasis R I) +
      (↑s⁻¹ : R) • (eBasis R I - (if i ∈ I then (1 : R) else 0) • eBasis R I) =
    (↑(s⁻¹ * ∏ j ∈ I, if j = i then s ^ 2 else 1) : R) • eBasis R I
  by_cases h : i ∈ I <;> simp only [Finset.prod_ite_eq', h, ite_true, ite_false, hs, mul_one,
    one_smul, zero_smul, sub_self, smul_zero, add_zero, sub_zero, zero_add]

private theorem threePlaneCliffordProduct {R : Type u} [CommRing R] [Algebra ℤ R] (s : Rˣ) :
    (diagonalUnit (onePlaneParameter 1 (s ^ planePower 0))).val.val *
        (diagonalUnit (onePlaneParameter 2 (s ^ planePower 1))).val.val *
        (diagonalUnit (onePlaneParameter 3 (s ^ planePower 2))).val.val =
      (diagonalUnit (threePlaneParameter s)).val.val := by
  let D := diagonalLift (R := R)
  let t₀ := onePlaneParameter 1 (s ^ planePower 0)
  let t₁ := onePlaneParameter 2 (s ^ planePower 1)
  let t₂ := onePlaneParameter 3 (s ^ planePower 2)
  change _ = (D ((t₀ * t₁) * t₂)).val.val
  rw [D.map_mul (t₀ * t₁) t₂, D.map_mul t₀ t₁]
  rfl

private theorem pairing_of_values {T : Specs.GroupScheme K} (χ : Character T)
    (c : Cocharacter T) (n : ℤ)
    (h : ∀ (R : TestAlgebra K) (s : Rˣ),
      characterValue χ R (cocharacterPoint c R s) = ((s ^ n : Rˣ) : R)) :
    pairing T χ c = n := by
  let R := laurentAlgebra (CommAlgCat.of K K)
  let s := laurentParameter (CommAlgCat.of K K)
  have hval : (↑(s ^ pairing T χ c) : R) = (↑(s ^ n) : R) := by
    rw [← (RootData.CharacterPairing.characterPairingComposition T χ c).2 R s,
      h]
  rw [laurentParameter_zpow, laurentParameter_zpow] at hval
  by_contra hne
  have hc := congrArg (fun f : LaurentPolynomial K => (f * LaurentPolynomial.C 1).coeff n) hval
  rw [monomial_coeff, monomial_coeff] at hc
  simp [Ne.symm hne] at hc

private theorem regular_of_marked_scales {G : Specs.GroupScheme K} (T : ClosedSubgroup G)
    [IsCommMonObj T.group.X] (c : Cocharacter T.group)
    (d : ∀ R : TestAlgebra K, Points T.group.X R ≃* DiagonalPoints R)
    (C : Additive (Character T.group) ≃ₗ[ℤ] CharacterExponents)
    (Y : Additive (Cocharacter T.group) ≃ₗ[ℤ] evenSumLattice)
    (hval : ∀ (R : TestAlgebra K) (t : Points T.group.X R) (χ : Character T.group),
      characterValue χ R t = ((Additive.toMul (evaluate (d R t) (C (Additive.ofMul χ))) : Rˣ) : R))
    (hpair : ∀ (χ : Character T.group) (ψ : Cocharacter T.group),
      pairing T.group χ ψ = latticePairing (C (Additive.ofMul χ)) (Y (Additive.ofMul ψ)))
    (hroots : Set.MapsTo (fun χ : Character T.group => C (Additive.ofMul χ))
      (absoluteRoots T) rootCharacters)
    (hscales : ∀ (R : TestAlgebra K) (s : Rˣ) (i : Fin 4),
      scales (d R (cocharacterPoint c R s)) i = s ^ vectorExponent i) :
    IsRegular T c := by
  let y := Y (Additive.ofMul c)
  have hy (i : Fin 4) : y.val i = vectorExponent i := by
    let χ := Additive.toMul (C.symm (epsilon i))
    have hχ : C (Additive.ofMul χ) = epsilon i := C.apply_symm_apply _
    have hp : pairing T.group χ c = vectorExponent i := by
      apply pairing_of_values
      intro R s
      rw [hval, hχ]
      rw [((Albert.SpinWeights.weightEvaluation R (d R (cocharacterPoint c R s))).1 i).1, hscales]
    rw [hpair, hχ, epsilon, latticePairing_vectorPullback, coordinate_dot] at hp
    exact hp
  intro α
  obtain ⟨r, hr, he⟩ := hroots α.property
  change vectorPullback r = C (Additive.ofMul α.val) at he
  rw [hpair, ← he, latticePairing_vectorPullback]
  obtain ⟨i, j, hij, a, b, ha, hb, rfl⟩ := (vectorRoots_signs r).mp hr
  rw [dot_signed, hy i, hy j]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    fin_cases i <;> fin_cases j <;> first | contradiction | norm_num [vectorExponent]

private theorem factor_marked_cocharacter
    (G : Specs.AffineAlgebraicGroup K)
    (e : ∀ R : TestAlgebra K, SchemePoints G.val R →*
      (Albert.SplitSpinSpecification.ScalarClifford 4 R)ˣ)
    (T : ClosedSubgroup G.val)
    (d : ∀ R : TestAlgebra K, Points T.group.X R ≃* DiagonalPoints R)
    (ht : TorusPointPresentation e T d) (c : Cocharacter G.val)
    (hc : ∀ (R : TestAlgebra K) (s : Rˣ),
      e R (cocharacterPoint c R s) = (diagonalUnit (threePlaneParameter s)).val) :
    ∃ ψ : Cocharacter T.group, ψ ≫ T.inclusion = c ∧
      ∀ (R : TestAlgebra K) (s : Rˣ) (i : Fin 4),
        scales (d R (cocharacterPoint ψ R s)) i = s ^ vectorExponent i := by
  have ha : IsAffine (specGroup (groupAlgebra K IntegerCharacters)).X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (MonoidAlgebra K IntegerCharacters))))
  obtain ⟨ψ, hψ⟩ := subgroupInclusionFactors ha T c (by
    intro R x
    obtain ⟨s, rfl⟩ := (unitEquiv R).symm.surjective x
    rw [show (unitEquiv R).symm s = unitPoint R s from unitPointHom_apply R s]
    exact (ht.2.1 R _).mpr ⟨threePlaneParameter s, by
      change HasActionMatrix 4 (e R (cocharacterPoint c R s)) _
      rw [hc]
      exact diagonalUnit_action _⟩)
  refine ⟨ψ, hψ, fun R s i => ?_⟩
  obtain ⟨E, _, hE⟩ := ht.2.2 R
  have hg : (cocharacterPoint ψ R s : GroupPoints T.group R) ≫ T.inclusion.hom.hom =
      cocharacterPoint c R s := by
    change unitPoint R s ≫ ψ.hom.hom ≫ T.inclusion.hom.hom = unitPoint R s ≫ c.hom.hom
    rw [← Category.assoc, ← hψ]; rfl
  have hM := (hE (cocharacterPoint ψ R s)).1
  rw [hg, hc] at hM
  have hm := action_matrix_unique hM (diagonalUnit_action (threePlaneParameter s))
  rw [middle_diagonal, middle_diagonal] at hm
  have hv := congrArg (fun M : Matrix (PairIndex 4) (PairIndex 4) R => M (Sum.inl i) (Sum.inl i)) hm
  have he : scales (d R (cocharacterPoint ψ R s)) i = scales (threePlaneParameter s) i := by
    apply Units.ext
    simp only [Matrix.diagonal_apply_eq, vectorEigenvalue, Sum.elim_inl] at hv
    exact hv
  exact he.trans (threePlaneParameter_scales s i)

end MarkedTorus


section GeometricComparison

open Albert.SplitSpinSpecification (PairIndex)
open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.GeometricRadicals (GeometricGroup)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition cocharacterPoint unitPoint)
open Specs.Arithmetic.SpinHyperbolicDynamics (HyperbolicPair diagonal vectorOver)
open Specs.Arithmetic.SpinScalarExtension (restricted vectorComparison IsMultiplicativeComparison)
open private splitBasis splitE splitF from LinearAlgebraicGroups.Albert.SplitSpin
open private creation contraction diagonalUnit from LinearAlgebraicGroups.Albert.SpinWeights
open private scalarIsometryClifford scalarIsometryClifford_vectors
  from LinearAlgebraicGroups.Arithmetic.OddSpinInnerDescent
open private cocharacterPoint_baseChange
  from LinearAlgebraicGroups.Arithmetic.SpinScalarExtension
open private borel_of_same limits_subgroups_extend
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private map_parabolic_of_comp regular_isBorel centralizer_of_regular
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private smooth_baseChange_iff connected_baseChange_iff
  from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private connected_of_geometricallyConnected
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private geometricallyConnected_of_connected
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry

local notation "𝔾ₘ" k => specGroup (groupAlgebra k IntegerCharacters)

private theorem cocharacterPoint_comp {G J : Specs.GroupScheme K} (c : Cocharacter G)
    (i : G ⟶ J) (R : TestAlgebra K) (s : Rˣ) :
    cocharacterPoint (c ≫ i) R s = cocharacterPoint c R s ≫ i.hom.hom :=
  (Category.assoc (unitPoint R s) c.hom.hom i.hom.hom).symm

private theorem mark_in_integral_comparison (R : TestAlgebra K) (j : PairIndex 4) :
    integralComparison R (vectors (integralForm 4) R (splitBasis 4 R (toLex j))) =
      vectors (modelForm K) R (1 ⊗ₜ[K] splitBasis 4 K (toLex j)) := by
  rw [integralComparison_vectors]
  congr 1
  change integralVectorComparison R (((hyperbolicBasis ℤ 4).baseChange R) (toLex j)) =
    1 ⊗ₜ[K] ((hyperbolicBasis ℤ 4).baseChange K) (toLex j)
  rw [Basis.baseChange_apply, Basis.baseChange_apply]
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul ℤ K R _ _

variable {F : Type u} [Field F] [Algebra K F]

private theorem compared_diagonal {V : Type u} [AddCommGroup V] [Module K V]
    (q : QuadraticForm K V) {I : Type u} [LinearOrder I] (b : Basis I K V)
    (h : HyperbolicPair q) (a : (coefficientForm F q b).IsometryEquiv (modelForm F))
    (j : Fin 4)
    (he : a (1 ⊗ₜ[K] h.e) = splitE j) (hf : a (1 ⊗ₜ[K] h.f) = splitF j)
    (R : TestAlgebra F)
    (A : ScalarClifford q (restricted K R) ≃ₐ[R] ScalarClifford (coefficientForm F q b) R)
    (hv : ∀ x : R ⊗[F] (F ⊗[K] V),
      A (vectors q (restricted K R) (vectorComparison R x)) =
        vectors (coefficientForm F q b) R x)
    (s : Rˣ) :
    scalarIsometryClifford a R (A (diagonal q h (restricted K R) s)) =
      integralComparison R (diagonalUnit (onePlaneParameter j s)).val.val := by
  have hvec (x : V) :
      scalarIsometryClifford a R (A (vectors q (restricted K R) (1 ⊗ₜ[K] x))) =
        vectors (modelForm F) R (1 ⊗ₜ[F] a (1 ⊗ₜ[K] x)) := by
    have hv' : A (vectors q (restricted K R) (1 ⊗ₜ[K] x)) =
        vectors (coefficientForm F q b) R (1 ⊗ₜ[F] (1 ⊗ₜ[K] x)) := by
      simpa [vectorComparison] using hv (1 ⊗ₜ[F] (1 ⊗ₜ[K] x))
    rw [hv', scalarIsometryClifford_vectors]
    simp [LinearEquiv.baseChange]

  rw [← onePlaneClifford]
  simp only [diagonal, vectorOver, map_add, map_mul, map_smul, hvec, he, hf]
  rw [show integralComparison R (creation j) = vectors (modelForm F) R (1 ⊗ₜ[F] splitE j)
      from mark_in_integral_comparison R (Sum.inl j),
    show integralComparison R (contraction j) = vectors (modelForm F) R (1 ⊗ₜ[F] splitF j)
      from mark_in_integral_comparison R (Sum.inr j)]

private theorem transported_limit_borel {H G : Specs.AffineAlgebraicGroup K}
    [IsAlgClosed K] (e : H.val ≅ G.val)
    {c : Cocharacter H.val} {d : Cocharacter G.val} (he : c ≫ e.hom = d)
    (D : LimitDecomposition c) (E : LimitDecomposition d) (hE : IsBorel E.parabolic) :
    IsBorel D.parabolic := by
  obtain ⟨f, hf⟩ := map_parabolic_of_comp H.property.1 e.hom he D E
  have he' : d ≫ e.inv = c := by rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]
  obtain ⟨g, hg⟩ := map_parabolic_of_comp G.property.1 e.inv he' E D
  apply borel_of_same (H := H) (borel_transport e.symm hE)
  refine ⟨⟨g, hg⟩, ⟨f, ?_⟩⟩
  change f ≫ E.parabolic.inclusion ≫ e.inv = D.parabolic.inclusion
  rw [← Category.assoc, hf, Category.assoc, e.hom_inv_id, Category.comp_id]

private theorem reductive_of_geometric_reference (H : Specs.AffineAlgebraicGroup K)
    (G : Specs.AffineAlgebraicGroup (AlgebraicClosure K))
    (e : (GeometricGroup H).val ≅ G.val) (hG : IsReductive G) : IsReductive H := by
  have hg := reductive_of_groupIso e.symm hG
  have hs : Smooth H.val.X.hom :=
    (smooth_baseChange_iff (K := AlgebraicClosure K) H.val.X).mp hg.1
  have hconn : ConnectedSpace H.val.X.left :=
    (connected_baseChange_iff (K := AlgebraicClosure K) H).mp
      (connected_of_geometricallyConnected hg.2.1)
  let := hconn
  exact (Reductive.RadicalBaseChange.reductiveFieldExtension (K := AlgebraicClosure K) H hs
    (geometricallyConnected_of_connected H)).mp hg


open private same_subgroup_of_same_affine_points
  from LinearAlgebraicGroups.RootData.RankOneFlag

theorem binaryKernelSpinStructure :
    Specs.Arithmetic.RankEightSpinStructure.BinaryKernelSpinStructure.{u} := by
  intro K _ q H p _ hp q₀ h₀ _ hq
  classical
  obtain ⟨a⟩ := hq
  let F := AlgebraicClosure K
  let b := (Pi.basisFun K (Fin 8)).reindex (Equiv.ulift.symm : Fin 8 ≃ ULift.{u} (Fin 8))
  let h (i : Fin 3) := pullbackPair a (productPair q₀ i)
  have horth (i j : Fin 3) (hij : i ≠ j) :
      q.polarBilin (h i).e (h j).e = 0 ∧ q.polarBilin (h i).e (h j).f = 0 ∧
      q.polarBilin (h i).f (h j).e = 0 ∧ q.polarBilin (h i).f (h j).f = 0 := by
    simpa only [h, pullbackPair, isometry_polar a.symm] using productPair_orthogonal q₀ hij
  obtain ⟨c, hc⟩ := cocharacterOfThreePlanes q b h horth p hp
  obtain ⟨D⟩ := CocharacterDynamics.existsLimitDecomposition H c
  obtain ⟨m, hm, hP, _, _, hPE, _, _, _⟩ :=
    CocharacterDynamics.limitSubgroupsBaseChange (K := F) H c D
  obtain ⟨aF, haF⟩ := binaryModelIsometry (F := F) q q₀ b a h₀
  obtain ⟨A, pF, hAv, _, _, _, _, hpFval, hpF, _⟩ :=
    SpinScalarExtension.spinRepresentationExtension (F := F) q b H p hp
  obtain ⟨G, e, he, hG, _, _, T, d, ht, hT, hTm, _, hCoord⟩ :=
    Albert.SpinWeights.fieldStructure F
  obtain ⟨hComm, hCoord⟩ := hCoord
  let := hComm
  obtain ⟨C, Y, _, hval, hpair, hroots, _⟩ := hCoord
  obtain ⟨j, hj⟩ := OddSpinInnerDescent.spinIsometryGroupComparison
    (coefficientForm F q b) (modelForm F) aF (GeometricGroup H) G pF
    (modelRepresentation G e) hpF (modelRepresentation_valid G e he)
  let cF : Cocharacter (GeometricGroup H).val := m.hom ≫ (groupBaseChange K F).map c
  let cG : Cocharacter G.val := cF ≫ j.hom
  have hcG (R : TestAlgebra F) (s : Rˣ) :
      e R (cocharacterPoint cG R s) = (diagonalUnit (threePlaneParameter s)).val := by
    apply Units.ext
    apply (integralComparison R).injective
    rw [show cocharacterPoint cG R s = cocharacterPoint cF R s ≫ j.hom.hom.hom
      from cocharacterPoint_comp cF j.hom R s]
    have hcompare := congrArg Units.val (hj R (cocharacterPoint cF R s))
    change integralComparison R (e R (cocharacterPoint cF R s ≫ j.hom.hom.hom)).val =
      scalarIsometryClifford aF R (pF R (cocharacterPoint cF R s)).val at hcompare
    rw [hcompare, hpFval,
      show baseChangePoint K F H.val.X R (cocharacterPoint cF R s) =
        cocharacterPoint c (restricted K R) s from cocharacterPoint_baseChange c m hm R s]
    change scalarIsometryClifford aF R
        (A R (p (restricted K R) (cocharacterPoint c (restricted K R) s)).val) = _
    rw [hc]
    simp only [map_mul]
    rw [compared_diagonal q b (h 0) aF 1 (haF 0).1 (haF 0).2 R (A R) (hAv R),
      compared_diagonal q b (h 1) aF 2 (haF 1).1 (haF 1).2 R (A R) (hAv R),
      compared_diagonal q b (h 2) aF 3 (haF 2).1 (haF 2).2 R (A R) (hAv R),
      ← map_mul, ← map_mul, threePlaneCliffordProduct]
  obtain ⟨ψ, hψ, hscales⟩ := factor_marked_cocharacter G e T d ht cG hcG
  have hreg := regular_of_marked_scales T ψ d C Y hval hpair hroots.1 hscales
  obtain ⟨E⟩ := CocharacterDynamics.existsLimitDecomposition G (ψ ≫ T.inclusion)
  have hB := regular_isBorel G hG T hT hTm ψ hreg E
    (centralizer_of_regular G hG T hT hTm ψ hreg E)
  obtain ⟨DF⟩ := CocharacterDynamics.existsLimitDecomposition (GeometricGroup H) cF
  have hBF := transported_limit_borel j hψ.symm DF E hB
  refine ⟨reductive_of_geometric_reference H G j hG, D.parabolic, hP,
    borel_of_same (H := GeometricGroup H) hBF
      (same_subgroup_of_same_affine_points (G := GeometricGroup H) DF.parabolic_points hPE)⟩

end GeometricComparison

end
end LinearAlgebraicGroups.Arithmetic.RankEightSpinStructure
