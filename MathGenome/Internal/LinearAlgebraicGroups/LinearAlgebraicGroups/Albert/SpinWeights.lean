import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SpinWeights
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SchemeCentre
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbstractPairing
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.RingTheory.FiniteStability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.FinCases

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
namespace LinearAlgebraicGroups.Albert.SpinWeights

open LinearAlgebraicGroups.Specs.SpinWeights
open scoped BigOperators

universe u

private theorem coordinate_apply (i j : Fin 4) :
    coordinate i j = if j = i then 1 else 0 := by
  simp [coordinate, Pi.single_apply]

private theorem parity_coordinate (i : Fin 4) : parityMap (coordinate i) = 1 := by
  change ((∑ j, coordinate i j : ℤ) : ZMod 2) = 1
  simp [coordinate_apply]

private theorem vectorPullback_apply (x : VectorExponents) :
    vectorPullback x = (-2 * x 0, fun i => x i.succ - x 0) := rfl

private theorem epsilon_succ (i : Fin 3) : epsilon i.succ = (0, Pi.single i 1) := by
  ext j <;> simp [epsilon, vectorPullback_apply, coordinate_apply, Pi.single_apply, Ne.symm (Fin.succ_ne_zero i)]

private theorem epsilon_zero : epsilon 0 = (-2, fun _ => -1) := by
  ext j <;> simp [epsilon, vectorPullback_apply, coordinate_apply]

private theorem halfSumRelation_proof : HalfSumRelation := by
  change (2 : ℤ) • halfSum = ∑ i, epsilon i
  rw [Fin.sum_univ_succ]
  simp only [epsilon_succ, epsilon_zero]
  apply Prod.ext
  · change _ = -2 + (LinearMap.fst ℤ ℤ (Fin 3 → ℤ)) (∑ i : Fin 3, (0, Pi.single i 1))
    simp [halfSum]
  · funext j
    change _ = -1 + ((LinearMap.snd ℤ ℤ (Fin 3 → ℤ)) (∑ i : Fin 3, (0, Pi.single i 1))) j
    simp [halfSum, Finset.sum_apply, Pi.single_apply]

private theorem characterGenerators_proof : CharacterGenerators := by
  classical
  let X := Submodule.span ℤ (insert halfSum (Set.range epsilon))
  have hU : halfSum ∈ X := Submodule.subset_span (Set.mem_insert _ _)
  have hε (i : Fin 4) : epsilon i ∈ X := Submodule.subset_span
    (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  apply top_unique
  rintro ⟨n, a⟩ _
  have hrep : (n, a) = (-n) • halfSum + ∑ i : Fin 3, a i • epsilon i.succ := by
    simp only [epsilon_succ, halfSum]
    apply Prod.ext
    · change n = -n * -1 + (LinearMap.fst ℤ ℤ (Fin 3 → ℤ)) (∑ i, a i • (0, Pi.single i 1))
      simp
    · funext j
      change a j = (-n) • ((0 : Fin 3 → ℤ) j) + ((LinearMap.snd ℤ ℤ (Fin 3 → ℤ))
        (∑ i, a i • (0, Pi.single i 1))) j
      simp [Finset.sum_apply, Pi.single_apply]
  rw [hrep]
  exact X.add_mem (X.smul_mem _ hU) (X.sum_mem fun i _ => X.smul_mem _ (hε _))

private theorem parity_zero_of_root {x : VectorExponents} (hx : x ∈ vectorRoots) :
    parityMap x = 0 := by
  rcases hx with ⟨i, j, -, rfl | rfl | rfl⟩
  · rw [map_add, parity_coordinate, parity_coordinate]
    decide
  · rw [map_sub, parity_coordinate, parity_coordinate, sub_self]
  · rw [map_sub, map_neg, parity_coordinate, parity_coordinate]
    decide

private theorem even_sum_iff (x : VectorExponents) :
    x ∈ evenSumLattice ↔ (2 : ℤ) ∣ ∑ i, x i := by
  change ((∑ i, x i : ℤ) : ZMod 2) = 0 ↔ (2 : ℤ) ∣ ∑ i, x i
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

private theorem corootSpan_proof : CorootSpan := by
  classical
  change Submodule.span ℤ vectorRoots = evenSumLattice
  let Q := Submodule.span ℤ vectorRoots
  apply le_antisymm
  · exact Submodule.span_le.mpr fun x hx => parity_zero_of_root hx
  · intro x hx
    obtain ⟨n, hn⟩ := (even_sum_iff x).mp hx
    have hdiff (i : Fin 3) : coordinate i.succ - coordinate 0 ∈ Q :=
      Submodule.subset_span ⟨i.succ, 0, Fin.succ_ne_zero _, Or.inr (Or.inl rfl)⟩
    have hplus : coordinate 0 + coordinate 1 ∈ Q :=
      Submodule.subset_span ⟨0, 1, by decide, Or.inl rfl⟩
    have hminus : coordinate 0 - coordinate 1 ∈ Q :=
      Submodule.subset_span ⟨0, 1, by decide, Or.inr (Or.inl rfl)⟩
    have hdouble : (2 : ℤ) • coordinate 0 ∈ Q := by
      convert Q.add_mem hplus hminus using 1
      funext j
      change 2 * coordinate 0 j = coordinate 0 j + coordinate 1 j + (coordinate 0 j - coordinate 1 j)
      omega
    have hrep : x = n • ((2 : ℤ) • coordinate 0) +
        ∑ i : Fin 3, x i.succ • (coordinate i.succ - coordinate 0) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · have hs (i : Fin 3) : 0 ≠ i.succ := (Fin.succ_ne_zero i).symm
        simp [coordinate_apply, Finset.sum_apply, zsmul_eq_mul, hs]
        rw [Fin.sum_univ_succ] at hn
        omega
      · simp [coordinate_apply, Finset.sum_apply, zsmul_eq_mul]
    rw [hrep]
    exact Q.add_mem (Q.smul_mem _ hdouble) (Q.sum_mem fun i _ => Q.smul_mem _ (hdiff i))

private theorem centralClass_vectorPullback (x : VectorExponents) :
    centralClass (vectorPullback x) = (0, parityMap x) := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hneg (t : ZMod 2) : -t = t := by
    calc
      -t = -t + (2 : ZMod 2) * t := by simp [htwo]
      _ = t := by rw [two_mul, ← add_assoc, neg_add_cancel, zero_add]
  apply Prod.ext
  · change ((-2 * x 0 : ℤ) : ZMod 2) = 0
    simp [htwo]
  · change (↑((∑ i : Fin 3, (x i.succ - x 0)) : ℤ) : ZMod 2) = (↑((∑ i, x i) : ℤ) : ZMod 2)
    rw [Fin.sum_univ_succ x, Finset.sum_sub_distrib]
    simp [Finset.sum_const, sub_eq_add_neg, hneg, add_comm, show (3 : ZMod 2) = 1 from rfl]

private theorem centralClass_surjective : Function.Surjective centralClass := by
  rintro ⟨a, b⟩
  use ((a.val : ℤ), Pi.single (0 : Fin 3) (b.val : ℤ))
  apply Prod.ext
  · exact_mod_cast ZMod.natCast_zmod_val a
  · change (↑((∑ i : Fin 3, (Pi.single (0 : Fin 3) (b.val : ℤ) : Fin 3 → ℤ) i) : ℤ) : ZMod 2) = b
    simp [Pi.single_apply]

private theorem rootCharacters_span : Submodule.span ℤ rootCharacters = centralClass.ker := by
  rw [show rootCharacters = vectorPullback '' vectorRoots from rfl, ← Submodule.map_span]
  rw [show Submodule.span ℤ vectorRoots = evenSumLattice from corootSpan_proof]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [LinearMap.mem_ker, centralClass_vectorPullback, (LinearMap.mem_ker.mp hx : parityMap x = 0)]
    rfl
  · intro hy
    obtain ⟨n, hn⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd y.1 2).mp
      (congrArg Prod.fst (LinearMap.mem_ker.mp hy))
    let x : VectorExponents := Fin.cases (-n) fun i => y.2 i - n
    have hyx : vectorPullback x = y := by
      apply Prod.ext
      · change -2 * -n = y.1
        omega
      · funext i
        change y.2 i - n - -n = y.2 i
        omega
    refine ⟨x, ?_, hyx⟩
    apply LinearMap.mem_ker.mpr
    rw [← hyx, LinearMap.mem_ker, centralClass_vectorPullback] at hy
    exact congrArg Prod.snd hy

private theorem centralClass_epsilon (i : Fin 4) : centralClass (epsilon i) = (0, 1) := by
  rw [epsilon, centralClass_vectorPullback, parity_coordinate]

private theorem centralClass_halfSum : centralClass halfSum = (1, 0) := by
  decide

private theorem centralClasses_proof : CentralClasses := by
  refine ⟨centralClass_surjective, rootCharacters_span, ?_, ?_⟩
  · intro i
    refine ⟨centralClass_epsilon i, ?_⟩
    rw [map_neg, centralClass_epsilon]
    decide
  · intro I
    rw [exteriorWeight, map_sub, map_sum, centralClass_halfSum]
    simp only [centralClass_epsilon, Finset.sum_const]
    apply Prod.ext
    · change (I.card • (0 : ZMod 2)) - 1 = 1
      rw [nsmul_zero]
      decide
    · change (I.card • (1 : ZMod 2)) - 0 = (I.card : ZMod 2)
      rw [sub_zero, nsmul_one]

section Torus

variable {R : Type u} [CommRing R]

private theorem diagonal_norm (t : DiagonalPoints R) :
    (scalar t) ^ 2 * ∏ i, scales t i = 1 := t.property

private theorem scale_zero (t : DiagonalPoints R) :
    scales t 0 = ((scalar t) ^ 2 * ∏ i : Fin 3, scales t i.succ)⁻¹ := by
  have h := diagonal_norm t
  rw [Fin.prod_univ_succ] at h
  have h' : scales t 0 * ((scalar t) ^ 2 * ∏ i : Fin 3, scales t i.succ) = 1 := by
    rwa [mul_left_comm]
  exact eq_inv_of_mul_eq_one_left h'

private def fromFree (p : Rˣ × (Fin 3 → Rˣ)) : DiagonalPoints R :=
  ⟨(Fin.cases ((p.1 ^ 2 * ∏ i, p.2 i)⁻¹) p.2, p.1), by
    change p.1 ^ 2 * (∏ i, Fin.cases ((p.1 ^ 2 * ∏ j, p.2 j)⁻¹) p.2 i) = 1
    rw [Fin.prod_univ_succ]
    change p.1 ^ 2 * ((p.1 ^ 2 * ∏ j, p.2 j)⁻¹ * ∏ i, p.2 i) = 1
    rw [mul_left_comm, inv_mul_cancel]⟩

private theorem diagonalParameters_proof : DiagonalParameters.{u} := by
  intro R _
  refine ⟨⟨⟨fun t => (scalar t, fun i => scales t i.succ), fromFree, ?_, ?_⟩, ?_⟩, fun _ => rfl⟩
  · intro t
    apply Subtype.ext
    apply Prod.ext
    · funext i
      refine Fin.cases ?_ (fun _ => rfl) i
      exact (scale_zero t).symm
    · rfl
  · intro p
    rfl
  · intro x y
    rfl

private theorem evaluate_epsilon (t : DiagonalPoints R) (i : Fin 4) :
    Additive.toMul (evaluate t (epsilon i)) = scales t i := by
  classical
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [epsilon_zero]
    change scalar t ^ (-2 : ℤ) * (∏ j : Fin 3, scales t j.succ ^ (-1 : ℤ)) = scales t 0
    rw [scale_zero, zpow_neg, zpow_ofNat, mul_inv, ← Finset.prod_inv_distrib]
    simp
  · rw [epsilon_succ]
    change scalar t ^ (0 : ℤ) * (∏ i : Fin 3, scales t i.succ ^ ((Pi.single j 1 : Fin 3 → ℤ) i)) = _
    simp [Pi.single_apply]

private theorem evaluate_halfSum (t : DiagonalPoints R) :
    Additive.toMul (evaluate t halfSum) = (scalar t)⁻¹ := by
  change scalar t ^ (-1 : ℤ) * (∏ i : Fin 3, scales t i.succ ^ (0 : ℤ)) = _
  simp

private theorem weightEvaluation_proof : WeightEvaluation.{u} := by
  intro R _ t
  refine ⟨fun i => ⟨evaluate_epsilon t i, ?_⟩, ?_⟩
  · rw [map_neg, toMul_neg, evaluate_epsilon]
  · intro I
    rw [exteriorWeight, map_sub, toMul_sub, map_sum, toMul_sum,
      evaluate_halfSum, div_inv_eq_mul, mul_comm]
    simp [evaluate_epsilon]

private theorem diagonalCentralCharacters_proof : DiagonalCentralCharacters.{u} := by
  intro R _ t
  constructor
  · intro h
    have hdiff (i j : Fin 4) (hij : i ≠ j) : scales t i = scales t j := by
      have hh := h (vectorPullback (coordinate i - coordinate j))
        ⟨_, ⟨i, j, hij, Or.inr (Or.inl rfl)⟩, rfl⟩
      rw [map_sub, ← epsilon, ← epsilon, map_sub, toMul_sub,
        evaluate_epsilon, evaluate_epsilon] at hh
      exact div_eq_one.mp hh
    have hi (i : Fin 4) : scales t i = scales t 0 :=
      if h0 : i = 0 then congrArg (scales t) h0 else hdiff i 0 h0
    have hb := h (vectorPullback (coordinate 0 + coordinate 1))
      ⟨_, ⟨0, 1, by decide, Or.inl rfl⟩, rfl⟩
    rw [map_add, ← epsilon, ← epsilon, map_add, toMul_add,
      evaluate_epsilon, evaluate_epsilon, hi 1, ← pow_two] at hb
    refine ⟨scales t 0, hb, ?_, hi⟩
    have hh := diagonal_norm t
    simp only [hi, Fin.prod_const] at hh
    have hp : scales t 0 ^ 4 = 1 := by
      change scales t 0 ^ (2 * 2) = 1
      rw [pow_mul, hb, one_pow]
    simpa only [hp, mul_one] using hh
  · rintro ⟨b, hb, _, hscales⟩ _ ⟨x, ⟨i, j, -, rfl | rfl | rfl⟩, rfl⟩
    · rw [map_add, ← epsilon, ← epsilon, map_add, toMul_add,
        evaluate_epsilon, evaluate_epsilon, hscales, hscales, ← pow_two, hb]
    · rw [map_sub, ← epsilon, ← epsilon, map_sub, toMul_sub,
        evaluate_epsilon, evaluate_epsilon, hscales, hscales, div_self']
    · rw [map_sub, map_neg, ← epsilon, ← epsilon, map_sub, map_neg,
        toMul_sub, toMul_neg, evaluate_epsilon, evaluate_epsilon,
        hscales, hscales, div_eq_mul_inv, ← pow_two, inv_pow, hb, inv_one]

end Torus

section CliffordAction

open Matrix CliffordAlgebra
open SplitSpinSpecification
open scoped Matrix

open private splitForm splitIsometry splitCoordinates integralCliffordEquiv exteriorRep
  exteriorImplementer exterior_implementer_even exterior_implementer_norm exterior_implementer_action
  native_middle_coordinates IsCliffordLift intrinsic_to_tensor_lift map_isometry_evenOdd
  map_isometry_reverse IsTensorLift IsTensorLift.mul IsTensorLift.mem_spin tensor_scalar_lift
  splitScalarUnit factor_det unitConj
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin

open private cliffordEquiv_vector from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
open private exteriorUnit from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin

variable {R : Type u} [CommRing R]

private theorem diagonalBlock_det_unit (t : DiagonalPoints R) : IsUnit (diagonalBlock t).det := by
  rw [diagonalBlock, det_diagonal]
  exact ⟨∏ i, scales t i, map_prod (Units.coeHom R) _ _⟩

private noncomputable abbrev diagonalLinearEquiv (t : DiagonalPoints R) :=
  Matrix.toLinearEquiv (Pi.basisFun R (Fin 4)) (diagonalBlock t) (diagonalBlock_det_unit t)

private theorem diagonalLinearEquiv_basis (t : DiagonalPoints R) (i : Fin 4) :
    diagonalLinearEquiv t (Pi.basisFun R (Fin 4) i) = (scales t i : R) • Pi.basisFun R (Fin 4) i := by
  rw [Pi.basisFun_apply]
  change (Matrix.toLin (Pi.basisFun R (Fin 4)) (Pi.basisFun R (Fin 4)) (diagonalBlock t))
    (Pi.single i 1) = (scales t i : R) • Pi.single i 1
  rw [Matrix.toLin_eq_toLin']
  change (diagonalBlock t) *ᵥ Pi.single i 1 = _
  rw [diagonalBlock, diagonal_mulVec_single, mul_one]
  simpa only [smul_eq_mul, mul_one] using
    (Pi.single_smul' i (scales t i : R) (1 : R))

private theorem diagonal_exterior (t : DiagonalPoints R) (I : Finset (Fin 4)) :
    ExteriorAlgebra.map (diagonalLinearEquiv t).toLinearMap
        ((Pi.basisFun R (Fin 4)).ExteriorAlgebra I) =
      (↑(∏ i ∈ I, scales t i) : R) • (Pi.basisFun R (Fin 4)).ExteriorAlgebra I := by
  classical
  let b := Pi.basisFun R (Fin 4)
  let S := Set.powersetCard.ofCard (s := I) rfl
  let i := Set.powersetCard.ofFinEmbEquiv.symm S
  have hm (j : Fin 4) : j ∈ Set.range i ↔ j ∈ I :=
    Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S j
  let e : Fin I.card ≃ (↥I) :=
    (Equiv.ofInjective i i.injective).trans (Equiv.subtypeEquiv (Equiv.refl _) hm)
  have hprod : (∏ j, (scales t (i j) : R)) = ↑(∏ j ∈ I, scales t j) := by
    calc
      _ = ∏ j : ↥I, (scales t j : R) :=
        Fintype.prod_equiv e _ _ (fun _ => rfl)
      _ = ∏ j ∈ I, (scales t j : R) := Finset.prod_coe_sort I (fun j => (scales t j : R))
      _ = _ := (map_prod (Units.coeHom R) _ _).symm
  have hf : ∀ j : Fin I.card, diagonalLinearEquiv t (b (i j)) = (scales t (i j) : R) • b (i j) :=
    fun j => diagonalLinearEquiv_basis t (i j)
  rw [ExteriorAlgebra.basis_apply_ofCard b (s := I) rfl, ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.map_apply_ιMulti]
  change ExteriorAlgebra.ιMulti R I.card (fun j => diagonalLinearEquiv t (b (i j))) =
    _ • ExteriorAlgebra.ιMulti R I.card (fun j => b (i j))
  simp_rw [hf]
  rw [AlternatingMap.map_smul_univ, hprod]

variable [Algebra ℤ R]

private noncomputable abbrev nativeModel (R : Type u) [CommRing R] [Algebra ℤ R] :
    CliffordAlgebra (splitForm 4 R) ≃ₐ[R] CliffordAlgebra (QuadraticForm.dualProd R (FreeModule R 4)) :=
  CliffordAlgebra.equivOfIsometry (splitIsometry 4 R)

private noncomputable def exteriorModel (R : Type u) [CommRing R] [Algebra ℤ R] :
    ScalarClifford 4 R ≃ₐ[R] Module.End R (ExteriorSpace R) :=
  (integralCliffordEquiv 4 R).trans ((nativeModel R).trans (exteriorRep 4 R))

private noncomputable def diagonalUnscaled (t : DiagonalPoints R) :
    (CliffordAlgebra (splitForm 4 R))ˣ :=
  Units.map (nativeModel R).symm.toMonoidHom (exteriorImplementer (diagonalLinearEquiv t))

private theorem diagonalUnscaled_lift (t : DiagonalPoints R) :
    IsCliffordLift (middle (diagonalBlock t)) (diagonalUnscaled t) 0 (diagonalBlock t).det := by
  let f := diagonalLinearEquiv t
  let E := nativeModel R
  let b := exteriorImplementer f
  have he : E (diagonalUnscaled t : CliffordAlgebra (splitForm 4 R)) = b := E.apply_symm_apply _
  have hi : E (↑(diagonalUnscaled t)⁻¹ : CliffordAlgebra (splitForm 4 R)) = (↑b⁻¹) := by
    change E (↑(Units.map E.symm.toMonoidHom b)⁻¹ : CliffordAlgebra (splitForm 4 R)) = _
    rw [← map_inv]
    exact E.apply_symm_apply _
  refine ⟨map_isometry_evenOdd (splitIsometry 4 R).symm.toIsometry (exterior_implementer_even f), ?_, ?_⟩
  · apply E.injective
    rw [map_mul, show E (reverse (diagonalUnscaled t : CliffordAlgebra (splitForm 4 R))) =
      reverse (E (diagonalUnscaled t)) from map_isometry_reverse (splitIsometry 4 R).toIsometry _,
      he, E.commutes, exterior_implementer_norm]
    congr 1
    rw [← LinearMap.det_toMatrix (Pi.basisFun R (Fin 4))]
    exact congrArg Matrix.det (LinearMap.toMatrix_toLin _ _ _)
  · intro v
    let iso := splitIsometry 4 R
    let w := iso ((splitCoordinates 4 R).symm v)
    have hw (y : PairIndex 4 → R) :
        iso ((splitCoordinates 4 R).symm y) = (hyperbolicBasis R 4).equivFun.symm y := by
      change (hyperbolicBasis R 4).equivFun.symm
        ((splitCoordinates 4 R) ((splitCoordinates 4 R).symm y)) = _
      rw [LinearEquiv.apply_symm_apply]
    have hmiddle := native_middle_coordinates (diagonalBlock t) (diagonalBlock_det_unit t) w
    apply E.injective
    rw [unitConj, map_mul, map_mul, he, hi]
    simp only [E, equivOfIsometry_apply, map_apply_ι]
    change unitConj b (ι _ w) = ι _ (iso ((splitCoordinates 4 R).symm (middle (diagonalBlock t) *ᵥ v)))
    change unitConj b (ι _ (w.1, w.2)) = _
    rw [exterior_implementer_action, hw]
    apply congrArg (ι _)
    apply (hyperbolicBasis R 4).equivFun.injective
    let z : Lex (PairIndex 4) → R := middle (diagonalBlock t) *ᵥ v
    change (hyperbolicBasis R 4).equivFun (w.1.comp f.symm.toLinearMap, f w.2) =
      (hyperbolicBasis R 4).equivFun ((hyperbolicBasis R 4).equivFun.symm z)
    have hw' : (hyperbolicBasis R 4).equivFun w = (v : Lex (PairIndex 4) → R) :=
      (congrArg (hyperbolicBasis R 4).equivFun (hw v)).trans
        ((hyperbolicBasis R 4).equivFun.apply_symm_apply v)
    exact hmiddle.trans ((congrArg ((middle (diagonalBlock t)).mulVec) hw').trans
      ((hyperbolicBasis R 4).equivFun.apply_symm_apply z).symm)

private theorem exteriorModel_vectors (x : ExtendedModule 4 R) :
    exteriorModel R (SpinSpecification.vectors (integralForm 4) R x) =
      CliffordSpecification.hyperbolicOperator (splitIsometry 4 R x) := by
  change (exteriorRep 4 R) ((nativeModel R)
    ((integralCliffordEquiv 4 R) (SpinSpecification.vectors (integralForm 4) R x))) = _
  rw [cliffordEquiv_vector (integralForm 4) R (hyperbolicBasis ℤ 4), equivOfIsometry_apply, map_apply_ι]
  exact CliffordModel.hyperbolicRepresentation_ι _

private theorem diagonal_lift (t : DiagonalPoints R) :
    ∃ s : (ScalarClifford 4 R)ˣ,
      s ∈ SpinSpecification.spinUnits (integralForm 4) R ∧ HasActionMatrix 4 s (middle (diagonalBlock t)) ∧
      ∀ I : Finset (Fin 4), exteriorModel R s ((Pi.basisFun R (Fin 4)).ExteriorAlgebra I) =
        ((scalar t * ∏ i ∈ I, scales t i : Rˣ) : R) • (Pi.basisFun R (Fin 4)).ExteriorAlgebra I := by
  let A := diagonalBlock t
  let m := middle A
  let e := integralCliffordEquiv 4 R
  let a := Units.map e.symm.toMonoidHom (diagonalUnscaled t)
  have hM : IsUnit m.det := by
    have h := factor_det (0 : Block 4 R) (0 : Block 4 R) A (diagonalBlock_det_unit t)
    have hd : m.det = 1 := by simpa [lower, upper, fromBlocks_one, m] using h
    rw [hd]
    exact isUnit_one
  have ha : IsTensorLift m a A.det := intrinsic_to_tensor_lift hM (diagonalUnscaled_lift t)
  let s := splitScalarUnit (m := 4) (scalar t) * a
  have hn : (scalar t : R) ^ 2 * A.det = 1 := by
    have h := congrArg (fun x : Rˣ => (x : R)) (diagonal_norm t)
    simpa [A, diagonalBlock, det_diagonal] using h
  have hs : IsTensorLift m s 1 := by
    have h := IsTensorLift.mul (tensor_scalar_lift (m := 4) (scalar t)) ha
    simpa only [one_mul, hn] using h
  refine ⟨s, IsTensorLift.mem_spin hs, hs.2.2, fun I => ?_⟩
  let b := (Pi.basisFun R (Fin 4)).ExteriorAlgebra I
  have ha' : exteriorModel R (a : ScalarClifford 4 R) =
      (exteriorUnit (diagonalLinearEquiv t) : Module.End R (ExteriorSpace R)) := by
    change (exteriorRep 4 R) (nativeModel R (e (e.symm (diagonalUnscaled t)))) = _
    rw [AlgEquiv.apply_symm_apply]
    change (exteriorRep 4 R) ((nativeModel R) ((nativeModel R).symm
      (exteriorImplementer (diagonalLinearEquiv t)))) = _
    rw [AlgEquiv.apply_symm_apply]
    exact (exteriorRep 4 R).apply_symm_apply _
  change exteriorModel R ((algebraMap R _ (scalar t : R)) * a) b = _
  rw [map_mul, (exteriorModel R).commutes, ha']
  change (scalar t : R) • ExteriorAlgebra.map (diagonalLinearEquiv t).toLinearMap b = _
  rw [diagonal_exterior, smul_smul, Units.val_mul]

private theorem diagonalCliffordAction_proof : DiagonalCliffordAction.{u} := by
  intro R _ _
  refine ⟨exteriorModel R, exteriorModel_vectors, fun t => ?_⟩
  obtain ⟨s, hs, hm, he⟩ := diagonal_lift t
  refine ⟨s, hs, hm, fun I => ?_⟩
  rw [(weightEvaluation_proof R t).2 I, he]


end CliffordAction

section VectorDiagonal

open Matrix SplitSpinSpecification

variable {K : Type u} [CommRing K]

private def vectorEigenvalue (t : DiagonalPoints K) : PairIndex 4 → K :=
  Sum.elim (fun i => ↑(scales t i)) (fun i => ↑((scales t i)⁻¹))

private theorem middle_diagonal (t : DiagonalPoints K) :
    middle (diagonalBlock t) = Matrix.diagonal (vectorEigenvalue t) := by
  let A := diagonalBlock t
  let B := Matrix.diagonal fun i => (↑((scales t i)⁻¹) : K)
  have hAB : A * B = 1 := by
    change Matrix.diagonal _ * Matrix.diagonal _ = _
    rw [diagonal_mul_diagonal]
    simp [diagonal_one]
  have hB : A⁻¹ = B := by
    rw [← nonsing_inv_mul_cancel_left A B (diagonalBlock_det_unit t), hAB, mul_one]
  rw [middle, hB]
  ext (i | i) (j | j) <;> simp [B, diagonalBlock, vectorEigenvalue, diagonal_apply, eq_comm]

end VectorDiagonal

section Irreducibility

open Matrix
open scoped Matrix
open SplitSpinSpecification

variable {K : Type u} [Field K]

private theorem diagonal_coefficient {I V : Type*} [Fintype I]
    [AddCommGroup V] [Module K V] (b : Module.Basis I K V)
    (D : V →ₗ[K] V) (c : I → K) (hD : ∀ i, D (b i) = c i • b i)
    (x : V) (j : I) : b.repr (D x) j = c j * b.repr x j := by
  classical
  have hr := congrArg (fun w => (b.repr (D w)) j) (b.sum_repr x).symm
  rw [hr]
  simp only [map_sum, map_smul, hD, Module.Basis.repr_self, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
  simp [mul_ite, Finset.sum_ite_eq', mul_comm]

/-- A submodule stable under diagonals separating the basis lines contains
the basis vector at each nonzero coordinate of any of its vectors. -/
private theorem basis_mem_of_separation {I V : Type*} [Fintype I]
    [AddCommGroup V] [Module K V] (b : Module.Basis I K V) (W : Submodule K V)
    (separates : ∀ i j : I, i ≠ j → ∃ (D : V →ₗ[K] V) (eigenvalue : I → K),
      (∀ x ∈ W, D x ∈ W) ∧ (∀ l, D (b l) = eigenvalue l • b l) ∧ eigenvalue i ≠ eigenvalue j)
    {x : V} (hx : x ∈ W) (i : I) (hi : b.repr x i ≠ 0) : b i ∈ W := by
  classical
  have prune (T : Finset I) (hT : i ∉ T) :
      ∃ y ∈ W, b.repr y i = b.repr x i ∧ ∀ l ∈ T, b.repr y l = 0 := by
    induction T using Finset.induction_on with
    | empty => exact ⟨x, hx, rfl, by simp⟩
    | @insert j T hjT ih =>
      obtain ⟨y, hy, hyi, hyT⟩ := ih (fun h => hT (Finset.mem_insert_of_mem h))
      have hij : i ≠ j := fun h => hT (h ▸ Finset.mem_insert_self j T)
      obtain ⟨D, eigenvalue, hD, hdiag, hd⟩ := separates i j hij
      have hrepr := diagonal_coefficient b D eigenvalue hdiag y
      let a := (eigenvalue i - eigenvalue j)⁻¹
      refine ⟨a • (D y - eigenvalue j • y), W.smul_mem _ (W.sub_mem (hD y hy) (W.smul_mem _ hy)), ?_, ?_⟩
      · simp only [map_smul, map_sub, Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul, hrepr]
        rw [← sub_mul, ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hd), one_mul, hyi]
      · intro l hl
        simp only [map_smul, map_sub, Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul, hrepr]
        rcases Finset.mem_insert.mp hl with rfl | hl
        · simp
        · simp [hyT l hl]
  obtain ⟨y, hy, hyi, hyother⟩ := prune (Finset.univ.erase i) (Finset.notMem_erase i _)
  have hEq : y = b.repr x i • b i := by
    apply b.repr.injective
    ext j
    by_cases hji : j = i
    · subst j
      simpa using hyi
    · rw [hyother j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)]
      simp [hji]
  rw [hEq] at hy
  exact (Submodule.smul_mem_iff W hi).mp hy

private def singleScale (z : Kˣ) (i : Fin 4) : DiagonalPoints K :=
  ⟨(fun j => if j = i then z ^ 2 else 1, z⁻¹), by
    change z⁻¹ ^ 2 * (∏ j : Fin 4, if j = i then z ^ 2 else 1) = 1
    simp [Finset.prod_ite_eq', inv_pow]⟩

private theorem exists_separating_unit [Infinite K] : ∃ z : Kˣ, (z : K) ^ 4 ≠ 1 := by
  let p : Polynomial K := Polynomial.X * (Polynomial.X ^ 4 - 1)
  have hp : p ≠ 0 := by
    apply mul_ne_zero Polynomial.X_ne_zero
    intro h
    have h0 := congrArg (Polynomial.eval (0 : K)) h
    simp at h0
  have hex : ∃ x : K, p.eval x ≠ 0 := by
    by_contra! h
    exact hp (Polynomial.zero_of_eval_zero _ h)
  obtain ⟨x, hx⟩ := hex
  change (Polynomial.X * (Polynomial.X ^ 4 - 1 : Polynomial K)).eval x ≠ 0 at hx
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one] at hx
  exact ⟨Units.mk0 x (left_ne_zero_of_mul hx), sub_ne_zero.mp (right_ne_zero_of_mul hx)⟩

private theorem vectorEigenvalue_singleScale (z : Kˣ) (i : Fin 4) :
    vectorEigenvalue (singleScale z i) =
      Sum.elim (fun j => if j = i then (z : K) ^ 2 else 1)
        (fun j => if j = i then (↑z⁻¹ : K) ^ 2 else 1) := by
  funext j
  cases j with
  | inl j => by_cases hj : j = i <;> simp [vectorEigenvalue, singleScale, scales, hj]
  | inr j =>
    by_cases hj : j = i <;> simp [vectorEigenvalue, singleScale, scales, hj, inv_pow]

private theorem vector_separation (z : Kˣ) (hz : (z : K) ^ 4 ≠ 1) {i j : PairIndex 4} (hij : i ≠ j) :
    ∃ l : Fin 4, vectorEigenvalue (singleScale z l) i ≠ vectorEigenvalue (singleScale z l) j := by
  have h₁ : (z : K) ^ 2 ≠ 1 := by
    intro h
    apply hz
    change (z : K) ^ (2 * 2) = 1
    rw [pow_mul, h, one_pow]
  have h₂ : (↑z⁻¹ : K) ^ 2 ≠ 1 := by
    intro h
    apply h₁
    have h' := congrArg (fun a : K => a⁻¹) h
    simpa [Units.val_inv_eq_inv_val, ← inv_pow] using h'
  have h₃ : (z : K) ^ 2 ≠ (↑z⁻¹ : K) ^ 2 := by
    intro h
    apply hz
    change (z : K) ^ (2 + 2) = 1
    rw [pow_add]
    nth_rw 2 [h]
    exact congrArg (fun a : Kˣ => (a : K)) (by rw [inv_pow, mul_inv_cancel] : z ^ 2 * z⁻¹ ^ 2 = 1)
  cases i with
  | inl i =>
    use i
    rw [vectorEigenvalue_singleScale]
    cases j with
    | inl j =>
      have h : j ≠ i := fun h => hij (congrArg Sum.inl h.symm)
      simpa [h] using h₁
    | inr j =>
      by_cases h : j = i
      · simpa [h] using h₃
      · simpa [h] using h₁
  | inr i =>
    use i
    rw [vectorEigenvalue_singleScale]
    cases j with
    | inl j =>
      by_cases h : j = i
      · simpa [h] using h₃.symm
      · simpa [h] using h₂
    | inr j =>
      have h : j ≠ i := fun h => hij (congrArg Sum.inr h.symm)
      simpa [h] using h₂

variable [IsAlgClosed K] [Algebra ℤ K]

private theorem middle_perm_lift (σ : Equiv.Perm (Fin 4)) :
    ∃ a : (ScalarClifford 4 K)ˣ, a ∈ SpinSpecification.spinUnits (integralForm 4) K ∧
      HasActionMatrix 4 a (middle (σ.permMatrix K)) := by
  let A := σ.permMatrix K
  have hA : IsUnit A.det := by
    change IsUnit (σ.permMatrix K).det
    rw [det_permutation]
    exact ((Equiv.Perm.sign σ).map (Int.castRingHom K).toMonoidHom).isUnit
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (A.det)⁻¹ (n := 2) (by decide)
  have hnonzero : r ≠ 0 := by
    intro h
    exact inv_ne_zero hA.ne_zero (by simpa [h] using hr.symm)
  let p : ChartParameters 4 K :=
    ⟨0, 0, A, Units.mk0 r hnonzero, by simp [IsAlternating], by simp [IsAlternating], by
      change r ^ 2 * A.det = 1
      rw [hr, inv_mul_cancel₀ hA.ne_zero]⟩
  obtain ⟨e, he, -⟩ := SplitSpin.cliffordChart.{u} 4 (by decide)
  refine ⟨(e K p).val, (e K p).property.1, ?_⟩
  simpa [p, lower, upper, fromBlocks_one] using he K p

omit [IsAlgClosed K] [Algebra ℤ K] in
private theorem middle_perm (σ : Equiv.Perm (Fin 4)) :
    middle (σ.permMatrix K) = fromBlocks (σ.permMatrix K) 0 0 (σ.permMatrix K) := by
  let A := σ.permMatrix K
  have hA : IsUnit A.det := by
    change IsUnit (σ.permMatrix K).det
    rw [det_permutation]
    exact ((Equiv.Perm.sign σ).map (Int.castRingHom K).toMonoidHom).isUnit
  have hA' : A * (σ⁻¹).permMatrix K = 1 := by simp [A, ← permMatrix_mul]
  have hinv : A⁻¹ = (σ⁻¹).permMatrix K := by
    rw [← nonsing_inv_mul_cancel_left A ((σ⁻¹).permMatrix K) hA, hA', mul_one]
  simp [middle, hinv, transpose_permMatrix, A]

open private switch_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin

private theorem vectorIrreducibility_proof : VectorIrreducibility.{u} := by
  intro K _ _ _ W hW
  classical
  let b := Pi.basisFun K (PairIndex 4)
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨x, hx, hxn⟩ := W.ne_bot_iff.mp hbot
    obtain ⟨i, hi⟩ : ∃ i, b.repr x i ≠ 0 := by
      by_contra! h
      apply hxn
      apply b.repr.injective
      ext i
      exact h i
    obtain ⟨z, hz⟩ := exists_separating_unit (K := K)
    have hsep (i j : PairIndex 4) (hij : i ≠ j) :
        ∃ (D : (PairIndex 4 → K) →ₗ[K] (PairIndex 4 → K)) (eigenvalue : PairIndex 4 → K),
          (∀ x ∈ W, D x ∈ W) ∧ (∀ l, D (b l) = eigenvalue l • b l) ∧ eigenvalue i ≠ eigenvalue j := by
      obtain ⟨l, hl⟩ := vector_separation z hz hij
      let t := singleScale z l
      obtain ⟨e, -, he⟩ := diagonalCliffordAction_proof K
      obtain ⟨s, hs, hm, -⟩ := he t
      refine ⟨Matrix.toLin' (middle (diagonalBlock t)), vectorEigenvalue t,
        hW s hs _ hm, fun j => ?_, hl⟩
      change middle (diagonalBlock t) *ᵥ b j = _
      rw [middle_diagonal]
      have hb : b j = Pi.single j 1 := Pi.basisFun_apply _ _ j
      rw [hb, diagonal_mulVec_single]
      exact Pi.single_smul' j (vectorEigenvalue t j) (1 : K)
    have hbase := basis_mem_of_separation b W hsep hx i hi
    have hleft (l : Fin 4) : b (Sum.inl l) =
        Sum.elim (Pi.single l 1) (0 : Fin 4 → K) := by
      ext (i | i) <;> simp [b, Pi.basisFun_apply, Pi.single_apply]
    have hright (l : Fin 4) : b (Sum.inr l) =
        Sum.elim (0 : Fin 4 → K) (Pi.single l 1) := by
      ext (i | i) <;> simp [b, Pi.basisFun_apply, Pi.single_apply]
    have hperm (l j : Fin 4) : (b (Sum.inl l) ∈ W → b (Sum.inl j) ∈ W) ∧
        (b (Sum.inr l) ∈ W → b (Sum.inr j) ∈ W) := by
      let σ := Equiv.swap l j
      obtain ⟨a, ha, hm⟩ := middle_perm_lift (K := K) σ
      have hσ : σ.symm l = j := by simp [σ]
      have hmove : σ.permMatrix K *ᵥ Pi.single l 1 = Pi.single j 1 := by
        rw [permMatrix_mulVec]
        funext v
        simp [Pi.single_apply, ← σ.eq_symm_apply, hσ]
      constructor
      · intro hl
        have h := hW a ha _ hm _ hl
        rw [middle_perm, hleft, fromBlocks_mulVec] at h
        simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, mulVec_zero,
          hmove, add_zero] at h
        exact (hleft j).symm ▸ h
      · intro hl
        have h := hW a ha _ hm _ hl
        rw [middle_perm, hright, fromBlocks_mulVec] at h
        simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, mulVec_zero,
          hmove, zero_add, add_zero] at h
        exact (hright j).symm ▸ h
    have hcross : (b (Sum.inl 0) ∈ W → b (Sum.inr 0) ∈ W) ∧
        (b (Sum.inr 0) ∈ W → b (Sum.inl 0) ∈ W) := by
      let J : EvenSwitches 4 := ⟨{0, 1}, by decide⟩
      obtain ⟨a, ha, hm⟩ := SplitSpin.even_switch_spin_lift (S := K) J
      have hl : signedSwitch 4 K J.val *ᵥ b (Sum.inl 0) = - b (Sum.inr 0) := by
        rw [hleft, hright, switch_apply]
        ext (i | i) <;> fin_cases i <;> simp [J, Pi.single_apply]
      have hr : signedSwitch 4 K J.val *ᵥ b (Sum.inr 0) = - b (Sum.inl 0) := by
        rw [hleft, hright, switch_apply]
        ext (i | i) <;> fin_cases i <;> simp [J, Pi.single_apply]
      exact ⟨fun h => W.neg_mem_iff.mp (hl ▸ hW a ha _ hm _ h),
        fun h => W.neg_mem_iff.mp (hr ▸ hW a ha _ hm _ h)⟩
    have hall (j : PairIndex 4) : b j ∈ W := by
      have h₀ : b (Sum.inl 0) ∈ W ∧ b (Sum.inr 0) ∈ W := by
        cases i with
        | inl i =>
          have h := (hperm i 0).1 hbase
          exact ⟨h, hcross.1 h⟩
        | inr i =>
          have h := (hperm i 0).2 hbase
          exact ⟨hcross.2 h, h⟩
      cases j with
      | inl j => exact (hperm 0 j).1 h₀.1
      | inr j => exact (hperm 0 j).2 h₀.2
    exact b.span_eq ▸ Submodule.span_le.mpr (Set.range_subset_iff.mpr hall) |> top_unique

end Irreducibility

section HalfSpin

open Matrix CliffordAlgebra Module
open scoped Matrix
open SplitSpinSpecification

open private splitE splitF split_coordinates_e split_coordinates_f split_e_polar
  splitIsometry splitCoordinates integralCliffordEquiv native_pair_coordinates
  action_matrix_on_vectors unitConj map_isometry_evenOdd exteriorRep
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin
open private cliffordEquiv_vector cliffordEquiv_even from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
open private create contract create_contract_basis exteriorBasis_word exteriorWord orderedIndices
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.CliffordModel
open private switch_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin

section ExteriorBasis

variable {K : Type u} [CommRing K] [Algebra ℤ K]

private noncomputable abbrev eBasis (K : Type u) [CommRing K] :=
  (Pi.basisFun K (Fin 4)).ExteriorAlgebra

private noncomputable abbrev creation (i : Fin 4) : ScalarClifford 4 K :=
  SpinSpecification.vectors (integralForm 4) K (splitE (m := 4) (S := K) i)

private noncomputable abbrev contraction (i : Fin 4) : ScalarClifford 4 K :=
  SpinSpecification.vectors (integralForm 4) K (splitF (m := 4) (S := K) i)

private theorem creation_operator (i : Fin 4) :
    exteriorModel K (creation i) = create (Pi.basisFun K (Fin 4) i) := by
  rw [exteriorModel_vectors]
  have h : (splitIsometry 4 K) (splitE i) = (0, Pi.basisFun K (Fin 4) i) := by
    apply (hyperbolicBasis K 4).equivFun.injective
    let v : Lex (PairIndex 4) → K := splitCoordinates 4 K (splitE i)
    change (hyperbolicBasis K 4).equivFun ((hyperbolicBasis K 4).equivFun.symm v) = _
    rw [LinearEquiv.apply_symm_apply, native_pair_coordinates, Pi.basisFun_apply]
    exact split_coordinates_e i
  rw [h]
  simp [CliffordSpecification.hyperbolicOperator, create]

private theorem contraction_operator (i : Fin 4) :
    exteriorModel K (contraction i) = contract ((Pi.basisFun K (Fin 4)).coord i) := by
  rw [exteriorModel_vectors]
  have h : (splitIsometry 4 K) (splitF i) = ((Pi.basisFun K (Fin 4)).coord i, 0) := by
    apply (hyperbolicBasis K 4).equivFun.injective
    let v : Lex (PairIndex 4) → K := splitCoordinates 4 K (splitF i)
    change (hyperbolicBasis K 4).equivFun ((hyperbolicBasis K 4).equivFun.symm v) = _
    rw [LinearEquiv.apply_symm_apply, native_pair_coordinates]
    change (splitCoordinates 4 K (splitF i) : PairIndex 4 → K) = _
    rw [split_coordinates_f]
    congr 1
    funext j
    rw [← Pi.basisFun_apply K (Fin 4) j]
    change (Pi.single i (1 : K) : Fin 4 → K) j =
      ((Pi.basisFun K (Fin 4)).repr (Pi.basisFun K (Fin 4) j)) i
    simp [Pi.single_apply, eq_comm]
  rw [h]
  simp [CliffordSpecification.hyperbolicOperator]

private theorem contraction_creation (i : Fin 4) :
    contraction (K := K) i * creation i = 1 - creation i * contraction i := by
  let e := integralCliffordEquiv 4 K
  apply e.injective
  rw [map_mul, map_sub, map_one, map_mul]
  simp only [e, creation, contraction, integralCliffordEquiv, cliffordEquiv_vector]
  rw [ι_mul_ι_comm, QuadraticMap.polar_comm, split_e_polar, split_coordinates_f]
  simp

private theorem occupation (i : Fin 4) (I : Finset (Fin 4)) :
    exteriorModel K (creation i * contraction i) (eBasis K I) =
      (if i ∈ I then (1 : K) else 0) • eBasis K I := by
  rw [map_mul, creation_operator, contraction_operator]
  change create (Pi.basisFun K (Fin 4) i)
    (contract ((Pi.basisFun K (Fin 4)).coord i) (eBasis K I)) = _
  rw [create_contract_basis]
  by_cases h : i ∈ I <;> simp [h]

end ExteriorBasis

variable {K : Type u} [Field K] [Algebra ℤ K]

private theorem switch_basis_vectors (J : Finset (Fin 4)) (i : Fin 4) :
    let D := signedSwitch 4 K J
    (D *ᵥ splitCoordinates 4 K (splitE i) =
      if i ∈ J then -(splitCoordinates 4 K (splitF i) : PairIndex 4 → K)
        else splitCoordinates 4 K (splitE i)) ∧
    (D *ᵥ splitCoordinates 4 K (splitF i) =
      if i ∈ J then -(splitCoordinates 4 K (splitE i) : PairIndex 4 → K)
        else splitCoordinates 4 K (splitF i)) := by
  simp only [split_coordinates_e, split_coordinates_f, switch_apply]
  constructor <;> ext (j | j) <;> by_cases hj : j = i <;> by_cases hi : i ∈ J <;>
    simp [hj, hi, Pi.single_apply]

private theorem switch_occupations {a : (ScalarClifford 4 K)ˣ} (J : Finset (Fin 4))
    (ha : HasActionMatrix 4 a (signedSwitch 4 K J)) (i : Fin 4) :
    unitConj a (creation i * contraction i) =
      if i ∈ J then 1 - creation i * contraction i else creation i * contraction i := by
  have hE := action_matrix_on_vectors ha (splitE i)
  have hF := action_matrix_on_vectors ha (splitF i)
  obtain ⟨h₁, h₂⟩ := switch_basis_vectors (K := K) J i
  rw [h₁] at hE
  rw [h₂] at hF
  have hmul (x y : ScalarClifford 4 K) :
      unitConj a (x * y) = unitConj a x * unitConj a y := by
    change (↑a : ScalarClifford 4 K) * (x * y) * ↑a⁻¹ =
      ((↑a : ScalarClifford 4 K) * x * ↑a⁻¹) * ((↑a : ScalarClifford 4 K) * y * ↑a⁻¹)
    symm
    calc
      _ = ((a : ScalarClifford 4 K) * x) * (↑a⁻¹ * a) * (y * ↑a⁻¹) := by simp only [mul_assoc]
      _ = _ := by simp only [Units.inv_mul, mul_one, mul_assoc]
  rw [hmul]
  by_cases hi : i ∈ J
  · rw [ite_eq_left hi] at hE hF ⊢
    simp only [map_neg, LinearEquiv.symm_apply_apply] at hE hF
    rw [hE, hF]
    exact (neg_mul_neg _ _).trans (contraction_creation i)
  · rw [ite_eq_right hi] at hE hF ⊢
    simp only [LinearEquiv.symm_apply_apply] at hE hF
    rw [hE, hF]

private theorem occupation_coefficient (i : Fin 4) (x : ExteriorSpace K) (L : Finset (Fin 4)) :
    (eBasis K).repr (exteriorModel K (creation i * contraction i) x) L =
      (if i ∈ L then (1 : K) else 0) * (eBasis K).repr x L := by
  exact diagonal_coefficient (eBasis K) (exteriorModel K (creation i * contraction i))
    (fun L => if i ∈ L then 1 else 0) (occupation i) x L

open scoped symmDiff in
set_option maxHeartbeats 500000 in
private theorem switch_wedge_line {a : (ScalarClifford 4 K)ˣ} (J : Finset (Fin 4))
    (ha : HasActionMatrix 4 a (signedSwitch 4 K J)) (I : Finset (Fin 4)) :
    ∃ c : K, c ≠ 0 ∧ exteriorModel K a (eBasis K I) = c • eBasis K (I ∆ J) := by
  let x := exteriorModel K a (eBasis K I)
  have hxn : x ≠ 0 := by
    intro h
    have hinv := congrArg (fun w => exteriorModel K (↑a⁻¹ : ScalarClifford 4 K) w) h
    change (exteriorModel K (↑a⁻¹ : ScalarClifford 4 K) * exteriorModel K a) (eBasis K I) =
      exteriorModel K (↑a⁻¹ : ScalarClifford 4 K) 0 at hinv
    rw [← map_mul, Units.inv_mul, map_one, map_zero] at hinv
    exact (eBasis K).ne_zero I hinv
  have hconj (i : Fin 4) :
      exteriorModel K (creation i * contraction i) x =
        (if i ∈ I ∆ J then (1 : K) else 0) • x := by
    have h := congrArg (fun q : ScalarClifford 4 K => exteriorModel K q x) (switch_occupations J ha i)
    have hleft : exteriorModel K (unitConj a (creation i * contraction i)) x =
        exteriorModel K a (exteriorModel K (creation i * contraction i) (eBasis K I)) := by
      change (exteriorModel K (unitConj a (creation i * contraction i)) *
        exteriorModel K (a : ScalarClifford 4 K)) (eBasis K I) = _
      let C := ScalarClifford 4 K
      let q : C := creation i * contraction i
      have hcancel : unitConj a q * (a : C) = (a : C) * q := by
        change (((a : C) * q) * (↑a⁻¹ : C)) * (a : C) = (a : C) * q
        rw [mul_assoc ((a : C) * q) (↑a⁻¹ : C) (a : C), Units.inv_mul, mul_one]
      rw [← map_mul, show unitConj a (creation i * contraction i) * (a : C) = (a : C) * q from hcancel,
        map_mul, Module.End.mul_apply]
    rw [hleft, occupation, map_smul] at h
    by_cases hj : i ∈ J <;> by_cases hi : i ∈ I <;>
      simp only [Finset.mem_symmDiff, hj, hi, not_true_eq_false, not_false_eq_true,
        and_true, and_false, or_false, or_true,
        ite_true, ite_false, one_smul, zero_smul, map_sub, map_one, LinearMap.sub_apply,
        Module.End.one_apply] at h ⊢
    · exact sub_eq_self.mp h.symm
    · exact (sub_eq_zero.mp h.symm).symm
    · exact h.symm
    · exact h.symm
  have hzero (L : Finset (Fin 4)) (hL : L ≠ I ∆ J) : (eBasis K).repr x L = 0 := by
    have hm : ∃ i : Fin 4, ¬ (i ∈ L ↔ i ∈ I ∆ J) := by
      by_contra! hh
      exact hL (Finset.ext hh)
    obtain ⟨i, hi⟩ := hm
    have h := congrArg (fun v => (eBasis K).repr v L) (hconj i)
    change (eBasis K).repr (exteriorModel K (creation i * contraction i) x) L =
      (eBasis K).repr ((if i ∈ I ∆ J then (1 : K) else 0) • x) L at h
    rw [occupation_coefficient, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
    by_cases h₁ : i ∈ L <;> by_cases h₂ : i ∈ I ∆ J
    · exact (hi (by simp [h₁, h₂])).elim
    · simpa [h₁, h₂] using h
    · simpa [h₁, h₂] using h.symm
    · exact (hi (by simp [h₁, h₂])).elim
  let c := (eBasis K).repr x (I ∆ J)
  have hx : x = c • eBasis K (I ∆ J) := by
    apply (eBasis K).repr.injective
    ext L
    by_cases h : L = I ∆ J
    · subst L
      simp [c]
    · simp [hzero L h, h]
  exact ⟨c, fun hc => hxn (by simp [hx, hc]), hx⟩

omit [Algebra ℤ K] in
private theorem exterior_parity_span (p : ZMod 2) :
    evenOdd (0 : QuadraticForm K (FreeModule K 4)) p =
      Submodule.span K ((eBasis K) '' {I | (I.card : ZMod 2) = p}) := by
  rw [CliffordModel.parity_span (0 : QuadraticForm K (FreeModule K 4)) (Pi.basisFun K (Fin 4)) p]
  congr 2
  funext I
  rw [show eBasis K I = exteriorWord (Pi.basisFun K (Fin 4)) (orderedIndices I)
    from exteriorBasis_word _ _]
  rw [CliffordSpecification.orderedWord, exteriorWord, orderedIndices, List.map_ofFn]
  rfl

private theorem exteriorModel_preserves (p : ZMod 2) {a : (ScalarClifford 4 K)ˣ}
    (ha : a ∈ SpinSpecification.spinUnits (integralForm 4) K) {x : ExteriorSpace K}
    (hx : x ∈ evenOdd (0 : QuadraticForm K (FreeModule K 4)) p) :
    exteriorModel K a x ∈ evenOdd (0 : QuadraticForm K (FreeModule K 4)) p := by
  have h := (cliffordEquiv_even (integralForm 4) K (hyperbolicBasis ℤ 4) a).mpr ha.1
  have hp := map_isometry_evenOdd (splitIsometry 4 K).toIsometry h
  exact (CliffordModel.hyperbolicEquiv_even (Pi.basisFun K (Fin 4)) _).mp hp p x hx

open scoped symmDiff in
private theorem even_symmetric_difference (I L : Finset (Fin 4))
    (h : (I.card : ZMod 2) = (L.card : ZMod 2)) : Even (I ∆ L).card := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  have hcard : (I ∆ L).card + 2 * (I ∩ L).card = I.card + L.card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
    have hI := Finset.card_sdiff_add_card_inter I L
    have hL := Finset.card_sdiff_add_card_inter L I
    rw [Finset.inter_comm L I] at hL
    omega
  have hx := congrArg (fun n : ℕ => (n : ZMod 2)) hcard
  simpa [h, ← two_mul, show (2 : ZMod 2) = 0 from rfl] using hx

omit [Algebra ℤ K] in
private theorem exterior_eigenvalue_singleScale (z : Kˣ) (i : Fin 4) (I : Finset (Fin 4)) :
    ((scalar (singleScale z i) * ∏ j ∈ I, scales (singleScale z i) j : Kˣ) : K) =
      if i ∈ I then (z : K) else ↑z⁻¹ := by
  change ((z⁻¹ * ∏ j ∈ I, if j = i then z ^ 2 else 1 : Kˣ) : K) = _
  have hz : z⁻¹ * z ^ 2 = z := by rw [pow_two, ← mul_assoc, inv_mul_cancel, one_mul]
  by_cases h : i ∈ I <;> simp [Finset.prod_ite_eq', h, hz]

open scoped symmDiff in
private theorem halfSpinIrreducibility_proof : HalfSpinIrreducibility.{u} := by
  intro K _ _ _
  refine ⟨exteriorModel K, exteriorModel_vectors, fun p => ?_⟩
  let V := evenOdd (0 : QuadraticForm K (FreeModule K 4)) p
  change (∀ (a : (ScalarClifford 4 K)ˣ), a ∈ SpinSpecification.spinUnits (integralForm 4) K →
    ∀ x ∈ V, exteriorModel K a x ∈ V) ∧ _
  refine ⟨fun a ha x hx => exteriorModel_preserves p ha hx, ?_⟩
  intro W hWV hW
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, hx, hxn⟩ := W.ne_bot_iff.mp hbot
  obtain ⟨I, hI⟩ : ∃ I, (eBasis K).repr x I ≠ 0 := by
    by_contra! h
    apply hxn
    apply (eBasis K).repr.injective
    ext I
    simpa only [map_zero, Finsupp.zero_apply] using h I
  obtain ⟨z, hz⟩ := exists_separating_unit (K := K)
  have hz' : (z : K) ≠ ↑z⁻¹ := by
    intro h
    apply hz
    have h' : (z : K) ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 2 [h]
      exact congrArg (fun a : Kˣ => (a : K)) (mul_inv_cancel z)
    change (z : K) ^ (2 * 2) = 1
    rw [pow_mul, h', one_pow]
  have hsep (L M : Finset (Fin 4)) (hLM : L ≠ M) :
      ∃ (D : Module.End K (ExteriorSpace K)) (eigenvalue : Finset (Fin 4) → K),
        (∀ v ∈ W, D v ∈ W) ∧ (∀ N, D (eBasis K N) = eigenvalue N • eBasis K N) ∧
          eigenvalue L ≠ eigenvalue M := by
    have he : ∃ i, ¬ (i ∈ L ↔ i ∈ M) := by
      by_contra! h
      exact hLM (Finset.ext h)
    obtain ⟨i, hi⟩ := he
    obtain ⟨a, ha, -, hd⟩ := diagonal_lift (singleScale z i)
    refine ⟨exteriorModel K a, fun N => if i ∈ N then (z : K) else ↑z⁻¹,
      hW a ha, fun N => ?_, ?_⟩
    · exact (hd N).trans (congrArg (· • eBasis K N) (exterior_eigenvalue_singleScale z i N))
    · by_cases hL : i ∈ L <;> by_cases hM : i ∈ M
      · exact (hi (by simp [hL, hM])).elim
      · simpa [hL, hM] using hz'
      · simpa [hL, hM] using hz'.symm
      · exact (hi (by simp [hL, hM])).elim
  have hbase := basis_mem_of_separation (eBasis K) W hsep hx I hI
  have hspan : V = Submodule.span K ((eBasis K) '' {I | (I.card : ZMod 2) = p}) :=
    exterior_parity_span p
  have hIp : (I.card : ZMod 2) = p := by
    by_contra hIp
    have hvanish : V ≤ LinearMap.ker ((Finsupp.lapply I).comp (eBasis K).repr.toLinearMap) := by
      rw [hspan, Submodule.span_le]
      rintro _ ⟨L, hL, rfl⟩
      apply LinearMap.mem_ker.mpr
      change (eBasis K).repr (eBasis K L) I = 0
      rw [Basis.repr_self]
      have hLI : L ≠ I := fun e => hIp (e ▸ hL)
      simp [hLI]
    have h := LinearMap.mem_ker.mp (hvanish (hWV hbase))
    change (eBasis K).repr (eBasis K I) I = 0 at h
    simp at h
  apply le_antisymm hWV
  change V ≤ W
  rw [hspan, Submodule.span_le]
  rintro _ ⟨L, hL, rfl⟩
  let J : EvenSwitches 4 := ⟨I ∆ L, even_symmetric_difference I L (hIp.trans hL.symm)⟩
  obtain ⟨a, ha, hm⟩ := SplitSpin.even_switch_spin_lift (S := K) J
  obtain ⟨c, hc, hmove⟩ := switch_wedge_line J.val hm I
  have h := hW a ha _ hbase
  rw [hmove, show I ∆ J.val = L from symmDiff_symmDiff_cancel_left I L] at h
  exact (W.smul_mem_iff hc).mp h

end HalfSpin

section CorootCoordinates

open scoped Matrix BigOperators

private theorem coordinate_dot (i : Fin 4) (x : VectorExponents) :
    coordinate i ⬝ᵥ x = x i := by
  simp [coordinate, single_dotProduct]

private theorem dot_coordinate (x : VectorExponents) (i : Fin 4) :
    x ⬝ᵥ coordinate i = x i :=
  (dotProduct_comm _ _).trans (coordinate_dot i x)

private theorem vectorPullback_injective : Function.Injective vectorPullback := by
  intro x y he
  have h0 : x 0 = y 0 := by
    have h := congrArg Prod.fst he
    change -2 * x 0 = -2 * y 0 at h
    omega
  funext i
  refine Fin.cases h0 (fun i => ?_) i
  have h := congrArg (fun z : CharacterExponents => z.2 i) he
  change x i.succ - x 0 = y i.succ - y 0 at h
  omega

private theorem latticePairing_vectorPullback (x : VectorExponents) (y : evenSumLattice) :
    latticePairing (vectorPullback x) y = x ⬝ᵥ y.val := by
  obtain ⟨n, hn⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (∑ i, y.val i) 2).mp y.property
  change (∑ i, y.val i) = 2 * n at hn
  change (-2 * x 0) * (-(∑ i, y.val i) / 2) +
    (∑ i : Fin 3, (x i.succ - x 0) * y.val i.succ) = _
  rw [hn, show -(2 * n) / 2 = -n by omega]
  change _ = ∑ i, x i * y.val i
  rw [Fin.sum_univ_succ (fun i => x i * y.val i)]
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Fin.sum_univ_succ] at hn
  have h := congrArg (fun a : ℤ => x 0 * a) hn
  simp only [mul_add] at h
  linarith only [h]

private theorem vectorRoots_signs (r : VectorExponents) :
    r ∈ vectorRoots ↔ ∃ i j : Fin 4, i ≠ j ∧ ∃ a b : ℤ,
      (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) ∧ r = a • coordinate i + b • coordinate j := by
  constructor
  · rintro ⟨i, j, hij, rfl | rfl | rfl⟩
    · exact ⟨i, j, hij, 1, 1, Or.inl rfl, Or.inl rfl, by simp⟩
    · exact ⟨i, j, hij, 1, -1, Or.inl rfl, Or.inr rfl, by simp [sub_eq_add_neg]⟩
    · exact ⟨i, j, hij, -1, -1, Or.inr rfl, Or.inr rfl, by simp [sub_eq_add_neg]⟩
  · rintro ⟨i, j, hij, a, b, ha, hb, rfl⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact ⟨i, j, hij, Or.inl (by simp)⟩
    · exact ⟨i, j, hij, Or.inr (Or.inl (by simp [sub_eq_add_neg]))⟩
    · exact ⟨j, i, hij.symm, Or.inr (Or.inl (by simp [sub_eq_add_neg, add_comm]))⟩
    · exact ⟨i, j, hij, Or.inr (Or.inr (by simp [sub_eq_add_neg]))⟩

private theorem dot_signed (i j : Fin 4) (a b : ℤ) (x : VectorExponents) :
    (a • coordinate i + b • coordinate j) ⬝ᵥ x = a * x i + b * x j := by
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, coordinate_dot, coordinate_dot]
  rfl

private theorem signed_coordinate (i j : Fin 4) (a b : ℤ) (k : Fin 4) :
    (a • coordinate i + b • coordinate j) k =
      (if k = i then a else 0) + (if k = j then b else 0) := by
  change a * (Pi.single i 1 : VectorExponents) k + b * (Pi.single j 1 : VectorExponents) k = _
  simp only [Pi.single_apply]
  split <;> split <;> simp_all

private theorem vectorRoot_square {r : VectorExponents} (hr : r ∈ vectorRoots) :
    r ⬝ᵥ r = 2 := by
  obtain ⟨i, j, hij, a, b, ha, hb, rfl⟩ := (vectorRoots_signs r).mp hr
  rw [dot_signed, signed_coordinate, signed_coordinate]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [hij, hij.symm]

/-- The coroot is forced by the integral reflection law and the displayed roots. -/
private theorem coroot_eq_vectorRoot {r y : VectorExponents} (hr : r ∈ vectorRoots)
    (hpair : r ⬝ᵥ y = 2)
    (hreflect : ∀ b ∈ vectorRoots, b - (b ⬝ᵥ y) • r ∈ vectorRoots) :
    y = r := by
  have hdot (b : VectorExponents) (hb : b ∈ vectorRoots) :
      b ⬝ᵥ y = 0 ∨ b ⬝ᵥ y = b ⬝ᵥ r := by
    let n := b ⬝ᵥ y
    have hs := vectorRoot_square (hreflect b hb)
    change (b - n • r) ⬝ᵥ (b - n • r) = 2 at hs
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      vectorRoot_square hr, vectorRoot_square hb, dotProduct_comm r b] at hs
    simp only [zsmul_eq_mul] at hs
    have h : n * (n - b ⬝ᵥ r) = 0 := by
      have h₂ : 2 * (n * (n - b ⬝ᵥ r)) = 0 := by
        calc
          _ = (2 - n * (b ⬝ᵥ r) - n * ((b ⬝ᵥ r) - n * 2)) - 2 := by ring
          _ = 0 := sub_eq_zero.mpr hs
      exact (mul_eq_zero.mp h₂).resolve_left (by decide)
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  obtain ⟨i, j, hij, a, b, ha, hb, rfl⟩ := (vectorRoots_signs r).mp hr
  let r : VectorExponents := a • coordinate i + b • coordinate j
  have hi : r i = a := by change (a • coordinate i + b • coordinate j) i = a; rw [signed_coordinate]; simp [hij]
  have hj : r j = b := by change (a • coordinate i + b • coordinate j) j = b; rw [signed_coordinate]; simp [hij.symm]
  have hout (l : Fin 4) (hli : l ≠ i) (hlj : l ≠ j) : r l = 0 := by
    change (a • coordinate i + b • coordinate j) l = 0
    rw [signed_coordinate]
    simp [hli, hlj]
  have h₁ : a * y i + b * y j = 2 := (dot_signed _ _ _ _ _).symm.trans hpair
  have hneg : -b = 1 ∨ -b = -1 := by rcases hb with rfl | rfl <;> decide
  have horth : a • coordinate i + (-b) • coordinate j ∈ vectorRoots :=
    (vectorRoots_signs _).mpr ⟨i, j, hij, a, -b, ha, hneg, rfl⟩
  have h₂ := hdot _ horth
  change _ = 0 ∨ _ = (a • coordinate i + (-b) • coordinate j) ⬝ᵥ r at h₂
  rw [dot_signed, dot_signed, hi, hj] at h₂
  have hab : y i = a ∧ y j = b := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      norm_num at h₁ h₂ ⊢ <;> omega
  funext l
  change y l = r l
  by_cases hli : l = i
  · rw [hli, hi]
    exact hab.1
  by_cases hlj : l = j
  · rw [hlj, hj]
    exact hab.2
  have hpos : coordinate i + coordinate l ∈ vectorRoots :=
    ⟨i, l, Ne.symm hli, Or.inl rfl⟩
  have hneg : coordinate i - coordinate l ∈ vectorRoots :=
    ⟨i, l, Ne.symm hli, Or.inr (Or.inl rfl)⟩
  have hp := hdot _ hpos
  change _ = 0 ∨ _ = (coordinate i + coordinate l) ⬝ᵥ r at hp
  have hm := hdot _ hneg
  change _ = 0 ∨ _ = (coordinate i - coordinate l) ⬝ᵥ r at hm
  simp only [add_dotProduct, sub_dotProduct, coordinate_dot, hi, hout l hli hlj,
    hab.1, add_zero, sub_zero] at hp hm
  rw [hout l hli hlj]
  rcases ha with rfl | rfl <;> omega

section AttachedCoroots

open LinearAlgebraicGroups.Specs
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots pairing)
open scoped CategoryTheory.MonObj


variable {k : Type u} [Field k]
variable {G : Specs.AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
variable [CategoryTheory.IsCommMonObj T.group.X]

/-- The coroot comparison uses the actual integral root datum of the torus. -/
private theorem attachedCoroot_coordinates
    (C : Additive (Character T.group) ≃ₗ[ℤ] CharacterExponents)
    (Y : Additive (Cocharacter T.group) ≃ₗ[ℤ] evenSumLattice)
    (D : Specs.AbstractPairing.Datum T)
    (hpair : ∀ (χ : Character T.group) (ψ : Cocharacter T.group),
      pairing T.group χ ψ = latticePairing (C (Additive.ofMul χ)) (Y (Additive.ofMul ψ)))
    (hroots : Set.BijOn (fun χ : Character T.group => C (Additive.ofMul χ))
      (absoluteRoots T) rootCharacters) :
    ∀ α : Specs.AbstractPairing.Root T,
      vectorPullback (Y (D.rootDatum.coroot α)).val = C (Additive.ofMul α.val) := by
  classical
  let P := D.rootDatum
  have hroot (α : Specs.AbstractPairing.Root T) :
      ∃ x ∈ vectorRoots, vectorPullback x = C (P.root α) := by
    rw [D.root_eq]
    exact hroots.mapsTo α.property
  choose x hx hC using hroot
  have hP (β α : Specs.AbstractPairing.Root T) :
      P.toLinearMap (P.root β) (P.coroot α) = x β ⬝ᵥ (Y (P.coroot α)).val := by
    rw [D.root_eq, show P.coroot α = Additive.ofMul (Additive.toMul (P.coroot α)) from rfl,
      D.pairing_eq, hpair, ← D.root_eq, ← hC β, latticePairing_vectorPullback]
  intro α
  have h₂ : x α ⬝ᵥ (Y (P.coroot α)).val = 2 :=
    (hP α α).symm.trans (P.root_coroot_two α)
  have hreflect (b : VectorExponents) (hb : b ∈ vectorRoots) :
      b - (b ⬝ᵥ (Y (P.coroot α)).val) • x α ∈ vectorRoots := by
    obtain ⟨χ, hχ, hCb⟩ := hroots.surjOn (show vectorPullback b ∈ rootCharacters from ⟨b, hb, rfl⟩)
    let β : Specs.AbstractPairing.Root T := ⟨χ, hχ⟩
    have hβ : x β = b := by
      apply vectorPullback_injective
      rw [hC, D.root_eq]
      exact hCb
    let reflected := P.reflectionPerm α β
    have he := congrArg C (P.reflectionPerm_root α β)
    rw [map_sub, map_smul, hP, ← hC β, ← hC α, ← hC reflected, ← map_smul, ← map_sub] at he
    rw [← hβ, vectorPullback_injective he]
    exact hx reflected
  have hr := coroot_eq_vectorRoot (hx α) h₂ hreflect
  change vectorPullback (Y (P.coroot α)).val = C (Additive.ofMul α.val)
  rw [hr, hC, D.root_eq]

/-- Once the weights and perfect lattice pairing are identified, their
coroots fill the full cocharacter lattice of the actual split torus. -/
private theorem attachedCoroots_span
    (C : Additive (Character T.group) ≃ₗ[ℤ] CharacterExponents)
    (Y : Additive (Cocharacter T.group) ≃ₗ[ℤ] evenSumLattice)
    (D : Specs.AbstractPairing.Datum T)
    (hroots : Set.BijOn (fun χ : Character T.group => C (Additive.ofMul χ))
      (absoluteRoots T) rootCharacters)
    (hcoroots : ∀ α : Specs.AbstractPairing.Root T,
      vectorPullback (Y (D.rootDatum.coroot α)).val = C (Additive.ofMul α.val)) :
    SimplyConnectedLattice.corootLatticeOf D = ⊤ := by
  let f := evenSumLattice.subtype.comp Y.toLinearMap
  have hf : Function.Injective f := Subtype.val_injective.comp Y.injective
  have hfp (α : Specs.AbstractPairing.Root T) :
      vectorPullback (f (D.rootDatum.coroot α)) = C (Additive.ofMul α.val) := hcoroots α
  have h : f '' Set.range D.rootDatum.coroot = vectorRoots := by
    ext x
    constructor
    · rintro ⟨_, ⟨α, rfl⟩, rfl⟩
      obtain ⟨b, hb, he⟩ := hroots.mapsTo α.property
      have hb' : f (D.rootDatum.coroot α) = b :=
        vectorPullback_injective ((hfp α).trans he.symm)
      rwa [hb']
    · intro hx
      obtain ⟨χ, hχ, hCx⟩ := hroots.surjOn (show vectorPullback x ∈ rootCharacters from ⟨x, hx, rfl⟩)
      let α : Specs.AbstractPairing.Root T := ⟨χ, hχ⟩
      exact ⟨_, ⟨α, rfl⟩, vectorPullback_injective ((hfp α).trans hCx)⟩
  apply (Submodule.map_injective_of_injective hf)
  rw [SimplyConnectedLattice.corootLatticeOf, Submodule.map_span, h, Submodule.map_top]
  rw [show Submodule.span ℤ vectorRoots = evenSumLattice from corootSpan_proof]
  ext v
  constructor
  · intro hv
    obtain ⟨y, hy⟩ := Y.surjective ⟨v, hv⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, rfl⟩
    exact (Y y).property

end AttachedCoroots

end CorootCoordinates

section FieldPresentation

open SplitSpinSpecification
open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj TensorProduct


noncomputable section

private abbrev integralSpinRing :=
  SpinFunctor.CoordinateRing (integralForm 4) (hyperbolicBasis ℤ 4)

variable (k : Type u) [Field k]

private abbrev fieldSpinRing :=
  k ⊗[ℤ] integralSpinRing

private abbrev fieldSpinScheme : SchemeOver k :=
  (testSpec k).obj (op (CommAlgCat.of k (fieldSpinRing k)))

private abbrev spinUnitsAt (R : TestAlgebra k) :=
  SpinFunctor.Spin (integralForm 4) R (hyperbolicBasis ℤ 4)

private def spinCoordinatePoint (R : TestAlgebra k) :
    Points (fieldSpinScheme k) R ≃ (fieldSpinRing k →ₐ[k] R) :=
  (algSpec.fullyFaithful (R := CommRingCat.of k)).homEquiv.symm.trans
    { toFun := fun f => f.unop.hom
      invFun := fun f => (CommAlgCat.ofHom f).op
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private def spinPointEquiv (R : TestAlgebra k) :
    Points (fieldSpinScheme k) R ≃ spinUnitsAt k R :=
  (spinCoordinatePoint k R).trans
    ((AlgHom.liftEquiv ℤ k integralSpinRing R).symm.trans
      (SpinFunctor.pointEquiv (integralForm 4) (hyperbolicBasis ℤ 4) R))

private abbrev mapSpin {R S : TestAlgebra k} (f : R ⟶ S) :
    spinUnitsAt k R →* spinUnitsAt k S :=
  SpinFunctor.map (integralForm 4) (hyperbolicBasis ℤ 4) (f.hom.restrictScalars ℤ)

private theorem spinPointEquiv_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (p : Points (fieldSpinScheme k) R) :
    spinPointEquiv k S (mapPoints f p) = mapSpin k f (spinPointEquiv k R p) := by
  let F := testSpec k
  let g : op R ⟶ op (CommAlgCat.of k (fieldSpinRing k)) :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage p
  have hp : F.map g = p := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage p
  rw [← hp]
  change spinPointEquiv k S (F.map f.op ≫ F.map g) = _
  rw [← F.map_comp]
  let E (R : TestAlgebra k) := AlgHom.liftEquiv ℤ k integralSpinRing R
  have hc : (E S).symm ((f.op ≫ g).unop.hom) =
      (f.hom.restrictScalars ℤ).comp ((E R).symm g.unop.hom) := by
    ext a
    rfl
  change SpinFunctor.pointEquiv (integralForm 4) _ S
    ((E S).symm (((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      (F.map (f.op ≫ g))).unop.hom)) =
      mapSpin k f (SpinFunctor.pointEquiv (integralForm 4) _ R
        ((E R).symm (((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
          (F.map g)).unop.hom)))
  rw [Functor.FullyFaithful.preimage_map, Functor.FullyFaithful.preimage_map, hc]
  exact SpinFunctor.pointEquiv_natural (integralForm 4) (hyperbolicBasis ℤ 4) _ _

private def spinNaturalLaw : NaturalGroupLaw (fieldSpinScheme k) where
  group R := (spinPointEquiv k R).group
  map_one {R S} f := by
    apply (spinPointEquiv k S).injective
    change spinPointEquiv k S (mapPoints f ((spinPointEquiv k R).symm 1)) =
      spinPointEquiv k S ((spinPointEquiv k S).symm 1)
    rw [spinPointEquiv_natural, Equiv.apply_symm_apply, Equiv.apply_symm_apply, map_one]
  map_mul {R S} f p q := by
    apply (spinPointEquiv k S).injective
    change spinPointEquiv k S (mapPoints f ((spinPointEquiv k R).symm
      (spinPointEquiv k R p * spinPointEquiv k R q))) =
      spinPointEquiv k S ((spinPointEquiv k S).symm
        (spinPointEquiv k S (mapPoints f p) * spinPointEquiv k S (mapPoints f q)))
    rw [spinPointEquiv_natural, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      map_mul, spinPointEquiv_natural, spinPointEquiv_natural]

private theorem fieldSpinAffine : IsAffine (fieldSpinScheme k).left := by
  change IsAffine (Spec (CommRingCat.of (fieldSpinRing k)))
  infer_instance

private abbrev spinGroupObj : GrpObj (fieldSpinScheme k) :=
  (groupLawEquiv (fieldSpinScheme k) (fieldSpinAffine k)).symm (spinNaturalLaw k)

private def fieldSpinGroup : Specs.AffineAlgebraicGroup k := by
  letI := spinGroupObj k
  refine ⟨Grp.mk (fieldSpinScheme k), fieldSpinAffine k, ?_, ?_⟩
  · change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k (fieldSpinRing k))))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    change RingHom.FiniteType (algebraMap k (fieldSpinRing k))
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  · change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k (fieldSpinRing k))))
    infer_instance

private def fieldSpinPoints (R : TestAlgebra k) :
    Points (fieldSpinGroup k).val.X R ≃* spinUnitsAt k R :=
  { spinPointEquiv k R with
    map_mul' := fun p q => by
      change spinPointEquiv k R (((inducedGroupLaw _ (spinGroupObj k)).group R).mul p q) = _
      have h : inducedGroupLaw (fieldSpinScheme k) (spinGroupObj k) = spinNaturalLaw k :=
        (groupLawEquiv (fieldSpinScheme k) (fieldSpinAffine k)).apply_symm_apply _
      rw [h]
      exact (spinPointEquiv k R).apply_symm_apply _ }

private def fieldSpinRepresentation (R : TestAlgebra k) :
    Points (fieldSpinGroup k).val.X R →* (ScalarClifford 4 R)ˣ :=
  (SpinFunctor.spinSubgroup (integralForm 4) R (hyperbolicBasis ℤ 4)).subtype.comp
    (fieldSpinPoints k R).toMonoidHom

private theorem fieldSpinPresentation : SpinPointPresentation (fieldSpinGroup k) (fieldSpinRepresentation k) := by
  refine ⟨fun R => ⟨Subtype.val_injective.comp (fieldSpinPoints k R).injective, ?_⟩, ?_⟩
  · ext a
    constructor
    · rintro ⟨p, rfl⟩
      exact (fieldSpinPoints k R p).property
    · intro ha
      obtain ⟨p, hp⟩ := (fieldSpinPoints k R).surjective ⟨a, ha⟩
      exact ⟨p, congrArg Subtype.val hp⟩
  · intro R S f p
    exact congrArg Subtype.val (spinPointEquiv_natural k f p)

section Geometry

open scoped Matrix
open CategoryTheory.Limits

open private standardDet StandardRing translateSpin integralSwitch switchOpen
  switchOpen_cover switchOpen_point standardOpen standardOpen_point standardRing_smooth
  splitSpinScheme splitSpinPointEquiv integralSwitch_action_after_map action_matrix_mul
  chartPoint chartPoint_action spec_basicOpen_iff ChartIndex LargeRing largeDenominator
  blockOfValues unitVariable factorVariables eval_largeDenominator standardRing_retract
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin

private def spinSwitch (J : EvenSwitches 4) : integralSpinRing ≃ₐ[ℤ] integralSpinRing :=
  CommAlgCat.algEquivOfIso
    ((algSpec.fullyFaithful (R := CommRingCat.of ℤ)).preimageIso
      (translateSpin 4 (integralSwitch 4 J))).unop

private def switchDenominator (J : EvenSwitches 4) : integralSpinRing :=
  spinSwitch J (standardDet 4)

private theorem switchOpen_eq_basicOpen (J : EvenSwitches 4) :
    switchOpen 4 J = PrimeSpectrum.basicOpen (switchDenominator J) := by
  have h : (algSpec (CommRingCat.of ℤ)).map (.op (CommAlgCat.ofHom
      (spinSwitch J).toAlgHom)) = (translateSpin 4 (integralSwitch 4 J)).hom :=
    (algSpec.fullyFaithful (R := CommRingCat.of ℤ)).map_preimage _
  rw [switchOpen, ← h]
  rfl

private theorem switchDenominators_span :
    Ideal.span (Set.range switchDenominator) = ⊤ := by
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
  have h := switchOpen_cover 4
  simp_rw [switchOpen_eq_basicOpen] at h
  exact h

private abbrev fieldDenominator (a : integralSpinRing) : fieldSpinRing k :=
  (1 : k) ⊗ₜ[ℤ] a

private abbrev fieldOpen (a : integralSpinRing) : (fieldSpinScheme k).left.Opens :=
  PrimeSpectrum.basicOpen (fieldDenominator k a)

private theorem fieldOpens_cover : (⨆ J, fieldOpen k (switchDenominator J)) = ⊤ := by
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr
  have h := congrArg (Ideal.map (Algebra.TensorProduct.includeRight :
    integralSpinRing →ₐ[ℤ] fieldSpinRing k).toRingHom) switchDenominators_span
  rw [Ideal.map_top, Ideal.map_span, ← Set.range_comp] at h
  exact h

private abbrev integralBaseChange (K A : Type*) [CommRing K] [CommRing A]
    [Algebra ℤ K] [Algebra ℤ A] :=
  letI : Module ℤ K := Algebra.toModule
  letI : Module ℤ A := Algebra.toModule
  K ⊗[ℤ] A

private def chartScalarChange (a : integralSpinRing) :
    integralBaseChange k (Localization.Away a) ≃ₐ[k] Localization.Away (fieldDenominator k a) :=
  IsLocalization.Away.tensorProductEquivTMulRight ℤ k a (Localization.Away a)

private def switchChartIso (J : EvenSwitches 4) :
    StandardRing 4 ≃ₐ[ℤ] Localization.Away (switchDenominator J) :=
  IsLocalization.algEquivOfAlgEquiv _ _ (spinSwitch J) (by
    change (Submonoid.powers (standardDet 4)).map (spinSwitch J).toMonoidHom =
      Submonoid.powers (switchDenominator J)
    rw [Submonoid.map_powers]
    rfl)

private theorem standardChart_smooth : Algebra.Smooth ℤ (StandardRing 4) := by
  have := standardRing_smooth 4 (by decide)
  have h : Smooth (Spec.map (CommRingCat.ofHom (algebraMap ℤ (StandardRing 4)))) :=
    SmoothOfRelativeDimension.smooth (2 * 4 ^ 2 - 4) _
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at h
  exact RingHom.smooth_algebraMap.mp h

private theorem fieldOpen_smooth (a : integralSpinRing) (h : Algebra.Smooth ℤ (Localization.Away a)) :
    Smooth ((fieldOpen k a).ι ≫ (fieldSpinScheme k).hom) := by
  let e := basicOpenIsoSpecAway (R := CommRingCat.of (fieldSpinRing k)) (fieldDenominator k a)
  have := h
  have := Algebra.Smooth.of_equiv (chartScalarChange k a)
  have hs : Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap k (Localization.Away (fieldDenominator k a))))) := by
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    change (algebraMap k (Localization.Away (fieldDenominator k a))).Smooth
    exact RingHom.smooth_algebraMap.mpr inferInstance
  let B := Localization.Away (fieldDenominator k a)
  let j := Spec.map (CommRingCat.ofHom (algebraMap (fieldSpinRing k) B))
  have hι : e.hom ≫ j = (fieldOpen k a).ι :=
    basicOpenIsoSpecAway_hom_SpecMap
      (R := CommRingCat.of (fieldSpinRing k)) (fieldDenominator k a)
  have hcomp : j ≫ (fieldSpinScheme k).hom =
      Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
    change Spec.map (CommRingCat.ofHom (algebraMap (fieldSpinRing k) B)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (fieldSpinRing k))) = _
    rw [← Spec.map_comp]
    congr 1
  have heq : (fieldOpen k a).ι ≫ (fieldSpinScheme k).hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k B)) :=
    (congrArg (fun f => f ≫ (fieldSpinScheme k).hom) hι.symm).trans
      ((Category.assoc e.hom j (fieldSpinScheme k).hom).trans (congrArg (e.hom ≫ ·) hcomp))
  have : IsOpenImmersion e.hom := inferInstance
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) := hs
  exact heq.symm ▸ (smooth_comp e.hom _)

private theorem fieldSpin_smooth : Smooth (fieldSpinGroup k).val.X.hom := by
  change Smooth (fieldSpinScheme k).hom
  let : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth.{u}) _ (fieldOpens_cover k)
  intro J
  have := standardChart_smooth
  exact fieldOpen_smooth k _ (Algebra.Smooth.of_equiv (switchChartIso J))

private theorem largeChart_domain : IsDomain (integralBaseChange k (LargeRing 4)) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := ChartIndex 4) ℤ k
  let : IsDomain (k ⊗[ℤ] MvPolynomial (ChartIndex 4) ℤ) :=
    Function.Injective.isDomain e e.injective
  have hn : (1 : k) ⊗ₜ[ℤ] largeDenominator 4 ≠ 0 := by
    intro h
    let x : ChartIndex 4 → k := Sum.elim (factorVariables (0 : Block 4 k) 0 1) (fun _ => 1)
    have hx : blockOfValues x = 1 := rfl
    have he := congrArg (fun z => MvPolynomial.aeval x (e z)) h
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul, map_zero, map_zero] at he
    rw [MvPolynomial.aeval_map_algebraMap (R := ℤ) k, eval_largeDenominator, hx, Matrix.det_one] at he
    simp [x] at he
  let : IsDomain (Localization.Away ((1 : k) ⊗ₜ[ℤ] largeDenominator 4)) :=
    IsLocalization.Away.isDomain _ hn
  let e' := IsLocalization.Away.tensorProductEquivTMulRight ℤ k (largeDenominator 4) (LargeRing 4)
  exact Function.Injective.isDomain e' e'.injective

private theorem standardChart_domain : IsDomain (integralBaseChange k (StandardRing 4)) := by
  obtain ⟨f, g, hg⟩ := standardRing_retract (0 : Fin 4)
  let := largeChart_domain k
  let fK := Algebra.TensorProduct.map (AlgHom.id k k) f
  let gK := Algebra.TensorProduct.map (AlgHom.id k k) g
  have he : gK.comp fK = AlgHom.id k _ := by
    change (Algebra.TensorProduct.map (AlgHom.id k k) g).comp
      (Algebra.TensorProduct.map (AlgHom.id k k) f) = _
    rw [← Algebra.TensorProduct.map_id_comp, hg, Algebra.TensorProduct.map_id]
  exact Function.Injective.isDomain fK
    (Function.LeftInverse.injective (g := gK) fun x => DFunLike.congr_fun he x)

private theorem fieldOpen_connected (a : integralSpinRing)
    (e : StandardRing 4 ≃ₐ[ℤ] Localization.Away a) :
    _root_.IsConnected (fieldOpen k a).1 := by
  let eK := (Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) e).trans (chartScalarChange k a)
  have := standardChart_domain k
  have : IsDomain (Localization.Away (fieldDenominator k a)) :=
    Function.Injective.isDomain eK.symm eK.symm.injective
  let iso := basicOpenIsoSpecAway (R := CommRingCat.of (fieldSpinRing k)) (fieldDenominator k a)
  exact isConnected_iff_connectedSpace.mpr
    (iso.hom.homeomorph.connectedSpace_iff.mpr inferInstance)

private theorem integralChart_overlap (J : EvenSwitches 4) :
    ∃ f : integralSpinRing →ₐ[ℤ] ℤ, IsUnit (f (standardDet 4)) ∧ IsUnit (f (switchDenominator J)) := by
  obtain ⟨P, hP, hd⟩ := SplitSpin.evenSwitchOverlap 4 ℤ J
  let p : ChartParameters 4 ℤ := ⟨P, 0, 1, 1, hP, by intro x; simp, by simp⟩
  let A := CommAlgCat.of ℤ ℤ
  let a := (splitSpinPointEquiv 4 A).symm ⟨(chartPoint p).val, (chartPoint p).property.1⟩
  have hm : HasActionMatrix 4 ((splitSpinPointEquiv 4 A) a).val (lower P) := by
    dsimp only [a]
    rw [MulEquiv.apply_symm_apply]
    have h := chartPoint_action p
    change HasActionMatrix 4 (chartPoint p).val (lower P * middle 1 * upper 0) at h
    simpa [middle, upper] using h
  have h₁ := (standardOpen_point 4 A a).mpr ⟨_, hm, by simp [lower]⟩
  have h₂ := (switchOpen_point 4 J A a).mpr
    ⟨_, by rw [map_mul]; exact action_matrix_mul (integralSwitch_action_after_map 4 J A) hm, hd⟩
  obtain ⟨f, hf⟩ := (algSpec.fullyFaithful (R := CommRingCat.of ℤ)).map_surjective a
  rw [← hf] at h₁ h₂
  rw [switchOpen_eq_basicOpen] at h₂
  exact ⟨f.unop.hom, (spec_basicOpen_iff _).mp h₁, (spec_basicOpen_iff _).mp h₂⟩

private theorem fieldChart_overlap (J : EvenSwitches 4) :
    ((fieldOpen k (standardDet 4)).1 ∩ (fieldOpen k (switchDenominator J)).1).Nonempty := by
  obtain ⟨f, h₁, h₂⟩ := integralChart_overlap J
  let fK := AlgHom.liftEquiv ℤ k integralSpinRing k ((Algebra.ofId ℤ k).comp f)
  have he (a : integralSpinRing) : fK (fieldDenominator k a) = algebraMap ℤ k (f a) := by
    simp [fK]
  refine ⟨PrimeSpectrum.comap fK.toRingHom (IsLocalRing.closedPoint k), ?_, ?_⟩
  · change fK (fieldDenominator k (standardDet 4)) ∉ IsLocalRing.maximalIdeal k
    rw [he]
    intro hm
    exact (IsLocalRing.maximalIdeal.isMaximal k).ne_top
      ((IsLocalRing.maximalIdeal k).eq_top_of_isUnit_mem hm (h₁.map (algebraMap ℤ k)))
  · change fK (fieldDenominator k (switchDenominator J)) ∉ IsLocalRing.maximalIdeal k
    rw [he]
    intro hm
    exact (IsLocalRing.maximalIdeal.isMaximal k).ne_top
      ((IsLocalRing.maximalIdeal k).eq_top_of_isUnit_mem hm (h₂.map (algebraMap ℤ k)))

private theorem fieldSpin_connected : ConnectedSpace (fieldSpinScheme k).left := by
  let C := (fieldOpen k (standardDet 4)).1
  let U (J : EvenSwitches 4) := (fieldOpen k (switchDenominator J)).1
  have hc : _root_.IsConnected C := fieldOpen_connected k _ (AlgEquiv.refl)
  have hu : (⋃ J, C ∪ U J) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⨆ J, fieldOpen k (switchDenominator J) := by
      rw [fieldOpens_cover]
      exact trivial
    obtain ⟨J, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨J, Or.inr hj⟩
  obtain ⟨x, hx⟩ := hc.nonempty
  have hi : (⋂ J, C ∪ U J).Nonempty := ⟨x, Set.mem_iInter.mpr fun _ => Or.inl hx⟩
  rw [connectedSpace_iff_univ, ← hu]
  refine ⟨⟨x, Set.mem_iUnion.mpr ⟨⟨∅, by simp⟩, Or.inl hx⟩⟩,
    isPreconnected_iUnion hi fun J => ?_⟩
  exact (hc.union (fieldChart_overlap k J) (fieldOpen_connected k _ (switchChartIso J))).isPreconnected

private theorem fieldSpin_geometricallyConnected : GeometricallyConnected (fieldSpinGroup k).val.X.hom := by
  constructor
  apply (geometrically_iff_of_isClosedUnderIsomorphisms (P := fun X : Scheme => ConnectedSpace X)).mpr
  intro K _ y
  let a := (Spec.fullyFaithful.preimage y).unop
  let : Algebra k K := a.hom.toAlgebra
  have hy : y = Spec.map (CommRingCat.ofHom (algebraMap k K)) :=
    (Spec.fullyFaithful.map_preimage y).symm
  let b := Algebra.TensorProduct.cancelBaseChange ℤ k K K integralSpinRing
  change ConnectedSpace ↥(pullback (C := Scheme.{u})
    (Spec.map (CommRingCat.ofHom (algebraMap k (fieldSpinRing k)))) y)
  rw [hy]
  let e := pullbackSymmetry _ _ ≪≫ pullbackSpecIso k K (fieldSpinRing k) ≪≫
    Scheme.Spec.mapIso b.symm.toRingEquiv.toCommRingCatIso.op
  exact e.hom.homeomorph.connectedSpace_iff.mpr (fieldSpin_connected K)

end Geometry

end

end FieldPresentation

section DiagonalLift

open SplitSpinSpecification
open CliffordAlgebra Module
open scoped Matrix BigOperators TensorProduct

noncomputable section

open private action_matrix_unique splitBasis splitE splitF splitScalarUnit_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin
open private changeCoefficients_vector changeModule_basis from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

variable {R : Type u} [CommRing R] [Algebra ℤ R]

private theorem clifford_ext_wedges {a b : ScalarClifford 4 R}
    (h : ∀ I : Finset (Fin 4), exteriorModel R a (eBasis R I) = exteriorModel R b (eBasis R I)) :
    a = b :=
  (exteriorModel R).injective ((eBasis R).ext h)

private def diagonalUnit (t : DiagonalPoints R) :
    SpinFunctor.Spin (integralForm 4) R (hyperbolicBasis ℤ 4) :=
  ⟨(diagonal_lift t).choose, (diagonal_lift t).choose_spec.1⟩

private theorem diagonalUnit_action (t : DiagonalPoints R) :
    HasActionMatrix 4 (diagonalUnit t).val (middle (diagonalBlock t)) :=
  (diagonal_lift t).choose_spec.2.1

private theorem diagonalUnit_wedge (t : DiagonalPoints R) (I : Finset (Fin 4)) :
    exteriorModel R (diagonalUnit t).val (eBasis R I) =
      ((scalar t * ∏ i ∈ I, scales t i : Rˣ) : R) • eBasis R I :=
  (diagonal_lift t).choose_spec.2.2 I

private def diagonalLift :
    DiagonalPoints R →* SpinFunctor.Spin (integralForm 4) R (hyperbolicBasis ℤ 4) where
  toFun := diagonalUnit
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    apply clifford_ext_wedges
    intro I
    change exteriorModel R (diagonalUnit (1 : DiagonalPoints R)).val (eBasis R I) = exteriorModel R 1 (eBasis R I)
    rw [diagonalUnit_wedge, map_one]
    simp [scalar, scales]
  map_mul' t s := by
    apply Subtype.ext
    apply Units.ext
    apply clifford_ext_wedges
    intro I
    change exteriorModel R (diagonalUnit (t * s)).val (eBasis R I) =
      exteriorModel R ((diagonalUnit t).val.val * (diagonalUnit s).val.val) (eBasis R I)
    rw [diagonalUnit_wedge, map_mul, Module.End.mul_apply, diagonalUnit_wedge,
      LinearMap.map_smul, diagonalUnit_wedge, smul_smul]
    congr 1
    change (↑((scalar t * scalar s) * ∏ i ∈ I, scales t i * scales s i) : R) = _
    rw [Finset.prod_mul_distrib]
    simp only [Units.val_mul]
    ring

private theorem diagonalLift_injective : Function.Injective (diagonalLift (R := R)) := by
  intro t s h
  change diagonalUnit t = diagonalUnit s at h
  have hM := action_matrix_unique (diagonalUnit_action t)
    (h.symm ▸ diagonalUnit_action s)
  apply Subtype.ext
  apply Prod.ext
  · funext i
    apply Units.ext
    have h₁ := congrArg (fun M : Matrix (PairIndex 4) (PairIndex 4) R => M (.inl i) (.inl i)) hM
    simpa [middle, diagonalBlock, scales] using h₁
  · apply Units.ext
    have h₁ : exteriorModel R (diagonalUnit t).val (eBasis R ∅) =
        exteriorModel R (diagonalUnit s).val (eBasis R ∅) := by rw [h]
    simp only [diagonalUnit_wedge, Finset.prod_empty, mul_one] at h₁
    simpa [scalar] using congrArg ((eBasis R).coord ∅) h₁

private def diagonalFactor (t : DiagonalPoints R) (i : Fin 4) : ScalarClifford 4 R :=
  1 + (algebraMap R _ (scales t i : R) - 1) * (creation i * contraction i)

private theorem diagonalFactor_wedge (t : DiagonalPoints R) (i : Fin 4) (I : Finset (Fin 4)) :
    exteriorModel R (diagonalFactor t i) (eBasis R I) =
      (if i ∈ I then (scales t i : R) else 1) • eBasis R I := by
  rw [diagonalFactor, map_add, map_one, map_mul, map_sub, map_one, (exteriorModel R).commutes]
  rw [show algebraMap R (Module.End R (ExteriorSpace R)) (scales t i : R) - 1 =
      algebraMap R _ ((scales t i : R) - 1) from by rw [map_sub, map_one]]
  change eBasis R I + ((scales t i : R) - 1) •
    exteriorModel R (creation i * contraction i) (eBasis R I) = _
  rw [occupation]
  by_cases h : i ∈ I
  · simp only [h, ite_true, one_smul]
    calc
      _ = (1 + ((scales t i : R) - 1)) • eBasis R I := by rw [add_smul, one_smul]
      _ = _ := by simp
  · simp [h]

private theorem diagonalFactors_wedge (t : DiagonalPoints R) (I : Finset (Fin 4))
    (L : List (Fin 4)) :
    exteriorModel R ((L.map (diagonalFactor t)).prod) (eBasis R I) =
      ((L.map fun i => if i ∈ I then (scales t i : R) else 1).prod) • eBasis R I := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ih,
      LinearMap.map_smul, diagonalFactor_wedge, smul_smul, mul_comm]

private theorem diagonalUnit_val (t : DiagonalPoints R) :
    (diagonalUnit t).val.val = algebraMap R _ (scalar t : R) *
      ((List.finRange 4).map (diagonalFactor t)).prod := by
  apply clifford_ext_wedges
  intro I
  rw [diagonalUnit_wedge, map_mul, (exteriorModel R).commutes]
  change _ = (scalar t : R) • exteriorModel R ((List.finRange 4).map (diagonalFactor t)).prod (eBasis R I)
  rw [diagonalFactors_wedge, smul_smul, Units.val_mul]
  congr 1
  rw [← List.prod_toFinset _ (List.nodup_finRange 4)]
  have h : (List.finRange 4).toFinset = Finset.univ := by
    ext i
    simp
  rw [h, ← Finset.prod_filter]
  have hp : Finset.univ.filter (fun i : Fin 4 => i ∈ I) = I := by ext; simp
  rw [hp]
  exact congrArg ((scalar t : R) * ·) (map_prod (Units.coeHom R) (scales t) I)

open private action_matrix_unit_det factor_blocks chartPoint chartPoint_action chartPoint_surjective
  factor_topLeft tensor_ratio tensor_scalar_lift IsTensorLift IsTensorLift.mul splitScalarUnit
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin
open private scalar_tensor_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

private theorem diagonalLift_exists_of_matrix
    (a : SpinFunctor.Spin (integralForm 4) R (hyperbolicBasis ℤ 4))
    {M : Matrix (PairIndex 4) (PairIndex 4) R} (hm : HasActionMatrix 4 a.val M)
    (hd : ∀ i j, i ≠ j → M i j = 0) :
    ∃ t : DiagonalPoints R, diagonalLift t = a := by
  classical
  have hdiagonal : M = Matrix.diagonal (fun i => M i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, hd i j hij]
  have hdet : IsUnit (∏ i, M i i) := by
    rw [← Matrix.det_diagonal, ← hdiagonal]
    exact action_matrix_unit_det hm
  have hunit (i : Fin 4) : IsUnit (M (.inl i) (.inl i)) :=
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => M i i) (Finset.mem_univ (Sum.inl i : PairIndex 4))) hdet
  let w (i : Fin 4) := (hunit i).unit
  let A := Matrix.diagonal fun i => (w i : R)
  have hA : M.toBlocks₁₁ = A := by
    ext i j
    by_cases hij : i = j
    · subst j
      change M (.inl i) (.inl i) = Matrix.diagonal (fun i => (w i : R)) i i
      rw [Matrix.diagonal_apply_eq]
      exact (hunit i).unit_spec.symm
    · simpa [A, Matrix.toBlocks₁₁, Matrix.diagonal_apply_ne _ hij] using hd (.inl i) (.inl j)
        (fun he => hij (Sum.inl.inj he))
  have hdetA : IsUnit A.det := by
    rw [Matrix.det_diagonal]
    exact ⟨∏ i, w i, map_prod (Units.coeHom R) _ _⟩
  have hdetM : IsUnit M.toBlocks₁₁.det := hA.symm ▸ hdetA
  obtain ⟨p, hp⟩ := chartPoint_surjective 4 R ⟨a.val, a.property, M, hm, hdetM⟩
  have hpval : (chartPoint p).val = a.val := congrArg Subtype.val hp
  have hfac := action_matrix_unique hm (hpval ▸ chartPoint_action p)
  have hPA : p.A = A := (factor_topLeft p.P p.Q p.A).symm.trans
    ((congrArg Matrix.toBlocks₁₁ hfac).symm.trans hA)
  have hpos : M.toBlocks₁₂ = 0 := by
    ext i j
    exact hd (.inl i) (.inr j) (by simp)
  have hneg : M.toBlocks₂₁ = 0 := by
    ext i j
    exact hd (.inr i) (.inl j) (by simp)
  rw [factor_blocks, hPA] at hfac
  have hPQ : A * p.Q = 0 := (congrArg Matrix.toBlocks₁₂ hfac).symm.trans hpos
  have hQP : p.P * A = 0 := (congrArg Matrix.toBlocks₂₁ hfac).symm.trans hneg
  rw [hPQ, hQP, zero_mul, zero_add] at hfac
  let t : DiagonalPoints R := ⟨(w, p.u), by
    change p.u ^ 2 * (∏ i, w i) = 1
    apply Units.ext
    simpa [hPA, A, Matrix.det_diagonal] using p.normOne⟩
  have htM : M = middle (diagonalBlock t) := hfac
  obtain ⟨z, hz⟩ := tensor_ratio (htM ▸ hm) (diagonalUnit_action t)
  have htLift : IsTensorLift (middle (diagonalBlock t)) (diagonalUnit t).val 1 :=
    ⟨(diagonalUnit t).property.1, by simpa only [map_one] using (diagonalUnit t).property.2.1,
      diagonalUnit_action t⟩
  have hn := (IsTensorLift.mul (tensor_scalar_lift (m := 4) z) htLift).2.1
  rw [← hz, mul_one] at hn
  have hz2 : z ^ 2 = 1 := by
    apply Units.ext
    change (z : R) ^ 2 = 1
    apply scalar_tensor_injective (integralForm 4) R (hyperbolicBasis ℤ 4)
    rw [← hn, map_one]
    exact a.property.2.1
  let q : DiagonalPoints R := ⟨(w, z * scalar t), by
    change (z * scalar t) ^ 2 * ∏ i, scales t i = 1
    rw [mul_pow, hz2, one_mul]
    exact t.property⟩
  refine ⟨q, Subtype.ext (Units.ext ?_)⟩
  change (diagonalUnit q).val.val = a.val.val
  rw [hz]
  apply clifford_ext_wedges
  intro I
  rw [diagonalUnit_wedge, Units.val_mul]
  change _ = exteriorModel R (algebraMap R _ (z : R) * (diagonalUnit t).val.val) (eBasis R I)
  rw [map_mul, (exteriorModel R).commutes]
  change _ = (z : R) • exteriorModel R (diagonalUnit t).val (eBasis R I)
  rw [diagonalUnit_wedge, smul_smul]
  change (↑((z * scalar t) * ∏ i ∈ I, scales t i) : R) • eBasis R I = _
  simp only [Units.val_mul, mul_assoc]

variable {S : Type u} [CommRing S] [Algebra ℤ S]

private theorem coefficientMap_creation (f : R →ₐ[ℤ] S) (i : Fin 4) :
    SpinSpecification.coefficientMap (integralForm 4) R f (creation i) = creation i := by
  change SpinFunctor.changeCoefficients (integralForm 4) f
    (SpinSpecification.vectors (integralForm 4) R (splitE i)) = _
  rw [changeCoefficients_vector]
  apply congrArg (SpinSpecification.vectors (integralForm 4) S)
  exact changeModule_basis (hyperbolicBasis ℤ 4) f (toLex (Sum.inl i))

private theorem coefficientMap_contraction (f : R →ₐ[ℤ] S) (i : Fin 4) :
    SpinSpecification.coefficientMap (integralForm 4) R f (contraction i) = contraction i := by
  change SpinFunctor.changeCoefficients (integralForm 4) f
    (SpinSpecification.vectors (integralForm 4) R (splitF i)) = _
  rw [changeCoefficients_vector]
  apply congrArg (SpinSpecification.vectors (integralForm 4) S)
  exact changeModule_basis (hyperbolicBasis ℤ 4) f (toLex (Sum.inr i))

private theorem coefficientMap_scalar (f : R →ₐ[ℤ] S) (x : Rˣ) :
    SpinSpecification.coefficientMap (integralForm 4) R f (algebraMap R _ (x : R)) =
      algebraMap S _ (f (x : R)) :=
  congrArg Units.val (splitScalarUnit_natural (m := 4) f x)

private theorem diagonalFactor_map (f : R →ₐ[ℤ] S) (t : DiagonalPoints R) (i : Fin 4) :
    SpinSpecification.coefficientMap (integralForm 4) R f (diagonalFactor t i) =
      diagonalFactor (mapDiagonal f.toRingHom t) i := by
  simp only [diagonalFactor, map_add, map_one, map_mul, coefficientMap_scalar, coefficientMap_creation,
    coefficientMap_contraction, map_sub]
  rfl

private theorem diagonalLift_natural (f : R →ₐ[ℤ] S) (t : DiagonalPoints R) :
    SpinFunctor.map (integralForm 4) (hyperbolicBasis ℤ 4) f (diagonalLift t) =
      diagonalLift (mapDiagonal f.toRingHom t) := by
  apply Subtype.ext
  apply Units.ext
  change SpinSpecification.coefficientMap (integralForm 4) R f (diagonalUnit t).val.val =
    (diagonalUnit (mapDiagonal f.toRingHom t)).val.val
  rw [diagonalUnit_val, diagonalUnit_val, map_mul, coefficientMap_scalar, map_list_prod, List.map_map]
  have hmap : SpinSpecification.coefficientMap (integralForm 4) R f ∘ diagonalFactor t =
      diagonalFactor (mapDiagonal f.toRingHom t) := funext (diagonalFactor_map f t)
  rw [hmap]
  rfl

end

end DiagonalLift

noncomputable section

/-- Free scalar and upper vector exponents, in position order. -/
private def freeCoordinates : CharacterExponents ≃ₗ[ℤ] VectorExponents where
  toFun x := Fin.cases x.1 x.2
  invFun x := (x 0, fun i => x i.succ)
  left_inv _ := rfl
  right_inv _ := funext (fun i => Fin.cases rfl (fun _ => rfl) i)
  map_add' _ _ := funext (fun i => Fin.cases rfl (fun _ => rfl) i)
  map_smul' _ _ := funext (fun i => Fin.cases rfl (fun _ => rfl) i)

private def fromFreeCochar (x : CharacterExponents) : evenSumLattice :=
  ⟨Fin.cases (-2 * x.1 - ∑ i, x.2 i) x.2, by
    change ((∑ i : Fin 4, Fin.cases (-2 * x.1 - ∑ i, x.2 i) x.2 i : ℤ) : ZMod 2) = 0
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    use -x.1
    rw [Fin.sum_univ_succ]
    change -2 * x.1 - ∑ i, x.2 i + ∑ i, x.2 i = 2 * -x.1
    ring⟩

private theorem fromFreeCochar_sum (x : CharacterExponents) :
    ∑ i, (fromFreeCochar x).val i = -2 * x.1 := by
  rw [Fin.sum_univ_succ]
  change -2 * x.1 - ∑ i, x.2 i + ∑ i, x.2 i = -2 * x.1
  exact sub_add_cancel _ _

private def freeCocharCoordinates : CharacterExponents ≃ₗ[ℤ] evenSumLattice where
  toFun := fromFreeCochar
  invFun := fun y => (-(∑ i, y.val i) / 2, fun i => y.val i.succ)
  left_inv x := by
    apply Prod.ext
    · change -(∑ i, (fromFreeCochar x).val i) / 2 = x.1
      rw [fromFreeCochar_sum]
      omega
    · rfl
  right_inv y := by
    obtain ⟨s, hs⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (∑ i, y.val i) 2).mp y.property
    change (∑ i, y.val i) = 2 * s at hs
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    change -2 * (-(∑ i, y.val i) / 2) - ∑ i : Fin 3, y.val i.succ = y.val 0
    rw [hs, show -(2 * s) / 2 = -s by omega]
    rw [Fin.sum_univ_succ] at hs
    omega
  map_add' x z := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    change -2 * (x.1 + z.1) - ∑ i, (x.2 i + z.2 i) =
      (-2 * x.1 - ∑ i, x.2 i) + (-2 * z.1 - ∑ i, z.2 i)
    rw [Finset.sum_add_distrib]
    ring
  map_smul' n x := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    change -2 * (n * x.1) - ∑ i, n * x.2 i = n * (-2 * x.1 - ∑ i, x.2 i)
    rw [← Finset.mul_sum]
    ring

private theorem freeCochar_pairing (x q : CharacterExponents) :
    latticePairing x (freeCocharCoordinates q) = x.1 * q.1 + ∑ i, x.2 i * q.2 i := by
  change x.1 * (-(∑ i, (fromFreeCochar q).val i) / 2) + (∑ i, x.2 i * q.2 i) = _
  rw [fromFreeCochar_sum, show -(-2 * q.1) / 2 = q.1 by omega]

private def exponentBasis : Module.Basis (Fin 4) ℤ CharacterExponents :=
  (Pi.basisFun ℤ (Fin 4)).map freeCoordinates.symm

private def latticeDual : Module.Dual ℤ CharacterExponents ≃ₗ[ℤ] evenSumLattice :=
  exponentBasis.dualBasis.equivFun.trans (freeCoordinates.symm.trans freeCocharCoordinates)

private theorem latticeDual_pairing (f : Module.Dual ℤ CharacterExponents) (x : CharacterExponents) :
    latticePairing x (latticeDual f) = f x := by
  change latticePairing x (freeCocharCoordinates
    (freeCoordinates.symm (exponentBasis.dualBasis.equivFun f))) = _
  rw [freeCochar_pairing]
  change x.1 * exponentBasis.dualBasis.equivFun f 0 +
    (∑ i : Fin 3, x.2 i * exponentBasis.dualBasis.equivFun f i.succ) = f x
  have hsum : ∑ i : Fin 4, (freeCoordinates x) i * (exponentBasis.dualBasis.equivFun f i) = f x := by
    have hh := congrArg f (exponentBasis.sum_repr x)
    rw [map_sum] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Module.Basis.dualBasis_equivFun, map_smul]
    have hc : exponentBasis.repr x i = freeCoordinates x i := by
      change ((Pi.basisFun ℤ (Fin 4)).repr (freeCoordinates x)) i = _
      simp [Pi.basisFun_repr]
    rw [hc]
    rfl
  rw [Fin.sum_univ_succ] at hsum
  exact hsum

section Cocharacters

open LinearAlgebraicGroups.Specs
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (pairing)
open scoped CategoryTheory.MonObj


variable {k : Type u} [Field k] {T : GroupScheme k}
variable [CategoryTheory.IsCommMonObj T.X]

private def cocharacterCoordinates
    (C : Additive (Character T) ≃ₗ[ℤ] CharacterExponents)
    (P : Additive (Character T) →ₗ[ℤ] Additive (Cocharacter T) →ₗ[ℤ] ℤ)
    [P.IsPerfPair] : Additive (Cocharacter T) ≃ₗ[ℤ] evenSumLattice :=
  P.flip.toPerfPair.trans (C.symm.dualMap.trans latticeDual)

private theorem cocharacterCoordinates_pairing
    (C : Additive (Character T) ≃ₗ[ℤ] CharacterExponents)
    (P : Additive (Character T) →ₗ[ℤ] Additive (Cocharacter T) →ₗ[ℤ] ℤ) [P.IsPerfPair]
    (x : Additive (Character T)) (y : Additive (Cocharacter T)) :
    latticePairing (C x) (cocharacterCoordinates C P y) = P x y := by
  change latticePairing (C x) (latticeDual (C.symm.dualMap (P.flip.toPerfPair y))) = _
  rw [latticeDual_pairing, LinearEquiv.dualMap_apply, LinearEquiv.symm_apply_apply]
  rfl

end Cocharacters

end

section SplitDiagonalTorus

open LinearAlgebraicGroups.Specs
open SplitSpinSpecification
open AlgebraicGeometry CategoryTheory Opposite
open DiagonalizableGroups (IntegerCharacters integerGenerator groupAlgebra groupAlgebraMap)
open Specs.CharacterDescent (StandardLattice)
open scoped BigOperators CategoryTheory.MonObj


noncomputable section

open private actionMatrix actionMatrix_spec actionMatrix_change action_matrix_unique
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin

private abbrev DiagonalLattice := StandardLattice.{u} 4

private def diagonalExponent (m : DiagonalLattice.{u}) (i : Fin 4) : ℤ :=
  (m i).down.toAdd

private def diagonalGenerator (i : Fin 4) : DiagonalLattice.{u} :=
  fun j => if j = i then integerGenerator else 1

private theorem diagonalGenerator_pow (z : ℤ) :
    (integerGenerator : IntegerCharacters.{u}) ^ z = ⟨Multiplicative.ofAdd z⟩ := by
  apply ULift.ext
  apply Multiplicative.toAdd.injective
  change z • (1 : ℤ) = z
  simp

private theorem diagonalGenerator_exp (i j : Fin 4) :
    diagonalExponent (diagonalGenerator.{u} i) j = if j = i then 1 else 0 := by
  by_cases h : j = i <;> simp [diagonalGenerator, diagonalExponent, h]

private theorem diagonalGenerator_prod (m : DiagonalLattice.{u}) :
    (∏ i, diagonalGenerator i ^ diagonalExponent m i) = m := by
  funext j
  rw [Finset.prod_apply]
  rw [Finset.prod_eq_single j (fun i _ hi => by simp [diagonalGenerator, Ne.symm hi])
    (by simp)]
  change (diagonalGenerator.{u} j j) ^ diagonalExponent m j = m j
  rw [show diagonalGenerator.{u} j j = integerGenerator from by simp [diagonalGenerator],
    diagonalGenerator_pow]
  rfl

private def torusPointGenerators (R : Type u) [CommRing R] :
    (DiagonalLattice.{u} →* Rˣ) ≃* (Fin 4 → Rˣ) where
  toFun f i := f (diagonalGenerator i)
  invFun a :=
    { toFun := fun m => ∏ i, a i ^ diagonalExponent m i
      map_one' := by simp [diagonalExponent]
      map_mul' := by
        intro x y
        change (∏ i, a i ^ (diagonalExponent x i + diagonalExponent y i)) = _
        simp only [zpow_add, Finset.prod_mul_distrib] }
  left_inv f := by
    apply MonoidHom.ext
    intro m
    change (∏ i, f (diagonalGenerator i) ^ diagonalExponent m i) = f m
    simp_rw [← map_zpow]
    rw [← map_prod, diagonalGenerator_prod]
  right_inv a := by
    funext i
    change (∏ j, a j ^ diagonalExponent (diagonalGenerator.{u} i) j) = a i
    simp [diagonalGenerator_exp, Finset.prod_ite_eq']
  map_mul' _ _ := rfl

private abbrev torusParam (R : Type u) [CommRing R] :
    DiagonalPoints R ≃* Rˣ × (Fin 3 → Rˣ) :=
  (diagonalParameters_proof R).choose

private theorem torusParam_apply {R : Type u} [CommRing R] (t : DiagonalPoints R) :
    torusParam R t = (scalar t, fun i => scales t i.succ) :=
  (diagonalParameters_proof R).choose_spec t

private def coordinatesPair (R : Type u) [CommRing R] :
    (Fin 4 → Rˣ) ≃* Rˣ × (Fin 3 → Rˣ) where
  toFun a := (a 0, fun i => a i.succ)
  invFun a := Fin.cases a.1 a.2
  left_inv _ := funext (fun i => Fin.cases rfl (fun _ => rfl) i)
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable (k : Type u) [Field k]

private abbrev splitDiagonalGroup : Specs.GroupScheme k :=
  specGroup (groupAlgebra k (DiagonalLattice.{u}))

private def torusGroupPoints (R : TestAlgebra k) :
    Points (splitDiagonalGroup k).X R ≃* (DiagonalLattice.{u} →* Rˣ) :=
  ((LinearAlgebraicGroups.DiagonalizableGroups.groupAlgebraPointsIso k (DiagonalLattice.{u})).app
    R).groupIsoToMulEquiv

private def diagonalGroupPoints (R : TestAlgebra k) :
    Points (splitDiagonalGroup k).X R ≃* DiagonalPoints R :=
  (torusGroupPoints k R).trans ((torusPointGenerators R).trans
    ((coordinatesPair R).trans (torusParam R).symm))

private theorem diagonalGroupPoints_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (t : Points (splitDiagonalGroup k).X R) :
    diagonalGroupPoints k S (mapPoints f t) =
      mapDiagonal f.hom.toRingHom (diagonalGroupPoints k R t) := by
  have h := ConcreteCategory.congr_hom
    ((LinearAlgebraicGroups.DiagonalizableGroups.groupAlgebraPointsIso k (DiagonalLattice.{u})).hom.naturality f) t
  change torusGroupPoints k S (mapPoints f t) =
    (Units.map f.hom.toMonoidHom).comp (torusGroupPoints k R t) at h
  apply (torusParam S).injective
  have hp (R : TestAlgebra k) (p : Points (splitDiagonalGroup k).X R) :
      torusParam R (diagonalGroupPoints k R p) =
        (coordinatesPair R) (torusPointGenerators R (torusGroupPoints k R p)) :=
    (torusParam R).apply_symm_apply _
  rw [hp, h, torusParam_apply]
  have hr := (hp R t).symm.trans (torusParam_apply (diagonalGroupPoints k R t))
  apply Prod.ext
  · exact congrArg (fun p : Rˣ × (Fin 3 → Rˣ) => Units.map f.hom.toMonoidHom p.1) hr
  · funext i
    exact congrArg (fun p : Rˣ × (Fin 3 → Rˣ) => Units.map f.hom.toMonoidHom (p.2 i)) hr

private theorem splitDiagonalGroup_split : Specs.GeometricRadicals.IsSplitTorus (splitDiagonalGroup k) :=
  ⟨4, LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) 4⟩

section DiagonalSubgroup

set_option backward.isDefEq.respectTransparency false

open scoped Matrix

private def diagonalPointMap :
    (groupPointsFunctor k).obj (splitDiagonalGroup k) ⟶
      (groupPointsFunctor k).obj (fieldSpinGroup k).val where
  app R := GrpCat.ofHom ((fieldSpinPoints k R).symm.toMonoidHom.comp
    (diagonalLift.comp (diagonalGroupPoints k R).toMonoidHom))
  naturality {R S} f := by
    apply GrpCat.ext
    intro p
    change Points (splitDiagonalGroup k).X R at p
    apply (fieldSpinPoints k S).injective
    change (fieldSpinPoints k S) ((fieldSpinPoints k S).symm
      (diagonalLift (diagonalGroupPoints k S (mapPoints f p)))) =
      fieldSpinPoints k S (mapPoints f ((fieldSpinPoints k R).symm
        (diagonalLift (diagonalGroupPoints k R p))))
    rw [MulEquiv.apply_symm_apply, diagonalGroupPoints_natural]
    have h := spinPointEquiv_natural k f ((fieldSpinPoints k R).symm (diagonalLift (diagonalGroupPoints k R p)))
    change fieldSpinPoints k S (mapPoints f ((fieldSpinPoints k R).symm
      (diagonalLift (diagonalGroupPoints k R p)))) =
      SpinFunctor.map (integralForm 4) (hyperbolicBasis ℤ 4) (f.hom.restrictScalars ℤ)
        (fieldSpinPoints k R ((fieldSpinPoints k R).symm
          (diagonalLift (diagonalGroupPoints k R p)))) at h
    rw [h, MulEquiv.apply_symm_apply, diagonalLift_natural]
    rfl

private theorem diagonalGroup_affine : IsAffine (splitDiagonalGroup k).X.left := by
  change IsAffine (Spec (CommRingCat.of (MonoidAlgebra k (DiagonalLattice.{u}))))
  infer_instance

private def diagonalInclusion : splitDiagonalGroup k ⟶ (fieldSpinGroup k).val :=
  (groupHomEquiv _ _ (diagonalGroup_affine k)).symm (diagonalPointMap k)

private theorem diagonalInclusion_point (R : TestAlgebra k)
    (t : Points (splitDiagonalGroup k).X R) :
    fieldSpinPoints k R (t ≫ (diagonalInclusion k).hom.hom) =
      diagonalLift (diagonalGroupPoints k R t) := by
  have he := (groupHomEquiv (splitDiagonalGroup k) (fieldSpinGroup k).val
    (diagonalGroup_affine k)).apply_symm_apply (diagonalPointMap k)
  have h := DFunLike.congr_fun (congrArg (fun τ => (τ.app R).hom) he)
    (show ((groupPointsFunctor k).obj (splitDiagonalGroup k)).obj R from t)
  change (t ≫ (diagonalInclusion k).hom.hom) =
    (fieldSpinPoints k R).symm (diagonalLift (diagonalGroupPoints k R t)) at h
  rw [h, MulEquiv.apply_symm_apply]

private theorem diagonalInclusion_point_injective (R : TestAlgebra k) :
    Function.Injective (fun t : Points (splitDiagonalGroup k).X R =>
      t ≫ (diagonalInclusion k).hom.hom) := by
  intro x y h
  apply (diagonalGroupPoints k R).injective
  apply diagonalLift_injective
  simpa only [diagonalInclusion_point] using congrArg (fieldSpinPoints k R) h

private def spinVectorMatrix (R : TestAlgebra k) (p : Points (fieldSpinGroup k).val.X R) :
    Matrix (PairIndex 4) (PairIndex 4) R :=
  actionMatrix 4 (fieldSpinPoints k R p)

private theorem spinVectorMatrix_valid (R : TestAlgebra k) (p : Points (fieldSpinGroup k).val.X R) :
    HasActionMatrix 4 (fieldSpinRepresentation k R p) (spinVectorMatrix k R p) :=
  actionMatrix_spec 4 _

private theorem spinVectorMatrix_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (p : Points (fieldSpinGroup k).val.X R) :
    spinVectorMatrix k S (mapPoints f p) = (spinVectorMatrix k R p).map f.hom := by
  have h := spinPointEquiv_natural k f p
  change fieldSpinPoints k S (mapPoints f p) =
    SpinFunctor.map (integralForm 4) (hyperbolicBasis ℤ 4) (f.hom.restrictScalars ℤ) (fieldSpinPoints k R p) at h
  unfold spinVectorMatrix
  rw [h]
  exact actionMatrix_change (f.hom.restrictScalars ℤ) _

private theorem diagonalInclusion_matrix (R : TestAlgebra k)
    (t : Points (splitDiagonalGroup k).X R) :
    spinVectorMatrix k R (t ≫ (diagonalInclusion k).hom.hom) =
      middle (diagonalBlock (diagonalGroupPoints k R t)) := by
  apply action_matrix_unique (spinVectorMatrix_valid k R _)
  change HasActionMatrix 4 (fieldSpinPoints k R (t ≫ (diagonalInclusion k).hom.hom)).val _
  rw [diagonalInclusion_point]
  exact diagonalUnit_action _

private theorem diagonalInclusion_range (R : TestAlgebra k)
    (p : Points (fieldSpinGroup k).val.X R) :
    (∃ t : Points (splitDiagonalGroup k).X R, t ≫ (diagonalInclusion k).hom.hom = p) ↔
      ∀ i j, i ≠ j → spinVectorMatrix k R p i j = 0 := by
  constructor
  · rintro ⟨t, rfl⟩ i j hij
    rw [diagonalInclusion_matrix, middle_diagonal, Matrix.diagonal_apply_ne _ hij]
  · intro hp
    obtain ⟨d, hd⟩ := diagonalLift_exists_of_matrix (fieldSpinPoints k R p)
      (spinVectorMatrix_valid k R p) hp
    refine ⟨(diagonalGroupPoints k R).symm d, ?_⟩
    apply (fieldSpinPoints k R).injective
    rw [diagonalInclusion_point, MulEquiv.apply_symm_apply, hd]

private def diagonalIdeal : Ideal (fieldSpinRing k) :=
  let R := CommAlgCat.of k (fieldSpinRing k)
  let M := spinVectorMatrix k R (𝟙 (fieldSpinScheme k))
  Ideal.span (Set.range (fun ij : {ij : PairIndex 4 × PairIndex 4 // ij.1 ≠ ij.2} => M ij.val.1 ij.val.2))

set_option maxHeartbeats 900000 in
private theorem diagonalInclusion_closed :
    IsClosedImmersion (diagonalInclusion k).hom.hom.left := by
  let _ : CommRing (fieldSpinRing k) := inferInstance
  let _ : Algebra k (fieldSpinRing k) := inferInstance
  let A := MonoidAlgebra k (DiagonalLattice.{u})
  let F := testSpec k
  let fa := algSpec.fullyFaithful (R := CommRingCat.of k)
  let f : (fieldSpinRing k) →ₐ[k] A := (fa.preimage (diagonalInclusion k).hom.hom).unop.hom
  have hf : F.map (CommAlgCat.ofHom f).op = (diagonalInclusion k).hom.hom := fa.map_preimage _
  let R := CommAlgCat.of k A
  let U := CommAlgCat.of k (fieldSpinRing k)
  let J : Ideal (fieldSpinRing k) := diagonalIdeal k
  have h_eval (S : TestAlgebra k) (g : (fieldSpinRing k) →ₐ[k] S) :
      spinVectorMatrix k S (F.map (CommAlgCat.ofHom g).op) =
        (spinVectorMatrix k U (𝟙 (fieldSpinScheme k))).map g := by
    have h := spinVectorMatrix_natural k (CommAlgCat.ofHom g) (𝟙 (fieldSpinScheme k))
    change spinVectorMatrix k S (F.map (CommAlgCat.ofHom g).op ≫ 𝟙 (fieldSpinScheme k)) =
      (spinVectorMatrix k U (𝟙 (fieldSpinScheme k))).map g at h
    rw [Category.comp_id] at h
    exact h
  have hJ : J ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨⟨i, j⟩, hij⟩, rfl⟩
    have ho := (diagonalInclusion_range k R ((diagonalInclusion k).hom.hom)).mp
      ⟨𝟙 _, Category.id_comp _⟩ i j hij
    have := congrArg (fun M : Matrix (PairIndex 4) (PairIndex 4) A => M i j) (h_eval R f)
    rw [hf, ho] at this
    exact this.symm
  let Q := CommAlgCat.of k ((fieldSpinRing k) ⧸ J)
  let π := Ideal.Quotient.mkₐ k J
  have hπ : ∀ i j, i ≠ j → spinVectorMatrix k Q (F.map (CommAlgCat.ofHom π).op) i j = 0 := by
    intro i j hij
    have h := congrArg (fun M : Matrix (PairIndex 4) (PairIndex 4) Q => M i j) (h_eval Q π)
    rw [h]
    let m := spinVectorMatrix k U (𝟙 (fieldSpinScheme k)) i j
    change Ideal.Quotient.mk J m = 0
    have hm : m ∈ J := Ideal.subset_span (Set.mem_range_self
      (⟨(i, j), hij⟩ : {ij : PairIndex 4 × PairIndex 4 // ij.1 ≠ ij.2}))
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hm
  obtain ⟨p, hp⟩ := (diagonalInclusion_range k Q _).mpr hπ
  let g : A →ₐ[k] Q := (fa.preimage p).unop.hom
  have hg : F.map (CommAlgCat.ofHom g).op = p := fa.map_preimage p
  have he : g.comp f = π := by
    rw [← hf, ← hg, ← Functor.map_comp] at hp
    exact congrArg (fun z : op Q ⟶ op U => z.unop.hom) (fa.map_injective hp)
  let l : ((fieldSpinRing k) ⧸ J) →ₐ[k] A := Ideal.Quotient.liftₐ J f (fun _ hz => hJ hz)
  have hl : l.comp π = f := Ideal.Quotient.liftₐ_comp ..
  have hlg : l.comp g = AlgHom.id k A := by
    have hcomp : (l.comp g).comp f = f := by rw [AlgHom.comp_assoc, he, hl]
    have hh := congrArg (fun a : (fieldSpinRing k) →ₐ[k] A => F.map (CommAlgCat.ofHom a).op) hcomp
    rw [CommAlgCat.ofHom_comp, op_comp, Functor.map_comp, hf] at hh
    have hi : F.map (CommAlgCat.ofHom (l.comp g)).op = 𝟙 (splitDiagonalGroup k).X :=
      diagonalInclusion_point_injective k R (hh.trans (Category.id_comp _).symm)
    exact congrArg (fun z : op R ⟶ op R => z.unop.hom) (fa.map_injective (hi.trans (CategoryTheory.Functor.map_id F _).symm))
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (g x)
    refine ⟨b, ?_⟩
    rw [← DFunLike.congr_fun hl b, AlgHom.comp_apply, show π b = g x from hb]
    exact DFunLike.congr_fun hlg x
  rw [← hf]
  exact IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom f.toRingHom) hsurj

private def diagonalSubgroup : ClosedSubgroup (fieldSpinGroup k).val :=
  ⟨splitDiagonalGroup k, diagonalInclusion k, diagonalInclusion_closed k⟩

private theorem diagonalSubgroup_presentation :
    TorusPointPresentation (fieldSpinRepresentation k) (diagonalSubgroup k) (diagonalGroupPoints k) := by
  refine ⟨fun f t => diagonalGroupPoints_natural k f t, ?_, ?_⟩
  · intro R g
    constructor
    · rintro ⟨d, rfl⟩
      refine ⟨diagonalGroupPoints k R d, ?_⟩
      change HasActionMatrix 4 (fieldSpinRepresentation k R (d ≫ (diagonalInclusion k).hom.hom)) _
      rw [← diagonalInclusion_matrix]
      exact spinVectorMatrix_valid k R _
    · rintro ⟨t, ht⟩
      apply (diagonalInclusion_range k R g).mpr
      intro i j hij
      rw [action_matrix_unique (spinVectorMatrix_valid k R g) ht, middle_diagonal,
        Matrix.diagonal_apply_ne _ hij]
  · intro R
    refine ⟨exteriorModel R, exteriorModel_vectors, fun t => ⟨?_, ?_⟩⟩
    · exact (diagonalInclusion_matrix k R t) ▸ spinVectorMatrix_valid k R _
    · intro I
      change exteriorModel R (fieldSpinPoints k R (t ≫ (diagonalInclusion k).hom.hom)).val _ = _
      rw [diagonalInclusion_point, (weightEvaluation_proof R _).2]
      exact diagonalUnit_wedge (diagonalGroupPoints k R t) I

end DiagonalSubgroup

section CharacterCoordinates

set_option backward.isDefEq.respectTransparency false

open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue)
open WithConv

open private pointsIso_spec pointsIso_precompose
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups

private def latticeExponents : Additive DiagonalLattice.{u} ≃ₗ[ℤ] CharacterExponents :=
  (show Additive DiagonalLattice.{u} ≃+ VectorExponents from {
    toFun := fun x => diagonalExponent x.toMul
    invFun := fun x => Additive.ofMul (fun i => ⟨Multiplicative.ofAdd (x i)⟩)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl } ).toIntLinearEquiv.trans freeCoordinates.symm

private theorem torusGroupPoints_monomial (R : TestAlgebra k)
    (t : Points (splitDiagonalGroup k).X R) (m : DiagonalLattice.{u}) :
    torusGroupPoints k R t m =
      Additive.toMul (evaluate (diagonalGroupPoints k R t) (latticeExponents (Additive.ofMul m))) := by
  let h := torusGroupPoints k R t
  let p := diagonalGroupPoints k R t
  have hfree : (h (diagonalGenerator 0), fun i : Fin 3 => h (diagonalGenerator i.succ)) =
      (scalar p, fun i => scales p i.succ) := by
    exact ((torusParam R).apply_symm_apply _).symm.trans (torusParam_apply p)
  have h₀ : h (diagonalGenerator 0) = scalar p := congrArg Prod.fst hfree
  have hs (i : Fin 3) : h (diagonalGenerator i.succ) = scales p i.succ := congrArg (fun a : Rˣ × (Fin 3 → Rˣ) => a.2 i) hfree
  change h m = scalar p ^ diagonalExponent m 0 * ∏ i : Fin 3, scales p i.succ ^ diagonalExponent m i.succ
  calc
    h m = ∏ i, h (diagonalGenerator i) ^ diagonalExponent m i := by
      simp_rw [← map_zpow]
      rw [← map_prod, diagonalGenerator_prod]
    _ = _ := by
      rw [Fin.prod_univ_succ, h₀]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      rw [hs]

private theorem unitPoint_coordinate (R : TestAlgebra k)
    (p : Points (specGroup (groupAlgebra k IntegerCharacters.{u})).X R) :
    ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage p).unop.hom
      (MonoidAlgebra.single integerGenerator 1) =
      ((show IntegerCharacters.{u} →* Rˣ from
        (LinearAlgebraicGroups.DiagonalizableGroups.groupAlgebraPointsIso k IntegerCharacters).hom.app R p)
        integerGenerator).val := by
  let A := groupAlgebra k IntegerCharacters.{u}
  let e := (hopfSpecPointIso A).app R
  obtain ⟨f, hf⟩ := e.groupIsoToMulEquiv.surjective p
  have hp : p = (testSpec k).map (CommAlgCat.ofHom f.ofConv).op := hf.symm
  have h := (pointsIso_spec (k := k) IntegerCharacters R f.ofConv integerGenerator).symm
  change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage p).unop.hom
    (MonoidAlgebra.single integerGenerator 1) =
    ((show IntegerCharacters.{u} →* Rˣ from
      (LinearAlgebraicGroups.DiagonalizableGroups.groupAlgebraPointsIso k IntegerCharacters).hom.app R p)
      integerGenerator).val
  rw [hp, CategoryTheory.Functor.FullyFaithful.preimage_map]
  exact h

private theorem diagonalCharacterCoordinates :
    ∃ C : Additive (Character (splitDiagonalGroup k)) ≃ₗ[ℤ] CharacterExponents,
      ∀ (R : TestAlgebra k) (t : Points (splitDiagonalGroup k).X R) (χ : Character (splitDiagonalGroup k)),
        characterValue χ R t =
          ((Additive.toMul (evaluate (diagonalGroupPoints k R t) (C (Additive.ofMul χ))) : Rˣ) : R) := by
  obtain ⟨χ, _, hχ, _, _⟩ :=
    LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing (k := k) 4
  let e : Additive (Character (splitDiagonalGroup k)) ≃ₗ[ℤ] Additive DiagonalLattice.{u} :=
    χ.symm.toAdditive.toIntLinearEquiv
  refine ⟨e.trans latticeExponents, fun R t ψ => ?_⟩
  obtain ⟨m, rfl⟩ := χ.surjective ψ
  have h₁ : e (Additive.ofMul (χ m)) = Additive.ofMul m :=
    congrArg Additive.ofMul (χ.symm_apply_apply m)
  change characterValue (χ m) R t = _
  rw [LinearEquiv.trans_apply, h₁, ← torusGroupPoints_monomial]
  let f := (zpowersHom DiagonalLattice m).comp MulEquiv.ulift.toMonoidHom
  rw [hχ]
  change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    (t ≫ (specGroupMap (groupAlgebraMap k f)).hom.hom)).unop.hom
      (MonoidAlgebra.single integerGenerator 1) = _
  rw [unitPoint_coordinate]
  have hm := pointsIso_precompose (k := k) f R t integerGenerator
  have hf : f integerGenerator = m ^ (1 : ℤ) := rfl
  rw [hf, zpow_one] at hm
  exact congrArg Units.val hm

end CharacterCoordinates

section Maximality

open Specs.GeometricRadicals (IsMaximalTorus IsTorus baseChangedSubgroup)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open scoped Matrix

open private action_matrix_mul from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin
open private isCommMonObj_of_groupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.HopfAlgebras
open private extendedGroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem vectorEigenvalue_map {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (t : DiagonalPoints R) (i : PairIndex 4) :
    vectorEigenvalue (mapDiagonal f t) i = f (vectorEigenvalue t i) := by
  cases i with
  | inl j => rfl
  | inr j =>
    change ↑((Units.map f.toMonoidHom (scales t j))⁻¹) = f ↑((scales t j)⁻¹)
    rw [← map_inv]
    rfl

/-- In any algebra over an infinite field, the constant diagonal spin
points already force a commuting vector action to be diagonal. -/
private theorem diagonal_of_commutes_with_spin_torus
    {K R : Type u} [Field K] [Infinite K] [CommRing R] [Algebra K R]
    (M : Matrix (PairIndex 4) (PairIndex 4) R)
    (h : ∀ t : DiagonalPoints K,
      let D := middle (diagonalBlock (mapDiagonal (algebraMap K R) t))
      M * D = D * M) :
    ∀ i j, i ≠ j → M i j = 0 := by
  intro i j hij
  obtain ⟨z, hz⟩ := exists_separating_unit (K := K)
  obtain ⟨a, ha⟩ := vector_separation z hz hij
  let t := singleScale z a
  let D := vectorEigenvalue (mapDiagonal (algebraMap K R) t)
  have he : M i j * D j = D i * M i j := by
    have hh := h t
    change M * middle (diagonalBlock (mapDiagonal (algebraMap K R) t)) =
      middle (diagonalBlock (mapDiagonal (algebraMap K R) t)) * M at hh
    rw [middle_diagonal] at hh
    have hc := congrArg (fun N : Matrix (PairIndex 4) (PairIndex 4) R => N i j) hh
    simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul] using hc
  have hu : IsUnit (D j - D i) := by
    change IsUnit (vectorEigenvalue (mapDiagonal (algebraMap K R) t) j -
      vectorEigenvalue (mapDiagonal (algebraMap K R) t) i)
    rw [vectorEigenvalue_map, vectorEigenvalue_map, ← map_sub]
    exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm ha))).map (algebraMap K R)
  have hzero : M i j * (D j - D i) = 0 := by
    rw [mul_sub, he, mul_comm (D i), sub_self]
  obtain ⟨u, hu⟩ := hu
  rw [← hu] at hzero
  have hz := congrArg (fun x : R => x * (↑u⁻¹ : R)) hzero
  rw [mul_assoc, Units.mul_inv, mul_one, zero_mul] at hz
  exact hz


private theorem torusComm {K : Type u} [Field K]
    (H : Specs.GroupScheme K) (hAff : IsAffine H.X.left) (h : IsTorus H) :
    IsCommMonObj H.X := by
  let e := affineHopfEquivalence K
  let X : Specs.AffineGroupScheme K := ⟨H, hAff⟩
  let A := (e.inverse.obj X).unop
  let i : specGroup A ≅ H := (affineGroupInclusion K).mapIso (e.counitIso.app X)
  obtain ⟨K', _, _, _, r, ⟨j⟩⟩ := h
  have hs : IsTorus (specGroup A) :=
    ⟨K', inferInstance, inferInstance, inferInstance, r, ⟨(groupBaseChange K K').mapIso i ≪≫ j⟩⟩
  have hA := (LinearAlgebraicGroups.CharacterDescent.torusOnSchemes A).mpr hs
  exact isCommMonObj_of_groupIso i (LinearAlgebraicGroups.CharacterDescent.multiplicativeTypeProperties A
    (LinearAlgebraicGroups.CharacterDescent.torusIsMultiplicativeType A hA)).2

private theorem splitDiagonalGroup_isTorus : IsTorus (splitDiagonalGroup k) := by
  let A := groupAlgebra k (DiagonalLattice.{u})
  apply (LinearAlgebraicGroups.CharacterDescent.torusOnSchemes A).mp
  exact ⟨k, inferInstance, inferInstance, inferInstance, 4,
    ⟨(CommHopfAlgCat.isoMk (LinearAlgebraicGroups.CharacterDescent.groupAlgebraBaseChange
      k k (DiagonalLattice.{u}))).symm⟩⟩

private def diagonalBaseChangeIso (K : Type u) [Field K] [Algebra k K] :
    (groupBaseChange k K).obj (splitDiagonalGroup k) ≅ splitDiagonalGroup K :=
  let A := groupAlgebra k (DiagonalLattice.{u})
  let e := CommHopfAlgCat.isoMk
    (LinearAlgebraicGroups.CharacterDescent.groupAlgebraBaseChange k K (DiagonalLattice.{u}))
  (extendedGroupIso K A).symm ≪≫ (hopfSpec (CommRingCat.of K)).mapIso e.symm.op

private theorem spinVectorMatrix_mul (R : TestAlgebra k)
    (p q : Points (fieldSpinGroup k).val.X R) :
    spinVectorMatrix k R (p * q) = spinVectorMatrix k R p * spinVectorMatrix k R q := by
  apply action_matrix_unique (spinVectorMatrix_valid k R _)
  rw [map_mul]
  exact action_matrix_mul (spinVectorMatrix_valid k R p) (spinVectorMatrix_valid k R q)

set_option backward.isDefEq.respectTransparency false in
private theorem subgroupOf_of_testPoints {K : Type u} [Field K] {G : Specs.GroupScheme K}
    {S T : ClosedSubgroup G} (hS : IsAffine S.group.X.left)
    (h : ∀ (R : TestAlgebra K) (s : Points S.group.X R),
      ∃ t : Points T.group.X R, t ≫ T.inclusion.hom.hom = s ≫ S.inclusion.hom.hom) :
    IsSubgroupOf S T := by
  classical
  let j := T.inclusion.hom.hom
  have := T.isClosedImmersion
  have : Mono j := Over.mono_of_mono_left _
  let l (R : TestAlgebra K) (s : Points S.group.X R) := (h R s).choose
  have hl (R : TestAlgebra K) (s : Points S.group.X R) : l R s ≫ j = s ≫ S.inclusion.hom.hom :=
    (h R s).choose_spec
  let α : (groupPointsFunctor K).obj S.group ⟶ (groupPointsFunctor K).obj T.group :=
    { app := fun R =>
        GrpCat.ofHom
          { toFun := l R
            map_one' := by
              change l R 1 = 1
              rw [← cancel_mono j, hl, MonObj.one_comp, MonObj.one_comp]
            map_mul' := fun p q => by
              change l R (p * q) = l R p * l R q
              rw [← cancel_mono j, hl]
              simp only [MonObj.mul_comp, hl] }
      naturality := by
        intro R V f
        apply GrpCat.ext
        intro s
        change Points S.group.X R at s
        change l V (mapPoints f s) = mapPoints f (l R s)
        rw [← cancel_mono j, hl]
        change _ = ((testSpec K).map f.op ≫ l R s) ≫ j
        simp only [Category.assoc, hl] }
  let E := groupHomEquiv S.group T.group hS
  let f := E.symm α
  have hf := E.apply_symm_apply α
  refine ⟨f, (groupHomComparison K S.group G hS).1 ?_⟩
  change (groupPointsFunctor K).map (f ≫ T.inclusion) = (groupPointsFunctor K).map S.inclusion
  rw [CategoryTheory.Functor.map_comp]
  change E f ≫ (groupPointsFunctor K).map T.inclusion = _
  rw [hf]
  ext R p
  exact hl R p

set_option backward.isDefEq.respectTransparency false in
private theorem diagonalSubgroup_geometricallyMaximal :
    IsGeometricallyMaximal (diagonalSubgroup k) := by
  let K := AlgebraicClosure k
  let G := baseChangedAlgebraicGroup K (fieldSpinGroup k)
  let i := diagonalInclusion k
  have hcl : IsClosedImmersion ((groupBaseChange k K).map i).hom.hom.left :=
    baseChangeClosedSubgroup k K i (diagonalInclusion_closed k)
  let T := baseChangedSubgroup K (diagonalSubgroup k) hcl
  refine ⟨hcl, ?_⟩
  change IsMaximalTorus T
  constructor
  · let e := diagonalBaseChangeIso k K
    obtain ⟨E, _, _, _, r, ⟨f⟩⟩ := splitDiagonalGroup_isTorus K
    exact ⟨E, inferInstance, inferInstance, inferInstance, r,
      ⟨(groupBaseChange K E).mapIso e ≪≫ f⟩⟩
  intro S hS hTS
  let hAff := (closedSubgroupAlgebraicGroup (G := G) S).property.1
  have hcomm : IsCommMonObj S.group.X := torusComm S.group hAff hS
  obtain ⟨j, hj⟩ := hTS
  have hj' : j.hom.hom ≫ S.inclusion.hom.hom = T.inclusion.hom.hom :=
    congrArg (fun a : T.group ⟶ G.val => a.hom.hom) hj
  have hinf : Infinite K := inferInstance
  apply subgroupOf_of_testPoints hAff
  intro R s
  let Rk := (restrictTestAlgebra k K).obj R
  let E := baseChangePointGroupEquiv K (fieldSpinGroup k).val R
  let F := baseChangePointGroupEquiv K (splitDiagonalGroup k) R
  let x := E (s ≫ S.inclusion.hom.hom)
  let M := spinVectorMatrix k Rk x
  have hnat (t : Points T.group.X R) :
      E (t ≫ T.inclusion.hom.hom) = F t ≫ i.hom.hom :=
    baseChangePointsSchemeNaturality k K i.hom.hom R t
  have hM : ∀ (p : DiagonalPoints K),
      let D := middle (diagonalBlock (mapDiagonal (algebraMap K R) p))
      M * D = D * M := by
    intro p
    let q := mapDiagonal (algebraMap K R) p
    let t := F.symm ((diagonalGroupPoints k Rk).symm q)
    have ht : spinVectorMatrix k Rk (E (t ≫ T.inclusion.hom.hom)) = middle (diagonalBlock q) := by
      rw [hnat]
      change spinVectorMatrix k Rk (F t ≫ (diagonalInclusion k).hom.hom) = _
      rw [diagonalInclusion_matrix]
      dsimp only [t]
      rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    have hc : (s ≫ S.inclusion.hom.hom) * (t ≫ T.inclusion.hom.hom) =
        (t ≫ T.inclusion.hom.hom) * (s ≫ S.inclusion.hom.hom) := by
      rw [← hj', ← Category.assoc, ← MonObj.mul_comp, ← MonObj.mul_comp]
      rw [mul_comm]
    have hh := congrArg (fun a => spinVectorMatrix k Rk (E a)) hc
    rw [map_mul, map_mul, spinVectorMatrix_mul, spinVectorMatrix_mul, ht] at hh
    exact hh
  obtain ⟨t, ht⟩ := (diagonalInclusion_range k Rk x).mpr
    (diagonal_of_commutes_with_spin_torus (K := K) M hM)
  refine ⟨F.symm t, E.injective ?_⟩
  rw [hnat, MulEquiv.apply_symm_apply]
  exact ht

end Maximality

end

end SplitDiagonalTorus

section TangentMatrices

open SplitSpinSpecification Matrix TrivSqZeroExt
open scoped Matrix


variable {K : Type u} [CommRing K]

/-- The quadratic norm, evaluated on dual numbers, also imposes the zero
diagonal of the shear blocks in characteristic two. -/
private theorem tangent_norm_blocks (M : Matrix (PairIndex 4) (PairIndex 4) (DualNumber K))
    (hM : PreservesNorm M) (h₀ : M.map (fstHom K K K) = 1) :
    let B : Matrix (PairIndex 4) (PairIndex 4) K := fun i j => (M i j).snd
    IsAlternating B.toBlocks₂₁ ∧ IsAlternating B.toBlocks₁₂ ∧ B.toBlocks₂₂ = -B.toBlocks₁₁ᵀ := by
  classical
  let B : Matrix (PairIndex 4) (PairIndex 4) K := fun i j => (M i j).snd
  let e (v : PairIndex 4 → K) : PairIndex 4 → DualNumber K :=
    fun i => algebraMap K (DualNumber K) (v i)
  have hF (v : PairIndex 4 → K) (i : PairIndex 4) : ((M *ᵥ e v) i).fst = v i := by
    calc
      _ = ((M.map (fstHom K K K)) *ᵥ v) i := by
        simp only [mulVec, dotProduct, fst_sum, fst_mul, e, algebraMap_eq_inl, fst_inl,
          Matrix.map_apply, fstHom_apply]
      _ = v i := by rw [h₀, one_mulVec]
  have hS (v : PairIndex 4 → K) (i : PairIndex 4) : ((M *ᵥ e v) i).snd = (B *ᵥ v) i := by
    simp only [mulVec, dotProduct, snd_sum, DualNumber.snd_mul, e, algebraMap_eq_inl, fst_inl,
      snd_inl, mul_zero, zero_add, B]
  have hnorm (v : PairIndex 4 → K) :
      (∑ i, (v (.inl i) * (B *ᵥ v) (.inr i) + (B *ᵥ v) (.inl i) * v (.inr i))) = 0 := by
    have h := congrArg (snd : DualNumber K → K) (hM (e v))
    simp only [hyperbolicNorm, dotProduct, snd_sum, DualNumber.snd_mul] at h
    simp only [hF, hS] at h
    simpa only [e, algebraMap_eq_inl, fst_inl, snd_inl, mul_zero, zero_mul,
      add_zero, Finset.sum_const_zero] using h
  have leftBlock (x y : Fin 4 → K) (i : Fin 4) :
      (B *ᵥ Sum.elim x y) (.inl i) = (B.toBlocks₁₁ *ᵥ x) i + (B.toBlocks₁₂ *ᵥ y) i := by
    simp [mulVec, dotProduct, Fintype.sum_sum_type, toBlocks₁₁, toBlocks₁₂]
  have rightBlock (x y : Fin 4 → K) (i : Fin 4) :
      (B *ᵥ Sum.elim x y) (.inr i) = (B.toBlocks₂₁ *ᵥ x) i + (B.toBlocks₂₂ *ᵥ y) i := by
    simp [mulVec, dotProduct, Fintype.sum_sum_type, toBlocks₂₁, toBlocks₂₂]
  have hP : IsAlternating B.toBlocks₂₁ := by
    intro x
    simpa [dotProduct, leftBlock, rightBlock] using hnorm (Sum.elim x 0)
  have hQ : IsAlternating B.toBlocks₁₂ := by
    intro y
    rw [dotProduct_comm]
    simpa [dotProduct, leftBlock, rightBlock] using hnorm (Sum.elim 0 y)
  refine ⟨hP, hQ, ?_⟩
  have hmixed (x y : Fin 4 → K) :
      x ⬝ᵥ (B.toBlocks₂₂ *ᵥ y) + (B.toBlocks₁₁ *ᵥ x) ⬝ᵥ y = 0 := by
    have he := hnorm (Sum.elim x y)
    simp only [Sum.elim_inl, Sum.elim_inr, leftBlock, rightBlock,
      mul_add, add_mul, Finset.sum_add_distrib] at he
    change x ⬝ᵥ (B.toBlocks₂₁ *ᵥ x) + x ⬝ᵥ (B.toBlocks₂₂ *ᵥ y) +
      ((B.toBlocks₁₁ *ᵥ x) ⬝ᵥ y + (B.toBlocks₁₂ *ᵥ y) ⬝ᵥ y) = 0 at he
    rw [hP x, dotProduct_comm (B.toBlocks₁₂ *ᵥ y) y, hQ y, zero_add, add_zero] at he
    exact he
  ext i j
  have hj := hmixed (Pi.single i 1) (Pi.single j 1)
  rw [single_dotProduct, dotProduct_single, one_mul, mul_one] at hj
  have hsingle (A : Block 4 K) (i j : Fin 4) : (A *ᵥ Pi.single j 1) i = A i j := by
    change (fun l => A i l) ⬝ᵥ Pi.single j 1 = _
    rw [dotProduct_single, mul_one]
  rw [hsingle, hsingle] at hj
  exact eq_neg_of_add_eq_zero_left hj

section VectorWeights

private def vectorWeight (i : PairIndex 4) : CharacterExponents :=
  Sum.elim epsilon (fun j => -epsilon j) i

private theorem vectorWeight_value (t : DiagonalPoints K) (i : PairIndex 4) :
    ((Additive.toMul (evaluate t (vectorWeight i)) : Kˣ) : K) = vectorEigenvalue t i := by
  cases i with
  | inl i => exact congrArg Units.val ((weightEvaluation_proof K t).1 i).1
  | inr i => exact congrArg Units.val ((weightEvaluation_proof K t).1 i).2

/-- Each permissible off-diagonal tangent entry has a root weight. -/
private theorem tangent_entry_root (B : Matrix (PairIndex 4) (PairIndex 4) K)
    (hP : IsAlternating B.toBlocks₂₁) (hQ : IsAlternating B.toBlocks₁₂)
    {i j : PairIndex 4} (hij : i ≠ j) (h : B i j ≠ 0) :
    vectorWeight i - vectorWeight j ∈ rootCharacters := by
  rcases i with i | i <;> rcases j with j | j
  · refine ⟨coordinate i - coordinate j, ⟨i, j, ?_, Or.inr (Or.inl rfl)⟩, ?_⟩
    · exact fun he => hij (congrArg Sum.inl he)
    · exact map_sub _ _ _
  · have h' : i ≠ j := by
      intro he
      subst j
      exact h (((SplitSpin.alternatingEntries 4 K B.toBlocks₁₂).mp hQ).1 i)
    refine ⟨coordinate i + coordinate j, ⟨i, j, h', Or.inl rfl⟩, ?_⟩
    change vectorPullback (coordinate i + coordinate j) = epsilon i - -epsilon j
    rw [map_add, sub_neg_eq_add]
    rfl
  · have h' : i ≠ j := by
      intro he
      subst j
      exact h (((SplitSpin.alternatingEntries 4 K B.toBlocks₂₁).mp hP).1 i)
    refine ⟨-coordinate i - coordinate j, ⟨i, j, h', Or.inr (Or.inr rfl)⟩, ?_⟩
    change vectorPullback (-coordinate i - coordinate j) = -epsilon i - epsilon j
    rw [map_sub, map_neg]
    rfl
  · refine ⟨coordinate j - coordinate i, ⟨j, i, ?_, Or.inr (Or.inl rfl)⟩, ?_⟩
    · exact fun he => hij (congrArg Sum.inr he.symm)
    · change vectorPullback (coordinate j - coordinate i) = -epsilon i - -epsilon j
      rw [map_sub, sub_neg_eq_add, sub_eq_add_neg, add_comm]
      rfl

end VectorWeights

end TangentMatrices

section Reductivity

open LinearAlgebraicGroups.Specs
open AlgebraicGeometry CategoryTheory Opposite Topology
open SplitSpinSpecification Matrix
open scoped Matrix CategoryTheory.MonObj


open Specs.GeometricRadicals (GeometricGroup IsReductive)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.RationalRepresentations
open WithConv

open private action_matrix_unique splitBasis from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin
open private pointMatrix pointMatrix_isCoactionMatrix pointMatrix_evaluation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
open private invariant_iff_coaction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Criteria
open private sections_normal isIso_of_schemeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

variable (k : Type u) [Field k]

private theorem spinVectorMatrix_one (R : TestAlgebra k) : spinVectorMatrix k R 1 = 1 := by
  apply action_matrix_unique (spinVectorMatrix_valid k R 1)
  refine ⟨LinearEquiv.refl R _, ?_, ?_⟩
  · rw [map_one]
    intro x
    simp [SpinSpecification.conjugate]
  · change LinearMap.toMatrix (splitBasis 4 R) (splitBasis 4 R) LinearMap.id = 1
    exact LinearMap.toMatrix_id _

private abbrev geometricTest (R : TestAlgebra (AlgebraicClosure k)) :=
  (restrictTestAlgebra k (AlgebraicClosure k)).obj R

private abbrev geometricPoint (R : TestAlgebra (AlgebraicClosure k)) :=
  baseChangePointGroupEquiv (AlgebraicClosure k) (fieldSpinGroup k).val R

private def geometricVectorMatrix (R : TestAlgebra (AlgebraicClosure k)) :
    Points (GeometricGroup (fieldSpinGroup k)).val.X R →* Matrix (PairIndex 4) (PairIndex 4) R where
  toFun x := spinVectorMatrix k (geometricTest k R) (geometricPoint k R x)
  map_one' := by rw [map_one, spinVectorMatrix_one]
  map_mul' x y := by rw [map_mul, spinVectorMatrix_mul]

private def geometricVectorPoints :
    (groupPointsFunctor (AlgebraicClosure k)).obj (GeometricGroup (fieldSpinGroup k)).val ⟶
      StandardGroups.generalLinearPoints (AlgebraicClosure k) (ULift.{u} (PairIndex 4)) where
  app R := GrpCat.ofHom <|
    (Units.map (Matrix.reindexRingEquiv R (Equiv.ulift.symm : PairIndex 4 ≃ ULift.{u} (PairIndex 4))).toMonoidHom).comp (MonoidHom.toHomUnits (geometricVectorMatrix k R))
  naturality {R S} f := by
    apply GrpCat.ext
    intro x
    apply Units.ext
    ext i j
    symm
    change f.hom (spinVectorMatrix k (geometricTest k R) (geometricPoint k R x) i.down j.down) =
      spinVectorMatrix k (geometricTest k S) (geometricPoint k S (mapPoints f x)) i.down j.down
    rw [show geometricPoint k S (mapPoints f x) =
      mapPoints ((restrictTestAlgebra k (AlgebraicClosure k)).map f) (geometricPoint k R x) from
        baseChangePointsNaturality k (AlgebraicClosure k) _ f x, spinVectorMatrix_natural]
    rfl

private theorem vectorPoints_fixed_vector
    {K : Type u} [Field K] (A : HopfAlgebraCategory K) (hU : Unipotent.HasInvariantVectors A)
    (α : convolutionPoints A ⟶ StandardGroups.generalLinearPoints K (ULift.{u} (PairIndex 4))) :
    ∃ x : ULift.{u} (PairIndex 4) → K, x ≠ 0 ∧
      ∀ f : (convolutionPoints A).obj (CommAlgCat.of K K),
        (α.app (CommAlgCat.of K K) f).val *ᵥ x = x := by
  let I := ULift.{u} (PairIndex 4)
  let V := I → K
  let b := Pi.basisFun K I
  let ρ := coactionOfMatrix A b (pointMatrix A α) (pointMatrix_isCoactionMatrix A α)
  obtain ⟨x, hx, hρ⟩ := hU V ρ
  refine ⟨x, hx, fun f => ?_⟩
  let M := (α.app (CommAlgCat.of K K) f).val
  have he : M.mulVecLin =
      (TensorProduct.rid K V).toLinearMap.comp (LinearAlgebraicGroups.RationalRepresentations.evaluate A ρ f.ofConv) := by
    apply b.ext
    intro j
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe]
    unfold LinearAlgebraicGroups.RationalRepresentations.evaluate
    rw [LinearMap.comp_apply, coaction_apply_basis A b ρ, coefficients_coactionOfMatrix]
    have hf := pointMatrix_evaluation A α (CommAlgCat.of K K) f
    change M = (pointMatrix A α).map f.ofConv at hf
    ext i
    simp only [map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    have hb (l : I) : b l = Pi.single l (1 : K) := Pi.basisFun_apply _ _ _
    simp only [hb]
    change (M *ᵥ Pi.single j 1) i = (∑ l : I, f.ofConv (pointMatrix A α l j) • Pi.single l 1) i
    rw [Matrix.mulVec_single_one, Matrix.col_apply, hf, Matrix.map_apply, Finset.sum_apply]
    simp [Pi.smul_apply, Pi.single_apply]
  have hxe := DFunLike.congr_fun he x
  have hi := (invariant_iff_coaction A ρ x).mp hρ
  change M.mulVecLin x = x
  rw [hxe, LinearMap.comp_apply, LinearEquiv.coe_coe]
  unfold LinearAlgebraicGroups.RationalRepresentations.evaluate
  rw [LinearMap.comp_apply, hi, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, map_one, TensorProduct.rid_tmul, one_smul]

/-- The scalar vector kernel has finitely many points over the algebraic closure. -/
private theorem finite_rational_points_of_trivial_vector
    (N : ClosedSubgroup (GeometricGroup (fieldSpinGroup k)).val)
    (h : ∀ n : Points N.group.X (CommAlgCat.of (AlgebraicClosure k) (AlgebraicClosure k)),
      geometricVectorMatrix k _ (n ≫ N.inclusion.hom.hom) = 1) :
    Finite (Points N.group.X (CommAlgCat.of (AlgebraicClosure k) (AlgebraicClosure k))) := by
  let K := AlgebraicClosure k
  let R := CommAlgCat.of K K
  let a (n : Points N.group.X R) := fieldSpinPoints k (geometricTest k R)
    (geometricPoint k R (n ≫ N.inclusion.hom.hom))
  let e := SpinFunctor.hyperbolicKernel (geometricTest k R) (Pi.basisFun ℤ (Fin 4)) (hyperbolicBasis ℤ 4)
  have hk (n : Points N.group.X R) :
      a n ∈ (SpinFunctor.vectorAction (integralForm 4) (geometricTest k R) (hyperbolicBasis ℤ 4)).ker := by
    change SpinFunctor.vectorAction (integralForm 4) _ _ (a n) = 1
    apply LinearEquiv.toLinearMap_injective
    apply (LinearMap.toMatrix (splitBasis 4 (geometricTest k R)) (splitBasis 4 (geometricTest k R))).injective
    rw [show (1 : ExtendedModule 4 (geometricTest k R) ≃ₗ[geometricTest k R] _).toLinearMap = LinearMap.id from rfl,
      LinearMap.toMatrix_id]
    exact h n
  apply Finite.of_injective (fun n => e.symm ⟨a n, hk n⟩)
  intro x y hxy
  have hN := N.isClosedImmersion
  have : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono N.inclusion.hom.hom).mp
  apply (geometricPoint k R).injective
  apply (fieldSpinPoints k (geometricTest k R)).injective
  exact congrArg Subtype.val (e.symm.injective hxy)

/-- A smooth connected affine group with finitely many rational points over an algebraically
closed field is trivial. -/
private theorem trivial_of_finite_rational_points {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K) (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (hf : Finite (Points G.val.X (CommAlgCat.of K K))) :
    Nonempty (G.val ≅ Grp.trivial (SchemeOver K)) := by
  let _ := hs
  let _ := hc
  have : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  have : JacobsonSpace G.val.X.left := LocallyOfFiniteType.jacobsonSpace G.val.X.hom
  have : IsReduced G.val.X.left := isReduced_of_smooth_over_field G.val.X.hom
  let p (x : closedPoints G.val.X.left) : Points G.val.X (CommAlgCat.of K K) :=
    Over.homMk (pointOfClosedPoint G.val.X.hom x.val x.property) (by
      rw [pointOfClosedPoint_comp]
      change 𝟙 _ = Spec.map (CommRingCat.ofHom (algebraMap K K))
      exact (Spec.map_id _).symm)
  have hclosed : (closedPoints G.val.X.left).Finite := by
    apply Set.finite_coe_iff.mp
    apply Finite.of_injective p
    intro x y h
    apply Subtype.ext
    have h' := congrArg (fun p : Points G.val.X (CommAlgCat.of K K) => p.left (IsLocalRing.closedPoint K)) h
    change pointOfClosedPoint G.val.X.hom x.val x.property (IsLocalRing.closedPoint K) =
      pointOfClosedPoint G.val.X.hom y.val y.property (IsLocalRing.closedPoint K) at h'
    rw [pointOfClosedPoint_apply, pointOfClosedPoint_apply] at h'
    exact h'
  have : DiscreteTopology G.val.X.left := JacobsonSpace.discreteTopology hclosed
  have : Subsingleton G.val.X.left := subsingleton_of_preconnected_totallyDisconnected
  let N := Specs.GeometricRadicals.identitySubgroup G
  have := N.isClosedImmersion
  have hsurj : Function.Surjective N.inclusion.hom.hom.left :=
    fun x => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩
  have : AlgebraicGeometry.Surjective N.inclusion.hom.hom.left := ⟨hsurj⟩
  have := isIso_of_isClosedImmersion_of_surjective N.inclusion.hom.hom.left
  let _ := isIso_of_schemeIso N.inclusion
  exact ⟨(asIso N.inclusion).symm⟩

private theorem fieldSpin_reductive : IsReductive (fieldSpinGroup k) := by
  classical
  refine ⟨fieldSpin_smooth k, fieldSpin_geometricallyConnected k, ?_⟩
  let K := AlgebraicClosure k
  let R := CommAlgCat.of K K
  let G := GeometricGroup (fieldSpinGroup k)
  let N := Specs.GeometricRadicals.geometricUnipotentRadical (fieldSpinGroup k)
  let H := closedSubgroupAlgebraicGroup (G := G) N
  have hN := LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest (fieldSpinGroup k)
  obtain ⟨A, ⟨e⟩, hinv⟩ := hN.2.1
  let β := (hopfSpecPointIso A) ≪≫ (groupPointsFunctor K).mapIso e
  let α := β.hom ≫ (groupPointsFunctor K).map N.inclusion ≫ geometricVectorPoints k
  obtain ⟨x, hx, hfix⟩ := vectorPoints_fixed_vector A hinv α
  let W : Submodule K (PairIndex 4 → K) :=
    { carrier := {w | ∀ n : Points N.group.X R, geometricVectorMatrix k R
        (n ≫ N.inclusion.hom.hom) *ᵥ w = w}
      zero_mem' := fun _ => Matrix.mulVec_zero _
      add_mem' := fun {v w} hv hw n => by
        change _ *ᵥ (v + w) = v + w
        rw [Matrix.mulVec_add, hv n, hw n]
      smul_mem' := fun c {w} hw n => by
        change _ *ᵥ (c • w) = c • w
        rw [Matrix.mulVec_smul, hw n] }
  have hw : (fun i : PairIndex 4 => x (ULift.up i)) ∈ W := by
    intro n
    let eR := (β.app R).groupIsoToMulEquiv
    let f := eR.symm n
    have hf : (β.hom.app R) f = n := eR.apply_symm_apply n
    have h := hfix f
    change ((geometricVectorPoints k).app R ((β.hom.app R f) ≫ N.inclusion.hom.hom)).val *ᵥ x = x at h
    rw [hf] at h
    funext i
    have hi := congrFun h (ULift.up i)
    change (∑ j : ULift.{u} (PairIndex 4),
      geometricVectorMatrix k R (n ≫ N.inclusion.hom.hom) i j.down * x j) = x (ULift.up i) at hi
    change (∑ j : PairIndex 4,
      geometricVectorMatrix k R (n ≫ N.inclusion.hom.hom) i j * x (ULift.up j)) = x (ULift.up i)
    rwa [← Equiv.sum_comp (Equiv.ulift.symm : PairIndex 4 ≃ ULift.{u} (PairIndex 4))
      (fun j => geometricVectorMatrix k R (n ≫ N.inclusion.hom.hom) i j.down * x j)] at hi
  have hWne : W ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hw
    apply hx
    funext i
    exact congrFun hw i.down
  have hstable (g : Points G.val.X R) (w : PairIndex 4 → K) (hw : w ∈ W) :
      geometricVectorMatrix k R g *ᵥ w ∈ W := by
    intro n
    let b := n ≫ N.inclusion.hom.hom
    have hn := sections_normal hN.1.2.2 ((testSpec K).obj (op R))
    obtain ⟨m, hm⟩ := hn.conj_mem b ⟨n, rfl⟩ g⁻¹
    have hb : b * g = g * (m ≫ N.inclusion.hom.hom) := by
      change (m ≫ N.inclusion.hom.hom) = g⁻¹ * b * (g⁻¹)⁻¹ at hm
      rw [hm, inv_inv, ← mul_assoc, mul_inv_cancel_left]
    have hM := congrArg (geometricVectorMatrix k R) hb
    rw [map_mul, map_mul] at hM
    rw [mulVec_mulVec, hM, ← mulVec_mulVec, hw m]
  have hWt : W = ⊤ := by
    apply (vectorIrreducibility_proof K W ?_).resolve_left hWne
    intro a ha M hM w hw
    let y : spinUnitsAt k (geometricTest k R) := ⟨a, ha⟩
    let g := (geometricPoint k R).symm ((fieldSpinPoints k (geometricTest k R)).symm y)
    have hg : geometricVectorMatrix k R g = M := by
      change spinVectorMatrix k (geometricTest k R) (geometricPoint k R g) = M
      dsimp only [g]
      rw [MulEquiv.apply_symm_apply]
      apply action_matrix_unique (spinVectorMatrix_valid k _ _)
      change HasActionMatrix 4 ((fieldSpinPoints k (geometricTest k R))
        ((fieldSpinPoints k (geometricTest k R)).symm y)).val M
      rw [MulEquiv.apply_symm_apply]
      exact hM
    exact hg ▸ hstable g w hw
  have htriv (n : Points N.group.X R) : geometricVectorMatrix k R
      (n ≫ N.inclusion.hom.hom) = 1 := by
    ext i j
    have hh : (Pi.single j (1 : K) : PairIndex 4 → K) ∈ W := hWt.symm ▸ Submodule.mem_top
    have hh' := congrFun (hh n) i
    simpa [Matrix.mulVec_single, Pi.single_apply, Matrix.one_apply, eq_comm] using hh'
  exact trivial_of_finite_rational_points H hN.1.1 hN.1.2.1
    (finite_rational_points_of_trivial_vector k N htriv)

end
end Reductivity

section RootShears

open SplitSpinSpecification Matrix CliffordAlgebra
open scoped Matrix

noncomputable section

open private splitBasis splitForm splitCoordinates splitE splitF split_e_norm split_f_norm
  split_e_polar split_f_polar split_coordinates_e split_coordinates_f integralCliffordEquiv
  action_matrix_on_vectors unitConj from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin
open private cliffordEquiv_vector cliffordEquiv_even vectors_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
open private baseChangeEquiv_reverse from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.CliffordModel

set_option backward.isDefEq.respectTransparency false

private def hyperbolicIndex : PairIndex 4 → Fin 4 := Sum.elim id id

variable {R : Type u} [CommRing R] [Algebra ℤ R]

private theorem hyperbolic_polar_basis (i j : PairIndex 4) :
    QuadraticMap.polar (splitForm 4 R) (splitBasis 4 R i) (splitBasis 4 R j) =
      if j = i.swap then 1 else 0 := by
  rcases i with i | i <;> rcases j with j | j
  · change QuadraticMap.polar _ (splitE i) (splitE j) = _
    rw [split_e_polar, split_coordinates_e]
    rfl
  · change QuadraticMap.polar _ (splitE i) (splitF j) = _
    rw [split_e_polar, split_coordinates_f]
    simp [Pi.single_apply, eq_comm]
  · change QuadraticMap.polar _ (splitF i) (splitE j) = _
    rw [split_f_polar, split_coordinates_e]
    simp [Pi.single_apply, eq_comm]
  · change QuadraticMap.polar _ (splitF i) (splitF j) = _
    rw [split_f_polar, split_coordinates_f]
    rfl

private theorem shear_isotropic (i : PairIndex 4) : splitForm 4 R (splitBasis 4 R i) = 0 :=
  i.rec split_e_norm split_f_norm

private theorem shear_orthogonal {i j : PairIndex 4} (hij : hyperbolicIndex i ≠ hyperbolicIndex j) :
    QuadraticMap.polar (splitForm 4 R) (splitBasis 4 R i) (splitBasis 4 R j) = 0 := by
  rw [hyperbolic_polar_basis, ite_eq_right_iff]
  intro he
  exfalso
  apply hij
  rw [he]
  cases i <;> rfl

private def hyperbolicVector (R : Type u) [CommRing R] [Algebra ℤ R] (i : PairIndex 4) :
    ScalarClifford 4 R :=
  SpinSpecification.vectors (integralForm 4) R (splitBasis 4 R i)

private def shearPolynomial (R : Type u) [CommRing R] [Algebra ℤ R]
    (i j : PairIndex 4) (t : R) : ScalarClifford 4 R :=
  1 + t • (hyperbolicVector R i * hyperbolicVector R j)

private theorem shearPolynomial_intrinsic (i j : PairIndex 4) (t : R) :
    integralCliffordEquiv 4 R (shearPolynomial R i j t) =
      1 + t • (CliffordAlgebra.ι (splitForm 4 R) (splitBasis 4 R i) * CliffordAlgebra.ι (splitForm 4 R) (splitBasis 4 R j)) := by
  rw [shearPolynomial, map_add, map_one, map_smul, map_mul]
  exact congrArg (fun c : CliffordAlgebra (splitForm 4 R) => 1 + t • c)
    (congrArg₂ (· * ·)
      (cliffordEquiv_vector (integralForm 4) R (hyperbolicBasis ℤ 4) _)
      (cliffordEquiv_vector (integralForm 4) R (hyperbolicBasis ℤ 4) _))

private theorem shearPolynomial_spin (i j : PairIndex 4) (hij : hyperbolicIndex i ≠ hyperbolicIndex j)
    (t : R) : ∃ a : (ScalarClifford 4 R)ˣ,
      a ∈ SpinSpecification.spinUnits (integralForm 4) R ∧ a.val = shearPolynomial R i j t := by
  let q := splitForm 4 R
  let Q := integralForm 4
  let E := integralCliffordEquiv 4 R
  let v := splitBasis 4 R i
  let w := splitBasis 4 R j
  let ξ := CliffordAlgebra.ι q v * CliffordAlgebra.ι q w
  let c := 1 + t • ξ
  have hp : QuadraticMap.polar q v w = 0 := shear_orthogonal hij
  obtain ⟨he, hn, hm, hf⟩ :=
    SplitSpin.cliffordElementaryShear q v w (shear_isotropic i) (shear_isotropic j) hp t
  let b : (CliffordAlgebra q)ˣ := ⟨c, reverse c, hm, hn⟩
  let a := Units.map E.symm.toMonoidHom b
  have hav : E (a : ScalarClifford 4 R) = c := E.apply_symm_apply _
  have hai : E (↑a⁻¹ : ScalarClifford 4 R) = reverse c := by
    dsimp only [a]
    rw [← map_inv]
    exact E.apply_symm_apply _
  have hr : reverse c = 1 + (-t) • ξ := by
    have hew : CliffordAlgebra.ι q w * CliffordAlgebra.ι q v = -(CliffordAlgebra.ι q v * CliffordAlgebra.ι q w) := by
      apply eq_neg_of_add_eq_zero_left
      rw [add_comm, ι_mul_ι_add_swap, hp, map_zero]
    simp [c, ξ, reverse.map_mul, hew]
  obtain ⟨_, _, _, hb⟩ :=
    SplitSpin.cliffordElementaryShear q v w (shear_isotropic i) (shear_isotropic j) hp (-t)
  have hEV (x : ExtendedModule 4 R) :
      E (SpinSpecification.vectors Q R x) = CliffordAlgebra.ι q x :=
    cliffordEquiv_vector Q R (hyperbolicBasis ℤ 4) x
  refine ⟨a, ⟨?_, ?_, ?_, ?_⟩, E.injective (hav.trans (shearPolynomial_intrinsic i j t).symm)⟩
  · apply (cliffordEquiv_even Q R (hyperbolicBasis ℤ 4) _).mp
    exact hav.symm ▸ he
  · apply E.injective
    change E (SpinSpecification.reversion Q R a * (a : ScalarClifford 4 R)) = E 1
    rw [map_mul, map_one, show E (SpinSpecification.reversion Q R a) = reverse (E a) from
      baseChangeEquiv_reverse R Q (hyperbolicBasis ℤ 4) _, hav]
    exact hn
  · rintro _ ⟨x, rfl⟩
    refine ⟨x + t • (QuadraticMap.polar q w x • v - QuadraticMap.polar q v x • w), ?_⟩
    apply E.injective
    rw [hEV, SpinSpecification.conjugate, map_mul, map_mul, hav, hai, hEV]
    exact (hf x).symm
  · rintro _ ⟨x, rfl⟩
    refine ⟨x + (-t) • (QuadraticMap.polar q w x • v - QuadraticMap.polar q v x • w), ?_⟩
    apply E.injective
    rw [hEV, SpinSpecification.conjugate, map_mul, map_mul, inv_inv, hai, hav, hEV]
    have h := hb x
    change (1 + (-t) • ξ) * CliffordAlgebra.ι q x * reverse (1 + (-t) • ξ) = _ at h
    rw [← hr, reverse_reverse] at h
    exact h.symm

variable {S : Type u} [CommRing S] [Algebra ℤ S]

private theorem shearPolynomial_map (f : R →ₐ[ℤ] S) (i j : PairIndex 4) (t : R) :
    SpinSpecification.coefficientMap (integralForm 4) R f (shearPolynomial R i j t) =
      shearPolynomial S i j (f t) := by
  let F := SpinSpecification.coefficientMap (integralForm 4) R f
  have hs : F (algebraMap R (ScalarClifford 4 R) t) =
      algebraMap S (ScalarClifford 4 S) (f t) := by
    simp [F, SpinSpecification.coefficientMap, Algebra.TensorProduct.algebraMap_apply]
  have hv (l : PairIndex 4) : F (hyperbolicVector R l) = hyperbolicVector S l := by
    cases l with
    | inl l => exact coefficientMap_creation f l
    | inr l => exact coefficientMap_contraction f l
  change F (shearPolynomial R i j t) = _
  simp only [shearPolynomial, Algebra.smul_def, map_add, map_one, map_mul, hs, hv]

private theorem diagonal_conjugates_shear
    (a : (ScalarClifford 4 R)ˣ) (z : PairIndex 4 → R) (h : HasActionMatrix 4 a (Matrix.diagonal z))
    (i j : PairIndex 4) (t : R) :
    unitConj a (shearPolynomial R i j t) = shearPolynomial R i j (t * (z i * z j)) := by
  have hZ (l : PairIndex 4) :
      unitConj a (hyperbolicVector R l) = z l • hyperbolicVector R l := by
    rw [hyperbolicVector, action_matrix_on_vectors h, ← map_smul]
    congr 1
    apply (splitCoordinates 4 R).injective
    rw [LinearEquiv.apply_symm_apply, map_smul]
    have h : splitCoordinates 4 R (splitBasis 4 R l) = Pi.single l 1 := by
      funext b
      change (splitBasis 4 R).equivFun ((splitBasis 4 R) l) b = _
      simpa only [Pi.single_apply, eq_comm] using (splitBasis 4 R).equivFun_self l b
    rw [h, Matrix.diagonal_mulVec_single]
    funext j
    by_cases hj : j = l <;> simp [hj, Pi.smul_apply]
  have hmul (x y : ScalarClifford 4 R) :
      unitConj a (x * y) = unitConj a x * unitConj a y := by simp [unitConj, mul_assoc]
  have hsmul (r : R) (x : ScalarClifford 4 R) :
      unitConj a (r • x) = r • unitConj a x := by simp only [unitConj, mul_smul_comm, smul_mul_assoc]
  calc
    _ = 1 + t • unitConj a (hyperbolicVector R i * hyperbolicVector R j) := by
      rw [shearPolynomial, unitConj, mul_add, add_mul, mul_one, Units.mul_inv]
      exact congrArg (1 + ·) (hsmul _ _)
    _ = _ := by
      rw [hmul, hZ, hZ, smul_mul_assoc, mul_smul_comm, ← mul_smul, ← mul_smul]
      rw [mul_assoc]
      rfl

private theorem shearPolynomial_ne_one (i j : PairIndex 4)
    (hij : hyperbolicIndex i ≠ hyperbolicIndex j) {t : R} (ht : t ≠ 0) :
    shearPolynomial R i j t ≠ 1 := by
  intro he
  let q := splitForm 4 R
  let v := splitBasis 4 R i
  let w := splitBasis 4 R j
  let x := splitBasis 4 R j.swap
  let c := 1 + t • (CliffordAlgebra.ι q v * CliffordAlgebra.ι q w)
  have hc : c = 1 := (shearPolynomial_intrinsic i j t).symm.trans
    ((congrArg (integralCliffordEquiv 4 R) he).trans (map_one _))
  obtain ⟨_, _, _, hs⟩ := SplitSpin.cliffordElementaryShear q v w (shear_isotropic i)
    (shear_isotropic j) (shear_orthogonal hij) t
  have hwx : QuadraticMap.polar q w x = 1 := by
    change QuadraticMap.polar (splitForm 4 R) (splitBasis 4 R j) (splitBasis 4 R j.swap) = 1
    simp only [hyperbolic_polar_basis, ↓reduceIte]
  have hvx : QuadraticMap.polar q v x = 0 := by
    apply shear_orthogonal
    cases j <;> exact hij
  have hx := hs x
  change c * CliffordAlgebra.ι q x * reverse c = _ at hx
  rw [hc, reverse.map_one, one_mul, mul_one, hwx, hvx, one_smul, zero_smul, sub_zero] at hx
  have hι : Function.Injective (CliffordAlgebra.ι q) := by
    intro v w h
    apply vectors_injective (integralForm 4) R (hyperbolicBasis ℤ 4)
    apply (integralCliffordEquiv 4 R).injective
    exact (cliffordEquiv_vector (integralForm 4) R (hyperbolicBasis ℤ 4) v).trans
      (h.trans (cliffordEquiv_vector (integralForm 4) R (hyperbolicBasis ℤ 4) w).symm)
  have hv := add_left_cancel (show x + 0 = x + t • v from (add_zero x).trans (hι hx))
  apply ht
  have hv' := congrArg ((splitBasis 4 R).coord i) hv
  simpa only [v, map_zero, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, mul_one, smul_eq_mul] using hv'.symm

end
end RootShears

section AbsoluteRoots

open LinearAlgebraicGroups.Specs
open AlgebraicGeometry CategoryTheory Opposite
open SplitSpinSpecification Matrix TrivSqZeroExt
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (adjointWeightVectors absoluteRoots characterValue)
open Specs.AdjointRepresentation (dualMap constants scale reduction)
open scoped Matrix CategoryTheory.MonObj

noncomputable section

open private action_matrix_unique unitConj from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

variable (k : Type u) [Field k]

private abbrev tangentBase := CommAlgCat.of k k

private abbrev tangentTest (R : TestAlgebra k) := CommAlgCat.of k (DualNumber R)

private abbrev spinTangent := Lie k (fieldSpinGroup k).val

private abbrev tangentExtension (R : TestAlgebra k) : tangentTest k (tangentBase k) ⟶ tangentTest k R :=
  dualMap (CommAlgCat.ofHom (Algebra.ofId k R))

private theorem spinCoordinatePoint_map {R S : TestAlgebra k} (f : R ⟶ S)
    (p : Points (fieldSpinGroup k).val.X R) :
    spinCoordinatePoint k S (mapPoints f p) = f.hom.comp (spinCoordinatePoint k R p) := by
  obtain ⟨q, rfl⟩ := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_surjective p
  change spinCoordinatePoint k S ((testSpec k).map f.op ≫ (testSpec k).map q) = _
  rw [← Functor.map_comp]
  change (((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      ((testSpec k).map (f.op ≫ q))).unop).hom =
    f.hom.comp (((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      ((testSpec k).map q)).unop).hom
  rw [Functor.FullyFaithful.preimage_map, Functor.FullyFaithful.preimage_map]
  rfl

private theorem spin_tangent_scale_injective (v : spinTangent k) (hv : v ≠ 0) (R : TestAlgebra k) :
    Function.Injective (fun a : R =>
      mapPoints (scale R a) (mapPoints (tangentExtension k R) v.toMul.val)) := by
  let D := tangentTest k (tangentBase k)
  let x := spinCoordinatePoint k D v.toMul.val
  let y := spinCoordinatePoint k D (1 : Points (fieldSpinGroup k).val.X D)
  have hred : mapPoints (reduction (tangentBase k)) v.toMul.val =
      (1 : Points (fieldSpinGroup k).val.X (tangentBase k)) := v.toMul.property
  have hbase (z : fieldSpinRing k) : (x z).fst = (y z).fst := by
    have hone : mapPoints (reduction (tangentBase k))
        (1 : Points (fieldSpinGroup k).val.X D) = 1 :=
      (((groupPointsFunctor k).obj (fieldSpinGroup k).val).map
        (reduction (tangentBase k))).hom.map_one
    have h := congrArg (fun p => spinCoordinatePoint k (tangentBase k) p z) (hred.trans hone.symm)
    rw [spinCoordinatePoint_map, spinCoordinatePoint_map] at h
    exact h
  have hzero (z : fieldSpinRing k) : (y z).snd = 0 := by
    have hOne : mapPoints (constants (tangentBase k))
        (1 : Points (fieldSpinGroup k).val.X (tangentBase k)) =
        (1 : Points (fieldSpinGroup k).val.X D) :=
      (((groupPointsFunctor k).obj (fieldSpinGroup k).val).map (constants (tangentBase k))).hom.map_one
    have h := congrArg (fun p => (spinCoordinatePoint k D p z).snd) hOne
    rw [spinCoordinatePoint_map] at h
    exact h.symm
  have hex : ∃ z : fieldSpinRing k, (x z).snd ≠ 0 := by
    by_contra! h
    apply hv
    apply Subtype.ext
    apply (spinCoordinatePoint k D).injective
    apply AlgHom.ext
    intro z
    exact TrivSqZeroExt.ext (hbase z) ((h z).trans (hzero z).symm)
  obtain ⟨z, hz⟩ := hex
  intro a b hab
  have h := congrArg (fun p => (spinCoordinatePoint k (tangentTest k R) p z).snd) hab
  dsimp only at h
  rw [spinCoordinatePoint_map, spinCoordinatePoint_map, spinCoordinatePoint_map, spinCoordinatePoint_map] at h
  change a * algebraMap k R (x z).snd = b * algebraMap k R (x z).snd at h
  exact ((isUnit_iff_ne_zero.mpr hz).map (algebraMap k R)).mul_right_cancel h

private def tangentMatrix (v : spinTangent k) : Matrix (PairIndex 4) (PairIndex 4) k :=
  fun i j => (spinVectorMatrix k (tangentTest k (tangentBase k)) v.toMul.val i j).snd

private theorem tangentMatrix_norm (v : spinTangent k) :
    IsAlternating (tangentMatrix k v).toBlocks₂₁ ∧ IsAlternating (tangentMatrix k v).toBlocks₁₂ := by
  let D := tangentTest k (tangentBase k)
  let M := spinVectorMatrix k D v.toMul.val
  have hm : PreservesNorm M := by
    obtain ⟨N, ⟨hN, h⟩, _⟩ := SplitSpin.spinMatrix 4 D (fieldSpinPoints k D v.toMul.val).val
      (fieldSpinPoints k D v.toMul.val).property
    have hh := action_matrix_unique (spinVectorMatrix_valid k D v.toMul.val) hN
    change PreservesNorm (spinVectorMatrix k D v.toMul.val)
    rw [hh]
    exact h
  have h₀ : M.map (fstHom k k k) = 1 := by
    have h : mapPoints (reduction (tangentBase k)) v.toMul.val =
        (1 : Points (fieldSpinGroup k).val.X (tangentBase k)) := v.toMul.property
    have hh := spinVectorMatrix_natural k (reduction (tangentBase k)) v.toMul.val
    rw [h, spinVectorMatrix_one] at hh
    exact hh.symm
  exact ⟨(tangent_norm_blocks M hm h₀).1, (tangent_norm_blocks M hm h₀).2.1⟩

private theorem tangent_diagonal_commutes (v : spinTangent k)
    (hv : ∀ i j, i ≠ j → tangentMatrix k v i j = 0)
    (R : TestAlgebra k) (t : Points (splitDiagonalGroup k).X R) :
    let p := mapPoints (tangentExtension k R) v.toMul.val
    let g := mapPoints (constants R) (t ≫ (diagonalInclusion k).hom.hom)
    g * p * g⁻¹ = p := by
  let D := tangentTest k (tangentBase k)
  have h : mapPoints (reduction (tangentBase k)) v.toMul.val =
      (1 : Points (fieldSpinGroup k).val.X (tangentBase k)) := v.toMul.property
  have h₀ : (spinVectorMatrix k D v.toMul.val).map (fstHom k k k) = 1 := by
    have hh := spinVectorMatrix_natural k (reduction (tangentBase k)) v.toMul.val
    rw [h, spinVectorMatrix_one] at hh
    exact hh.symm
  obtain ⟨q, hq⟩ := (diagonalInclusion_range k D v.toMul.val).mpr (by
    intro i j hij
    apply TrivSqZeroExt.ext
    · have h := congrArg (fun M : Matrix (PairIndex 4) (PairIndex 4) k => M i j) h₀
      change (spinVectorMatrix k D v.toMul.val i j).fst = (1 : Matrix (PairIndex 4) (PairIndex 4) k) i j at h
      rw [Matrix.one_apply_ne hij] at h
      exact h
    · exact hv i j hij)
  have hp : mapPoints (tangentExtension k R) v.toMul.val =
      mapPoints (tangentExtension k R) q ≫ (diagonalInclusion k).hom.hom := by
    rw [← hq]
    exact (Category.assoc _ _ _).symm
  have hg : mapPoints (constants R) (t ≫ (diagonalInclusion k).hom.hom) =
      mapPoints (constants R) t ≫ (diagonalInclusion k).hom.hom := (Category.assoc _ _ _).symm
  change _ * _ * _⁻¹ = _
  rw [hp, hg, mul_inv_eq_iff_eq_mul, ← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]

private theorem absoluteRoot_not_diagonal
    (detect : Specs.CharacterPairing.CharacterValuesDetectCharacters.{u})
    (hunit : ∀ (R : TestAlgebra k) (t : Points (splitDiagonalGroup k).X R),
      characterValue (1 : Character (splitDiagonalGroup k)) R t = 1)
    {χ : Character (splitDiagonalGroup k)} {v : spinTangent k}
    (hχ : χ ≠ 1) (hv : v ≠ 0) (hw : v ∈ adjointWeightVectors (diagonalSubgroup k) χ) :
    ∃ i j, i ≠ j ∧ tangentMatrix k v i j ≠ 0 := by
  by_contra! h
  apply hχ
  apply detect (splitDiagonalGroup_split k)
  intro R t
  rw [hunit]
  have he := (tangent_diagonal_commutes k v h R t).symm.trans (hw R t)
  have h₁ : scale R 1 = 𝟙 _ := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    exact TrivSqZeroExt.ext rfl (one_mul z.snd)
  apply spin_tangent_scale_injective k v hv R
  change mapPoints (scale R (characterValue χ R t)) (mapPoints (tangentExtension k R) v.toMul.val) =
    mapPoints (scale R 1) (mapPoints (tangentExtension k R) v.toMul.val)
  rw [h₁]
  change _ = (testSpec k).map (𝟙 _) ≫ _
  rw [(testSpec k).map_id (op (tangentTest k R)), Category.id_comp]
  exact he.symm

private theorem tangent_coefficient_weight
    (v : spinTangent k) {χ : Character (splitDiagonalGroup k)}
    (hχ : v ∈ adjointWeightVectors (diagonalSubgroup k) χ)
    {i j : PairIndex 4} (h : tangentMatrix k v i j ≠ 0)
    (R : TestAlgebra k) (t : Points (splitDiagonalGroup k).X R) :
    characterValue χ R t =
      ((Additive.toMul (evaluate (diagonalGroupPoints k R t) (vectorWeight i - vectorWeight j)) : Rˣ) : R) := by
  let D := tangentTest k R
  let p := mapPoints (tangentExtension k R) v.toMul.val
  let g := mapPoints (constants R) (t ≫ (diagonalInclusion k).hom.hom)
  let r := characterValue χ R t
  let z := diagonalGroupPoints k R t
  let c := algebraMap k R (tangentMatrix k v i j)
  have hp : (spinVectorMatrix k D p i j).snd = c := by
    rw [spinVectorMatrix_natural]
    rfl
  have hD : spinVectorMatrix k D g =
      Matrix.diagonal (fun l => algebraMap R (DualNumber R) (vectorEigenvalue z l)) := by
    rw [spinVectorMatrix_natural, diagonalInclusion_matrix, middle_diagonal, Matrix.diagonal_map (map_zero (constants R).hom)]
    rfl
  have hsc : (spinVectorMatrix k D (mapPoints (scale R r) p) i j).snd = r * c := by
    rw [spinVectorMatrix_natural]
    exact congrArg (fun x => r * x) hp
  have he : g * p = mapPoints (scale R r) p * g := mul_inv_eq_iff_eq_mul.mp (hχ R t)
  have hm := congrArg (spinVectorMatrix k D) he
  rw [spinVectorMatrix_mul, spinVectorMatrix_mul, hD] at hm
  let L (l : PairIndex 4) := algebraMap R (DualNumber R) (vectorEigenvalue z l)
  have hm' : ((diagonal L * spinVectorMatrix k D p) i j).snd =
      ((spinVectorMatrix k D (mapPoints (scale R r) p) * diagonal L) i j).snd :=
    congrArg (fun M : Matrix (PairIndex 4) (PairIndex 4) (DualNumber R) => (M i j).snd) hm
  dsimp only [L] at hm'
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, DualNumber.snd_mul,
    algebraMap_eq_inl, fst_inl, snd_inl, zero_mul, add_zero, hp] at hm'
  have hRight :
      (spinVectorMatrix k D (mapPoints (scale R r) p) i j *
        (TrivSqZeroExt.inl (vectorEigenvalue z j) : DualNumber R)).snd =
          r * c * vectorEigenvalue z j := by
    change (spinVectorMatrix k D (mapPoints (scale R r) p) i j).fst * 0 +
      (spinVectorMatrix k D (mapPoints (scale R r) p) i j).snd * vectorEigenvalue z j = _
    rw [hsc, mul_zero, zero_add]
  rw [hRight] at hm'
  have hc : IsUnit c := (isUnit_iff_ne_zero.mpr h).map (algebraMap k R)
  have heval (l : PairIndex 4) := vectorWeight_value z l
  have hcancel : vectorEigenvalue z i = r * vectorEigenvalue z j := by
    apply hc.mul_right_cancel
    rw [mul_right_comm r]
    exact hm'
  let a : Rˣ := Additive.toMul (evaluate z (vectorWeight i))
  let b : Rˣ := Additive.toMul (evaluate z (vectorWeight j))
  change r = (Additive.toMul (evaluate z (vectorWeight i - vectorWeight j)) : Rˣ).val
  rw [map_sub]
  change r = ((a / b : Rˣ) : R)
  apply b.isUnit.mul_right_cancel
  rw [← heval i, ← heval j] at hcancel
  calc
    r * (b : R) = (a : R) := hcancel.symm
    _ = ((a / b : Rˣ) : R) * (b : R) := by simp [div_eq_mul_inv, mul_assoc]

/-- A nonzero off-diagonal tangent coefficient detects its weight on every test algebra. -/
private theorem absoluteRoots_mapsTo
    (detect : Specs.CharacterPairing.CharacterValuesDetectCharacters.{u})
    (C : Additive (Character (splitDiagonalGroup k)) ≃ₗ[ℤ] CharacterExponents)
    (ev : ∀ (R : TestAlgebra k) (t : Points (splitDiagonalGroup k).X R)
      (χ : Character (splitDiagonalGroup k)),
      characterValue χ R t = ((Additive.toMul (evaluate (diagonalGroupPoints k R t) (C (Additive.ofMul χ))) : Rˣ) : R)) :
    Set.MapsTo (fun χ : Character (splitDiagonalGroup k) => C (Additive.ofMul χ))
      (absoluteRoots (diagonalSubgroup k)) rootCharacters := by
  rintro χ ⟨hχ, v, hv, hne⟩
  have hunit (R : TestAlgebra k) (t : Points (splitDiagonalGroup k).X R) :
      characterValue (1 : Character (splitDiagonalGroup k)) R t = 1 := by
    rw [ev]
    change ((Additive.toMul (evaluate _ (C 0)) : Rˣ) : R) = 1
    rw [C.map_zero, map_zero]
    rfl
  obtain ⟨i, j, hij, hB⟩ := absoluteRoot_not_diagonal k detect hunit hχ hne hv
  let ψ := Additive.toMul (C.symm (vectorWeight i - vectorWeight j))
  have hEq : χ = ψ := by
    apply detect (splitDiagonalGroup_split k)
    intro R t
    rw [ev R t ψ]
    change characterValue χ R t = ((Additive.toMul (evaluate _ (C (C.symm _))) : Rˣ) : R)
    rw [C.apply_symm_apply]
    exact tangent_coefficient_weight k v hv hB R t
  rw [hEq]
  change C (C.symm _) ∈ rootCharacters
  rw [C.apply_symm_apply]
  have hnorm := tangentMatrix_norm k v
  exact tangent_entry_root _ hnorm.1 hnorm.2 hij hB

private theorem fieldSpin_clifford_value_map {R S : TestAlgebra k} (f : R ⟶ S)
    (p : Points (fieldSpinGroup k).val.X R) :
    (fieldSpinRepresentation k S (mapPoints f p)).val =
      SpinSpecification.coefficientMap (integralForm 4) R (f.hom.restrictScalars ℤ)
        (fieldSpinRepresentation k R p).val :=
  congrArg Units.val ((fieldSpinPresentation k).2 f p)

/-- The shear at the dual-number generator supplies a nonzero tangent in the specified weight. -/
private theorem shear_gives_weight {χ : Character (splitDiagonalGroup k)}
    (i j : PairIndex 4) (hij : hyperbolicIndex i ≠ hyperbolicIndex j)
    (hχ : ∀ (R : TestAlgebra k) (t : Points (splitDiagonalGroup k).X R),
      characterValue χ R t =
        vectorEigenvalue (diagonalGroupPoints k R t) i * vectorEigenvalue (diagonalGroupPoints k R t) j) :
    ∃ v ∈ adjointWeightVectors (diagonalSubgroup k) χ, v ≠ 0 := by
  let R₀ := tangentBase k
  let D₀ := tangentTest k R₀
  let δ : DualNumber k := TrivSqZeroExt.inr 1
  obtain ⟨a, ha, haVal⟩ := shearPolynomial_spin (R := DualNumber k) i j hij δ
  let p := (fieldSpinPoints k D₀).symm ⟨a, ha⟩
  have hp : (fieldSpinRepresentation k D₀ p).val = shearPolynomial (DualNumber k) i j δ := by
    exact (congrArg (fun b : SpinFunctor.Spin (integralForm 4) D₀ (hyperbolicBasis ℤ 4) =>
      b.val.val) ((fieldSpinPoints k D₀).apply_symm_apply ⟨a, ha⟩)).trans haVal
  have hred : mapPoints (reduction R₀) p = (1 : Points (fieldSpinGroup k).val.X R₀) := by
    apply ((fieldSpinPresentation k).1 R₀).1
    apply Units.ext
    rw [fieldSpin_clifford_value_map, hp, shearPolynomial_map, map_one]
    change shearPolynomial k i j 0 = 1
    simp [shearPolynomial]
  have hnp : p ≠ 1 := by
    intro h
    apply shearPolynomial_ne_one i j hij
      (show δ ≠ (0 : DualNumber k) from fun h₀ => one_ne_zero (congrArg snd h₀))
    rw [← hp, h, map_one]
    rfl
  let v : spinTangent k := Additive.ofMul ⟨p, hred⟩
  refine ⟨v, ?_, fun hv => hnp (congrArg (fun v : spinTangent k => v.toMul.val) hv)⟩
  intro R t
  let D := tangentTest k R
  let q := mapPoints (tangentExtension k R) p
  let g := mapPoints (constants R) (t ≫ (diagonalInclusion k).hom.hom)
  let r := characterValue χ R t
  let z := diagonalGroupPoints k R t
  let M (l : PairIndex 4) := algebraMap R (DualNumber R) (vectorEigenvalue z l)
  have hg : HasActionMatrix 4 (fieldSpinRepresentation k D g) (Matrix.diagonal M) := by
    have hh := spinVectorMatrix_valid k D g
    dsimp only [g] at hh
    rw [spinVectorMatrix_natural, diagonalInclusion_matrix, middle_diagonal, Matrix.diagonal_map (map_zero (constants R).hom)] at hh
    exact hh
  have hq : (fieldSpinRepresentation k D q).val =
      shearPolynomial (DualNumber R) i j (TrivSqZeroExt.inr 1) := by
    rw [fieldSpin_clifford_value_map, hp, shearPolynomial_map]
    congr 1
    change (algebraMap k R 0, algebraMap k R 1) = _
    exact TrivSqZeroExt.ext (map_zero _) (map_one _)
  have hs : (fieldSpinRepresentation k D (mapPoints (scale R r) q)).val =
      shearPolynomial (DualNumber R) i j (TrivSqZeroExt.inr r) := by
    rw [fieldSpin_clifford_value_map, hq, shearPolynomial_map]
    congr 1
    exact TrivSqZeroExt.ext rfl (mul_one _)
  change g * q * g⁻¹ = mapPoints (scale R r) q
  apply ((fieldSpinPresentation k).1 D).1
  apply Units.ext
  rw [map_mul, map_mul, map_inv]
  change unitConj (fieldSpinRepresentation k D g) (fieldSpinRepresentation k D q).val = _
  rw [hq, diagonal_conjugates_shear _ _ hg, hs]
  congr 1
  rw [show r = _ from hχ R t]
  apply TrivSqZeroExt.ext
  · change (0 : R) * (vectorEigenvalue z i * vectorEigenvalue z j) = 0
    exact zero_mul _
  · change (0 : R) * (vectorEigenvalue z i * 0 + 0 * vectorEigenvalue z j) +
      1 * (vectorEigenvalue z i * vectorEigenvalue z j) = vectorEigenvalue z i * vectorEigenvalue z j
    rw [zero_mul, zero_add, one_mul]

private theorem rootCharacters_signed_pair {r : CharacterExponents} (hr : r ∈ rootCharacters) :
    ∃ i j, hyperbolicIndex i ≠ hyperbolicIndex j ∧ r = vectorWeight i + vectorWeight j := by
  obtain ⟨x, ⟨i, j, h, hx | hx | hx⟩, rfl⟩ := hr
  · exact ⟨.inl i, .inl j, h, by rw [hx, map_add]; rfl⟩
  · exact ⟨.inl i, .inr j, h, by rw [hx, map_sub, sub_eq_add_neg]; rfl⟩
  · exact ⟨.inr i, .inr j, h, by rw [hx, map_sub, map_neg, sub_eq_add_neg]; rfl⟩

private theorem absoluteRoots_coordinates
    (detect : Specs.CharacterPairing.CharacterValuesDetectCharacters.{u})
    (C : Additive (Character (splitDiagonalGroup k)) ≃ₗ[ℤ] CharacterExponents)
    (ev : ∀ (R : TestAlgebra k) (t : Points (splitDiagonalGroup k).X R)
      (χ : Character (splitDiagonalGroup k)),
      characterValue χ R t = ((Additive.toMul (evaluate (diagonalGroupPoints k R t) (C (Additive.ofMul χ))) : Rˣ) : R)) :
    Set.BijOn (fun χ : Character (splitDiagonalGroup k) => C (Additive.ofMul χ))
      (absoluteRoots (diagonalSubgroup k)) rootCharacters := by
  refine ⟨absoluteRoots_mapsTo k detect C ev, fun _ _ _ _ h => C.injective h, ?_⟩
  intro r hr
  let χ := Additive.toMul (C.symm r)
  have hCr : C (Additive.ofMul χ) = r := C.apply_symm_apply r
  refine ⟨χ, ⟨?_, ?_⟩, hCr⟩
  · intro hχ
    obtain ⟨x, hx, hxr⟩ := hr
    have hz : r = 0 := by rw [← hCr, hχ]; exact C.map_zero
    have hx' : x = 0 := vectorPullback_injective (hxr.trans (hz.trans vectorPullback.map_zero.symm))
    have h := vectorRoot_square hx
    simp [hx'] at h
  · obtain ⟨i, j, hij, h⟩ := rootCharacters_signed_pair hr
    apply shear_gives_weight k i j hij
    intro R t
    rw [ev, hCr, h, map_add]
    exact congrArg₂ (· * ·) (vectorWeight_value (diagonalGroupPoints k R t) i)
      (vectorWeight_value (diagonalGroupPoints k R t) j)


end
end AbsoluteRoots

section Structure

open LinearAlgebraicGroups.Specs
open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj BigOperators

noncomputable section

open Specs.GeometricRadicals (IsReductive IsSemisimple)
open Specs.SimplyConnectedLattice (AdjointForm LatticeCriterion SplitCover)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (characterValue absoluteRoots pairing)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap diagonalClosedInclusion)
open Specs.SchemeCentre (rootLattice)
open private diagonal_root_kernel torus_equations from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SchemeCentre

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

variable (k : Type u) [Field k]

private theorem finite_root_quotient
    (C : Additive (Character (splitDiagonalGroup k)) ≃ₗ[ℤ] CharacterExponents)
    (h : Set.BijOn (fun χ : Character (splitDiagonalGroup k) => C (Additive.ofMul χ))
      (absoluteRoots (diagonalSubgroup k)) rootCharacters) :
    Finite (Character (splitDiagonalGroup k) ⧸ rootLattice (diagonalSubgroup k)) := by
  let T := diagonalSubgroup k
  let f : Character T.group →* Multiplicative (ZMod 2 × ZMod 2) :=
    (centralClass.comp C.toLinearMap).toAddMonoidHom.toMultiplicative
  have hroots : C.toLinearMap '' (Additive.toMul ⁻¹' absoluteRoots T) = rootCharacters := by
    ext a
    constructor
    · rintro ⟨χ, hχ, rfl⟩
      exact h.mapsTo (x := Additive.toMul χ) hχ
    · intro ha
      obtain ⟨χ, hχ, rfl⟩ := h.surjOn ha
      exact ⟨Additive.ofMul χ, hχ, rfl⟩
  have hspan : Submodule.map C.toLinearMap (Submodule.span ℤ (Additive.toMul ⁻¹' absoluteRoots T)) =
      centralClass.ker := by
    rw [Submodule.map_span, hroots, rootCharacters_span]
  have hk : rootLattice T = f.ker := by
    ext χ
    change χ ∈ Subgroup.closure (absoluteRoots T) ↔ centralClass (C (Additive.ofMul χ)) = 0
    rw [← LinearMap.mem_ker, ← hspan]
    constructor
    · intro hχ
      refine ⟨Additive.ofMul χ, ?_, rfl⟩
      change Additive.ofMul χ ∈ (Submodule.span ℤ _).toAddSubgroup
      rw [Submodule.span_int_eq_addSubgroupClosure, ← Subgroup.toAddSubgroup_closure]
      exact hχ
    · rintro ⟨ψ, hψ, hC⟩
      have he : ψ = Additive.ofMul χ := C.injective hC
      rw [he] at hψ
      change Additive.ofMul χ ∈ (Subgroup.closure (absoluteRoots T)).toAddSubgroup
      rwa [Subgroup.toAddSubgroup_closure, ← Submodule.span_int_eq_addSubgroupClosure]
  change Finite (Character T.group ⧸ rootLattice T)
  rw [hk]
  exact Finite.of_injective (QuotientGroup.quotientKerEquivRange f)
    (QuotientGroup.quotientKerEquivRange f).injective

private def constantDiagonal {R : Type u} [CommRing R]
    (x : rootsOfUnity 2 R × rootsOfUnity 2 R) : DiagonalPoints R :=
  ⟨(fun _ => x.1.val, x.2.val), by
    have hb : x.1.val ^ 2 = 1 := x.1.property
    have hu : x.2.val ^ 2 = 1 := x.2.property
    change x.2.val ^ 2 * (∏ _ : Fin 4, x.1.val) = 1
    rw [hu, one_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hb, one_pow]⟩

private theorem diagonalCentre_points {Z : GroupScheme k}
    (i : Z ⟶ (diagonalSubgroup k).group) [Mono i.hom.hom]
    (hker : ∀ (R : TestAlgebra k) (t : Points (diagonalSubgroup k).group.X R),
      (∃ z : Points Z.X R, z ≫ i.hom.hom = t) ↔
        ∃ b : Rˣ, b ^ 2 = 1 ∧ (scalar (diagonalGroupPoints k R t)) ^ 2 = 1 ∧
          ∀ j, scales (diagonalGroupPoints k R t) j = b) :
    ∃ e : ∀ R : TestAlgebra k, Points Z.X R ≃* rootsOfUnity 2 R × rootsOfUnity 2 R,
      (∀ (R : TestAlgebra k) (z : Points Z.X R),
        let p := diagonalGroupPoints k R (z ≫ i.hom.hom)
        (∀ j, scales p j = (e R z).1.val) ∧ scalar p = (e R z).2.val) ∧
      ∀ {R S : TestAlgebra k} (a : R ⟶ S) (z : Points Z.X R),
        (e S (mapPoints a z)).1.val = Units.map a.hom.toMonoidHom (e R z).1.val ∧
        (e S (mapPoints a z)).2.val = Units.map a.hom.toMonoidHom (e R z).2.val := by
  let q (R : TestAlgebra k) : Points Z.X R →* DiagonalPoints R :=
    (diagonalGroupPoints k R).toMonoidHom.comp (((groupPointsFunctor k).map i).app R).hom
  have hq (R : TestAlgebra k) (z : Points Z.X R) :
      (scales (q R z) 0) ^ 2 = 1 ∧ (scalar (q R z)) ^ 2 = 1 ∧
        ∀ j, scales (q R z) j = scales (q R z) 0 := by
    obtain ⟨b, hb, hu, hb'⟩ := (hker R (z ≫ i.hom.hom)).mp ⟨z, rfl⟩
    exact ⟨(congrArg (fun b : Rˣ => b ^ 2) (hb' 0)).trans hb, hu, fun j => (hb' j).trans (hb' 0).symm⟩
  let f (R : TestAlgebra k) : Points Z.X R →* rootsOfUnity 2 R × rootsOfUnity 2 R :=
    { toFun := fun z => (⟨scales (q R z) 0, (hq R z).1⟩, ⟨scalar (q R z), (hq R z).2.1⟩)
      map_one' := by
        apply Prod.ext <;> apply Subtype.ext
        · change scales (q R 1) 0 = 1
          rw [map_one]
          rfl
        · change scalar (q R 1) = 1
          rw [map_one]
          rfl
      map_mul' := fun x y => by
        simp only [map_mul]
        rfl }
  refine ⟨fun R => MulEquiv.ofBijective (f R) ⟨?_, ?_⟩, fun R z => ⟨(hq R z).2.2, rfl⟩, ?_⟩
  · intro x y hxy
    apply (cancel_mono i.hom.hom).mp
    apply (diagonalGroupPoints k R).injective
    change q R x = q R y
    apply Subtype.ext
    apply Prod.ext
    · funext j
      exact ((hq R x).2.2 j).trans
        ((congrArg (fun p : rootsOfUnity 2 R × rootsOfUnity 2 R => p.1.val) hxy).trans
          ((hq R y).2.2 j).symm)
    · exact congrArg (fun p : rootsOfUnity 2 R × rootsOfUnity 2 R => p.2.val) hxy
  · intro x
    let t := (diagonalGroupPoints k R).symm (constantDiagonal x)
    have ht : diagonalGroupPoints k R t = constantDiagonal x :=
      (diagonalGroupPoints k R).apply_symm_apply _
    obtain ⟨z, hz⟩ := (hker R t).mpr ⟨x.1.val, x.1.property, by rw [ht]; exact x.2.property,
      fun j => by rw [ht]; rfl⟩
    have hz' : q R z = constantDiagonal x :=
      (congrArg (diagonalGroupPoints k R) hz).trans ht
    refine ⟨z, Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
    · exact congrArg (fun y : DiagonalPoints R => scales y 0) hz'
    · exact congrArg (fun y : DiagonalPoints R => scalar y) hz'
  · intro R S a z
    have h : q S (mapPoints a z) = mapDiagonal a.hom.toRingHom (q R z) := by
      change diagonalGroupPoints k S (mapPoints a z ≫ i.hom.hom) =
        mapDiagonal a.hom.toRingHom (diagonalGroupPoints k R (z ≫ i.hom.hom))
      rw [show mapPoints a z ≫ i.hom.hom = mapPoints a (z ≫ i.hom.hom) from Category.assoc _ _ _]
      exact diagonalGroupPoints_natural k a (z ≫ i.hom.hom)
    exact ⟨congrArg (fun p : DiagonalPoints S => scales p 0) h,
      congrArg (fun p : DiagonalPoints S => scalar p) h⟩


private theorem diagonalCentre
    (hG : IsReductive (fieldSpinGroup k))
    (C : Additive (Character (splitDiagonalGroup k)) ≃ₗ[ℤ] CharacterExponents)
    (ev : ∀ (R : TestAlgebra k) (t : Points (splitDiagonalGroup k).X R)
      (χ : Character (splitDiagonalGroup k)),
      characterValue χ R t = ((Additive.toMul (evaluate (diagonalGroupPoints k R t) (C (Additive.ofMul χ))) : Rˣ) : R))
    (hroots : Set.BijOn (fun χ : Character (splitDiagonalGroup k) => C (Additive.ofMul χ))
      (absoluteRoots (diagonalSubgroup k)) rootCharacters) :
    CentreCoordinates (diagonalSubgroup k) (diagonalGroupPoints k) ∧ IsSemisimple (fieldSpinGroup k) := by
  let G := fieldSpinGroup k
  let T := diagonalSubgroup k
  obtain ⟨_, e, he, hcl, hrep, _⟩ := LinearAlgebraicGroups.RootData.SchemeCentre.schemeCentre
    G hG T (splitDiagonalGroup_split k) (diagonalSubgroup_geometricallyMaximal k)
  let Z : ClosedSubgroup G.val :=
    ⟨_, diagonalClosedInclusion k (rootLattice T) ≫ e.hom ≫ T.inclusion, hcl⟩
  let i : Z.group ⟶ T.group := diagonalClosedInclusion k (rootLattice T) ≫ e.hom
  have hi : i ≫ T.inclusion = Z.inclusion := by simp only [i, Z, Category.assoc]
  have hZ : RepresentsSubgroup Z (fun _ z => Centralizes (𝟙 G.val) z) := hrep
  have hmon : Mono i.hom.hom := by
    have := T.isClosedImmersion
    have hcl : IsClosedImmersion (i.hom.hom.left ≫ T.inclusion.hom.hom.left) := by
      rw [show i.hom.hom.left ≫ T.inclusion.hom.hom.left = Z.inclusion.hom.hom.left from
        congrArg (fun f : Z.group ⟶ G.val => f.hom.hom.left) hi]
      exact Z.isClosedImmersion
    have : IsClosedImmersion i.hom.hom.left :=
      IsClosedImmersion.of_comp_isClosedImmersion i.hom.hom.left T.inclusion.hom.hom.left
    exact Over.mono_of_mono_left i.hom.hom
  have hker (R : TestAlgebra k) (t : Points T.group.X R) :
      (∃ z : Points Z.group.X R, z ≫ i.hom.hom = t) ↔
        ∃ b : Rˣ, b ^ 2 = 1 ∧ (scalar (diagonalGroupPoints k R t)) ^ 2 = 1 ∧
          ∀ j, scales (diagonalGroupPoints k R t) j = b := by
    have hr := (diagonal_root_kernel (T := T) e he R t).symm
    change (∃ z : Points Z.group.X R, z ≫ i.hom.hom = t) ↔ _ at hr
    rw [hr, ← diagonalCentralCharacters_proof R (diagonalGroupPoints k R t)]
    constructor
    · intro ht r hr
      obtain ⟨χ, hχ, hC⟩ := hroots.surjOn hr
      rw [← hC]
      apply Units.ext
      rw [← ev R t χ]
      exact (torus_equations e he R t χ).mp (ht χ hχ)
    · intro ht χ hχ
      apply (torus_equations e he R t χ).mpr
      rw [ev]
      exact congrArg Units.val (ht _ (hroots.mapsTo hχ))
  obtain ⟨coords, hc, _⟩ := diagonalCentre_points k i hker
  refine ⟨⟨Z, i, hZ, hi, coords, hc⟩, ?_⟩
  have : Finite (Character T.group ⧸ rootLattice T) := finite_root_quotient k C hroots
  have hfinite : IsFinite Z.group.X.hom := by
    change IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap k (MonoidAlgebra k (Character T.group ⧸ rootLattice T)))))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  exact (LinearAlgebraicGroups.Reductive.CentralDerived.semisimpleIffFiniteCentre G hG Z hZ).mpr hfinite

theorem fieldStructure_conditional (_adjoint : AdjointForm.{u})
    (lattice : LatticeCriterion.{u}) (_cover : SplitCover.{u}) :
    FieldStructure.{u} := by
  intro k _
  let G := fieldSpinGroup k
  let T := diagonalSubgroup k
  have hG : IsReductive G := fieldSpin_reductive k
  have hsplit : Specs.GeometricRadicals.IsSplitTorus T.group := splitDiagonalGroup_split k
  have hmax := diagonalSubgroup_geometricallyMaximal k
  obtain ⟨C, ev⟩ := diagonalCharacterCoordinates k
  have hroots := absoluteRoots_coordinates k
    LinearAlgebraicGroups.RootData.CharacterPairing.characterValuesDetectCharacters C ev
  obtain ⟨hcentre, hss⟩ := diagonalCentre k hG C ev hroots
  obtain ⟨hcomm, _, _, _, _, P, hP, pe⟩ :=
    LinearAlgebraicGroups.RootData.CharacterPairing.perfectCharacterPairing T.group hsplit
  let _ := hcomm
  let _ := hP
  let Y := cocharacterCoordinates C P
  have hpair (χ : Character T.group) (ψ : Cocharacter T.group) :
      pairing T.group χ ψ = latticePairing (C (Additive.ofMul χ)) (Y (Additive.ofMul ψ)) :=
    (pe χ ψ).symm.trans (cocharacterCoordinates_pairing C P _ _).symm
  obtain ⟨_, ⟨D⟩⟩ := LinearAlgebraicGroups.RootData.AbstractPairing.abstractPairing G hG T hsplit hmax
  have hcor := attachedCoroot_coordinates (T := T) C Y D hpair hroots
  have hsc := (lattice G hss T hsplit hmax D).mpr (attachedCoroots_span (T := T) C Y D hroots hcor)
  exact ⟨G, fieldSpinRepresentation k, fieldSpinPresentation k, hG, hss, hsc,
    T, diagonalGroupPoints k, diagonalSubgroup_presentation k, hsplit, hmax, hcentre,
    hcomm, C, Y, D, ev, hpair, hroots, hcor⟩

end
end Structure

section Conditional

open Specs.SimplyConnectedLattice (AdjointForm LatticeCriterion SplitCover)

theorem halfSumRelation_conditional (_adjoint : AdjointForm.{u})
    (_lattice : LatticeCriterion.{u}) (_cover : SplitCover.{u}) :
    HalfSumRelation :=
  halfSumRelation_proof

theorem characterGenerators_conditional (_adjoint : AdjointForm.{u})
    (_lattice : LatticeCriterion.{u}) (_cover : SplitCover.{u}) :
    CharacterGenerators :=
  characterGenerators_proof

theorem corootSpan_conditional (_adjoint : AdjointForm.{u})
    (_lattice : LatticeCriterion.{u}) (_cover : SplitCover.{u}) :
    CorootSpan :=
  corootSpan_proof

theorem centralClasses_conditional (_adjoint : AdjointForm.{u})
    (_lattice : LatticeCriterion.{u}) (_cover : SplitCover.{u}) :
    CentralClasses :=
  centralClasses_proof

theorem diagonalParameters_conditional (_adjoint : AdjointForm.{u})
    (_lattice : LatticeCriterion.{u}) (_cover : SplitCover.{u}) :
    DiagonalParameters.{u} :=
  diagonalParameters_proof

theorem weightEvaluation_conditional (_adjoint : AdjointForm.{u})
    (_lattice : LatticeCriterion.{u}) (_cover : SplitCover.{u}) :
    WeightEvaluation.{u} :=
  weightEvaluation_proof

theorem diagonalCentralCharacters_conditional (_adjoint : AdjointForm.{u})
    (_lattice : LatticeCriterion.{u}) (_cover : SplitCover.{u}) :
    DiagonalCentralCharacters.{u} :=
  diagonalCentralCharacters_proof

theorem diagonalCliffordAction_conditional (_adjoint : AdjointForm.{u})
    (_lattice : LatticeCriterion.{u}) (_cover : SplitCover.{u}) :
    DiagonalCliffordAction.{u} :=
  diagonalCliffordAction_proof

theorem vectorIrreducibility_conditional (_adjoint : AdjointForm.{u})
    (_lattice : LatticeCriterion.{u}) (_cover : SplitCover.{u}) :
    VectorIrreducibility.{u} :=
  vectorIrreducibility_proof

theorem halfSpinIrreducibility_conditional (_adjoint : AdjointForm.{u})
    (_lattice : LatticeCriterion.{u}) (_cover : SplitCover.{u}) :
    HalfSpinIrreducibility.{u} :=
  halfSpinIrreducibility_proof

end Conditional

end LinearAlgebraicGroups.Albert.SpinWeights

universe v8_closure_7bf89f8f6695d210_u0
theorem _root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«centralClasses» : _root_.«LinearAlgebraicGroups».«Specs».«SpinWeights».«CentralClasses» :=
  @_root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«centralClasses_conditional».{0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{0})
theorem _root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«characterGenerators» : _root_.«LinearAlgebraicGroups».«Specs».«SpinWeights».«CharacterGenerators» :=
  @_root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«characterGenerators_conditional».{0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{0})
theorem _root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«corootSpan» : _root_.«LinearAlgebraicGroups».«Specs».«SpinWeights».«CorootSpan» :=
  @_root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«corootSpan_conditional».{0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{0})
theorem _root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«diagonalCentralCharacters» : _root_.«LinearAlgebraicGroups».«Specs».«SpinWeights».«DiagonalCentralCharacters».{v8_closure_7bf89f8f6695d210_u0} :=
  @_root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«diagonalCentralCharacters_conditional».{v8_closure_7bf89f8f6695d210_u0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{v8_closure_7bf89f8f6695d210_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{v8_closure_7bf89f8f6695d210_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{v8_closure_7bf89f8f6695d210_u0})
theorem _root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«diagonalCliffordAction» : _root_.«LinearAlgebraicGroups».«Specs».«SpinWeights».«DiagonalCliffordAction».{v8_closure_7bf89f8f6695d210_u0} :=
  @_root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«diagonalCliffordAction_conditional».{v8_closure_7bf89f8f6695d210_u0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{v8_closure_7bf89f8f6695d210_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{v8_closure_7bf89f8f6695d210_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{v8_closure_7bf89f8f6695d210_u0})
theorem _root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«diagonalParameters» : _root_.«LinearAlgebraicGroups».«Specs».«SpinWeights».«DiagonalParameters».{v8_closure_7bf89f8f6695d210_u0} :=
  @_root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«diagonalParameters_conditional».{v8_closure_7bf89f8f6695d210_u0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{v8_closure_7bf89f8f6695d210_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{v8_closure_7bf89f8f6695d210_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{v8_closure_7bf89f8f6695d210_u0})
theorem _root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«fieldStructure» : _root_.«LinearAlgebraicGroups».«Specs».«SpinWeights».«FieldStructure».{v8_closure_7bf89f8f6695d210_u0} :=
  @_root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«fieldStructure_conditional».{v8_closure_7bf89f8f6695d210_u0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{v8_closure_7bf89f8f6695d210_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{v8_closure_7bf89f8f6695d210_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{v8_closure_7bf89f8f6695d210_u0})
theorem _root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«halfSpinIrreducibility» : _root_.«LinearAlgebraicGroups».«Specs».«SpinWeights».«HalfSpinIrreducibility».{v8_closure_7bf89f8f6695d210_u0} :=
  @_root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«halfSpinIrreducibility_conditional».{v8_closure_7bf89f8f6695d210_u0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{v8_closure_7bf89f8f6695d210_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{v8_closure_7bf89f8f6695d210_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{v8_closure_7bf89f8f6695d210_u0})
theorem _root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«halfSumRelation» : _root_.«LinearAlgebraicGroups».«Specs».«SpinWeights».«HalfSumRelation» :=
  @_root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«halfSumRelation_conditional».{0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{0})
theorem _root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«vectorIrreducibility» : _root_.«LinearAlgebraicGroups».«Specs».«SpinWeights».«VectorIrreducibility».{v8_closure_7bf89f8f6695d210_u0} :=
  @_root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«vectorIrreducibility_conditional».{v8_closure_7bf89f8f6695d210_u0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{v8_closure_7bf89f8f6695d210_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{v8_closure_7bf89f8f6695d210_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{v8_closure_7bf89f8f6695d210_u0})
theorem _root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«weightEvaluation» : _root_.«LinearAlgebraicGroups».«Specs».«SpinWeights».«WeightEvaluation».{v8_closure_7bf89f8f6695d210_u0} :=
  @_root_.«LinearAlgebraicGroups».«Albert».«SpinWeights».«weightEvaluation_conditional».{v8_closure_7bf89f8f6695d210_u0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{v8_closure_7bf89f8f6695d210_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{v8_closure_7bf89f8f6695d210_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{v8_closure_7bf89f8f6695d210_u0})
