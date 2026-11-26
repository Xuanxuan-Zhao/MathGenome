import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.AutomorphismType
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitAlbertAdjointWeights
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.AlbertAutomorphismDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntegralSmoothness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbstractPairing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRecognition
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRelativeCell
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntegralAlbertRootPins
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option Elab.async false

namespace LinearAlgebraicGroups.Albert.AutomorphismType

open AutomorphismTypeSpecification
open LinearAlgebraicGroups.Specs
open SpinWeights (CharacterExponents VectorExponents coordinate epsilon halfSum
  exteriorWeight vectorPullback)

private theorem longRootCharacters :
    Set.range (fun r : LongIndex => rootCharacter (.inl r)) = SpinWeights.rootCharacters := by
  classical
  have h (i j : Fin 4) (a b : Bool) :
      vectorPullback (rootSign a • coordinate i + rootSign b • coordinate j) =
        rootSign a • epsilon i + rootSign b • epsilon j := by
    simp only [map_add, map_smul, SpinWeights.epsilon]
  have forward (i j : Fin 4) (hne : i ≠ j) (a b : Bool) :
      rootSign a • coordinate i + rootSign b • coordinate j ∈ SpinWeights.vectorRoots := by
    cases a <;> cases b
    · exact ⟨i, j, hne, Or.inl (by simp [rootSign])⟩
    · exact ⟨i, j, hne, Or.inr (Or.inl (by simp [rootSign, sub_eq_add_neg]))⟩
    · exact ⟨j, i, hne.symm, Or.inr (Or.inl (by simp [rootSign, sub_eq_add_neg, add_comm]))⟩
    · exact ⟨i, j, hne, Or.inr (Or.inr (by simp [rootSign, sub_eq_add_neg]))⟩
  have reverse (i j : Fin 4) (hne : i ≠ j) (a b : Bool) :
      vectorPullback (rootSign a • coordinate i + rootSign b • coordinate j) ∈
        Set.range (fun r : LongIndex => rootCharacter (.inl r)) := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨(⟨(i, j), hlt⟩, a, b), (h i j a b).symm⟩
    · refine ⟨(⟨(j, i), hgt⟩, b, a), ?_⟩
      rw [h]
      exact add_comm _ _
  ext x
  constructor
  · rintro ⟨⟨⟨⟨i, j⟩, hij⟩, a, b⟩, rfl⟩
    exact ⟨_, forward i j (ne_of_lt hij) a b, h i j a b⟩
  · rintro ⟨y, ⟨i, j, hij, rfl | rfl | rfl⟩, rfl⟩
    · simpa [rootSign] using reverse i j hij false false
    · simpa [rootSign, sub_eq_add_neg] using reverse i j hij false true
    · simpa [rootSign, sub_eq_add_neg] using reverse i j hij true true

private theorem rootSpan : Submodule.span ℤ (Set.range rootCharacter) = ⊤ := by
  have h : Submodule.span ℤ (insert halfSum (Set.range epsilon)) ≤
      Submodule.span ℤ (Set.range rootCharacter) := by
    refine Submodule.span_le.mpr ?_
    rintro _ (rfl | ⟨i, rfl⟩)
    · apply (Submodule.span ℤ (Set.range rootCharacter)).neg_mem_iff.mp
      exact Submodule.subset_span ⟨.inr (.inr ∅), by simp [rootCharacter, exteriorWeight]⟩
    · exact Submodule.subset_span ⟨.inr (.inl (i, false)), by simp [rootCharacter, rootSign]⟩
  apply eq_top_iff.mpr
  intro x _
  apply h
  let M := Submodule.span ℤ (insert halfSum (Set.range epsilon))
  have hx : x = (-x.1) • halfSum + ∑ i : Fin 3, x.2 i • epsilon i.succ := by
    rcases x with ⟨a, b⟩
    apply Prod.ext
    · simp [halfSum, SpinWeights.epsilon, SpinWeights.vectorPullback, coordinate,
        Pi.single_apply, Fin.sum_univ_three]
    · change b = (AddMonoidHom.snd ℤ (Fin 3 → ℤ))
        ((-a) • halfSum + ∑ i : Fin 3, b i • epsilon i.succ)
      rw [map_add, map_sum]
      funext j
      simp [halfSum, SpinWeights.epsilon, SpinWeights.vectorPullback, coordinate,
        Pi.single_apply, Fin.succ_inj]
  rw [hx]
  exact M.add_mem (M.smul_mem _ (Submodule.subset_span (Set.mem_insert _ _)))
    (Submodule.sum_mem M fun i _ =>
      M.smul_mem _ (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self _))))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem rootLatticeCalculation : RootLatticeCalculation := by
  refine ⟨by decide, by decide, by decide, ?_, by decide, longRootCharacters, rootSpan⟩
  intro a b h
  have test : ∀ i j : RootIndex,
      decide (rootCharacter i = rootCharacter j) = false ∨ decide (i = j) = true := by decide +kernel
  exact of_decide_eq_true ((test a b).resolve_left (by simp [h]))

private theorem coordinatePairing_doubled (x : CharacterExponents) (r : RootIndex) :
    2 * coordinatePairing x (corootCoordinates r) =
      ∑ j, doubledCoordinates x j * vectorCoroot r j := by
  have parity : ∀ s : RootIndex, (∑ i, vectorCoroot s i) % 2 = 0 := by decide
  have h := Int.emod_add_mul_ediv (-(∑ i, vectorCoroot r i)) 2
  rw [Int.neg_emod_two, parity, zero_add] at h
  simp only [coordinatePairing, corootCoordinates, doubledCoordinates, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ] at *
  linear_combination x.1 * h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem corootCalculation : CorootCalculation := by
  refine ⟨?_, by decide, by decide, coordinatePairing_doubled⟩
  intro a b h
  have test : ∀ i j : RootIndex,
      decide (corootCoordinates i = corootCoordinates j) = false ∨ decide (i = j) = true := by decide +kernel
  exact of_decide_eq_true ((test a b).resolve_left (by simp [h]))


private noncomputable def characterBasis : Module.Basis (Unit ⊕ Fin 3) ℤ CharacterExponents :=
  (Module.Basis.singleton Unit ℤ).prod (Pi.basisFun ℤ (Fin 3))

private noncomputable def integralPairing :
    CharacterExponents →ₗ[ℤ] CharacterExponents →ₗ[ℤ] ℤ :=
  (Module.Dual.eval ℤ CharacterExponents).compl₁₂ (LinearEquiv.refl ℤ CharacterExponents).toLinearMap
    characterBasis.toDualEquiv.toLinearMap

private instance : integralPairing.IsPerfPair :=
  inferInstanceAs
    ((Module.Dual.eval ℤ CharacterExponents).compl₁₂ (LinearEquiv.refl ℤ CharacterExponents).toLinearMap
      characterBasis.toDualEquiv.toLinearMap).IsPerfPair

private theorem integralPairing_apply (x y : CharacterExponents) :
    integralPairing x y = coordinatePairing x y := by
  change characterBasis.toDualEquiv y x = _
  suffices characterBasis.toDualEquiv y x = y.1 * x.1 + ∑ i, y.2 i * x.2 i by
    simpa only [coordinatePairing, mul_comm] using this
  rw [Module.Basis.toDualEquiv_apply]
  calc
    characterBasis.toDual y x =
        characterBasis.toDual (∑ j, characterBasis.repr y j • characterBasis j) x := by
      rw [characterBasis.sum_repr]
    _ = ∑ j, characterBasis.repr y j * characterBasis.repr x j := by
      rw [map_sum]
      simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
        Module.Basis.toDual_apply_right]
    _ = _ := by
      simp [characterBasis, Fintype.sum_sum_type,
        Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr]

private def reflectedRoot (a b : RootIndex) : CharacterExponents :=
  rootCharacter b - coordinatePairing (rootCharacter b) (corootCoordinates a) • rootCharacter a

private def reflectedCoroot (a b : RootIndex) : CharacterExponents :=
  corootCoordinates b - coordinatePairing (rootCharacter a) (corootCoordinates b) • corootCoordinates a

/-- Read a root index from its doubled coordinates. The two integral
families have one or two nonzero coordinates. The half-integral family
is determined by the positions of its positive coordinates. -/
private def indexOfCoordinates (v : VectorExponents) : RootIndex :=
  match (List.finRange 4).filter (fun i => v i != 0) with
  | [i] => .inr (.inl (i, decide (v i < 0)))
  | [i, j] => if h : i < j then .inl (⟨(i, j), h⟩, decide (v i < 0), decide (v j < 0))
      else .inr (.inl (0, false))
  | _ => .inr (.inr (Finset.univ.filter fun i => 0 < v i))

private def reflectedIndex (a b : RootIndex) : RootIndex :=
  indexOfCoordinates (doubledCoordinates (reflectedRoot a b))

private abbrev ReflectionPreservesPair (a b : RootIndex) : Prop :=
  decide (reflectedRoot a b = rootCharacter (reflectedIndex a b)) = true ∧
    decide (reflectedCoroot a b = corootCoordinates (reflectedIndex a b)) = true

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem reflection_recognizes : ∀ a b : RootIndex, ReflectionPreservesPair a b := by
  decide +kernel

private noncomputable def pairingRootDatum : RootDatum RootIndex CharacterExponents CharacterExponents :=
  RootPairing.mk' integralPairing ⟨rootCharacter, rootLatticeCalculation.2.2.2.1⟩
    ⟨corootCoordinates, corootCalculation.1⟩
    (fun a => (integralPairing_apply _ _).trans (corootCalculation.2.1 a))
    (by
      rintro a _ ⟨b, rfl⟩
      let c := reflectedIndex a b
      have hc := (reflection_recognizes a b).1
      refine ⟨c, ?_⟩
      change rootCharacter c = rootCharacter b - integralPairing _ _ • rootCharacter a
      rw [integralPairing_apply]
      exact (of_decide_eq_true hc).symm)
    (by
      rintro a _ ⟨b, rfl⟩
      let c := reflectedIndex a b
      have hc := (reflection_recognizes a b).2
      refine ⟨c, ?_⟩
      change corootCoordinates c = corootCoordinates b -
        integralPairing _ _ • corootCoordinates a
      rw [integralPairing_apply]
      exact (of_decide_eq_true hc).symm)


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
private theorem pairingReduced : pairingRootDatum.IsReduced := by
  constructor
  intro i j h
  have calcFour : ∀ a b : RootIndex,
      coordinatePairing (rootCharacter a) (corootCoordinates b) *
        coordinatePairing (rootCharacter b) (corootCoordinates a) ≠ 4 ∨
      (decide (rootCharacter a = rootCharacter b) = true ∨
        decide (rootCharacter a = -rootCharacter b) = true) := by decide +kernel
  have h₄ := (pairingRootDatum.coxeterWeight_eq_four_iff_not_linearIndependent).2 h
  change integralPairing (rootCharacter i) (corootCoordinates j) *
    integralPairing (rootCharacter j) (corootCoordinates i) = 4 at h₄
  rw [integralPairing_apply, integralPairing_apply] at h₄
  exact ((calcFour i j).resolve_left (not_not_intro h₄)).imp of_decide_eq_true of_decide_eq_true

private theorem simpleRootValues (i : Fin 4) :
    rootCharacter (simpleIndex i) =
      ![(0, ![1, -1, 0]), (0, ![0, 1, -1]), (0, ![0, 0, 1]), (-1, ![-1, -1, -1])] i := by
  revert i
  decide

private theorem simpleCorootValues (i : Fin 4) :
    corootCoordinates (simpleIndex i) =
      ![(0, ![1, -1, 0]), (0, ![0, 1, -1]), (-1, ![0, 0, 2]), (1, ![-1, -1, -1])] i := by
  revert i
  decide

private theorem sumSimpleRoots (c : Fin 4 → ℤ) :
    ∑ i, c i • rootCharacter (simpleIndex i) =
      (-c 3, ![c 0 - c 3, -c 0 + c 1 - c 3, -c 1 + c 2 - c 3]) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, simpleRootValues]
  apply Prod.ext
  · change c 0 * 0 + (c 1 * 0 + (c 2 * 0 + c 3 * (-1))) = -c 3
    ring
  · funext i
    fin_cases i <;> simp [Prod.smul_mk] <;> ring

private theorem sumSimpleCoroots (c : Fin 4 → ℤ) :
    ∑ i, c i • corootCoordinates (simpleIndex i) =
      (-c 2 + c 3, ![c 0 - c 3, -c 0 + c 1 - c 3, -c 1 + 2 * c 2 - c 3]) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, simpleCorootValues]
  apply Prod.ext
  · change c 0 * 0 + (c 1 * 0 + (c 2 * (-1) + c 3 * 1)) = -c 2 + c 3
    ring
  · funext i
    fin_cases i <;> simp [Prod.smul_mk] <;> ring

private theorem simpleRootIndependent :
    LinearIndependent ℤ (rootCharacter ∘ simpleIndex) := by
  rw [Fintype.linearIndependent_iff]
  intro c h i
  change ∑ j, c j • rootCharacter (simpleIndex j) = 0 at h
  rw [sumSimpleRoots] at h
  have h₀ : -c 3 = 0 := congrArg Prod.fst h
  have h₁ : c 0 - c 3 = 0 := congrArg (fun x : CharacterExponents => x.2 0) h
  have h₂ : -c 0 + c 1 - c 3 = 0 := congrArg (fun x : CharacterExponents => x.2 1) h
  have h₃ : -c 1 + c 2 - c 3 = 0 := congrArg (fun x : CharacterExponents => x.2 2) h
  fin_cases i <;>
    (first | change c 0 = 0 | change c 1 = 0 | change c 2 = 0 | change c 3 = 0) <;> omega

private theorem simpleRootsSpan (x : CharacterExponents) :
    x ∈ Submodule.span ℤ (Set.range (rootCharacter ∘ simpleIndex)) := by
  let c : Fin 4 → ℤ :=
    ![x.2 0 - x.1, x.2 0 + x.2 1 - 2 * x.1, x.2 0 + x.2 1 + x.2 2 - 3 * x.1, -x.1]
  have h : ∑ i, c i • rootCharacter (simpleIndex i) = x := by
    rw [sumSimpleRoots]
    apply Prod.ext
    · change -(-x.1) = x.1
      simp
    · funext i
      fin_cases i <;> simp [c] <;> ring
  rw [← h]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

private theorem simpleCorootsSpan (x : CharacterExponents) :
    x ∈ Submodule.span ℤ (Set.range (corootCoordinates ∘ simpleIndex)) := by
  let d := -x.2 0 - x.2 1 - x.2 2 - 2 * x.1
  let c : Fin 4 → ℤ := ![x.2 0 + d, x.2 0 + x.2 1 + 2 * d, d - x.1, d]
  have h : ∑ i, c i • corootCoordinates (simpleIndex i) = x := by
    rw [sumSimpleCoroots]
    apply Prod.ext
    · change -(d - x.1) + d = x.1
      ring
    · funext i
      fin_cases i <;> simp [c, d] <;> ring
  rw [← h]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

private def simpleSupport : Finset RootIndex := Finset.univ.image simpleIndex

private theorem simpleSupport_coe : (simpleSupport : Set RootIndex) = Set.range simpleIndex := by
  simp [simpleSupport]

private noncomputable def pairingBase : pairingRootDatum.Base :=
  RootPairing.Base.mkOfPairwiseLEZero pairingRootDatum (s := simpleSupport)
    (by
      rw [simpleSupport_coe, linearIndepOn_range_iff (show Function.Injective simpleIndex from by
        change ∀ i j : Fin 4, simpleIndex i = simpleIndex j → i = j
        decide)]
      exact simpleRootIndependent)
    (by
      rw [simpleSupport_coe]
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h
      have hn : i ≠ j := fun e => h (congrArg simpleIndex e)
      have hpair := pairingRootDatum.algebraMap_pairingIn ℤ (simpleIndex i) (simpleIndex j)
      change pairingRootDatum.pairingIn ℤ (simpleIndex i) (simpleIndex j) =
        pairingRootDatum.pairing (simpleIndex i) (simpleIndex j) at hpair
      rw [hpair]
      change integralPairing (rootCharacter (simpleIndex i)) (corootCoordinates (simpleIndex j)) ≤ 0
      rw [integralPairing_apply, corootCalculation.2.2.1]
      have hcartan : ∀ a b : Fin 4, a ≠ b → cartanMatrix a b ≤ 0 := by decide
      exact hcartan i j hn)
    (fun i => by
      rw [simpleSupport_coe, ← Set.range_comp]
      exact simpleCorootsSpan (corootCoordinates i))
    (fun i => by
      rw [simpleSupport_coe, ← Set.range_comp]
      exact simpleRootsSpan (rootCharacter i))

private noncomputable abbrev f4Datum : Pinning.BasedRootDatum.{0} where
  I := RootIndex
  X := CharacterExponents
  Y := CharacterExponents
  finiteRoots := inferInstance
  freeX := inferInstance
  freeY := inferInstance
  finiteX := inferInstance
  finiteY := inferInstance
  datum := pairingRootDatum
  reduced := pairingReduced
  base := pairingBase

theorem integralDatumExists : IntegralDatumExists :=
  ⟨f4Datum, ⟨{
    characters := LinearEquiv.refl ℤ _
    cocharacters := LinearEquiv.refl ℤ _
    roots := Equiv.refl _
    root_eq := fun _ => rfl
    coroot_eq := fun _ => rfl
    pair_eq := integralPairing_apply
    simple_eq := fun i => by
      change i ∈ (simpleSupport : Set RootIndex) ↔ i ∈ Set.range simpleIndex
      rw [simpleSupport_coe]
  }⟩⟩

theorem reflectionRecovery : ReflectionRecovery := by
  intro r f h₂ hReflection x
  have h := Module.Dual.eq_of_preReflection_mapsTo
    (Set.finite_range rootCharacter) rootSpan h₂ hReflection
    (pairingRootDatum.coroot_root_two r) (pairingRootDatum.mapsTo_reflection_root r)
  have hx : f x = integralPairing x (corootCoordinates r) :=
    DFunLike.congr_fun h x
  rw [hx, integralPairing_apply]

/-- The roots of a torus marked by these coordinates generate its whole
character group. This applies to the group-algebra quotient defining the centre. -/
theorem rootLattice_eq_top {k : Type} [Field k] {G : GroupScheme k} (T : ClosedSubgroup G)
    (C : Additive (CharacterDescent.Character T.group) ≃ₗ[ℤ] CharacterExponents)
    (hC : Set.SurjOn (fun χ : CharacterDescent.Character T.group => C (Additive.ofMul χ))
      (CharacterPairing.absoluteRoots T) (Set.range rootCharacter)) :
    SchemeCentre.rootLattice T = ⊤ := by
  let L : Submodule ℤ (Additive (CharacterDescent.Character T.group)) :=
    (SchemeCentre.rootLattice T).toAddSubgroup.toIntSubmodule
  have span_le : Submodule.span ℤ (Set.range rootCharacter) ≤ L.map C.toLinearMap := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨χ, hχ, rfl⟩ := hC hx
    refine ⟨Additive.ofMul χ, ?_, rfl⟩
    change χ ∈ SchemeCentre.rootLattice T
    exact Subgroup.subset_closure hχ
  rw [rootSpan] at span_le
  apply eq_top_iff.mpr
  intro χ _
  obtain ⟨ψ, hψ, he⟩ := span_le (show C (Additive.ofMul χ) ∈ ⊤ from trivial)
  change Additive.ofMul χ ∈ L
  rw [← C.injective he]
  exact hψ

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj
open IntegralSmoothnessSpecification (SplitGroup algebraicFiber geometricFiber)
open ShortDirectionSpecification (IntegralPresentation)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (absoluteRoots pairing)
open Specs.GeometricRadicals (IsReductive)

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

private theorem adjointRootSet :
    SplitAlbertAdjointWeightsSpecification.roots = Set.range rootCharacter := by
  have hvec : Set.range SplitFrameTorusSpecification.vectorWeight =
      Set.range (fun r : VectorIndex => rootCharacter (.inr (.inl r))) := by
    ext x
    constructor
    · rintro ⟨i | i, rfl⟩
      · exact ⟨(i, false), by simp [rootCharacter, rootSign, SplitFrameTorusSpecification.vectorWeight]⟩
      · exact ⟨(i, true), by simp [rootCharacter, rootSign, SplitFrameTorusSpecification.vectorWeight]⟩
    · rintro ⟨⟨i, p⟩, rfl⟩
      cases p
      · exact ⟨.inl i, by simp [rootCharacter, rootSign, SplitFrameTorusSpecification.vectorWeight]⟩
      · exact ⟨.inr i, by simp [rootCharacter, rootSign, SplitFrameTorusSpecification.vectorWeight]⟩
  rw [SplitAlbertAdjointWeightsSpecification.roots, SplitAlbertAdjointWeightsSpecification.shortRoots,
    ← longRootCharacters, hvec]
  ext x
  constructor
  · rintro (⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩)
    · exact ⟨.inl r, rfl⟩
    · exact ⟨.inr (.inl r), rfl⟩
    · exact ⟨.inr (.inr r), rfl⟩
  · rintro ⟨r | r | r, rfl⟩
    · exact Or.inl ⟨r, rfl⟩
    · exact Or.inr (Or.inl ⟨r, rfl⟩)
    · exact Or.inr (Or.inr ⟨r, rfl⟩)

private def cocharCoordinates {k : Type} [Field k] {G : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X] (E : AbstractPairing.Datum T)
    (C : Additive (Character T.group) ≃ₗ[ℤ] CharacterExponents) :
    Additive (Cocharacter T.group) ≃ₗ[ℤ] CharacterExponents :=
  (E.rootDatum.toLinearMap.flip.toPerfPair.trans C.symm.dualMap).trans
    pairingRootDatum.toLinearMap.flip.toPerfPair.symm

private theorem cocharCoordinates_pair {k : Type} [Field k] {G : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X] (E : AbstractPairing.Datum T)
    (C : Additive (Character T.group) ≃ₗ[ℤ] CharacterExponents)
    (x : Additive (Character T.group)) (y : Additive (Cocharacter T.group)) :
    E.rootDatum.toLinearMap x y = coordinatePairing (C x) (cocharCoordinates E C y) := by
  rw [← integralPairing_apply]
  change E.rootDatum.toLinearMap x y =
    pairingRootDatum.toLinearMap.flip.toPerfPair (cocharCoordinates E C y) (C x)
  unfold cocharCoordinates
  rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.trans_apply]
  change E.rootDatum.toLinearMap x y = E.rootDatum.toLinearMap (C.symm (C x)) y
  rw [LinearEquiv.symm_apply_apply]

private def rootIndexEquiv {k : Type} [Field k] {G : GroupScheme k} {T : ClosedSubgroup G}
    (C : Additive (Character T.group) ≃ₗ[ℤ] CharacterExponents)
    (hC : Set.BijOn (fun χ : Character T.group => C (Additive.ofMul χ))
      (absoluteRoots T) (Set.range rootCharacter)) : ↥(absoluteRoots T) ≃ RootIndex :=
  (Equiv.ofBijective (hC.mapsTo.restrict (fun χ : Character T.group => C (Additive.ofMul χ))
    (absoluteRoots T) (Set.range rootCharacter)) hC.bijective).trans
      (Equiv.ofInjective rootCharacter rootLatticeCalculation.2.2.2.1).symm

private theorem rootIndexEquiv_char {k : Type} [Field k] {G : GroupScheme k} {T : ClosedSubgroup G}
    (C : Additive (Character T.group) ≃ₗ[ℤ] CharacterExponents)
    (hC : Set.BijOn (fun χ : Character T.group => C (Additive.ofMul χ))
      (absoluteRoots T) (Set.range rootCharacter)) (α : ↥(absoluteRoots T)) :
    rootCharacter (rootIndexEquiv C hC α) = C (Additive.ofMul α.val) := by
  exact congrArg Subtype.val ((Equiv.ofInjective rootCharacter
    rootLatticeCalculation.2.2.2.1).apply_symm_apply _)

private theorem cocharCoordinates_coroot {k : Type} [Field k] {G : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X] (E : AbstractPairing.Datum T)
    (C : Additive (Character T.group) ≃ₗ[ℤ] CharacterExponents)
    (hC : Set.BijOn (fun χ : Character T.group => C (Additive.ofMul χ))
      (absoluteRoots T) (Set.range rootCharacter)) (α : AbstractPairing.Root T) :
    cocharCoordinates E C (E.rootDatum.coroot α) = corootCoordinates (rootIndexEquiv C hC α) := by
  let f := (E.rootDatum.coroot' α).comp C.symm.toLinearMap
  let i := rootIndexEquiv C hC α
  have hr (β : AbstractPairing.Root T) :
      C (E.rootDatum.root β) = rootCharacter (rootIndexEquiv C hC β) := by
    rw [E.root_eq, rootIndexEquiv_char]
  have h₂ : f (rootCharacter i) = 2 := by
    rw [← hr α]
    change E.rootDatum.coroot' α (C.symm (C (E.rootDatum.root α))) = 2
    rw [C.symm_apply_apply, E.rootDatum.coroot_root_two]
  have hm : Set.MapsTo (Module.preReflection (rootCharacter i) f)
      (Set.range rootCharacter) (Set.range rootCharacter) := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨β, rfl⟩ := (rootIndexEquiv C hC).surjective j
    rw [← hr β, ← hr α]
    have he : Module.preReflection (C (E.rootDatum.root α)) f (C (E.rootDatum.root β)) =
        C (E.rootDatum.reflection α (E.rootDatum.root β)) := by
      rw [Module.preReflection_apply, RootPairing.reflection_apply]
      change C (E.rootDatum.root β) -
        E.rootDatum.coroot' α (C.symm (C (E.rootDatum.root β))) • C (E.rootDatum.root α) =
          C (E.rootDatum.root β - E.rootDatum.coroot' α (E.rootDatum.root β) • E.rootDatum.root α)
      rw [C.symm_apply_apply]
      symm
      exact (C.toLinearMap.map_sub _ _).trans (congrArg
        (fun z => C (E.rootDatum.root β) - z) (C.toLinearMap.map_smul _ _))
    rw [he]
    refine ⟨rootIndexEquiv C hC (E.rootDatum.reflectionPerm α β), ?_⟩
    exact (hr _).symm.trans (congrArg C (E.rootDatum.root_reflectionPerm α β))
  apply pairingRootDatum.toLinearMap.flip.toPerfPair.injective
  apply LinearMap.ext
  intro x
  have hx := cocharCoordinates_pair E C (C.symm x) (E.rootDatum.coroot α)
  rw [C.apply_symm_apply] at hx
  change integralPairing x (cocharCoordinates E C (E.rootDatum.coroot α)) =
    integralPairing x (corootCoordinates i)
  rw [integralPairing_apply, integralPairing_apply, ← hx]
  exact reflectionRecovery i f h₂ hm x

private theorem fibreRoots_of_weights {P : IntegralPresentation} {G : SplitGroup P}
    (T : FrameTorus G)
    (hG : ∀ (k : Type) [Field k] [IsAlgClosed k], IsReductive (algebraicFiber G k))
    (hW : ∀ (k : Type) [Field k] [IsAlgClosed k],
      SplitAlbertAdjointWeightsSpecification.FibreWeights T k) :
    FibreRoots T := by
  intro k _ _
  obtain ⟨hS, hM, C, hC⟩ := hW k
  rw [adjointRootSet] at hC
  obtain ⟨comm, ⟨E⟩⟩ := RootData.AbstractPairing.abstractPairing
    (algebraicFiber G k) (hG k) (T.fibre k) hS hM
  letI := comm
  refine ⟨hS, hM, C, hC, comm, E, cocharCoordinates E C.characters, ?_, ?_⟩
  · intro χ ψ
    exact (E.pairing_eq χ ψ).symm.trans (cocharCoordinates_pair E C.characters _ _)
  · intro α
    exact ⟨rootIndexEquiv C.characters hC α, (rootIndexEquiv_char C.characters hC α).symm,
      cocharCoordinates_coroot E C.characters hC α⟩

private def chamberCoweight : CharacterExponents := (-7, ![3, 2, 1])

private theorem chamber_height (r : RootIndex) :
    coordinatePairing (rootCharacter r) chamberCoweight = pairingBase.height r := by
  have simple : ∀ i : Fin 4, coordinatePairing (rootCharacter (simpleIndex i)) chamberCoweight = 1 := by
    decide
  obtain ⟨n, _, _, hn⟩ := pairingBase.exists_root_eq_sum_int r
  rw [pairingBase.height_eq_sum hn, ← integralPairing_apply]
  change integralPairing.flip chamberCoweight (rootCharacter r) = _
  change rootCharacter r = ∑ j ∈ pairingBase.support, n j • rootCharacter j at hn
  rw [hn, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change j ∈ simpleSupport at hj
  obtain ⟨i, rfl⟩ := simpleSupport_coe ▸ (show j ∈ (simpleSupport : Set RootIndex) from hj)
  rw [map_zsmul]
  change n (simpleIndex i) * integralPairing (rootCharacter (simpleIndex i)) chamberCoweight = _
  rw [integralPairing_apply, simple, mul_one]

private theorem positive_decomposition {r : RootIndex} (hr : pairingBase.IsPos r) :
    r ∈ pairingBase.support ∨ ∃ i j, pairingBase.IsPos i ∧ pairingBase.IsPos j ∧
      rootCharacter r = rootCharacter i + rootCharacter j := by
  letI : pairingRootDatum.IsReduced := pairingReduced
  refine RootPairing.Base.IsPos.induction_on_add hr
    (p := fun r => r ∈ pairingBase.support ∨ ∃ i j, pairingBase.IsPos i ∧ pairingBase.IsPos j ∧
      rootCharacter r = rootCharacter i + rootCharacter j) (fun i hi => Or.inl hi) ?_
  intro i j _ h hi hj
  have hi' : pairingBase.IsPos i := by
    rcases hi with hi | ⟨a, b, ha, hb, hab⟩
    · exact pairingBase.isPos_of_mem_support hi
    · exact RootPairing.Base.IsPos.add ha hb hab
  exact Or.inr ⟨i, j, hi', pairingBase.isPos_of_mem_support hj, h⟩

private def fibreDatumEquiv {k : Type} [Field k] {G : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X] (E : AbstractPairing.Datum T)
    (C : Additive (Character T.group) ≃ₗ[ℤ] CharacterExponents)
    (hC : Set.BijOn (fun χ : Character T.group => C (Additive.ofMul χ))
      (absoluteRoots T) (Set.range rootCharacter)) :
    f4Datum.datum.Equiv E.rootDatum where
  weightMap := C.symm.toLinearMap
  coweightMap := (cocharCoordinates E C).toLinearMap
  indexEquiv := (rootIndexEquiv C hC).symm
  weight_coweight_transpose := by
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro x
    change E.rootDatum.toLinearMap (C.symm x) y =
      integralPairing x (cocharCoordinates E C y)
    rw [integralPairing_apply, cocharCoordinates_pair E C, C.apply_symm_apply]
  root_weightMap := by
    funext r
    apply C.injective
    change C (C.symm (rootCharacter r)) = C (E.rootDatum.root ((rootIndexEquiv C hC).symm r))
    rw [C.apply_symm_apply, E.root_eq, ← rootIndexEquiv_char C hC, Equiv.apply_symm_apply]
  coroot_coweightMap := funext (cocharCoordinates_coroot E C hC)
  bijective_weightMap := C.symm.bijective
  bijective_coweightMap := (cocharCoordinates E C).bijective

open BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open CocharacterDynamics (existsLimitDecomposition)

private theorem calibratedBasedFibre {k : Type} [Field k] [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hS : GeometricRadicals.IsSplitTorus T.group)
    (hM : RankOneFlag.IsGeometricallyMaximal T)
    (C : Additive (Character T.group) ≃ₗ[ℤ] CharacterExponents)
    (hC : Set.BijOn (fun χ : Character T.group => C (Additive.ofMul χ))
      (absoluteRoots T) (Set.range rootCharacter)) :
    ∃ (B : ClosedSubgroup G.val) (hB : GeometricBorelConjugacy.IsKBorel B)
      (hTB : SchemeDerivedGroup.IsSubgroupOf T B),
      let Q : Pinning.SplitBorelPair k := ⟨G, hG, T, hS, hM, B, hB, hTB⟩
      ∃ (E : Pinning.AttachedDatum Q) (d : Pinning.BasedIso f4Datum E.toBased),
        ∀ x : CharacterExponents, Additive.toMul (d.val.weightEquiv x) =
          Additive.toMul (C.symm x) := by
  obtain ⟨comm, ⟨E⟩⟩ := RootData.AbstractPairing.abstractPairing G hG T hS hM
  letI := comm
  let Y := cocharCoordinates E C
  let c : Cocharacter T.group := Additive.toMul (Y.symm chamberCoweight)
  let idx := rootIndexEquiv C hC
  have hpair (α : AbstractPairing.Root T) :
      pairing T.group α.val c = pairingBase.height (idx α) := by
    rw [← E.pairing_eq α.val c, cocharCoordinates_pair, ← rootIndexEquiv_char C hC]
    change coordinatePairing (rootCharacter (idx α)) (Y (Y.symm chamberCoweight)) = _
    rw [Y.apply_symm_apply, chamber_height]
  have hreg : IsRegular T c := fun α => (hpair α).symm ▸ pairingBase.height_ne_zero (idx α)
  obtain ⟨U⟩ := existsLimitDecomposition G (c ≫ T.inclusion)
  obtain ⟨_, hB, hTB, hPos, _⟩ :=
    RootData.BorelsAndChambers.regularCocharacterBorel G hG T hS hM c hreg U
  let Q : Pinning.SplitBorelPair k := ⟨G, hG, T, hS, hM, U.parabolic, hB, hTB⟩
  have hpos (α : AbstractPairing.Root T) : α ∈ subgroupRoots T Q.B ↔ pairingBase.IsPos (idx α) := by
    change α ∈ subgroupRoots T U.parabolic ↔ _
    rw [hPos]
    change (0 < pairing T.group α.val c) ↔ 0 < pairingBase.height (idx α)
    rw [hpair]
  have hsum (α β δ : AbstractPairing.Root T) : α.val = β.val * δ.val ↔
      rootCharacter (idx α) = rootCharacter (idx β) + rootCharacter (idx δ) := by
    rw [rootIndexEquiv_char C hC, rootIndexEquiv_char C hC, rootIndexEquiv_char C hC, ← C.map_add]
    exact ⟨fun h => congrArg (fun χ => C (Additive.ofMul χ)) h, fun h => C.injective h⟩
  have hsimple (α : AbstractPairing.Root T) : idx α ∈ pairingBase.support ↔ Pinning.IsSimple Q α := by
    constructor
    · intro hi
      refine ⟨(hpos α).2 (pairingBase.isPos_of_mem_support hi), ?_⟩
      intro β hb δ hd h
      have hs := pairingBase.height_add ((hsum α β δ).1 h)
      have hα := pairingBase.height_one_of_mem_support hi
      have hβ := (hpos β).1 hb
      have hδ := (hpos δ).1 hd
      simp only [RootPairing.Base.IsPos] at hβ hδ
      omega
    · rintro ⟨ha, hnot⟩
      obtain h | ⟨i, j, hi, hj, h⟩ := positive_decomposition ((hpos α).1 ha)
      · exact h
      · obtain ⟨β, rfl⟩ := idx.surjective i
        obtain ⟨δ, rfl⟩ := idx.surjective j
        exact False.elim (hnot β ((hpos β).2 hi) δ ((hpos δ).2 hj) ((hsum α β δ).2 h))
  let e := fibreDatumEquiv E C hC
  have hb : ∀ α, α ∈ (pairingBase.map e).support ↔ idx α ∈ pairingBase.support := by
    classical
    intro α
    rw [RootPairing.Base.support_map_eq]
    change α ∈ pairingBase.support.image idx.symm ↔ _
    rw [Finset.mem_image]
    exact ⟨fun ⟨i, hi, h⟩ => h ▸ (show idx (idx.symm i) ∈ pairingBase.support by simpa),
      fun h => ⟨idx α, h, idx.symm_apply_apply α⟩⟩
  let E' : Pinning.AttachedDatum Q := ⟨comm, E, pairingBase.map e, fun α => (hb α).trans (hsimple α)⟩
  let d : Pinning.BasedIso f4Datum E'.toBased := ⟨e, by
    classical
    change e.indexEquiv '' (pairingBase.support : Set RootIndex) =
      ((pairingBase.map e).support : Set _)
    simp only [RootPairing.Base.support_map_eq, Finset.coe_image]⟩
  exact ⟨U.parabolic, hB, hTB, E', d, fun _ => rfl⟩

private def groupChangeComp {R S U : Type} [CommRing R] [CommRing S] [CommRing U]
    [Algebra R S] [Algebra S U] [Algebra R U]
    (hMap : (algebraMap S U).comp (algebraMap R S) = algebraMap R U) :
    groupChange R U ≅ groupChange R S ⋙ groupChange S U := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap S U))
  let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
  have h : f ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R U)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hMap]
  exact (eqToIso (congrArg (fun m : Spec (CommRingCat.of U) ⟶ Spec (CommRingCat.of R) =>
    (Over.pullback m).mapGrp) h.symm) ≪≫ Functor.mapGrpNatIso (Over.pullbackComp f g)) ≪≫
      Functor.mapGrpCompIso

private def splitComparison_of_integral {D : Pinning.BasedRootDatum.{0}}
    (C : IntegralSemisimpleModel.Model D)
    {P : IntegralPresentation} {G : SplitGroup P}
    (e : G.group ≅ (chevalleyChange ℤ).obj C.group)
    (R : Type) [CommRing R] :
    (groupChange ℤ R).obj G.group ≅ (chevalleyChange R).obj C.group := by
  let I := IntegralSemisimpleModel.Integers.{0}
  letI : Algebra I ℤ := IntegralSemisimpleModel.integerAlgebra ℤ
  letI : Algebra I R := IntegralSemisimpleModel.integerAlgebra R
  have h : (algebraMap ℤ R).comp (algebraMap I ℤ) = algebraMap I R := by
    ext (i : I)
    change algebraMap ℤ R i.down = (i.down : R)
    simp
  exact (groupChange ℤ R).mapIso e ≪≫
    (groupChangeComp h).symm.app C.group

private theorem forms_of_identification (L : IntegralSplitIdentification)
    (centre : SplitAlbertAdjointWeightsSpecification.UniversallyTrivialCentre L.split) :
    AlbertForms L.datum L.chevalley := by
  intro R _ M _ _ J hJ
  obtain ⟨G, hA, hFP, hRep, hBC⟩ := AutomorphismDescent.automorphismRepresentation J hJ
  obtain ⟨hFib, hSplit, ⟨hSmooth, hConnected⟩, hCentre⟩ :=
    AutomorphismDescent.automorphismDescent J hJ G hA hRep L.split
  letI : SmoothOfRelativeDimension 52 L.split.group.X.hom := L.smooth
  refine ⟨G, hA, hFP, hRep, hSmooth (SmoothOfRelativeDimension.smooth 52 L.split.group.X.hom),
    hConnected L.connected, hCentre centre,
    hBC, ?_, ?_⟩
  · intro K _ _ _
    exact ⟨algebraicFiber L.split K, (L.adjointSemisimple K).1, hFib K,
      ⟨splitComparison_of_integral L.chevalley L.comparison K⟩⟩
  · intro h
    obtain ⟨e⟩ := hSplit h
    exact ⟨e ≪≫ splitComparison_of_integral L.chevalley L.comparison R⟩

end
end LinearAlgebraicGroups.Albert.AutomorphismType

namespace LinearAlgebraicGroups.Albert.AutomorphismType

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open LinearAlgebraicGroups.Specs AutomorphismTypeSpecification
open IntegralCentralQuotient (HopfSpectrum spectrumOfHopfHom)
open scoped CategoryTheory.MonObj TensorProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.unnecessarySimpa false

open private fibreSpecIso fibreGroupIso fibreSpecIso_natural fibreSpecIso_inv_fst
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRelativeCell

private abbrev hopfIso {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [HopfAlgebra R A] [HopfAlgebra R B] (e : A ≃ₐc[R] B) :
    HopfSpectrum R B ≅ HopfSpectrum R A :=
  (hopfSpec (CommRingCat.of R)).mapIso (CommHopfAlgCat.isoMk e).op

private theorem hopfSchemeExists {R : Type} [CommRing R] (G : SpinSpecification.GroupScheme R)
    (hG : IsAffine G.X.left) :
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra R A), Nonempty (HopfSpectrum R A ≅ G) := by
  obtain ⟨A, ⟨e⟩⟩ := (essImage_hopfSpec (R := CommRingCat.of R)).2 hG
  exact ⟨A.unop, inferInstance, inferInstance, ⟨e⟩⟩

private def hopfRestriction {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [HopfAlgebra R A] [HopfAlgebra R B] (j : HopfSpectrum R B ⟶ HopfSpectrum R A) :
    A →ₐc[R] B :=
  ((hopfSpec.fullyFaithful (R := CommRingCat.of R)).preimage j).unop.hom

private theorem hopfRestriction_spec {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [HopfAlgebra R A] [HopfAlgebra R B] (j : HopfSpectrum R B ⟶ HopfSpectrum R A) :
    spectrumOfHopfHom (hopfRestriction j) = j :=
  (hopfSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage j

private theorem hopfRestriction_surj {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [HopfAlgebra R A] [HopfAlgebra R B] (j : HopfSpectrum R B ⟶ HopfSpectrum R A)
    (hj : IsClosedImmersion j.hom.hom.left) : Function.Surjective (hopfRestriction j) := by
  rw [← hopfRestriction_spec j] at hj
  let a := hopfRestriction j
  change IsClosedImmersion (Spec.map (CommRingCat.ofHom a.toAlgHom.toRingHom)) at hj
  have := hj
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine
    (Spec.map (CommRingCat.ofHom a.toAlgHom.toRingHom))).2
  have en := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom a.toAlgHom.toRingHom)
  have h := ConcreteCategory.congr_hom en
  intro b
  have : IsIso ((Scheme.ΓSpecIso (CommRingCat.of B)).inv) := inferInstance
  obtain ⟨x, hx⟩ := hs (((Scheme.ΓSpecIso (CommRingCat.of B)).inv) b)
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2 x
  exact ⟨y, (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).1
    ((h y).trans hx)⟩

private theorem spectrum_finitePresentation {R A : Type} [CommRing R] [CommRing A] [HopfAlgebra R A]
    (h : LocallyOfFinitePresentation (HopfSpectrum R A).X.hom) :
    Algebra.FinitePresentation R A :=
  RingHom.finitePresentation_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp h)

private theorem fibreGroupIso_natural {R A B k : Type} [CommRing R] [CommRing A] [CommRing B]
    [Field k] [Algebra R k] [HopfAlgebra R A] [HopfAlgebra R B] (f : A →ₐc[R] B) :
    (fibreGroupIso k B).inv ≫ (groupChange R k).map (spectrumOfHopfHom f) =
      spectrumOfHopfHom (Bialgebra.TensorProduct.map (BialgHom.id k k) f) ≫ (fibreGroupIso k A).inv := by
  apply Grp.hom_ext
  exact fibreSpecIso_natural k f.toAlgHom

private theorem pullbackComp_fst {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (V : Over Z) :
    ((Over.pullbackComp f g).hom.app V).left ≫
      pullback.fst (pullback.snd V.hom g) f ≫ pullback.fst V.hom g =
      pullback.fst V.hom (f ≫ g) := by
  have h := conjugateEquiv_counit (Over.mapPullbackAdj (f ≫ g))
    ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g)) (Over.mapComp f g).inv V
  have h' := congrArg Over.Hom.left h
  simpa [Over.pullbackComp, Adjunction.comp_counit] using h'

private def hopfChangeIso (S : Type) {R B : Type} [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [HopfAlgebra R B] :
    (groupChange R S).obj (HopfSpectrum R B) ≅ HopfSpectrum S (S ⊗[R] B) := by
  let e : ((groupChange R S).obj (HopfSpectrum R B)).X ≅ (HopfSpectrum S (S ⊗[R] B)).X :=
    (pullbackSymmetry .. ≪≫ pullbackSpecIso' R S B).asOver (Spec (CommRingCat.of S))
  letI : IsMonHom e.hom := by
    change IsMonHom ((pullbackSymmetry .. ≪≫ pullbackSpecIso' R S B).hom.asOver
      (Spec (CommRingCat.of S)))
    infer_instance
  exact Grp.mkIso' e

@[reassoc]
private theorem hopfChangeIso_inv_fst (S : Type) {R B : Type} [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [HopfAlgebra R B] :
    (hopfChangeIso S (R := R) (B := B)).inv.hom.hom.left ≫ pullback.fst
      (HopfSpectrum R B).X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom) := by
  change (pullbackSpecIso' R S B).inv ≫ (pullbackSymmetry _ _).inv ≫ pullback.fst _ _ = _
  rw [pullbackSymmetry_inv_comp_fst]
  exact pullbackSpecIso_inv_snd R S B

open Coalgebra Algebra.TensorProduct in
private def groupAlgebraChange (R S M : Type) [CommRing R] [CommRing S] [Algebra R S] [CommGroup M] :
    S ⊗[R] MonoidAlgebra R M ≃ₐc[S] MonoidAlgebra S M := by
  let e := MonoidAlgebra.scalarTensorEquiv R S (M := M)
  have hm (m : M) : e ((1 : S) ⊗ₜ[R] MonoidAlgebra.single m 1) =
      MonoidAlgebra.single m 1 := by
    apply e.symm.injective
    rw [AlgEquiv.symm_apply_apply]
    exact (MonoidAlgebra.scalarTensorEquiv_symm_single (R := R) (A := S) m 1).symm
  refine BialgEquiv.ofAlgEquiv e ?_ ?_
  · apply Algebra.TensorProduct.ext_ring
    apply (MonoidAlgebra.lift R S M).symm.injective
    apply MonoidHom.ext
    intro m
    simp only [MonoidAlgebra.lift_symm_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      includeRight_apply, Bialgebra.counitAlgHom_apply, AlgEquiv.toAlgHom_apply,
      TensorProduct.counit_tmul, MonoidAlgebra.counit_single, hm, CommSemiring.counit_apply]
    rw [Algebra.smul_def, map_one, one_mul]
  · apply Algebra.TensorProduct.ext_ring
    apply (MonoidAlgebra.lift R _ M).symm.injective
    apply MonoidHom.ext
    intro m
    simp only [MonoidAlgebra.lift_symm_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      includeRight_apply, Bialgebra.comulAlgHom_apply, AlgEquiv.toAlgHom_apply,
      hm, TensorProduct.comul_tmul, CommSemiring.comul_apply, MonoidAlgebra.comul_single,
      TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      Algebra.TensorProduct.map_tmul]

/-- The standard identification of a group-algebra torus with the scalar
extension of the same torus over the coefficient ring. -/
private def groupAlgebraSchemeChange (R S M : Type) [CommRing R] [CommRing S] [Algebra R S] [CommGroup M] :
    HopfSpectrum S (MonoidAlgebra S M) ≅ (groupChange R S).obj (HopfSpectrum R (MonoidAlgebra R M)) :=
  hopfIso (groupAlgebraChange R S M) ≪≫ (hopfChangeIso S (R := R) (B := MonoidAlgebra R M)).symm

@[reassoc]
private theorem groupAlgebraSchemeChange_fst (R S M : Type) [CommRing R] [CommRing S]
    [Algebra R S] [CommGroup M] :
    (groupAlgebraSchemeChange R S M).hom.hom.hom.left ≫
      pullback.fst (HopfSpectrum R (MonoidAlgebra R M)).X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      Spec.map (CommRingCat.ofHom ((groupAlgebraChange R S M).toAlgEquiv.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight : MonoidAlgebra R M →ₐ[R] S ⊗[R] MonoidAlgebra R M).toRingHom)) := by
  rw [groupAlgebraSchemeChange, Iso.trans_hom, Grp.comp_hom_hom, Over.comp_left, Category.assoc]
  rw [show (hopfChangeIso S (R := R) (B := MonoidAlgebra R M)).symm.hom =
    (hopfChangeIso S (R := R) (B := MonoidAlgebra R M)).inv from rfl,
    hopfChangeIso_inv_fst]
  exact (Spec.map_comp _ _).symm

private def pullbackGroupComp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (hf : f ≫ g = h) :
    (Over.pullback h).mapGrp ≅ (Over.pullback g).mapGrp ⋙ (Over.pullback f).mapGrp :=
  (eqToIso (congrArg (fun m : X ⟶ Z => (Over.pullback m).mapGrp) hf.symm) ≪≫
    Functor.mapGrpNatIso (Over.pullbackComp f g)) ≪≫ Functor.mapGrpCompIso

@[reassoc]
private theorem pullbackGroupComp_inv_fst {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (hf : f ≫ g = h) (G : Grp (Over Z)) :
    ((pullbackGroupComp f g h hf).inv.app G).hom.hom.left ≫ pullback.fst G.X.hom h =
      pullback.fst (pullback.snd G.X.hom g) f ≫ pullback.fst G.X.hom g := by
  subst h
  let b := pullbackGroupComp f g (f ≫ g) rfl
  have he : ((b.hom.app G).hom.hom.left) ≫ pullback.fst (pullback.snd G.X.hom g) f ≫
      pullback.fst G.X.hom g = pullback.fst G.X.hom (f ≫ g) :=
    pullbackComp_fst f g G.X
  rw [← he, ← Category.assoc]
  have hid := congrArg (fun a => (a.app G).hom.hom.left) b.inv_hom_id
  change (b.inv.app G).hom.hom.left ≫ (b.hom.app G).hom.hom.left = 𝟙 _ at hid
  rw [hid, Category.id_comp]

@[reassoc]
private theorem changeMap_fst {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    {G H : SpinSpecification.GroupScheme R} (f : G ⟶ H) :
    ((groupChange R S).map f).hom.hom.left ≫
      pullback.fst H.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≫ f.hom.hom.left :=
  pullback.lift_fst _ _ _

private theorem changeMap_closed {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    {G H : SpinSpecification.GroupScheme R} (i : G ⟶ H)
    (hi : IsClosedImmersion i.hom.hom.left) :
    IsClosedImmersion ((groupChange R S).map i).hom.hom.left := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let j := i.hom.hom
  let b := ((Over.pullback f).map j).left
  change IsClosedImmersion b
  have top : IsPullback (pullback.fst G.X.hom f) (pullback.snd G.X.hom f)
      (j.left ≫ H.X.hom) f := by
    rw [Over.w j]
    exact IsPullback.of_hasPullback _ _
  have h₁ : b ≫ pullback.fst H.X.hom f = pullback.fst G.X.hom f ≫ j.left :=
    pullback.lift_fst _ _ _
  have h₂ : b ≫ pullback.snd H.X.hom f = pullback.snd G.X.hom f :=
    pullback.lift_snd _ _ _
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (IsPullback.of_bot (h₂.symm ▸ top) h₁.symm (IsPullback.of_hasPullback _ _)) hi

end
end LinearAlgebraicGroups.Albert.AutomorphismType

namespace LinearAlgebraicGroups.Albert.AutomorphismType

open AlgebraicGeometry CategoryTheory Opposite WithConv
open LinearAlgebraicGroups.Specs
open IntegralCentralQuotient (IntegralRing HopfSpectrum spectrumOfAlgHom spectrumOfHopfHom)
open IntegralRecognition
open Specs.IntegralAlbertRootPins (WeightSpace identityDifferential HasExtendedWeight)
open CharacterDescent (Character)
open CharacterPairing (absoluteRoots adjointWeightVectors adjointWeightSpace characterValue)
open Specs.AdjointRepresentation (GroupPoints constants scale dualMap)
open scoped CategoryTheory.MonObj TensorProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open private tangentPoint characterValue_spectrum spectrumOfAlgHom_comp spectrumOfAlgHom_injective
  integralRing_isDomain integralRing_isPrincipalIdealRing
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRecognition
open private canonicalZero_eq from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private functional_ext from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntegralAlbertRootPins
open private pointConvolutionGroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRootCoordinates
attribute [local instance] pointConvolutionGroup

local instance (priority := 2000) integralScalarModule {A : Type} [CommRing A]
    [Algebra IntegralRing A] : Module IntegralRing A := Algebra.toModule

private theorem tangentPoint_surjective {k A : Type} [Field k] [CommRing A] [HopfAlgebra k A]
    {G : GroupScheme k} (e : HopfSpectrum k A ≅ G) :
    Function.Surjective (tangentPoint e) := by
  intro v
  let q : WithConv (A →ₐ[k] DualNumber k) :=
    Spec.mapMulEquiv.symm (v.toMul.val ≫ e.inv.hom.hom)
  have hq : spectrumOfAlgHom q.ofConv ≫ e.hom.hom.hom = v.toMul.val := by
    change Spec.mapMulEquiv q ≫ e.hom.hom.hom = _
    rw [MulEquiv.apply_symm_apply, Category.assoc]
    rw [← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  have h₁ : (TrivSqZeroExt.fstHom k k k).comp q.ofConv = Bialgebra.counitAlgHom k A := by
    have hv := v.toMul.property
    change mapPoints (dualReduction k) v.toMul.val = 1 at hv
    rw [← hq] at hv
    change spectrumOfAlgHom (TrivSqZeroExt.fstHom k k k) ≫
      (spectrumOfAlgHom q.ofConv ≫ e.hom.hom.hom) = _ at hv
    rw [← Category.assoc, ← spectrumOfAlgHom_comp] at hv
    apply spectrumOfAlgHom_injective
    apply (cancel_mono e.hom.hom.hom).mp
    rw [hv]
    change 1 = Spec.mapMulEquiv (1 : WithConv (A →ₐ[k] k)) ≫ e.hom.hom.hom
    rw [map_one, MonObj.one_comp]
  exact ⟨⟨q.ofConv, h₁⟩, Subtype.ext hq⟩

private theorem tangentPoint_scale_coeff {k A : Type} [Field k] [CommRing A] [HopfAlgebra k A]
    {G : GroupScheme k} (e : HopfSpectrum k A ≅ G) (c : k) (v w : Tangent k A)
    (h : scalePointKernel G c (tangentPoint e v) = tangentPoint e w) (a : A) :
    c * (v.val a).snd = (w.val a).snd := by
  have h' := congrArg (fun q : Lie k G => q.toMul.val) h
  change spectrumOfAlgHom (dualNumberScale c) ≫ (spectrumOfAlgHom v.val ≫ e.hom.hom.hom) =
    spectrumOfAlgHom w.val ≫ e.hom.hom.hom at h'
  rw [← Category.assoc, ← spectrumOfAlgHom_comp] at h'
  have he := spectrumOfAlgHom_injective ((cancel_mono e.hom.hom.hom).mp h')
  have hval := congrArg (fun q : A →ₐ[k] DualNumber k => (q a).snd) he
  simpa only [AlgHom.comp_apply, dualNumberScale, TrivSqZeroExt.snd_map, LinearMap.smul_apply,
    LinearMap.id_apply, smul_eq_mul] using hval

private theorem tangentPoint_weight_iff {R K A X : Type} [CommRing R] [Field K] [Algebra R K]
    [CommRing A] [HopfAlgebra R A] [CommGroup X]
    (t : A →ₐc[R] MonoidAlgebra R X) (α : X)
    {G : GroupScheme K} (T : ClosedSubgroup G) (χ : Character T.group)
    (e : HopfSpectrum K (K ⊗[R] A) ≅ G)
    (s : HopfSpectrum K (K ⊗[R] MonoidAlgebra R X) ≅ T.group)
    (hs : spectrumOfHopfHom (Bialgebra.TensorProduct.map (BialgHom.id K K) t) ≫ e.hom =
      s.hom ≫ T.inclusion)
    (hχ : characterMonomial (s.hom ≫ χ) = (1 : K) ⊗ₜ[R] MonoidAlgebra.of R X α)
    (v : Tangent K (K ⊗[R] A)) :
    HasExtendedWeight t α K v ↔
      tangentPoint e v ∈ adjointWeightVectors T χ := by
  let H := K ⊗[R] MonoidAlgebra R X
  let tK := Bialgebra.TensorProduct.map (BialgHom.id K K) t
  have transport (S : TestAlgebra K) (a : H →ₐ[K] S) :
      (let g := toConv ((TrivSqZeroExt.inlAlgHom K S S).comp (a.comp tK.toAlgHom))
       let p := (dualCoefficients S).comp v.val
       let c := a ((1 : K) ⊗ₜ[R] MonoidAlgebra.of R X α)
       let act := (TrivSqZeroExt.map (c • (LinearMap.id : S →ₗ[S] S))).restrictScalars K
       g * toConv p * toConv (g.ofConv.comp (HopfAlgebra.antipodeAlgHom K (K ⊗[R] A))) =
        toConv (act.comp p)) ↔
      (let b := spectrumOfAlgHom a ≫ s.hom.hom.hom
       let p := mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId K S))) (tangentPoint e v).toMul.val
       let g := mapPoints (constants S) (b ≫ T.inclusion.hom.hom)
       g * p * g⁻¹ = mapPoints (scale S (characterValue χ S b)) p) := by
    dsimp only
    let W := CommAlgCat.of K (DualNumber S)
    let m : WithConv (K ⊗[R] A →ₐ[K] W) →* GroupPoints G W :=
      (((groupPointsFunctor K).map e.hom).app W).hom.comp Spec.mapMulEquiv.toMonoidHom
    have hm : Function.Injective m := by
      intro p q h
      exact Spec.mapMulEquiv.injective ((cancel_mono e.hom.hom.hom).mp h)
    let g := toConv ((TrivSqZeroExt.inlAlgHom K S S).comp (a.comp tK.toAlgHom))
    let p := (dualCoefficients S).comp v.val
    let c := a ((1 : K) ⊗ₜ[R] MonoidAlgebra.of R X α)
    have hval : characterValue χ S (spectrumOfAlgHom a ≫ s.hom.hom.hom) = c := by
      rw [show characterValue χ S (spectrumOfAlgHom a ≫ s.hom.hom.hom) =
        characterValue (s.hom ≫ χ) S (spectrumOfAlgHom a) by
          unfold characterValue
          rw [Category.assoc]
          rfl, characterValue_spectrum, hχ]
    have hg : m g = mapPoints (constants S)
        ((spectrumOfAlgHom a ≫ s.hom.hom.hom) ≫ T.inclusion.hom.hom) := by
      change spectrumOfAlgHom ((TrivSqZeroExt.inlAlgHom K S S).comp (a.comp tK.toAlgHom)) ≫
        e.hom.hom.hom = spectrumOfAlgHom (TrivSqZeroExt.inlAlgHom K S S) ≫ _
      rw [spectrumOfAlgHom_comp, spectrumOfAlgHom_comp, Category.assoc, Category.assoc]
      change _ ≫ (_ ≫ (spectrumOfHopfHom tK).hom.hom ≫ e.hom.hom.hom) = _
      rw [← Grp.comp_hom_hom, hs, Grp.comp_hom_hom, Category.assoc]
    have hp : m (toConv p) =
        mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId K S))) (tangentPoint e v).toMul.val := by
      change spectrumOfAlgHom p ≫ e.hom.hom.hom =
        spectrumOfAlgHom (dualCoefficients (R := K) S) ≫
          (spectrumOfAlgHom v.val ≫ e.hom.hom.hom)
      rw [← Category.assoc, ← spectrumOfAlgHom_comp]
    have hscale : m (toConv ((scale S c).hom.comp p)) = mapPoints (scale S c) (m (toConv p)) := by
      change spectrumOfAlgHom ((scale S c).hom.comp p) ≫ e.hom.hom.hom =
        spectrumOfAlgHom (scale S c).hom ≫ (spectrumOfAlgHom p ≫ e.hom.hom.hom)
      rw [spectrumOfAlgHom_comp, Category.assoc]
    let u := (TrivSqZeroExt.map (c • (LinearMap.id : S →ₗ[S] S))).restrictScalars K
    have hu : u = (scale S c).hom := by
      apply AlgHom.ext
      intro w
      apply TrivSqZeroExt.ext
      · change ((TrivSqZeroExt.map (c • (LinearMap.id : S →ₗ[S] S))) w).fst = w.fst
        exact TrivSqZeroExt.fst_map _ _
      · change ((TrivSqZeroExt.map (c • (LinearMap.id : S →ₗ[S] S))) w).snd = c * w.snd
        rw [TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    change g * toConv p * g⁻¹ = toConv (u.comp p) ↔ _
    rw [hu, ← hm.eq_iff, map_mul, map_mul, map_inv, hscale, hg, hp, hval]
  constructor
  · intro hv S b
    let a : WithConv (H →ₐ[K] S) := Spec.mapMulEquiv.symm (b ≫ s.inv.hom.hom)
    have hb : spectrumOfAlgHom a.ofConv ≫ s.hom.hom.hom = b := by
      change Spec.mapMulEquiv a ≫ s.hom.hom.hom = _
      rw [MulEquiv.apply_symm_apply, Category.assoc, ← Grp.comp_hom_hom, s.inv_hom_id,
        Grp.id_hom_hom, Category.comp_id]
    have ht := (transport S a.ofConv).mp (hv S a.ofConv)
    dsimp only at ht
    rwa [hb] at ht
  · intro hv S a
    exact (transport S a).mpr (hv S (spectrumOfAlgHom a ≫ s.hom.hom.hom))

private theorem weight_Finrank {A K X : Type} [CommRing A] [HopfAlgebra IntegralRing A]
    [CommGroup X] [Field K] [Algebra IntegralRing K]
    (t : A →ₐc[IntegralRing] MonoidAlgebra IntegralRing X)
    (hFP : Algebra.FinitePresentation IntegralRing A)
    (hS : Smooth (HopfSpectrum IntegralRing A).X.hom) (ht : Function.Surjective t)
    (α : X) {G : AffineAlgebraicGroup K} (hG : GeometricRadicals.IsReductive G)
    (T : ClosedSubgroup G.val) (hSplit : GeometricRadicals.IsSplitTorus T.group)
    (hMax : RankOneFlag.IsGeometricallyMaximal T) (χ : Character T.group) (hRoot : χ ∈ absoluteRoots T)
    (e : HopfSpectrum K (K ⊗[IntegralRing] A) ≅ G.val)
    (s : HopfSpectrum K (K ⊗[IntegralRing] MonoidAlgebra IntegralRing X) ≅ T.group)
    (hs : spectrumOfHopfHom (Bialgebra.TensorProduct.map (BialgHom.id K K) t) ≫ e.hom =
      s.hom ≫ T.inclusion)
    (hχ : characterMonomial (s.hom ≫ χ) = (1 : K) ⊗ₜ[IntegralRing] MonoidAlgebra.of IntegralRing X α) :
    Module.finrank K (WeightSpace t α K) = 1 := by
  letI : IsDomain IntegralRing := integralRing_isDomain
  letI : IsPrincipalIdealRing IntegralRing := integralRing_isPrincipalIdealRing
  obtain ⟨_, _, _, hbase⟩ := IntegralAlbertRootPins.weightBaseChange t α hFP hS ht
  obtain ⟨_, hto, hfrom⟩ := hbase K
  obtain ⟨L⟩ := LinearAlgebraicGroups.identityLieBracket K G
  letI := L.lieRing
  letI := L.lieAlgebra
  let M := adjointWeightSpace T χ L
  have hM : Module.finrank K M = 1 :=
    (RootData.RootGroups.rootSubgroups G hG T hSplit hMax).2 χ hRoot |>.1 L
  have hmem (v : Lie K G.val) : v ∈ M ↔ v ∈ adjointWeightVectors T χ := by
    change v ∈ (M : Set (Lie K G.val)) ↔ _
    rw [show (M : Set (Lie K G.val)) = adjointWeightVectors T χ from
      RootData.CharacterPairing.adjointWeightSpaceVectors G T L χ]
  obtain ⟨_, v, hv, hn⟩ := hRoot
  obtain ⟨b, he⟩ := tangentPoint_surjective e v
  have hw := (tangentPoint_weight_iff t α T χ e s hs hχ b).mpr (he ▸ hv)
  obtain ⟨f, hf, _⟩ := (hto b).mp hw
  have hvM : v ∈ M := (hmem v).mpr hv
  let vM : M := ⟨v, hvM⟩
  have hvnz : vM ≠ 0 := by
    intro h
    have hh := congrArg (fun z : M => (z : Lie K G.val)) h
    exact hn (hh.trans (canonicalZero_eq L).symm)
  have hspan := (finrank_eq_one_iff_of_nonzero' vM hvnz).mp hM
  have hscale (c : K) (w : Tangent K (K ⊗[IntegralRing] A))
      (he' : scalePointKernel G.val c (tangentPoint e b) = tangentPoint e w) (a : A) :
      c * (b.val ((1 : K) ⊗ₜ[IntegralRing] a)).snd = (w.val ((1 : K) ⊗ₜ[IntegralRing] a)).snd := by
    exact tangentPoint_scale_coeff e c b w he' _
  have fnz : f ≠ 0 := by
    intro hz
    obtain ⟨w, hw⟩ := tangentPoint_surjective e (0 : Lie K G.val)
    have hscaleZero : scalePointKernel G.val 0 (tangentPoint e b) = tangentPoint e w := by
      rw [hw, canonicalZero_eq L, ← congrFun (congrFun L.scalar_law (0 : K)) (tangentPoint e b)]
      letI : AddCommGroup (Lie K G.val) := L.lieRing.toAddCommGroup
      letI : Module K (Lie K G.val) := L.lieAlgebra.toModule
      exact @zero_smul K (Lie K G.val) _ L.lieRing.toAddCommGroup.toZero _ _
    have hzero (a : A) : (w.val ((1 : K) ⊗ₜ[IntegralRing] a)).snd = 0 :=
      ((hscale 0 w hscaleZero a).symm.trans (zero_mul _))
    have eq : b = w := by
      apply Subtype.ext
      apply (AlgHom.liftEquiv IntegralRing K A (DualNumber K)).symm.injective
      apply AlgHom.ext
      intro a
      apply TrivSqZeroExt.ext
      · exact (DFunLike.congr_fun b.property ((1 : K) ⊗ₜ[IntegralRing] a)).trans
          (DFunLike.congr_fun w.property ((1 : K) ⊗ₜ[IntegralRing] a)).symm
      · rw [show ((AlgHom.liftEquiv IntegralRing K A (DualNumber K)).symm b.val a).snd =
            (b.val ((1 : K) ⊗ₜ[IntegralRing] a)).snd from rfl,
          show ((AlgHom.liftEquiv IntegralRing K A (DualNumber K)).symm w.val a).snd =
            (w.val ((1 : K) ⊗ₜ[IntegralRing] a)).snd from rfl, hf, hzero, hz]
        rfl
    exact hn (he.symm.trans ((congrArg (tangentPoint e) eq).trans hw))
  apply (finrank_eq_one_iff_of_nonzero' f fnz).mpr
  intro f'
  obtain ⟨w, ⟨hw, hf'⟩, _⟩ := hfrom f'
  let wM : M := ⟨tangentPoint e w, (hmem _).mpr ((tangentPoint_weight_iff t α T χ e s hs hχ w).mp hw)⟩
  obtain ⟨c, hc⟩ := hspan wM
  have hw' : scalePointKernel G.val c (tangentPoint e b) = tangentPoint e w := by
    rw [he, ← congrFun (congrFun L.scalar_law c) v]
    exact congrArg (fun z : M => (z : Lie K G.val)) hc
  refine ⟨c, Subtype.ext (functional_ext fun a => ?_)⟩
  exact (congrArg (c * ·) (hf a).symm).trans ((hscale c w hw' a).trans (hf' a))

end
end LinearAlgebraicGroups.Albert.AutomorphismType

namespace LinearAlgebraicGroups.Albert.AutomorphismType

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open LinearAlgebraicGroups.Specs
open IntegralCentralQuotient (IntegralRing HopfSpectrum spectrumOfAlgHom spectrumOfHopfHom)
open Specs.IntegralSemisimpleModel (splitTorus torusPoint TorusValues forgetFibrePoint)
open Specs.Pinning (BasedRootDatum BasedIso SplitBorelPair AttachedDatum)
open CharacterPairing (characterValue)
open Specs.AdjointRepresentation (GroupPoints)
open AutomorphismTypeSpecification (groupChange)
open scoped TensorProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

open private fibreGroupIso fibreSpecIso fibreSpecIso_inv_fst
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRelativeCell
open private characterValue_spectrum from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRecognition
open private torusPoint_surjective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates

local instance (priority := 2000) markedIntegralModule {A : Type} [CommRing A]
    [Algebra IntegralRing A] : Module IntegralRing A := Algebra.toModule

private abbrev IntegralGroup := SpinSpecification.GroupScheme IntegralRing.{0}
private abbrev CharacterRing (D : BasedRootDatum.{0}) := MonoidAlgebra IntegralRing (Multiplicative D.X)

private theorem integerAlgebra_eq (k : Type) [CommRing k] (a b : Algebra IntegralRing.{0} k) : a = b := by
  apply Algebra.algebra_ext
  intro i
  have hi : i = (i.down : IntegralRing.{0}) := ULift.ext (by simp)
  rw [hi, map_intCast, map_intCast]

private abbrev groupAlgebraTest (R k M : Type) [CommRing R] [Field k] [Algebra R k] [CommGroup M] :=
  CommAlgCat.of k (k ⊗[R] MonoidAlgebra R M)

private abbrev universalGroupAlgebraPoint (R k M : Type) [CommRing R] [Field k] [Algebra R k]
    [CommGroup M] :
    GroupPoints ((groupChange R k).obj (HopfSpectrum R (MonoidAlgebra R M))) (groupAlgebraTest R k M) :=
  (fibreGroupIso k (R := R) (MonoidAlgebra R M)).inv.hom.hom

private def mapGroupAlgebraPoint (R k M : Type) [CommRing R] [Field k] [Algebra R k] [CommGroup M]
    {T : GroupScheme k} (e : (groupChange R k).obj (HopfSpectrum R (MonoidAlgebra R M)) ≅ T) :
    GroupPoints T (groupAlgebraTest R k M) :=
  universalGroupAlgebraPoint R k M ≫ e.hom.hom.hom

private abbrev groupAlgebraMonomial (R k M : Type) [CommRing R] [Field k] [Algebra R k] [CommGroup M]
    (m : M) : groupAlgebraTest R k M :=
  (1 : k) ⊗ₜ[R] MonoidAlgebra.of R M m

private abbrev torusTest (D : BasedRootDatum.{0}) (k : Type) [Field k] [Algebra IntegralRing k] :=
  groupAlgebraTest IntegralRing k (Multiplicative D.X)

/-- The universal torus point before changing from the affine to the pullback presentation. -/
private abbrev universalTorus (D : BasedRootDatum.{0}) (k : Type) [Field k] [Algebra IntegralRing k] :=
  universalGroupAlgebraPoint IntegralRing k (Multiplicative D.X)

private abbrev mappedUniversalTorus (D : BasedRootDatum.{0}) (k : Type) [Field k] [Algebra IntegralRing k]
    {T : GroupScheme k} (e : (groupChange IntegralRing k).obj (splitTorus D) ≅ T) :=
  mapGroupAlgebraPoint IntegralRing k (Multiplicative D.X) e

private abbrev torusMonomial (D : BasedRootDatum.{0}) (k : Type) [Field k] [Algebra IntegralRing k]
    (x : D.X) : torusTest D k :=
  groupAlgebraMonomial IntegralRing k (Multiplicative D.X) (Multiplicative.ofAdd x)

private def MarkedOneFibre {D : Pinning.BasedRootDatum.{0}} {G : IntegralGroup}
    (j : splitTorus D ⟶ G) (k : Type) [Field k] [Algebra IntegralRing k] : Prop :=
    ∃ (Q : Pinning.SplitBorelPair k) (e : (groupChange IntegralRing k).obj G ≅ Q.G.val)
      (s : (groupChange IntegralRing k).obj (splitTorus D) ≅ Q.T.group)
      (E : Pinning.AttachedDatum Q) (d : Pinning.BasedIso D E.toBased),
      (groupChange IntegralRing k).map j ≫ e.hom = s.hom ≫ Q.T.inclusion ∧
      ∀ x : D.X, characterValue (Additive.toMul (d.val.weightEquiv x)) (torusTest D k)
        (mappedUniversalTorus D k s) =
        torusMonomial D k x

private def MarkedFibres {D : BasedRootDatum.{0}} {G : IntegralGroup} (j : splitTorus D ⟶ G) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra IntegralRing k], MarkedOneFibre j k

private theorem chevalley_markedFibres {D : BasedRootDatum.{0}} (C : IntegralSemisimpleModel.Model D) :
    MarkedFibres C.torus := by
  intro k _ _ alg
  rw [integerAlgebra_eq k alg (IntegralSemisimpleModel.integerAlgebra k)]
  letI : Algebra IntegralRing k := IntegralSemisimpleModel.integerAlgebra k
  obtain ⟨A, F, e, s, _, hj, _, hval, _⟩ := C.fieldFibre k
  let S : TestAlgebra k := torusTest D k
  let p := universalTorus D k
  obtain ⟨v, hv⟩ := torusPoint_surjective D (CommAlgCat.of IntegralRing S)
    (forgetFibrePoint (splitTorus D) S p)
  refine ⟨F.pinned.pair, e, s, F.attached, F.datumIso, hj, fun x => ?_⟩
  have heval := hval S p v hv.symm x
  change characterValue _ S (mappedUniversalTorus D k s) = _ at heval
  rw [heval]
  let a := MonoidAlgebra.lift IntegralRing S (Multiplicative D.X) ((Units.coeHom S).comp v)
  let inc : CharacterRing D →ₐ[IntegralRing] k ⊗[IntegralRing] CharacterRing D :=
    Algebra.TensorProduct.includeRight
  have h := congrArg Over.Hom.left hv.symm
  change (fibreGroupIso k (CharacterRing D)).inv.hom.hom.left ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom a.toRingHom) at h
  have hp : (fibreGroupIso k (CharacterRing D)).inv.hom.hom.left ≫
      pullback.fst (splitTorus D).X.hom (Spec.map (CommRingCat.ofHom (algebraMap IntegralRing k))) =
        Spec.map (CommRingCat.ofHom inc.toRingHom) :=
    fibreSpecIso_inv_fst (R := IntegralRing) k (CharacterRing D)
  rw [hp] at h
  have he := ConcreteCategory.congr_hom (Spec.map_injective h) (MonoidAlgebra.of IntegralRing
    (Multiplicative D.X) (Multiplicative.ofAdd x))
  change inc (MonoidAlgebra.of IntegralRing _ (Multiplicative.ofAdd x)) =
    a (MonoidAlgebra.of IntegralRing _ (Multiplicative.ofAdd x)) at he
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.lift_single] at he
  simpa [Algebra.smul_def, inc, MonoidAlgebra.of_apply, a, torusMonomial, groupAlgebraMonomial] using he.symm

set_option maxHeartbeats 1000000 in
private theorem recognition_of_markedGroup {D : BasedRootDatum.{0}} (G : IntegralGroup)
    (j : splitTorus D ⟶ G) (hAffine : IsAffine G.X.left) (hFP : LocallyOfFinitePresentation G.X.hom)
    (hSmooth : Smooth G.X.hom) (hClosed : IsClosedImmersion j.hom.hom.left)
    (hFibre : MarkedFibres j) :
    ∃ (P : IntegralRecognition.Model D) (e : HopfSpectrum IntegralRing P.A ≅ G),
      spectrumOfHopfHom P.torus ≫ e.hom = j := by
  obtain ⟨A, rA, hA, ⟨e⟩⟩ := hopfSchemeExists G hAffine
  letI := rA
  letI := hA
  let t : A →ₐc[IntegralRing] CharacterRing D := hopfRestriction (j ≫ e.inv)
  have ht : spectrumOfHopfHom t = j ≫ e.inv := hopfRestriction_spec _
  have hj : spectrumOfHopfHom t ≫ e.hom = j := by rw [ht, Category.assoc, e.inv_hom_id, Category.comp_id]
  haveI : IsIso e.inv.hom.hom.left := (Over.forget _).map_isIso e.inv.hom.hom
  haveI : IsIso e.hom.hom.hom.left := (Over.forget _).map_isIso e.hom.hom.hom
  haveI : IsClosedImmersion e.inv.hom.hom.left := inferInstance
  have tSurj : Function.Surjective t :=
    hopfRestriction_surj _ (by
      change IsClosedImmersion (j.hom.hom.left ≫ e.inv.hom.hom.left)
      letI := hClosed
      infer_instance)
  have hEq := Over.w e.hom.hom.hom
  have fPres : Algebra.FinitePresentation IntegralRing A := spectrum_finitePresentation
    (by
      rw [← hEq]
      letI := hFP
      infer_instance)
  have sm : Smooth (HopfSpectrum IntegralRing A).X.hom := by
    rw [← hEq]
    letI := hSmooth
    exact smooth_comp _ _
  have data (k : Type) [Field k] [IsAlgClosed k] [Algebra IntegralRing k] :
      IntegralRecognition.HasFibreDatum D t k := by
    obtain ⟨Q, eK, sK, E, d, hjK, hmon⟩ := hFibre k
    let F := groupChange IntegralRing k
    let eg := (fibreGroupIso k A).symm ≪≫ F.mapIso e ≪≫ eK
    let et := (fibreGroupIso k (CharacterRing D)).symm ≪≫ sK
    refine ⟨Q, eg, et, E, d, ?_, ?_⟩
    · change spectrumOfHopfHom (Bialgebra.TensorProduct.map (BialgHom.id k k) t) ≫
        ((fibreGroupIso k A).inv ≫ (F.map e.hom ≫ eK.hom)) =
          ((fibreGroupIso k (CharacterRing D)).inv ≫ sK.hom) ≫ Q.T.inclusion
      rw [← Category.assoc, ← Category.assoc, ← fibreGroupIso_natural]
      calc
        _ = (fibreGroupIso k (CharacterRing D)).inv ≫ F.map (spectrumOfHopfHom t ≫ e.hom) ≫ eK.hom := by
          simp only [F, Category.assoc, Functor.map_comp]
        _ = _ := by
          simp only [F, hj, Category.assoc, hjK]
    · intro x
      let χ := Additive.toMul (d.val.weightEquiv x)
      let B := k ⊗[IntegralRing] CharacterRing D
      have v := characterValue_spectrum (A := B) (B := B) (et.hom ≫ χ) (AlgHom.id k B)
      have hv : spectrumOfAlgHom (AlgHom.id k B) =
          𝟙 ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k B))) := by
        change (algSpec (CommRingCat.of k)).map (𝟙 (op (CommAlgCat.of k B))) = _
        exact (algSpec (CommRingCat.of k)).map_id _
      rw [hv] at v
      have hpt : (𝟙 (HopfSpectrum k B).X) ≫ (et.hom ≫ χ).hom.hom =
          (mappedUniversalTorus D k sK) ≫ χ.hom.hom := by
        rw [Category.id_comp, Grp.comp_hom_hom]
        rfl
      let alg := algSpec (CommRingCat.of k)
      let L := MonoidAlgebra k DiagonalizableGroups.IntegerCharacters.{0}
      let evMonomial (p : alg.obj (op (CommAlgCat.of k B)) ⟶ alg.obj (op (CommAlgCat.of k L))) : B :=
        ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage p).unop.hom
          (MonoidAlgebra.single DiagonalizableGroups.integerGenerator 1)
      have ev : characterValue (et.hom ≫ χ) (torusTest D k) (𝟙 (HopfSpectrum k B).X) =
          characterValue χ (torusTest D k) (mappedUniversalTorus D k sK) :=
        congrArg evMonomial hpt
      exact v.symm.trans (ev.trans (hmon x))
  let K := AlgebraicClosure ℚ
  letI : Algebra IntegralRing K := IntegralSemisimpleModel.integerAlgebra K
  have line (i : ↥D.base.support) :
      Module.finrank K (Specs.IntegralAlbertRootPins.WeightSpace t
        (Multiplicative.ofAdd (D.datum.root i.val)) K) = 1 := by
    obtain ⟨Q, e, s, E, d, ht, hχ⟩ := data K
    letI := E.comm
    let r := d.val.indexEquiv i.val
    have hr : Additive.toMul (d.val.weightEquiv (D.datum.root i.val)) = r.val := by
      have h := d.val.toHom.root_weightMap_apply D.datum E.datum.rootDatum i.val
      change d.val.weightEquiv (D.datum.root i.val) = E.datum.rootDatum.root r at h
      have h := h.trans (E.datum.root_eq r)
      exact congrArg Additive.toMul h
    apply weight_Finrank t fPres sm tSurj _ Q.reductive Q.T Q.split Q.maximal r.val r.property e s ht
    rw [← hr]
    exact hχ _
  obtain ⟨p, hp⟩ := IntegralAlbertRootPins.simpleRootPins t fPres sm tSurj K line
  exact ⟨{ A := A
           ring := rA
           hopf := hA
           finitePresentation := fPres
           smooth := sm
           torus := t
           torus_surjective := tSurj
           fibreDatum := data
           pin := p
           pin_basis := hp }, e, hj⟩


end
end LinearAlgebraicGroups.Albert.AutomorphismType

namespace LinearAlgebraicGroups.Albert.AutomorphismType

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open LinearAlgebraicGroups.Specs AutomorphismTypeSpecification
open IntegralCentralQuotient (IntegralRing HopfSpectrum spectrumOfHopfHom)
open Specs.IntegralSemisimpleModel (splitTorus integerAlgebra)
open SpinWeights (CharacterExponents evaluate)
open SplitFrameTorusSpecification (CharacterGroup diagonalTorus)
open CharacterDescent (Character)
open CharacterPairing (characterValue)
open Specs.AdjointRepresentation (GroupPoints)
open IntegralSmoothnessSpecification (SplitGroup algebraicFiber)
open ShortDirectionSpecification (IntegralPresentation)
open Specs.GeometricRadicals (IsReductive)
open scoped TensorProduct

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
set_option maxHeartbeats 680000

open private fibreGroupIso fibreSpecIso_inv_fst
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRelativeCell

local instance (priority := 2000) comparisonIntegralModule {A : Type} [CommRing A]
    [Algebra IntegralRing A] : Module IntegralRing A := Algebra.toModule

private abbrev fromIntegers := groupChange ℤ IntegralRing.{0}

private def frameTorusOverLift :
    splitTorus f4Datum ≅ fromIntegers.obj SplitFrameTorusSpecification.diagonalTorus :=
  groupAlgebraSchemeChange ℤ IntegralRing CharacterGroup

private def frameInclusionOverLift {P : IntegralPresentation} {G : SplitGroup P} (T : FrameTorus G) :
    splitTorus f4Datum ⟶ fromIntegers.obj G.group :=
  frameTorusOverLift.hom ≫ fromIntegers.map T.inclusion

private theorem changeFromIntegers_comp (k : Type) [CommRing k] [Algebra IntegralRing k] :
    Spec.map (CommRingCat.ofHom (algebraMap IntegralRing k)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℤ IntegralRing)) =
        Spec.map (CommRingCat.ofHom (algebraMap ℤ k)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext n
  simp

private def fibreTower (k : Type) [CommRing k] [Algebra IntegralRing k] :
    groupChange ℤ k ≅ fromIntegers ⋙ groupChange IntegralRing k :=
  pullbackGroupComp _ _ _ (changeFromIntegers_comp k)

private theorem frameInclusionOverLift_closed {P : IntegralPresentation} {G : SplitGroup P} (T : FrameTorus G) :
    IsClosedImmersion (frameInclusionOverLift T).hom.hom.left := by
  letI : IsIso frameTorusOverLift.hom.hom.hom.left :=
    (Over.forget _).map_isIso frameTorusOverLift.hom.hom.hom
  haveI : IsClosedImmersion frameTorusOverLift.hom.hom.hom.left := inferInstance
  haveI := changeMap_closed (S := IntegralRing) T.inclusion T.closed
  change IsClosedImmersion
    (frameTorusOverLift.hom.hom.hom.left ≫ (fromIntegers.map T.inclusion).hom.hom.left)
  infer_instance

private def groupAlgebraProjection (R S K M : Type) [CommRing R] [CommRing S] [CommRing K]
    [Algebra R S] [Algebra S K] [CommGroup M] :
    MonoidAlgebra R M →+* K ⊗[S] MonoidAlgebra S M :=
  let inc : MonoidAlgebra S M →ₐ[S] K ⊗[S] MonoidAlgebra S M := Algebra.TensorProduct.includeRight
  let c : MonoidAlgebra R M →ₐ[R] S ⊗[R] MonoidAlgebra R M := Algebra.TensorProduct.includeRight
  let e := groupAlgebraChange R S M
  inc.toRingHom.comp (e.toAlgEquiv.toAlgHom.toRingHom.comp c.toRingHom)

private theorem groupAlgebraProjection_of (R S K M : Type) [CommRing R] [CommRing S] [CommRing K]
    [Algebra R S] [Algebra S K] [CommGroup M] (m : M) :
    groupAlgebraProjection R S K M (MonoidAlgebra.of R M m) =
      (1 : K) ⊗ₜ[S] MonoidAlgebra.of S M m := by
  let e := MonoidAlgebra.scalarTensorEquiv R S (M := M)
  have he : e ((1 : S) ⊗ₜ[R] MonoidAlgebra.single m 1) = MonoidAlgebra.single m 1 := by
    apply e.symm.injective
    rw [AlgEquiv.symm_apply_apply, MonoidAlgebra.scalarTensorEquiv_symm_single]
  change (1 : K) ⊗ₜ[S] e ((1 : S) ⊗ₜ[R] MonoidAlgebra.single m 1) =
    (1 : K) ⊗ₜ[S] MonoidAlgebra.single m 1
  rw [he]

private theorem pullbackGroupComp_map_fst {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (he : f ≫ g = h) {T : Grp (Over Y)} {G : Grp (Over Z)}
    (u : T ⟶ (Over.pullback g).mapGrp.obj G) :
    (((Over.pullback f).mapGrp.map u) ≫ (pullbackGroupComp f g h he).inv.app G).hom.hom.left ≫
      pullback.fst G.X.hom h =
      pullback.fst T.X.hom f ≫ u.hom.hom.left ≫ pullback.fst G.X.hom g := by
  rw [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
    pullbackGroupComp_inv_fst f g h he]
  rw [← Category.assoc, ← Category.assoc]
  change ((Over.pullback f).map u.hom.hom).left ≫ pullback.fst _ _ ≫
    pullback.fst G.X.hom g = _
  simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst_assoc]

private def groupAlgebraTowerIso (R S K M : Type) [CommRing R] [CommRing S] [Field K]
    [Algebra R S] [Algebra S K] [Algebra R K] [CommGroup M]
    (h : Spec.map (CommRingCat.ofHom (algebraMap S K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    (groupChange S K).obj (HopfSpectrum S (MonoidAlgebra S M)) ≅
      (groupChange R K).obj (HopfSpectrum R (MonoidAlgebra R M)) :=
  (groupChange S K).mapIso (groupAlgebraSchemeChange R S M) ≪≫
    (pullbackGroupComp _ _ _ h).symm.app _

private theorem groupAlgebraTowerIso_fst (R S K M : Type) [CommRing R] [CommRing S] [Field K]
    [Algebra R S] [Algebra S K] [Algebra R K] [CommGroup M]
    (h : Spec.map (CommRingCat.ofHom (algebraMap S K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    let H := HopfSpectrum R (MonoidAlgebra R M)
    let T := HopfSpectrum S (MonoidAlgebra S M)
    (groupAlgebraTowerIso R S K M h).hom.hom.hom.left ≫
      pullback.fst H.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      pullback.fst T.X.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))) ≫
        Spec.map (CommRingCat.ofHom ((groupAlgebraChange R S M).toAlgEquiv.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight : MonoidAlgebra R M →ₐ[R] S ⊗[R] MonoidAlgebra R M).toRingHom)) := by
  dsimp only
  have h₁ := pullbackGroupComp_map_fst _ _ _ h (groupAlgebraSchemeChange R S M).hom
  have h₂ := groupAlgebraSchemeChange_fst R S M
  exact h₁.trans (congrArg (fun g => pullback.fst
    (HopfSpectrum S (MonoidAlgebra S M)).X.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))) ≫ g) h₂)

private abbrev fibreFrameTorus (k : Type) [Field k] [Algebra IntegralRing k] :
    (groupChange IntegralRing k).obj (splitTorus f4Datum) ≅
      (groupChange ℤ k).obj SplitFrameTorusSpecification.diagonalTorus :=
  groupAlgebraTowerIso ℤ IntegralRing k CharacterGroup (changeFromIntegers_comp k)

private theorem calibratedValue_of_projection {P : IntegralPresentation} {G : SplitGroup P}
    {T : FrameTorus G} {k : Type} [Field k]
    (C : SplitAlbertAdjointWeightsSpecification.FibreCalibration T k)
    (S : TestAlgebra k) (z : GroupPoints (T.fibre k).group S)
    (a : SplitFrameTorusSpecification.LaurentRing →ₐ[ℤ] S)
    (h : z.left ≫ pullback.fst SplitFrameTorusSpecification.diagonalTorus.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) =
      Spec.map (CommRingCat.ofHom a.toRingHom))
    (χ : CharacterDescent.Character (T.fibre k).group) :
    characterValue χ S z = a (SplitFrameTorusSpecification.monomial (C.characters (Additive.ofMul χ))) := by
  obtain ⟨q, hq, hz⟩ := C.projection S z
  have eq : q = (algSpec (CommRingCat.of ℤ)).map (CommAlgCat.ofHom a).op :=
    Over.OverMorphism.ext (hq.trans (by rw [algSpec_map_left]; exact h))
  have he := C.evaluation S z χ
  rw [hz, eq] at he
  exact he.trans (T.characters (CommAlgCat.of ℤ S) a _)


private theorem calibratedCoordinateValue {P : IntegralPresentation} {G : SplitGroup P}
    {T : FrameTorus G} {k : Type} [Field k]
    (C : SplitAlbertAdjointWeightsSpecification.FibreCalibration T k)
    (S : TestAlgebra k) (z : GroupPoints (T.fibre k).group S)
    (a : SplitFrameTorusSpecification.LaurentRing →ₐ[ℤ] S)
    (h : z.left ≫ pullback.fst diagonalTorus.X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) =
      Spec.map (CommRingCat.ofHom a.toRingHom))
    (x : CharacterExponents) :
    characterValue (Additive.toMul (C.characters.symm x)) S z =
      a (SplitFrameTorusSpecification.monomial x) := by
  have h' := calibratedValue_of_projection C S z a h (Additive.toMul (C.characters.symm x))
  change _ = a (SplitFrameTorusSpecification.monomial (C.characters (C.characters.symm x))) at h'
  rwa [C.characters.apply_symm_apply] at h'

private theorem calibratedCoordinateValue_of_ringHom {P : IntegralPresentation} {G : SplitGroup P}
    {T : FrameTorus G} {k : Type} [Field k]
    (C : SplitAlbertAdjointWeightsSpecification.FibreCalibration T k)
    (B : TestAlgebra k) (z : GroupPoints (T.fibre k).group B)
    (a : SplitFrameTorusSpecification.LaurentRing →+* B)
    (h : z.left ≫ pullback.fst diagonalTorus.X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) =
      Spec.map (CommRingCat.ofHom a))
    (x : CharacterExponents) :
    characterValue (Additive.toMul (C.characters.symm x)) B z = a (SplitFrameTorusSpecification.monomial x) :=
  calibratedCoordinateValue C B z a.toIntAlgHom h x

/-- The Laurent-coordinate map for the projection of a specified fibre point. -/
private structure FramePointCoordinates (k : Type) [Field k] (B : TestAlgebra k)
    (point : GroupPoints ((groupChange ℤ k).obj diagonalTorus) B) where
  coordinates : SplitFrameTorusSpecification.LaurentRing →+* B
  projection : point.left ≫ pullback.fst diagonalTorus.X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) =
      Spec.map (CommRingCat.ofHom coordinates)

private abbrev towerPoint (S k : Type) [CommRing S] [Field k] [Algebra S k]
    (tower : Spec.map (CommRingCat.ofHom (algebraMap S k)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℤ S)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) :=
  mapGroupAlgebraPoint S k CharacterGroup (groupAlgebraTowerIso ℤ S k CharacterGroup tower)

private def towerFrameCoordinates (S k : Type) [CommRing S] [Field k] [Algebra S k]
    (tower : Spec.map (CommRingCat.ofHom (algebraMap S k)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℤ S)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) :
    FramePointCoordinates k (groupAlgebraTest S k CharacterGroup) (towerPoint S k tower) where
  coordinates := groupAlgebraProjection ℤ S k CharacterGroup
  projection := by
    change (universalGroupAlgebraPoint S k CharacterGroup ≫ _).left ≫ _ = _
    rw [Over.comp_left, Category.assoc, groupAlgebraTowerIso_fst, ← Category.assoc]
    have h₁ := fibreSpecIso_inv_fst (R := S) k (MonoidAlgebra S CharacterGroup)
    have he : (fibreGroupIso k (R := S) (MonoidAlgebra S CharacterGroup)).inv.hom.hom.left ≫
        pullback.fst (HopfSpectrum S (MonoidAlgebra S CharacterGroup)).X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap S k))) = _ := h₁
    rw [he, ← Spec.map_comp]
    rfl

private theorem framePoint_evaluation {P : IntegralPresentation} {G : SplitGroup P} {T : FrameTorus G}
    {k : Type} [Field k] (C : SplitAlbertAdjointWeightsSpecification.FibreCalibration T k)
    {B : TestAlgebra k} {point} (f : FramePointCoordinates k B point) (x : CharacterExponents) :
    characterValue (Additive.toMul (C.characters.symm x)) B point =
      f.coordinates (SplitFrameTorusSpecification.monomial x) :=
  calibratedCoordinateValue_of_ringHom C B point f.coordinates f.projection x

private theorem towerFrameCoordinates_value (S k : Type) [CommRing S] [Field k] [Algebra S k]
    (tower : Spec.map (CommRingCat.ofHom (algebraMap S k)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℤ S)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) (x : CharacterExponents) :
    (towerFrameCoordinates S k tower).coordinates (SplitFrameTorusSpecification.monomial x) =
      groupAlgebraMonomial S k CharacterGroup (Multiplicative.ofAdd x) :=
  groupAlgebraProjection_of ℤ S k CharacterGroup (Multiplicative.ofAdd x)

/-- The calibrated character on the universal point is the corresponding
monomial in the base-changed group algebra. -/
private theorem frameMonomialGeneric {P : IntegralPresentation} {G : SplitGroup P} {T : FrameTorus G}
    (S k : Type) [CommRing S] [Field k] [Algebra S k]
    (tower : Spec.map (CommRingCat.ofHom (algebraMap S k)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℤ S)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))
    (C : SplitAlbertAdjointWeightsSpecification.FibreCalibration T k) (x : CharacterExponents) :
    characterValue (Additive.toMul (C.characters.symm x)) (groupAlgebraTest S k CharacterGroup)
      (towerPoint S k tower) =
      groupAlgebraMonomial S k CharacterGroup (Multiplicative.ofAdd x) :=
  (framePoint_evaluation C (towerFrameCoordinates S k tower) x).trans (towerFrameCoordinates_value S k tower x)

set_option maxHeartbeats 50000 in
private theorem frameMonomialAtUniversal {P : IntegralPresentation} {G : SplitGroup P}
    {T : FrameTorus G} (k : Type) [Field k] [Algebra IntegralRing k]
    (C : SplitAlbertAdjointWeightsSpecification.FibreCalibration T k) (x : f4Datum.X) :
    characterValue (Additive.toMul (C.characters.symm x)) (torusTest f4Datum k)
      (mappedUniversalTorus f4Datum k (fibreFrameTorus k)) = torusMonomial f4Datum k x :=
  frameMonomialGeneric IntegralRing k (changeFromIntegers_comp k) C x

private theorem baseChange_torus_square {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {H : D ⥤ E} {L : C ⥤ E} (n : L ≅ F ⋙ H)
    {X Y : C} {T : D} (a : X ⟶ Y) (t : T ≅ F.obj X) :
    H.map (t.hom ≫ F.map a) ≫ (n.symm.app Y).hom =
      (H.mapIso t ≪≫ n.symm.app X).hom ≫ L.map a := by
  have h := n.inv.naturality a
  change H.map (F.map a) ≫ (n.symm.app Y).hom = (n.symm.app X).hom ≫ L.map a at h
  simp only [Functor.map_comp, Category.assoc, h, Iso.trans_hom, Functor.mapIso_hom]

private theorem frameFibre_inclusion {P : IntegralPresentation} {G : SplitGroup P} (T : FrameTorus G)
    (k : Type) [Field k] [Algebra IntegralRing k] :
    (groupChange IntegralRing k).map (frameInclusionOverLift T) ≫ ((fibreTower k).symm.app G.group).hom =
      (fibreFrameTorus k).hom ≫ (T.fibre k).inclusion :=
  baseChange_torus_square (F := fromIntegers) (H := groupChange IntegralRing k)
    (L := groupChange ℤ k) (fibreTower k) T.inclusion frameTorusOverLift

private theorem markedOneFibre_of_basis {D : Pinning.BasedRootDatum.{0}}
    {H : IntegralGroup} (j : splitTorus D ⟶ H)
    (k : Type) [Field k] [Algebra IntegralRing k]
    (A : AffineAlgebraicGroup k) (T : ClosedSubgroup A.val)
    (hA : IsReductive A) (hS : GeometricRadicals.IsSplitTorus T.group)
    (hM : RankOneFlag.IsGeometricallyMaximal T)
    (e : (groupChange IntegralRing k).obj H ≅ A.val)
    (s : (groupChange IntegralRing k).obj (splitTorus D) ≅ T.group)
    (hT : (groupChange IntegralRing k).map j ≫ e.hom = s.hom ≫ T.inclusion)
    (C : Additive (Character T.group) ≃ₗ[ℤ] D.X)
    (hMon : ∀ x : D.X, characterValue (Additive.toMul (C.symm x)) (torusTest D k)
      (mappedUniversalTorus D k s) =
      torusMonomial D k x)
    (hBased : ∃ (B : ClosedSubgroup A.val) (hB : GeometricBorelConjugacy.IsKBorel B)
        (hTB : SchemeDerivedGroup.IsSubgroupOf T B),
        let Q : Pinning.SplitBorelPair k := ⟨A, hA, T, hS, hM, B, hB, hTB⟩
        ∃ (E : Pinning.AttachedDatum Q) (d : Pinning.BasedIso D E.toBased),
          ∀ x : D.X, Additive.toMul (d.val.weightEquiv x) = Additive.toMul (C.symm x)) :
    MarkedOneFibre j k := by
  obtain ⟨B, hB, hTB, E, d, hd⟩ := hBased
  let Q : Pinning.SplitBorelPair k := ⟨A, hA, T, hS, hM, B, hB, hTB⟩
  refine ⟨Q, e, s, E, d, hT, fun x => ?_⟩
  let ev (χ : Character T.group) :=
    characterValue χ (torusTest D k) (mappedUniversalTorus D k s)
  exact (congrArg ev (hd x)).trans (hMon x)

set_option maxHeartbeats 50000 in
private theorem albert_markedOneFibre {P : IntegralPresentation} {G : SplitGroup P} (T : FrameTorus G)
    (k : Type) [Field k] [IsAlgClosed k] [Algebra IntegralRing k]
    (hG : IsReductive (algebraicFiber G k))
    (hW : SplitAlbertAdjointWeightsSpecification.FibreWeights T k) :
    MarkedOneFibre (frameInclusionOverLift T) k := by
  let A := algebraicFiber G k
  let T' : ClosedSubgroup A.val := T.fibre k
  obtain ⟨hS, hM, C, hRoots⟩ := hW
  rw [adjointRootSet] at hRoots
  exact markedOneFibre_of_basis (frameInclusionOverLift T) k A T' hG hS hM
    ((fibreTower k).symm.app G.group) (fibreFrameTorus k) (frameFibre_inclusion T k)
    C.characters (frameMonomialAtUniversal k C)
    (calibratedBasedFibre A hG T' hS hM C.characters hRoots)

private theorem albert_markedFibres {P : IntegralPresentation} {G : SplitGroup P}
    (T : FrameTorus G)
    (hG : ∀ (k : Type) [Field k] [IsAlgClosed k], IsReductive (algebraicFiber G k))
    (hW : ∀ (k : Type) [Field k] [IsAlgClosed k],
      SplitAlbertAdjointWeightsSpecification.FibreWeights T k) :
    MarkedFibres (frameInclusionOverLift T) :=
  fun k _ _ _ => albert_markedOneFibre T k (hG k) (hW k)

private def roundTrip :
    𝟭 (SpinSpecification.GroupScheme ℤ) ≅ fromIntegers ⋙ chevalleyChange ℤ := by
  letI : Algebra IntegralRing ℤ := integerAlgebra ℤ
  have h : (algebraMap ℤ ℤ : ℤ →+* ℤ) = RingHom.id ℤ := by ext; simp
  let p := (Functor.mapGrpIdIso (C := Over (Spec (CommRingCat.of ℤ)))).symm ≪≫
    (Functor.mapGrpNatIso (Over.pullbackId (X := Spec (CommRingCat.of ℤ)))).symm
  let q := eqToIso (congrArg (fun m : Spec (CommRingCat.of ℤ) ⟶ Spec (CommRingCat.of ℤ) =>
    (Over.pullback m).mapGrp) (show 𝟙 _ = Spec.map (CommRingCat.ofHom (algebraMap ℤ ℤ)) by
      rw [h, CommRingCat.ofHom_id, Spec.map_id]))
  exact p ≪≫ q ≪≫ fibreTower ℤ

private theorem integralComparison {P : IntegralPresentation} {G : SplitGroup P}
    (T : FrameTorus G) (hSmooth : Smooth G.group.X.hom)
    (hMark : MarkedFibres (frameInclusionOverLift T))
    (C : IntegralSemisimpleModel.Model f4Datum) :
    ∃ (e : G.group ≅ (chevalleyChange ℤ).obj C.group)
      (t : SplitFrameTorusSpecification.diagonalTorus ≅ (chevalleyChange ℤ).obj (splitTorus f4Datum)),
      T.inclusion ≫ e.hom = t.hom ≫ (chevalleyChange ℤ).map C.torus := by
  let H := fromIntegers.obj G.group
  haveI := G.affine
  haveI := G.finitePresentation
  haveI := hSmooth
  have hA : IsAffine H.X.left := by
    change IsAffine (pullback G.group.X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℤ IntegralRing))))
    infer_instance
  have hFP : LocallyOfFinitePresentation H.X.hom := by
    change LocallyOfFinitePresentation (pullback.snd G.group.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ IntegralRing))))
    infer_instance
  have hS : Smooth H.X.hom := by
    change Smooth (pullback.snd G.group.X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℤ IntegralRing))))
    infer_instance
  obtain ⟨U, eU, hU⟩ := recognition_of_markedGroup H (frameInclusionOverLift T) hA hFP hS
    (frameInclusionOverLift_closed T) hMark
  obtain ⟨V, eV, hV⟩ := recognition_of_markedGroup C.group C.torus C.affine
    C.locallyOfFinitePresentation C.smooth C.torusClosed (chevalley_markedFibres C)
  let d : Pinning.BasedIso f4Datum f4Datum := ⟨RootPairing.Equiv.id f4Datum.datum, by simp⟩
  obtain ⟨f, hf, _⟩ := Classification.IntegralRecognition.pinnedIsomorphisms U V d
  have hT : U.torus.comp f.toBialgHom = V.torus := by
    have hf := hf.1
    have hd : d.val.weightEquiv = LinearEquiv.refl ℤ f4Datum.X := by
      apply LinearEquiv.ext
      intro x
      rfl
    have hd' : d.val.weightEquiv.symm.toAddEquiv.toAddMonoidHom.toMultiplicative =
        MonoidHom.id (Multiplicative f4Datum.X) := by
      rw [hd]
      rfl
    change U.torus.comp f.toBialgHom = (MonoidAlgebra.mapDomainBialgHom IntegralRing
      d.val.weightEquiv.symm.toAddEquiv.toAddMonoidHom.toMultiplicative).comp V.torus at hf
    rwa [hd', MonoidAlgebra.mapDomainBialgHom_id, BialgHom.id_comp] at hf
  let i : H ≅ C.group := eU.symm ≪≫ hopfIso f ≪≫ eV
  have hi : frameInclusionOverLift T ≫ i.hom = C.torus := by
    rw [← hU]
    change (spectrumOfHopfHom U.torus ≫ eU.hom) ≫
      (eU.inv ≫ ((hopfIso f).hom ≫ eV.hom)) = _
    rw [Category.assoc, eU.hom_inv_id_assoc, ← Category.assoc, ← hV]
    change ((hopfSpec (CommRingCat.of IntegralRing)).map (CommHopfAlgCat.ofHom U.torus).op ≫
      (hopfSpec (CommRingCat.of IntegralRing)).map (CommHopfAlgCat.ofHom f.toBialgHom).op) ≫ _ = _
    rw [← Functor.map_comp]
    exact congrArg (fun g => spectrumOfHopfHom g ≫ eV.hom) hT
  let F := chevalleyChange ℤ
  let e := roundTrip.app G.group ≪≫ F.mapIso i
  let t := roundTrip.app SplitFrameTorusSpecification.diagonalTorus ≪≫ F.mapIso frameTorusOverLift.symm
  refine ⟨e, t, ?_⟩
  have hj : (fromIntegers.map T.inclusion) ≫ i.hom = frameTorusOverLift.inv ≫ C.torus := by
    rw [← hi]
    change _ = frameTorusOverLift.inv ≫ (frameTorusOverLift.hom ≫ fromIntegers.map T.inclusion) ≫ i.hom
    rw [← Category.assoc, frameTorusOverLift.inv_hom_id_assoc]
  have hn := roundTrip.hom.naturality T.inclusion
  change T.inclusion ≫ (roundTrip.app G.group).hom =
    (roundTrip.app SplitFrameTorusSpecification.diagonalTorus).hom ≫ F.map (fromIntegers.map T.inclusion) at hn
  change _ ≫ (_ ≫ F.map i.hom) = (_ ≫ F.map frameTorusOverLift.inv) ≫ F.map C.torus
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp, hj, F.map_comp, Category.assoc]

/-- The smooth adjoint Albert group is an arbitrary faithfully flat form of the
split Chevalley group with the specified integral frame torus. -/
theorem automorphismType : Statement := by
  obtain ⟨P, G, hS, hC, hG⟩ := IntegralSmoothness.integralGeometry
  obtain ⟨T, hT, hW, hCentre⟩ := SplitAlbertAdjointWeights.splitAlbertAdjointWeights P G hG
  obtain ⟨C⟩ := Classification.IntegralRealization.integralRealization f4Datum
  have hRoots k [Field k] [IsAlgClosed k] := (hW k).1
  letI := hS
  obtain ⟨e, t, ht⟩ := integralComparison T (SmoothOfRelativeDimension.smooth 52 G.group.X.hom)
    (albert_markedFibres T hG hRoots) C
  have coord : DatumCoordinates f4Datum :=
    { characters := LinearEquiv.refl ℤ _
      cocharacters := LinearEquiv.refl ℤ _
      roots := Equiv.refl _
      root_eq := fun _ => rfl
      coroot_eq := fun _ => rfl
      pair_eq := integralPairing_apply
      simple_eq := fun i => by
        change i ∈ (simpleSupport : Set RootIndex) ↔ i ∈ Set.range simpleIndex
        rw [simpleSupport_coe] }
  let L : IntegralSplitIdentification :=
    ⟨f4Datum, coord, C, P, G, T, hT, e, t, ht, hS, hC,
      fibreRoots_of_weights T hG hRoots, fun k _ _ => (hW k).2⟩
  exact ⟨L, forms_of_identification L hCentre⟩


end
end LinearAlgebraicGroups.Albert.AutomorphismType
