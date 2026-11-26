import Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianRelativeRoots
import LinearAlgebraicGroups.Arithmetic.TrialitarianFixedRootSL2
import LinearAlgebraicGroups.Arithmetic.TrialitarianPinnedBorelPair
import LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
import LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
import LinearAlgebraicGroups.Classification.RankOneRelations
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.TrialitarianRelativeRoots

open LinearAlgebraicGroups.Specs.AbsoluteDynkinTypes (D4Cartan)
open LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianRelativeRoots
  (project positiveCoordinates longCoordinates)
open scoped Matrix

/-- The positive absolute roots of D₄ in simple-root coefficients, with
the central vertex numbered 1. -/
private def positiveD4 (i : Fin 12) : Fin 4 → ℤ :=
  ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1],
    ![1, 1, 0, 0], ![0, 1, 1, 0], ![0, 1, 0, 1],
    ![1, 1, 1, 0], ![1, 1, 0, 1], ![0, 1, 1, 1], ![1, 1, 1, 1], ![1, 2, 1, 1]] i

private def signedD4 (j : Fin 12 × Bool) : Fin 4 → ℤ :=
  if j.2 then positiveD4 j.1 else -positiveD4 j.1

/-- The simple reflection on coefficients in the simple-root basis. -/
private def reflectD4 (i : Fin 4) (c : Fin 4 → ℤ) : Fin 4 → ℤ :=
  c - (∑ j, c j * D4Cartan i j) • Pi.single i 1

private theorem reflect_signed (i : Fin 4) (j : Fin 12 × Bool) :
    ∃ k, signedD4 k = reflectD4 i (signedD4 j) := by
  have h : ∀ (a : Fin 4) (b : Fin 12 × Bool),
      ∃ k, signedD4 k = reflectD4 a (signedD4 b) := by decide +kernel
  exact h i j

private theorem signed_injective : Function.Injective signedD4 := by
  have h : ∀ a b : Fin 12 × Bool, signedD4 a = signedD4 b → a = b := by decide +kernel
  exact h

private theorem negative_signed (j : Fin 12 × Bool) :
    signedD4 (j.1, !j.2) = -signedD4 j := by
  rcases j with ⟨i, b⟩
  cases b <;> simp [signedD4]

/-- Paths to the positive roots by simple reflections, starting at the
specified simple vertex and applying the list from left to right. -/
private def positivePath (i : Fin 12) : Fin 4 × List (Fin 4) :=
  ![(0, []), (1, []), (2, []), (3, []), (1, [0]), (1, [2]), (1, [3]),
    (1, [0, 2]), (1, [0, 3]), (1, [2, 3]), (1, [0, 2, 3]), (1, [0, 2, 3, 1])] i

private theorem path_eq (i : Fin 12) :
    (positivePath i).2.foldl (fun c j ↦ reflectD4 j c) (Pi.single (positivePath i).1 1)
      = positiveD4 i := by
  have h : ∀ k : Fin 12,
      (positivePath k).2.foldl (fun c j ↦ reflectD4 j c) (Pi.single (positivePath k).1 1)
        = positiveD4 k := by decide +kernel
  exact h i

private theorem simple_signed (i : Fin 4) : signedD4 (i.castLE (by decide), true) = Pi.single i 1 := by
  have h : ∀ j : Fin 4, signedD4 (j.castLE (by decide), true) = Pi.single j 1 := by decide +kernel
  exact h i

section RootPairing

variable {I X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootPairing I ℤ X Y) (B : P.Base)
  (simple : Fin 4 ≃ B.support)
  (cartan : ∀ i j, P.pairing (simple j).val (simple i).val = D4Cartan i j)

private def expand (c : Fin 4 → ℤ) : X :=
  ∑ i, c i • P.root (simple i).val

private theorem expand_injective : Function.Injective (expand P B simple) :=
  fun _ _ h ↦ funext (Fintype.linearIndependent_iffₛ.mp
    (B.linearIndepOn_root.linearIndependent.comp simple simple.injective) _ _ h)

private theorem expand_single (i : Fin 4) :
    expand P B simple (Pi.single i 1) = P.root (simple i).val := by
  simp [expand, Pi.single_apply, Finset.sum_ite_eq']

private theorem expand_neg (c : Fin 4 → ℤ) :
    expand P B simple (-c) = -expand P B simple c := by
  simp [expand, Finset.sum_neg_distrib]

include cartan in
private theorem expand_reflect (i : Fin 4) (a : I) (c : Fin 4 → ℤ)
    (h : expand P B simple c = P.root a) :
    expand P B simple (reflectD4 i c) = P.root (P.reflectionPerm (simple i).val a) := by
  have hs (b : ℤ) : expand P B simple (c - b • Pi.single i 1) =
      expand P B simple c - b • expand P B simple (Pi.single i 1) := by
    simp only [expand, Pi.sub_apply, Pi.smul_apply, sub_smul, smul_assoc,
      Finset.sum_sub_distrib, Finset.smul_sum]
  have hp : (P.toLinearMap (P.root a)) (P.coroot (simple i).val) =
      ∑ j, c j * D4Cartan i j := by
    rw [← h]
    simp [expand, RootPairing.root_coroot_eq_pairing, cartan]
  rw [reflectD4, hs, h, expand_single, ← hp, P.reflectionPerm_root]

private theorem root_neg (a : I) : P.root (P.reflectionPerm a a) = -P.root a := by
  rw [← P.reflectionPerm_root, P.root_coroot_eq_pairing, P.pairing_same, two_smul]
  abel

variable [Finite I] [P.IsReduced]

include cartan in
/-- The full D₄ root set is the expansion of the 24 signed coefficient vectors. -/
private theorem root_range_eq :
    Set.range P.root = Set.range (expand P B simple ∘ signedD4) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    apply B.induction_reflect a (p := fun r ↦ P.root r ∈ Set.range (expand P B simple ∘ signedD4))
    · intro r
      rintro ⟨j, hj⟩
      exact ⟨(j.1, !j.2), by
        simpa only [Function.comp_apply, negative_signed, expand_neg, root_neg] using
          congrArg Neg.neg hj⟩
    · intro r hr
      let i := simple.symm ⟨r, hr⟩
      have hi : (simple i).val = r := by simp [i]
      exact ⟨(i.castLE (by decide), true), by
        simp only [Function.comp_apply, simple_signed, expand_single, hi]⟩
    · intro r s
      rintro ⟨j, hj⟩ hs
      let i := simple.symm ⟨s, hs⟩
      have hi : (simple i).val = s := by simp [i]
      obtain ⟨k, hk⟩ := reflect_signed i j
      exact ⟨k, by
        simp only [Function.comp_apply, hk, expand_reflect P B simple cartan i r _ hj, hi]⟩
  · rintro ⟨⟨j, b⟩, rfl⟩
    have applyPath (l : List (Fin 4)) (a : I) (c : Fin 4 → ℤ)
        (hc : expand P B simple c = P.root a) :
        expand P B simple (l.foldl (fun d i ↦ reflectD4 i d) c) ∈ Set.range P.root := by
      induction l generalizing a c with
      | nil => exact ⟨a, hc.symm⟩
      | cons i l ih => exact ih _ _ (expand_reflect P B simple cartan i a c hc)
    let i := (positivePath j).1
    have hpos := applyPath (positivePath j).2 (simple i).val _ (expand_single P B simple i)
    rw [path_eq] at hpos
    obtain ⟨a, ha⟩ := hpos
    cases b
    · exact ⟨P.reflectionPerm a a, by
        simp only [Function.comp_apply, signedD4, Bool.false_eq_true, ↓reduceIte,
          expand_neg, root_neg, ha]⟩
    · exact ⟨a, ha⟩

include cartan in
private noncomputable def signedIndex : I ≃ Fin 12 × Bool := by
  classical
  let f := expand P B simple ∘ signedD4
  have hf : Function.Injective f := (expand_injective P B simple).comp signed_injective
  have h : Set.range P.root = Set.range f := root_range_eq P B simple cartan
  exact (Equiv.ofInjective P.root P.root.injective).trans
    ((Set.equivOfEq h).trans (Equiv.ofInjective f hf).symm)

include cartan in
private theorem signedIndex_expand (a : I) :
    expand P B simple (signedD4 (signedIndex P B simple cartan a)) = P.root a := by
  classical
  let f := expand P B simple ∘ signedD4
  have hf : Function.Injective f := (expand_injective P B simple).comp signed_injective
  exact congrArg Subtype.val ((Equiv.ofInjective f hf).apply_symm_apply
    ((Set.equivOfEq (root_range_eq P B simple cartan)) ⟨P.root a, ⟨a, rfl⟩⟩))

omit [Finite I] [P.IsReduced] in
private theorem height_eq (a : I) (c : Fin 4 → ℤ) (h : expand P B simple c = P.root a) :
    B.height a = ∑ i, c i := by
  classical
  let f (j : I) : ℤ := if h : j ∈ B.support then c (simple.symm ⟨j, h⟩) else 0
  have hf (j : B.support) : f j.val = c (simple.symm j) := dite_eq_left j.property
  have heq : P.root a = ∑ j ∈ B.support, f j • P.root j := by
    rw [Finset.sum_subtype B.support (fun _ ↦ Iff.rfl)]
    rw [← Equiv.sum_comp simple (fun j : B.support ↦ f j.val • P.root j.val)]
    simpa only [hf, Equiv.symm_apply_apply, expand] using h.symm
  rw [B.height_eq_sum heq, Finset.sum_subtype B.support (fun _ ↦ Iff.rfl)]
  rw [← Equiv.sum_comp simple (fun j : B.support ↦ f j.val)]
  simp only [hf, Equiv.symm_apply_apply]

end RootPairing

private theorem positive_signed (j : Fin 12 × Bool) :
    (0 < ∑ i, signedD4 j i) ↔ j.2 = true := by
  have h : ∀ a : Fin 12 × Bool, (0 < ∑ i, signedD4 a i) ↔ a.2 = true := by decide +kernel
  exact h j

private theorem positive_image :
    Set.range (project ∘ positiveD4) = (positiveCoordinates : Set (ℤ × ℤ)) := by
  have h : Finset.univ.image (project ∘ positiveD4) = positiveCoordinates := by decide +kernel
  simpa [Function.comp_def] using congrArg (fun s : Finset (ℤ × ℤ) ↦ (s : Set (ℤ × ℤ))) h

private theorem signed_image :
    Set.range (project ∘ signedD4) =
      (LieAlgebrasAndRepresentations.rankTwoCoefficients .G₂ : Set (ℤ × ℤ)) := by
  have h : Finset.univ.image (project ∘ signedD4) =
      LieAlgebrasAndRepresentations.rankTwoCoefficients .G₂ := by decide +kernel
  simpa [Function.comp_def] using congrArg (fun s : Finset (ℤ × ℤ) ↦ (s : Set (ℤ × ℤ))) h

private theorem signed_nonzero (j : Fin 12 × Bool) : project (signedD4 j) ≠ 0 := by
  have h : ∀ a : Fin 12 × Bool, project (signedD4 a) ≠ 0 := by decide +kernel
  exact h j

private def projectionCount (p : ℤ × ℤ) : ℕ :=
  (Finset.univ.filter fun j : Fin 12 × Bool ↦ project (signedD4 j) = p).card

private theorem card_projection (p : ℤ × ℤ) :
    Nat.card {j : Fin 12 × Bool // project (signedD4 j) = p} = projectionCount p := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

private theorem unique_long_projection (p : ℤ × ℤ) (hp : p ∈ longCoordinates) :
    ∃! j : Fin 12 × Bool, project (signedD4 j) = p := by
  have h : ∀ q : ↥longCoordinates, ∃ j : Fin 12 × Bool,
      project (signedD4 j) = q.val ∧
        ∀ k : Fin 12 × Bool, project (signedD4 k) = q.val → k = j := by decide +kernel
  exact h ⟨p, hp⟩

section RootPairing

variable {I X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Finite I]
  (P : RootPairing I ℤ X Y) [P.IsReduced] (B : P.Base)
  (simple : Fin 4 ≃ B.support)
  (cartan : ∀ i j, P.pairing (simple j).val (simple i).val = D4Cartan i j)

include cartan in
/-- Folding the roots of an integral D₄ datum by the outer orbit and the
central vertex gives the G₂ coordinate set, with the stated fibres. -/
theorem rootCoefficientFolding :
    ∃ coeff : I → Fin 4 → ℤ,
      (∀ a, P.root a = ∑ i, coeff a i • P.root (simple i).val) ∧
      (∀ i, coeff (simple i).val = Pi.single i 1) ∧
      (∀ a, project (coeff a) ≠ 0) ∧
      (fun a ↦ project (coeff a)) '' {a | B.IsPos a} =
        (positiveCoordinates : Set (ℤ × ℤ)) ∧
      Set.range (fun a ↦ project (coeff a)) =
        (LieAlgebrasAndRepresentations.rankTwoCoefficients .G₂ : Set (ℤ × ℤ)) ∧
      Nat.card {a // project (coeff a) = (1, 0)} = 3 ∧
      Nat.card {a // project (coeff a) = (0, 1)} = 1 ∧
      Nat.card {a // project (coeff a) = (1, 1)} = 3 ∧
      Nat.card {a // project (coeff a) = (2, 1)} = 3 ∧
      Nat.card {a // project (coeff a) = (3, 1)} = 1 ∧
      Nat.card {a // project (coeff a) = (3, 2)} = 1 ∧
      (∀ p ∈ longCoordinates, ∃! a, project (coeff a) = p) := by
  classical
  let e := signedIndex P B simple cartan
  let coeff := signedD4 ∘ e
  have he (a : I) : expand P B simple (coeff a) = P.root a :=
    signedIndex_expand P B simple cartan a
  have hpos (a : I) : B.IsPos a ↔ (e a).2 = true := by
    rw [B.isPos_iff, height_eq P B simple a (coeff a) (he a)]
    exact positive_signed (e a)
  have hpositive :
      (fun a ↦ project (coeff a)) '' {a | B.IsPos a} =
        Set.range (project ∘ positiveD4) := by
    ext p
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(e a).1, by simp [coeff, signedD4, (hpos a).mp ha]⟩
    · rintro ⟨j, rfl⟩
      refine ⟨e.symm (j, true), (hpos _).mpr ?_, ?_⟩
      · simp
      · simp [coeff, signedD4]
  have hcard (p : ℤ × ℤ) :
      Nat.card {a // project (coeff a) = p} = projectionCount p :=
    (Nat.card_congr (e.subtypeEquiv (fun _ ↦ Iff.rfl))).trans (card_projection p)
  refine ⟨coeff, fun a ↦ (he a).symm, ?_, fun a ↦ signed_nonzero (e a),
    hpositive.trans positive_image,
    (e.surjective.range_comp (project ∘ signedD4)).trans signed_image,
    (hcard _).trans (by decide +kernel), (hcard _).trans (by decide +kernel),
    (hcard _).trans (by decide +kernel), (hcard _).trans (by decide +kernel),
    (hcard _).trans (by decide +kernel), (hcard _).trans (by decide +kernel), ?_⟩
  · intro i
    exact expand_injective P B simple ((he _).trans (expand_single P B simple i).symm)
  · intro p hp
    obtain ⟨j, hj, hu⟩ := unique_long_projection p hp
    refine ⟨e.symm j, ?_, fun a ha ↦ e.injective ?_⟩
    · simpa [coeff] using hj
    · rw [e.apply_symm_apply]
      exact hu (e a) ha

include B in
/-- A full integral coroot lattice makes each coroot primitive, by
transporting a simple coordinate functional along reflections. -/
theorem corootPrimitive (hspan : Submodule.span ℤ (Set.range P.coroot) = ⊤) (a : I) :
    ∃ f : Y →ₗ[ℤ] ℤ, f (P.coroot a) = 1 := by
  classical
  have hs : Submodule.span ℤ (Set.range (fun i : B.support ↦ P.coroot i.val)) = ⊤ := by
    change Submodule.span ℤ (Set.range (fun i : (↑B.support : Set I) ↦ P.coroot i.val)) = ⊤
    rw [← Set.image_eq_range, B.span_int_coroot_support, hspan]
  let b := Module.Basis.mk B.linearIndepOn_coroot hs.ge
  have hb (i : B.support) : b i = P.coroot i.val := Module.Basis.mk_apply _ _ _
  apply B.induction_reflect a (p := fun r ↦ ∃ f : Y →ₗ[ℤ] ℤ, f (P.coroot r) = 1)
  · rintro r ⟨f, hf⟩
    exact ⟨-f, by simp [hf]⟩
  · intro r hr
    let i : B.support := ⟨r, hr⟩
    exact ⟨b.coord i, by
      change b.coord i (P.coroot i.val) = 1
      rw [← hb]
      simp [Module.Basis.coord]⟩
  · rintro r s ⟨f, hf⟩ _
    exact ⟨f.comp (P.coreflection s).symm.toLinearMap, by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, P.coroot_reflectionPerm,
        LinearEquiv.symm_apply_apply, hf]⟩

/-- The Weyl word consisting of the three outer reflections followed by
the central reflection sends the central simple root to the highest root. -/
def highestRootIndex : I :=
  P.reflectionPerm (simple 1).val
    (P.reflectionPerm (simple 3).val
      (P.reflectionPerm (simple 2).val (P.reflectionPerm (simple 0).val (simple 1).val)))

omit [Finite I] [P.IsReduced] in
include cartan in
theorem highestRootExpansion :
    P.root (highestRootIndex P B simple) =
      P.root (simple 0).val + (2 : ℤ) • P.root (simple 1).val +
      P.root (simple 2).val + P.root (simple 3).val := by
  have h := expand_reflect P B simple cartan 0 _ _ (expand_single P B simple 1)
  have h := expand_reflect P B simple cartan 2 _ _ h
  have h := expand_reflect P B simple cartan 3 _ _ h
  have h := expand_reflect P B simple cartan 1 _ _ h
  change expand P B simple ((positivePath 11).2.foldl (fun c j ↦ reflectD4 j c)
    (Pi.single (positivePath 11).1 1)) = P.root (highestRootIndex P B simple) at h
  rw [path_eq] at h
  rw [← h]
  simp [expand, positiveD4, Fin.sum_univ_four]

omit [Finite I] [P.IsReduced] in
include cartan in
theorem highestCorootExpansion :
    P.coroot (highestRootIndex P B simple) =
      P.coroot (simple 0).val + (2 : ℤ) • P.coroot (simple 1).val +
      P.coroot (simple 2).val + P.coroot (simple 3).val := by
  have hsymm (i j : Fin 4) : (D4Cartan j i : ℤ) = D4Cartan i j := by
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hc (i j : Fin 4) : P.flip.pairing (simple j).val (simple i).val = D4Cartan i j :=
    (cartan j i).trans (hsymm i j)
  exact highestRootExpansion P.flip B.flip simple hc

private def intermediateRootIndex : I :=
  P.reflectionPerm (simple 3).val
    (P.reflectionPerm (simple 2).val (P.reflectionPerm (simple 0).val (simple 1).val))

omit [Finite I] [P.IsReduced] in
include cartan in
private theorem intermediateRootExpansion :
    P.root (intermediateRootIndex P B simple) = ∑ i, P.root (simple i).val := by
  have h := expand_reflect P B simple cartan 0 _ _ (expand_single P B simple 1)
  have h := expand_reflect P B simple cartan 2 _ _ h
  have h := expand_reflect P B simple cartan 3 _ _ h
  change expand P B simple ((positivePath 10).2.foldl (fun c j ↦ reflectD4 j c)
    (Pi.single (positivePath 10).1 1)) = P.root (intermediateRootIndex P B simple) at h
  rw [path_eq] at h
  rw [← h]
  simp [expand, positiveD4, Fin.sum_univ_four]

omit [Finite I] [P.IsReduced] in
include cartan in
private theorem intermediateCorootExpansion :
    P.coroot (intermediateRootIndex P B simple) = ∑ i, P.coroot (simple i).val := by
  have hsymm (i j : Fin 4) : (D4Cartan j i : ℤ) = D4Cartan i j := by
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hc (i j : Fin 4) : P.flip.pairing (simple j).val (simple i).val = D4Cartan i j :=
    (cartan j i).trans (hsymm i j)
  exact intermediateRootExpansion P.flip B.flip simple hc

omit [Finite I] [P.IsReduced] in
include cartan in
private theorem intermediateReflection :
    P.reflectionPerm (intermediateRootIndex P B simple) (simple 1).val =
      highestRootIndex P B simple := by
  have h : P.toLinearMap (P.root (simple 1).val) (P.coroot (intermediateRootIndex P B simple)) =
      -1 := by
    rw [intermediateCorootExpansion P B simple cartan]
    simp only [Fin.sum_univ_four, map_add, RootPairing.root_coroot_eq_pairing, cartan]
    decide +kernel
  apply P.root.injective
  rw [← P.reflectionPerm_root, h, intermediateRootExpansion P B simple cartan,
    highestRootExpansion P B simple cartan, Fin.sum_univ_four]
  module

omit [Finite I] [P.IsReduced] in
include cartan in
private theorem highestCorootEval (a : I) (c : Fin 4 → ℤ) (hc : expand P B simple c = P.root a) :
    P.toLinearMap (P.root a) (P.coroot (highestRootIndex P B simple)) = c 1 := by
  have hsum (j : Fin 4) :
      P.toLinearMap (P.root (simple j).val) (P.coroot (highestRootIndex P B simple)) =
        if j = 1 then 1 else 0 := by
    rw [highestCorootExpansion P B simple cartan]
    simp only [map_add, map_smul, RootPairing.root_coroot_eq_pairing, cartan]
    fin_cases j <;> decide +kernel
  rw [← hc]
  dsimp only [expand]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, hsum, smul_ite,
    smul_zero, zsmul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

end RootPairing

/-- No positive integral combination involving the highest root and a
second positive root can be a root. -/
theorem highestRootExcludesPositiveCone (q : ℤ × ℤ) (hq : q ∈ positiveCoordinates)
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    (i : ℤ) • ((3, 2) : ℤ × ℤ) + (j : ℤ) • q ∉
      LieAlgebrasAndRepresentations.rankTwoCoefficients .G₂ := by
  have hpos : ∀ p : ↥positiveCoordinates, 1 ≤ p.val.1 + p.val.2 := by decide +kernel
  have hroot : ∀ p : ↥(LieAlgebrasAndRepresentations.rankTwoCoefficients .G₂),
      p.val.1 + p.val.2 ≤ 5 := by decide +kernel
  intro h
  have hu := hroot ⟨_, h⟩
  have hl := hpos ⟨q, hq⟩
  change 1 ≤ q.1 + q.2 at hl
  change (i : ℤ) * 3 + (j : ℤ) * q.1 + ((i : ℤ) * 2 + (j : ℤ) * q.2) ≤ 5 at hu
  have hj' : 1 ≤ (j : ℤ) := by omega
  have hi' : 1 ≤ (i : ℤ) := by omega
  have hmul := Int.mul_le_mul hj' hl (by decide : 0 ≤ (1 : ℤ)) (by omega : 0 ≤ (j : ℤ))
  nlinarith

section Folding

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open AbstractPairing (Root)
open BorelsAndChambers (subgroupRoots)
open CharacterDescent (Character Cocharacter)
open GeometricBorelConjugacy (subgroupOfSubgroup)
open Pinning (AttachedDatum)
open QuasiSplitPinnedPairModel (BorelPair)
open Specs.Relative.RelativeChambers (relativeRoots)
open Specs.Arithmetic.TrialitarianRelativeRoots (AbsolutePair Folding IsRestriction)
open Specs.Arithmetic.QuasiSplitFixedWeyl (multiplicativeGroup IsUnitComparison IsLargestSplitSubtorus)

universe u

variable {F K : Type u} [Field F] [Field K] [Algebra F K] {G : AffineAlgebraicGroup F}
  {M : BorelPair G}

private def coordinateMap {X : Type u} [AddCommGroup X] (s l : X) : (ℤ × ℤ) →+ X :=
  AddMonoidHom.mk' (fun p ↦ p.1 • s + p.2 • l) (fun p q ↦ by
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    abel)

private theorem coordinateMap_injective {X : Type u} [AddCommGroup X] (s l : X)
    (f g : X →ₗ[ℤ] ℤ) (hfs : f s = 2) (hfl : f l = -3)
    (hgs : g s = -1) (hgl : g l = 2) : Function.Injective (coordinateMap s l) := by
  intro p q h
  have hf := congrArg f h
  have hg := congrArg g h
  change f (p.1 • s + p.2 • l) = f (q.1 • s + q.2 • l) at hf
  change g (p.1 • s + p.2 • l) = g (q.1 • s + q.2 • l) at hg
  simp only [map_add, map_smul, hfs, hfl, hgs, hgl, Int.zsmul_eq_mul] at hf hg
  exact Prod.ext (by omega) (by omega)

private theorem coordinateMap_project {X : Type u} [AddCommGroup X] (s l : X)
    (c : Fin 4 → ℤ) :
    coordinateMap s l (project c) = ∑ i, c i • (if i = 1 then l else s) := by
  change (c 0 + c 2 + c 3) • s + c 1 • l = _
  rw [Fin.sum_univ_four]
  simp [add_smul]
  abel

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- The restricted roots have the indicated signed G₂ coordinates once
the two simple restrictions are paired with the invariant coroots. -/
theorem foldingOfPairings (S : ClosedSubgroup M.torus.group)
    (P : AbsolutePair K M) (D : AttachedDatum P.pair)
    (simple : letI := D.comm; Fin 4 ≃ D.base.support)
    (restrict : Character P.pair.T.group →* Character S.group)
    (cartan : letI := D.comm; ∀ i j,
      D.datum.rootDatum.pairing (simple j).val (simple i).val = D4Cartan i j)
    (hpositive : letI := D.comm; ∀ a : Root P.pair.T, D.base.IsPos a ↔
      a ∈ subgroupRoots P.pair.T P.pair.B)
    (houter : ∀ i ≠ 1, restrict (simple i).val.val = restrict (simple 0).val.val)
    (f g : Additive (Character S.group) →ₗ[ℤ] ℤ)
    (hfs : f (Additive.ofMul (restrict (simple 0).val.val)) = 2)
    (hfl : f (Additive.ofMul (restrict (simple 1).val.val)) = -3)
    (hgs : g (Additive.ofMul (restrict (simple 0).val.val)) = -1)
    (hgl : g (Additive.ofMul (restrict (simple 1).val.val)) = 2)
    (hroots : relativeRoots (subgroupOfSubgroup M.torus S) =
      Set.range (fun a : Root P.pair.T ↦ restrict a.val) \ {1}) :
    ∃ coeff coord, Folding S P D simple restrict coeff coord := by
  classical
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.reduced
  let s := Additive.ofMul (restrict (simple 0).val.val)
  let l := Additive.ofMul (restrict (simple 1).val.val)
  let coord := coordinateMap s l
  have hinj := coordinateMap_injective s l f g hfs hfl hgs hgl
  obtain ⟨coeff, he, _, hnonzero, hpos, hall, h10, h01, h11, h21, h31, h32, hlong⟩ :=
    rootCoefficientFolding D.datum.rootDatum D.base simple cartan
  let f₀ := (MonoidHom.toAdditive restrict).toIntLinearMap
  have hsimple (i : Fin 4) : f₀ (D.datum.rootDatum.root (simple i).val) =
      if i = 1 then l else s := by
    rw [D.datum.root_eq]
    change Additive.ofMul (restrict (simple i).val.val) = _
    by_cases hi : i = 1
    · subst i
      simp [l]
    · simp [hi, houter i hi, s]
  have hproj (a : Root P.pair.T) :
      coord (project (coeff a)) = Additive.ofMul (restrict a.val) := by
    have h := congrArg f₀ (he a)
    rw [D.datum.root_eq, map_sum] at h
    change Additive.ofMul (restrict a.val) = _ at h
    simpa only [map_smul, hsimple, ← coordinateMap_project s l] using h.symm
  have hne (a : Root P.pair.T) : restrict a.val ≠ 1 := by
    intro h
    apply hnonzero a
    apply hinj
    rw [hproj, h]
    exact coord.map_zero.symm
  have hre : relativeRoots (subgroupOfSubgroup M.torus S) =
      Set.range (fun a : Root P.pair.T ↦ restrict a.val) := by
    rw [hroots]
    ext χ
    constructor
    · exact fun h ↦ h.1
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a, rfl⟩, fun ha ↦ hne a (Set.mem_singleton_iff.mp ha)⟩
  refine ⟨coeff, coord, he, hproj, ?_, hinj, hne, hre, ?_,
    hall, h10, h01, h11, h21, h31, h32, hlong⟩
  · intro i
    by_cases hi : i = 1
    · subst i
      change restrict (simple 1).val.val = (0 • s + 1 • l).toMul
      simp [l]
    · rw [ite_eq_right hi, houter i hi]
      change restrict (simple 0).val.val = (1 • s + 0 • l).toMul
      simp [s]
  · have h : subgroupRoots P.pair.T P.pair.B = {a | D.base.IsPos a} :=
      Set.ext fun a ↦ (hpositive a).symm
    rw [h]
    exact hpos

open private splitSchemeComparison splitSchemeComparison_naturality
  from LinearAlgebraicGroups.Relative.RationalCocharacter
open private splitPresentation from LinearAlgebraicGroups.RootData.CharacterPairing
open private splitGroupHomEquiv from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private groupBaseChange_injective scalarMorphism scalarMorphism_comp scalarMorphism_baseChange
  scalarMorphism_left scalarMorphism_descends
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes
open private pairing_extended from LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
open private multiplicativeGroupAlgebra from LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
open private unitEquiv from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private isCommMonObj_of_groupIso from LinearAlgebraicGroups.Affine.HopfAlgebras
open CocharacterDynamics (unitPoint)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.DiagonalizableGroups (IntegerCharacters groupAlgebraMap)
open CharacterDescent (StandardLattice)

set_option backward.isDefEq.respectTransparency false in
private theorem liftSplitCharacter {T : GroupScheme F} (hT : IsSplitTorus T)
    (t : multiplicativeGroup K ≅ (groupBaseChange F K).obj (multiplicativeGroup F))
    (χ : Character ((groupBaseChange F K).obj T)) :
    ∃ a : Character T, (groupBaseChange F K).map a = χ ≫ t.hom := by
  let E := groupBaseChange F K
  obtain ⟨r, ⟨q⟩⟩ := splitPresentation hT
  let i := splitSchemeComparison (k := F) K IntegerCharacters
  let j := splitSchemeComparison (k := F) K (StandardLattice.{u} r)
  let b := j.hom ≫ E.map q.hom ≫ χ ≫ t.hom ≫ i.inv
  obtain ⟨f, hf⟩ := (splitGroupHomEquiv (k := K) IntegerCharacters (StandardLattice.{u} r)).surjective b
  change specGroupMap (groupAlgebraMap K f) = b at hf
  let a := specGroupMap (groupAlgebraMap F f)
  have hnat : b ≫ i.hom = j.hom ≫ E.map a := by
    rw [← hf]
    exact splitSchemeComparison_naturality K f
  refine ⟨q.inv ≫ a, ?_⟩
  calc
    E.map (q.inv ≫ a) = E.map q.inv ≫ j.inv ≫ b ≫ i.hom := by
      rw [E.map_comp]
      have h := congrArg (fun z ↦ j.inv ≫ z) hnat
      simp only [Iso.inv_hom_id_assoc] at h
      exact congrArg (fun z ↦ E.map q.inv ≫ z) h.symm
    _ = χ ≫ t.hom := by
      simp only [b, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
      rw [← Category.assoc (E.map q.inv), ← E.map_comp, q.inv_hom_id, E.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- A character of the split Borel torus restricts to an actual
ground-field character of its split subtorus. -/
theorem restrictionExists (S : ClosedSubgroup M.torus.group) (hS : IsSplitTorus S.group)
    (t : multiplicativeGroup K ≅ (groupBaseChange F K).obj (multiplicativeGroup F)) :
    ∃ restrict, IsRestriction S t restrict := by
  classical
  let E := groupBaseChange F K
  let h (χ : Character (E.obj M.torus.group)) :=
    liftSplitCharacter hS t (E.map S.inclusion ≫ χ)
  let r (χ : Character (E.obj M.torus.group)) := (h χ).choose
  have hr (χ : Character (E.obj M.torus.group)) :=
    (h χ).choose_spec
  letI : IsCommMonObj (E.obj (multiplicativeGroup F)).X :=
    isCommMonObj_of_groupIso t inferInstance
  let restrict : Character (E.obj M.torus.group) →* Character S.group := {
    toFun := r
    map_one' := by
      apply groupBaseChange_injective (F := F) (K := K)
      rw [hr]
      apply Grp.hom_ext
      change ((E.map S.inclusion).hom.hom ≫ (1 : _ ⟶ _) ≫ t.hom.hom.hom) =
        (baseChange F K).map (1 : S.group.X ⟶ (multiplicativeGroup F).X)
      rw [Functor.map_one, MonObj.one_comp, MonObj.comp_one]
    map_mul' := by
      intro a b
      apply groupBaseChange_injective (F := F) (K := K)
      have hm : E.map (r a * r b) = E.map (r a) * E.map (r b) := by
        apply Grp.hom_ext
        exact (baseChange F K).map_mul _ _
      rw [hr, hm, hr, hr]
      apply Grp.hom_ext
      change (E.map S.inclusion).hom.hom ≫ (a.hom.hom * b.hom.hom) ≫ t.hom.hom.hom =
        (((E.map S.inclusion).hom.hom ≫ a.hom.hom ≫ t.hom.hom.hom) *
          ((E.map S.inclusion).hom.hom ≫ b.hom.hom ≫ t.hom.hom.hom))
      rw [← Category.assoc, MonObj.comp_mul, MonObj.mul_comp, Category.assoc, Category.assoc] }
  exact ⟨restrict, hr⟩

private theorem unitComparison_unique
    {t t' : multiplicativeGroup K ≅ (groupBaseChange F K).obj (multiplicativeGroup F)}
    (ht : IsUnitComparison t) (ht' : IsUnitComparison t') : t = t' := by
  apply Iso.ext
  apply Grp.hom_ext
  apply hom_ext_of_points (multiplicativeGroupAlgebra K).property.1
  intro R p
  let a := unitEquiv R p
  have ha : unitPoint R a = p := (unitEquiv R).symm_apply_apply p
  rw [← ha]
  exact (baseChangePoints F K (multiplicativeGroup F).X R).injective
    ((ht R a).trans (ht' R a).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The adjoint weights of the actual split torus are the nontrivial
restrictions of the absolute roots. -/
theorem rootsOfRestriction (S : ClosedSubgroup M.torus.group) (hS : IsSplitTorus S.group)
    (P : AbsolutePair K M)
    (t : multiplicativeGroup K ≅ (groupBaseChange F K).obj (multiplicativeGroup F))
    (ht : IsUnitComparison t)
    (restrict : Character P.pair.T.group →* Character S.group)
    (hrestrict : IsRestriction S t restrict) :
    relativeRoots (subgroupOfSubgroup M.torus S) =
      Set.range (fun a : Root P.pair.T ↦ restrict a.val) \ {1} := by
  let E := groupBaseChange F K
  let S₀ := subgroupOfSubgroup M.torus S
  obtain ⟨t', ht', hinj, he⟩ := Relative.RelativeChambers.relativeRootsByRestriction
    G S₀ M.torus S.inclusion rfl hS P.torusClosed P.split
  have ht₁ : IsUnitComparison t' := ht'
  have e : t' = t := unitComparison_unique ht₁ ht
  subst t'
  let b (χ : Character S.group) : Character (E.obj S.group) := E.map χ ≫ t.inv
  have hb (χ : Character P.pair.T.group) : b (restrict χ) = E.map S.inclusion ≫ χ := by
    change E.map (restrict χ) ≫ t.inv = _
    erw [hrestrict χ]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  have hb₁ : b 1 = 1 := by
    apply Grp.hom_ext
    have hf : (E.map (1 : Character S.group)).hom.hom =
        (1 : (E.obj S.group).X ⟶ (E.obj (multiplicativeGroup F)).X) :=
      (baseChange F K).map_one
    change (E.map (1 : Character S.group)).hom.hom ≫ t.inv.hom.hom =
      (1 : (E.obj S.group).X ⟶ (multiplicativeGroup K).X)
    rw [hf, MonObj.one_comp]
  change b '' relativeRoots S₀ =
    ((fun χ : Character P.pair.T.group ↦ E.map S.inclusion ≫ χ) ''
      CharacterPairing.absoluteRoots P.pair.T) \ {1} at he
  ext χ
  have hχ : χ ∈ relativeRoots S₀ ↔ b χ ∈ b '' relativeRoots S₀ :=
    ⟨fun h ↦ ⟨χ, h, rfl⟩, fun ⟨a, ha, h⟩ ↦ hinj h ▸ ha⟩
  rw [hχ, he]
  constructor
  · rintro ⟨⟨a, ha, hae⟩, hn⟩
    refine ⟨⟨⟨a, ha⟩, hinj ((hb a).trans hae)⟩, ?_⟩
    intro h
    apply hn
    exact Set.mem_singleton_iff.mpr ((congrArg b (Set.mem_singleton_iff.mp h)).trans hb₁)
  · rintro ⟨⟨a, rfl⟩, hn⟩
    refine ⟨⟨a.val, a.property, (hb a.val).symm⟩, ?_⟩
    intro h
    exact hn (Set.mem_singleton_iff.mpr (hinj ((Set.mem_singleton_iff.mp h).trans hb₁.symm)))

open Specs.Arithmetic.QuasiSplitFixedWeyl (IsScalarAction)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.AbsoluteDynkinTypes (D4Outer)
open Specs.CharacterPairing (pairing)
open private cocharacterFactorsThroughMaximalSplit
  from LinearAlgebraicGroups.Relative.MaximalSplitTori

section ScalarAction

variable (S : ClosedSubgroup M.torus.group) (P : AbsolutePair K M) (D : AttachedDatum P.pair)
  (t : multiplicativeGroup K ≅ (groupBaseChange F K).obj (multiplicativeGroup F))
  (ρ : letI := D.comm; Gal(K/F) →* D.datum.rootDatum.Aut)
  (action : IsScalarAction M.torus P.torusClosed D.comm D.datum t ρ)

include action in
set_option backward.isDefEq.respectTransparency false in
private theorem invariantCocharacter [IsGalois F K]
    (hmax : IsMaximalSplitTorus (subgroupOfSubgroup M.torus S))
    (y : Additive (Cocharacter P.pair.T.group))
    (hy : letI := D.comm; ∀ σ, (ρ σ).coweightEquiv.symm y = y) :
    ∃ c : Cocharacter S.group, t.hom ≫ (groupBaseChange F K).map (c ≫ S.inclusion) = y.toMul := by
  let E := groupBaseChange F K
  let d : Cocharacter (E.obj M.torus.group) := y.toMul
  have hd (σ : Gal(K/F)) : scalarMorphism σ (t.inv ≫ d) = t.inv ≫ d := by
    apply Grp.hom_ext
    apply Over.OverMorphism.ext
    rw [scalarMorphism_left]
    exact ((action.2 σ d).symm.trans (congrArg
      (fun z ↦ (t.inv ≫ (show Cocharacter (E.obj M.torus.group) from Additive.toMul z)).hom.hom.left)
      (hy σ)))
  obtain ⟨c, hc⟩ := scalarMorphism_descends (multiplicativeGroupAlgebra F)
    (closedSubgroupAlgebraicGroup M.torus) (t.inv ≫ d) hd
  obtain ⟨a, ha⟩ := cocharacterFactorsThroughMaximalSplit G
    (subgroupOfSubgroup M.torus S) M.torus hmax M.isTorus S.inclusion rfl c
  refine ⟨a, ?_⟩
  change t.hom ≫ E.map (a ≫ S.inclusion) = d
  rw [ha, hc, Iso.hom_inv_id_assoc]

include action in
set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private theorem restrictionInvariant
    (restrict : Character P.pair.T.group →* Character S.group)
    (hrestrict : IsRestriction S t restrict) (σ : Gal(K/F))
    (χ : Character P.pair.T.group) :
    letI := D.comm
    restrict ((ρ σ).weightEquiv (Additive.ofMul χ)).toMul = restrict χ := by
  letI := D.comm
  let E := groupBaseChange F K
  let χ' : Character (E.obj M.torus.group) :=
    ((ρ σ).weightEquiv (Additive.ofMul χ)).toMul
  have he : scalarMorphism σ (χ ≫ t.hom) = χ' ≫ t.hom := by
    apply Grp.hom_ext
    apply Over.OverMorphism.ext
    rw [scalarMorphism_left]
    exact (action.1 σ χ).symm
  change restrict χ' = restrict χ
  apply groupBaseChange_injective (F := F) (K := K)
  calc
    E.map (restrict χ') = E.map S.inclusion ≫ χ' ≫ t.hom := hrestrict χ'
    _ = scalarMorphism σ (E.map S.inclusion ≫ χ ≫ t.hom) := by
      rw [scalarMorphism_comp, scalarMorphism_baseChange, he]
    _ = E.map (restrict χ) := by
      erw [← hrestrict χ, scalarMorphism_baseChange]
      rfl

end ScalarAction

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private theorem attachedPositive (P : Pinning.SplitBorelPair K) (D : AttachedDatum P) :
    letI := D.comm
    ∀ a : Root P.T, D.base.IsPos a ↔ a ∈ subgroupRoots P.T P.B := by
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.freeCharacters
  letI := D.datum.finiteCharacters
  letI := D.datum.reduced
  obtain ⟨c, _, hc, _, hpos⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT P.G P.reductive P.T P.split P.maximal).1
      P.B P.borel P.containsTorus
  let R := D.datum.rootDatum
  let f := Specs.SimpleRoots.evaluate D.datum c
  have he (i : Root P.T) : f (R.root i) = pairing P.T.group i.val c := by
    change R.toLinearMap (R.root i) (Additive.ofMul c) = _
    rw [D.datum.root_eq, D.datum.pairing_eq]
  obtain ⟨b, hb⟩ := RootData.SimpleRoots.baseFor R f (fun i ↦ he i ▸ hc i)
  have hf : Specs.SimpleRoots.positive R f = subgroupRoots P.T P.B := by
    rw [hpos]
    ext i
    change 0 < f (R.root i) ↔ 0 < pairing P.T.group i.val c
    rw [he]
  have hs : b.support = D.base.support := by
    ext i
    rw [hb.simple_iff, hf, D.simple_iff]
    unfold Pinning.IsSimple
    dsimp only [R]
    simp only [D.datum.root_eq]
    rfl
  have eq_of_support (b₁ b₂ : R.Base) (h : b₁.support = b₂.support) : b₁ = b₂ := by
    cases b₁
    cases b₂
    cases h
    rfl
  intro a
  rw [← eq_of_support b D.base hs, hb.positive_iff, hf]

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- The actual Galois action and the maximal split torus give the
character folding and the central and outer-orbit cocharacters. -/
theorem foldingOfScalarAction [IsGalois F K]
    (S : ClosedSubgroup M.torus.group) (P : AbsolutePair K M) (D : AttachedDatum P.pair)
    (hS : IsLargestSplitSubtorus S)
    (hmax : IsMaximalSplitTorus (subgroupOfSubgroup M.torus S))
    (simple : letI := D.comm; Fin 4 ≃ D.base.support)
    (t : multiplicativeGroup K ≅ (groupBaseChange F K).obj (multiplicativeGroup F))
    (ht : IsUnitComparison t)
    (ρ : letI := D.comm; Gal(K/F) →* D.datum.rootDatum.Aut)
    (action : IsScalarAction M.torus P.torusClosed D.comm D.datum t ρ)
    (cartan : letI := D.comm; ∀ i j,
      D.datum.rootDatum.pairing (simple j).val (simple i).val = D4Cartan i j)
    (hstable : letI := D.comm; ∀ σ a, (ρ σ).indexEquiv a ∈ D.base.support ↔ a ∈ D.base.support)
    (hcentral : letI := D.comm; ∀ σ, (ρ σ).indexEquiv (simple 1).val = (simple 1).val)
    (htrans : letI := D.comm; ∀ i j : D4Outer, ∃ σ,
      (ρ σ).indexEquiv (simple i.val).val = (simple j.val).val) :
    letI := D.comm
    ∃ (restrict : Character P.pair.T.group →* Character S.group)
      (coeff : Root P.pair.T → Fin 4 → ℤ)
      (coord : (ℤ × ℤ) →+ Additive (Character S.group)) (outer central : Cocharacter S.group),
      IsRestriction S t restrict ∧ Folding S P D simple restrict coeff coord ∧
      Additive.ofMul (t.hom ≫ (groupBaseChange F K).map (outer ≫ S.inclusion)) =
        D.datum.rootDatum.coroot (simple 0).val + D.datum.rootDatum.coroot (simple 2).val +
          D.datum.rootDatum.coroot (simple 3).val ∧
      Additive.ofMul (t.hom ≫ (groupBaseChange F K).map (central ≫ S.inclusion)) =
        D.datum.rootDatum.coroot (simple 1).val := by
  classical
  letI := D.comm
  let T := P.pair.T
  let R := D.datum.rootDatum
  let Y := Additive (Cocharacter T.group)
  let coroot (i : Fin 4) : Y := R.coroot (simple i).val
  let total := ∑ i, coroot i
  let y := coroot 0 + coroot 2 + coroot 3
  have hy : y = total - coroot 1 := by
    dsimp only [y, total]
    rw [Fin.sum_univ_four]
    abel
  have hcor (σ : Gal(K/F)) (a : Root T) :
      (ρ σ).coweightEquiv.symm (R.coroot a) = R.coroot ((ρ σ).indexEquiv a) := by
    apply (ρ σ).coweightEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    have h := RootPairing.Hom.coroot_coweightMap_apply R R ((ρ σ).indexEquiv a) (ρ σ).toHom
    simpa using h.symm
  have hc (σ : Gal(K/F)) : (ρ σ).coweightEquiv.symm (coroot 1) = coroot 1 :=
    (hcor σ _).trans (congrArg R.coroot (hcentral σ))
  have htotal (σ : Gal(K/F)) : (ρ σ).coweightEquiv.symm total = total := by
    let p : Fin 4 ≃ Fin 4 := simple.trans
      (((ρ σ).indexEquiv.subtypeEquiv (fun a ↦ (hstable σ a).symm)).trans simple.symm)
    have hp (i : Fin 4) : (simple (p i)).val = (ρ σ).indexEquiv (simple i).val := by
      simp [p]
    dsimp only [total]
    rw [map_sum, ← Equiv.sum_comp p coroot]
    apply Finset.sum_congr rfl
    intro i _
    change (ρ σ).coweightEquiv.symm (R.coroot (simple i).val) = R.coroot (simple (p i)).val
    rw [hcor, hp]
  obtain ⟨outer, ho⟩ := invariantCocharacter S P D t ρ action hmax y (fun σ ↦ by
    rw [hy, map_sub, htotal, hc])
  obtain ⟨central, hce⟩ := invariantCocharacter S P D t ρ action hmax _ hc
  obtain ⟨r, hr⟩ := restrictionExists (K := K) S hS.1 t
  have houter (i : Fin 4) (hi : i ≠ 1) :
      r (simple i).val.val = r (simple 0).val.val := by
    have h0 : (0 : Fin 4) ≠ 1 := by decide
    obtain ⟨σ, hσ⟩ := htrans ⟨0, h0⟩ ⟨i, hi⟩
    have h := RootPairing.Hom.root_weightMap_apply R R (simple 0).val (ρ σ).toHom
    change (ρ σ).weightEquiv (R.root (simple 0).val) =
      R.root ((ρ σ).indexEquiv (simple 0).val) at h
    change (ρ σ).indexEquiv (simple 0).val = (simple i).val at hσ
    rw [hσ, D.datum.root_eq, D.datum.root_eq] at h
    have hinv := restrictionInvariant S P D t ρ action r hr σ (simple 0).val.val
    rw [h] at hinv
    exact hinv
  obtain ⟨comm, _, _, _, _, p, _, hp⟩ :=
    RootData.CharacterPairing.perfectCharacterPairing S.group hS.1
  letI := comm
  let f := p.flip (Additive.ofMul outer)
  let g := p.flip (Additive.ofMul central)
  let E := groupBaseChange F K
  have heval (a : Cocharacter S.group) (w : Y)
      (ha : t.hom ≫ E.map (a ≫ S.inclusion) = w.toMul) (i : Fin 4) :
      p (Additive.ofMul (r (simple i).val.val)) (Additive.ofMul a) =
        R.toLinearMap (R.root (simple i).val) w := by
    rw [D.datum.root_eq]
    let χ : Character (E.obj M.torus.group) := (simple i).val.val
    have hχ : E.map S.inclusion ≫ χ = E.map (r χ) ≫ t.inv := by
      erw [hr χ]
      simp [E]
    have h := pairing_extended K t ht S.inclusion (r χ) χ hχ a
    have hm : t.hom ≫ E.map a ≫ E.map S.inclusion = w.toMul := by
      rw [← E.map_comp, ha]
    change pairing T.group (simple i).val.val (t.hom ≫ E.map a ≫ E.map S.inclusion) =
      pairing S.group (r (simple i).val.val) a at h
    rw [hm] at h
    exact (hp _ _).trans (h.symm.trans (D.datum.pairing_eq _ w.toMul).symm)
  have hcart (i j : Fin 4) : R.toLinearMap (R.root (simple j).val) (coroot i) = D4Cartan i j :=
    (R.root_coroot_eq_pairing _ _).trans (cartan i j)
  have hfs : f (Additive.ofMul (r (simple 0).val.val)) = 2 := by
    change p _ _ = _
    rw [heval outer y ho, show y = coroot 0 + coroot 2 + coroot 3 from rfl]
    simp only [map_add, hcart]
    decide +kernel
  have hfl : f (Additive.ofMul (r (simple 1).val.val)) = -3 := by
    change p _ _ = _
    rw [heval outer y ho, show y = coroot 0 + coroot 2 + coroot 3 from rfl]
    simp only [map_add, hcart]
    decide +kernel
  have hgs : g (Additive.ofMul (r (simple 0).val.val)) = -1 := by
    change p _ _ = _
    rw [heval central (coroot 1) hce, hcart]
    decide +kernel
  have hgl : g (Additive.ofMul (r (simple 1).val.val)) = 2 := by
    change p _ _ = _
    rw [heval central (coroot 1) hce, hcart]
    decide +kernel
  obtain ⟨coeff, coord, hfold⟩ := foldingOfPairings S P D simple r cartan (attachedPositive P.pair D)
    houter f g hfs hfl hgs hgl (rootsOfRestriction S hS.1 P t ht r hr)
  exact ⟨r, coeff, coord, outer, central, hr, hfold,
    congrArg Additive.ofMul ho, congrArg Additive.ofMul hce⟩

end Folding

section WeylTransport

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open AbstractPairing (Root)
open AbsoluteDynkinTypes (D4Outer)
open CharacterDescent (Character Cocharacter)
open GeometricBorelConjugacy (subgroupOfSubgroup)
open QuasiSplitPinnedPairModel (BorelPair)
open Pinning (AttachedDatum)
open Specs.Arithmetic.TrialitarianRelativeRoots
open Specs.Arithmetic.QuasiSplitFixedWeyl
  (multiplicativeGroup IsScalarAction IsUnitComparison fixedWeyl)
open private reflection_conjugation
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl

variable {F K : Type u} [Field F] [Field K] [Algebra F K] {G : AffineAlgebraicGroup F}
  {M : BorelPair G} {S : ClosedSubgroup M.torus.group} {P : AbsolutePair K M}
  {D : AttachedDatum P.pair}

set_option linter.style.haveILetI false in
private theorem projectedDistinguishedRoots
    (simple : letI := D.comm; Fin 4 ≃ D.base.support)
    (cartan : letI := D.comm; ∀ i j,
      D.datum.rootDatum.pairing (simple j).val (simple i).val = D4Cartan i j)
    (coeff : Root P.pair.T → Fin 4 → ℤ)
    (he : letI := D.comm; ∀ a, D.datum.rootDatum.root a =
      ∑ i, coeff a i • D.datum.rootDatum.root (simple i).val) :
    letI := D.comm
    let R := D.datum.rootDatum
    project (coeff (simple 1).val) = (0, 1) ∧
    project (coeff (intermediateRootIndex R D.base simple)) = (3, 1) ∧
    project (coeff (highestRootIndex R D.base simple)) = (3, 2) := by
  letI := D.comm
  let R := D.datum.rootDatum
  have eq (a : Root P.pair.T) (v : Fin 4 → ℤ) (h : expand R D.base simple v = R.root a) :
      coeff a = v := expand_injective R D.base simple ((he a).symm.trans h.symm)
  constructor
  · rw [eq _ _ (expand_single R D.base simple 1)]
    decide +kernel
  constructor
  · rw [eq _ (fun _ ↦ 1) (by
      change expand R D.base simple (fun _ ↦ 1) =
        R.root (intermediateRootIndex R D.base simple)
      rw [intermediateRootExpansion R D.base simple cartan]
      simp [expand])]
    decide +kernel
  · rw [eq _ (![1, 2, 1, 1] : Fin 4 → ℤ) (by
      change expand R D.base simple ![1, 2, 1, 1] =
        R.root (highestRootIndex R D.base simple)
      rw [highestRootExpansion R D.base simple cartan]
      simp [expand, Fin.sum_univ_four])]
    decide +kernel

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- A single Galois-fixed absolute reflection sends the fixed central
simple root to the root over the highest relative root. -/
theorem highestRootFixedReflection
    (simple : letI := D.comm; Fin 4 ≃ D.base.support)
    (cartan : letI := D.comm; ∀ i j,
      D.datum.rootDatum.pairing (simple j).val (simple i).val = D4Cartan i j)
    (t : multiplicativeGroup K ≅ (groupBaseChange F K).obj (multiplicativeGroup F))
    (ρ : letI := D.comm; Gal(K/F) →* D.datum.rootDatum.Aut)
    (action : IsScalarAction M.torus P.torusClosed D.comm D.datum t ρ)
    (restrict : Character P.pair.T.group →* Character S.group)
    (hr : IsRestriction S t restrict)
    (coeff : Root P.pair.T → Fin 4 → ℤ)
    (coord : (ℤ × ℤ) →+ Additive (Character S.group))
    (hf : Folding S P D simple restrict coeff coord) :
    letI := D.comm
    let R := D.datum.rootDatum
    ∃ v : fixedWeyl R ρ,
      v.val.val.indexEquiv (simple 1).val = highestRootIndex R D.base simple := by
  letI := D.comm
  let R := D.datum.rootDatum
  obtain ⟨he, hp, _, hcoord, _, _, _, _, _, _, _, _, _, _, hu⟩ := hf
  let δ := intermediateRootIndex R D.base simple
  have hδ : project (coeff δ) = (3, 1) := (projectedDistinguishedRoots simple cartan coeff he).2.1
  have hfixed (σ : Gal(K/F)) : (ρ σ).indexEquiv δ = δ := by
    have hw : (ρ σ).weightEquiv (Additive.ofMul δ.val) =
        Additive.ofMul ((ρ σ).indexEquiv δ).val := by
      have h := RootPairing.Hom.root_weightMap_apply R R δ (ρ σ).toHom
      change (ρ σ).weightEquiv (R.root δ) = R.root ((ρ σ).indexEquiv δ) at h
      dsimp only [R] at h
      rwa [D.datum.root_eq, D.datum.root_eq] at h
    have h := restrictionInvariant S P D t ρ action restrict hr σ δ.val
    rw [hw] at h
    have h' : project (coeff ((ρ σ).indexEquiv δ)) = project (coeff δ) := by
      apply hcoord
      rw [hp, hp, ← h]
      rfl
    obtain ⟨a, _, ha⟩ := hu (3, 1) (by decide +kernel)
    exact (ha _ (h'.trans hδ)).trans (ha _ hδ).symm
  refine ⟨⟨RootPairing.weylGroup.ofIdx R δ, ?_⟩, intermediateReflection R D.base simple cartan⟩
  intro σ
  change (ρ σ) * RootPairing.Equiv.reflection R δ =
    RootPairing.Equiv.reflection R δ * (ρ σ)
  have h := reflection_conjugation R (ρ σ) δ
  rw [hfixed] at h
  exact (eq_mul_inv_iff_mul_eq.mp h).symm

end WeylTransport

section RankOneRadicals

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open AbstractPairing (Root)
open AdjointRepresentation (GroupPoints)
open BorelProper (IsParabolic)
open BorelsAndChambers (subgroupRoots)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (pairing)
open GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.GeometricRadicals (IsReductive IsSplitTorus baseChangedSubgroup)
open OrderedRootProducts (RootSubgroupFamily)
open Pinning (AttachedDatum)
open QuasiSplitPinnedPairModel (BorelPair)
open RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open RootGroups (rootPoint)
open SchemeDerivedGroup (IsSubgroupOf)
open Specs.Arithmetic.QuasiSplitFixedWeyl (multiplicativeGroup IsUnitComparison)
open Specs.Arithmetic.TrialitarianRelativeRoots (AbsolutePair RankOne)
open Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open CocharacterDynamics (LimitDecomposition bigCellMap oppositeCocharacter lieImage
  cocharacterDynamics existsLimitDecomposition)
open private rootCoordinate_exists rootPoint_hasLimit rootPoint_surjective
  from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private subgroupInclusionFactors from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private connected_of_geometricallyConnected pairing_inv
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private oppositeCocharacter_eq_inv from LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
open private same_subgroup_of_same_sections centralizes_opposite_iff extendSubgroup
  limits_subgroups_extend subgroupOf_of_extend opposite_baseChange parabolic_of_cast
  contracting_of_cast
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private subgroupOf_trans from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private limitIsParabolic from LinearAlgebraicGroups.Relative.MaximalSplitTori
open private limitParabolic_root_iff from LinearAlgebraicGroups.Relative.RationalCocharacter
open private isIso_of_section from LinearAlgebraicGroups.Relative.RelativeChambers
open private differential_comp from LinearAlgebraicGroups.RootData.BorelsAndChambers

variable {F K : Type u} [Field F] [Field K] [Algebra F K] {G : AffineAlgebraicGroup F}
  {M : BorelPair G} {S : ClosedSubgroup M.torus.group} {P : AbsolutePair K M}

set_option backward.isDefEq.respectTransparency false in
private theorem rootSubgroupContracts {k : Type u} [Field k] (J : AffineAlgebraicGroup k)
    (hJ : IsReductive J) (T : ClosedSubgroup J.val)
    (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (U : RootSubgroupFamily T) (a : Root T) (d : Cocharacter T.group)
    (C : LimitDecomposition (d ≫ T.inclusion)) (hd : 0 < pairing T.group a.val d) :
    IsSubgroupOf (U a).val C.contracting := by
  obtain ⟨⟨A, x, hx, _⟩⟩ := rootCoordinate_exists RootData.RootGroups.rootSubgroups J hJ T hT hTm U a
  apply subgroupInclusionFactors (closedSubgroupAlgebraicGroup (U a).val).property.1
  intro R p
  obtain ⟨b, rfl⟩ := rootPoint_surjective x R p
  apply (C.contracting_points R _).mp
  exact rootPoint_hasLimit hx d hd R b

private theorem limitProperOfNegative {k : Type u} [Field k] (J : AffineAlgebraicGroup k)
    (T : ClosedSubgroup J.val) (d : Cocharacter T.group)
    (C : LimitDecomposition (d ≫ T.inclusion)) (a : Root T) (hd : pairing T.group a.val d < 0) :
    ¬ IsIso C.parabolic.inclusion := by
  intro h
  have hr : a ∈ subgroupRoots T C.parabolic := by
    intro v _
    refine ⟨mapPointKernel (inv C.parabolic.inclusion) v, ?_⟩
    rw [← differential_comp, IsIso.inv_hom_id]
    exact (lieFunctoriality k).2.1 _ _
  exact (not_le_of_gt hd) ((limitParabolic_root_iff J T d C a).mp hr)

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private theorem compareRootLimit (U : RootSubgroupFamily P.pair.T)
    (t : multiplicativeGroup K ≅ (groupBaseChange F K).obj (multiplicativeGroup F))
    (ht : IsUnitComparison t) {d : Cocharacter G.val}
    (C : LimitDecomposition d) (dK : Cocharacter P.pair.T.group)
    (he : dK ≫ P.pair.T.inclusion = t.hom ≫ (groupBaseChange F K).map d)
    (a b : Root P.pair.T) (ha : 0 < pairing P.pair.T.group a.val dK)
    (hb : pairing P.pair.T.group b.val dK < 0) (V : ClosedSubgroup G.val)
    (hV : SameSubgroup (extendSubgroup K V) (U a).val) :
    ¬ IsIso C.parabolic.inclusion ∧ IsSubgroupOf V C.contracting := by
  let J := baseChangedAlgebraicGroup K G
  obtain ⟨E⟩ := existsLimitDecomposition J (dK ≫ P.pair.T.inclusion)
  let E' : LimitDecomposition (t.hom ≫ (groupBaseChange F K).map d) := he ▸ E
  obtain ⟨hp, hc, _⟩ := limits_subgroups_extend G C t ht E'
  have hp' : SameSubgroup E.parabolic (extendSubgroup K C.parabolic) := by
    simpa only [E', parabolic_of_cast] using hp
  have hc' : SameSubgroup E.contracting (extendSubgroup K C.contracting) := by
    simpa only [E', contracting_of_cast] using hc
  constructor
  · intro hi
    obtain ⟨f, hf⟩ := hp'.2
    letI : IsIso ((groupBaseChange F K).map C.parabolic.inclusion) :=
      (groupBaseChange F K).map_isIso C.parabolic.inclusion
    exact limitProperOfNegative J P.pair.T dK E b hb
      (isIso_of_section E.parabolic (inv ((groupBaseChange F K).map C.parabolic.inclusion) ≫ f)
        (by rw [Category.assoc, hf]; exact IsIso.inv_hom_id _))
  · apply subgroupOf_of_extend (K := K)
    exact subgroupOf_trans hV.1 (subgroupOf_trans
      (rootSubgroupContracts J P.reductive P.pair.T P.split P.maximal U a dK E ha) hc'.1)

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- A rank-one embedding with the attached absolute coroot and matching
opposite root subgroups has the two proper opposite limit parabolics. -/
theorem oppositeRadicalsOfAbsolute (hG : IsReductive G)
    (D : AttachedDatum P.pair) (U : RootSubgroupFamily P.pair.T)
    (t : multiplicativeGroup K ≅ (groupBaseChange F K).obj (multiplicativeGroup F))
    (ht : IsUnitComparison t) (a b : Root P.pair.T)
    (L : RankOne (subgroupOfSubgroup M.torus S))
    (hL : L.MatchesAbsolute S P D U t a b) :
    L.HasOppositeRadicals := by
  letI := D.comm
  letI := hG.1
  letI : ConnectedSpace G.val.X.left := connected_of_geometricallyConnected hG.2.1
  obtain ⟨hneg, ⟨_, _, hpos, hnegSub⟩, hcor, _⟩ := hL
  let c := L.cochar ≫ (subgroupOfSubgroup M.torus S).inclusion
  let d : Cocharacter P.pair.T.group := t.hom ≫ (groupBaseChange F K).map (L.cochar ≫ S.inclusion)
  have he : d ≫ P.pair.T.inclusion = t.hom ≫ (groupBaseChange F K).map c := by
    change (t.hom ≫ (groupBaseChange F K).map (L.cochar ≫ S.inclusion)) ≫
      (groupBaseChange F K).map M.torus.inclusion = _
    rw [Category.assoc, ← Functor.map_comp, Category.assoc]
    rfl
  have he' : oppositeCocharacter d ≫ P.pair.T.inclusion =
      t.hom ≫ (groupBaseChange F K).map (oppositeCocharacter c) := by
    rw [← opposite_baseChange c t ht, ← he]
    simp only [oppositeCocharacter, Category.assoc]
  have hp : pairing P.pair.T.group a.val d = 2 := by
    rw [← D.datum.pairing_eq, ← D.datum.root_eq a]
    rw [hcor, RootPairing.root_coroot_eq_pairing, RootPairing.pairing_same]
  have hn : pairing P.pair.T.group b.val d = -2 := by
    rw [← D.datum.pairing_eq, ← D.datum.root_eq b, hneg, map_neg, LinearMap.neg_apply,
      D.datum.root_eq, D.datum.pairing_eq, hp]
  have hsign (x : Root P.pair.T) : pairing P.pair.T.group x.val (oppositeCocharacter d) =
      -pairing P.pair.T.group x.val d := by
    rw [oppositeCocharacter_eq_inv, ← D.datum.pairing_eq, ← D.datum.pairing_eq]
    exact map_neg _ _
  obtain ⟨C, E, _, _, _, _, _, _, _, _, _, _, hcell, _, _⟩ := cocharacterDynamics G c
  obtain ⟨hC, hU⟩ := compareRootLimit U t ht C d he a b (by omega) (by omega) L.positive hpos
  obtain ⟨hE, hV⟩ := compareRootLimit U t ht E (oppositeCocharacter d) he' b a
    (by rw [hsign, hn]; decide) (by rw [hsign, hp]; decide) L.negative hnegSub
  exact ⟨C, E, limitIsParabolic G hG c C, limitIsParabolic G hG _ E, hC, hE,
    same_subgroup_of_same_sections (H := G) C.centralizer_points
      (fun Y y ↦ (centralizes_opposite_iff c y).symm.trans (E.centralizer_points Y y)),
    hcell, Relative.SplitContractingRadical.contractingSubgroupIsRadical G hG c C,
    Relative.SplitContractingRadical.contractingSubgroupIsRadical G hG _ E, hU, hV⟩

end RankOneRadicals

section HighestRootCentrality

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open LinearAlgebraicGroups.Specs
open AbstractPairing (Root)
open AdjointRepresentation (GroupPoints)
open BorelsAndChambers (positiveRoots subgroupRoots contractingSubgroup)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (pairing)
open GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open OrderedRootProducts (RootSubgroupFamily rootProduct)
open QuasiSplitPinnedPairModel (BorelPair)
open Pinning (AttachedDatum)
open RootGroups (rootPoint)
open Specs.Arithmetic.TrialitarianRelativeRoots (AbsolutePair Folding IsRestriction RankOne)
open Specs.Arithmetic.QuasiSplitFixedWeyl (multiplicativeGroup IsUnitComparison)
open Specs.Relative.RelativeChambers (relativeRoots nonnegativeRoots)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open BorelProper (IsParabolic)
open RankOneFlag (SameSubgroup)
open SchemeDerivedGroup (IsSubgroupOf)
open CocharacterDynamics (LimitDecomposition lieImage limitSubgroupsSmooth
  geometricallyConnectedLimitSubgroups existsLimitDecomposition)
open LinearAlgebraicGroups.WeilRestriction (extendScalars)
open private rootPoint_add from LinearAlgebraicGroups.Classification.RankOneRelations
open private rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups
open private rootCoordinate_exists rootPoint_surjective
  from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private pairing_extended from LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
open private connected_of_geometricallyConnected limitLie_weightSpans pairing_one
  isIso_of_closedImmersion_of_differential kBorel_smooth_connected subgroupOf_limit_of_rootSigns
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private adjointWeightsInternal from LinearAlgebraicGroups.RootData.RootGroups
open private limitParabolics_le isIso_of_section
  from LinearAlgebraicGroups.Relative.RelativeChambers
open private subgroupOf_trans from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private extendSubgroup subgroupOf_of_extend limits_subgroups_extend parabolic_of_cast
  contracting_of_cast from LinearAlgebraicGroups.RootData.RankOneFlag
open private mapPoints_injective from LinearAlgebraicGroups.Classification.RankOneRelations
open private has_enumeration from LinearAlgebraicGroups.Flag.SimpleParabolicProduct

variable {F K : Type u} [Field F] [Field K] [Algebra F K] {G : AffineAlgebraicGroup F}
  {M : BorelPair G} {S : ClosedSubgroup M.torus.group} {P : AbsolutePair K M}

set_option backward.isDefEq.respectTransparency false in
/-- The absolute root over the highest relative root commutes with each
positive absolute root subgroup, over arbitrary test algebras. -/
theorem highestRootCommutesWithPositive (D : AttachedDatum P.pair)
    (simple : letI := D.comm; Fin 4 ≃ D.base.support)
    (restrict : Character P.pair.T.group →* Character S.group)
    (coeff : Root P.pair.T → Fin 4 → ℤ)
    (coord : (ℤ × ℤ) →+ Additive (Character S.group))
    (hf : Folding S P D simple restrict coeff coord)
    (a : Root P.pair.T) (ha : project (coeff a) = (3, 2))
    (b : Root P.pair.T) (hb : b ∈ subgroupRoots P.pair.T P.pair.B)
    (U : RootSubgroupFamily P.pair.T) (R : TestAlgebra K)
    (x : GroupPoints (U a).val.group R) (y : GroupPoints (U b).val.group R) :
    Commute (x ≫ (U a).val.inclusion.hom.hom : GroupPoints P.pair.G.val R)
      (y ≫ (U b).val.inclusion.hom.hom : GroupPoints P.pair.G.val R) := by
  let J := P.pair.G
  let T := P.pair.T
  by_cases hab : b = a
  · subst b
    obtain ⟨⟨A, e, _, _⟩⟩ :=
      rootCoordinate_exists RootData.RootGroups.rootSubgroups J P.reductive T P.split P.maximal U a
    obtain ⟨c, rfl⟩ := rootPoint_surjective e R x
    obtain ⟨d, rfl⟩ := rootPoint_surjective e R y
    change (rootPoint e.hom R c ≫ (U a).val.inclusion.hom.hom) *
      (rootPoint e.hom R d ≫ (U a).val.inclusion.hom.hom) =
      (rootPoint e.hom R d ≫ (U a).val.inclusion.hom.hom) *
        (rootPoint e.hom R c ≫ (U a).val.inclusion.hom.hom)
    rw [← rootPoint_comp, ← rootPoint_comp, ← rootPoint_add, ← rootPoint_add, add_comm c d]
  obtain ⟨_, hcoord, _, hinj, _, _, hpositive, hall, _⟩ := hf
  have hq : project (coeff b) ∈ positiveCoordinates := by
    change project (coeff b) ∈ (positiveCoordinates : Set _)
    rw [← hpositive]
    exact ⟨b, hb, rfl⟩
  have hind : ¬ RootGroups.Proportional a.val b.val := by
    intro h
    rcases (((RootData.RootGroups.rootSubgroups J P.reductive T P.split P.maximal).2
      a.val a.property).2.1 b.val).mp ⟨b.property, h⟩ with h | h
    · exact hab (Subtype.ext h)
    · have hneg : project (coeff b) = -((3, 2) : ℤ × ℤ) := by
        apply hinj
        rw [hcoord, map_neg, ← ha, hcoord, h, map_inv]
        rfl
      rw [hneg] at hq
      exact (by decide +kernel : -((3, 2) : ℤ × ℤ) ∉ positiveCoordinates) hq
  have hcone (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
      a.val ^ i * b.val ^ j ∉ CharacterPairing.absoluteRoots T := by
    intro h
    let d : Root T := ⟨a.val ^ i * b.val ^ j, h⟩
    have hd : project (coeff d) = i • ((3, 2) : ℤ × ℤ) + j • project (coeff b) := by
      apply hinj
      rw [hcoord, map_add, map_nsmul, map_nsmul, ← ha, hcoord, hcoord]
      change Additive.ofMul (restrict (a.val ^ i * b.val ^ j)) =
        Additive.ofMul (restrict a.val ^ i * restrict b.val ^ j)
      rw [map_mul, map_pow, map_pow]
    have hk : project (coeff d) ∈ LieAlgebrasAndRepresentations.rankTwoCoefficients .G₂ := by
      change project (coeff d) ∈ (LieAlgebrasAndRepresentations.rankTwoCoefficients .G₂ : Set _)
      rw [← hall]
      exact ⟨d, rfl⟩
    rw [hd] at hk
    exact highestRootExcludesPositiveCone (project (coeff b)) hq i j hi hj hk
  exact Classification.RankOneRelations.independentRootCommutation J P.reductive T P.split P.maximal
    a.val a.property b.val b.property hind hcone (U a).val (U b).val (U a).property (U b).property R x y

set_option backward.isDefEq.respectTransparency false in
private theorem commuteRootProduct (U : RootSubgroupFamily P.pair.T) (R : TestAlgebra K)
    (x : GroupPoints P.pair.G.val R) (l : List (Root P.pair.T))
    (h : ∀ a ∈ l, ∀ y : GroupPoints (U a).val.group R,
      Commute x (y ≫ (U a).val.inclusion.hom.hom : GroupPoints P.pair.G.val R)) :
    ∀ y : Points (OrderedRootProducts.product (fun a ↦ (U a).val.group.X) l) R,
      Commute x (y ≫ rootProduct U l : GroupPoints P.pair.G.val R) := by
  induction l with
  | nil =>
    intro y
    change Commute x (y ≫ (1 : 𝟙_ (SchemeOver K) ⟶ P.pair.G.val.X))
    rw [MonObj.comp_one]
    exact Commute.one_right x
  | cons a l ih =>
    intro y
    change Commute x (y ≫ ((fst _ _ ≫ (U a).val.inclusion.hom.hom) *
      (snd _ _ ≫ rootProduct U l)) : GroupPoints P.pair.G.val R)
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc]
    exact (h a (List.mem_cons_self) _).mul_right
      (ih (fun b hb ↦ h b (List.mem_cons_of_mem _ hb)) _)

set_option backward.isDefEq.respectTransparency false in
private theorem pairingOfRestriction
    (t : multiplicativeGroup K ≅ (groupBaseChange F K).obj (multiplicativeGroup F))
    (ht : IsUnitComparison t)
    (restrict : Character P.pair.T.group →* Character S.group)
    (hr : IsRestriction S t restrict)
    (a : Root P.pair.T) (c : Cocharacter S.group) :
    pairing S.group (restrict a.val) c = pairing P.pair.T.group a.val
      (t.hom ≫ (groupBaseChange F K).map (c ≫ S.inclusion)) := by
  let E := groupBaseChange F K
  have hχ : E.map S.inclusion ≫ a.val = E.map (restrict a.val) ≫ t.inv := by
    erw [hr a.val]
    simp [E]
  have h := pairing_extended K t ht S.inclusion (restrict a.val) a.val hχ c
  change pairing P.pair.T.group a.val (t.hom ≫ E.map c ≫ E.map S.inclusion) =
    pairing S.group (restrict a.val) c at h
  rw [← E.map_comp] at h
  exact h.symm

set_option linter.style.haveILetI false in
private theorem pairingInCoordinates
    {k : Type u} [Field k] {T : GroupScheme k} (hT : IsSplitTorus T)
    (coord : (ℤ × ℤ) →+ Additive (Character T)) (c : Cocharacter T) (p : ℤ × ℤ) :
    pairing T (coord p).toMul c =
      p.1 * pairing T (coord (1, 0)).toMul c + p.2 * pairing T (coord (0, 1)).toMul c := by
  obtain ⟨comm, _, _, _, _, b, _, hb⟩ := RootData.CharacterPairing.perfectCharacterPairing T hT
  letI := comm
  simp only [← hb]
  change b (coord p) (Additive.ofMul c) = _
  have hp : p = p.1 • ((1, 0) : ℤ × ℤ) + p.2 • ((0, 1) : ℤ × ℤ) := by
    ext <;> simp
  have hcoord : coord p = p.1 • coord (1, 0) + p.2 • coord (0, 1) :=
    (congrArg coord hp).trans (by simp only [map_add, map_zsmul])
  rw [hcoord]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, zsmul_eq_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private theorem limitIsIsoOfNonnegative {k : Type u} [Field k] (J : AffineAlgebraicGroup k)
    (hJ : IsReductive J) (T : ClosedSubgroup J.val) (hT : IsSplitTorus T.group)
    (d : Cocharacter T.group) (E : LimitDecomposition (d ≫ T.inclusion))
    (h : ∀ a : relativeRoots T, 0 ≤ pairing T.group a.val d) :
    IsIso E.parabolic.inclusion := by
  classical
  letI := hJ.1
  letI : ConnectedSpace J.val.X.left := connected_of_geometricallyConnected hJ.2.1
  apply isIso_of_closedImmersion_of_differential
    (A := closedSubgroupAlgebraicGroup E.parabolic) (B := J)
    E.parabolic.inclusion E.parabolic.isClosedImmersion
    (limitSubgroupsSmooth J _ E).1
    (connected_of_geometricallyConnected (geometricallyConnectedLimitSubgroups J _ E).1)
    hJ.1 (connected_of_geometricallyConnected hJ.2.1)
  apply Set.range_eq_univ.mp
  change lieImage E.parabolic = Set.univ
  let s := identityLieStructure J
  letI := s.lieRing
  letI := s.lieAlgebra
  rw [(limitLie_weightSpans J T hT d E s).1]
  have htop : (⨆ a : {a : Character T.group // 0 ≤ pairing T.group a d},
      CharacterPairing.adjointWeightSpace T a.val s) = ⊤ := by
    apply top_unique
    rw [← (adjointWeightsInternal J T hT s).submodule_iSup_eq_top]
    apply iSup_le
    intro a
    by_cases ha : 0 ≤ pairing T.group a d
    · exact le_iSup (fun a : {a : Character T.group // 0 ≤ pairing T.group a d} ↦
        CharacterPairing.adjointWeightSpace T a.val s) ⟨a, ha⟩
    have hz : CharacterPairing.adjointWeightSpace T a s = ⊥ := by
      by_contra hw
      have ha' : a ≠ 1 := fun he ↦ ha (he.symm ▸ (pairing_one _ hT d).ge)
      exact ha (h ⟨a, (RootData.CharacterPairing.absoluteRootWeights T s a).mpr ⟨ha', hw⟩⟩)
    rw [hz]
    exact bot_le
  rw [htop, Submodule.top_coe]

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private theorem highestLimitMaximal
    (hG : IsReductive G) (hmax : IsMaximalSplitTorus (subgroupOfSubgroup M.torus S))
    (coord : (ℤ × ℤ) →+ Additive (Character S.group))
    (hroots : relativeRoots (subgroupOfSubgroup M.torus S) =
      (fun p : ℤ × ℤ ↦ (coord p).toMul) ''
        (LieAlgebrasAndRepresentations.rankTwoCoefficients .G₂ : Set _))
    (c : Cocharacter S.group) (C : LimitDecomposition (c ≫ (subgroupOfSubgroup M.torus S).inclusion))
    (hweight : ∀ p ∈ LieAlgebrasAndRepresentations.rankTwoCoefficients .G₂,
      pairing S.group (coord p).toMul c = p.2) :
    ∀ Q : ClosedSubgroup G.val, IsParabolic G Q → IsSubgroupOf C.parabolic Q →
      IsSubgroupOf Q C.parabolic ∨ IsIso Q.inclusion := by
  let S₀ := subgroupOfSubgroup M.torus S
  letI := hG.1
  letI : ConnectedSpace G.val.X.left := connected_of_geometricallyConnected hG.2.1
  have hSC : IsSubgroupOf S₀ C.parabolic :=
    (Relative.RelativeChambers.limitParabolicThroughSplitTorus G hG S₀ hmax.1 c C).2
  intro Q hQ hCQ
  obtain ⟨d, E, hQE⟩ := Relative.RelativeChambers.parabolicThroughSplitTorus G S₀ hmax Q hQ
    (subgroupOf_trans hSC hCQ)
  have hCE := (limitParabolics_le G S₀ hmax.1 c d C E).mp (subgroupOf_trans hCQ hQE.1)
  have htest (p : ℤ × ℤ) (hp : p ∈ LieAlgebrasAndRepresentations.rankTwoCoefficients .G₂)
      (h : 0 ≤ p.2) : 0 ≤ pairing S.group (coord p).toMul d := by
    let a : relativeRoots S₀ := ⟨(coord p).toMul, hroots.symm ▸ ⟨p, hp, rfl⟩⟩
    exact hCE (a := a) (by
      change 0 ≤ pairing S.group (coord p).toMul c
      rw [hweight p hp]
      exact h)
  have hs := htest (1, 0) (by decide +kernel) (by decide)
  have hns := htest (-1, 0) (by decide +kernel) (by decide)
  have hl := htest (0, 1) (by decide +kernel) (by decide)
  rw [pairingInCoordinates (T := S.group) hmax.1 coord d (-1, 0)] at hns
  simp only [neg_mul, one_mul, zero_mul, add_zero] at hns
  have hs0 : pairing S.group (coord (1, 0)).toMul d = 0 := by omega
  have heval (p : ℤ × ℤ) : pairing S.group (coord p).toMul d =
      p.2 * pairing S.group (coord (0, 1)).toMul d := by
    rw [pairingInCoordinates (T := S.group) hmax.1 coord d p, hs0, mul_zero, zero_add]
  by_cases hl0 : pairing S.group (coord (0, 1)).toMul d = 0
  · haveI : IsIso E.parabolic.inclusion := limitIsIsoOfNonnegative G hG S₀ hmax.1 d E (by
      rintro ⟨a, ha⟩
      rw [hroots] at ha
      obtain ⟨p, hp, rfl⟩ := ha
      change 0 ≤ pairing S.group (coord p).toMul d
      rw [heval, hl0, mul_zero])
    obtain ⟨i, hi⟩ := hQE.2
    exact Or.inr (isIso_of_section Q (inv E.parabolic.inclusion ≫ i)
      (by rw [Category.assoc, hi, IsIso.inv_hom_id]))
  · left
    apply subgroupOf_trans hQE.1
    apply (limitParabolics_le G S₀ hmax.1 d c E C).mpr
    rintro ⟨a, ha⟩ h
    rw [hroots] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    change 0 ≤ pairing S.group (coord p).toMul d at h
    change 0 ≤ pairing S.group (coord p).toMul c
    rw [hweight p hp]
    rw [heval] at h
    exact nonneg_of_mul_nonneg_left h (lt_of_le_of_ne hl (Ne.symm hl0))

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private theorem commuteDescends (A B : ClosedSubgroup G.val)
    (h : ∀ (R : TestAlgebra K) (x : GroupPoints (extendSubgroup K A).group R)
      (y : GroupPoints (extendSubgroup K B).group R),
      Commute (x ≫ (extendSubgroup K A).inclusion.hom.hom :
        GroupPoints ((groupBaseChange F K).obj G.val) R)
        (y ≫ (extendSubgroup K B).inclusion.hom.hom :
          GroupPoints ((groupBaseChange F K).obj G.val) R)) :
    ∀ (R : TestAlgebra F) (x : GroupPoints A.group R) (y : GroupPoints B.group R),
      Commute (x ≫ A.inclusion.hom.hom : GroupPoints G.val R)
        (y ≫ B.inclusion.hom.hom : GroupPoints G.val R) := by
  intro R x y
  let E : TestAlgebra K := (extendScalars F K).obj R
  let E₀ := (restrictTestAlgebra F K).obj E
  let tensorInclusion : R →+* (R ⊗[F] K) :=
    (Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := R) (B := K)).toRingHom
  letI : Algebra F E₀ := E₀.algebra
  let f₀ : R →ₐ[F] E₀ :=
    { toRingHom := tensorInclusion
      commutes' a := by
        change (algebraMap F R a) ⊗ₜ[F] (1 : K) =
          (1 : R) ⊗ₜ[F] (algebraMap F K a)
        simpa only [Algebra.algebraMap_eq_smul_one] using
          (TensorProduct.smul_tmul (R := F) a (1 : R) (1 : K)) }
  let f : R ⟶ E₀ := ConcreteCategory.ofHom (C := CommAlgCat F) f₀
  have hf : Function.Injective f.hom := by
    change Function.Injective tensorInclusion
    exact Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F K).injective
  obtain ⟨x', hx⟩ := (baseChangePointGroupEquiv K A.group E).surjective (mapPoints f x)
  obtain ⟨y', hy⟩ := (baseChangePointGroupEquiv K B.group E).surjective (mapPoints f y)
  let j := (((groupPointsFunctor F).obj G.val).map f).hom
  have eqmap (C : ClosedSubgroup G.val) (p : GroupPoints C.group R)
      (q : GroupPoints (extendSubgroup K C).group E)
      (hq : baseChangePointGroupEquiv K C.group E q = mapPoints f p) :
      baseChangePointGroupEquiv K G.val E (q ≫ (extendSubgroup K C).inclusion.hom.hom) =
        j (p ≫ C.inclusion.hom.hom) := by
    have H := baseChangePointsSchemeNaturality F K C.inclusion.hom.hom E q
    change baseChangePointGroupEquiv K G.val E (q ≫ (extendSubgroup K C).inclusion.hom.hom) =
      baseChangePointGroupEquiv K C.group E q ≫ C.inclusion.hom.hom at H
    rw [H, hq]
    exact Category.assoc _ _ _
  have hx' := eqmap A x x' hx
  have hy' := eqmap B y y' hy
  have h' := ((h E x' y').map (baseChangePointGroupEquiv K G.val E)).eq
  change (x ≫ A.inclusion.hom.hom) * (y ≫ B.inclusion.hom.hom) =
    (y ≫ B.inclusion.hom.hom) * (x ≫ A.inclusion.hom.hom)
  exact mapPoints_injective G.property.1 f hf
    (by
      change j _ = j _
      simp only [map_mul]
      exact (congrArg₂ (· * ·) hx'.symm hy'.symm).trans
        (h'.trans (congrArg₂ (· * ·) hy' hx')))

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
set_option maxHeartbeats 500000 in
/-- The highest coroot defines the maximal standard parabolic with the
central simple root omitted. Its upper group centralizes the radical. -/
theorem centralUpperOfHighest
    (hG : IsReductive G) (hmax : IsMaximalSplitTorus (subgroupOfSubgroup M.torus S))
    (D : AttachedDatum P.pair) (U : RootSubgroupFamily P.pair.T)
    (simple : letI := D.comm; Fin 4 ≃ D.base.support)
    (cartan : letI := D.comm; ∀ i j,
      D.datum.rootDatum.pairing (simple j).val (simple i).val = D4Cartan i j)
    (t : multiplicativeGroup K ≅ (groupBaseChange F K).obj (multiplicativeGroup F))
    (ht : IsUnitComparison t)
    (restrict : Character P.pair.T.group →* Character S.group)
    (hr : IsRestriction S t restrict) (coeff : Root P.pair.T → Fin 4 → ℤ)
    (coord : (ℤ × ℤ) →+ Additive (Character S.group))
    (hf : Folding S P D simple restrict coeff coord)
    (b : Root P.pair.T) (H : RankOne (subgroupOfSubgroup M.torus S))
    (hH : letI := D.comm; H.MatchesAbsolute S P D U t (highestRootIndex D.datum.rootDatum D.base simple) b) :
    H.HasCentralUpper M.positive := by
  letI := D.comm
  letI := D.datum.finiteRoots
  let S₀ := subgroupOfSubgroup M.torus S
  let θ := highestRootIndex D.datum.rootDatum D.base simple
  obtain ⟨C, _, hC, _, hproper, _, _, _, hrad, _, hu, _⟩ :=
    oppositeRadicalsOfAbsolute hG D U t ht θ b H hH
  obtain ⟨_, ⟨_, _, huK, _⟩, hcor, _⟩ := hH
  have hθ : project (coeff θ) = (3, 2) :=
    (projectedDistinguishedRoots simple cartan coeff hf.1).2.2
  have hfold := hf
  obtain ⟨he, hp, _, _, _, hroots, hpositive, hall, _⟩ := hfold
  let c := H.cochar
  let d : Cocharacter P.pair.T.group := t.hom ≫ (groupBaseChange F K).map (c ≫ S.inclusion)
  have hsign (a : Root P.pair.T) : pairing P.pair.T.group a.val d = (project (coeff a)).2 := by
    rw [← D.datum.pairing_eq, ← D.datum.root_eq a]
    change D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root a) (Additive.ofMul d) = coeff a 1
    rw [hcor]
    exact highestCorootEval D.datum.rootDatum D.base simple cartan a (coeff a) (he a).symm
  have hcoordinate (a : Root P.pair.T) : (coord (project (coeff a))).toMul = restrict a.val :=
    congrArg Additive.toMul (hp a)
  have hroots' : relativeRoots S₀ = (fun p : ℤ × ℤ ↦ (coord p).toMul) ''
      (LieAlgebrasAndRepresentations.rankTwoCoefficients .G₂ : Set _) := by
    rw [← hall, hroots]
    ext χ
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨project (coeff a), ⟨a, rfl⟩, hcoordinate a⟩
    · rintro ⟨p, ⟨a, rfl⟩, h⟩
      exact ⟨a, (hcoordinate a).symm.trans h⟩
  have hweight (p : ℤ × ℤ) (hp' : p ∈ LieAlgebrasAndRepresentations.rankTwoCoefficients .G₂) :
      pairing S.group (coord p).toMul c = p.2 := by
    change p ∈ (LieAlgebrasAndRepresentations.rankTwoCoefficients .G₂ : Set _) at hp'
    rw [← hall] at hp'
    obtain ⟨a, rfl⟩ := hp'
    rw [hcoordinate, pairingOfRestriction t ht restrict hr, hsign]
  let J := P.pair.G
  let T := P.pair.T
  let E := groupBaseChange F K
  have hco : d ≫ T.inclusion = t.hom ≫ E.map (c ≫ S₀.inclusion) := by
    change (t.hom ≫ E.map (c ≫ S.inclusion)) ≫ E.map M.torus.inclusion = _
    rw [Category.assoc, ← E.map_comp, Category.assoc]
    rfl
  obtain ⟨C'⟩ := existsLimitDecomposition J (d ≫ T.inclusion)
  let C'' : LimitDecomposition (t.hom ≫ E.map (c ≫ S₀.inclusion)) := hco ▸ C'
  obtain ⟨hPK, hUK, _⟩ := limits_subgroups_extend G C t ht C''
  change SameSubgroup C''.parabolic (extendSubgroup K C.parabolic) at hPK
  change SameSubgroup C''.contracting (extendSubgroup K C.contracting) at hUK
  have hPK' : SameSubgroup C'.parabolic (extendSubgroup K C.parabolic) := by
    simpa only [C'', parabolic_of_cast] using hPK
  have hUK' : SameSubgroup C'.contracting (extendSubgroup K C.contracting) := by
    simpa only [C'', contracting_of_cast] using hUK
  have hB : IsSubgroupOf M.positive C.parabolic := by
    apply subgroupOf_of_extend (K := K)
    apply subgroupOf_trans _ hPK'.1
    obtain ⟨hs, hc⟩ := kBorel_smooth_connected J P.pair.B P.borel
    apply subgroupOf_limit_of_rootSigns J P.reductive T P.pair.B P.split P.maximal
      hs hc P.containsTorus d C'
    intro a ha
    have hn : ∀ p : ↥positiveCoordinates, 0 ≤ p.val.2 := by decide +kernel
    have hmem : project (coeff a) ∈ (positiveCoordinates : Set _) := by
      rw [← hpositive]
      exact ⟨a, ha, rfl⟩
    rw [hsign]
    exact hn ⟨_, hmem⟩
  let V := contractingSubgroup C
  have hV : (subgroupOfSubgroup C.parabolic V).inclusion = C.contracting.inclusion :=
    C.contracting_in_G
  refine ⟨C.parabolic, V, hC, hB, hproper, highestLimitMaximal hG hmax coord hroots' c C hweight,
    hrad.1, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hu
    exact ⟨i, by rw [hV, hi]⟩
  · intro R x y
    have comm := commuteDescends (K := K) H.positive C.contracting (by
      intro W x' y'
      obtain ⟨i, hi⟩ := huK.1
      obtain ⟨j, hj⟩ := hUK'.2
      have hx : (x' ≫ i.hom.hom) ≫ (U θ).val.inclusion.hom.hom =
          x' ≫ (extendSubgroup K H.positive).inclusion.hom.hom := by
        rw [Category.assoc, ← Grp.comp_hom_hom, hi]
        rfl
      have hy : (y' ≫ j.hom.hom) ≫ C'.contracting.inclusion.hom.hom =
          y' ≫ (extendSubgroup K C.contracting).inclusion.hom.hom := by
        rw [Category.assoc, ← Grp.comp_hom_hom, hj]
      rw [← hx, ← hy]
      obtain ⟨l, hl⟩ := has_enumeration (positiveRoots T d)
      obtain ⟨e, he'⟩ := ((RootData.OrderedRootProducts.contractingProduct
        J P.reductive T P.split P.maximal).2.2 d).2 C' U l hl
      let p := (y' ≫ j.hom.hom) ≫ e.inv
      have hp' : p ≫ rootProduct U l = (y' ≫ j.hom.hom) ≫ C'.contracting.inclusion.hom.hom := by
        simp only [p, ← he', Category.assoc, Iso.inv_hom_id_assoc]
      rw [← hp']
      apply commuteRootProduct
      intro a ha z
      apply highestRootCommutesWithPositive D simple restrict coeff coord hf θ hθ a _ U W
      have hz : 0 < pairing T.group a.val d := (hl.2 a).mp ha
      rw [hsign] at hz
      have hab : D.base.IsPos a := by
        letI := D.datum.reduced
        let index := signedIndex D.datum.rootDatum D.base simple cartan a
        have heq : coeff a = signedD4 index :=
          expand_injective D.datum.rootDatum D.base simple
            ((he a).symm.trans (signedIndex_expand D.datum.rootDatum D.base simple cartan a).symm)
        have hx : ∀ i : Fin 12 × Bool, 0 < (project (signedD4 i)).2 → i.2 = true := by decide +kernel
        rw [heq] at hz
        rw [D.base.isPos_iff,
          height_eq D.datum.rootDatum D.base simple a _ (he a).symm, heq]
        exact (positive_signed index).2 (hx index hz)
      exact (attachedPositive P.pair D a).mp hab) R x y
    change Commute (x ≫ H.positive.inclusion.hom.hom : GroupPoints G.val R)
      (y ≫ V.inclusion.hom.hom ≫ C.parabolic.inclusion.hom.hom : GroupPoints G.val R)
    have hv : V.inclusion ≫ C.parabolic.inclusion = C.contracting.inclusion := hV
    rw [← Grp.comp_hom_hom, hv]
    exact comm

end HighestRootCentrality

section RankOneTransport

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open Specs.Arithmetic.TrialitarianRelativeRoots (RankOne)
open RootGroups (rootPoint)
open CocharacterDynamics (cocharacterPoint)
open private conjugationIso comp_conjugation from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private pushSubgroup cocharacterPoint_postcompose
  from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups
open private mono_over from LinearAlgebraicGroups.Affine.Stabilizers

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F} {S : ClosedSubgroup G.val}

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- Conjugation by a rational point which preserves the specified torus
transports the scheme embedding, the elementary coordinates, and its diagonal. -/
noncomputable def conjugateRankOne (L : RankOne S) (g : 𝟙_ (SchemeOver F) ⟶ G.val.X)
    (s : S.group ≅ S.group)
    (hs : s.hom ≫ S.inclusion = S.inclusion ≫ (conjugationIso g).hom) : RankOne S := by
  let e := conjugationIso g
  have hclosed : IsClosedImmersion (L.embedding ≫ e.hom).hom.hom.left := by
    letI := L.closedEmbedding
    letI : IsIso e.hom.hom.hom.left :=
      (Grp.forget (SchemeOver F) ⋙ Over.forget _).map_isIso e.hom
    exact IsClosedImmersion.comp _ _
  refine
    { group := L.group
      matrix := L.matrix
      embedding := L.embedding ≫ e.hom
      closedEmbedding := hclosed
      trivialKernel := ?_
      positive := pushSubgroup e L.positive
      negative := pushSubgroup e L.negative
      additive := L.additive
      upper := L.upper
      lower := L.lower
      cochar := L.cochar ≫ s.hom
      upperFormula := ?_
      lowerFormula := ?_
      diagonalFormula := ?_ }
  · letI := mono_over _ hclosed
    apply IsPullback.of_vert_isIso_mono
    exact ⟨by rw [Category.id_comp, IsMonHom.one_hom]⟩
  · intro R a
    change (_ ≫ L.embedding.hom.hom) ≫ e.hom.hom.hom =
      rootPoint (L.upper.hom ≫ L.positive.inclusion ≫ e.hom) R a
    rw [L.upperFormula R a, ← rootPoint_comp, Category.assoc]
  · intro R a
    change (_ ≫ L.embedding.hom.hom) ≫ e.hom.hom.hom =
      rootPoint (L.lower.hom ≫ L.negative.inclusion ≫ e.hom) R a
    rw [L.lowerFormula R a, ← rootPoint_comp, Category.assoc]
  · intro R a
    obtain ⟨z, hz, hm⟩ := L.diagonalFormula R a
    refine ⟨z, ?_, hm⟩
    change (z ≫ L.embedding.hom.hom) ≫ e.hom.hom.hom =
      cocharacterPoint ((L.cochar ≫ s.hom) ≫ S.inclusion) R a
    rw [hz, ← cocharacterPoint_postcompose, Category.assoc L.cochar s.hom, hs, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem conjugateRankOne_isTransport (L : RankOne S) (g : 𝟙_ (SchemeOver F) ⟶ G.val.X)
    (s : S.group ≅ S.group)
    (hs : s.hom ≫ S.inclusion = S.inclusion ≫ (conjugationIso g).hom) :
    L.IsTransport (conjugateRankOne L g s hs) g := by
  refine ⟨Iso.refl _, ?_, ?_⟩
  · simp [conjugateRankOne]
  · change ((𝟙 L.group.val) ≫ (L.embedding ≫ (conjugationIso g).hom)).hom.hom = _
    rw [Category.id_comp]
    change L.embedding.hom.hom ≫ (conjugationIso g).hom.hom.hom = _
    exact comp_conjugation g L.embedding.hom.hom

end RankOneTransport

section RationalWeyl

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open AbstractPairing (Root)
open CharacterDescent (Character)
open DatumAndWeyl (Identification)
open GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.GeometricRadicals (IsReductive baseChangedSubgroup)
open QuasiSplitPinnedPairModel (BorelPair)
open Pinning (AttachedDatum)
open Specs.Arithmetic.TrialitarianRelativeRoots (AbsolutePair IsRestriction Folding)
open Specs.Arithmetic.QuasiSplitFixedWeyl
  (multiplicativeGroup IsLargestSplitSubtorus fixedWeyl)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus IsMinimalParabolic)
open Specs.Relative.RelativeWeylScheme (QuotientData rationalProjection)
open SchemeDerivedGroup (IsSubgroupOf)
open private relativeFixedComparison scalarDatumAction scalarDatum_isScalarAction
  groupBaseChange_injective from LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
open private conjugatesSplitTorusOfGeometricLabel from LinearAlgebraicGroups.Relative.RelativeWeylScheme
open private labelConjugation from LinearAlgebraicGroups.RootData.DatumAndWeyl
open private conjugationIso conjugate comp_conjugate
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private scalarExtendedPoint_natural from LinearAlgebraicGroups.RootData.RankOneFlag
open private multiplicativeBaseChange from LinearAlgebraicGroups.Relative.RationalCocharacter

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  {G : AffineAlgebraicGroup F} {M : BorelPair G} {S : ClosedSubgroup M.torus.group} {P : AbsolutePair K M}

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private theorem compatibleNormalizerConjugations (D : AttachedDatum P.pair) :
    letI := D.comm
    ∀ (W : Identification D.datum)
      (Q : QuotientData (subgroupOfSubgroup M.torus S)) (w : Q.splitImage.labels)
      (n : 𝟙_ (SchemeOver F) ⟶ Q.normalizer.group.X)
      (_ : rationalProjection Q n = Q.splitImage.constantGroup.sectionPoint w)
      (v : D.datum.rootDatum.weylGroup)
      (r : 𝟙_ (SchemeOver K) ⟶ W.normalizer.group.X)
      (_ : r ≫ W.normalizer.inclusion.hom.hom =
        scalarExtendedRationalPoint K (n ≫ Q.normalizer.inclusion.hom.hom))
      (_ : r ≫ W.quotient.hom.hom = W.image.constantGroup.sectionPoint (W.labelEquiv v)),
      (groupBaseChange F K).map (Q.splitImage.conjugation w).hom ≫
        (groupBaseChange F K).map S.inclusion =
      (groupBaseChange F K).map S.inclusion ≫ (W.image.conjugation (W.labelEquiv v)).hom := by
  letI := D.comm
  intro W Q w n hn v r hr hv
  let E := groupBaseChange F K
  let e := Q.splitImage.conjugation w
  let f := W.image.conjugation (W.labelEquiv v)
  let g := r ≫ W.normalizer.inclusion.hom.hom
  let i := E.map S.inclusion
  let j := E.map M.torus.inclusion
  have ht : f.hom ≫ j = j ≫ (conjugationIso g).hom := by
    apply Grp.hom_ext
    change _ = j.hom.hom ≫ conjugate g (𝟙 _)
    rw [comp_conjugate, Category.comp_id]
    exact labelConjugation W.image (W.labelEquiv v) r hv
  have hs : E.map e.hom ≫ i ≫ j = (i ≫ j) ≫ (conjugationIso g).hom := by
    let nK := scalarExtendedRationalPoint K n
    have hpro : nK ≫ (E.map Q.projection).hom.hom =
        scalarExtendedRationalPoint K (Q.splitImage.constantGroup.sectionPoint w) := by
      exact (scalarExtendedPoint_natural K n Q.projection.hom.hom).symm.trans
        (congrArg (scalarExtendedRationalPoint K) hn)
    have hgn : nK ≫ (E.map Q.normalizer.inclusion).hom.hom = g :=
      (scalarExtendedPoint_natural K n Q.normalizer.inclusion.hom.hom).symm.trans hr.symm
    have h := conjugatesSplitTorusOfGeometricLabel Q w K nK hpro
    change E.map e.hom ≫ E.map (S.inclusion ≫ M.torus.inclusion) =
      E.map (S.inclusion ≫ M.torus.inclusion) ≫
        (conjugationIso (nK ≫ (E.map Q.normalizer.inclusion).hom.hom)).hom at h
    rw [hgn, E.map_comp] at h
    exact h
  change E.map e.hom ≫ i = i ≫ f.hom
  letI : IsClosedImmersion j.hom.hom.left := P.torusClosed
  letI : Mono j.hom.hom := Over.mono_of_mono_left _
  letI : Mono j := (Grp.forget (SchemeOver K)).mono_of_mono_map (show Mono j.hom.hom from inferInstance)
  apply (cancel_mono j).mp
  calc
    (E.map e.hom ≫ i) ≫ j = E.map e.hom ≫ i ≫ j := Category.assoc _ _ _
    _ = (i ≫ j) ≫ (conjugationIso g).hom := hs
    _ = i ≫ (j ≫ (conjugationIso g).hom) := Category.assoc _ _ _
    _ = i ≫ (f.hom ≫ j) := congrArg (i ≫ ·) ht.symm
    _ = (i ≫ f.hom) ≫ j := (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private theorem restrictionIntertwinesNormalizer (D : AttachedDatum P.pair) :
    letI := D.comm
    ∀ (W : Identification D.datum)
      (Q : QuotientData (subgroupOfSubgroup M.torus S)) (w : Q.splitImage.labels)
      (n : 𝟙_ (SchemeOver F) ⟶ Q.normalizer.group.X)
      (_ : rationalProjection Q n = Q.splitImage.constantGroup.sectionPoint w)
      (v : D.datum.rootDatum.weylGroup)
      (r : 𝟙_ (SchemeOver K) ⟶ W.normalizer.group.X)
      (_ : r ≫ W.normalizer.inclusion.hom.hom =
        scalarExtendedRationalPoint K (n ≫ Q.normalizer.inclusion.hom.hom))
      (_ : r ≫ W.quotient.hom.hom = W.image.constantGroup.sectionPoint (W.labelEquiv v))
      (t : multiplicativeGroup K ≅ (groupBaseChange F K).obj (multiplicativeGroup F))
      (restrict : Character P.pair.T.group →* Character S.group) (_ : IsRestriction S t restrict)
      (a : Root P.pair.T), w.val (restrict a.val) = restrict (v.val.indexEquiv a).val := by
  letI := D.comm
  intro W Q w n hn v r hr hv t restrict hres a
  let E := groupBaseChange F K
  let e := Q.splitImage.conjugation w
  let f := W.image.conjugation (W.labelEquiv v)
  let i := E.map S.inclusion
  have he : E.map e.hom ≫ i = i ≫ f.hom :=
    compatibleNormalizerConjugations D W Q w n hn v r hr hv
  have hei : E.map e.inv ≫ i = i ≫ f.inv := by
    apply (cancel_mono f.hom).mp
    rw [Category.assoc, ← he, ← Category.assoc, ← E.map_comp, Iso.inv_hom_id, E.map_id,
      Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hW : f.inv ≫ a.val = (v.val.indexEquiv a).val := by
    have h := RootPairing.Hom.root_weightMap_apply D.datum.rootDatum D.datum.rootDatum a v.val.toHom
    change v.val.weightEquiv (D.datum.rootDatum.root a) =
      D.datum.rootDatum.root (v.val.indexEquiv a) at h
    rw [D.datum.root_eq, D.datum.root_eq, W.characterAction, W.image.characterAction] at h
    exact congrArg Additive.toMul h
  apply groupBaseChange_injective (F := F) (K := K)
  rw [Q.splitImage.characterAction]
  change E.map (e.inv ≫ restrict a.val) = E.map (restrict (v.val.indexEquiv a).val)
  have hrestrict (χ : Character P.pair.T.group) : E.map (restrict χ) = i ≫ χ ≫ t.hom :=
    hres χ
  calc
    _ = (E.map e.inv ≫ i) ≫ a.val ≫ t.hom := by
      rw [E.map_comp, hrestrict a.val, Category.assoc]
    _ = i ≫ (f.inv ≫ a.val) ≫ t.hom := by rw [hei, Category.assoc, Category.assoc f.inv]
    _ = E.map (restrict (v.val.indexEquiv a).val) := by rw [hW, hrestrict]

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- The fixed reflection can be lifted to a rational normalizer section
having the required effect on the restricted character. -/
theorem highestRootRationalRepresentative [IsGalois F K]
    (hG : IsReductive G) (hS : IsLargestSplitSubtorus S)
    (hmax : IsMaximalSplitTorus (subgroupOfSubgroup M.torus S))
    (hB : IsMinimalParabolic G M.positive)
    (hSB : IsSubgroupOf (subgroupOfSubgroup M.torus S) M.positive)
    (hC : RepresentsSubgroup M.torus
      (fun _ g ↦ Centralizes (subgroupOfSubgroup M.torus S).inclusion g))
    (D : AttachedDatum P.pair) (W : letI := D.comm; Identification D.datum)
    (simple : letI := D.comm; Fin 4 ≃ D.base.support)
    (cartan : letI := D.comm; ∀ i j,
      D.datum.rootDatum.pairing (simple j).val (simple i).val = D4Cartan i j)
    (restrict : Character P.pair.T.group →* Character S.group)
    (coeff : Root P.pair.T → Fin 4 → ℤ) (coord : (ℤ × ℤ) →+ Additive (Character S.group))
    (hres : IsRestriction S (multiplicativeBaseChange F K) restrict)
    (hf : Folding S P D simple restrict coeff coord) :
    letI := D.comm
    ∃ (Q : QuotientData (subgroupOfSubgroup M.torus S)) (w : Q.splitImage.labels)
      (n : 𝟙_ (SchemeOver F) ⟶ Q.normalizer.group.X)
      (v : D.datum.rootDatum.weylGroup) (r : 𝟙_ (SchemeOver K) ⟶ W.normalizer.group.X),
      rationalProjection Q n = Q.splitImage.constantGroup.sectionPoint w ∧
      r ≫ W.normalizer.inclusion.hom.hom =
        scalarExtendedRationalPoint K (n ≫ Q.normalizer.inclusion.hom.hom) ∧
      r ≫ W.quotient.hom.hom = W.image.constantGroup.sectionPoint (W.labelEquiv v) ∧
      v.val.indexEquiv (simple 1).val = highestRootIndex D.datum.rootDatum D.base simple ∧
      w.val (restrict (simple 1).val.val) =
        restrict (highestRootIndex D.datum.rootDatum D.base simple).val := by
  letI := D.comm
  letI : IsCommMonObj (baseChangedSubgroup K M.torus P.torusClosed).group.X := D.comm
  let ρ := scalarDatumAction (hT := P.torusClosed) W P.split
  have ha := scalarDatum_isScalarAction (hT := P.torusClosed) W P.split
  obtain ⟨v, hv⟩ := highestRootFixedReflection simple cartan
    (multiplicativeBaseChange F K) ρ ha restrict hres coeff coord hf
  obtain ⟨Q, _⟩ := Relative.RelativeWeylScheme.finiteConstantQuotient G hG
    (subgroupOfSubgroup M.torus S) hmax
  obtain ⟨e, _, hn, hr⟩ := relativeFixedComparison (hT := P.torusClosed) W P.split
    hG S hS M.positive hmax hB hSB hC Q
  obtain ⟨w, rfl⟩ := e.surjective v
  obtain ⟨n, hn'⟩ := hn w
  obtain ⟨r, hG', hr'⟩ := hr n w hn'
  refine ⟨Q, w, n, (e w).val, r, hn', hG', hr', hv, ?_⟩
  rw [restrictionIntertwinesNormalizer D W Q w n hn' (e w).val r hG' hr' _
    restrict hres (simple 1).val, hv]

end RationalWeyl

section AbsoluteMarkings

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open AbstractPairing (Root)
open BruhatOrbitParametrization (IsRepresentative)
open CharacterDescent (Cocharacter)
open DatumAndWeyl (Identification)
open GeometricBorelConjugacy (ConjugatesSubgroups subgroupOfSubgroup)
open GeometricRadicals (baseChangedSubgroup)
open OrderedRootProducts (RootSubgroupFamily)
open Pinning (AttachedDatum)
open QuasiSplitPinnedPairModel (BorelPair)
open RankOneFlag (SameSubgroup)
open Specs.Arithmetic.TrialitarianRelativeRoots (AbsolutePair RankOne)
open Specs.Arithmetic.QuasiSplitFixedWeyl (multiplicativeGroup)
open Specs.Relative.RelativeWeylScheme (QuotientData rationalProjection)
open private conjugationIso comp_conjugation conjugates_iff_iso
  from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private pushSubgroup from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private labelConjugation from LinearAlgebraicGroups.RootData.DatumAndWeyl
open private conjugates_baseChange same_conjugate_subgroups
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private conjugates_inverse conjugates_of_same
  from LinearAlgebraicGroups.RootData.BorelNormalizer
open private subgroupOf_trans from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private extendSubgroup from LinearAlgebraicGroups.RootData.RankOneFlag
open private innerIso transportSubgroup comp_innerMap from LinearAlgebraicGroups.Reductive.BorelProper
open private representative_transports_root from LinearAlgebraicGroups.Flag.SimpleParabolicProduct

variable {F K : Type u} [Field F] [Field K] [Algebra F K] {G : AffineAlgebraicGroup F}
  {M : BorelPair G} {S : ClosedSubgroup M.torus.group} {P : AbsolutePair K M}

set_option backward.isDefEq.respectTransparency false in
private theorem rationalNormalizerConjugation
    (Q : QuotientData (subgroupOfSubgroup M.torus S)) (w : Q.splitImage.labels)
    (n : 𝟙_ (SchemeOver F) ⟶ Q.normalizer.group.X)
    (hn : rationalProjection Q n = Q.splitImage.constantGroup.sectionPoint w) :
    (Q.splitImage.conjugation w).hom ≫ (subgroupOfSubgroup M.torus S).inclusion =
      (subgroupOfSubgroup M.torus S).inclusion ≫
        (conjugationIso (n ≫ Q.normalizer.inclusion.hom.hom)).hom := by
  apply Grp.hom_ext
  let T := subgroupOfSubgroup M.torus S
  let g := n ≫ Q.normalizer.inclusion.hom.hom
  change ((Q.splitImage.conjugation w).hom ≫ T.inclusion).hom.hom =
    T.inclusion.hom.hom ≫ (conjugationIso g).hom.hom.hom
  exact (labelConjugation Q.splitImage w n hn).trans
    (comp_conjugation g T.inclusion.hom.hom).symm

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private theorem conjugateAbsoluteRoot (D : AttachedDatum P.pair) :
    letI := D.comm
    ∀ (W : Identification D.datum) (U : RootSubgroupFamily P.pair.T)
      (v : D.datum.rootDatum.weylGroup)
      (r : 𝟙_ (SchemeOver K) ⟶ W.normalizer.group.X) (_ : IsRepresentative W v r)
      (g : 𝟙_ (SchemeOver F) ⟶ G.val.X)
      (_ : r ≫ W.normalizer.inclusion.hom.hom = scalarExtendedRationalPoint K g)
      (a : Root P.pair.T) {A B : ClosedSubgroup G.val} (_ : ConjugatesSubgroups g A B)
      (_ : ∃ hA, SameSubgroup (baseChangedSubgroup K A hA) (U a).val),
      ∃ hB, SameSubgroup (baseChangedSubgroup K B hB) (U (v.val.indexEquiv a)).val := by
  letI := D.comm
  intro W U v r hv g hr a A B hg ha
  let gK := r ≫ W.normalizer.inclusion.hom.hom
  obtain ⟨_, ha⟩ := ha
  have hA : SameSubgroup (extendSubgroup K A) (U a).val := ha
  have hB : ConjugatesSubgroups gK (extendSubgroup K A) (extendSubgroup K B) := by
    change ConjugatesSubgroups (r ≫ W.normalizer.inclusion.hom.hom) _ _
    rw [hr]
    exact conjugates_baseChange K hg
  have hB' : ConjugatesSubgroups gK (U a).val (extendSubgroup K B) := by
    have h := conjugates_of_same (conjugates_inverse hB) hA
    simpa only [inv_inv] using conjugates_inverse h
  let V := transportSubgroup (U a).val (innerIso gK)
  have hV : RootGroups.IsRootSubgroup P.pair.T V (v.val.indexEquiv a).val :=
    representative_transports_root W hv a (U a).property
  have hV' : ConjugatesSubgroups gK (U a).val V := by
    refine ⟨Iso.refl _, ?_⟩
    change ((𝟙 (U a).val.group) ≫ ((U a).val.inclusion ≫ (innerIso gK).hom)).hom.hom = _
    rw [Category.id_comp]
    exact comp_innerMap gK _
  let b := v.val.indexEquiv a
  obtain ⟨_, _, Z, _, _, _, _, hZ⟩ :=
    (RootData.RootGroups.rootSubgroups P.pair.G P.reductive P.pair.T P.split P.maximal).2
      b.val b.property
  let hVU : SameSubgroup V (U b).val :=
    ⟨subgroupOf_trans (hZ V hV).2 (hZ (U b).val (U b).property).1,
     subgroupOf_trans (hZ (U b).val (U b).property).2 (hZ V hV).1⟩
  exact ⟨(extendSubgroup K B).isClosedImmersion,
    same_conjugate_subgroups hB' (conjugates_of_same hV' hVU)⟩


private theorem conjugatesPushedSubgroup (A : ClosedSubgroup G.val)
    (g : 𝟙_ (SchemeOver F) ⟶ G.val.X) :
    ConjugatesSubgroups g A (pushSubgroup (conjugationIso g) A) :=
  (conjugates_iff_iso g _ _).mpr ⟨Iso.refl _, Category.id_comp _⟩

end AbsoluteMarkings

section TransportedRankOne

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open AbstractPairing (Root)
open BruhatOrbitParametrization (IsRepresentative)
open CharacterDescent (Cocharacter)
open DatumAndWeyl (Identification)
open GeometricBorelConjugacy (ConjugatesSubgroups subgroupOfSubgroup)
open OrderedRootProducts (RootSubgroupFamily)
open Pinning (AttachedDatum)
open QuasiSplitPinnedPairModel (BorelPair)
open Specs.Arithmetic.TrialitarianRelativeRoots (AbsolutePair RankOne)
open Specs.Arithmetic.QuasiSplitFixedWeyl (multiplicativeGroup)
open private conjugationIso from LinearAlgebraicGroups.Descent.FiniteFieldFlags

variable {F K : Type u} [Field F] [Field K] [Algebra F K] {G : AffineAlgebraicGroup F}
  {M : BorelPair G} {S : ClosedSubgroup M.torus.group} {P : AbsolutePair K M}

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private theorem transportAbsoluteMarkings (D : AttachedDatum P.pair) :
    letI := D.comm
    ∀ (W : Identification D.datum) (U : RootSubgroupFamily P.pair.T)
      (v : D.datum.rootDatum.weylGroup)
      (r : 𝟙_ (SchemeOver K) ⟶ W.normalizer.group.X) (_ : IsRepresentative W v r)
      (g : 𝟙_ (SchemeOver F) ⟶ G.val.X)
      (_ : r ≫ W.normalizer.inclusion.hom.hom = scalarExtendedRationalPoint K g)
      (s : S.group ≅ S.group)
      (hs : s.hom ≫ (subgroupOfSubgroup M.torus S).inclusion =
        (subgroupOfSubgroup M.torus S).inclusion ≫ (conjugationIso g).hom)
      (_ : (groupBaseChange F K).map s.hom ≫ (groupBaseChange F K).map S.inclusion =
        (groupBaseChange F K).map S.inclusion ≫ (W.image.conjugation (W.labelEquiv v)).hom)
      (t : multiplicativeGroup K ≅ (groupBaseChange F K).obj (multiplicativeGroup F))
      (a b : Root P.pair.T) (L : RankOne (subgroupOfSubgroup M.torus S)),
      L.MatchesAbsolute S P D U t a b →
      (conjugateRankOne L g s hs).MatchesAbsolute S P D U t
        (v.val.indexEquiv a) (v.val.indexEquiv b) := by
  letI := D.comm
  intro W U v r hv g hr s hs he t a b L hL
  let E := groupBaseChange F K
  let H := conjugateRankOne L g s hs
  let R := D.datum.rootDatum
  let e := W.image.conjugation (W.labelEquiv v)
  let y (J : RankOne (subgroupOfSubgroup M.torus S)) : Cocharacter P.pair.T.group :=
    t.hom ≫ E.map (J.cochar ≫ S.inclusion)
  obtain ⟨hneg, ⟨hpc, hnc, hp, hn⟩, hc, f, hf⟩ := hL
  have hpositive : ConjugatesSubgroups g L.positive H.positive :=
    conjugatesPushedSubgroup L.positive g
  have hnegative : ConjugatesSubgroups g L.negative H.negative :=
    conjugatesPushedSubgroup L.negative g
  obtain ⟨hp', hpos⟩ := conjugateAbsoluteRoot D W U v r hv g hr a hpositive ⟨hpc, hp⟩
  obtain ⟨hn', hnegSub⟩ := conjugateAbsoluteRoot D W U v r hv g hr b hnegative ⟨hnc, hn⟩
  have hnegativeRoot : R.root (v.val.indexEquiv b) = -R.root (v.val.indexEquiv a) := by
    change R.root (R.weylGroupToPerm v b) = -R.root (R.weylGroupToPerm v a)
    rw [← R.weylGroup_apply_root v b, ← R.weylGroup_apply_root v a, hneg, smul_neg]
  have hy : y H = y L ≫ e.hom := by
    change t.hom ≫ E.map ((L.cochar ≫ s.hom) ≫ S.inclusion) = _
    calc
      _ = (t.hom ≫ E.map L.cochar) ≫ (E.map s.hom ≫ E.map S.inclusion) := by
        simp only [Functor.map_comp, Category.assoc]
      _ = y L ≫ e.hom := by
        rw [he]
        simp only [y, e, E, Functor.map_comp, Category.assoc]
  have hy' : Additive.ofMul (y H) = v.val.coweightEquiv.symm (Additive.ofMul (y L)) := by
    rw [hy]
    exact (W.cocharacterAction v (y L)).symm
  have hcoroot : v.val.coweightEquiv.symm (R.coroot a) = R.coroot (v.val.indexEquiv a) := by
    apply v.val.coweightEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    have h := RootPairing.Hom.coroot_coweightMap_apply R R (v.val.indexEquiv a) v.val.toHom
    simpa using h.symm
  refine ⟨hnegativeRoot, ⟨hp', hn', hpos, hnegSub⟩, ?_, ?_⟩
  · change Additive.ofMul (y H) = _
    rw [hy', show Additive.ofMul (y L) = R.coroot a from hc, hcoroot]
  · refine ⟨f.comp v.val.coweightEquiv.toLinearMap, ?_⟩
    change f (v.val.coweightEquiv (Additive.ofMul (y H))) = 1
    rw [hy', LinearEquiv.apply_symm_apply]
    exact hf

end TransportedRankOne

section Assembly

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open AbstractPairing (Root)
open AbsoluteDynkinTypes (D4Outer PreservesCartan)
open Pinning (SimpleRoot)
open QuasiSplitOrbitDerivedRoots (diagramRoot)
open QuasiSplitOrbitLevis (simplePermutation)
open Specs.Arithmetic.TrialitarianPinnedBorelPair (underlyingAction)
open Specs.Arithmetic.TrialitarianRelativeRoots
open Specs.Arithmetic.QuasiSplitFixedWeyl (IsUnitComparison)
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology (restriction)
open private multiplicativeBaseChange multiplicativeBaseChange_unit
  from LinearAlgebraicGroups.Relative.RationalCocharacter

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
set_option maxHeartbeats 800000 in
/-- The quasi-split trialitarian group has reduced relative roots of type G₂
and a split highest-root SL₂ with the two opposite contracting radicals. -/
theorem trialitarianRelativeRoots : Statement.{u} := by
  classical
  intro F _ _ _ _ G hG hsc htrial hqs
  obtain ⟨ref, htransRef⟩ := htrial
  obtain ⟨K, M, S, hS, hmax, hC, hB, hSB, P, D, hdata⟩ :=
    TrialitarianPinnedBorelPair.pinnedBorelPair G hG hsc hqs
      ref.sequence ref.splitIso ref.relativeIso ref.induced
  letI := D.comm
  obtain ⟨W, A, U, pin, a, m, ω, j, hcoord, hm, hpin, haction, hjCartan, hjAction⟩ := hdata
  let simple : Fin 4 ≃ D.base.support := ref.simple.trans j
  let ρ := underlyingAction D ω
  have hcartan (i j' : Fin 4) :
      D.datum.rootDatum.pairing (simple j').val (simple i).val = D4Cartan i j' :=
    (hjCartan (ref.simple i) (ref.simple j')).trans (ref.cartan i j')
  have hstable (σ : Gal(K/F)) (α : Root P.pair.T) :
      (ρ σ).indexEquiv α ∈ D.base.support ↔ α ∈ D.base.support := by
    let support : Set (Root P.pair.T) := D.base.support
    change (ρ σ).indexEquiv α ∈ support ↔ α ∈ support
    have he : (ρ σ).indexEquiv '' support = support :=
      (ω σ).asIso.hom.property
    constructor
    · intro h
      rw [← he] at h
      obtain ⟨β, hβ, eq⟩ := h
      exact ((ρ σ).indexEquiv.injective eq) ▸ hβ
    · intro h
      rw [← he]
      exact ⟨α, h, rfl⟩
  have hcentral (σ : Gal(K/F)) :
      (ρ σ).indexEquiv (simple 1).val = (simple 1).val := by
    let perm := simple.trans ((simplePermutation D (ω σ)).trans simple.symm)
    have hperm (i : Fin 4) : (simple (perm i)).val = (ρ σ).indexEquiv (simple i).val := by
      exact congrArg Subtype.val (simple.apply_symm_apply (simplePermutation D (ω σ) (simple i)))
    have hp : PreservesCartan D4Cartan D4Cartan perm := by
      intro i j'
      change Fin 4 at i j'
      calc
        _ = D.datum.rootDatum.pairing (simple j').val (simple i).val := (hcartan i j').symm
        _ = D.datum.rootDatum.pairing ((ρ σ).indexEquiv (simple j').val)
              ((ρ σ).indexEquiv (simple i).val) := ((ρ σ).toHom.pairing).symm
        _ = D.datum.rootDatum.pairing (simple (perm j')).val (simple (perm i)).val :=
          congrArg₂ D.datum.rootDatum.pairing (hperm j').symm (hperm i).symm
        _ = _ := hcartan (perm i) (perm j')
    exact (hperm 1).symm.trans (congrArg (fun i => (simple i).val)
      ((RootData.AbsoluteDynkinTypes.d4Permutations perm).mp hp))
  have htrans (i j' : D4Outer) : ∃ σ : Gal(K/F),
      (ρ σ).indexEquiv (simple i.val).val = (simple j'.val).val := by
    obtain ⟨σ, hσ⟩ := htransRef i j'
    have hσ' : simplePermutation ref.datum
        (QuasiSplitInnerForms.outerHom ref.sequence
          (RelativeFormComparison.transportedAut F (SeparableClosure F) ref.relativeIso σ))
        (ref.simple i.val) = ref.simple j'.val := Subtype.ext hσ
    exact ⟨restriction K σ,
      congrArg Subtype.val ((hjAction σ (ref.simple i.val)).trans (congrArg j hσ'))⟩
  have hunit : IsUnitComparison m := hm
  obtain ⟨restrict, coeff, coord, _, _, hres, hfold, _, _⟩ :=
    foldingOfScalarAction S P D hS hmax simple m hunit ρ haction hcartan hstable hcentral htrans
  let α : SimpleRoot P.pair := ⟨(simple 1).val, (D.simple_iff _).mp (simple 1).property⟩
  have hfixed (σ : Gal(K/F)) : diagramRoot ω σ α.val = α.val := hcentral σ
  obtain ⟨β, L, hβ, hsub, hpinL, hcoroot, f, hf⟩ :=
    TrialitarianFixedRootSL2.fixedSimpleRootSL2 G hG hsc M S hS hmax
      P D ref.additive A U pin a m ω hm hpin hcoord α hfixed
  have hneg : D.datum.rootDatum.root β = -D.datum.rootDatum.root α.val := by
    rw [D.datum.root_eq, D.datum.root_eq, hβ]
    rfl
  have hL : RankOne.MatchesAbsolute S L P D U m α.val β :=
    ⟨hneg, hsub, hcoroot, f, (congrArg f hcoroot).trans hf⟩
  have hmCanonical : m = multiplicativeBaseChange F K :=
    unitComparison_unique hunit (multiplicativeBaseChange_unit K)
  have hresCanonical : IsRestriction S (multiplicativeBaseChange F K) restrict :=
    hmCanonical ▸ hres
  obtain ⟨Q, w, n, v, r, hn, hr, hv, hroot, hw⟩ :=
    highestRootRationalRepresentative hqs.1 hS hmax hB hSB hC D W simple hcartan
      restrict coeff coord hresCanonical hfold
  let g := n ≫ Q.normalizer.inclusion.hom.hom
  let s := Q.splitImage.conjugation w
  have hs := rationalNormalizerConjugation Q w n hn
  let H := conjugateRankOne L g s hs
  let θ := highestRootIndex D.datum.rootDatum D.base simple
  let θneg := v.val.indexEquiv β
  have hH : H.MatchesAbsolute S P D U m θ θneg := by
    have h := transportAbsoluteMarkings D W U v r hv g hr s hs
      (compatibleNormalizerConjugations D W Q w n hn v r hr hv) m α.val β L hL
    change H.MatchesAbsolute S P D U m (v.val.indexEquiv (simple 1).val) θneg at h
    rw [hroot] at h
    exact h
  have hproject := projectedDistinguishedRoots (D := D) simple hcartan coeff hfold.1
  refine ⟨M, S, hS, hmax, (K : Type u), inferInstance, inferInstance, inferInstance,
    inferInstance, P, D, A, U, pin, simple, ω, m, hunit, haction,
    ⟨ref.additive, a, hcoord, hpin⟩, hcartan, hcentral, htrans, restrict, coeff, coord, hres, hfold,
    β, θ, θneg, L, H, hproject.1, hproject.2.2, hL, hH, hpinL, ?_, ?_, ?_⟩
  · exact ⟨Q, w, n, hn, hw, conjugateRankOne_isTransport L g s hs⟩
  · exact oppositeRadicalsOfAbsolute hqs.1 D U m hunit θ θneg H hH
  · exact centralUpperOfHighest hqs.1 hmax D U simple hcartan m hunit restrict hres
      coeff coord hfold θneg H hH

end Assembly

end LinearAlgebraicGroups.Arithmetic.TrialitarianRelativeRoots
