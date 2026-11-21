import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ExceptionalOuterInvolutions
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreSimplicity
import Mathlib.LinearAlgebra.Eigenspace.Basic
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.StableCartanVoganData
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ExceptionalCoordinateE
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CartanDecompositionSignature
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealFormsConjugations

namespace LieAlgebrasAndRepresentations.ExceptionalOuterInvolutions

open Specs.LieAlgebrasAndRepresentations.ExceptionalOuterInvolutions
open Specs.LieAlgebrasAndRepresentations.VoganEquivalence
open Serre
open Specs.LieAlgebrasAndRepresentations.StableCartanVoganData (DiagramData)
open Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature (complexFixed)
open scoped BigOperators
open _root_.LieAlgebrasAndRepresentations.RealForms

universe u

set_option maxRecDepth 4096

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem rootCounts : rootCountsType := by
  unfold rootCountsType
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blackSimpleRoots : blackSimpleRootsType := by
  unfold blackSimpleRootsType
  decide +kernel


private theorem iterBracket_lowest {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    [Module.Finite ℂ L] (H E F X : L) (m : ℕ)
    (hE : ⁅H,E⁆ = (2 : ℂ) • E) (hX : ⁅H,X⁆ = -(m : ℂ) • X)
    (hFE : ⁅F,E⁆ = -H) (hFX : ⁅F,X⁆ = 0) :
    iterBracket E (m + 1) X = 0 := by
  classical
  by_cases hz : X = 0
  · rw [hz, iterBracket_eq_pow]
    exact map_zero _
  have hex : ∃ n, iterBracket E n X = 0 := by
    by_contra! hn
    let μ (n : ℕ) : ℂ := -(m : ℂ) + n * 2
    have hμ : Function.Injective μ := by
      intro i j hij
      dsimp [μ] at hij
      exact_mod_cast (show (i : ℂ) = j by linear_combination hij / 2)
    have hv : LinearIndependent ℂ (fun n => iterBracket E n X) := by
      apply (LieAlgebra.ad ℂ L H).eigenvectors_linearIndependent' μ hμ
      intro n
      exact ⟨Module.End.mem_eigenspace_iff.mpr
        (bracket_iterBracket_weight H E X 2 (-(m : ℂ)) hE hX n), hn n⟩
    exact Module.Finite.not_linearIndependent_of_infinite _ hv
  let n := Nat.find hex
  have hn : iterBracket E n X = 0 := Nat.find_spec hex
  obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := by
    cases heq : n with
    | zero => exact (hz (by simpa [heq, iterBracket] using hn)).elim
    | succ k => exact ⟨k, rfl⟩
  have hkn : iterBracket E k X ≠ 0 := Nat.find_min hex (by omega)
  rw [hk] at hn
  have hl := lowering_iterBracket H E F X (-(m : ℂ)) hE hX hFE hFX k
  rw [hn, lie_zero] at hl
  have hs := (smul_eq_zero.mp hl.symm).resolve_right hkn
  apply neg_eq_zero.mp at hs
  have he := (mul_eq_zero.mp hs).resolve_left (by exact_mod_cast Nat.succ_ne_zero k)
  have hkm : k = m := by
    exact_mod_cast (show (k : ℂ) = m by linear_combination he)
  simpa [hkm] using hn

private theorem serre_of_mixed_relations {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    [Module.Finite ℂ L] {A : Matrix (Fin 4) (Fin 4) ℤ}
    (hd : ∀ i, A i i = 2) (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    (E F H : Fin 4 → L)
    (hh : ∀ i j, ⁅H i,H j⁆ = 0)
    (he : ∀ i j, ⁅H i,E j⁆ = (A i j : ℂ) • E j)
    (hf : ∀ i j, ⁅H i,F j⁆ = -(A i j : ℂ) • F j)
    (hef : ∀ i j, ⁅E i,F j⁆ = if i = j then H i else 0) :
    RelationsHold A E F H := by
  refine ⟨hh, ?_, ?_, hef, ?_, ?_⟩
  · simpa only [Int.cast_smul_eq_zsmul] using he
  · simpa only [neg_smul, Int.cast_smul_eq_zsmul] using hf
  · intro i j hij
    have hFE : ⁅F i,E i⁆ = -H i := by rw [← lie_skew, hef, ite_eq_left rfl]
    have hFX : ⁅F i,E j⁆ = 0 := by rw [← lie_skew, hef, ite_eq_right hij.symm, neg_zero]
    let m := (-A i j).toNat
    have hm : (m : ℤ) = -A i j := Int.toNat_of_nonneg (by have := ho i j hij; omega : 0 ≤ -A i j)
    have hm' : -(m : ℂ) = (A i j : ℂ) := by exact_mod_cast (neg_eq_iff_eq_neg.mpr hm)
    have hn : (1 - A i j).toNat = m + 1 := by omega
    rw [hn]
    refine iterBracket_lowest (H i) (E i) (F i) (E j) m ?_ ?_ hFE hFX
    · norm_num [he, hd]
    · rw [he, hm']
  · intro i j hij
    let m := (-A i j).toNat
    have hm : (m : ℤ) = -A i j := Int.toNat_of_nonneg (by have := ho i j hij; omega)
    have hm' : -(m : ℂ) = (A i j : ℂ) := by exact_mod_cast (neg_eq_iff_eq_neg.mpr hm)
    have hn : (1 - A i j).toNat = m + 1 := by omega
    rw [hn]
    refine iterBracket_lowest (-H i) (F i) (E i) (F j) m ?_ ?_ ?_ ?_
    · norm_num [hf, hd, neg_lie]
    · rw [neg_lie, hf, neg_smul, neg_neg, hm']
    · rw [hef, ite_eq_left rfl, neg_neg]
    · rw [hef, ite_eq_right hij]

private theorem e6CartanConditions : CartanConditions e6Cartan := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
  · intro i j
    fin_cases i <;> fin_cases j <;> decide

private theorem e6BasisData :
    ∃ b : Module.Basis (Fin 6) ℝ ExceptionalE.e6Space,
      IsSimpleBasis ExceptionalE.e6Roots ExceptionalE.e6Regular b ∧
      (∀ i, b i = ExceptionalE.e6Simple (coordinateIndex i)) ∧
      (∀ i j, (e6Cartan i j : ℝ) = cartanMatrix b i j) := by
  obtain ⟨_, b, hb, hsimple⟩ := ExceptionalE.e6_basis
  refine ⟨b.reindex coordinateIndex.symm, ?_, ?_, ?_⟩
  · simpa only [IsSimpleBasis, Module.Basis.range_reindex] using hsimple
  · intro i
    simpa only [Module.Basis.reindex_apply, Equiv.symm_symm] using hb (coordinateIndex i)
  · intro i j
    simp only [cartanMatrix, Module.Basis.reindex_apply, Equiv.symm_symm, hb]
    change (e6Cartan i j : ℝ) =
      cartanMatrix ExceptionalE.e6Simple (coordinateIndex i) (coordinateIndex j)
    rw [ExceptionalE.e6_diagram.1]
    fin_cases i <;> fin_cases j <;>
      norm_num [e6Cartan, coordinateIndex, ExceptionalE.adjacent, Matrix.cons_val_zero,
        Matrix.cons_val_succ]

private instance finiteE6 : Module.Finite ℂ (Algebra e6Cartan) := by
  obtain ⟨b, hb, _, hA⟩ := e6BasisData
  exact (finiteType_spec ExceptionalE.e6Roots ExceptionalE.e6_isRootSystem
    ExceptionalE.e6Regular ExceptionalE.e6_basis.1 b hb e6Cartan hA).1

private theorem he_complex (i j : Fin 6) :
    ⁅h e6Cartan i, e e6Cartan j⁆ = (e6Cartan i j : ℂ) • e e6Cartan j := by
  rw [Serre.he, Int.cast_smul_eq_zsmul]

private theorem hf_complex (i j : Fin 6) :
    ⁅h e6Cartan i, f e6Cartan j⁆ = -(e6Cartan i j : ℂ) • f e6Cartan j := by
  rw [Serre.hf, neg_smul, Int.cast_smul_eq_zsmul]

set_option maxHeartbeats 0 in
theorem foldedSerre : foldedSerreType := by
  apply serre_of_mixed_relations (by decide) (by intro i j; fin_cases i <;> fin_cases j <;> decide)
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [foldGenerators, add_lie, lie_add, Serre.hh]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [foldGenerators, add_lie, lie_add, he_complex, e6Cartan, f4Cartan,
        Matrix.cons_val_zero, Matrix.cons_val_succ] <;> module
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [foldGenerators, add_lie, lie_add, hf_complex, e6Cartan, f4Cartan,
        Matrix.cons_val_zero, Matrix.cons_val_succ] <;> module
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [foldGenerators, add_lie, lie_add, Serre.ef]


private theorem zero_colorMove_iff {b c : Coloring} (h : ColorMove b c) :
    b = 0 ↔ c = 0 := by
  have h₂ : ∀ b : Coloring, b = 0 ↔ reflectColoring 2 b = 0 := by decide
  have h₅ : ∀ b : Coloring, b = 0 ↔ reflectColoring 5 b = 0 := by decide
  rcases h with rfl | rfl
  · exact h₂ b
  · exact h₅ b

theorem colorOrbits : colorOrbitsType := by
  intro b c
  constructor
  · intro h
    induction h with
    | rel _ _ h => exact zero_colorMove_iff h
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    let both : Coloring := (1, 1)
    have hcases : ∀ t : Coloring, t = 0 ∨ t = both ∨
        ColorMove t both := by unfold ColorMove; decide
    by_cases hb : b = 0
    · rw [hb, h.mp hb]
      exact Relation.EqvGen.refl _
    have hc : c ≠ 0 := fun hc => hb (h.mpr hc)
    have route (t : Coloring) (ht : t ≠ 0) : Relation.EqvGen ColorMove t both := by
      rcases (hcases t).resolve_left ht with rfl | hm
      · exact Relation.EqvGen.refl _
      · exact Relation.EqvGen.rel _ _ hm
    exact Relation.EqvGen.trans _ _ _ (route b hb) (Relation.EqvGen.symm _ _ (route c hc))

private def outerDiagram (b : Coloring) : DiagramData e6Cartan where
  perm := diagramInvolution
  involutive := diagramInvolution.left_inv
  preserves := by intro i j; fin_cases i <;> fin_cases j <;> decide
  sign := fun i => colorSign (vertexColor b i)
  sign_cases := fun i => by
    by_cases hi : vertexColor b i = 0 <;> simp [colorSign, hi]
  paired := by
    have hp : ∀ i : Fin 6, diagramInvolution i ≠ i → i ≠ 2 ∧ i ≠ 5 := by decide
    intro i hi
    simp [vertexColor, colorSign, (hp i hi).1, (hp i hi).2]

theorem realizeOuter : realizeOuterType.{u} := by
  intro L _ _ ω E F H hP hω b
  obtain ⟨_, a, hcomm, ha, hgen, _⟩ :=
    _root_.LieAlgebrasAndRepresentations.StableCartanVoganData.realize e6Cartan
      e6CartanConditions.2.1 (outerDiagram b) ω E F H hP hω
  exact ⟨a, hgen, hcomm, ha⟩


private theorem he_bracket (i j k : Fin 6) :
    ⁅h e6Cartan i, ⁅e e6Cartan j, e e6Cartan k⁆⁆ =
      ((e6Cartan i j : ℂ) + (e6Cartan i k : ℂ)) • ⁅e e6Cartan j, e e6Cartan k⁆ := by
  rw [leibniz_lie, he_complex, he_complex, smul_lie, lie_smul, add_smul]

private theorem hf_bracket (i j k : Fin 6) :
    ⁅h e6Cartan i, ⁅f e6Cartan j, f e6Cartan k⁆⁆ =
      (-(e6Cartan i j : ℂ) - (e6Cartan i k : ℂ)) • ⁅f e6Cartan j, f e6Cartan k⁆ := by
  rw [leibniz_lie, hf_complex, hf_complex, smul_lie, lie_smul, sub_eq_add_neg, add_smul]

private theorem e_fBracket (i j k : Fin 6) :
    ⁅e e6Cartan i, ⁅f e6Cartan j, f e6Cartan k⁆⁆ =
      (if i = j then -(e6Cartan j k : ℂ) • f e6Cartan k else 0) +
      (if i = k then (e6Cartan k j : ℂ) • f e6Cartan j else 0) := by
  have hflip (a b : Fin 6) : ⁅f e6Cartan a, h e6Cartan b⁆ =
      (e6Cartan b a : ℂ) • f e6Cartan a := by
    rw [← lie_skew, hf_complex, neg_smul, neg_neg]
  rw [leibniz_lie, Serre.ef e6Cartan i j, Serre.ef e6Cartan i k]
  split_ifs <;> subst_vars <;> simp [hf_complex, hflip]

private theorem eBracket_f (i j k : Fin 6) :
    ⁅⁅e e6Cartan i, e e6Cartan j⁆, f e6Cartan k⁆ =
      (if j = k then -(e6Cartan j i : ℂ) • e e6Cartan i else 0) -
      (if i = k then -(e6Cartan i j : ℂ) • e e6Cartan j else 0) := by
  have hflip (a b : Fin 6) : ⁅e e6Cartan a, h e6Cartan b⁆ =
      -(e6Cartan b a : ℂ) • e e6Cartan a := by
    rw [← lie_skew, he_complex, neg_smul]
  rw [lie_lie, Serre.ef e6Cartan j k, Serre.ef e6Cartan i k]
  split_ifs <;> subst_vars <;> simp [hflip]

private theorem eBracket_fBracket (i j k l : Fin 6) :
    ⁅⁅e e6Cartan i, e e6Cartan j⁆, ⁅f e6Cartan k, f e6Cartan l⁆⁆ =
      ⁅e e6Cartan i,
        (if j = k then -(e6Cartan k l : ℂ) • f e6Cartan l else 0) +
        (if j = l then (e6Cartan l k : ℂ) • f e6Cartan k else 0)⁆ -
      ⁅e e6Cartan j,
        (if i = k then -(e6Cartan k l : ℂ) • f e6Cartan l else 0) +
        (if i = l then (e6Cartan l k : ℂ) • f e6Cartan k else 0)⁆ := by
  rw [lie_lie, e_fBracket, e_fBracket]

set_option maxHeartbeats 0 in
theorem blackFoldedSerre : blackFoldedSerreType := by
  apply serre_of_mixed_relations (by decide) (by intro i j; fin_cases i <;> fin_cases j <;> decide)
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [blackH, add_lie, lie_add, Serre.hh, smul_lie, lie_smul]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [blackH, blackE, add_lie, lie_add, lie_sub, smul_lie, he_complex,
        he_bracket, e6Cartan, c4Cartan, Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
      rw [← lie_skew (e e6Cartan 2) (e e6Cartan 1),
        ← lie_skew (e e6Cartan 2) (e e6Cartan 3)] <;> module
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [blackH, blackF, add_lie, lie_add, lie_sub, smul_lie, hf_complex,
        hf_bracket, e6Cartan, c4Cartan, Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
      rw [← lie_skew (f e6Cartan 1) (f e6Cartan 2),
        ← lie_skew (f e6Cartan 3) (f e6Cartan 2)] <;> module
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [blackH, blackF, blackE, add_lie, lie_add, lie_sub, sub_lie,
        eBracket_fBracket, eBracket_f, e_fBracket, lie_smul, Serre.ef, e6Cartan,
        Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
      (try rw [← lie_skew (e e6Cartan 2) (h e6Cartan 3)]) <;>
      norm_num [he_complex, e6Cartan, Matrix.cons_val_zero, Matrix.cons_val_succ] <;> module

open ExceptionalGF (QVec)

private def permuteCoefficients (c : QVec 6) : QVec 6 := c ∘ diagramInvolution

private theorem permuteCoefficients_involutive : Function.Involutive permuteCoefficients := by
  intro c
  funext i
  exact congrArg c (diagramInvolution.left_inv i)

private theorem foldRoot_permute (c : QVec 6) : foldRoot (permuteCoefficients c) = foldRoot c := by
  funext i
  fin_cases i <;> simp [foldRoot, permuteCoefficients, diagramInvolution, add_comm]

private def orbitRepresentative (c : QVec 6) : QVec 6 :=
  if c 0 < c 4 ∨ c 0 = c 4 ∧ c 1 < c 3 then permuteCoefficients c else c

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem representativeCount : (e6Coefficients.image orbitRepresentative).card = 48 := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem whiteRootCount : (e6Coefficients.image foldRoot).card = 48 := by
  decide +kernel

private theorem foldRoot_representative (c : QVec 6) :
    foldRoot (orbitRepresentative c) = foldRoot c := by
  unfold orbitRepresentative
  split_ifs <;> simp [foldRoot_permute]

private theorem foldRoot_fibers :
    ∀ c ∈ e6Coefficients, ∀ d ∈ e6Coefficients,
      foldRoot c = foldRoot d ↔ d = c ∨ d = permuteCoefficients c := by
  have heq : (e6Coefficients.image orbitRepresentative).image foldRoot =
      e6Coefficients.image foldRoot := by
    rw [Finset.image_image]
    exact congrArg (fun f => e6Coefficients.image f) (funext foldRoot_representative)
  have hinj : Set.InjOn foldRoot (e6Coefficients.image orbitRepresentative : Set (QVec 6)) :=
    Finset.card_image_iff.mp (by rw [heq, whiteRootCount, representativeCount])
  intro c hc d hd
  constructor
  · intro h
    have hcd : orbitRepresentative c = orbitRepresentative d :=
      hinj (Finset.mem_image_of_mem _ hc) (Finset.mem_image_of_mem _ hd)
        (by simpa only [foldRoot_representative] using h)
    unfold orbitRepresentative at hcd
    split_ifs at hcd
    · exact Or.inl (permuteCoefficients_involutive.injective hcd).symm
    · exact Or.inr hcd.symm
    · exact Or.inr (by rw [hcd, permuteCoefficients_involutive d])
    · exact Or.inl hcd.symm
  · rintro (rfl | rfl)
    · rfl
    · exact (foldRoot_permute c).symm

private def simpleQInSourceOrder (i : Fin 6) : QVec 8 :=
  ExceptionalE.simpleQ ((coordinateIndex i).castLE (by decide))

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem simpleCoefficients_reconstruct :
    ∀ q ∈ ExceptionalE.e6List,
      (∑ i, simpleCoefficients q i • simpleQInSourceOrder i) = q := by
  decide +kernel

noncomputable section

private def coefficientVector (b : Module.Basis (Fin 6) ℝ ExceptionalE.e6Space)
    (c : QVec 6) : ExceptionalE.e6Space :=
  ∑ i, (c i : ℝ) • b i

private theorem coefficientVector_reconstruct
    (b : Module.Basis (Fin 6) ℝ ExceptionalE.e6Space)
    (hb : ∀ i, b i = ExceptionalE.e6Simple (coordinateIndex i))
    {q : QVec 8} (hq : q ∈ ExceptionalE.e6List) :
    (coefficientVector b (simpleCoefficients q) : ExceptionalGF.Space 8) =
      ExceptionalGF.realize q := by
  change ExceptionalE.e6Space.subtype (coefficientVector b (simpleCoefficients q)) = _
  simp only [coefficientVector, map_sum, map_smul, Submodule.subtype_apply, hb]
  change (∑ i, (simpleCoefficients q i : ℝ) •
    ExceptionalGF.realize (simpleQInSourceOrder i)) = _
  calc
    _ = ExceptionalGF.realize (∑ i, simpleCoefficients q i • simpleQInSourceOrder i) := by
      induction (Finset.univ : Finset (Fin 6)) using Finset.induction_on with
      | empty => simp
      | insert i t hi ht =>
        simp only [Finset.sum_insert hi, ExceptionalGF.realize_add, ExceptionalGF.realize_smul, ht]
    _ = _ := congrArg ExceptionalGF.realize (simpleCoefficients_reconstruct q hq)

private theorem coefficientVector_root_iff
    (b : Module.Basis (Fin 6) ℝ ExceptionalE.e6Space)
    (hb : ∀ i, b i = ExceptionalE.e6Simple (coordinateIndex i))
    (x : ExceptionalE.e6Space) :
    x ∈ ExceptionalE.e6Roots ↔ ∃ c ∈ e6Coefficients, x = coefficientVector b c := by
  have hmem : x ∈ ExceptionalE.e6Roots ↔
      (x : ExceptionalGF.Space 8) ∈ ExceptionalE.e6AmbientRoots := by
    rw [← ExceptionalE.e6_roots_image]
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact (Subtype.ext hyx : y = x) ▸ hy
  rw [hmem, ExceptionalE.e6AmbientRoots]
  constructor
  · rintro ⟨q, hq, hqx⟩
    refine ⟨simpleCoefficients q, ?_, ?_⟩
    · rw [e6Coefficients, Finset.mem_image]
      exact ⟨q, hq, rfl⟩
    · exact Subtype.ext (hqx.symm.trans (coefficientVector_reconstruct b hb hq).symm)
  · rintro ⟨c, hc, rfl⟩
    rw [e6Coefficients, Finset.mem_image] at hc
    obtain ⟨q, hq, rfl⟩ := hc
    exact ⟨q, hq, (coefficientVector_reconstruct b hb hq).symm⟩

private def coefficientWeight (c : QVec 6) (i : Fin 6) : ℂ :=
  ∑ j, (e6Cartan i j : ℂ) * (c j : ℂ)

private theorem coefficientWeight_eq
    (b : Module.Basis (Fin 6) ℝ ExceptionalE.e6Space)
    (hA : ∀ i j, (e6Cartan i j : ℝ) = cartanMatrix b i j) (c : QVec 6) :
    coefficientWeight c = rootWeight b (coefficientVector b c) := by
  funext i
  have hA' (j : Fin 6) : (e6Cartan i j : ℂ) = (cartanMatrix b i j : ℝ) := by
    exact_mod_cast hA i j
  simp only [coefficientWeight, hA', cartanMatrix, rootWeight, coefficientVector,
    rootCartan, sum_inner, Finset.mul_sum, Finset.sum_div,
    Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro j _
  erw [real_inner_smul_left (b j) (b i) (c j : ℝ), Complex.ofReal_mul]
  rw [Complex.ofReal_ratCast]
  ring

private theorem e6WeightCover :
    (∀ c ∈ e6Coefficients, Module.finrank ℂ (weightSpace e6Cartan (coefficientWeight c)) = 1) ∧
    ∀ χ : Fin 6 → ℂ, χ = 0 ∨ weightSpace e6Cartan χ = ⊥ ∨
      ∃ c ∈ e6Coefficients, χ = coefficientWeight c := by
  obtain ⟨b, hs, hb, hA⟩ := e6BasisData
  have ht := finiteType_spec ExceptionalE.e6Roots ExceptionalE.e6_isRootSystem
    ExceptionalE.e6Regular ExceptionalE.e6_basis.1 b hs e6Cartan hA
  constructor
  · intro c hc
    rw [coefficientWeight_eq b hA]
    exact ht.2.2.2.1 _ ((coefficientVector_root_iff b hb _).mpr ⟨c, hc, rfl⟩)
  · intro χ
    by_cases hχ : χ = 0
    · exact Or.inl hχ
    by_cases hw : weightSpace e6Cartan χ = ⊥
    · exact Or.inr (Or.inl hw)
    obtain ⟨x, hx, rfl⟩ := (ht.2.2.1 χ hχ).mp hw
    obtain ⟨c, hc, rfl⟩ := (coefficientVector_root_iff b hb x).mp hx
    exact Or.inr (Or.inr ⟨c, hc, (coefficientWeight_eq b hA c).symm⟩)

private theorem permuteWeight (c : QVec 6) (i : Fin 6) :
    coefficientWeight (permuteCoefficients c) i = coefficientWeight c (diagramInvolution i) := by
  have hm (i j : Fin 6) : e6Cartan (diagramInvolution i) (diagramInvolution j) = e6Cartan i j :=
    (outerDiagram 0).preserves i j
  change (∑ j, (e6Cartan i j : ℂ) * (c (diagramInvolution j) : ℂ)) = _
  unfold coefficientWeight
  rw [← diagramInvolution.sum_comp
    (fun j => (e6Cartan (diagramInvolution i) j : ℂ) * (c j : ℂ))]
  exact Finset.sum_congr rfl (fun j _ => by rw [hm i j])

private def fixedAverage (a : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan)
    (ha : Function.Involutive a) : Algebra e6Cartan →ₗ[ℂ] complexFixed a :=
  ((2 : ℂ)⁻¹ • (LinearMap.id + a.toLinearMap)).codRestrict (complexFixed a).toSubmodule
    (fun x => by
      change a ((2 : ℂ)⁻¹ • (x + a x)) = (2 : ℂ)⁻¹ • (x + a x)
      rw [map_smul, map_add, ha, add_comm])

private theorem fixedAverage_apply_coe (a : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan)
    (ha : Function.Involutive a) (x : Algebra e6Cartan) :
    ((fixedAverage a ha x : complexFixed a) : Algebra e6Cartan) =
      (2 : ℂ)⁻¹ • (x + a x) := rfl

private theorem fixedAverage_surjective (a : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan)
    (ha : Function.Involutive a) : Function.Surjective (fixedAverage a ha) := by
  intro x
  refine ⟨x, Subtype.ext ?_⟩
  rw [fixedAverage_apply_coe, show a (x : Algebra e6Cartan) = x from x.property]
  module

private theorem fixedAverage_invariant (a : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan)
    (ha : Function.Involutive a) (x : Algebra e6Cartan) :
    fixedAverage a ha (a x) = fixedAverage a ha x := by
  apply Subtype.ext
  rw [fixedAverage_apply_coe, fixedAverage_apply_coe, ha x, add_comm]

private theorem apply_mem_permutedWeight (a : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan)
    (hh : ∀ i, a (h e6Cartan i) = h e6Cartan (diagramInvolution i))
    (c : QVec 6) {x : Algebra e6Cartan} (hx : x ∈ weightSpace e6Cartan (coefficientWeight c)) :
    a x ∈ weightSpace e6Cartan (coefficientWeight (permuteCoefficients c)) := by
  intro i
  rw [permuteWeight]
  have he := congrArg a (hx (diagramInvolution i))
  have hi : diagramInvolution (diagramInvolution i) = i := (outerDiagram 0).involutive i
  rw [a.map_lie, hh, hi, map_smul] at he
  exact he

set_option maxRecDepth 4096 in
/-- One averaged vector per surviving restriction, together with four averaged
Cartan generators, suffices to span the complex fixed space. -/
private theorem fixedRank_le (a : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan)
    (ha : Function.Involutive a)
    (hh : ∀ i, a (h e6Cartan i) = h e6Cartan (diagramInvolution i))
    (S : Finset (QVec 6)) (hS : S ⊆ e6Coefficients)
    (hvanish : ∀ c ∈ e6Coefficients, c ∉ S →
      ∀ x ∈ weightSpace e6Cartan (coefficientWeight c), fixedAverage a ha x = 0) :
    Module.finrank ℂ (complexFixed a) ≤ 4 + (S.image foldRoot).card := by
  classical
  have hrep (r : (S.image foldRoot : Finset (QVec 4))) :
      ∃ c ∈ S, foldRoot c = r := Finset.mem_image.mp r.property
  choose c hc hrc using hrep
  have hc' (r : (S.image foldRoot : Finset (QVec 4))) : c r ∈ e6Coefficients :=
    hS (hc r)
  have hdim (r : (S.image foldRoot : Finset (QVec 4))) :=
    e6WeightCover.1 (c r) (hc' r)
  have hv (r : (S.image foldRoot : Finset (QVec 4))) :=
    (finrank_eq_one_iff'.mp (hdim r))
  choose v _hvn hvspan using hv
  let g : Fin 4 ⊕ (S.image foldRoot : Finset (QVec 4)) → complexFixed a :=
    Sum.elim (fun j => fixedAverage a ha (h e6Cartan (![0,1,2,5] j)))
      (fun r => fixedAverage a ha (v r))
  let W := Submodule.span ℂ (Set.range g)
  have hWc (i : Fin 6) : fixedAverage a ha (h e6Cartan i) ∈ W := by
    have havg (j : Fin 6) :
        fixedAverage a ha (h e6Cartan (diagramInvolution j)) =
          fixedAverage a ha (h e6Cartan j) := by
      rw [← hh, fixedAverage_invariant]
    have hw (j : Fin 4) :
        fixedAverage a ha (h e6Cartan (![0,1,2,5] j)) ∈ W :=
      Submodule.subset_span ⟨Sum.inl j, rfl⟩
    fin_cases i
    · exact hw 0
    · exact hw 1
    · exact hw 2
    · exact (havg 1).symm ▸ hw 1
    · exact (havg 0).symm ▸ hw 0
    · exact hw 3
  have hWr (d : QVec 6) (hd : d ∈ e6Coefficients) (x : Algebra e6Cartan)
      (hx : x ∈ weightSpace e6Cartan (coefficientWeight d)) :
      fixedAverage a ha x ∈ W := by
    by_cases hds : d ∈ S
    · let r : (S.image foldRoot : Finset (QVec 4)) :=
        ⟨foldRoot d, Finset.mem_image_of_mem _ hds⟩
      have hr := (foldRoot_fibers (c r) (hc' r) d hd).mp (hrc r)
      have hgen : fixedAverage a ha (v r) ∈ W := Submodule.subset_span ⟨Sum.inr r, rfl⟩
      have hline (y : Algebra e6Cartan)
          (hy : y ∈ weightSpace e6Cartan (coefficientWeight (c r))) :
          fixedAverage a ha y ∈ W := by
        obtain ⟨k, hk⟩ := hvspan r ⟨y, hy⟩
        have hky : k • (v r : Algebra e6Cartan) = y := congrArg Subtype.val hk
        rw [← hky, map_smul]
        exact W.smul_mem k hgen
      rcases hr with h | h
      · exact hline x (h ▸ hx)
      · have hy := apply_mem_permutedWeight a hh d hx
        have hdd : permuteCoefficients d = c r := by
          rw [h]
          funext i
          exact congrArg (c r) ((outerDiagram 0).involutive i)
        rw [hdd] at hy
        rw [← fixedAverage_invariant a ha x]
        exact hline (a x) hy
    · rw [hvanish d hd hds x hx]
      exact W.zero_mem
  have hzero : weightSpace e6Cartan 0 = cartan e6Cartan := by
    obtain ⟨b, _, _, hA⟩ := e6BasisData
    exact zero_weightSpace_eq_cartan e6Cartan b hA
  have htop : W = ⊤ := by
    have hle : (⊤ : Submodule ℂ (Algebra e6Cartan)) ≤ W.comap (fixedAverage a ha) := by
      rw [← weightSpace_iSup_eq_top e6Cartan]
      apply iSup_le
      intro χ
      rcases e6WeightCover.2 χ with rfl | hz | ⟨c, hc, rfl⟩
      · rw [hzero, cartan]
        exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hWc i)
      · rw [hz]
        exact bot_le
      · exact fun x hx => hWr c hc x hx
    apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := fixedAverage_surjective a ha x
    exact hle Submodule.mem_top
  have hcard := finrank_range_le_card (R := ℂ) g
  change Module.finrank ℂ W ≤ _ at hcard
  rw [htop, finrank_top, Fintype.card_sum, Fintype.card_fin, Fintype.card_coe] at hcard
  exact hcard

private theorem chainConnected {A : Matrix (Fin 4) (Fin 4) ℤ}
    (h₀₁ : A 0 1 ≠ 0) (h₁₂ : A 1 2 ≠ 0) (h₂₃ : A 2 3 ≠ 0) :
    ∀ i j, MatrixConnected A i j := by
  have h01 : MatrixConnected A 0 1 := Relation.EqvGen.rel _ _ ⟨by decide, h₀₁⟩
  have h12 : MatrixConnected A 1 2 := Relation.EqvGen.rel _ _ ⟨by decide, h₁₂⟩
  have h23 : MatrixConnected A 2 3 := Relation.EqvGen.rel _ _ ⟨by decide, h₂₃⟩
  have h02 := Relation.EqvGen.trans _ _ _ h01 h12
  have h03 := Relation.EqvGen.trans _ _ _ h02 h23
  have h0 (i : Fin 4) : MatrixConnected A 0 i := by
    fin_cases i
    · exact Relation.EqvGen.refl _
    · exact h01
    · exact h02
    · exact h03
  exact fun i j => Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (h0 i)) (h0 j)

private theorem f4BasisData :
    ∃ b : Module.Basis (Fin 4) ℝ (ExceptionalGF.Space 4),
      IsSimpleBasis ExceptionalGF.f4Roots ExceptionalGF.f4Regular b ∧
      (∀ i j, (f4Cartan i j : ℝ) = cartanMatrix b i j) := by
  let rev : Fin 4 ≃ Fin 4 :=
    { toFun := fun i => ![3,2,1,0] i
      invFun := fun i => ![3,2,1,0] i
      left_inv := by decide
      right_inv := by decide }
  obtain ⟨_, b, hb, hs⟩ := ExceptionalGF.f4_basis
  refine ⟨b.reindex rev.symm, ?_, ?_⟩
  · simpa only [IsSimpleBasis, Module.Basis.range_reindex] using hs
  · intro i j
    change (f4Cartan i j : ℝ) = cartanMatrix (b.reindex rev.symm) i j
    simp only [cartanMatrix, Module.Basis.reindex_apply, Equiv.symm_symm, hb]
    change (f4Cartan i j : ℝ) = cartanMatrix ExceptionalGF.f4Simple (rev i) (rev j)
    rw [ExceptionalGF.f4_diagram.1]
    fin_cases i <;> fin_cases j <;>
      norm_num [f4Cartan, rev, Matrix.cons_val_zero, Matrix.cons_val_succ]

private theorem c4BasisData :
    ∃ b : Module.Basis (Fin 4) ℝ (ClassicalCoordinates.Space 4),
      IsSimpleBasis (ClassicalCoordinates.rootsC 4) (ClassicalCoordinates.regularBCD 4 (1/2)) b ∧
      (∀ i j, (c4Cartan i j : ℝ) = cartanMatrix b i j) := by
  obtain ⟨b, hb, hs⟩ := ClassicalCoordinates.simpleC_basis 4 (by decide)
  refine ⟨b, hs, ?_⟩
  intro i j
  simp only [cartanMatrix, rootCartan, hb, ClassicalCoordinates.simpleC_gram]
  fin_cases i <;> fin_cases j <;>
    norm_num [c4Cartan, ClassicalCoordinates.terminalEdge, ClassicalCoordinates.adjacent,
      Matrix.cons_val_zero, Matrix.cons_val_succ]

private theorem f4Model :
    Module.Finite ℂ (Algebra f4Cartan) ∧
      LieAlgebra.IsSimple ℂ (Algebra f4Cartan) ∧ Module.finrank ℂ (Algebra f4Cartan) = 52 := by
  obtain ⟨b, hs, hA⟩ := f4BasisData
  have ht := finiteType_spec ExceptionalGF.f4Roots ExceptionalGF.f4_isRootSystem
    ExceptionalGF.f4Regular ExceptionalGF.f4_basis.1 b hs f4Cartan hA
  refine ⟨ht.1, isSimple_spec ExceptionalGF.f4Roots ExceptionalGF.f4_isRootSystem
    ExceptionalGF.f4Regular ExceptionalGF.f4_basis.1 b hs f4Cartan hA
      (chainConnected (by decide) (by decide) (by decide)), ?_⟩
  have hc := ExceptionalGF.f4_count.1
  rw [ht.2.2.2.2.2.2, Nat.card_coe_set_eq, hc]
  rfl

private theorem c4Model :
    Module.Finite ℂ (Algebra c4Cartan) ∧
      LieAlgebra.IsSimple ℂ (Algebra c4Cartan) ∧ Module.finrank ℂ (Algebra c4Cartan) = 36 := by
  obtain ⟨b, hs, hA⟩ := c4BasisData
  have hr := ClassicalCoordinates.rootSystemC 4 (by decide)
  have hz := ClassicalCoordinates.regularC_regular 4
  have ht := finiteType_spec _ hr _ hz b hs c4Cartan hA
  refine ⟨ht.1, isSimple_spec _ hr _ hz b hs c4Cartan hA
    (chainConnected (by decide) (by decide) (by decide)), ?_⟩
  have hc := ClassicalCoordinates.countC 4 (by decide)
  rw [ht.2.2.2.2.2.2, Nat.card_coe_set_eq, hc]
  rfl

private theorem e6ModelRank : Module.finrank ℂ (Algebra e6Cartan) = 78 := by
  obtain ⟨b, hb, _, hA⟩ := e6BasisData
  have ht := finiteType_spec ExceptionalE.e6Roots ExceptionalE.e6_isRootSystem
    ExceptionalE.e6Regular ExceptionalE.e6_basis.1 b hb e6Cartan hA
  have hc := ExceptionalE.e6_count.1
  rw [ht.2.2.2.2.2.2, Nat.card_coe_set_eq, hc]
  rfl

private theorem homInjectiveOfNonzero {L K : Type*} [LieRing L] [LieAlgebra ℂ L]
    [LieRing K] [LieAlgebra ℂ K] (hs : LieAlgebra.IsSimple ℂ L)
    (φ : L →ₗ⁅ℂ⁆ K) {x : L} (hx : φ x ≠ 0) : Function.Injective φ := by
  apply (LieHom.ker_eq_bot φ).mp
  rcases hs.eq_bot_or_eq_top φ.ker with hb | ht
  · exact hb
  · exact (hx (LieHom.mem_ker.mp (ht.symm ▸ LieSubmodule.mem_top x))).elim

private theorem cartanGeneratorIndependent : LinearIndependent ℂ (h e6Cartan) := by
  obtain ⟨b, hb⟩ := (triangular_of_cartanConditions e6Cartan e6CartanConditions).2.1
  have heq : (cartan e6Cartan).subtype ∘ b = h e6Cartan := funext hb
  rw [← heq]
  exact b.linearIndependent.map' (cartan e6Cartan).subtype (Submodule.ker_subtype _)

private theorem foldedHLast_ne_zero :
    foldGenerators (h e6Cartan) 3 ≠ 0 := by
  exact cartanGeneratorIndependent.ne_zero 5

private theorem blackHLast_ne_zero : blackH 3 ≠ 0 := by
  exact cartanGeneratorIndependent.ne_zero 5

private def liftFixed {A : Matrix (Fin 4) (Fin 4) ℤ}
    (ha : ∀ i j, i ≠ j → A i j ≤ 0)
    {a : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan}
    {E F H : Fin 4 → Algebra e6Cartan} (hr : RelationsHold A E F H)
    (he : ∀ i, a (E i) = E i) (hf : ∀ i, a (F i) = F i)
    (hh : ∀ i, a (H i) = H i) : Algebra A →ₗ⁅ℂ⁆ complexFixed a := by
  let φ := lift A ha E F H hr
  have hcomp : a.toLieHom.comp φ = φ := by
    apply Serre.hom_ext A
    · intro i
      simpa [φ] using he i
    · intro i
      simpa [φ] using hf i
    · intro i
      simpa [φ] using hh i
  exact
    { toLinearMap := φ.toLinearMap.codRestrict (complexFixed a).toSubmodule
        (fun x => LieHom.congr_fun hcomp x)
      map_lie' := by intro x y; apply Subtype.ext; exact φ.map_lie _ _ }

private theorem liftFixed_apply_h {A : Matrix (Fin 4) (Fin 4) ℤ}
    (ha : ∀ i j, i ≠ j → A i j ≤ 0)
    {a : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan}
    {E F H : Fin 4 → Algebra e6Cartan} (hr : RelationsHold A E F H)
    (he : ∀ i, a (E i) = E i) (hf : ∀ i, a (F i) = F i)
    (hh : ∀ i, a (H i) = H i) (i : Fin 4) :
    ((liftFixed ha hr he hf hh (h A i)) : Algebra e6Cartan) = H i := by
  change lift A ha E F H hr (h A i) = H i
  simp

private theorem fold_fixed (a : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan)
    (ha : HasColor (e e6Cartan) (f e6Cartan) (h e6Cartan) 0 a) :
    (∀ i, a (foldGenerators (e e6Cartan) i) = foldGenerators (e e6Cartan) i) ∧
    (∀ i, a (foldGenerators (f e6Cartan) i) = foldGenerators (f e6Cartan) i) ∧
    (∀ i, a (foldGenerators (h e6Cartan) i) = foldGenerators (h e6Cartan) i) := by
  have hE := fun i => (ha i).1
  have hF := fun i => (ha i).2.1
  have hH := fun i => (ha i).2.2
  refine ⟨?_, ?_, ?_⟩ <;> intro i <;> fin_cases i <;>
    simp [foldGenerators, hE, hF, hH, vertexColor, colorSign, diagramInvolution, add_comm]

private theorem black_fold_fixed (a : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan)
    (ha : HasColor (e e6Cartan) (f e6Cartan) (h e6Cartan) (1, 0) a) :
    (∀ i, a (blackE i) = blackE i) ∧ (∀ i, a (blackF i) = blackF i) ∧
      (∀ i, a (blackH i) = blackH i) := by
  have hE := fun i => (ha i).1
  have hF := fun i => (ha i).2.1
  have hH := fun i => (ha i).2.2
  refine ⟨?_, ?_, ?_⟩ <;> intro i <;> fin_cases i <;>
    norm_num [blackE, blackF, blackH, hE, hF, hH, vertexColor, colorSign,
      diagramInvolution, LieEquiv.map_lie, lie_neg, neg_lie] <;>
    first
    | rw [← lie_skew (e e6Cartan 2) (e e6Cartan 1),
        ← lie_skew (e e6Cartan 2) (e e6Cartan 3)] <;> module
    | rw [← lie_skew (f e6Cartan 1) (f e6Cartan 2),
        ← lie_skew (f e6Cartan 3) (f e6Cartan 2)] <;> module
    | abel

private theorem f4FixedEmbedding (hr : foldedSerreType)
    (a : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan)
    (ha : HasColor (e e6Cartan) (f e6Cartan) (h e6Cartan) 0 a) :
    ∃ φ : Algebra f4Cartan →ₗ⁅ℂ⁆ complexFixed a, Function.Injective φ := by
  obtain ⟨he, hf, hh⟩ := fold_fixed a ha
  have ho : ∀ i j, i ≠ j → f4Cartan i j ≤ 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  let φ := liftFixed ho hr he hf hh
  refine ⟨φ, homInjectiveOfNonzero f4Model.2.1 φ (x := h f4Cartan 3) ?_⟩
  intro hz
  apply foldedHLast_ne_zero
  rw [← liftFixed_apply_h ho hr he hf hh 3]
  exact congrArg Subtype.val hz

private theorem c4FixedEmbedding (hr : blackFoldedSerreType)
    (a : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan)
    (ha : HasColor (e e6Cartan) (f e6Cartan) (h e6Cartan) (1, 0) a) :
    ∃ φ : Algebra c4Cartan →ₗ⁅ℂ⁆ complexFixed a, Function.Injective φ := by
  obtain ⟨he, hf, hh⟩ := black_fold_fixed a ha
  have ho : ∀ i j, i ≠ j → c4Cartan i j ≤ 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  let φ := liftFixed ho hr he hf hh
  refine ⟨φ, homInjectiveOfNonzero c4Model.2.1 φ (x := h c4Cartan 3) ?_⟩
  intro hz
  apply blackHLast_ne_zero
  rw [← liftFixed_apply_h ho hr he hf hh 3]
  exact congrArg Subtype.val hz

private theorem fixedEquiv_of_rank_bound {A : Matrix (Fin 4) (Fin 4) ℤ}
    {a : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan}
    (φ : Algebra A →ₗ⁅ℂ⁆ complexFixed a) (hφ : Function.Injective φ)
    (hd : Module.finrank ℂ (complexFixed a) ≤ Module.finrank ℂ (Algebra A)) :
    Nonempty (Algebra A ≃ₗ⁅ℂ⁆ complexFixed a) ∧
      Module.finrank ℂ (complexFixed a) = Module.finrank ℂ (Algebra A) := by
  have hEq := le_antisymm hd (LinearMap.finrank_le_finrank_of_injective
    (f := φ.toLinearMap) hφ)
  have hRange := (φ.equivRangeOfInjective hφ).toLinearEquiv.finrank_eq
  have htop : φ.toLinearMap.range = ⊤ := Submodule.eq_top_of_finrank_eq
    (hRange.symm.trans hEq.symm)
  exact ⟨⟨LieEquiv.ofBijective φ ⟨hφ, LinearMap.range_eq_top.mp htop⟩⟩, hEq⟩

private theorem whiteFixed (hr : foldedSerreType)
    (a : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan) (ha : Function.Involutive a)
    (hc : HasColor (e e6Cartan) (f e6Cartan) (h e6Cartan) 0 a) :
    Nonempty (Algebra f4Cartan ≃ₗ⁅ℂ⁆ complexFixed a) ∧
      Module.finrank ℂ (complexFixed a) = 52 := by
  have hle := fixedRank_le a ha (fun i => (hc i).2.2) e6Coefficients
    (fun _ h => h) (fun c hc hnc => (hnc hc).elim)
  rw [whiteRootCount] at hle
  obtain ⟨f, hf⟩ := f4FixedEmbedding hr a hc
  have hBound : Module.finrank ℂ (complexFixed a) ≤ Module.finrank ℂ (Algebra f4Cartan) := by
    rw [f4Model.2.2]
    exact hle
  simpa only [f4Model.2.2] using fixedEquiv_of_rank_bound f hf hBound

private theorem allWhite_fixed_on_fixedRoot (hr : foldedSerreType)
    (a : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan) (ha : Function.Involutive a)
    (hc : HasColor (e e6Cartan) (f e6Cartan) (h e6Cartan) 0 a)
    {c : QVec 6} (hcf : c ∈ fixedRoots)
    {x : Algebra e6Cartan} (hx : x ∈ weightSpace e6Cartan (coefficientWeight c)) :
    a x = x := by
  classical
  have hm := (Finset.mem_filter.mp hcf).1
  have hp : permuteCoefficients c = c := funext (Finset.mem_filter.mp hcf).2
  by_contra hax
  let W := weightSpace e6Cartan (coefficientWeight c)
  let y := a x - x
  have hy : y ∈ W := W.sub_mem (by
    simpa only [hp] using apply_mem_permutedWeight a (fun i => (hc i).2.2) c hx) hx
  have hyn : (⟨y, hy⟩ : W) ≠ 0 := fun hz => hax (sub_eq_zero.mp (congrArg Subtype.val hz))
  have hdim : Module.finrank ℂ W = 1 := e6WeightCover.1 c hm
  have hline := (finrank_eq_one_iff_of_nonzero' (⟨y, hy⟩ : W) hyn).mp hdim
  have havg : fixedAverage a ha y = 0 := by
    simp only [y, map_sub, fixedAverage_invariant, sub_self]
  let S := e6Coefficients.erase c
  have hv (d : QVec 6) (hd : d ∈ e6Coefficients) (hds : d ∉ S) (z : Algebra e6Cartan)
      (hz : z ∈ weightSpace e6Cartan (coefficientWeight d)) : fixedAverage a ha z = 0 := by
    have hdc : d = c := by
      by_contra hdc
      exact hds (Finset.mem_erase.mpr ⟨hdc, hd⟩)
    subst d
    obtain ⟨k, hk⟩ := hline ⟨z, hz⟩
    have hkz : k • y = z := congrArg Subtype.val hk
    rw [← hkz, map_smul, havg, smul_zero]
  have hle := fixedRank_le a ha (fun i => (hc i).2.2) S (Finset.erase_subset _ _) hv
  have hsub : S.image foldRoot ⊆ (e6Coefficients.image foldRoot).erase (foldRoot c) := by
    intro r hrr
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hrr
    obtain ⟨hdn, hdm⟩ := Finset.mem_erase.mp hd
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_image_of_mem _ hdm⟩
    intro hEq
    have := (foldRoot_fibers c hm d hdm).mp hEq.symm
    exact hdn (by simpa [hp] using this)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_image_of_mem _ hm), whiteRootCount] at hcard
  have hEq := (whiteFixed hr a ha hc).2
  omega


private theorem apply_signed_word
    (d : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan)
    (E : Fin 6 → Algebra e6Cartan)
    (hE : ∀ i, d (E i) = (-1 : ℂ) ^ (Finsupp.single i (1 : ℕ)) 2 • E i)
    (w : BracketWord (Fin 6)) :
    d (w.evaluate E) = (-1 : ℂ) ^ (w.degree 2) • w.evaluate E := by
  induction w with
  | generator i => exact hE i
  | bracket v w hv hw =>
    simp only [BracketWord.evaluate, BracketWord.degree, d.map_lie, hv, hw, smul_lie,
      lie_smul, smul_smul, Finsupp.add_apply, pow_add]
    rw [mul_comm]

private theorem coefficientVector_repr
    (b : Module.Basis (Fin 6) ℝ ExceptionalE.e6Space)
    (c : QVec 6) (i : Fin 6) : b.repr (coefficientVector b c) i = (c i : ℝ) := by
  simp [coefficientVector, Finsupp.single_apply, Finset.sum_apply]

private theorem root_coefficient_den_eq_one {c : QVec 6} (hc : c ∈ e6Coefficients)
    (i : Fin 6) : (c i).den = 1 := by
  obtain ⟨b, _, hb, hA⟩ := e6BasisData
  have hroot := (coefficientVector_root_iff b hb (coefficientVector b c)).mpr ⟨c, hc, rfl⟩
  have hweight := coefficientWeight_eq b hA c
  have hnonzero : coefficientWeight c ≠ 0 := by
    rw [hweight, ← rootWeight_zero b]
    exact fun h => ExceptionalE.e6_isRootSystem.nonzero _ hroot (rootWeight_injective b h)
  have hne : weightSpace e6Cartan (coefficientWeight c) ≠ ⊥ := by
    have hdim := e6WeightCover.1 c hc
    intro h
    rw [h, finrank_bot] at hdim
    exact Nat.zero_ne_one hdim
  suffices h : ∃ z : ℤ, c i = (z : ℚ) by
    obtain ⟨z, hz⟩ := h
    rw [hz, Rat.den_intCast]
  obtain ⟨w, he | hf⟩ := nonzero_weight_word e6Cartan _ hnonzero hne
  · have hw : w.rootVector b = coefficientVector b c := by
      apply rootWeight_injective b
      rw [w.rootVector_weight e6Cartan b hA, ← he.1, hweight]
    refine ⟨w.degree i, ?_⟩
    have hi : (c i : ℝ) = (w.degree i : ℝ) := by
      simpa only [w.rootVector_repr b, coefficientVector_repr] using
        (congrArg (fun z => b.repr z i) hw).symm
    exact_mod_cast hi
  · have hw : -w.rootVector b = coefficientVector b c := by
      apply rootWeight_injective b
      rw [rootWeight_neg, w.rootVector_weight e6Cartan b hA, ← hf.1, hweight]
    refine ⟨-(w.degree i : ℤ), ?_⟩
    have hi : (c i : ℝ) = -(w.degree i : ℝ) := by
      simpa only [map_neg, Finsupp.neg_apply, w.rootVector_repr b, coefficientVector_repr] using
        (congrArg (fun z => b.repr z i) hw).symm
    exact_mod_cast hi

private theorem odd_weight_sign
    (d : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan)
    (he : ∀ i, d (e e6Cartan i) = (-1 : ℂ) ^ (Finsupp.single i (1 : ℕ)) 2 • e e6Cartan i)
    (hf : ∀ i, d (f e6Cartan i) = (-1 : ℂ) ^ (Finsupp.single i (1 : ℕ)) 2 • f e6Cartan i)
    {c : QVec 6} (hc : c ∈ e6Coefficients) (ho : (c 2).num % 2 ≠ 0)
    {x : Algebra e6Cartan} (hx : x ∈ weightSpace e6Cartan (coefficientWeight c)) :
    d x = -x := by
  classical
  obtain ⟨b, _, hb, hA⟩ := e6BasisData
  have hroot := (coefficientVector_root_iff b hb (coefficientVector b c)).mpr ⟨c, hc, rfl⟩
  have hweight := coefficientWeight_eq b hA c
  have hn : coefficientWeight c ≠ 0 := by
    rw [hweight, ← rootWeight_zero b]
    exact fun h => ExceptionalE.e6_isRootSystem.nonzero _ hroot (rootWeight_injective b h)
  let P := LinearMap.ker (d.toLinearMap + LinearMap.id)
  have hpow (w : BracketWord (Fin 6)) : (c 2).num = w.degree 2 ∨
      (c 2).num = -(w.degree 2 : ℤ) → (-1 : ℂ) ^ (w.degree 2) = -1 := by
    intro hdeg
    have hodd : Odd ((w.degree 2 : ℕ) : ℤ) := by
      rw [Int.odd_iff]
      rcases hdeg with hdeg | hdeg <;> omega
    simpa only [zpow_natCast] using (hodd.neg_one_zpow (α := ℂ))
  have hp : positiveWordSpace e6Cartan (coefficientWeight c) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    have hv : w.rootVector b = coefficientVector b c := by
      apply rootWeight_injective b
      rw [w.rootVector_weight e6Cartan b hA, hw, hweight]
    have h2 : (c 2 : ℝ) = (w.degree 2 : ℝ) := by
      simpa only [w.rootVector_repr b, coefficientVector_repr] using
        (congrArg (fun z => b.repr z 2) hv).symm
    have h2q : c 2 = (w.degree 2 : ℚ) := by exact_mod_cast h2
    change d (w.evaluate (e e6Cartan)) + w.evaluate (e e6Cartan) = 0
    rw [apply_signed_word d _ he, hpow w (Or.inl (by rw [h2q, Rat.num_natCast]))]
    simp
  have hm : negativeWordSpace e6Cartan (coefficientWeight c) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    have hv : -w.rootVector b = coefficientVector b c := by
      apply rootWeight_injective b
      rw [rootWeight_neg, w.rootVector_weight e6Cartan b hA, hw, hweight]
    have h2 : (c 2 : ℝ) = -(w.degree 2 : ℝ) := by
      simpa only [map_neg, Finsupp.neg_apply, w.rootVector_repr b, coefficientVector_repr] using
        (congrArg (fun z => b.repr z 2) hv).symm
    have h2q : c 2 = -(w.degree 2 : ℚ) := by exact_mod_cast h2
    change d (w.evaluate (f e6Cartan)) + w.evaluate (f e6Cartan) = 0
    rw [apply_signed_word d _ hf, hpow w (Or.inr (by rw [h2q, Rat.neg_num, Rat.num_natCast]))]
    simp
  have hP : weightSpace e6Cartan (coefficientWeight c) ≤ P := by
    rw [weightSpace_eq_signedWordSpace e6Cartan (weightSpace_iSupIndep e6Cartan)]
    simpa only [signedWordSpace, if_neg hn, bot_sup_eq, sup_le_iff] using And.intro hm hp
  exact eq_neg_of_add_eq_zero_left (hP hx)

private theorem blackFixed (hrw : foldedSerreType) (hrb : blackFoldedSerreType)
    (aW aB : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan)
    (haW : Function.Involutive aW) (haB : Function.Involutive aB)
    (hW : HasColor (e e6Cartan) (f e6Cartan) (h e6Cartan) 0 aW)
    (hB : HasColor (e e6Cartan) (f e6Cartan) (h e6Cartan) (1, 0) aB)
    (hc : blackSimpleRootsType) :
    Nonempty (Algebra c4Cartan ≃ₗ⁅ℂ⁆ complexFixed aB) ∧
      Module.finrank ℂ (complexFixed aB) = 36 := by
  let d := aW.trans aB
  have hE (i : Fin 6) :
      d (e e6Cartan i) = (-1 : ℂ) ^ (Finsupp.single i (1 : ℕ)) 2 • e e6Cartan i := by
    change aB (aW (e e6Cartan i)) = _
    rw [(hW i).1, map_smul, (hB (diagramInvolution i)).1]
    fin_cases i <;> norm_num [vertexColor, colorSign, diagramInvolution, Finsupp.single_apply]
  have hF (i : Fin 6) :
      d (f e6Cartan i) = (-1 : ℂ) ^ (Finsupp.single i (1 : ℕ)) 2 • f e6Cartan i := by
    change aB (aW (f e6Cartan i)) = _
    rw [(hW i).2.1, map_smul, (hB (diagramInvolution i)).2.1]
    fin_cases i <;> norm_num [vertexColor, colorSign, diagramInvolution, Finsupp.single_apply]
  let S := (e6Coefficients \ fixedRoots) ∪ evenFixedRoots
  have hs : S ⊆ e6Coefficients := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact (Finset.mem_sdiff.mp hc).1
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1
  have hv (c : QVec 6) (hcm : c ∈ e6Coefficients) (hcs : c ∉ S) (x : Algebra e6Cartan)
      (hx : x ∈ weightSpace e6Cartan (coefficientWeight c)) : fixedAverage aB haB x = 0 := by
    have hcf : c ∈ fixedRoots := by
      by_contra hcf
      exact hcs (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hcm, hcf⟩))
    have ho : (c 2).num % 2 ≠ 0 := by
      intro he
      exact hcs (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hcf, root_coefficient_den_eq_one hcm 2, he⟩))
    have hdx := odd_weight_sign d hE hF hcm ho hx
    change aB (aW x) = -x at hdx
    rw [allWhite_fixed_on_fixedRoot hrw aW haW hW hcf hx] at hdx
    apply Subtype.ext
    rw [fixedAverage_apply_coe, hdx, add_neg_cancel, smul_zero]
    rfl
  have hle := fixedRank_le aB haB (fun i => (hB i).2.2) S hs hv
  change Module.finrank ℂ (complexFixed aB) ≤ 4 + blackRoots.card at hle
  rw [hc.1] at hle
  obtain ⟨f, hf⟩ := c4FixedEmbedding hrb aB hB
  have hBound : Module.finrank ℂ (complexFixed aB) ≤ Module.finrank ℂ (Algebra c4Cartan) := by
    rw [c4Model.2.2]
    exact hle
  simpa only [c4Model.2.2] using fixedEquiv_of_rank_bound f hf hBound

private def simpleReflectionLift (i : Fin 6) : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan :=
  ((positiveExp e6Cartan i).trans (negativeExp e6Cartan i)).trans (positiveExp e6Cartan i)

private theorem e6_diagonal (i : Fin 6) : e6Cartan i i = 2 := e6CartanConditions.1 i

private theorem e6_off_diagonal (i j : Fin 6) (hij : i ≠ j) :
    e6Cartan i j = 0 ∨ e6Cartan i j = -1 := by
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide

private theorem e6_e_square (i j : Fin 6) (hij : i ≠ j) :
    ⁅e e6Cartan i, ⁅e e6Cartan i, e e6Cartan j⁆⁆ = 0 := by
  have hs := native_serre_e e6Cartan i j
  rcases e6_off_diagonal i j hij with h | h
  · have hz : ⁅e e6Cartan i, e e6Cartan j⁆ = 0 := by simpa [h, iterBracket] using hs
    rw [hz, lie_zero]
  · simpa [h, iterBracket] using hs

private theorem e6_f_square (i j : Fin 6) (hij : i ≠ j) :
    ⁅f e6Cartan i, ⁅f e6Cartan i, f e6Cartan j⁆⁆ = 0 := by
  have hs := native_serre_f e6Cartan i j
  rcases e6_off_diagonal i j hij with h | h
  · have hz : ⁅f e6Cartan i, f e6Cartan j⁆ = 0 := by simpa [h, iterBracket] using hs
    rw [hz, lie_zero]
  · simpa [h, iterBracket] using hs

private theorem positiveExp_f_self (i : Fin 6) :
    positiveExp e6Cartan i (f e6Cartan i) = f e6Cartan i + h e6Cartan i - e e6Cartan i := by
  have heh : ⁅e e6Cartan i,h e6Cartan i⁆ = -(2 : ℂ) • e e6Cartan i := by
    rw [← lie_skew, he_complex, e6_diagonal, neg_smul]
    norm_num
  rw [positiveExp, innerExp_apply_of_cube_zero]
  · rw [Serre.ef, if_pos rfl, heh]
    module
  · rw [Serre.ef, if_pos rfl, heh, lie_smul, lie_self, smul_zero]

private theorem negativeExp_f_self (i : Fin 6) :
    negativeExp e6Cartan i (f e6Cartan i) = f e6Cartan i := by
  rw [negativeExp, innerExp_apply_of_square_zero]
  · simp [neg_lie]
  · simp [neg_lie]

private theorem reflection_e_self (i : Fin 6) :
    simpleReflectionLift i (e e6Cartan i) = -f e6Cartan i := by
  change positiveExp e6Cartan i (negativeExp e6Cartan i (positiveExp e6Cartan i (e e6Cartan i))) = _
  rw [positiveExp_self, negativeExp_opposite _ _ (e6_diagonal i), map_sub, map_add,
    positiveExp_self, positiveExp_cartan, positiveExp_f_self, e6_diagonal]
  norm_num
  module

private theorem reflection_f_self (i : Fin 6) :
    simpleReflectionLift i (f e6Cartan i) = -e e6Cartan i := by
  change positiveExp e6Cartan i (negativeExp e6Cartan i (positiveExp e6Cartan i (f e6Cartan i))) = _
  rw [positiveExp_f_self, map_sub, map_add, negativeExp_f_self, negativeExp_cartan,
    negativeExp_opposite _ _ (e6_diagonal i), e6_diagonal]
  have heq : f e6Cartan i + (h e6Cartan i - (↑(2 : ℤ) : ℂ) • f e6Cartan i) -
      (e e6Cartan i + h e6Cartan i - f e6Cartan i) = -e e6Cartan i := by
    norm_num
    module
  rw [heq, map_neg, positiveExp_self]

private theorem reflection_e_ne (i j : Fin 6) (hij : i ≠ j) :
    simpleReflectionLift i (e e6Cartan j) =
      (1 + (e6Cartan i j : ℂ)) • e e6Cartan j + ⁅e e6Cartan i,e e6Cartan j⁆ := by
  let P := positiveExp e6Cartan i
  let N := negativeExp e6Cartan i
  let x := ⁅e e6Cartan i, e e6Cartan j⁆
  change P (N (P (e e6Cartan j))) = _
  have hPE : P (e e6Cartan j) = e e6Cartan j + x := by
    exact innerExp_apply_of_square_zero _ _ (e6_e_square i j hij)
  have hPX : P x = x := by
    unfold P positiveExp
    rw [innerExp_apply_of_square_zero]
    · rw [show ⁅e e6Cartan i, x⁆ = 0 from e6_e_square i j hij, add_zero]
    · rw [show ⁅e e6Cartan i, x⁆ = 0 from e6_e_square i j hij, lie_zero]
  have hNE_bracket : ⁅-(f e6Cartan i), e e6Cartan j⁆ = 0 := by
    rw [neg_lie, ← lie_skew (f e6Cartan i) (e e6Cartan j), Serre.ef,
      if_neg hij.symm, neg_zero, neg_zero]
  have hNE : N (e e6Cartan j) = e e6Cartan j := by
    unfold N negativeExp
    rw [innerExp_apply_of_square_zero]
    · simp [hNE_bracket]
    · rw [hNE_bracket, lie_zero]
  have hNX_bracket : ⁅-(f e6Cartan i), x⁆ = (e6Cartan i j : ℂ) • e e6Cartan j := by
    have hself : ⁅-(f e6Cartan i), e e6Cartan i⁆ = h e6Cartan i := by
      rw [neg_lie, ← lie_skew (f e6Cartan i) (e e6Cartan i), Serre.ef, if_pos rfl, neg_neg]
    dsimp [x]
    rw [leibniz_lie, hself, hNE_bracket, lie_zero, add_zero, he_complex]
  have hNX : N x = x + (e6Cartan i j : ℂ) • e e6Cartan j := by
    unfold N negativeExp
    rw [innerExp_apply_of_square_zero]
    · rw [hNX_bracket]
    · rw [hNX_bracket, lie_smul, hNE_bracket, smul_zero]
  rw [hPE, map_add N, hNE, hNX]
  rcases e6_off_diagonal i j hij with h | h
  · have hx : x = 0 := by simpa [h, iterBracket, x] using native_serre_e e6Cartan i j
    simp [h, hx, hPE]
    exact hx
  · norm_num [h, ← sub_eq_add_neg]
    exact hPX

private theorem reflection_f_ne (i j : Fin 6) (hij : i ≠ j) :
    simpleReflectionLift i (f e6Cartan j) =
      (1 + (e6Cartan i j : ℂ)) • f e6Cartan j - ⁅f e6Cartan i,f e6Cartan j⁆ := by
  let P := positiveExp e6Cartan i
  let N := negativeExp e6Cartan i
  let x := ⁅f e6Cartan i, f e6Cartan j⁆
  change P (N (P (f e6Cartan j))) = _
  have hPF_bracket : ⁅e e6Cartan i, f e6Cartan j⁆ = 0 := by rw [Serre.ef, if_neg hij]
  have hPF : P (f e6Cartan j) = f e6Cartan j := by
    unfold P positiveExp
    rw [innerExp_apply_of_square_zero]
    · simp [hPF_bracket]
    · rw [hPF_bracket, lie_zero]
  have hNF : N (f e6Cartan j) = f e6Cartan j - x := by
    unfold N negativeExp
    rw [innerExp_apply_of_square_zero]
    · simp [x, neg_lie, sub_eq_add_neg]
    · rw [neg_lie, neg_lie, lie_neg, neg_neg, e6_f_square _ _ hij]
  have hPX_bracket : ⁅e e6Cartan i, x⁆ = -(e6Cartan i j : ℂ) • f e6Cartan j := by
    dsimp [x]
    rw [leibniz_lie, Serre.ef e6Cartan i i, if_pos rfl, hPF_bracket, lie_zero, add_zero, hf_complex]
  have hPX : P x = x - (e6Cartan i j : ℂ) • f e6Cartan j := by
    unfold P positiveExp
    rw [innerExp_apply_of_square_zero]
    · rw [hPX_bracket, neg_smul, sub_eq_add_neg]
    · rw [hPX_bracket, lie_smul, hPF_bracket, smul_zero]
  rw [hPF, hNF, map_sub P, hPF, hPX]
  module

private theorem reflection_h (i j : Fin 6) :
    simpleReflectionLift i (h e6Cartan j) =
      h e6Cartan j - (e6Cartan j i : ℂ) • h e6Cartan i :=
  exponential_reflection_cartan e6Cartan i (e6_diagonal i) j


private theorem reflection_e (i j : Fin 6) :
    simpleReflectionLift i (e e6Cartan j) =
      if i = j then -f e6Cartan j else
      if e6Cartan i j = 0 then e e6Cartan j else ⁅e e6Cartan i,e e6Cartan j⁆ := by
  by_cases hij : i = j
  · subst j
    simp [reflection_e_self]
  rw [ite_eq_right hij, reflection_e_ne i j hij]
  rcases e6_off_diagonal i j hij with ha | ha
  · have hz : ⁅e e6Cartan i, e e6Cartan j⁆ = 0 := by
      simpa [ha, iterBracket] using native_serre_e e6Cartan i j
    simp [ha, hz]
  · norm_num [ha]

private theorem reflection_f (i j : Fin 6) :
    simpleReflectionLift i (f e6Cartan j) =
      if i = j then -e e6Cartan j else
      if e6Cartan i j = 0 then f e6Cartan j else -⁅f e6Cartan i,f e6Cartan j⁆ := by
  by_cases hij : i = j
  · subst j
    simp [reflection_f_self]
  rw [ite_eq_right hij, reflection_f_ne i j hij]
  rcases e6_off_diagonal i j hij with ha | ha
  · have hz : ⁅f e6Cartan i, f e6Cartan j⁆ = 0 := by
      simpa [ha, iterBracket] using native_serre_f e6Cartan i j
    simp [ha, hz]
  · norm_num [ha]

private theorem commutes_with_conjugation_of_generators
    (ω : Conjugation (Algebra e6Cartan)) (a : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan)
    (hE : ∀ i, ω.map (a (e e6Cartan i)) = a (ω.map (e e6Cartan i)))
    (hF : ∀ i, ω.map (a (f e6Cartan i)) = a (ω.map (f e6Cartan i)))
    (hH : ∀ i, ω.map (a (h e6Cartan i)) = a (ω.map (h e6Cartan i))) :
    Intertwines ω ω a := by
  let K : LieSubalgebra ℂ (Algebra e6Cartan) :=
    { carrier := {x | ω.map (a x) = a (ω.map x)}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change ω.map (a x) = a (ω.map x) at hx
        change ω.map (a y) = a (ω.map y) at hy
        change ω.map (a (x + y)) = a (ω.map (x + y))
        simp only [map_add, hx, hy]
      smul_mem' := by
        intro r x hx
        change ω.map (a x) = a (ω.map x) at hx
        change ω.map (a (r • x)) = a (ω.map (r • x))
        rw [map_smul, ω.antilinear, ω.antilinear, map_smul, hx]
      lie_mem' := by
        intro x y hx hy
        change ω.map (a x) = a (ω.map x) at hx
        change ω.map (a y) = a (ω.map y) at hy
        change ω.map (a ⁅x,y⁆) = a (ω.map ⁅x,y⁆)
        rw [a.map_lie, ω.map.map_lie, ω.map.map_lie, a.map_lie, hx, hy] }
  have htop := Serre.generators_generate e6Cartan K hE hF hH
  intro x
  have hx : x ∈ K := by rw [htop]; trivial
  exact hx

private theorem reflection_compact (ω : Conjugation (Algebra e6Cartan))
    (hω : ∀ j, ω.map (e e6Cartan j) = -f e6Cartan j ∧
      ω.map (f e6Cartan j) = -e e6Cartan j ∧ ω.map (h e6Cartan j) = -h e6Cartan j)
    (i : Fin 6) : Intertwines ω ω (simpleReflectionLift i) := by
  have he := fun j => (hω j).1
  have hf := fun j => (hω j).2.1
  have hh := fun j => (hω j).2.2
  apply commutes_with_conjugation_of_generators
  · intro j
    simp only [he, map_neg, reflection_e, reflection_f]
    split_ifs <;> simp [he, hf, ω.map.map_lie, neg_lie, lie_neg]
  · intro j
    simp only [hf, map_neg, reflection_e, reflection_f]
    split_ifs <;> simp [he, hf, ω.map.map_lie, neg_lie, lie_neg]
  · intro j
    rw [hh, map_neg, reflection_h, map_sub, ω.antilinear, hh, hh]
    fin_cases i <;> fin_cases j <;>
      norm_num [e6Cartan, Matrix.cons_val_zero, Matrix.cons_val_succ] <;> module

private def pairedCorrection : DiagramData e6Cartan where
  perm := Equiv.refl _
  involutive := fun _ => rfl
  preserves := fun _ _ => rfl
  sign := fun i => if i = 1 then -1 else 1
  sign_cases := fun i => by by_cases hi : i = 1 <;> simp [hi]
  paired := fun i hi => (hi rfl).elim

private theorem correction_exists (ω : Conjugation (Algebra e6Cartan))
    (hω : ∀ j, ω.map (e e6Cartan j) = -f e6Cartan j ∧
      ω.map (f e6Cartan j) = -e e6Cartan j ∧ ω.map (h e6Cartan j) = -h e6Cartan j) :
    ∃ t : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan, Intertwines ω ω t ∧
      ∀ i, t (e e6Cartan i) = (if i = 1 then (-1 : ℂ) else 1) • e e6Cartan i ∧
        t (f e6Cartan i) = (if i = 1 then (-1 : ℂ) else 1) • f e6Cartan i ∧
        t (h e6Cartan i) = h e6Cartan i := by
  obtain ⟨_, t, hcomm, _, hgen, _⟩ :=
    _root_.LieAlgebrasAndRepresentations.StableCartanVoganData.realize e6Cartan
      e6CartanConditions.2.1 pairedCorrection ω (e e6Cartan) (f e6Cartan) (h e6Cartan)
      ⟨LieEquiv.refl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩ hω
  exact ⟨t, hcomm, hgen⟩

private theorem intertwine_of_generators
    (a b g : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan)
    (hE : ∀ i, b (g (e e6Cartan i)) = g (a (e e6Cartan i)))
    (hF : ∀ i, b (g (f e6Cartan i)) = g (a (f e6Cartan i)))
    (hH : ∀ i, b (g (h e6Cartan i)) = g (a (h e6Cartan i))) :
    ∀ x, b (g x) = g (a x) := by
  have heq : b.toLieHom.comp g.toLieHom = g.toLieHom.comp a.toLieHom :=
    Serre.hom_ext e6Cartan hE hF hH
  exact LieHom.congr_fun heq

private theorem conjugacy_black_branch
    (ω : Conjugation (Algebra e6Cartan))
    (hω : ∀ j, ω.map (e e6Cartan j) = -f e6Cartan j ∧
      ω.map (f e6Cartan j) = -e e6Cartan j ∧ ω.map (h e6Cartan j) = -h e6Cartan j)
    (a b : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan)
    (ha : HasColor (e e6Cartan) (f e6Cartan) (h e6Cartan) (1, 0) a)
    (hb : HasColor (e e6Cartan) (f e6Cartan) (h e6Cartan) (1, 1) b) :
    ∃ g : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan, Intertwines ω ω g ∧
      ∀ x, b (g x) = g (a x) := by
  obtain ⟨t, ht, htg⟩ := correction_exists ω hω
  let g := (simpleReflectionLift 2).trans t
  have haE := fun j => (ha j).1
  have haF := fun j => (ha j).2.1
  have haH := fun j => (ha j).2.2
  have hbE := fun j => (hb j).1
  have hbF := fun j => (hb j).2.1
  have hbH := fun j => (hb j).2.2
  have htE := fun j => (htg j).1
  have htF := fun j => (htg j).2.1
  have htH := fun j => (htg j).2.2
  refine ⟨g, ?_, ?_⟩
  · intro x
    change ω.map (t (simpleReflectionLift 2 x)) = t (simpleReflectionLift 2 (ω.map x))
    rw [ht, reflection_compact ω hω]
  · apply intertwine_of_generators
    · intro j
      fin_cases j <;>
        norm_num [g, haE, hbE, htE, haF, hbF, htF, reflection_e, reflection_f, vertexColor,
          colorSign, diagramInvolution, e6Cartan, Matrix.cons_val_zero, Matrix.cons_val_succ,
          LieEquiv.map_lie, smul_lie, lie_smul]
    · intro j
      fin_cases j <;>
        norm_num [g, haF, hbF, htF, haE, hbE, htE, reflection_e, reflection_f, vertexColor,
          colorSign, diagramInvolution, e6Cartan, Matrix.cons_val_zero, Matrix.cons_val_succ,
          LieEquiv.map_lie, smul_lie, lie_smul]
    · intro j
      fin_cases j <;>
        norm_num [g, haH, hbH, htH, reflection_h, diagramInvolution, e6Cartan,
          Matrix.cons_val_zero, Matrix.cons_val_succ]

private theorem conjugacy_black_arm
    (ω : Conjugation (Algebra e6Cartan))
    (hω : ∀ j, ω.map (e e6Cartan j) = -f e6Cartan j ∧
      ω.map (f e6Cartan j) = -e e6Cartan j ∧ ω.map (h e6Cartan j) = -h e6Cartan j)
    (a b : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan)
    (ha : HasColor (e e6Cartan) (f e6Cartan) (h e6Cartan) (0, 1) a)
    (hb : HasColor (e e6Cartan) (f e6Cartan) (h e6Cartan) (1, 1) b) :
    ∃ g : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan, Intertwines ω ω g ∧
      ∀ x, b (g x) = g (a x) := by
  have haE := fun j => (ha j).1
  have haF := fun j => (ha j).2.1
  have haH := fun j => (ha j).2.2
  have hbE := fun j => (hb j).1
  have hbF := fun j => (hb j).2.1
  have hbH := fun j => (hb j).2.2
  refine ⟨simpleReflectionLift 5, reflection_compact ω hω 5, ?_⟩
  apply intertwine_of_generators
  · intro j
    fin_cases j <;>
      norm_num [haE, hbE, haF, hbF, reflection_e, reflection_f, vertexColor, colorSign,
        diagramInvolution, e6Cartan, Matrix.cons_val_zero, Matrix.cons_val_succ,
        LieEquiv.map_lie, smul_lie, lie_smul]
  · intro j
    fin_cases j <;>
      norm_num [haF, hbF, haE, hbE, reflection_e, reflection_f, vertexColor, colorSign,
        diagramInvolution, e6Cartan, Matrix.cons_val_zero, Matrix.cons_val_succ,
        LieEquiv.map_lie, smul_lie, lie_smul]
  · intro j
    fin_cases j <;>
      norm_num [haH, hbH, reflection_h, diagramInvolution, e6Cartan,
        Matrix.cons_val_zero, Matrix.cons_val_succ]

private def CompactConjugate (ω : Conjugation (Algebra e6Cartan))
    (a b : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan) : Prop :=
  ∃ g : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan,
    Intertwines ω ω g ∧ ∀ x, b (g x) = g (a x)

private theorem CompactConjugate.refl (ω : Conjugation (Algebra e6Cartan))
    (a : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan) : CompactConjugate ω a a :=
  ⟨LieEquiv.refl, fun _ => rfl, fun _ => rfl⟩

private theorem CompactConjugate.symm {ω : Conjugation (Algebra e6Cartan)}
    {a b : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan} :
    CompactConjugate ω a b → CompactConjugate ω b a := by
  rintro ⟨g, hw, hg⟩
  refine ⟨g.symm, ?_, ?_⟩
  · intro x
    have h := congrArg g.symm (hw (g.symm x))
    simpa only [g.apply_symm_apply, g.symm_apply_apply] using h.symm
  · intro x
    have h := congrArg g.symm (hg (g.symm x))
    simpa only [g.apply_symm_apply, g.symm_apply_apply] using h.symm

private theorem CompactConjugate.trans {ω : Conjugation (Algebra e6Cartan)}
    {a b c : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan} :
    CompactConjugate ω a b → CompactConjugate ω b c → CompactConjugate ω a c := by
  rintro ⟨g, hgw, hg⟩ ⟨k, hkw, hk⟩
  refine ⟨g.trans k, ?_, ?_⟩
  · intro x
    change ω.map (k (g x)) = k (g (ω.map x))
    rw [hkw, hgw]
  · intro x
    change c (k (g x)) = k (g (a x))
    rw [hk, hg]

private theorem normalized_unique (b : Coloring)
    {a a' : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan}
    (ha : HasColor (e e6Cartan) (f e6Cartan) (h e6Cartan) b a)
    (ha' : HasColor (e e6Cartan) (f e6Cartan) (h e6Cartan) b a') :
    a = a' := by
  have hhom : a.toLieHom = a'.toLieHom := by
    apply Serre.hom_ext e6Cartan
    · exact fun i => (ha i).1.trans (ha' i).1.symm
    · exact fun i => (ha i).2.1.trans (ha' i).2.1.symm
    · exact fun i => (ha i).2.2.trans (ha' i).2.2.symm
  ext x
  exact LieHom.congr_fun hhom x

private theorem conjugates_to_black
    (ω : Conjugation (Algebra e6Cartan))
    (hω : ∀ j, ω.map (e e6Cartan j) = -f e6Cartan j ∧
      ω.map (f e6Cartan j) = -e e6Cartan j ∧ ω.map (h e6Cartan j) = -h e6Cartan j)
    (aB aBoth : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan)
    (hB : HasColor (e e6Cartan) (f e6Cartan) (h e6Cartan) (1, 0) aB)
    (hBoth : HasColor (e e6Cartan) (f e6Cartan) (h e6Cartan) (1, 1) aBoth)
    (b : Coloring) (hb : b ≠ 0) (a : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan)
    (ha : HasColor (e e6Cartan) (f e6Cartan) (h e6Cartan) b a) :
    CompactConjugate ω a aB := by
  have hcases : ∀ b : Coloring, b = 0 ∨ b = (1,0) ∨ b = (0,1) ∨ b = (1,1) := by decide
  have hstep : CompactConjugate ω aB aBoth := conjugacy_black_branch ω hω aB aBoth hB hBoth
  rcases (hcases b).resolve_left hb with rfl | rfl | rfl
  · rw [normalized_unique _ ha hB]
    exact CompactConjugate.refl ω aB
  · exact CompactConjugate.trans (conjugacy_black_arm ω hω a aBoth ha hBoth) hstep.symm
  · rw [normalized_unique _ ha hBoth]
    exact hstep.symm

private def fixedEquiv {M N : Type*} [LieRing M] [LieAlgebra ℂ M] [LieRing N]
    [LieAlgebra ℂ N] (p : M ≃ₗ⁅ℂ⁆ N) (a : M ≃ₗ⁅ℂ⁆ M) (b : N ≃ₗ⁅ℂ⁆ N)
    (hp : ∀ x, b (p x) = p (a x)) : complexFixed a ≃ₗ⁅ℂ⁆ complexFixed b := by
  let f : complexFixed a →ₗ⁅ℂ⁆ complexFixed b :=
    { toFun := fun x => ⟨p x, (hp x).trans (congrArg p x.property)⟩
      map_add' := fun x y => Subtype.ext (map_add p (x : M) (y : M))
      map_smul' := fun r x => Subtype.ext (map_smul p r (x : M))
      map_lie' := by intros; apply Subtype.ext; exact p.map_lie _ _ }
  refine LieEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    exact Subtype.ext (p.injective (congrArg Subtype.val hxy))
  · intro y
    obtain ⟨x, hx⟩ := p.surjective (y : N)
    have hx' : p x = (y : N) := hx
    have hax : a x = x := by
      apply p.injective
      change p (a x) = p x
      rw [← hp, hx']
      exact y.property
    exact ⟨⟨x, hax⟩, Subtype.ext hx⟩

open Specs.LieAlgebrasAndRepresentations.PolarRealStructures (involutionConjugation)
open Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature
  (killingQuadratic killingSignature)

private theorem killingSignature_equiv {M N : Type*} [LieRing M] [LieAlgebra ℝ M]
    [LieRing N] [LieAlgebra ℝ N] (p : M ≃ₗ⁅ℝ⁆ N) :
    killingSignature M = killingSignature N := by
  have hq : QuadraticMap.Equivalent (killingQuadratic M) (killingQuadratic N) :=
    ⟨{ toLinearEquiv := p.toLinearEquiv
       map_app' := fun x => LieAlgebra.killingForm_of_equiv_apply p x x }⟩
  unfold killingSignature
  rw [hq.sigPos_eq, hq.sigNeg_eq]

set_option maxHeartbeats 0 in
theorem outerClassification : outerClassificationType.{u} := by
  intro L _ _ _ ω hc E F H hP hω
  obtain ⟨p, pe, pf, ph⟩ := hP
  let ω₀ := ω.transport p.symm
  have hω₀ (i : Fin 6) : ω₀.map (e e6Cartan i) = -f e6Cartan i ∧
      ω₀.map (f e6Cartan i) = -e e6Cartan i ∧ ω₀.map (h e6Cartan i) = -h e6Cartan i := by
    refine ⟨?_, ?_, ?_⟩
    · change p.symm (ω.map (p (e e6Cartan i))) = _
      rw [pe, (hω i).1, ← pf, map_neg, p.symm_apply_apply]
    · change p.symm (ω.map (p (f e6Cartan i))) = _
      rw [pf, (hω i).2.1, ← pe, map_neg, p.symm_apply_apply]
    · change p.symm (ω.map (p (h e6Cartan i))) = _
      rw [ph, (hω i).2.2, ← ph, map_neg, p.symm_apply_apply]
  have realizeModel : ∀ b : Coloring, ∃ a : Algebra e6Cartan ≃ₗ⁅ℂ⁆ Algebra e6Cartan,
      HasColor (e e6Cartan) (f e6Cartan) (h e6Cartan) b a ∧
        Intertwines ω₀ ω₀ a ∧ Function.Involutive a := by
    exact realizeOuter ω₀ (e e6Cartan) (f e6Cartan) (h e6Cartan)
      ⟨LieEquiv.refl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩ hω₀
  obtain ⟨aW, hW, _, haW⟩ := realizeModel 0
  obtain ⟨aB, hB, _, haB⟩ := realizeModel (1, 0)
  obtain ⟨aBoth, hBoth, _, _⟩ := realizeModel (1, 1)
  have hrW := foldedSerre
  have hrB := blackFoldedSerre
  have hBlackRoots := blackSimpleRoots
  have hWhite := whiteFixed hrW aW haW hW
  have hBlack := blackFixed hrW hrB aW aB haW haB hW hB hBlackRoots
  let model (a : L ≃ₗ⁅ℂ⁆ L) := (p.trans a).trans p.symm
  have hmodel (a : L ≃ₗ⁅ℂ⁆ L) (x : Algebra e6Cartan) :
      a (p x) = p (model a x) := (p.apply_symm_apply _).symm
  have hcol (b : Coloring) (a : L ≃ₗ⁅ℂ⁆ L) (hcol : HasColor E F H b a) :
      HasColor (e e6Cartan) (f e6Cartan) (h e6Cartan) b (model a) := by
    intro i
    refine ⟨?_, ?_, ?_⟩
    · change p.symm (a (p (e e6Cartan i))) = _
      rw [pe, (hcol i).1, ← pe, map_smul, p.symm_apply_apply]
    · change p.symm (a (p (f e6Cartan i))) = _
      rw [pf, (hcol i).2.1, ← pf, map_smul, p.symm_apply_apply]
    · change p.symm (a (p (h e6Cartan i))) = _
      rw [ph, (hcol i).2.2, ← ph, p.symm_apply_apply]
  have hamb : Module.finrank ℂ L = 78 := p.toLinearEquiv.finrank_eq.symm.trans e6ModelRank
  have hclassified (b : Coloring) (a : L ≃ₗ⁅ℂ⁆ L) (hcolA : HasColor E F H b a)
      (ha : Intertwines ω ω a) (hia : Function.Involutive a) :
      if b = 0 then
        Nonempty (Algebra f4Cartan ≃ₗ⁅ℂ⁆ complexFixed a) ∧
          Module.finrank ℂ (complexFixed a) = 52 ∧
          killingSignature (involutionConjugation ω a ha hia).fixed = -26
      else
        Nonempty (Algebra c4Cartan ≃ₗ⁅ℂ⁆ complexFixed a) ∧
          Module.finrank ℂ (complexFixed a) = 36 ∧
          killingSignature (involutionConjugation ω a ha hia).fixed = 6 := by
    have hsig := _root_.LieAlgebrasAndRepresentations.CartanDecompositionSignature.killing_signature
      ω a ha hia hc
    change killingSignature (involutionConjugation ω a ha hia).fixed =
      (Module.finrank ℂ L : ℤ) - 2 * (Module.finrank ℂ (complexFixed a) : ℤ) at hsig
    let ep := fixedEquiv p (model a) a (hmodel a)
    by_cases hb : b = 0
    · rw [if_pos hb]
      have heq : model a = aW := normalized_unique 0 (hb ▸ hcol b a hcolA) hW
      have ep' : complexFixed aW ≃ₗ⁅ℂ⁆ complexFixed a := heq ▸ ep
      have hdim := ep'.toLinearEquiv.finrank_eq.symm.trans hWhite.2
      exact ⟨hWhite.1.map (fun e => e.trans ep'), hdim, by rw [hsig, hamb, hdim]; norm_num⟩
    · rw [if_neg hb]
      obtain ⟨g, _, hg⟩ := conjugates_to_black ω₀ hω₀ aB aBoth hB hBoth b hb (model a)
        (hcol b a hcolA)
      let eg := fixedEquiv g (model a) aB hg
      let e := eg.symm.trans ep
      have hdim := e.toLinearEquiv.finrank_eq.symm.trans hBlack.2
      exact ⟨hBlack.1.map (fun f => f.trans e), hdim, by rw [hsig, hamb, hdim]; norm_num⟩
  refine ⟨?_, hclassified⟩
  intro b c a a' hca hca' ha hia ha' hia'
  constructor
  · rintro ⟨e⟩
    have hs := killingSignature_equiv e
    have hb := hclassified b a hca ha hia
    have hc' := hclassified c a' hca' ha' hia'
    by_cases h₁ : b = 0 <;> by_cases h₂ : c = 0 <;> simp [h₁, h₂] at hb hc' ⊢
    · rw [hb.2.2, hc'.2.2] at hs
      norm_num at hs
    · rw [hb.2.2, hc'.2.2] at hs
      norm_num at hs
  · intro he
    have hconj : CompactConjugate ω₀ (model a) (model a') := by
      by_cases hb : b = 0
      · have h := normalized_unique 0 (hb ▸ hcol b a hca) (he.mp hb ▸ hcol c a' hca')
        rw [h]
        exact CompactConjugate.refl ω₀ _
      · have hc' : c ≠ 0 := fun h => hb (he.mpr h)
        exact (conjugates_to_black ω₀ hω₀ aB aBoth hB hBoth b hb (model a)
          (hcol b a hca)).trans (conjugates_to_black ω₀ hω₀ aB aBoth hB hBoth c hc' (model a')
          (hcol c a' hca')).symm
    obtain ⟨g, hwg, hg⟩ := hconj
    let g' := (p.symm.trans g).trans p
    have hgw (x : L) : ω.map (g' x) = g' (ω.map x) := by
      change ω.map (p (g (p.symm x))) = p (g (p.symm (ω.map x)))
      have h := hwg (p.symm x)
      change p.symm (ω.map (p (g (p.symm x)))) =
        g (p.symm (ω.map (p (p.symm x)))) at h
      rw [p.apply_symm_apply] at h
      have h' := congrArg p h
      simpa only [p.apply_symm_apply] using h'
    have hga (x : L) : a' (g' x) = g' (a x) := by
      change a' (p (g (p.symm x))) = p (g (p.symm (a x)))
      have h := hg (p.symm x)
      change p.symm (a' (p (g (p.symm x)))) = g (p.symm (a (p (p.symm x)))) at h
      rw [p.apply_symm_apply] at h
      have h' := congrArg p h
      simpa only [p.apply_symm_apply] using h'
    have hInter : Intertwines (involutionConjugation ω a ha hia)
        (involutionConjugation ω a' ha' hia') g' := by
      intro x
      change a' (ω.map (g' x)) = g' (a (ω.map x))
      rw [hgw, hga]
    obtain ⟨e, _⟩ := restrict_complex_isomorphism _ _ g' hInter
    exact ⟨e⟩

end

end LieAlgebrasAndRepresentations.ExceptionalOuterInvolutions
