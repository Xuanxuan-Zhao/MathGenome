import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.UnitaryRankOne
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.RootGroups
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
/-! Rank-one matrix words for split and quadratic unitary groups. -/

universe u v

namespace LinearAlgebraicGroups.Arithmetic.UnitaryRankOne

open Matrix
open Specs.UnitaryRankOne

private theorem upper_det {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (Q a b : E) : (upper σ Q a b).det = 1 := by
  simp [upper, Matrix.det_fin_three]

private theorem lower_det {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (Q a b : E) : (lower σ Q a b).det = 1 := by
  simp [lower, Matrix.det_fin_three]

private theorem weyl_det (E : Type v) [Field E] : (unitaryWeyl E).det = 1 := by
  simp [unitaryWeyl, Matrix.det_fin_three]

private theorem upper_eq_transvection {R : Type u} [CommRing R] (a : R) :
    (splitUpper a).val = !![1, a; 0, 1] := by
  change Matrix.transvection 0 1 a = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.add_apply]

private theorem lower_eq_transvection {R : Type u} [CommRing R] (a : R) :
    (splitLower a).val = !![1, 0; a, 1] := by
  change Matrix.transvection 1 0 a = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.add_apply]

private theorem split_word_matrix {R : Type u} [CommRing R] (t : Rˣ) :
    (splitWord t).val = !![0, (t : R); -(↑t⁻¹ : R), 0] := by
  change ((splitUpper (t : R)).val * (splitLower (-(↑t⁻¹ : R))).val *
    (splitUpper (t : R)).val) = _
  rw [upper_eq_transvection, lower_eq_transvection]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem splitRankOneWords_conditional
    (_ : Specs.RootGroups.RankOneRootGroups.{u})
    (_ : Specs.RootGroups.RootDimension.{u})
    (_ : Specs.RootGroups.RootSubgroups.{u}) : SplitRankOneWords.{u} := by
  refine ⟨?_, ?_⟩
  · intro R _ t
    refine ⟨split_word_matrix t, ?_⟩
    change (splitWord t).val * (splitWord (-1 : Rˣ)).val = _
    rw [split_word_matrix, split_word_matrix, Matrix.diagonal_vec2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · intro ι R _ t
    dsimp only
    let H := Subgroup.closure
      (Set.range (fun a : ∀ i, R i => fun i => splitUpper (a i)) ∪
       Set.range (fun a : ∀ i, R i => fun i => splitLower (a i)))
    have hu (a : ∀ i, R i) : (fun i => splitUpper (a i)) ∈ H :=
      Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)
    have hl (a : ∀ i, R i) : (fun i => splitLower (a i)) ∈ H :=
      Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)
    have hw (r : ∀ i, (R i)ˣ) : (fun i => splitWord (r i)) ∈ H :=
      H.mul_mem (H.mul_mem (hu (fun i => r i)) (hl (fun i => -(↑(r i)⁻¹ : R i))))
        (hu (fun i => r i))
    exact ⟨hw (fun _ => 1), H.mul_mem (hw t) (hw (fun _ => -1))⟩

section Quadratic

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
variable [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]

local notation "bar" => quadraticConjugation F E

private theorem quadraticAut (τ : E ≃ₐ[F] E) : τ = 1 ∨ τ = bar := by
  have hdim := Algebra.IsQuadraticExtension.finrank_eq_two F E
  let : FiniteDimensional F E := .of_finrank_pos (hdim ▸ Nat.zero_lt_succ 1)
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 :=
    (IsGalois.card_aut_eq_finrank F E).trans hdim
  obtain ⟨τ', _, hall⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).mp hcard
  by_cases h : τ = 1
  · exact Or.inl h
  · exact Or.inr ((hall τ h).trans (hall bar (quadraticConjugation_ne_one F E)).symm)

@[local simp] private theorem conj_conj (x : E) : bar (bar x) = x := by
  have h : bar * bar = 1 := by
    rcases quadraticAut (bar * bar) with h | h
    · exact h
    · exact (quadraticConjugation_ne_one F E
        (mul_left_cancel (h.trans (mul_one bar).symm))).elim
  exact DFunLike.congr_fun h x

private theorem conj_eq_iff (x : E) : bar x = x ↔ x ∈ Set.range (algebraMap F E) := by
  have hdim := Algebra.IsQuadraticExtension.finrank_eq_two F E
  let : FiniteDimensional F E := .of_finrank_pos (hdim ▸ Nat.zero_lt_succ 1)
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  constructor
  · intro hx τ
    rcases quadraticAut τ with rfl | rfl
    · rfl
    · exact hx
  · intro h
    exact h bar

private theorem trace_eq (x : E) : algebraMap F E (Algebra.trace F E x) = x + bar x := by
  classical
  have hdim := Algebra.IsQuadraticExtension.finrank_eq_two F E
  let : FiniteDimensional F E := .of_finrank_pos (hdim ▸ Nat.zero_lt_succ 1)
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, bar} := by
    ext τ
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact quadraticAut τ
  rw [trace_eq_sum_automorphisms, huniv,
    Finset.sum_pair (Ne.symm (quadraticConjugation_ne_one F E))]
  rfl

private theorem exists_trace_zero_unit : ∃ b : Eˣ, (b : E) + bar (b : E) = 0 := by
  have h : ∃ z : E, bar z ≠ z := by
    by_contra! h
    exact quadraticConjugation_ne_one F E (AlgEquiv.ext h)
  obtain ⟨z, hz⟩ := h
  refine ⟨Units.mk0 (z - bar z) (sub_ne_zero.mpr hz.symm), ?_⟩
  change (z - bar z) + bar (z - bar z) = 0
  rw [map_sub, conj_conj]
  ring

theorem admissibleRatios_conditional
    (_ : Specs.RootGroups.RankOneRootGroups.{u})
    (_ : Specs.RootGroups.RootDimension.{u})
    (_ : Specs.RootGroups.RootSubgroups.{u}) : AdmissibleRatios.{u, v} := by
  intro F E _ _ _ _ _ _ q s
  dsimp only
  let σ := quadraticConjugation F E
  set Q := algebraMap F E (q : F)
  have hQ : Q ≠ 0 := (map_ne_zero (algebraMap F E)).mpr q.ne_zero
  have moveTrace {x : E} {c : F} (h : x + σ x = algebraMap F E c) :
      Algebra.trace F E x = c :=
    (algebraMap F E).injective ((trace_eq x).trans h)
  by_cases hs : (s : E) ∈ Set.range (algebraMap F E)
  · obtain ⟨b, hb⟩ := exists_trace_zero_unit (F := F) (E := E)
    have hs' := (conj_eq_iff (s : E)).mpr hs
    have hsb : (s : E) * b + σ ((s : E) * b) = 0 := by
      rw [map_mul, hs', ← mul_add, hb, mul_zero]
    refine ⟨b, 0, ?_, ?_, ?_, fun h => (h hs).elim⟩
    · simpa [Admissible] using hb
    · simpa [Admissible] using hsb
    · exact fun _ => ⟨rfl, moveTrace (by simpa using hb), moveTrace (by simpa using hsb)⟩
  · -- Solve for the two traces without dividing by two.
    let c : E := -(Q⁻¹)
    have hc : σ c = c := by
      change σ (-(Q⁻¹)) = -(Q⁻¹)
      simp [Q]
    have hss : (s : E) - σ (s : E) ≠ 0 :=
      sub_ne_zero.mpr (fun h => hs ((conj_eq_iff (s : E)).mp h.symm))
    have hs1 : 1 - σ (s : E) ≠ 0 := by
      intro h
      have h' : σ (s : E) = 1 := (sub_eq_zero.mp h).symm
      have h'' : (s : E) = 1 := σ.injective (by simpa using h')
      exact hs ⟨1, by simp [h'']⟩
    let b : E := c * (1 - σ (s : E)) / ((s : E) - σ (s : E))
    have hb₀ : b ≠ 0 := div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hQ)) hs1) hss
    have hσ : σ b = c * (1 - (s : E)) / (σ (s : E) - (s : E)) := by
      have hconj : σ (σ (s : E)) = s := conj_conj (s : E)
      simp [b, hc, hconj]
    have hss' : σ (s : E) - (s : E) ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hss).symm
    have hb : b + σ b = c := by
      rw [hσ]
      dsimp only [b]
      field_simp [hss, hss']
      ring
    have hsb : (s : E) * b + σ ((s : E) * b) = c := by
      rw [map_mul, hσ]
      dsimp only [b]
      field_simp [hss, hss']
      ring
    have hcm : c = algebraMap F E (-(q : F)⁻¹) := by simp [c, Q]
    have ha : -(1 * σ 1) / Q = c := by simp [c, div_eq_mul_inv]
    refine ⟨Units.mk0 b hb₀, 1, ?_, ?_, fun h => (hs h).elim, ?_⟩
    · exact hb.trans ha.symm
    · exact hsb.trans ha.symm
    · exact fun _ => ⟨rfl, moveTrace (hb.trans hcm), moveTrace (hsb.trans hcm)⟩

private theorem upper_preserves_iff (q : Fˣ) (a b c : E) :
    let Q := algebraMap F E (q : F)
    PreservesForm bar Q !![1, a, b; 0, 1, c; 0, 0, 1] ↔
      c = -(bar a) / Q ∧ Admissible bar Q a b := by
  dsimp only [PreservesForm, Admissible]
  set Q := algebraMap F E (q : F)
  have hQ : Q ≠ 0 := (map_ne_zero (algebraMap F E)).mpr q.ne_zero
  have hbarQ : bar Q = Q := AlgEquiv.commutes _ _
  constructor
  · intro h
    have hp := congrArg (fun A : Matrix (Fin 3) (Fin 3) E => A 1 2) h
    have ht := congrArg (fun A : Matrix (Fin 3) (Fin 3) E => A 2 2) h
    change _ = hermitianMatrix Q 1 2 at hp
    change _ = hermitianMatrix Q 2 2 at ht
    simp [Matrix.mul_apply, Fin.sum_univ_three, hermitianMatrix] at hp ht
    have hc : c = -(bar a) / Q := (eq_div_iff hQ).mpr (by linear_combination hp)
    refine ⟨hc, ?_⟩
    rw [hc, map_div₀, map_neg, conj_conj, hbarQ] at ht
    field_simp [hQ] at ht ⊢
    linear_combination ht
  · rintro ⟨rfl, hb⟩
    have htrace := (eq_div_iff hQ).mp hb
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, hermitianMatrix, map_div₀, hbarQ] <;>
      field_simp [hQ] <;> first | (ring; done) | linear_combination htrace

private theorem lower_preserves_iff (q : Fˣ) (a b c : E) :
    let Q := algebraMap F E (q : F)
    PreservesForm bar Q !![1, 0, 0; c, 1, 0; b, -a, 1] ↔
      c = bar a / Q ∧ Admissible bar Q a b := by
  dsimp only [PreservesForm, Admissible]
  set Q := algebraMap F E (q : F)
  have hQ : Q ≠ 0 := (map_ne_zero (algebraMap F E)).mpr q.ne_zero
  have hbarQ : bar Q = Q := AlgEquiv.commutes _ _
  constructor
  · intro h
    have hp := congrArg (fun A : Matrix (Fin 3) (Fin 3) E => A 1 0) h
    have ht := congrArg (fun A : Matrix (Fin 3) (Fin 3) E => A 0 0) h
    change _ = hermitianMatrix Q 1 0 at hp
    change _ = hermitianMatrix Q 0 0 at ht
    simp [Matrix.mul_apply, Fin.sum_univ_three, hermitianMatrix] at hp ht
    have hc : c = bar a / Q := (eq_div_iff hQ).mpr (by linear_combination hp)
    refine ⟨hc, ?_⟩
    rw [hc, map_div₀, conj_conj, hbarQ] at ht
    field_simp [hQ] at ht ⊢
    linear_combination ht
  · rintro ⟨rfl, hb⟩
    have htrace := (eq_div_iff hQ).mp hb
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, hermitianMatrix, map_div₀, hbarQ] <;>
      field_simp [hQ] <;> first | (ring; done) | linear_combination htrace

private theorem weyl_sq : unitaryWeyl E * unitaryWeyl E = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitaryWeyl, Matrix.mul_apply, Fin.sum_univ_three]

theorem admissibleCoordinates_conditional
    (_ : Specs.RootGroups.RankOneRootGroups.{u})
    (_ : Specs.RootGroups.RootDimension.{u})
    (_ : Specs.RootGroups.RootSubgroups.{u}) : AdmissibleCoordinates.{u, v} := by
  intro F E _ _ _ _ _ _ q
  dsimp only
  refine ⟨upper_preserves_iff q, lower_preserves_iff q, ?_, weyl_det E, ?_, weyl_sq⟩
  · intro a b
    refine ⟨upper_det _ _ _ _, lower_det _ _ _ _, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unitaryWeyl, upper, lower, Matrix.mul_apply, Fin.sum_univ_three, neg_div]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unitaryWeyl, hermitianMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem threeFactorInterchange_conditional
    (_ : Specs.RootGroups.RankOneRootGroups.{u})
    (_ : Specs.RootGroups.RootDimension.{u})
    (_ : Specs.RootGroups.RootSubgroups.{u}) : ThreeFactorInterchange.{u, v} := by
  intro F E _ _ _ _ _ _ q a b
  dsimp only
  let σ := quadraticConjugation F E
  intro hab hb
  set Q := algebraMap F E (q : F)
  have hQ : Q ≠ 0 := (map_ne_zero (algebraMap F E)).mpr q.ne_zero
  have hσb : σ b ≠ 0 := (map_ne_zero σ).mpr hb
  have htrace : (b + σ b) * Q = -(a * σ a) := (eq_div_iff hQ).mp hab
  have hconj : σ (σ b) = b := conj_conj b
  have hleft : Admissible σ Q (a / σ b) (σ b)⁻¹ := by
    simp only [Admissible, map_inv₀, map_div₀, hconj]
    field_simp [hb, hσb, hQ]
    linear_combination htrace
  have hright : Admissible σ Q (a / b) (σ b)⁻¹ := by
    simp only [Admissible, map_inv₀, map_div₀, hconj]
    field_simp [hb, hσb, hQ]
    linear_combination htrace
  refine ⟨hleft, hright, ?_⟩
  -- Multiplying on the right first leaves only the top-right entry in the first row.
  have hup : upper σ Q a b * lower σ Q (a / b) (σ b)⁻¹ =
      !![0, 0, b; 0, -(σ b / b), -(σ a) / Q; (σ b)⁻¹, -(a / b), 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upper, lower, Matrix.mul_apply, Fin.sum_univ_three] <;>
      (try field_simp [hQ, hb, hσb]) <;> first | (ring; done) | linear_combination htrace
  rw [mul_assoc, hup, unitaryDiagonal, Matrix.diagonal_vec3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lower, unitaryWeyl, Matrix.mul_apply, Fin.sum_univ_three] <;>
    (try field_simp [hQ, hb, hσb]) <;> first | (ring; done) | linear_combination htrace

private theorem diagonal_det (s : E) (hs : s ≠ 0) : (unitaryDiagonal bar s).det = 1 := by
  have hbars : bar s ≠ 0 := (map_ne_zero bar).mpr hs
  simp [unitaryDiagonal, Matrix.det_diagonal, Fin.prod_univ_three]
  field_simp [hs, hbars]

private theorem diagonal_preserves (q : Fˣ) (s : E) (hs : s ≠ 0) :
    PreservesForm bar (algebraMap F E (q : F)) (unitaryDiagonal bar s) := by
  have hbars : bar s ≠ 0 := (map_ne_zero bar).mpr hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitaryDiagonal, hermitianMatrix, Matrix.diagonal_vec3,
      Matrix.mul_apply, Fin.sum_univ_three, map_div₀] <;> field_simp [hs, hbars]

private theorem diagonal_classification (q : Fˣ) (d : Fin 3 → E) :
    ((Matrix.diagonal d).det = 1 ∧
      PreservesForm bar (algebraMap F E (q : F)) (Matrix.diagonal d)) ↔
      ∃ s : Eˣ, Matrix.diagonal d = unitaryDiagonal bar (s : E) := by
  constructor
  · rintro ⟨hd, hp⟩
    have h02 := congrArg (fun A : Matrix (Fin 3) (Fin 3) E => A 0 2) hp
    change (((Matrix.diagonal d).map bar).transpose *
      hermitianMatrix (algebraMap F E (q : F)) * Matrix.diagonal d) 0 2 = _ at h02
    have h02' : bar (d 0) * d 2 = 1 := by
      simpa [Matrix.diagonal_fin_three, hermitianMatrix, Matrix.mul_apply, Fin.sum_univ_three]
        using h02
    have hs : d 0 ≠ 0 := by
      intro h
      simp [h] at h02'
    have h₂ : d 2 = (bar (d 0))⁻¹ := (inv_eq_of_mul_eq_one_right h02').symm
    have h₁ : d 1 = bar (d 0) / d 0 := by
      apply (eq_div_iff hs).mpr
      simp only [Matrix.det_diagonal, Fin.prod_univ_three, h₂] at hd
      have hh := congrArg (fun x : E => x * bar (d 0)) hd
      have hbars : bar (d 0) ≠ 0 := (map_ne_zero bar).mpr hs
      simpa [mul_assoc, inv_mul_cancel₀ hbars, mul_comm (d 1) (d 0)] using hh
    refine ⟨Units.mk0 (d 0) hs, ?_⟩
    rw [unitaryDiagonal, Matrix.diagonal_vec3, Matrix.diagonal_fin_three, h₁, h₂]
    rfl
  · rintro ⟨s, hs⟩
    rw [hs]
    exact ⟨diagonal_det (F := F) (s : E) s.ne_zero, diagonal_preserves q (s : E) s.ne_zero⟩

private theorem diagonal_mul (s b : E) :
    unitaryDiagonal bar s * unitaryDiagonal bar b = unitaryDiagonal bar (s * b) := by
  rw [unitaryDiagonal, unitaryDiagonal, unitaryDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [map_mul, mul_div_mul_comm, mul_comm]

private theorem weyl_conj_diagonal (s : E) (hs : s ≠ 0) :
    unitaryWeyl E * unitaryDiagonal bar s * unitaryWeyl E = unitaryDiagonal bar ((bar s)⁻¹) := by
  have hbars : bar s ≠ 0 := (map_ne_zero bar).mpr hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitaryDiagonal, unitaryWeyl, Matrix.diagonal_vec3,
      Matrix.mul_apply, Fin.sum_univ_three]
  field_simp [hs, hbars]

private theorem norm_one_ratio (η : E) (hη : η * bar η = 1) :
    ∃ s : Eˣ, bar (s : E) / (s : E) = η := by
  by_cases h : η = -1
  · obtain ⟨s, hs⟩ := exists_trace_zero_unit (F := F) (E := E)
    refine ⟨s, (div_eq_iff s.ne_zero).mpr ?_⟩
    rw [h]
    linear_combination hs
  · let s : E := 1 + bar η
    have hs : s ≠ 0 := by
      intro hs
      apply h
      apply (quadraticConjugation F E).injective
      rw [map_neg, map_one]
      change 1 + bar η = 0 at hs
      linear_combination hs
    refine ⟨Units.mk0 s hs, (div_eq_iff hs).mpr ?_⟩
    change bar s = η * s
    simp only [s, map_add, map_one, conj_conj]
    linear_combination -hη

theorem unitaryTorusAndWeylWords_conditional
    (rankOne : Specs.RootGroups.RankOneRootGroups.{u})
    (dim : Specs.RootGroups.RootDimension.{u})
    (roots : Specs.RootGroups.RootSubgroups.{u}) : UnitaryTorusAndWeylWords.{u, v} := by
  intro F E _ _ _ _ _ _ q
  dsimp only
  let σ := quadraticConjugation F E
  let Q := algebraMap F E (q : F)
  let H := Subgroup.closure (unitaryRadicalGenerators σ Q)
  have word (a b : E) (hab : Admissible σ Q a b) (hb : b ≠ 0) :
      RepresentedIn (unitaryDiagonal σ b * unitaryWeyl E) H := by
    obtain ⟨hleft, hright, hprod⟩ :=
      threeFactorInterchange_conditional rankOne dim roots q a b hab hb
    let left : SpecialLinearGroup (Fin 3) E :=
      ⟨lower σ Q (a / σ b) (σ b)⁻¹, lower_det _ _ _ _⟩
    let middle : SpecialLinearGroup (Fin 3) E := ⟨upper σ Q a b, upper_det _ _ _ _⟩
    let right : SpecialLinearGroup (Fin 3) E :=
      ⟨lower σ Q (a / b) (σ b)⁻¹, lower_det _ _ _ _⟩
    have hl : left ∈ H := Subgroup.subset_closure ⟨_, _, hleft, Or.inr rfl⟩
    have hm : middle ∈ H := Subgroup.subset_closure ⟨_, _, hab, Or.inl rfl⟩
    have hr : right ∈ H := Subgroup.subset_closure ⟨_, _, hright, Or.inr rfl⟩
    exact ⟨left * middle * right, H.mul_mem (H.mul_mem hl hm) hr, hprod⟩
  have hdiag (s : Eˣ) : RepresentedIn (unitaryDiagonal σ (s : E)) H := by
    obtain ⟨b, a, hab, hsb, _, _⟩ := admissibleRatios_conditional rankOne dim roots q s
    obtain ⟨g, hg, hgv⟩ := word a b hab b.ne_zero
    obtain ⟨g', hg', hgv'⟩ := word a ((s : E) * b) hsb (mul_ne_zero s.ne_zero b.ne_zero)
    let d : SpecialLinearGroup (Fin 3) E :=
      ⟨unitaryDiagonal σ s, diagonal_det (F := F) (s : E) s.ne_zero⟩
    have hmul : d * g = g' := by
      apply Subtype.ext
      change unitaryDiagonal σ (s : E) * g.val = g'.val
      rw [hgv, hgv', ← mul_assoc, diagonal_mul]
    refine ⟨d, ?_, rfl⟩
    -- The common Weyl factor cancels in the quotient of the two words.
    have hd : d = g' * g⁻¹ := by rw [← hmul, mul_inv_cancel_right]
    rw [hd]
    exact H.mul_mem hg' (H.inv_mem hg)
  have hw : RepresentedIn (unitaryWeyl E) H := by
    obtain ⟨b, a, hab, _, _, _⟩ := admissibleRatios_conditional rankOne dim roots q (1 : Eˣ)
    obtain ⟨g, hg, hgv⟩ := word a b hab b.ne_zero
    obtain ⟨d, hd, hdv⟩ := hdiag b
    let w : SpecialLinearGroup (Fin 3) E := ⟨unitaryWeyl E, weyl_det E⟩
    have hmul : d * w = g := by
      apply Subtype.ext
      change d.val * unitaryWeyl E = g.val
      rw [hdv, hgv]
    refine ⟨w, ?_, rfl⟩
    have hw : w = d⁻¹ * g := by rw [← hmul, inv_mul_cancel_left]
    rw [hw]
    exact H.mul_mem (H.inv_mem hd) hg
  exact ⟨diagonal_classification q, fun s => ⟨hdiag s, weyl_conj_diagonal (s : E) s.ne_zero⟩,
    hw, norm_one_ratio⟩

end Quadratic

end LinearAlgebraicGroups.Arithmetic.UnitaryRankOne

universe v8_closure_0fbecb0658e55ee0_u0 v8_closure_0fbecb0658e55ee0_u1
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«UnitaryRankOne».«admissibleCoordinates» : _root_.«LinearAlgebraicGroups».«Specs».«UnitaryRankOne».«AdmissibleCoordinates».{v8_closure_0fbecb0658e55ee0_u0, v8_closure_0fbecb0658e55ee0_u1} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«UnitaryRankOne».«admissibleCoordinates_conditional».{v8_closure_0fbecb0658e55ee0_u0, v8_closure_0fbecb0658e55ee0_u1} (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rankOneRootGroups».{v8_closure_0fbecb0658e55ee0_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rootDimension».{v8_closure_0fbecb0658e55ee0_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rootSubgroups».{v8_closure_0fbecb0658e55ee0_u0})
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«UnitaryRankOne».«admissibleRatios» : _root_.«LinearAlgebraicGroups».«Specs».«UnitaryRankOne».«AdmissibleRatios».{v8_closure_0fbecb0658e55ee0_u0, v8_closure_0fbecb0658e55ee0_u1} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«UnitaryRankOne».«admissibleRatios_conditional».{v8_closure_0fbecb0658e55ee0_u0, v8_closure_0fbecb0658e55ee0_u1} (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rankOneRootGroups».{v8_closure_0fbecb0658e55ee0_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rootDimension».{v8_closure_0fbecb0658e55ee0_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rootSubgroups».{v8_closure_0fbecb0658e55ee0_u0})
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«UnitaryRankOne».«splitRankOneWords» : _root_.«LinearAlgebraicGroups».«Specs».«UnitaryRankOne».«SplitRankOneWords».{v8_closure_0fbecb0658e55ee0_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«UnitaryRankOne».«splitRankOneWords_conditional».{v8_closure_0fbecb0658e55ee0_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rankOneRootGroups».{v8_closure_0fbecb0658e55ee0_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rootDimension».{v8_closure_0fbecb0658e55ee0_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rootSubgroups».{v8_closure_0fbecb0658e55ee0_u0})
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«UnitaryRankOne».«threeFactorInterchange» : _root_.«LinearAlgebraicGroups».«Specs».«UnitaryRankOne».«ThreeFactorInterchange».{v8_closure_0fbecb0658e55ee0_u0, v8_closure_0fbecb0658e55ee0_u1} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«UnitaryRankOne».«threeFactorInterchange_conditional».{v8_closure_0fbecb0658e55ee0_u0, v8_closure_0fbecb0658e55ee0_u1} (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rankOneRootGroups».{v8_closure_0fbecb0658e55ee0_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rootDimension».{v8_closure_0fbecb0658e55ee0_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rootSubgroups».{v8_closure_0fbecb0658e55ee0_u0})
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«UnitaryRankOne».«unitaryTorusAndWeylWords» : _root_.«LinearAlgebraicGroups».«Specs».«UnitaryRankOne».«UnitaryTorusAndWeylWords».{v8_closure_0fbecb0658e55ee0_u0, v8_closure_0fbecb0658e55ee0_u1} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«UnitaryRankOne».«unitaryTorusAndWeylWords_conditional».{v8_closure_0fbecb0658e55ee0_u0, v8_closure_0fbecb0658e55ee0_u1} (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rankOneRootGroups».{v8_closure_0fbecb0658e55ee0_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rootDimension».{v8_closure_0fbecb0658e55ee0_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rootSubgroups».{v8_closure_0fbecb0658e55ee0_u0})
