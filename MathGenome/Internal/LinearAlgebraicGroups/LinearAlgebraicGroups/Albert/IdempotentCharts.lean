import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.IdempotentCharts
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.QuadraticOperators
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.ShortDirections
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.PeirceFrames
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

namespace LinearAlgebraicGroups.Albert.IdempotentCharts

open _root_.LinearAlgebraicGroups.Composition (Zorn)
open Composition.ZornSpecification (norm)
open Composition.AdjointSpecification (conjugate NormLaws)
open HermitianSpecification (cyclicNext cyclicPrev)
open CubicSpecification (cubicAdjoint linearTrace cubicUnit diagonalCoordinates singleBlockCoordinates)
open FrameSpecification (frameAxis)
open TrialitySpecification (Model modelOp)
open IdempotentSpecification
open scoped BigOperators

universe u v w

section Points

variable {R : Type u} [CommRing R]

private lemma next_prev (i : Fin 3) : cyclicNext (cyclicPrev i) = i := by
  fin_cases i <;> decide

private lemma prev_next (i : Fin 3) : cyclicPrev (cyclicNext i) = i := by
  fin_cases i <;> decide

private lemma next_next (i : Fin 3) : cyclicNext (cyclicNext i) = cyclicPrev i := by
  fin_cases i <;> decide

private lemma prev_prev (i : Fin 3) : cyclicPrev (cyclicPrev i) = cyclicNext i := by
  fin_cases i <;> decide

private lemma next_ne (i : Fin 3) : cyclicNext i ≠ i := by
  fin_cases i <;> decide

private lemma prev_ne (i : Fin 3) : cyclicPrev i ≠ i := by
  fin_cases i <;> decide

private lemma prev_ne_next (i : Fin 3) : cyclicPrev i ≠ cyclicNext i := by
  fin_cases i <;> decide

private lemma cyclic_cases (i s : Fin 3) :
    s = i ∨ s = cyclicNext i ∨ s = cyclicPrev i := by
  fin_cases i <;> fin_cases s <;> decide

private lemma trace_cyclic (x : Model R) (i : Fin 3) :
    trace x = x.1 i + x.1 (cyclicNext i) + x.1 (cyclicPrev i) := by
  rw [IdempotentSpecification.trace, Albert.linearTrace_apply, Fin.sum_univ_three]
  fin_cases i
  · change x.1 0 + x.1 1 + x.1 2 = x.1 0 + x.1 1 + x.1 2
    rfl
  · change x.1 0 + x.1 1 + x.1 2 = x.1 1 + x.1 2 + x.1 0
    ring
  · change x.1 0 + x.1 1 + x.1 2 = x.1 2 + x.1 0 + x.1 1
    ring

private lemma adjoint_diag (x : Model R) (i : Fin 3) :
    (adjoint x).1 i =
      x.1 (cyclicNext i) * x.1 (cyclicPrev i) - norm R (x.2 i) := by
  simp [adjoint, CubicSpecification.cubicAdjoint, CubicSpecification.blockWeight]

private lemma adjoint_block (x : Model R) (i : Fin 3) :
    (adjoint x).2 i = -(x.1 i) • x.2 i +
      conjugate (norm R) (x.2 (cyclicNext i) * x.2 (cyclicPrev i)) := by
  simp [adjoint, CubicSpecification.cubicAdjoint]

private lemma chart_diag_here (i : Fin 3) (a : Rˣ) (c d : Zorn R) :
    (chartCoordinates i a c d).1 i = a := by simp [chartCoordinates]

private lemma chart_diag_next (i : Fin 3) (a : Rˣ) (c d : Zorn R) :
    (chartCoordinates i a c d).1 (cyclicNext i) = (↑a⁻¹ : R) * norm R d := by
  simp [chartCoordinates, next_ne]

private lemma chart_diag_prev (i : Fin 3) (a : Rˣ) (c d : Zorn R) :
    (chartCoordinates i a c d).1 (cyclicPrev i) = (↑a⁻¹ : R) * norm R c := by
  simp [chartCoordinates, prev_ne, prev_ne_next]

private lemma chart_block_here (i : Fin 3) (a : Rˣ) (c d : Zorn R) :
    (chartCoordinates i a c d).2 i = (↑a⁻¹ : R) • conjugate (norm R) (c * d) := by
  simp [chartCoordinates]

private lemma chart_block_next (i : Fin 3) (a : Rˣ) (c d : Zorn R) :
    (chartCoordinates i a c d).2 (cyclicNext i) = c := by
  simp [chartCoordinates, next_ne]

private lemma chart_block_prev (i : Fin 3) (a : Rˣ) (c d : Zorn R) :
    (chartCoordinates i a c d).2 (cyclicPrev i) = d := by
  simp [chartCoordinates, prev_ne, prev_ne_next]

private lemma zornNormLaws : NormLaws (norm R) :=
  (Zorn.isOctonion R).toNormLaws

private lemma chart_adjoint_zero (i : Fin 3) (a : Rˣ) (c d : Zorn R) :
    adjoint (chartCoordinates i a c d) = 0 := by
  have h₁ : conjugate (norm R) (d * conjugate (norm R) (c * d)) = norm R d • c := by
    rw [Composition.conjugate_mul zornNormLaws,
      Composition.conjugate_involutive zornNormLaws (c * d)]
    exact (Composition.conjugate_right_products zornNormLaws d c).1
  have h₂ : conjugate (norm R) (conjugate (norm R) (c * d) * c) = norm R c • d := by
    rw [Composition.conjugate_mul zornNormLaws,
      Composition.conjugate_involutive zornNormLaws (c * d)]
    exact (Composition.conjugate_left_products zornNormLaws c d).1
  apply Prod.ext
  · funext s
    rcases cyclic_cases i s with rfl | rfl | rfl <;>
      simp only [adjoint_diag, next_next, prev_next, next_prev, prev_prev,
        chart_diag_here, chart_diag_next, chart_diag_prev, chart_block_here,
        chart_block_next, chart_block_prev, Prod.fst_zero, Pi.zero_apply,
        QuadraticMap.map_smul, smul_eq_mul, Composition.norm_conjugate zornNormLaws,
        Zorn.norm_mul, sub_eq_zero]
    · ring
    · rw [mul_comm (↑a⁻¹ : R) (norm R c), mul_assoc, Units.inv_mul, mul_one]
    · rw [← mul_assoc, Units.mul_inv, one_mul]
  · funext s
    rcases cyclic_cases i s with rfl | rfl | rfl <;>
      simp only [adjoint_block, next_next, prev_next, next_prev, prev_prev,
        chart_diag_here, chart_diag_next, chart_diag_prev, chart_block_here,
        chart_block_next, chart_block_prev, Prod.snd_zero, Pi.zero_apply]
    · rw [smul_smul, neg_mul, Units.mul_inv, neg_smul, one_smul, neg_add_cancel]
    · rw [mul_smul_comm, map_smul, h₁, smul_smul, neg_smul, neg_add_cancel]
    · rw [smul_mul_assoc, map_smul, h₂, smul_smul, neg_smul, neg_add_cancel]

private lemma chart_trace_iff (i : Fin 3) (a : Rˣ) (c d : Zorn R) :
    trace (chartCoordinates i a c d) = 1 ↔
      (a : R) ^ 2 - (a : R) + norm R c + norm R d = 0 := by
  rw [trace_cyclic _ i, chart_diag_here, chart_diag_next, chart_diag_prev,
    ← (Units.mul_right_inj a : (↑a : R) * _ = ↑a * _ ↔ _ = _), mul_one,
    mul_add, mul_add, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, one_mul]
  constructor <;> intro h <;> linear_combination h

private lemma reconstruct_of_adjoint {i : Fin 3} {a : Rˣ} {x : Model R}
    (ha : x.1 i = a) (hx : adjoint x = 0) :
    x = chartCoordinates i a (x.2 (cyclicNext i)) (x.2 (cyclicPrev i)) := by
  have hd (s : Fin 3) :
      x.1 (cyclicNext s) * x.1 (cyclicPrev s) = norm R (x.2 s) := by
    have h := congrArg (fun z : Model R => z.1 s) hx
    rwa [adjoint_diag, Prod.fst_zero, Pi.zero_apply, sub_eq_zero] at h
  have hb : x.1 i • x.2 i =
      conjugate (norm R) (x.2 (cyclicNext i) * x.2 (cyclicPrev i)) := by
    have h := congrArg (fun z : Model R => z.2 i) hx
    rw [adjoint_block, Prod.snd_zero, Pi.zero_apply, neg_smul, neg_add_eq_sub, sub_eq_zero] at h
    exact h.symm
  apply Prod.ext
  · funext s
    rcases cyclic_cases i s with rfl | rfl | rfl
    · rwa [chart_diag_here]
    · rw [chart_diag_next, ← hd (cyclicPrev i), next_prev, prev_prev, ha,
        ← mul_assoc, Units.inv_mul, one_mul]
    · rw [chart_diag_prev, ← hd (cyclicNext i), next_next, prev_next, ha,
        mul_comm (x.1 (cyclicPrev i)), ← mul_assoc, Units.inv_mul, one_mul]
  · funext s
    rcases cyclic_cases i s with rfl | rfl | rfl
    · rw [chart_block_here, ← hb, ha, smul_smul, Units.inv_mul, one_smul]
    · rw [chart_block_next]
    · rw [chart_block_prev]

theorem chartEquations : ChartEquationsType.{u} := by
  intro R _ i a x ha
  constructor
  · rintro ⟨ht, hq⟩
    have he := reconstruct_of_adjoint ha hq
    refine ⟨he, (chart_trace_iff i a _ _).mp ?_⟩
    exact (congrArg (IdempotentSpecification.trace (R := R)) he).symm.trans ht
  · rintro ⟨he, h⟩
    constructor
    · calc
        trace x = trace (chartCoordinates i a (x.2 (cyclicNext i)) (x.2 (cyclicPrev i))) :=
          congrArg trace he
        _ = 1 := (chart_trace_iff _ _ _ _).mpr h
    · calc
        adjoint x = adjoint (chartCoordinates i a (x.2 (cyclicNext i)) (x.2 (cyclicPrev i))) :=
          congrArg adjoint he
        _ = 0 := chart_adjoint_zero _ _ _ _

theorem chartEquivalence : ChartEquivalenceType.{u} := by
  intro R _ i
  refine ⟨Equiv.ofBijective (fun p : ChartPoint R => ⟨chartCoordinates i p.diagonal p.nextBlock p.prevBlock,
    ⟨(chart_trace_iff _ _ _ _).mpr p.equation, chart_adjoint_zero _ _ _ _⟩,
      (chart_diag_here i p.diagonal p.nextBlock p.prevBlock).symm ▸ p.diagonal.isUnit⟩) ⟨?_, ?_⟩, fun _ => rfl⟩
  · intro x y h
    have he := congrArg Subtype.val h
    have h₁ := congrArg (fun z : Model R => z.1 i) he
    have h₂ := congrArg (fun z : Model R => z.2 (cyclicNext i)) he
    have h₃ := congrArg (fun z : Model R => z.2 (cyclicPrev i)) he
    simp only [chart_diag_here] at h₁
    simp only [chart_block_next] at h₂
    simp only [chart_block_prev] at h₃
    have hd := Units.ext h₁
    cases x
    cases y
    congr
  · rintro ⟨x, hx, ⟨a, ha⟩⟩
    obtain ⟨he, h⟩ := (chartEquations R i a x ha.symm).mp hx
    exact ⟨⟨a, x.2 (cyclicNext i), x.2 (cyclicPrev i), h⟩, Subtype.ext he.symm⟩

theorem idempotents : IdempotentsType.{u} := by
  intro R _ x hx
  have h := (cubic_operator_identities (fun _ : Fin 3 => (1 : Rˣ))
    (Zorn.isOctonion R)).2.2.2.2.2.2.2.2.1 x
  change modelOp x cubicUnit = adjoint x + trace x • x -
    linearTrace (norm R) (fun _ => 1) (adjoint x) • cubicUnit at h
  rw [hx.2, hx.1, map_zero, one_smul, zero_smul, zero_add, sub_zero] at h
  exact h

private lemma axis_rank_one (i : Fin 3) : IsRankOneIdempotent (frameAxis i : Model R) :=
  let h := hermitian_frame_complements (norm R) (fun _ => 1) i
  ⟨h.1, h.2.1⟩

private lemma second_projector (x : Model R) :
    modelOp (cubicUnit - frameAxis 0) x =
      ((fun i => if i = 0 then 0 else x.1 i), Pi.single 0 (x.2 0)) := by
  have h := (hermitian_frame_complements (norm R) (fun _ => 1) 0).2.2.2 x
  change modelOp (cubicUnit - frameAxis 0) x = x.1 1 • frameAxis 1 +
    x.1 2 • frameAxis 2 + singleBlockCoordinates 0 (x.2 0) at h
  rw [h]
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [frameAxis, FrameSpecification.frameAxis, diagonalCoordinates,
        CubicSpecification.diagonalCoordinates, singleBlockCoordinates,
        CubicSpecification.singleBlockCoordinates, Pi.single_apply, smul_eq_mul]
  · funext i
    simp [frameAxis, FrameSpecification.frameAxis, diagonalCoordinates,
      CubicSpecification.diagonalCoordinates, singleBlockCoordinates,
      CubicSpecification.singleBlockCoordinates]

private lemma second_trace (a : R) (c : Zorn R) :
    trace (secondCoordinates a c) = 1 := by
  rw [trace_cyclic _ 0]
  change 0 + a + (1 - a) = 1
  ring

private lemma second_adjoint_iff (a : R) (c : Zorn R) :
    adjoint (secondCoordinates a c) = 0 ↔ a * (1 - a) = norm R c := by
  constructor
  · intro h
    have h0 := congrArg (fun x : Model R => x.1 0) h
    rw [adjoint_diag] at h0
    change a * (1 - a) - norm R c = 0 at h0
    exact sub_eq_zero.mp h0
  · intro h
    let b : Fin 3 → Zorn R := Pi.single 0 c
    have h1 : b 1 = 0 := Pi.single_eq_of_ne (by decide : (1 : Fin 3) ≠ 0) c
    have h2 : b 2 = 0 := Pi.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 0) c
    apply Prod.ext <;> funext i
    · rw [adjoint_diag]
      fin_cases i
      · change a * (1 - a) - norm R c = 0
        exact sub_eq_zero.mpr h
      · change (1 - a) * 0 - norm R (b 1) = 0
        simp only [h1, mul_zero, QuadraticMap.map_zero, sub_zero]
      · change 0 * a - norm R (b 2) = 0
        simp only [h2, zero_mul, QuadraticMap.map_zero, sub_zero]
    · rw [adjoint_block]
      fin_cases i
      · change -(0 : R) • b 0 + conjugate (norm R) (b 1 * b 2) = 0
        simp only [h1, neg_zero, zero_smul, zero_mul, map_zero, add_zero]
      · change -a • b 1 + conjugate (norm R) (b 2 * b 0) = 0
        simp only [h1, h2, smul_zero, zero_mul, map_zero, add_zero]
      · change -(1 - a) • b 2 + conjugate (norm R) (b 0 * b 1) = 0
        simp only [h1, h2, smul_zero, mul_zero, map_zero, add_zero]

private lemma second_components (a : R) (c : Zorn R) :
    (secondCoordinates a c).1 1 = a ∧ (secondCoordinates a c).2 0 = c := by
  simp [secondCoordinates]

theorem secondEquations : SecondEquationsType.{u} := by
  intro R _ x
  constructor
  · rintro ⟨_, ⟨ht, ha⟩, hu⟩
    rw [second_projector] at hu
    have h0 : x.1 0 = 0 := (congrArg (fun z : Model R => z.1 0) hu).symm
    have ht' := (trace_cyclic x 0).symm.trans ht
    change x.1 0 + x.1 1 + x.1 2 = 1 at ht'
    have h2 : x.1 2 = 1 - x.1 1 := by linear_combination ht' - h0
    have he : x = secondCoordinates (x.1 1) (x.2 0) := by
      apply Prod.ext
      · funext i
        fin_cases i
        · exact h0
        · rfl
        · exact h2
      · exact (congrArg Prod.snd hu).symm
    exact ⟨he, (second_adjoint_iff _ _).mp ((congrArg adjoint he).symm.trans ha)⟩
  · rintro ⟨he, h⟩
    have hq : IsRankOneIdempotent (secondCoordinates (x.1 1) (x.2 0)) :=
      ⟨second_trace _ _, (second_adjoint_iff _ _).mpr h⟩
    refine ⟨axis_rank_one 0, ?_, ?_⟩
    · exact he ▸ hq
    · rw [second_projector]
      apply Prod.ext
      · funext i
        change (if i = 0 then 0 else x.1 i) = x.1 i
        split_ifs with hi
        · subst i
          exact (congrArg (fun z : Model R => z.1 0) he).symm
        · rfl
      · exact (congrArg Prod.snd he).symm

theorem secondEquivalence : SecondEquivalenceType.{u} := by
  intro R _
  let f (p : {p : R × Zorn R // p.1 * (1 - p.1) = norm R p.2}) :
      {x : Model R // IsFramePair (frameAxis 0) x} :=
    ⟨secondCoordinates p.val.1 p.val.2, (secondEquations R _).mpr (by
      rw [(second_components _ _).1, (second_components _ _).2]
      exact ⟨rfl, p.property⟩)⟩
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩, fun _ => rfl⟩
  · intro p q h
    apply Subtype.ext
    apply Prod.ext
    · calc
        p.val.1 = (f p).val.1 1 := (second_components _ _).1.symm
        _ = (f q).val.1 1 := by rw [h]
        _ = q.val.1 := (second_components _ _).1
    · calc
        p.val.2 = (f p).val.2 0 := (second_components _ _).2.symm
        _ = (f q).val.2 0 := by rw [h]
        _ = q.val.2 := (second_components _ _).2
  · intro x
    obtain ⟨he, h⟩ := (secondEquations R _).mp x.property
    exact ⟨⟨(x.val.1 1, x.val.2 0), h⟩, Subtype.ext he.symm⟩

end Points

section Presentations

open MvPolynomial AlgebraicGeometry

variable {k : Type u} [CommRing k] {S : Type v} [CommRing S] [Algebra k S]

private lemma modelOfVariables_inverse (x : Model S) :
    modelOfVariables (modelVariables x) = x := by
  exact Prod.ext rfl (funext fun i => (Zorn.pairedFunctions S).symm_apply_apply _)

private lemma modelVariables_inverse (z : CoordinateIndex → S) :
    modelVariables (modelOfVariables z) = z := by
  funext j
  rcases j with i | ⟨i, j⟩
  · rfl
  · exact congrFun ((Zorn.pairedFunctions S).apply_symm_apply _) j

private lemma pairedFunctions_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (z : Zorn A) (j : ZornIndex) :
    Zorn.pairedFunctions B (Composition.ZornSpecification.mapCoordinates f z) j =
      f (Zorn.pairedFunctions A z j) := by
  rcases z with ⟨a, x, y, b⟩
  rcases j with (_ | i) | (_ | i)
  · rfl
  · rfl
  · rfl
  · exact (map_neg f (y i)).symm

private def mapModel {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (x : Model A) : Model B :=
  (fun i => f (x.1 i), fun i => Composition.ZornSpecification.mapCoordinates f (x.2 i))

private lemma modelOfVariables_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (z : CoordinateIndex → A) :
    modelOfVariables (f ∘ z) = mapModel f (modelOfVariables z) := by
  apply Prod.ext
  · rfl
  · funext i
    apply (Zorn.pairedFunctions B).injective
    funext j
    simp only [modelOfVariables, LinearEquiv.apply_symm_apply, Function.comp_apply]
    change _ = Zorn.pairedFunctions B (Composition.ZornSpecification.mapCoordinates f _) j
    simp only [pairedFunctions_map, LinearEquiv.apply_symm_apply]

private lemma zorn_map_smul {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (a : A) (x : Zorn A) :
    Composition.ZornSpecification.mapCoordinates f (a • x) =
      f a • Composition.ZornSpecification.mapCoordinates f x := by
  apply (Zorn.pairedFunctions B).injective
  funext j
  simp only [pairedFunctions_map, map_smul, Pi.smul_apply, smul_eq_mul, map_mul]

private lemma zorn_map_add {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (x y : Zorn A) :
    Composition.ZornSpecification.mapCoordinates f (x + y) =
      Composition.ZornSpecification.mapCoordinates f x +
        Composition.ZornSpecification.mapCoordinates f y := by
  apply (Zorn.pairedFunctions B).injective
  funext j
  simp only [pairedFunctions_map, map_add, Pi.add_apply]

private lemma mapModel_add {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (x y : Model A) : mapModel f (x + y) = mapModel f x + mapModel f y :=
  Prod.ext (funext fun i => map_add f (x.1 i) (y.1 i))
    (funext fun i => zorn_map_add f (x.2 i) (y.2 i))

private lemma mapModel_sub {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (x y : Model A) : mapModel f (x - y) = mapModel f x - mapModel f y := by
  apply Prod.ext
  · exact funext fun i => map_sub f (x.1 i) (y.1 i)
  · funext i
    apply (Zorn.pairedFunctions B).injective
    funext j
    simp only [mapModel, Prod.snd_sub, Pi.sub_apply, pairedFunctions_map, map_sub]

private lemma mapModel_unit {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    mapModel f cubicUnit = cubicUnit := by
  apply Prod.ext <;> funext i
  · exact map_one f
  · apply (Zorn.pairedFunctions B).injective
    funext j
    simp [mapModel, CubicSpecification.cubicUnit, pairedFunctions_map]

private lemma mapModel_scalar {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (a : A) (x : Model A) : mapModel f (a • x) = f a • mapModel f x :=
  Prod.ext (funext fun i => map_mul f a (x.1 i))
    (funext fun i => zorn_map_smul f a (x.2 i))

private lemma zorn_map_conjugate {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (x : Zorn A) :
    Composition.ZornSpecification.mapCoordinates f (conjugate (norm A) x) =
      conjugate (norm B) (Composition.ZornSpecification.mapCoordinates f x) := by
  rcases x with ⟨a, u, v, b⟩
  change Composition.ZornSpecification.mapCoordinates f
      (conjugate (norm A) (Zorn.ofCoordinates (a, u, v, b))) =
    conjugate (norm B) (Zorn.ofCoordinates (f a, f ∘ u, f ∘ v, f b))
  rw [Zorn.conjugate_formula, Zorn.conjugate_formula]
  apply (Zorn.coordinates B).injective
  simp [Composition.ZornSpecification.mapCoordinates, Function.comp_def, Pi.neg_def]

private lemma trace_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (x : Model A) :
    trace (mapModel f x) = f (trace x) := by
  rw [trace_cyclic _ 0, trace_cyclic _ 0, map_add, map_add]
  rfl

private lemma adjoint_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (x : Model A) :
    adjoint (mapModel f x) = mapModel f (adjoint x) := by
  apply Prod.ext <;> funext i
  · rw [adjoint_diag]
    change f _ * f _ - norm B (Composition.ZornSpecification.mapCoordinates f _) =
      f ((adjoint x).1 i)
    rw [adjoint_diag, Zorn.mapCoordinates_norm, map_sub, map_mul]
  · rw [adjoint_block]
    change _ = Composition.ZornSpecification.mapCoordinates f ((adjoint x).2 i)
    rw [adjoint_block, zorn_map_add, zorn_map_smul, map_neg, zorn_map_conjugate,
      Zorn.mapCoordinates_mul]
    rfl

private lemma modelOp_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (x y : Model A) :
    mapModel f (modelOp x y) = modelOp (mapModel f x) (mapModel f y) := by
  have hpolar (a b : Zorn A) :
      (norm B).polarBilin (Composition.ZornSpecification.mapCoordinates f a)
        (Composition.ZornSpecification.mapCoordinates f b) = f ((norm A).polarBilin a b) := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      ← zorn_map_add, Zorn.mapCoordinates_norm, map_sub]
  have hpair (a b : Model A) :
      CubicSpecification.tracePairing (norm B) (fun _ => 1) (mapModel f a) (mapModel f b) =
        f (CubicSpecification.tracePairing (norm A) (fun _ => 1) a b) := by
    change (∑ i : Fin 3, (f (a.1 i) * f (b.1 i) +
      CubicSpecification.blockWeight (fun _ => (1 : Bˣ)) i * (norm B).polarBilin
        (Composition.ZornSpecification.mapCoordinates f (a.2 i))
        (Composition.ZornSpecification.mapCoordinates f (b.2 i)))) =
      f (∑ i : Fin 3, (a.1 i * b.1 i +
        CubicSpecification.blockWeight (fun _ => (1 : Aˣ)) i * (norm A).polarBilin (a.2 i) (b.2 i)))
    simp [CubicSpecification.blockWeight, hpolar]
  simp only [TrialitySpecification.modelOp, QuadraticOperatorSpecification.applyOperator,
    CubicSpecification.adjointCross, mapModel_sub, mapModel_scalar, ← adjoint_map,
    mapModel_add, hpair]

private lemma modelVariables_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (x : Model A) (j : CoordinateIndex) :
    modelVariables (mapModel f x) j = f (modelVariables x j) := by
  rcases j with i | ⟨i, j⟩
  · rfl
  · exact pairedFunctions_map f _ _

private lemma frameEquation_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (x : Bool → Model A) (j : FrameEquationIndex) :
    frameEquation (mapModel f ∘ x) j = f (frameEquation x j) := by
  rcases j with ⟨b, j | j⟩ | j
  · change trace (mapModel f (x b)) - 1 = f (trace (x b) - 1)
    rw [trace_map, map_sub, map_one]
  · exact (congrArg (fun a => modelVariables a j) (adjoint_map f (x b))).trans
      (modelVariables_map f _ _)
  · change modelVariables (modelOp (cubicUnit - mapModel f (x false))
        (mapModel f (x true)) - mapModel f (x true)) j =
      f (modelVariables (modelOp (cubicUnit - x false) (x true) - x true) j)
    rw [← modelVariables_map, mapModel_sub, modelOp_map, mapModel_sub, mapModel_unit]

private lemma frameEquation_zero_iff (x : Bool → Model S) :
    (∀ j, frameEquation x j = 0) ↔ IsFramePair (x false) (x true) := by
  have hzero (a : Model S) : (∀ j, modelVariables a j = 0) ↔ a = 0 := by
    constructor
    · intro h
      rw [← modelOfVariables_inverse a, show modelVariables a = modelVariables (0 : Model S) from
        funext fun j => (h j).trans (by cases j <;> simp [modelVariables])]
      exact modelOfVariables_inverse _
    · rintro rfl j
      cases j <;> simp [modelVariables]
  constructor
  · intro h
    exact ⟨⟨sub_eq_zero.mp (h (.inl (false, .inl ()))), (hzero _).mp
      (fun j => h (.inl (false, .inr j)))⟩,
      ⟨sub_eq_zero.mp (h (.inl (true, .inl ()))), (hzero _).mp
        (fun j => h (.inl (true, .inr j)))⟩,
      sub_eq_zero.mp ((hzero _).mp fun j => h (.inr j))⟩
  · rintro ⟨hf, ht, hp⟩ (⟨b, j | j⟩ | j)
    · cases b
      · exact sub_eq_zero.mpr hf.1
      · exact sub_eq_zero.mpr ht.1
    · exact (hzero _).mpr (by cases b; exacts [hf.2, ht.2]) j
    · exact (hzero _).mpr (sub_eq_zero.mpr hp) j

private lemma quotientHom_ext {ι : Type*} {I : Ideal (MvPolynomial ι k)}
    {f g : (MvPolynomial ι k ⧸ I) →ₐ[k] S}
    (h : ∀ j, f (Ideal.Quotient.mk _ (X j)) = g (Ideal.Quotient.mk _ (X j))) : f = g := by
  have eq : f.comp (Ideal.Quotient.mkₐ k I) = g.comp (Ideal.Quotient.mkₐ k I) :=
    MvPolynomial.algHom_ext h
  apply AlgHom.ext
  intro t
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective t
  exact DFunLike.congr_fun eq p

private lemma quotientHom_zero {ι : Type*} {I : Ideal (MvPolynomial ι k)}
    (f : (MvPolynomial ι k ⧸ I) →ₐ[k] S) {p : MvPolynomial ι k} (hp : p ∈ I) :
    f (Ideal.Quotient.mk _ p) = 0 :=
  (congrArg f (Ideal.Quotient.eq_zero_iff_mem.mpr hp)).trans (map_zero f)

private lemma first_hom_point (f : IdempotentRing k →ₐ[k] S) :
    IsRankOneIdempotent (idempotentOfHom k f) := by
  let g := f.comp (Ideal.Quotient.mkₐ k (idempotentIdeal k))
  have he : idempotentOfHom k f = mapModel g.toRingHom (genericIdempotent k) :=
    modelOfVariables_map _ _
  rw [IsRankOneIdempotent, he, trace_map, adjoint_map]
  constructor
  · apply sub_eq_zero.mp
    rw [← map_one g.toRingHom, ← map_sub g.toRingHom]
    exact quotientHom_zero f (Ideal.subset_span (Or.inl (Set.mem_insert _ _)))
  · apply Prod.ext <;> funext i
    · exact quotientHom_zero f (Ideal.subset_span (Or.inl (Set.mem_insert_of_mem _ ⟨i, rfl⟩)))
    · apply (Zorn.pairedFunctions S).injective
      funext j
      change Zorn.pairedFunctions S
        (Composition.ZornSpecification.mapCoordinates g.toRingHom
          ((adjoint (genericIdempotent k)).2 i)) j = _
      rw [pairedFunctions_map]
      have hz := quotientHom_zero f (Ideal.subset_span
        (Or.inr (Set.mem_range_self (i, j)) : _ ∈
          insert (trace (genericIdempotent k) - 1)
            (Set.range fun i => (adjoint (genericIdempotent k)).1 i) ∪
            Set.range fun (ij : Fin 3 × ZornIndex) =>
              Zorn.pairedFunctions _ ((adjoint (genericIdempotent k)).2 ij.1) ij.2))
      have hz' : g.toRingHom
          (Zorn.pairedFunctions _ ((adjoint (genericIdempotent k)).2 i) j) = 0 := hz
      simpa only [Prod.snd_zero, Pi.zero_apply, map_zero] using hz'

private noncomputable def firstPointHom (x : IdempotentPoint S) : IdempotentRing k →ₐ[k] S := by
  let g := MvPolynomial.aeval (R := k) (modelVariables x.val)
  have h : mapModel g.toRingHom (genericIdempotent k) = x.val := by
    rw [genericIdempotent, ← modelOfVariables_map]
    change modelOfVariables (fun j => g (X j)) = x.val
    simp only [g, MvPolynomial.aeval_X, modelOfVariables_inverse]
  apply Ideal.Quotient.liftₐ _ g
  intro p hp
  have hker : idempotentIdeal k ≤ RingHom.ker g.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ((rfl | ⟨i, rfl⟩) | ⟨⟨i, j⟩, rfl⟩)
    · change g.toRingHom (trace (genericIdempotent k) - 1) = 0
      rw [map_sub, map_one, ← trace_map, h, x.property.1, sub_self]
    · change (mapModel _ (adjoint (genericIdempotent k))).1 i = 0
      rw [← adjoint_map, h, x.property.2]
      rfl
    · change g.toRingHom (Zorn.pairedFunctions _ ((adjoint (genericIdempotent k)).2 i) j) = 0
      rw [← pairedFunctions_map]
      change Zorn.pairedFunctions S ((mapModel _ (adjoint (genericIdempotent k))).2 i) j = 0
      rw [← adjoint_map, h, x.property.2]
      simp
  exact hker hp

private lemma firstPointHom_var (x : IdempotentPoint S) (j : CoordinateIndex) :
    firstPointHom (k := k) x (Ideal.Quotient.mk _ (X j)) = modelVariables x.val j := by
  change MvPolynomial.aeval (R := k) (modelVariables x.val) (X j) = _
  exact MvPolynomial.aeval_X _ _

theorem firstRepresentation : FirstRepresentationType.{u,v} := by
  intro k _ S _ _
  refine ⟨⟨fun f => ⟨idempotentOfHom k f, first_hom_point f⟩, firstPointHom,
    ?_, ?_⟩, fun _ => rfl⟩
  · intro f
    apply quotientHom_ext
    intro j
    rw [firstPointHom_var]
    exact congrFun (modelVariables_inverse (fun j => f (Ideal.Quotient.mk _ (X j)))) j
  · intro x
    apply Subtype.ext
    change idempotentOfHom k (firstPointHom x) = x.val
    simp only [idempotentOfHom, firstPointHom_var, modelOfVariables_inverse]

theorem chartCover : ChartCoverType.{u} := by
  intro k _
  apply top_unique
  intro p _
  have h : ∑ i : Fin 3, diagonalCoordinate k i = 1 := by
    change ∑ i : Fin 3, Ideal.Quotient.mk (idempotentIdeal k) (X (.inl i)) = 1
    rw [← map_sum]
    apply sub_eq_zero.mp
    rw [← map_one (Ideal.Quotient.mk (idempotentIdeal k)), ← map_sub]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← show trace (genericIdempotent k) = ∑ i : Fin 3, X (.inl i) from
      Albert.linearTrace_apply _ _]
    exact Ideal.subset_span (Or.inl (Set.mem_insert _ _))
  simp only [TopologicalSpace.Opens.mem_iSup, PrimeSpectrum.mem_basicOpen]
  by_contra! ha
  have := p.asIdeal.sum_mem (t := Finset.univ) (fun i _ => ha i)
  exact p.isPrime.ne_top (p.asIdeal.eq_top_iff_one.mpr (h ▸ this))

private lemma frame_hom_point (f : FrameRing k →ₐ[k] S) :
    IsFramePair (frameOfHom k f).1 (frameOfHom k f).2 := by
  let g := f.comp (Ideal.Quotient.mkₐ k (frameIdeal k))
  let x : Bool → Model S := mapModel g.toRingHom ∘ genericFrame k
  have h (b : Bool) : x b =
      modelOfVariables (fun j : CoordinateIndex => f (Ideal.Quotient.mk _ (X (b, j)))) :=
    (modelOfVariables_map _ _).symm
  change IsFramePair
    (modelOfVariables fun j => f (Ideal.Quotient.mk (frameIdeal k) (X (false, j))))
    (modelOfVariables fun j => f (Ideal.Quotient.mk (frameIdeal k) (X (true, j))))
  rw [← h false, ← h true]
  apply (frameEquation_zero_iff x).mp
  intro j
  rw [show x = mapModel g.toRingHom ∘ genericFrame k from rfl, frameEquation_map]
  exact quotientHom_zero f (Ideal.subset_span (Set.mem_range_self j))

private noncomputable def framePointHom (p : FramePairPoint S) : FrameRing k →ₐ[k] S := by
  let x (b : Bool) := if b then p.val.2 else p.val.1
  let g : MvPolynomial FrameIndex k →ₐ[k] S := aeval fun j => modelVariables (x j.1) j.2
  have hx : mapModel g.toRingHom ∘ genericFrame k = x := by
    funext b
    rw [Function.comp_apply, genericFrame, ← modelOfVariables_map]
    change modelOfVariables (fun j => g (X (b, j))) = _
    simp only [g, aeval_X, modelOfVariables_inverse]
  apply Ideal.Quotient.liftₐ (frameIdeal k) g
  have hker : frameIdeal k ≤ RingHom.ker g.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change g.toRingHom (frameEquation (genericFrame k) j) = 0
    rw [← frameEquation_map, hx]
    exact (frameEquation_zero_iff x).mpr p.property j
  exact fun _ ha => hker ha

private lemma framePointHom_var (p : FramePairPoint S) (b : Bool) (j : CoordinateIndex) :
    framePointHom (k := k) p (Ideal.Quotient.mk (frameIdeal k) (X (b, j))) =
      modelVariables (if b then p.val.2 else p.val.1) j := by
  change aeval (R := k) (fun i : FrameIndex =>
    modelVariables (if i.1 then p.val.2 else p.val.1) i.2) (X (b, j)) = _
  rw [aeval_X]

private noncomputable def frameHomEquiv :
    (FrameRing k →ₐ[k] S) ≃ FramePairPoint S where
  toFun f := ⟨frameOfHom k f, frame_hom_point f⟩
  invFun := framePointHom
  left_inv f := by
    apply quotientHom_ext
    rintro ⟨b, j⟩
    rw [framePointHom_var]
    cases b
    · exact congrFun (modelVariables_inverse
        (fun l => f (Ideal.Quotient.mk (frameIdeal k) (X (false, l))))) j
    · exact congrFun (modelVariables_inverse
        (fun l => f (Ideal.Quotient.mk (frameIdeal k) (X (true, l))))) j
  right_inv p := by
    apply Subtype.ext
    change frameOfHom k (framePointHom p) = p.val
    apply Prod.ext
    · exact (congrArg modelOfVariables (funext fun j => framePointHom_var p false j)).trans
        (modelOfVariables_inverse p.val.1)
    · exact (congrArg modelOfVariables (funext fun j => framePointHom_var p true j)).trans
        (modelOfVariables_inverse p.val.2)

theorem frameRepresentation : FrameRepresentationType.{u,v} :=
  fun _ _ _ _ _ => ⟨frameHomEquiv, fun _ => rfl⟩

private lemma frameOfHom_point (p : FramePairPoint S) :
    frameOfHom k (framePointHom p) = p.val :=
  congrArg Subtype.val ((frameHomEquiv (k := k)).apply_symm_apply p)

private lemma frameOfHom_comp {T : Type w} [CommRing T] [Algebra k T]
    (g : S →ₐ[k] T) (f : FrameRing k →ₐ[k] S) :
    frameOfHom k (g.comp f) =
      (mapModel g.toRingHom (frameOfHom k f).1, mapModel g.toRingHom (frameOfHom k f).2) :=
  Prod.ext
    (modelOfVariables_map g.toRingHom (fun j => f (Ideal.Quotient.mk (frameIdeal k) (X (false, j)))))
    (modelOfVariables_map g.toRingHom (fun j => f (Ideal.Quotient.mk (frameIdeal k) (X (true, j)))))

end Presentations

section Quadrics

open MvPolynomial AlgebraicGeometry

variable {k : Type u} [CommRing k] {S : Type v} [CommRing S] [Algebra k S]
variable {ι : Type w} [Fintype ι]

private def quadricValue {A : Type*} [CommRing A] (z : QuadricIndex ι → A) : A :=
  z none ^ 2 - z none + ∑ j : ι, z (some (j, false)) * z (some (j, true))

private lemma aeval_quadric (z : QuadricIndex ι → S) :
    MvPolynomial.aeval z (quadricEquation k ι) = quadricValue z := by
  simp [quadricEquation, quadricValue, map_sum]

private lemma quadricOfHom_equation (f : QuadricRing k ι →ₐ[k] S) :
    quadricValue (quadricOfHom k ι f) = 0 := by
  let g := f.comp (Ideal.Quotient.mkₐ k (Ideal.span {quadricEquation k ι}))
  have h : g (quadricEquation k ι) = 0 :=
    quotientHom_zero f (Ideal.subset_span (Set.mem_singleton (quadricEquation k ι)))
  change quadricValue (fun j => g (X j)) = 0
  simpa only [quadricEquation, quadricValue, map_pow, map_sub, map_add, map_sum, map_mul] using h

private noncomputable def quadricPointHom (z : QuadricIndex ι → S) (hz : quadricValue z = 0) :
    QuadricRing k ι →ₐ[k] S :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval z) (by
    have h : Ideal.span {quadricEquation k ι} ≤
        RingHom.ker (MvPolynomial.aeval z).toRingHom :=
      Ideal.span_le.mpr (by
        rintro _ rfl
        exact (aeval_quadric z).trans hz)
    exact fun _ hp => h hp)

private lemma quadricPointHom_var (z : QuadricIndex ι → S) (hz : quadricValue z = 0) (j) :
    quadricOfHom k ι (quadricPointHom z hz) j = z j :=
  MvPolynomial.aeval_X z j

private lemma quadricHom_bijective :
    Function.Bijective (fun f : QuadricRing k ι →ₐ[k] S =>
      (⟨quadricOfHom k ι f, quadricOfHom_equation f⟩ :
        {z : QuadricIndex ι → S // quadricValue z = 0})) := by
  constructor
  · intro f g h
    apply quotientHom_ext
    exact congrFun (congrArg Subtype.val h)
  · rintro ⟨z, hz⟩
    exact ⟨quadricPointHom z hz, Subtype.ext (funext (quadricPointHom_var z hz))⟩

private lemma octonionOfPairs_apply {A : Type*} [CommRing A]
    (z : Option (Fin 3) × Bool → A) (j : Option (Fin 3)) :
    Zorn.pairedFunctions A (octonionOfPairs z) (.inl j) = z (j, false) ∧
    Zorn.pairedFunctions A (octonionOfPairs z) (.inr j) = z (j, true) := by
  simp [octonionOfPairs]

private lemma norm_octonionOfPairs {A : Type*} [CommRing A]
    (z : Option (Fin 3) × Bool → A) :
    norm A (octonionOfPairs z) = ∑ j : Option (Fin 3), z (j, false) * z (j, true) := by
  change (∑ j : Option (Fin 3), Zorn.pairedFunctions A (octonionOfPairs z) (.inl j) *
    Zorn.pairedFunctions A (octonionOfPairs z) (.inr j)) = _
  exact Finset.sum_congr rfl fun j _ => by rw [(octonionOfPairs_apply z j).1,
    (octonionOfPairs_apply z j).2]

private def octonionPairs {A : Type*} [CommRing A] (c : Zorn A) :
    Option (Fin 3) × Bool → A
  | (j, false) => Zorn.pairedFunctions A c (.inl j)
  | (j, true) => Zorn.pairedFunctions A c (.inr j)

private lemma octonionOfPairs_inverse {A : Type*} [CommRing A] (c : Zorn A) :
    octonionOfPairs (octonionPairs c) = c := by
  apply (Zorn.pairedFunctions A).injective
  funext j
  rcases j with j | j
  · exact (octonionOfPairs_apply _ j).1
  · exact (octonionOfPairs_apply _ j).2

private lemma octonionPairs_inverse {A : Type*} [CommRing A]
    (z : Option (Fin 3) × Bool → A) : octonionPairs (octonionOfPairs z) = z := by
  funext j
  rcases j with ⟨i, b⟩
  cases b
  · exact (octonionOfPairs_apply z i).1
  · exact (octonionOfPairs_apply z i).2

private noncomputable def secondQuadricEquiv (S : Type v) [CommRing S] :
    {z : QuadricIndex (Option (Fin 3)) → S // quadricValue z = 0} ≃
      {p : S × Zorn S // p.1 * (1 - p.1) = norm S p.2} where
  toFun z := ⟨(z.val none, octonionOfPairs fun j => z.val (some j)), by
    simp only [norm_octonionOfPairs]
    have h := z.property
    unfold quadricValue at h
    linear_combination -h⟩
  invFun p := ⟨fun j => Option.elim j p.val.1 (octonionPairs p.val.2), by
    unfold quadricValue
    change p.val.1 ^ 2 - p.val.1 + ∑ j : Option (Fin 3),
      octonionPairs p.val.2 (j, false) * octonionPairs p.val.2 (j, true) = 0
    rw [← norm_octonionOfPairs, octonionOfPairs_inverse]
    linear_combination -p.property⟩
  left_inv z := by
    apply Subtype.ext
    funext j
    rcases j with _ | j
    · rfl
    · exact congrFun (octonionPairs_inverse (fun j => z.val (some j))) j
  right_inv p := Subtype.ext (Prod.ext rfl (octonionOfPairs_inverse p.val.2))

theorem secondRepresentation : SecondRepresentationType.{u,v} := by
  intro k _ S _ _
  obtain ⟨e, he⟩ := secondEquivalence S
  exact ⟨((Equiv.ofBijective _ quadricHom_bijective).trans (secondQuadricEquiv S)).trans e,
    fun _ => he _⟩

/-- A square-zero correction that works even when the base has characteristic two. -/
private lemma lift_quadric (I : Ideal S) (hI : I ^ 2 = ⊥)
    (z : QuadricIndex ι → S ⧸ I) (hz : quadricValue z = 0) :
    ∃ y : QuadricIndex ι → S, quadricValue y = 0 ∧ ∀ j, Ideal.Quotient.mk I (y j) = z j := by
  classical
  let q := Ideal.Quotient.mk I
  let x : QuadricIndex ι → S := Function.surjInv Ideal.Quotient.mk_surjective ∘ z
  have hx (j : QuadricIndex ι) : q (x j) = z j := Function.surjInv_eq _ _
  let a := x none
  let b (j : ι) := x (some (j, false))
  let c (j : ι) := x (some (j, true))
  let e := quadricValue x
  have he : q e = 0 := by
    simp only [e, quadricValue, map_add, map_sub, map_pow, map_sum, map_mul, hx]
    exact hz
  have hsq : e ^ 2 = 0 := by
    have h := Ideal.mul_mem_mul (Ideal.Quotient.eq_zero_iff_mem.mp he)
      (Ideal.Quotient.eq_zero_iff_mem.mp he)
    simpa only [← pow_two, hI, Ideal.mem_bot] using h
  let y : QuadricIndex ι → S
    | none => a - (2 * a - 1) * e
    | some (j, false) => b j - 4 * b j * e
    | some (j, true) => c j
  refine ⟨y, ?_, ?_⟩
  · have hterm (j : ι) :
        (b j - 4 * b j * e) * c j = b j * c j - (4 * e) * (b j * c j) := by ring
    have h0 : e = a ^ 2 - a + ∑ j, b j * c j := rfl
    change (a - (2 * a - 1) * e) ^ 2 - (a - (2 * a - 1) * e) +
      (∑ j, (b j - 4 * b j * e) * c j) = 0
    simp only [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
    linear_combination (4 * e - 1) * h0 + ((2 * a - 1)^2 - 4) * hsq
  · rintro (_ | ⟨j, _ | _⟩)
    · change q (a - (2 * a - 1) * e) = z none
      simp [a, he, hx]
    · change q (b j - 4 * b j * e) = z (some (j, false))
      simp [b, he, hx]
    · exact hx _

private lemma quadric_smooth (k : Type u) [CommRing k] (ι : Type w) [Fintype ι] :
    Algebra.Smooth k (QuadricRing k ι) := by
  refine ⟨Algebra.FormallySmooth.iff_comp_surjective.mpr ?_,
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_singleton _))⟩
  intro T _ _ I hI f
  obtain ⟨z, hz, he⟩ := lift_quadric I hI (quadricOfHom k ι f) (quadricOfHom_equation f)
  refine ⟨quadricPointHom z hz, quotientHom_ext (fun j => ?_)⟩
  exact (congrArg (Ideal.Quotient.mk I) (quadricPointHom_var z hz j)).trans (he j)

end Quadrics

section ChartRings

open MvPolynomial AlgebraicGeometry

variable {k : Type u} [CommRing k]
variable {S : Type v} [CommRing S] [Algebra k S]

private abbrev PairIndex := Bool × Option (Fin 3)

private def chartVariables {A : Type*} [CommRing A] (a : A) (c d : Zorn A) :
    QuadricIndex PairIndex → A
  | none => a
  | some ((false, j), b) => octonionPairs c (j, b)
  | some ((true, j), b) => octonionPairs d (j, b)

private def chartOctonion {A : Type*} [CommRing A]
    (z : QuadricIndex PairIndex → A) (b : Bool) : Zorn A :=
  octonionOfPairs fun j => z (some ((b, j.1), j.2))

private lemma chartVariables_block {A : Type*} [CommRing A]
    (a : A) (c d : Zorn A) :
    chartOctonion (chartVariables a c d) false = c ∧
      chartOctonion (chartVariables a c d) true = d :=
  ⟨octonionOfPairs_inverse c, octonionOfPairs_inverse d⟩

private lemma chartVariables_inverse {A : Type*} [CommRing A]
    (z : QuadricIndex PairIndex → A) :
    chartVariables (z none) (chartOctonion z false) (chartOctonion z true) = z := by
  funext j
  rcases j with _ | ⟨⟨i, j⟩, b⟩
  · rfl
  cases i <;> cases b
  · exact (octonionOfPairs_apply _ j).1
  · exact (octonionOfPairs_apply _ j).2
  · exact (octonionOfPairs_apply _ j).1
  · exact (octonionOfPairs_apply _ j).2

private lemma quadricValue_chart {A : Type*} [CommRing A]
    (z : QuadricIndex PairIndex → A) :
    quadricValue z = z none ^ 2 - z none +
      norm A (chartOctonion z false) + norm A (chartOctonion z true) := by
  simp only [quadricValue, chartOctonion, norm_octonionOfPairs, Fintype.sum_prod_type,
    Fintype.sum_bool, add_assoc]
  rw [add_comm (∑ y : Option (Fin 3), z (some ((true, y), false)) * z (some ((true, y), true)))]

private lemma liftAlgHom_eval {R : Type*} [CommRing R] [Algebra k R] (a : R)
    (f : R →ₐ[k] S) (ha : IsUnit (f a)) (r : R) :
    (IsLocalization.Away.liftAlgHom (S := Localization.Away a) a ha)
      (algebraMap R (Localization.Away a) r) = f r :=
  IsLocalization.Away.lift_eq a ha r

private lemma localizationAlgHom_eq {R : Type*} [CommRing R] [Algebra k R]
    (a : R) {f g : Localization.Away a →ₐ[k] S}
    (h : ∀ t, f (algebraMap R _ t) = g (algebraMap R _ t)) : f = g :=
  IsLocalization.algHom_ext (Submonoid.powers a) (AlgHom.ext h)

private noncomputable def openPoint (i : Fin 3)
    (f : Localization.Away (diagonalCoordinate k i) →ₐ[k] S) : IdempotentPoint S :=
  let g := f.comp (Algebra.algHom k (IdempotentRing k) _)
  ⟨idempotentOfHom k g, first_hom_point g⟩

private lemma openPoint_unit (i : Fin 3)
    (f : Localization.Away (diagonalCoordinate k i) →ₐ[k] S) :
    IsUnit ((openPoint i f).val.1 i) := by
  change IsUnit (f (algebraMap (IdempotentRing k) _
    (diagonalCoordinate k i)))
  exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away
    (diagonalCoordinate k i)) (diagonalCoordinate k i)).map f

private noncomputable def chartPointOfHom (f : ChartRing k →ₐ[k] S) : ChartPoint S := by
  let g := f.comp (Algebra.algHom k (QuadricRing k PairIndex) (ChartRing k))
  let z := quadricOfHom k PairIndex g
  have ha : IsUnit (z none) := (IsLocalization.Away.algebraMap_isUnit
    (S := ChartRing k) (quadricScalar k PairIndex)).map f
  have hz := quadricOfHom_equation g
  rw [quadricValue_chart] at hz
  exact ⟨ha.unit, chartOctonion z false, chartOctonion z true,
    by simpa only [IsUnit.unit_spec] using hz⟩

private lemma chartPointOfHom_diag (f : ChartRing k →ₐ[k] S) :
    ((chartPointOfHom f).diagonal : S) = f (algebraMap (QuadricRing k PairIndex) _
      (quadricScalar k PairIndex)) := IsUnit.unit_spec _

private noncomputable def chartPointHom (p : ChartPoint S) : ChartRing k →ₐ[k] S := by
  let z := chartVariables (p.diagonal : S) p.nextBlock p.prevBlock
  have hq : quadricValue z = 0 := by
    rw [quadricValue_chart, (chartVariables_block _ _ _).1, (chartVariables_block _ _ _).2]
    exact p.equation
  let f : QuadricRing k PairIndex →ₐ[k] S := quadricPointHom z hq
  have ha : IsUnit (f (quadricScalar k PairIndex)) := by
    change IsUnit (quadricOfHom k PairIndex f none)
    rw [quadricPointHom_var]
    exact p.diagonal.isUnit
  exact IsLocalization.Away.liftAlgHom (quadricScalar k PairIndex) ha

private lemma chartPointHom_var (p : ChartPoint S) (j : QuadricIndex PairIndex) :
    chartPointHom (k := k) p (algebraMap (QuadricRing k PairIndex) _
      (Ideal.Quotient.mk _ (X j))) =
    chartVariables (p.diagonal : S) p.nextBlock p.prevBlock j :=
  (liftAlgHom_eval _ _ _ _).trans (MvPolynomial.aeval_X _ _)

private lemma chartPointHom_left (p : ChartPoint S) :
    chartPointOfHom (chartPointHom (k := k) p) = p := by
  have hz : quadricOfHom k PairIndex
        ((chartPointHom (k := k) p).comp (Algebra.algHom k (QuadricRing k PairIndex) _)) =
      chartVariables (p.diagonal : S) p.nextBlock p.prevBlock :=
    funext (chartPointHom_var p)
  have ha : (chartPointOfHom (chartPointHom (k := k) p)).diagonal = p.diagonal := by
    apply Units.ext
    exact (chartPointOfHom_diag _).trans (chartPointHom_var p none)
  have hc : (chartPointOfHom (chartPointHom (k := k) p)).nextBlock = p.nextBlock := by
    change chartOctonion _ false = _
    rw [hz, (chartVariables_block _ _ _).1]
  have hd : (chartPointOfHom (chartPointHom (k := k) p)).prevBlock = p.prevBlock := by
    change chartOctonion _ true = _
    rw [hz, (chartVariables_block _ _ _).2]
  cases h : chartPointOfHom (chartPointHom (k := k) p)
  cases p
  simp only [h] at ha hc hd
  congr

private lemma chartPointHom_right (f : ChartRing k →ₐ[k] S) :
    chartPointHom (chartPointOfHom f) = f := by
  apply IsLocalization.algHom_ext (Submonoid.powers (quadricScalar k PairIndex))
  apply quotientHom_ext
  intro j
  change chartPointHom _ (algebraMap (QuadricRing k PairIndex) _
    (Ideal.Quotient.mk _ (X j))) = f (algebraMap (QuadricRing k PairIndex) _
    (Ideal.Quotient.mk _ (X j)))
  rw [chartPointHom_var, chartPointOfHom_diag]
  exact congrFun (chartVariables_inverse (quadricOfHom k PairIndex
    (f.comp (Algebra.algHom k (QuadricRing k PairIndex) _)))) j

private noncomputable def chartCoordinatesPoint (i : Fin 3) (p : ChartPoint S) :
    IdempotentPoint S :=
  ⟨chartCoordinates i p.diagonal p.nextBlock p.prevBlock,
    (chart_trace_iff _ _ _ _).mpr p.equation, chart_adjoint_zero _ _ _ _⟩

private noncomputable def openPointHom (i : Fin 3) (x : IdempotentPoint S)
    (hx : IsUnit (x.val.1 i)) : Localization.Away (diagonalCoordinate k i) →ₐ[k] S := by
  let f := firstPointHom (k := k) x
  have hu : IsUnit (f (diagonalCoordinate k i)) := by
    rw [diagonalCoordinate, firstPointHom_var]
    exact hx
  exact IsLocalization.Away.liftAlgHom (diagonalCoordinate k i) hu

private lemma openPointHom_eval (i : Fin 3) (x : IdempotentPoint S)
    (hx : IsUnit (x.val.1 i)) (j : CoordinateIndex) :
    openPointHom (k := k) i x hx (algebraMap (IdempotentRing k) _
      (Ideal.Quotient.mk _ (X j))) = modelVariables x.val j :=
  (liftAlgHom_eval _ _ _ _).trans (firstPointHom_var x j)

private lemma openPointHom_left (i : Fin 3) (x : IdempotentPoint S)
    (hx : IsUnit (x.val.1 i)) :
    openPoint i (openPointHom (k := k) i x hx) = x := by
  apply Subtype.ext
  change modelOfVariables (fun j => openPointHom (k := k) i x hx
    (algebraMap (IdempotentRing k) _ (Ideal.Quotient.mk _ (X j)))) = x.val
  simp only [openPointHom_eval, modelOfVariables_inverse]

private lemma openPoint_injective (i : Fin 3) :
    Function.Injective (openPoint (k := k) (S := S) i) := by
  intro f g h
  apply IsLocalization.algHom_ext (Submonoid.powers (diagonalCoordinate k i))
  apply quotientHom_ext
  intro j
  let z (a : Localization.Away (diagonalCoordinate k i) →ₐ[k] S) (t : CoordinateIndex) :=
    a (algebraMap (IdempotentRing k) _ (Ideal.Quotient.mk _ (X t)))
  have he : modelVariables (modelOfVariables (z f)) j = modelVariables (modelOfVariables (z g)) j :=
    congrArg (fun x : IdempotentPoint S => modelVariables x.val j) h
  change z f j = z g j
  rw [modelVariables_inverse, modelVariables_inverse] at he
  exact he

private noncomputable def chartPointFromOpen (i : Fin 3) (x : IdempotentPoint S)
    (hu : IsUnit (x.val.1 i)) : ChartPoint S :=
  ⟨hu.unit, x.val.2 (cyclicNext i), x.val.2 (cyclicPrev i),
    ((chartEquations S i hu.unit x.val hu.unit_spec.symm).mp x.property).2⟩

private lemma reconstruct_openPoint (i : Fin 3) (x : IdempotentPoint S)
    (hu : IsUnit (x.val.1 i)) :
    chartCoordinatesPoint i (chartPointFromOpen i x hu) = x :=
  Subtype.ext (reconstruct_of_adjoint hu.unit_spec.symm x.property.2).symm

private lemma openPoint_comp {T : Type w} [CommRing T] [Algebra k T] (i : Fin 3)
    (f : Localization.Away (diagonalCoordinate k i) →ₐ[k] S) (g : S →ₐ[k] T) :
    (openPoint i (g.comp f)).val = mapModel g.toRingHom (openPoint i f).val := by
  let z (j : CoordinateIndex) := f (algebraMap (IdempotentRing k) _
    (Ideal.Quotient.mk _ (X j)))
  change modelOfVariables (g.toRingHom ∘ z) = mapModel g.toRingHom (modelOfVariables z)
  exact modelOfVariables_map _ _

private lemma chartCoordinates_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (i : Fin 3) (a : Aˣ) (c d : Zorn A) :
    mapModel f (chartCoordinates i a c d) =
      chartCoordinates i (Units.map f.toMonoidHom a)
        (Composition.ZornSpecification.mapCoordinates f c)
        (Composition.ZornSpecification.mapCoordinates f d) := by
  apply Prod.ext <;> funext j
  · change f ((chartCoordinates i a c d).1 j) = _
    rcases cyclic_cases i j with rfl | rfl | rfl <;>
      simp only [chart_diag_here, chart_diag_next, chart_diag_prev, map_mul,
        Zorn.mapCoordinates_norm, Units.coe_map, ← map_inv]
    all_goals rfl
  · change Composition.ZornSpecification.mapCoordinates f ((chartCoordinates i a c d).2 j) = _
    rcases cyclic_cases i j with rfl | rfl | rfl <;>
      simp only [chart_block_here, chart_block_next, chart_block_prev,
        zorn_map_smul, zorn_map_conjugate, Zorn.mapCoordinates_mul]
    rfl

private lemma chartOctonion_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (z : QuadricIndex PairIndex → A) (b : Bool) :
    chartOctonion (f ∘ z) b =
      Composition.ZornSpecification.mapCoordinates f (chartOctonion z b) := by
  apply (Zorn.pairedFunctions B).injective
  funext j
  let p (j : Option (Fin 3) × Bool) := z (some ((b, j.1), j.2))
  rcases j with j | j
  · change Zorn.pairedFunctions B (octonionOfPairs (f ∘ p)) (.inl j) =
      Zorn.pairedFunctions B (Composition.ZornSpecification.mapCoordinates f (octonionOfPairs p)) (.inl j)
    rw [(octonionOfPairs_apply (f ∘ p) j).1, pairedFunctions_map, (octonionOfPairs_apply p j).1]
    rfl
  · change Zorn.pairedFunctions B (octonionOfPairs (f ∘ p)) (.inr j) =
      Zorn.pairedFunctions B (Composition.ZornSpecification.mapCoordinates f (octonionOfPairs p)) (.inr j)
    rw [(octonionOfPairs_apply (f ∘ p) j).2, pairedFunctions_map, (octonionOfPairs_apply p j).2]
    rfl

private lemma chart_coordinates_comp {T : Type w} [CommRing T] [Algebra k T]
    (i : Fin 3) (f : ChartRing k →ₐ[k] S) (g : S →ₐ[k] T) :
    (chartCoordinatesPoint i (chartPointOfHom (g.comp f))).val =
      mapModel g.toRingHom (chartCoordinatesPoint i (chartPointOfHom f)).val := by
  let z := quadricOfHom k PairIndex (f.comp (Algebra.algHom k (QuadricRing k PairIndex) _))
  have ha : (chartPointOfHom (g.comp f)).diagonal =
      Units.map g.toRingHom.toMonoidHom (chartPointOfHom f).diagonal := by
    apply Units.ext
    rw [chartPointOfHom_diag]
    change g (f (algebraMap (QuadricRing k PairIndex) _ (quadricScalar k PairIndex))) =
      g ((chartPointOfHom f).diagonal : S)
    rw [chartPointOfHom_diag]
  have hc : (chartPointOfHom (g.comp f)).nextBlock =
      Composition.ZornSpecification.mapCoordinates g.toRingHom (chartPointOfHom f).nextBlock :=
    chartOctonion_map g.toRingHom z false
  have hd : (chartPointOfHom (g.comp f)).prevBlock =
      Composition.ZornSpecification.mapCoordinates g.toRingHom (chartPointOfHom f).prevBlock :=
    chartOctonion_map g.toRingHom z true
  simp only [chartCoordinatesPoint, chartCoordinates_map, ha, hc, hd]

private lemma chartCoordinatesPoint_injective (i : Fin 3) :
    Function.Injective (chartCoordinatesPoint (S := S) i) := by
  intro p q h
  have hd := congrArg (fun x : IdempotentPoint S => x.val.1 i) h
  have hc := congrArg (fun x : IdempotentPoint S => x.val.2 (cyclicNext i)) h
  have he := congrArg (fun x : IdempotentPoint S => x.val.2 (cyclicPrev i)) h
  change (chartCoordinates i p.diagonal p.nextBlock p.prevBlock).1 i = _ at hd
  change (chartCoordinates i p.diagonal p.nextBlock p.prevBlock).2 (cyclicNext i) = _ at hc
  change (chartCoordinates i p.diagonal p.nextBlock p.prevBlock).2 (cyclicPrev i) = _ at he
  simp only [chartCoordinatesPoint, chart_diag_here] at hd
  simp only [chartCoordinatesPoint, chart_block_next] at hc
  simp only [chartCoordinatesPoint, chart_block_prev] at he
  have hu := Units.ext hd
  cases p
  cases q
  congr

theorem chartRings : ChartRingsType.{u} := by
  intro k _ i
  let L := Localization.Away (diagonalCoordinate k i)
  let C := ChartRing k
  let p := chartPointOfHom (AlgHom.id k C)
  let x := chartCoordinatesPoint i p
  let f : L →ₐ[k] C := openPointHom i x (by
    change IsUnit ((chartCoordinates i p.diagonal p.nextBlock p.prevBlock).1 i)
    rw [chart_diag_here]
    exact p.diagonal.isUnit)
  let q := chartPointFromOpen i (openPoint i (AlgHom.id k L)) (openPoint_unit i _)
  let g : C →ₐ[k] L := chartPointHom q
  have hf : openPoint i f = x := openPointHom_left _ _ _
  have hg : chartCoordinatesPoint i (chartPointOfHom g) = openPoint i (AlgHom.id k L) := by
    change chartCoordinatesPoint i (chartPointOfHom (chartPointHom q)) = _
    rw [chartPointHom_left]
    exact reconstruct_openPoint _ _ _
  refine ⟨AlgEquiv.ofAlgHom f g ?_ ?_⟩
  · apply Function.LeftInverse.injective (fun y => chartPointHom_right (k := k) y)
    apply chartCoordinatesPoint_injective (i := i)
    apply Subtype.ext
    rw [chart_coordinates_comp, hg]
    exact (openPoint_comp i (AlgHom.id k L) f).symm.trans (congrArg Subtype.val hf)
  · apply openPoint_injective i
    apply Subtype.ext
    rw [openPoint_comp, hf]
    exact (chart_coordinates_comp i (AlgHom.id k C) g).symm.trans
      (congrArg Subtype.val hg)

end ChartRings

section QuadricGeometry

open MvPolynomial AlgebraicGeometry
open scoped Polynomial

variable {k : Type u} [Field k] {ι : Type w} [Fintype ι]

open private irreducible_linear from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.PeirceFrames

private noncomputable def quadricRest (k : Type u) [CommRing k] (ι : Type w) [Fintype ι] [DecidableEq ι]
    (j : ι) : MvPolynomial (ι × Bool) k := by
  exact X (j, true) ^ 2 - X (j, true) +
    ∑ l ∈ Finset.univ.erase j, X (l, false) * X (l, true)

set_option maxHeartbeats 700000 in
private lemma quadricEquation_swap [DecidableEq ι] (j : ι) :
    let P := (MvPolynomial.renameEquiv k (Equiv.swap (none : QuadricIndex ι) (some (j, true)))).trans
      (MvPolynomial.optionEquivLeft k (ι × Bool))
    P (quadricEquation k ι) =
      Polynomial.C (X (j, false)) * Polynomial.X + Polynomial.C (quadricRest k ι j) := by
  classical
  let e := Equiv.swap (none : QuadricIndex ι) (some (j, true))
  let P := (MvPolynomial.renameEquiv k e).trans (MvPolynomial.optionEquivLeft k (ι × Bool))
  change P (quadricEquation k ι) = _
  have hn : P (X none) = Polynomial.C (X (j, true)) := by simp [P, e]
  have hj : P (X (some (j, true))) = Polynomial.X := by simp [P, e]
  have hfalse (l : ι) : P (X (some (l, false))) = Polynomial.C (X (l, false)) := by
    have h : (some (l, false) : QuadricIndex ι) ≠ some (j, true) := by simp
    simp [P, e, Equiv.swap_apply_of_ne_of_ne (by simp : (some (l, false) : QuadricIndex ι) ≠ none) h]
  have htrue (l : ι) (hl : l ≠ j) :
      P (X (some (l, true))) = Polynomial.C (X (l, true)) := by
    have h : (some (l, true) : QuadricIndex ι) ≠ some (j, true) := by simp [hl]
    simp [P, e, Equiv.swap_apply_of_ne_of_ne (by simp : (some (l, true) : QuadricIndex ι) ≠ none) h]
  rw [quadricEquation, map_add, map_sub, map_pow, hn, map_sum]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  simp only [map_mul, hfalse, hj, quadricRest, map_add, map_sub, map_pow, map_sum]
  have hsum :
      (∑ l ∈ Finset.univ.erase j, Polynomial.C (X (l, false)) * P (X (some (l, true)))) =
        ∑ l ∈ Finset.univ.erase j, Polynomial.C (X (l, false)) * Polynomial.C (X (l, true)) :=
    Finset.sum_congr rfl (fun l hl => by rw [htrue l (Finset.ne_of_mem_erase hl)])
  rw [hsum]
  ac_rfl

private lemma quadric_domain (k : Type u) [Field k] (ι : Type w) [Fintype ι] [Nonempty ι] :
    IsDomain (QuadricRing k ι) := by
  classical
  let j : ι := Classical.choice ‹Nonempty ι›
  let E := (MvPolynomial.renameEquiv k (Equiv.swap (none : QuadricIndex ι) (some (j, true)))).trans
    (MvPolynomial.optionEquivLeft k (ι × Bool))
  have hn : ¬ (X (j, false) : MvPolynomial (ι × Bool) k) ∣ quadricRest k ι j := by
    rintro ⟨p, hp⟩
    let ev : MvPolynomial (ι × Bool) k →ₐ[k] k[X] :=
      MvPolynomial.aeval (fun l : ι × Bool => if l = (j, true) then Polynomial.X else 0)
    have h := congrArg ev hp
    have hsum : (∑ l ∈ Finset.univ.erase j,
        ev (X (l, false)) * ev (X (l, true))) = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      simp [ev]
    simp only [quadricRest, map_add, map_sub, map_pow, map_sum, map_mul, hsum, add_zero] at h
    have hT : ev (X (j, true)) = Polynomial.X := by simp [ev]
    have hF : ev (X (j, false)) = 0 := by simp [ev]
    rw [hT, hF, zero_mul] at h
    have he := congrArg (fun p : k[X] => p.coeff 2) h
    simpa [Polynomial.coeff_X_pow, Polynomial.coeff_X] using he
  have hi := irreducible_linear (MvPolynomial.X_prime (R := k) (i := (j, false))) hn
  have hp : Prime (quadricEquation k ι) := by
    rw [← MulEquiv.prime_iff E.toMulEquiv]
    change Prime (E (quadricEquation k ι))
    rw [quadricEquation_swap (k := k) j]
    exact UniqueFactorizationMonoid.irreducible_iff_prime.mp hi
  letI : (Ideal.span {quadricEquation k ι}).IsPrime := Ideal.isPrime_span_singleton_of_prime hp
  exact inferInstance

private noncomputable def quadricMonic (k : Type u) [CommRing k] (ι : Type w) [Fintype ι] :
    (MvPolynomial (ι × Bool) k)[X] :=
  Polynomial.X ^ 2 - Polynomial.X + Polynomial.C
    (∑ j : ι, X (j, false) * X (j, true))

private lemma quadricEquation_monic :
    MvPolynomial.optionEquivLeft k (ι × Bool) (quadricEquation k ι) = quadricMonic k ι := by
  simp [quadricEquation, quadricMonic, map_sum]

private lemma quadric_monic : (quadricMonic k ι).Monic := by
  unfold quadricMonic
  rw [sub_eq_add_neg, add_assoc]
  apply Polynomial.monic_X_pow_add
  refine (Polynomial.degree_add_le _ _).trans_lt ?_
  rw [max_lt_iff, Polynomial.degree_neg, Polynomial.degree_X]
  exact ⟨by decide, Polynomial.degree_C_le.trans_lt (by decide)⟩

private lemma quadric_degree_pos : 0 < (quadricMonic k ι).degree := by
  have h : (quadricMonic k ι).coeff 2 = 1 := by
    simp [quadricMonic, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  exact lt_of_lt_of_le (by decide : (0 : WithBot ℕ) < 2)
    (Polynomial.le_degree_of_ne_zero (h ▸ one_ne_zero))

private noncomputable def quadricAdjoinRoot :
    QuadricRing k ι ≃ₐ[k] AdjoinRoot (quadricMonic k ι) :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.optionEquivLeft k (ι × Bool))
    (by
      rw [Ideal.map_span, Set.image_singleton]
      change Ideal.span {quadricMonic k ι} = Ideal.span
        {MvPolynomial.optionEquivLeft k (ι × Bool) (quadricEquation k ι)}
      rw [quadricEquation_monic])

private lemma quadric_dimension :
    ringKrullDim (QuadricRing k ι) = (Fintype.card (ι × Bool) : ℕ) := by
  let P := MvPolynomial (ι × Bool) k
  let A := AdjoinRoot (quadricMonic k ι)
  letI : Algebra.IsIntegral P A := AdjoinRoot.isIntegral_of_monic quadric_monic
  have hi : Function.Injective (algebraMap P A) :=
    AdjoinRoot.of.injective_of_monic_of_degree_pos quadric_monic quadric_degree_pos
  letI : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hi
  have hd : ringKrullDim P = (Fintype.card (ι × Bool) : ℕ) := by
    simp [P, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card]
  rw [ringKrullDim_eq_of_ringEquiv (quadricAdjoinRoot (k := k) (ι := ι)).toRingEquiv]
  change ringKrullDim A = _
  apply le_antisymm
  · rw [← hd]
    exact Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap P A))
      (fun _ _ h => Ideal.IsIntegral.under_lt_under h)
  · obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp (le_of_eq hd.symm)
    obtain ⟨Q, hQ, hQover⟩ := (inferInstance : Nonempty (Ideal.primesOver l.head.asIdeal A))
    obtain ⟨L, hL, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q
    exact Order.le_krullDim_iff.mpr ⟨L, hL.trans hl⟩

theorem secondGeometry : SecondGeometryType.{u} := by
  intro k _ _
  letI : IsDomain (SecondRing k) := quadric_domain k (Option (Fin 3))
  refine ⟨(HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr (quadric_smooth k (Option (Fin 3)))), ?_, ?_⟩
  · change IrreducibleSpace (PrimeSpectrum (SecondRing k))
    infer_instance
  · exact quadric_dimension

end QuadricGeometry

section FirstGeometry

open AlgebraicGeometry CategoryTheory MvPolynomial

private lemma localization_dimension_le {A : Type*} [CommRing A] (a : A) :
    ringKrullDim (Localization.Away a) ≤ ringKrullDim A := by
  let e := IsLocalization.primeSpectrumOrderIso (Submonoid.powers a) (Localization.Away a)
  exact Order.krullDim_le_of_strictMono (fun p => (e p).val) e.strictMono

private lemma dimension_le_of_cover {A : Type*} [CommRing A] {I : Type*}
    {f : I → A} {d : WithBot ℕ∞}
    (hc : (⨆ i, PrimeSpectrum.basicOpen (f i)) = ⊤)
    (h : ∀ i, ringKrullDim (Localization.Away (f i)) ≤ d) :
    ringKrullDim A ≤ d := by
  rw [ringKrullDim, Order.krullDim_eq_iSup_height, iSup_le_iff]
  intro p
  have hp : p ∈ ⨆ i, PrimeSpectrum.basicOpen (f i) := hc.symm ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  let e := IsLocalization.primeSpectrumOrderIso (Submonoid.powers (f i)) (Localization.Away (f i))
  have hq (q : Set.Iic p) : Disjoint (↑(Submonoid.powers (f i)) : Set A) q.val.asIdeal := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hi (p.isPrime.mem_of_pow_mem n (q.property hn))
  let F (q : Set.Iic p) := e.symm ⟨q.val, hq q⟩
  have hm : StrictMono F := fun _ _ hlt => e.symm.strictMono hlt
  rw [Order.height_eq_krullDim_Iic]
  exact (Order.krullDim_le_of_strictMono F hm).trans (h i)

private lemma localizations_equiv_of_algEquiv {k A B : Type u} [CommRing k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B) (a : A) :
    Nonempty (Localization.Away a ≃ₐ[k] Localization.Away (e a)) := by
  letI : IsLocalization.Away (e.toAlgHom a) (Localization.Away (e a)) :=
    inferInstanceAs (IsLocalization.Away (e a) (Localization.Away (e a)))
  let f := IsLocalization.Away.mapₐ (Localization.Away a) (Localization.Away (e a))
    e.toAlgHom a
  refine ⟨AlgEquiv.ofBijective f ⟨?_, ?_⟩⟩
  · exact IsLocalization.Away.mapₐ_injective_of_injective (f := e.toAlgHom) a e.injective
  · exact IsLocalization.Away.mapₐ_surjective_of_surjective (f := e.toAlgHom) a e.surjective

private noncomputable def reflectQuadric {k : Type u} [CommRing k] {ι : Type} [Fintype ι] :
    QuadricRing k ι ≃ₐ[k] QuadricRing k ι := by
  let Q := QuadricRing k ι
  let z := quadricOfHom k ι (AlgHom.id k Q)
  let z' : QuadricIndex ι → Q
    | none => 1 - z none
    | some j => z (some j)
  have h : quadricValue z' = 0 := by
    have hq := quadricOfHom_equation (AlgHom.id k Q)
    change quadricValue z = 0 at hq
    unfold quadricValue at hq ⊢
    change (1 - z none)^2 - (1 - z none) +
      (∑ j : ι, z (some (j, false)) * z (some (j, true))) = 0
    linear_combination hq
  let f : Q →ₐ[k] Q := quadricPointHom z' h
  have hf (j : QuadricIndex ι) : f (Ideal.Quotient.mk _ (X j)) = z' j :=
    quadricPointHom_var z' h j
  have hff : f.comp f = AlgHom.id k Q := by
    apply quotientHom_ext
    intro j
    change f (f (Ideal.Quotient.mk _ (X j))) = z j
    cases j
    · rw [hf]
      change f (1 - (Ideal.Quotient.mk _ (X none))) = z none
      rw [map_sub, map_one, hf]
      change 1 - (1 - z none) = z none
      ring
    · rw [hf]
      exact hf _
  exact AlgEquiv.ofAlgHom f f hff hff

private lemma reflectQuadric_scalar {k : Type u} [CommRing k] {ι : Type} [Fintype ι] :
    (reflectQuadric (k := k)) (quadricScalar k ι) = 1 - quadricScalar k ι := by
  unfold reflectQuadric
  rw [AlgEquiv.ofAlgHom_apply]
  exact MvPolynomial.aeval_X _ _

private lemma chartRing_dimension (k : Type u) [Field k] :
    ringKrullDim (ChartRing k) = 16 := by
  let Q := QuadricRing k PairIndex
  let a := quadricScalar k PairIndex
  let f : Bool → Q
    | false => a
    | true => 1 - a
  have hd : ringKrullDim Q = 16 := quadric_dimension
  have he : ringKrullDim (Localization.Away (1 - a)) = ringKrullDim (ChartRing k) := by
    obtain ⟨e⟩ := localizations_equiv_of_algEquiv (reflectQuadric (k := k) (ι := PairIndex)) a
    have hh := ringKrullDim_eq_of_ringEquiv e.toRingEquiv
    rw [show reflectQuadric a = 1 - a from reflectQuadric_scalar] at hh
    exact hh.symm
  have hcover : (⨆ i, PrimeSpectrum.basicOpen (f i)) = ⊤ := by
    apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr
    let I := Ideal.span (Set.range f)
    have h₁ : a ∈ I := Ideal.subset_span ⟨false, rfl⟩
    have h₂ : 1 - a ∈ I := Ideal.subset_span ⟨true, rfl⟩
    apply I.eq_top_iff_one.mpr
    simpa using I.add_mem h₂ h₁
  change ringKrullDim (Localization.Away a) = 16
  apply le_antisymm
  · exact (localization_dimension_le a).trans hd.le
  · rw [← hd]
    apply dimension_le_of_cover hcover
    intro i
    cases i
    · exact le_rfl
    · exact he.le

private lemma chartRing_domain (k : Type u) [Field k] : IsDomain (ChartRing k) := by
  letI : IsDomain (QuadricRing k PairIndex) := quadric_domain k PairIndex
  apply Localization.Away.isDomain
  intro h
  let z : QuadricIndex PairIndex → k := fun j => if j = none then 1 else 0
  have hz : quadricValue z = 0 := by simp [quadricValue, z]
  have hf := quadricPointHom_var (k := k) z hz none
  change (quadricPointHom z hz) (quadricScalar k PairIndex) = 1 at hf
  rw [h, map_zero] at hf
  exact zero_ne_one hf

private lemma chartRing_smooth (k : Type u) [CommRing k] : Algebra.Smooth k (ChartRing k) := by
  let Q := QuadricRing k PairIndex
  letI : Algebra.Smooth k Q := quadric_smooth k PairIndex
  letI : Algebra.Smooth Q (ChartRing k) := Algebra.Smooth.of_isLocalization_Away
    (quadricScalar k PairIndex)
  exact Algebra.Smooth.comp k Q (ChartRing k)

private lemma first_smooth (k : Type u) [CommRing k] : Smooth (firstStructure k) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  apply RingHom.Smooth.ofLocalizationSpanTarget (algebraMap k (IdempotentRing k))
    (Set.range (diagonalCoordinate k)) (PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp (chartCover k))
  rintro ⟨_, i, rfl⟩
  obtain ⟨e⟩ := chartRings k i
  letI : Algebra.Smooth k (ChartRing k) := chartRing_smooth k
  have hh : Algebra.Smooth k (Localization.Away (diagonalCoordinate k i)) :=
    Algebra.Smooth.of_equiv e.symm
  have h := RingHom.smooth_algebraMap.mpr hh
  rwa [IsScalarTower.algebraMap_eq k (IdempotentRing k)] at h

private lemma chart_irreducible (k : Type u) [Field k] (i : Fin 3) :
    IsIrreducible (PrimeSpectrum.basicOpen (diagonalCoordinate k i) :
      Set (PrimeSpectrum (IdempotentRing k))) := by
  obtain ⟨e⟩ := chartRings k i
  letI : IsDomain (ChartRing k) := chartRing_domain k
  letI : IsDomain (Localization.Away (diagonalCoordinate k i)) :=
    Function.Injective.isDomain e.toRingHom e.injective
  rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away (diagonalCoordinate k i))]
  rw [← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ (PrimeSpectrum.continuous_comap _).continuousOn

private lemma chart_intersection (k : Type u) [Field k] [IsAlgClosed k] (i j : Fin 3) :
    ((PrimeSpectrum.basicOpen (diagonalCoordinate k i) :
      Set (PrimeSpectrum (IdempotentRing k))) ∩
      (PrimeSpectrum.basicOpen (diagonalCoordinate k j) :
        Set (PrimeSpectrum (IdempotentRing k)))).Nonempty := by
  have exists_one (x : IdempotentPoint k) (hi : x.val.1 i ≠ 0) (hj : x.val.1 j ≠ 0) :
      ((PrimeSpectrum.basicOpen (diagonalCoordinate k i) :
        Set (PrimeSpectrum (IdempotentRing k))) ∩
        (PrimeSpectrum.basicOpen (diagonalCoordinate k j) :
          Set (PrimeSpectrum (IdempotentRing k)))).Nonempty := by
    let f := firstPointHom (k := k) x
    let p : PrimeSpectrum (IdempotentRing k) := ⟨RingHom.ker f.toRingHom, RingHom.ker_isPrime _⟩
    refine ⟨p, (PrimeSpectrum.mem_basicOpen _ _).mpr ?_,
      (PrimeSpectrum.mem_basicOpen _ _).mpr ?_⟩
    · change f (diagonalCoordinate k i) ≠ 0
      exact (firstPointHom_var (k := k) x (.inl i)).symm ▸ hi
    · change f (diagonalCoordinate k j) ≠ 0
      exact (firstPointHom_var (k := k) x (.inl j)).symm ▸ hj
  have exists_a : ∃ a : k, a ≠ 0 ∧ a ≠ 1 := by
    classical
    obtain ⟨a, -, ha⟩ := Set.infinite_univ.exists_notMem_finset ({0, 1} : Finset k)
    exact ⟨a, by simpa using ha⟩
  obtain ⟨a, ha, ha1⟩ := exists_a
  let aU : kˣ := Units.mk0 a ha
  let n := a * (1 - a)
  let z : Zorn k := Zorn.ofCoordinates (n, 0, 0, 1)
  have hz : norm k z = n := by
    rw [Zorn.norm_formula]
    simp [z, Composition.Specification.zornNorm]
  have hq : (aU : k)^2 - (aU : k) + norm k 0 + norm k z = 0 := by
    rw [QuadraticMap.map_zero, hz]
    change a^2 - a + 0 + a * (1 - a) = 0
    ring
  have hn : (↑aU⁻¹ : k) * norm k z ≠ 0 := by
    rw [hz]
    exact mul_ne_zero (Units.ne_zero _) (mul_ne_zero ha (sub_ne_zero.mpr (Ne.symm ha1)))
  rcases cyclic_cases i j with h | rfl | rfl
  · subst j
    let x := chartCoordinatesPoint i (⟨aU, 0, z, hq⟩ : ChartPoint k)
    have hx : x.val.1 i ≠ 0 := (chart_diag_here i aU 0 z).symm ▸ ha
    exact exists_one x hx hx
  · let x := chartCoordinatesPoint i (⟨aU, 0, z, hq⟩ : ChartPoint k)
    exact exists_one x ((chart_diag_here i aU 0 z).symm ▸ ha)
      ((chart_diag_next i aU 0 z).symm ▸ hn)
  · have hq' : (aU : k)^2 - (aU : k) + norm k z + norm k 0 = 0 := by
      simpa only [add_assoc, add_comm (norm k 0) (norm k z)] using hq
    let x := chartCoordinatesPoint i (⟨aU, z, 0, hq'⟩ : ChartPoint k)
    exact exists_one x ((chart_diag_here i aU z 0).symm ▸ ha)
      ((chart_diag_prev i aU z 0).symm ▸ hn)

private lemma first_irreducible (k : Type u) [Field k] [IsAlgClosed k] :
    IrreducibleSpace (firstScheme k) := by
  change IrreducibleSpace (PrimeSpectrum (IdempotentRing k))
  let U (i : Fin 3) := (PrimeSpectrum.basicOpen (diagonalCoordinate k i) :
    Set (PrimeSpectrum (IdempotentRing k)))
  have hc (p : PrimeSpectrum (IdempotentRing k)) : ∃ i, p ∈ U i := by
    apply TopologicalSpace.Opens.mem_iSup.mp
    rw [chartCover]
    trivial
  have hi (i) : IsIrreducible (U i) := chart_irreducible k i
  have ho (i) : IsOpen (U i) := PrimeSpectrum.isOpen_basicOpen
  have hn (i j) : (U i ∩ U j).Nonempty := chart_intersection k i j
  apply (irreducibleSpace_def _).mpr
  refine ⟨(hi 0).nonempty.mono (Set.subset_univ _), ?_⟩
  rintro A B hA hB ⟨x, -, hx⟩ ⟨y, -, hy⟩
  obtain ⟨i, hxi⟩ := hc x
  obtain ⟨j, hyj⟩ := hc y
  obtain ⟨z, _, hzA, hzj⟩ := (hi i).isPreirreducible A (U j) hA (ho j) ⟨x, hxi, hx⟩ (hn i j)
  obtain ⟨w, _, hwA, hwB⟩ := (hi j).isPreirreducible A B hA hB ⟨z, hzj, hzA⟩ ⟨y, hyj, hy⟩
  exact ⟨w, trivial, hwA, hwB⟩

theorem firstGeometry : FirstGeometryType.{u} := by
  intro k _ _
  refine ⟨first_smooth k, first_irreducible k, ?_⟩
  have h (i : Fin 3) : ringKrullDim (Localization.Away (diagonalCoordinate k i)) = 16 := by
    obtain ⟨e⟩ := chartRings k i
    exact (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).trans (chartRing_dimension k)
  exact le_antisymm (dimension_le_of_cover (chartCover k) fun i => (h i).le)
    ((h 0).symm.le.trans (localization_dimension_le (diagonalCoordinate k 0)))

end FirstGeometry

section OrbitValues

open _root_.Specs.LinearAlgebraicGroups.Albert (QuadraticJordan)
open SplitSpecification (ParaQuadratic)
open IntrinsicCubicSpecification (Coefficients)
open scoped TensorProduct

open private splitChart_ground from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.ShortDirections
open private preserves_coefficients precomposeCoefficients precomposeLaw from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntrinsicCubic

variable {R : Type u} [CommRing R]

private lemma splitAuto_preserves (g : Model R ≃ₗ[R] Model R) (h : IsSplitAutomorphism g) :
    (∀ x, trace (g x) = trace x) ∧ (∀ x, adjoint (g x) = g (adjoint x)) := by
  obtain ⟨J, F, hu, hop, hAlbert, hF, hAgree, _⟩ := Triality.cubicFrameStabilizer R
  let K := ParaQuadratic.ofJordan J
  have he : K.IsGroundIso K g := by
    change g J.unit = J.unit ∧ ∀ x y, g (J.groundOp x y) = J.groundOp (g x) (g y)
    simpa only [hu, hop, IsSplitAutomorphism] using h
  have hiso : K.IsIso K g := (K.isIso_iff_ground K g).mpr he
  have hc := preserves_coefficients hAlbert hF g hiso
  obtain ⟨c, hc'⟩ := splitChart_ground J hu hop
  have c_pure (x : Model R) : c.coordinates (1 ⊗ₜ[R] x) = x := by
    rw [hc', TensorProduct.lid_tmul, one_smul]
  have ht (x : Model R) :
      F.trace.eval R (1 ⊗ₜ[R] x) = trace x := by
    have h := (hAgree R c (1 ⊗ₜ[R] x)).1
    rw [c_pure] at h
    exact h
  have hS (x : Model R) :
      F.quadraticTrace.eval R (1 ⊗ₜ[R] x) =
        CubicSpecification.quadraticTrace (norm R) (fun _ => 1) x := by
    have h := (hAgree R c (1 ⊗ₜ[R] x)).2.1
    rw [c_pure] at h
    exact h
  have t_auto (x : Model R) : trace (g x) = trace x := by
    have hh := congrArg (fun F : Coefficients R (Model R) => F.trace.eval R (1 ⊗ₜ[R] x)) hc
    change F.trace.eval R (g.toLinearMap.baseChange R (1 ⊗ₜ[R] x)) =
      F.trace.eval R (1 ⊗ₜ[R] x) at hh
    rw [LinearMap.baseChange_tmul, ht, ht] at hh
    exact hh
  have s_auto (x : Model R) : CubicSpecification.quadraticTrace (norm R) (fun _ => 1) (g x) =
      CubicSpecification.quadraticTrace (norm R) (fun _ => 1) x := by
    have hh := congrArg (fun F : Coefficients R (Model R) =>
      F.quadraticTrace.eval R (1 ⊗ₜ[R] x)) hc
    change F.quadraticTrace.eval R (g.toLinearMap.baseChange R (1 ⊗ₜ[R] x)) =
      F.quadraticTrace.eval R (1 ⊗ₜ[R] x) at hh
    rw [LinearMap.baseChange_tmul, hS, hS] at hh
    exact hh
  refine ⟨t_auto, fun x => ?_⟩
  have squareFormula (x : Model R) :
      modelOp x cubicUnit = adjoint x + trace x • x -
        CubicSpecification.quadraticTrace (norm R) (fun _ => 1) x • cubicUnit :=
    (cubic_operator_identities (fun _ : Fin 3 => 1) (Zorn.isOctonion R)).2.2.2.2.2.2.2.2.1 x
  have hp := h.2 x cubicUnit
  rw [h.1, squareFormula, squareFormula] at hp
  simp only [map_add, map_sub, map_smul, h.1, t_auto, s_auto] at hp
  have he := congrArg (fun y : Model R => y +
      CubicSpecification.quadraticTrace (norm R) (fun _ => 1) x • cubicUnit) hp
  exact (add_right_cancel (by simpa only [sub_add_cancel] using he)).symm

private lemma auto_idempotent_iff (g : Model R ≃ₗ[R] Model R) (h : IsSplitAutomorphism g)
    (x : Model R) : IsRankOneIdempotent (g x) ↔ IsRankOneIdempotent x := by
  obtain ⟨ht, ha⟩ := splitAuto_preserves g h
  simp only [IsRankOneIdempotent, ht, ha, EmbeddingLike.map_eq_zero_iff]

private lemma auto_frame_iff (g : Model R ≃ₗ[R] Model R) (h : IsSplitAutomorphism g)
    (x y : Model R) : IsFramePair (g x) (g y) ↔ IsFramePair x y := by
  have eq : modelOp (cubicUnit - g x) (g y) = g (modelOp (cubicUnit - x) y) := by
    rw [h.2, map_sub, h.1]
  simp only [IsFramePair, auto_idempotent_iff g h, eq, EmbeddingLike.apply_eq_iff_eq]

theorem orbitValues : OrbitValuesType.{u} := by
  intro R _ g hg
  refine ⟨auto_idempotent_iff g hg, auto_frame_iff g hg, (auto_frame_iff g hg _ _).mpr ?_⟩
  refine ⟨axis_rank_one 0, axis_rank_one 1, ?_⟩
  rw [second_projector]
  apply Prod.ext
  · funext i
    by_cases hi : i = 0
    · subst i
      rfl
    · simp [hi]
  · simp [FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates]

end OrbitValues

section Differentials

open _root_.Specs.LinearAlgebraicGroups.Albert (QuadraticJordan)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (infinitesimal PreservesQuadratic)
open TrialitySpecification (modelBaseChange)
open ShortDirectionSpecification (splitDerivations frameEvaluation)
open scoped TensorProduct DualNumber Matrix

open private modelBaseChange_pure mapModel_axis from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.ShortDirections
open private infinitesimal_apply scalar_eps_tmul from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.AutomorphismScheme

variable {k : Type u} [Field k]

private abbrev Dual := DualNumber k

private def liftOctonion (c : Zorn k) : Zorn (Dual (k := k)) :=
  Composition.ZornSpecification.mapCoordinates (algebraMap k (Dual (k := k))) c

private lemma square_zero_octonion (c : Zorn (Dual (k := k)))
    (h : Composition.ZornSpecification.mapCoordinates
      (TrivSqZeroExt.fstHom k k k).toRingHom c = 0) :
    ∃ d : Zorn k, c = (ε : Dual (k := k)) • liftOctonion d := by
  let d := (Zorn.pairedFunctions k).symm (fun j => (Zorn.pairedFunctions _ c j).snd)
  refine ⟨d, (Zorn.pairedFunctions _).injective ?_⟩
  funext j
  have hz := congrArg (fun z => Zorn.pairedFunctions k z j) h
  rw [pairedFunctions_map, map_zero, Pi.zero_apply] at hz
  change (Zorn.pairedFunctions _ c j).fst = 0 at hz
  simp only [liftOctonion, LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul,
    pairedFunctions_map, d, LinearEquiv.apply_symm_apply]
  apply TrivSqZeroExt.ext
  · exact hz.trans (by simp)
  · simp [TrivSqZeroExt.algebraMap_eq_inl]

private lemma norm_pure_infinitesimal (c : Zorn k) :
    norm (Dual (k := k)) ((ε : Dual (k := k)) • liftOctonion c) = 0 := by
  rw [QuadraticMap.map_smul, DualNumber.eps_mul_eps, zero_smul]

private lemma first_jet_shape (x : IdempotentPoint (DualNumber k))
    (hx : reduceModel k x.val = frameAxis 0) :
    ∃ c d : Zorn k, x.val = frameAxis 0 +
      singleBlockCoordinates 1 ((ε : DualNumber k) • liftOctonion c) +
      singleBlockCoordinates 2 ((ε : DualNumber k) • liftOctonion d) := by
  have hred := congrArg (fun z : Model k => z.1 0) hx
  change (x.val.1 0).fst = 1 at hred
  have hu : IsUnit (x.val.1 0) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (hred.symm ▸ isUnit_one)
  have h1 := congrArg (fun z : Model k => z.2 1) hx
  have h2 := congrArg (fun z : Model k => z.2 2) hx
  change Composition.ZornSpecification.mapCoordinates _ (x.val.2 1) = 0 at h1
  change Composition.ZornSpecification.mapCoordinates _ (x.val.2 2) = 0 at h2
  obtain ⟨c, hc⟩ := square_zero_octonion _ h1
  obtain ⟨d, hd⟩ := square_zero_octonion _ h2
  obtain ⟨h, hq⟩ := (chartEquations (DualNumber k) 0 hu.unit x.val hu.unit_spec.symm).mp x.property
  change (hu.unit : DualNumber k)^2 - (hu.unit : DualNumber k) +
    norm _ (x.val.2 1) + norm _ (x.val.2 2) = 0 at hq
  rw [hc, hd, norm_pure_infinitesimal, norm_pure_infinitesimal, add_zero, add_zero] at hq
  have ha : hu.unit = 1 := by
    apply Units.ext
    change (hu.unit : DualNumber k) = 1
    have hcancel : (hu.unit : DualNumber k) * ((hu.unit : DualNumber k) - 1) =
        (hu.unit : DualNumber k) * 0 := by linear_combination hq
    exact sub_eq_zero.mp ((Units.mul_right_inj hu.unit).mp hcancel)
  change x.val = chartCoordinates 0 hu.unit (x.val.2 1) (x.val.2 2) at h
  refine ⟨c, d, h.trans ?_⟩
  rw [ha, hc, hd]
  have hprod :
      ((ε : DualNumber k) • liftOctonion c) * ((ε : DualNumber k) • liftOctonion d) = 0 := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, DualNumber.eps_mul_eps]
    exact zero_smul (DualNumber k) (liftOctonion c * liftOctonion d)
  apply Prod.ext <;> funext i
  · change (chartCoordinates 0 1 _ _).1 i =
      (Pi.single (M := fun _ : Fin 3 => DualNumber k) 0 1) i + 0 + 0
    rw [add_zero, add_zero]
    rcases cyclic_cases 0 i with rfl | h | h
    · rw [chart_diag_here, Pi.single_eq_same]
      rfl
    · rw [h, chart_diag_next, norm_pure_infinitesimal, mul_zero,
        Pi.single_eq_of_ne (next_ne 0)]
    · rw [h, chart_diag_prev, norm_pure_infinitesimal, mul_zero,
        Pi.single_eq_of_ne (prev_ne 0)]
  · change (chartCoordinates 0 1 _ _).2 i = 0 +
      (Pi.single (M := fun _ : Fin 3 => Zorn (DualNumber k)) 1
        ((ε : DualNumber k) • liftOctonion c)) i +
      (Pi.single (M := fun _ : Fin 3 => Zorn (DualNumber k)) 2
        ((ε : DualNumber k) • liftOctonion d)) i
    rcases cyclic_cases 0 i with rfl | h | h
    · rw [chart_block_here, hprod, map_zero, smul_zero,
        Pi.single_eq_of_ne (by decide : (0 : Fin 3) ≠ 1),
        Pi.single_eq_of_ne (by decide : (0 : Fin 3) ≠ 2), add_zero, add_zero]
    · rw [h, chart_block_next]
      change _ = 0 + (Pi.single (M := fun _ : Fin 3 => Zorn (DualNumber k)) 1 _) 1 +
        (Pi.single (M := fun _ : Fin 3 => Zorn (DualNumber k)) 2 _) 1
      simp only [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (1 : Fin 3) ≠ 2),
        zero_add, add_zero]
    · rw [h, chart_block_prev]
      change _ = 0 + (Pi.single (M := fun _ : Fin 3 => Zorn (DualNumber k)) 1 _) 2 +
        (Pi.single (M := fun _ : Fin 3 => Zorn (DualNumber k)) 2 _) 2
      simp only [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 1), zero_add]

private lemma second_jet_shape
    (x : {x : Model (DualNumber k) // IsFramePair (frameAxis 0) x})
    (hx : reduceModel k x.val = frameAxis 1) :
    ∃ c : Zorn k, x.val = frameAxis 1 +
      singleBlockCoordinates 0 ((ε : DualNumber k) • liftOctonion c) := by
  have hred := congrArg (fun z : Model k => z.1 1) hx
  change (x.val.1 1).fst = 1 at hred
  have hu : IsUnit (x.val.1 1) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (hred.symm ▸ isUnit_one)
  have h0 := congrArg (fun z : Model k => z.2 0) hx
  change Composition.ZornSpecification.mapCoordinates _ (x.val.2 0) = 0 at h0
  obtain ⟨c, hc⟩ := square_zero_octonion _ h0
  obtain ⟨h, he⟩ := (secondEquations (DualNumber k) x.val).mp x.property
  rw [hc, norm_pure_infinitesimal] at he
  have hcancel : (hu.unit : DualNumber k) * (1 - x.val.1 1) = (hu.unit : DualNumber k) * 0 := by
    rw [hu.unit_spec, mul_zero, he]
  have ha : x.val.1 1 = 1 := (sub_eq_zero.mp ((Units.mul_right_inj hu.unit).mp hcancel)).symm
  refine ⟨c, h.trans ?_⟩
  rw [ha, hc]
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [secondCoordinates, FrameSpecification.frameAxis,
      CubicSpecification.diagonalCoordinates, CubicSpecification.singleBlockCoordinates, Pi.single_apply]
  · change (Pi.single (M := fun _ : Fin 3 => Zorn (DualNumber k)) 0 _) = 0 + Pi.single 0 _
    exact (zero_add _).symm

private lemma baseChange_frameAxis (i : Fin 3) :
    modelBaseChange k (DualNumber k) (1 ⊗ₜ[k] (frameAxis i : Model k)) = frameAxis i := by
  rw [modelBaseChange_pure (DualNumber k)]
  exact (one_smul (DualNumber k) _).trans (mapModel_axis (algebraMap k (DualNumber k)) i)

private lemma axisJet_eq (D : Module.End k (Model k)) (i : Fin 3) :
    axisJet D i = frameAxis i + (ε : DualNumber k) •
      TrialitySpecification.mapModel (algebraMap k (DualNumber k)) (D (frameAxis i)) := by
  unfold axisJet
  rw [infinitesimal_apply, LinearMap.baseChange_tmul, scalar_eps_tmul]
  rw [map_add, baseChange_frameAxis, modelBaseChange_pure]

private lemma frameAxis_eval_zero (J : QuadraticJordan k (Model k))
    (hu : J.unit = cubicUnit) (ho : ∀ x y, J.groundOp x y = modelOp x y)
    (D : splitDerivations J) :
    D.val (frameAxis 0) = (0, ![0, -(frameEvaluation k D.val 1), frameEvaluation k D.val 2]) := by
  rw [ShortDirections.frameEvaluationSpec k J hu ho D.val D.property 0]
  refine Prod.ext (show (0 : Fin 3 → k) = 0 from rfl) ?_
  funext i
  fin_cases i <;> rfl

private lemma frameAxis_eval_one (J : QuadraticJordan k (Model k))
    (hu : J.unit = cubicUnit) (ho : ∀ x y, J.groundOp x y = modelOp x y)
    (D : splitDerivations J) :
    D.val (frameAxis 1) = (0, ![frameEvaluation k D.val 0, 0, -(frameEvaluation k D.val 2)]) := by
  rw [ShortDirections.frameEvaluationSpec k J hu ho D.val D.property 1]
  refine Prod.ext (show (0 : Fin 3 → k) = 0 from rfl) ?_
  funext i
  fin_cases i <;> rfl

private lemma zero_map_octonion :
    liftOctonion (0 : Zorn k) = 0 := by
  apply (Zorn.pairedFunctions _).injective
  funext j
  simp only [liftOctonion, pairedFunctions_map, map_zero, Pi.zero_apply]

private lemma firstAxisJet_value (J : QuadraticJordan k (Model k))
    (hu : J.unit = cubicUnit) (ho : ∀ x y, J.groundOp x y = modelOp x y)
    (D : splitDerivations J) (c d : Zorn k)
    (hc : frameEvaluation k D.val 1 = -c) (hd : frameEvaluation k D.val 2 = d) :
    axisJet D.val 0 = frameAxis 0 +
      singleBlockCoordinates 1 ((ε : DualNumber k) • liftOctonion c) +
      singleBlockCoordinates 2 ((ε : DualNumber k) • liftOctonion d) := by
  rw [axisJet_eq, frameAxis_eval_zero _ hu ho, hc, hd, neg_neg]
  apply Prod.ext <;> funext j
  · change (Pi.single (M := fun _ : Fin 3 => DualNumber k) 0 1) j + ε * algebraMap k (DualNumber k) 0 =
      (Pi.single (M := fun _ : Fin 3 => DualNumber k) 0 1) j + 0 + 0
    simp
  · change 0 + ((ε : DualNumber k) • liftOctonion (![0, c, d] j)) =
      0 + (Pi.single (M := fun _ : Fin 3 => Zorn (DualNumber k)) 1
        ((ε : DualNumber k) • liftOctonion c)) j +
      (Pi.single (M := fun _ : Fin 3 => Zorn (DualNumber k)) 2
        ((ε : DualNumber k) • liftOctonion d)) j
    simp only [zero_add]
    fin_cases j
    · change (ε : DualNumber k) • liftOctonion 0 = (0 : Zorn (DualNumber k)) + 0
      simp [zero_map_octonion]
    · change (ε : DualNumber k) • liftOctonion c = (ε : DualNumber k) • liftOctonion c + 0
      simp
    · change (ε : DualNumber k) • liftOctonion d = 0 + (ε : DualNumber k) • liftOctonion d
      simp

private lemma secondAxisJet_value (J : QuadraticJordan k (Model k))
    (hu : J.unit = cubicUnit) (ho : ∀ x y, J.groundOp x y = modelOp x y)
    (D : splitDerivations J) (c : Zorn k)
    (hc : frameEvaluation k D.val 0 = c) (hd : frameEvaluation k D.val 2 = 0) :
    axisJet D.val 1 = frameAxis 1 +
      singleBlockCoordinates 0 ((ε : DualNumber k) • liftOctonion c) := by
  rw [axisJet_eq, frameAxis_eval_one _ hu ho, hc, hd, neg_zero]
  apply Prod.ext <;> funext j
  · change (Pi.single (M := fun _ : Fin 3 => DualNumber k) 1 1) j + ε * algebraMap k (DualNumber k) 0 =
      (Pi.single (M := fun _ : Fin 3 => DualNumber k) 1 1) j + 0
    simp
  · change 0 + ((ε : DualNumber k) • liftOctonion (![c, 0, 0] j)) =
      0 + (Pi.single (M := fun _ : Fin 3 => Zorn (DualNumber k)) 0
        ((ε : DualNumber k) • liftOctonion c)) j
    simp only [zero_add]
    fin_cases j
    · rfl
    · change (ε : DualNumber k) • liftOctonion 0 = 0
      simp [zero_map_octonion]
    · change (ε : DualNumber k) • liftOctonion 0 = 0
      simp [zero_map_octonion]

theorem firstOrbitDifferential : FirstOrbitDifferentialType.{u} := by
  intro k _ J hu ho x hx
  obtain ⟨c, d, h⟩ := first_jet_shape x hx
  obtain ⟨D, hD⟩ := (ShortDirections.splitTangentRank k J hu ho).1 (![0, -c, d])
  have hc := congrFun hD (1 : Fin 3)
  have hd := congrFun hD (2 : Fin 3)
  exact ⟨D, (firstAxisJet_value J hu ho D c d hc hd).trans h.symm⟩

theorem secondOrbitDifferential : SecondOrbitDifferentialType.{u} := by
  intro k _ J hu ho x hx
  obtain ⟨c, h⟩ := second_jet_shape x hx
  obtain ⟨D, hD⟩ := (ShortDirections.splitTangentRank k J hu ho).1 (![c, 0, 0])
  have ha : frameEvaluation k D.val 0 = c := congrFun hD 0
  have hb : frameEvaluation k D.val 1 = 0 := congrFun hD 1
  have hc : frameEvaluation k D.val 2 = 0 := congrFun hD 2
  refine ⟨D, ?_, (secondAxisJet_value J hu ho D c ha hc).trans h.symm⟩
  rw [frameAxis_eval_zero J hu ho D, hb, hc, neg_zero]
  exact Prod.ext rfl (by funext i; fin_cases i <;> rfl)

open private infinitesimalUnit infinitesimal_quadratic_iff infinitesimal_add
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.AutomorphismScheme
open private preserves_splitCoordinates
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.ShortDirections

private noncomputable def dualAuto (D : Module.End k (Model k)) :
    Model (DualNumber k) ≃ₗ[DualNumber k] Model (DualNumber k) :=
  let B := modelBaseChange k (DualNumber k)
  B.symm.trans ((LinearMap.GeneralLinearGroup.toLinearEquiv (infinitesimalUnit D)).trans B)

private lemma dualAuto_act (D : Module.End k (Model k)) (x : DualNumber k ⊗[k] Model k) :
    dualAuto D (modelBaseChange k (DualNumber k) x) =
      modelBaseChange k (DualNumber k) (infinitesimal D x) := by
  unfold dualAuto
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

private lemma dualAuto_jet (D : Module.End k (Model k)) (i : Fin 3) :
    dualAuto D (frameAxis i) = axisJet D i := by
  rw [axisJet, ← baseChange_frameAxis (k := k) i, dualAuto_act]

private lemma dualAuto_isAuto (J : QuadraticJordan k (Model k)) (hu : J.unit = cubicUnit)
    (ho : ∀ x y, J.groundOp x y = modelOp x y) (D : splitDerivations J) :
    IsSplitAutomorphism (dualAuto D.val) :=
  (preserves_splitCoordinates J hu ho (infinitesimal D.val) (dualAuto D.val)
    (dualAuto_act D.val)).mp ((infinitesimal_quadratic_iff J D.val).mpr D.property)

private lemma dualAuto_reduction (D : Module.End k (Model k)) (z : Model (DualNumber k)) :
    reduceModel k (dualAuto D z) = reduceModel k z := by
  obtain ⟨x, rfl⟩ := (modelBaseChange k (DualNumber k)).surjective z
  rw [dualAuto_act]
  have h : infinitesimal D x = x + (ε : DualNumber k) • D.baseChange (DualNumber k) x := rfl
  rw [h, map_add, map_smul]
  unfold reduceModel
  change mapModel _ (_ + _ • _) = mapModel _ _
  rw [mapModel_add, mapModel_scalar]
  change _ + (0 : k) • _ = _
  rw [zero_smul, add_zero]

private lemma axisJet_add (D E : Module.End k (Model k)) (i : Fin 3) :
    axisJet (D + E) i = dualAuto D (axisJet E i) := by
  unfold axisJet
  rw [infinitesimal_add, dualAuto_act]
  rfl

theorem orderedFrameDifferential : OrderedFrameDifferentialType.{u} := by
  intro k _ J hu ho
  refine ⟨?_, (ShortDirections.splitTangentRank k J hu ho).1, ?_⟩
  · intro p hx hy
    obtain ⟨D, hD⟩ := firstOrbitDifferential k J hu ho ⟨p.val.1, p.property.1⟩ hx
    let g := dualAuto D.val
    have hg : IsSplitAutomorphism g := dualAuto_isAuto J hu ho D
    have hxg : g (frameAxis 0) = p.val.1 := (dualAuto_jet _ _).trans hD
    let y := g.symm p.val.2
    have hgy : g y = p.val.2 := g.apply_symm_apply _
    have h : IsFramePair (frameAxis 0) y :=
      (auto_frame_iff g hg _ _).mp (by rw [hxg, hgy]; exact p.property)
    have hyr : reduceModel k y = frameAxis 1 := by
      rw [← dualAuto_reduction D.val y]
      exact (congrArg (reduceModel k) hgy).trans hy
    obtain ⟨E, hE0, hE1⟩ := secondOrbitDifferential k J hu ho ⟨y, h⟩ hyr
    refine ⟨D + E, ?_, ?_⟩
    · change axisJet (D.val + E.val) 0 = _
      rw [axisJet_add, axisJet_eq, hE0]
      have hzero : TrialitySpecification.mapModel (algebraMap k (DualNumber k)) (0 : Model k) = 0 := by
        apply Prod.ext <;> funext i
        · exact map_zero _
        · exact zero_map_octonion
      rw [hzero, smul_zero, add_zero]
      exact hxg
    · change axisJet (D.val + E.val) 1 = _
      rw [axisJet_add, hE1]
      exact hgy
  · have h₈ : Module.finrank k (Zorn k) = 8 :=
      Module.finrank_eq_card_basis (Zorn.coordinateBasis k)
    rw [Module.finrank_pi_fintype]
    simp [h₈]


end Differentials

section FrameParameters

open MvPolynomial
open _root_.Specs.LinearAlgebraicGroups.Albert (QuadraticJordan)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (infinitesimal)
open IntegralZornDirectionsSpecification (DirectionIndex direction)
open ShortDirectionSpecification (splitDerivations frameEvaluation)
open TrialitySpecification (modelBaseChange)
open scoped TensorProduct DualNumber

open private shortFamily_natural shortFamily_groundIso shortFamily_differential mapModel_axis
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.ShortDirections
open private infinitesimal_add secondCoefficient secondCoefficient_tmul
  infinitesimal_apply scalar_eps_tmul from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.AutomorphismScheme

private abbrev FrameParameterIndex := Fin 3 × DirectionIndex
private abbrev FrameParameterRing (k : Type u) [CommRing k] :=
  MvPolynomial FrameParameterIndex k

private noncomputable def frameWord {R : Type u} [CommRing R]
    (t : FrameParameterIndex → R) (l : List FrameParameterIndex) : Model R ≃ₗ[R] Model R :=
  (l.map fun i => ShortDirections.shortFamily R i.1 i.2 (Multiplicative.ofAdd (t i))).prod

private noncomputable def frameProduct {R : Type u} [CommRing R]
    (t : FrameParameterIndex → R) : Model R ≃ₗ[R] Model R :=
  frameWord t Finset.univ.toList

private lemma frameWord_isAuto {R : Type u} [CommRing R]
    (t : FrameParameterIndex → R) (l : List FrameParameterIndex) :
    IsSplitAutomorphism (frameWord t l) := by
  obtain ⟨J, _, hu, ho, _, _, _, _⟩ := Triality.cubicFrameStabilizer R
  induction l with
  | nil => exact ⟨rfl, fun _ _ => rfl⟩
  | cons i l ih =>
    let a := ShortDirections.shortFamily R i.1 i.2 (Multiplicative.ofAdd (t i))
    have h : a J.unit = J.unit ∧
        ∀ x y, a (J.groundOp x y) = J.groundOp (a x) (a y) :=
      shortFamily_groundIso J hu ho i.1 i.2 (t i)
    have ha : IsSplitAutomorphism a := by simpa only [IsSplitAutomorphism, hu, ho] using h
    refine ⟨?_, fun x y => ?_⟩
    · change a (frameWord t l cubicUnit) = cubicUnit
      rw [ih.1, ha.1]
    · change a (frameWord t l (modelOp x y)) =
        modelOp (a (frameWord t l x)) (a (frameWord t l y))
      rw [ih.2, ha.2]

private lemma frameWord_natural {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (t : FrameParameterIndex → R) (l : List FrameParameterIndex) (x : Model R) :
    TrialitySpecification.mapModel f (frameWord t l x) =
      frameWord (f ∘ t) l (TrialitySpecification.mapModel f x) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change TrialitySpecification.mapModel f
      (ShortDirections.shortFamily R i.1 i.2 (Multiplicative.ofAdd (t i)) (frameWord t l x)) =
      ShortDirections.shortFamily S i.1 i.2 (Multiplicative.ofAdd (f (t i)))
        (frameWord (f ∘ t) l (TrialitySpecification.mapModel f x))
    rw [shortFamily_natural, ih]

private lemma frameWord_zero {R : Type u} [CommRing R] (l : List FrameParameterIndex) :
    frameWord (fun _ => (0 : R)) l = 1 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change ShortDirections.shortFamily R i.1 i.2 1 * frameWord (fun _ => (0 : R)) l = 1
    rw [map_one, ih, one_mul]

private noncomputable def frameParameterMap (k : Type u) [CommRing k] :
    FrameRing k →ₐ[k] FrameParameterRing k :=
  framePointHom ⟨(frameProduct X (frameAxis 0), frameProduct X (frameAxis 1)),
    (orbitValues _ _ (frameWord_isAuto X Finset.univ.toList)).2.2⟩

private lemma frameParameterMap_eval {k S : Type u} [CommRing k] [CommRing S] [Algebra k S]
    (f : FrameParameterRing k →ₐ[k] S) :
    frameOfHom k (f.comp (frameParameterMap k)) =
      (frameProduct (fun i => f (X i)) (frameAxis 0),
       frameProduct (fun i => f (X i)) (frameAxis 1)) := by
  have he : frameOfHom k (frameParameterMap k) =
      (frameProduct X (frameAxis 0), frameProduct X (frameAxis 1)) :=
    frameOfHom_point _
  rw [frameOfHom_comp, he]
  apply Prod.ext
  · change TrialitySpecification.mapModel f.toRingHom (frameWord X Finset.univ.toList (frameAxis 0)) = _
    rw [frameWord_natural, mapModel_axis]
    rfl
  · change TrialitySpecification.mapModel f.toRingHom (frameWord X Finset.univ.toList (frameAxis 1)) = _
    rw [frameWord_natural, mapModel_axis]
    rfl

private lemma frameWord_jet {k : Type u} [Field k] {J : QuadraticJordan k (Model k)}
    (t : FrameParameterIndex → k) (D : FrameParameterIndex → splitDerivations J)
    (h : ∀ i x, ShortDirections.shortFamily (DualNumber k) i.1 i.2
        (Multiplicative.ofAdd (TrivSqZeroExt.inr (t i)))
        (modelBaseChange k (DualNumber k) x) =
      modelBaseChange k (DualNumber k) (infinitesimal (D i).val x))
    (l : List FrameParameterIndex) (x : DualNumber k ⊗[k] Model k) :
    frameWord (TrivSqZeroExt.inr ∘ t) l (modelBaseChange k (DualNumber k) x) =
      modelBaseChange k (DualNumber k) (infinitesimal ((l.map D).sum : splitDerivations J).val x) := by
  induction l generalizing x with
  | nil =>
    change modelBaseChange k (DualNumber k) x = modelBaseChange k (DualNumber k) (infinitesimal 0 x)
    simp [infinitesimal]
  | cons i l ih =>
    change ShortDirections.shortFamily (DualNumber k) i.1 i.2
      (Multiplicative.ofAdd (TrivSqZeroExt.inr (t i)))
      (frameWord (TrivSqZeroExt.inr ∘ t) l (modelBaseChange k (DualNumber k) x)) =
        modelBaseChange k (DualNumber k)
          (infinitesimal ((D i).val + ((l.map D).sum : splitDerivations J).val) x)
    rw [ih, h, infinitesimal_add]
    rfl

private noncomputable def parameterVelocities (k : Type u) [Field k] :
    (FrameParameterIndex → k) ≃ (Fin 3 → Zorn k) where
  toFun t i := (IntegralZornDirections.directionBasis k).equivFun.symm (fun j => t (i, j))
  invFun z i := (IntegralZornDirections.directionBasis k).equivFun (z i.1) i.2
  left_inv t := by
    funext i
    exact congrFun ((IntegralZornDirections.directionBasis k).equivFun.apply_symm_apply _) i.2
  right_inv z := by
    funext i
    exact (IntegralZornDirections.directionBasis k).equivFun.symm_apply_apply (z i)

private lemma frameProduct_jet {k : Type u} [Field k] (J : QuadraticJordan k (Model k))
    (hu : J.unit = cubicUnit) (ho : ∀ a b, J.groundOp a b = modelOp a b) (t : FrameParameterIndex → k) :
    ∃ D : splitDerivations J,
      (∀ i, frameProduct (TrivSqZeroExt.inr ∘ t) (frameAxis i) = axisJet D.val i) ∧
      frameEvaluation k D.val = parameterVelocities k t := by
  classical
  choose D hD using fun i : FrameParameterIndex => shortFamily_differential k J hu ho i.1 i.2 (t i)
  refine ⟨∑ i, D i, ?_, ?_⟩
  · intro i
    rw [← baseChange_frameAxis (k := k) i, frameProduct,
      frameWord_jet t D (fun j => (hD j).1), Finset.sum_map_toList]
    rfl
  · let E := (frameEvaluation k).domRestrict (splitDerivations J)
    change E (∑ i, D i) = parameterVelocities k t
    rw [map_sum]
    have ev (i : FrameParameterIndex) :
        E (D i) = t i • Pi.single i.1 (direction k i.2) := (hD i).2
    simp only [ev, Fintype.sum_prod_type, Finset.sum_comm (s := Finset.univ (α := Fin 3))]
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
      eq_comm (a := i), Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    change _ = (IntegralZornDirections.directionBasis k).equivFun.symm (fun j => t (i, j))
    rw [Module.Basis.equivFun_symm_apply]
    simp only [IntegralZornDirections.directionBasis_apply]

private lemma frameAxis_jet_eq_iff {k : Type u} [Field k]
    (D E : Module.End k (Model k)) (i : Fin 3) :
    axisJet D i = axisJet E i ↔ D (frameAxis i) = E (frameAxis i) := by
  have h (D : Module.End k (Model k)) :
      secondCoefficient ((modelBaseChange k (DualNumber k)).symm (axisJet D i)) =
        D (frameAxis i) := by
    unfold axisJet
    rw [LinearEquiv.symm_apply_apply, infinitesimal_apply, LinearMap.baseChange_tmul, scalar_eps_tmul]
    simp only [map_add, secondCoefficient_tmul, TrivSqZeroExt.snd_one, DualNumber.snd_eps,
      zero_smul, one_smul, zero_add]
  constructor
  · intro he
    rw [← h D, ← h E, he]
  · intro he
    simp only [axisJet_eq, he]

private lemma evaluations_eq_iff {k : Type u} [Field k] (J : QuadraticJordan k (Model k))
    (hu : J.unit = cubicUnit) (ho : ∀ a b, J.groundOp a b = modelOp a b) (D E : splitDerivations J) :
    frameEvaluation k D.val = frameEvaluation k E.val ↔
      (axisJet D.val 0, axisJet D.val 1) = (axisJet E.val 0, axisJet E.val 1) := by
  constructor
  · intro h
    apply Prod.ext <;> apply (frameAxis_jet_eq_iff _ _ _).mpr
    · rw [frameAxis_eval_zero J hu ho D, frameAxis_eval_zero J hu ho E, h]
    · rw [frameAxis_eval_one J hu ho D, frameAxis_eval_one J hu ho E, h]
  · intro h
    have h₀ := (frameAxis_jet_eq_iff _ _ 0).mp (congrArg Prod.fst h)
    have h₁ := (frameAxis_jet_eq_iff _ _ 1).mp (congrArg Prod.snd h)
    rw [frameAxis_eval_zero J hu ho D, frameAxis_eval_zero J hu ho E] at h₀
    rw [frameAxis_eval_one J hu ho D, frameAxis_eval_one J hu ho E] at h₁
    funext i
    fin_cases i
    · change frameEvaluation k D.val 0 = frameEvaluation k E.val 0
      have he := congrArg (fun a : Model k => a.2 0) h₁
      exact he
    · exact neg_injective (congrArg (fun a : Model k => a.2 1) h₀)
    · change frameEvaluation k D.val 2 = frameEvaluation k E.val 2
      have he := congrArg (fun a : Model k => a.2 2) h₀
      exact he

open _root_.Specs.AdvCommAlg.Differentials.Tangent (PointLifts)

private noncomputable def parameterOrigin (k : Type u) [Field k] : FrameParameterRing k →ₐ[k] k :=
  aeval fun _ => 0

private noncomputable def standardFramePoint (k : Type u) [Field k] : FrameRing k →ₐ[k] k :=
  (parameterOrigin k).comp (frameParameterMap k)

private lemma standardFramePoint_eval (k : Type u) [Field k] :
    frameOfHom k (standardFramePoint k) = (frameAxis 0, frameAxis 1) := by
  rw [standardFramePoint, frameParameterMap_eval]
  have he : (fun i => parameterOrigin k (X i)) = fun _ => (0 : k) := by
    funext i
    exact aeval_X _ _
  rw [he, frameProduct, frameWord_zero]
  rfl

private def precomposeLifts {k B C : Type*} [Field k] [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] (m : B →ₐ[k] C) (y : C →ₐ[k] k) :
    PointLifts k C k y → PointLifts k B k (y.comp m) :=
  fun f => ⟨f.val.comp m, by rw [← AlgHom.comp_assoc, f.property]⟩

private noncomputable def parameterLiftsEquiv (k : Type u) [Field k] :
    (FrameParameterIndex → k) ≃ PointLifts k (FrameParameterRing k) k (parameterOrigin k) where
  toFun t := ⟨aeval (TrivSqZeroExt.inr ∘ t), by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, aeval_X, parameterOrigin]
    rfl⟩
  invFun f i := (f.val (X i)).snd
  left_inv t := by
    funext i
    change (aeval (R := k) (TrivSqZeroExt.inr ∘ t) (X i)).snd = _
    rw [aeval_X]
    rfl
  right_inv f := by
    apply Subtype.ext
    apply MvPolynomial.algHom_ext
    intro i
    change aeval (R := k) (fun j => TrivSqZeroExt.inr (f.val (X j)).snd) (X i) = _
    rw [aeval_X]
    apply TrivSqZeroExt.ext
    · have he := congrArg (fun g : FrameParameterRing k →ₐ[k] k => g (X i)) f.property
      change (f.val (X i)).fst = parameterOrigin k (X i) at he
      exact (he.trans (aeval_X _ _)).symm
    · rfl

private lemma frameParameterLifts_bijective (k : Type u) [Field k] :
    Function.Bijective (precomposeLifts (frameParameterMap k) (parameterOrigin k)) := by
  apply ((parameterLiftsEquiv k).bijective_comp _).mp
  obtain ⟨J, _, hu, ho, _, _, _, _⟩ := Triality.cubicFrameStabilizer k
  let F := precomposeLifts (frameParameterMap k) (parameterOrigin k) ∘ parameterLiftsEquiv k
  have h (t : FrameParameterIndex → k) :
      ∃ D : splitDerivations J,
        frameOfHom k (F t).val = (axisJet D.val 0, axisJet D.val 1) ∧
        frameEvaluation k D.val = parameterVelocities k t := by
    obtain ⟨D, hD, he⟩ := frameProduct_jet J hu ho t
    refine ⟨D, ?_, he⟩
    change frameOfHom k ((aeval (R := k) (TrivSqZeroExt.inr ∘ t)).comp
      (frameParameterMap k)) = _
    rw [frameParameterMap_eval]
    simp only [aeval_X, hD]
  have hinj {f g : FrameRing k →ₐ[k] DualNumber k}
      (hfg : frameOfHom k f = frameOfHom k g) : f = g :=
    frameHomEquiv.injective (Subtype.ext hfg)
  change Function.Bijective F
  constructor
  · intro s t he
    obtain ⟨D, hD, es⟩ := h s
    obtain ⟨E, hE, et⟩ := h t
    apply (parameterVelocities k).injective
    rw [← es, ← et, evaluations_eq_iff J hu ho, ← hD, ← hE, he]
  · intro f
    let p : FramePairPoint (DualNumber k) := frameHomEquiv f.val
    have hred : (reduceModel k p.val.1, reduceModel k p.val.2) =
        (frameAxis 0, frameAxis 1) := by
      change (mapModel (TrivSqZeroExt.fstHom k k k).toRingHom (frameOfHom k f.val).1,
        mapModel (TrivSqZeroExt.fstHom k k k).toRingHom (frameOfHom k f.val).2) = _
      rw [← frameOfHom_comp (TrivSqZeroExt.fstHom k k k) f.val, f.property]
      exact standardFramePoint_eval k
    obtain ⟨D, hx, hy⟩ := (orderedFrameDifferential k J hu ho).1 p
      (congrArg Prod.fst hred) (congrArg Prod.snd hred)
    obtain ⟨t, ht⟩ := (parameterVelocities k).surjective (frameEvaluation k D.val)
    obtain ⟨E, hE, he⟩ := h t
    refine ⟨t, Subtype.ext (hinj ?_)⟩
    have hp : (axisJet D.val 0, axisJet D.val 1) = p.val := Prod.ext hx hy
    exact hE.trans (((evaluations_eq_iff J hu ho E D).mp (he.trans ht)).trans hp)

open Specs.LinearAlgebraicGroups.Albert.SmoothIdentityCriterion (cotangentFiberMap CotangentFiber)
open Algebra TensorProduct KaehlerDifferential
open private formallyEtale_of_fiber_bijective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SmoothIdentityCriterion

private lemma openImage_of_lifts {k B C : Type*} [Field k] [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] [Algebra.FinitePresentation k B] [Algebra.FinitePresentation k C]
    [Algebra.FormallySmooth k C] (m : B →ₐ[k] C) (y : C →ₐ[k] k)
    (hm : Function.Bijective (precomposeLifts m y)) :
    ∃ s : C, y s ≠ 0 ∧
      IsOpen (Set.range (PrimeSpectrum.comap
        ((algebraMap C (Localization.Away s)).comp m.toRingHom))) := by
  let x := y.comp m
  let : Algebra B C := m.toRingHom.toAlgebra
  let : Algebra B k := x.toRingHom.toAlgebra
  let : Algebra C k := y.toRingHom.toAlgebra
  let : IsScalarTower k B C := .of_algebraMap_eq fun z => (m.commutes z).symm
  let : IsScalarTower k B k := .of_algebraMap_eq fun z => (x.commutes z).symm
  let : IsScalarTower k C k := .of_algebraMap_eq fun z => (y.commutes z).symm
  let : IsScalarTower B C k := .of_algebraMap_eq' rfl
  obtain ⟨eB, hB, _⟩ := AdvCommAlg.Differentials.point_dual_lifts k B k x
  obtain ⟨eC, hC, _⟩ := AdvCommAlg.Differentials.point_dual_lifts k C k y
  have he : (eB : _ → _) ∘ (cotangentFiberMap k B C k).dualMap =
      precomposeLifts m y ∘ eC := by
    funext l
    apply Subtype.ext
    apply AlgHom.ext
    intro b
    change (eB ((cotangentFiberMap k B C k).dualMap l)).val b = (eC l).val (m b)
    simp [hB, hC, x]
    rfl
  have hf : Function.Bijective (cotangentFiberMap k B C k) :=
    LinearMap.dualMap_bijective_iff.mp ((eB.comp_bijective _).mp
      (he.symm ▸ hm.comp eC.bijective))
  let q := RingHom.ker y.toRingHom
  let : q.IsPrime := RingHom.ker_isPrime _
  let L := Localization.AtPrime q
  let yL : L →+* k := IsLocalization.lift (M := q.primeCompl)
    (fun a => isUnit_iff_ne_zero.mpr a.2)
  let : Algebra L k := yL.toAlgebra
  have : IsScalarTower C L k := .of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  have : IsScalarTower B L k := .to₁₃₄ _ C _ _
  have hker : IsLocalRing.maximalIdeal L ≤ RingHom.ker (algebraMap L k) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q]
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change algebraMap L k (algebraMap C L a) = 0
    rw [← IsScalarTower.algebraMap_apply C L k]
    exact ha
  have : FormallyEtale C L := FormallyEtale.of_isLocalization q.primeCompl
  have : FormallySmooth k L := FormallySmooth.comp k C L
  have : EssFiniteType k L := .comp _ C _
  have hfl : Function.Bijective (cotangentFiberMap k B L k) := by
    rw [SmoothIdentityCriterion.cotangentFiberMap_comp (B := C)]
    exact SmoothIdentityCriterion.cotangentFiberMap_bijective_of_formallyEtale.comp hf
  have : IsEtaleAt B q := formallyEtale_of_fiber_bijective hker hfl
  have : Algebra.FinitePresentation B C := .of_restrict_scalars_finitePresentation k B C
  obtain ⟨s, hs, he⟩ := Algebra.exists_etale_of_isEtaleAt (R := B) q
  let T := Localization.Away s
  let : Algebra.Etale B T := he
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have : Module.Flat B T := Algebra.Smooth.flat_of_isNoetherianRing B T
  refine ⟨s, hs, ?_⟩
  change IsOpen (Set.range (PrimeSpectrum.comap (algebraMap B T)))
  simpa only [Set.image_univ] using
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation (R := B) (S := T)
      Set.univ isOpen_univ

private instance frameFinitePresentation (k : Type u) [CommRing k] :
    Algebra.FinitePresentation k (FrameRing k) :=
  Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))

private lemma frameParameterOpenImage (k : Type u) [Field k] :
    ∃ s : FrameParameterRing k, parameterOrigin k s ≠ 0 ∧
      IsOpen (Set.range (PrimeSpectrum.comap
        ((algebraMap (FrameParameterRing k) (Localization.Away s)).comp
          (frameParameterMap k).toRingHom))) :=
  openImage_of_lifts (frameParameterMap k) (parameterOrigin k) (frameParameterLifts_bijective k)

end FrameParameters

section FrameAction

open MvPolynomial
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (PreservesQuadratic)
open TrialitySpecification (modelBaseChange)
open SplitSpecification (ParaQuadratic)
open scoped TensorProduct

open private modelBaseChange_pure modelBaseChange_natural preserves_splitCoordinates
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.ShortDirections

variable {k S T : Type u} [CommRing k] [CommRing S] [CommRing T] [Algebra k S] [Algebra k T]

private noncomputable def extendFrameAuto (g : Model k ≃ₗ[k] Model k) (S : Type u)
    [CommRing S] [Algebra k S] : Model S ≃ₗ[S] Model S :=
  let B := modelBaseChange k S
  B.symm.trans ((g.baseChange k S (Model k) (Model k)).trans B)

private lemma extendFrameAuto_apply (g : Model k ≃ₗ[k] Model k) (x : S ⊗[k] Model k) :
    extendFrameAuto g S (modelBaseChange k S x) =
      modelBaseChange k S (g.toLinearMap.baseChange S x) := by
  unfold extendFrameAuto
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

private lemma extendFrameAuto_natural (g : Model k ≃ₗ[k] Model k)
    (f : S →ₐ[k] T) (x : Model S) :
    mapModel f.toRingHom (extendFrameAuto g S x) = extendFrameAuto g T (mapModel f.toRingHom x) := by
  obtain ⟨y, rfl⟩ := (modelBaseChange k S).surjective x
  change TrialitySpecification.mapModel f.toRingHom (extendFrameAuto g S _) =
    extendFrameAuto g T (TrialitySpecification.mapModel f.toRingHom _)
  rw [extendFrameAuto_apply, ← modelBaseChange_natural, ← modelBaseChange_natural, extendFrameAuto_apply]
  apply congrArg (modelBaseChange k T)
  induction y using TensorProduct.inductionOn with
  | tmul a z => simp [LinearMap.baseChange_tmul, LinearMap.rTensor_tmul]
  | add y z hy hz => simp only [map_add, hy, hz]

private lemma extendFrameAuto_symm (g : Model k ≃ₗ[k] Model k) :
    extendFrameAuto g.symm S = (extendFrameAuto g S).symm := by
  simp only [extendFrameAuto, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearEquiv.baseChange_symm]
  exact (LinearEquiv.trans_assoc _ _ _).symm

private lemma modelBaseChange_self (x : Model k) :
    modelBaseChange k k (1 ⊗ₜ[k] x) = x := by
  rw [modelBaseChange_pure]
  refine (one_smul k _).trans ?_
  rfl

private lemma extendFrameAuto_self (g : Model k ≃ₗ[k] Model k) (x : Model k) :
    extendFrameAuto g k x = g x := by
  calc
    _ = extendFrameAuto g k (modelBaseChange k k (1 ⊗ₜ[k] x)) :=
      congrArg (extendFrameAuto g k) (modelBaseChange_self x).symm
    _ = modelBaseChange k k (1 ⊗ₜ[k] g x) := by
      rw [extendFrameAuto_apply, LinearMap.baseChange_tmul]
      rfl
    _ = _ := modelBaseChange_self _

private lemma extendFrameAuto_preserves (g : Model k ≃ₗ[k] Model k) (hg : IsSplitAutomorphism g) :
    IsSplitAutomorphism (extendFrameAuto g S) := by
  obtain ⟨J, _, hu, ho, _, _, _, _⟩ := Triality.cubicFrameStabilizer k
  let A := ParaQuadratic.ofJordan J
  have hground : A.IsGroundIso A g := by
    change g J.unit = J.unit ∧ ∀ x y, g (J.groundOp x y) = J.groundOp (g x) (g y)
    simpa only [hu, ho, IsSplitAutomorphism] using hg
  have hiso : A.IsIso A g := (A.isIso_iff_ground A g).mpr hground
  apply (preserves_splitCoordinates J hu ho _ (extendFrameAuto g S) (extendFrameAuto_apply g)).mp
  refine ⟨?_, hiso.2 S⟩
  change g.toLinearMap.baseChange S (1 ⊗ₜ[k] J.unit) = 1 ⊗ₜ[k] J.unit
  rw [LinearMap.baseChange_tmul]
  exact congrArg (fun z => (1 : S) ⊗ₜ[k] z) hiso.1

private lemma inverseFrameAuto (g : Model k ≃ₗ[k] Model k) (hg : IsSplitAutomorphism g) :
    IsSplitAutomorphism g.symm := by
  refine ⟨g.injective ?_, fun x y => g.injective ?_⟩
  · rw [LinearEquiv.apply_symm_apply, hg.1]
  · rw [LinearEquiv.apply_symm_apply, hg.2, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

private noncomputable def frameTranslate (g : Model k ≃ₗ[k] Model k) (hg : IsSplitAutomorphism g) :
    FrameRing k →ₐ[k] FrameRing k :=
  let f := AlgHom.id k (FrameRing k)
  let a := extendFrameAuto g (FrameRing k)
  framePointHom ⟨(a (frameOfHom k f).1, a (frameOfHom k f).2),
    (auto_frame_iff a (extendFrameAuto_preserves g hg) _ _).mpr (frame_hom_point f)⟩

private lemma frameTranslate_eval (g : Model k ≃ₗ[k] Model k) (hg : IsSplitAutomorphism g)
    (f : FrameRing k →ₐ[k] S) :
    frameOfHom k (f.comp (frameTranslate g hg)) =
      (extendFrameAuto g S (frameOfHom k f).1, extendFrameAuto g S (frameOfHom k f).2) := by
  let e := AlgHom.id k (FrameRing k)
  rw [frameOfHom_comp, show frameOfHom k (frameTranslate g hg) =
      (extendFrameAuto g (FrameRing k) (frameOfHom k e).1,
        extendFrameAuto g (FrameRing k) (frameOfHom k e).2) from frameOfHom_point _,
    extendFrameAuto_natural, extendFrameAuto_natural]
  have hf := frameOfHom_comp f e
  change frameOfHom k f = _ at hf
  exact Prod.ext
    (congrArg (extendFrameAuto g S) (congrArg Prod.fst hf).symm)
    (congrArg (extendFrameAuto g S) (congrArg Prod.snd hf).symm)

private lemma frameTranslate_inverse (g : Model k ≃ₗ[k] Model k) (hg : IsSplitAutomorphism g) :
    (frameTranslate g.symm (inverseFrameAuto g hg)).comp (frameTranslate g hg) =
      AlgHom.id k (FrameRing k) := by
  apply frameHomEquiv.injective
  apply Subtype.ext
  change frameOfHom k _ = frameOfHom k _
  have he := frameTranslate_eval g.symm (inverseFrameAuto g hg) (AlgHom.id k (FrameRing k))
  rw [AlgHom.id_comp] at he
  rw [frameTranslate_eval, he, extendFrameAuto_symm]
  simp only [LinearEquiv.apply_symm_apply]

private lemma frameTranslate_bijective (g : Model k ≃ₗ[k] Model k) (hg : IsSplitAutomorphism g) :
    Function.Bijective (frameTranslate g hg).toRingHom := by
  have h := frameTranslate_inverse g hg
  have h' := frameTranslate_inverse g.symm (inverseFrameAuto g hg)
  exact ⟨(show Function.LeftInverse (frameTranslate g.symm (inverseFrameAuto g hg))
      (frameTranslate g hg) from DFunLike.congr_fun h).injective,
    (show Function.RightInverse (frameTranslate g.symm (inverseFrameAuto g hg))
      (frameTranslate g hg) from DFunLike.congr_fun h').surjective⟩

end FrameAction

section FrameBaseChange

open Algebra TensorProduct
open scoped TensorProduct

variable {k K S : Type u} [CommRing k] [CommRing K] [Algebra k K]

private noncomputable def frameBaseMap : FrameRing k →ₐ[k] FrameRing K :=
  framePointHom (frameHomEquiv (AlgHom.id K (FrameRing K)))

private lemma frameOfHom_base [CommRing S] [Algebra K S] [Algebra k S] [IsScalarTower k K S]
    (f : FrameRing K →ₐ[K] S) :
    frameOfHom k ((f.restrictScalars k).comp frameBaseMap) = frameOfHom K f := by
  rw [frameOfHom_comp, show frameOfHom k (frameBaseMap (k := k) (K := K)) =
    frameOfHom K (AlgHom.id K (FrameRing K)) from frameOfHom_point _]
  exact (frameOfHom_comp f (AlgHom.id K (FrameRing K))).symm

set_option maxHeartbeats 800000 in
private noncomputable def frameBaseChange : K ⊗[k] FrameRing k ≃ₐ[K] FrameRing K := by
  let L := K ⊗[k] FrameRing k
  let i : FrameRing k →ₐ[k] L := Algebra.TensorProduct.includeRight
  let f := AlgHom.liftEquiv k K (FrameRing k) (FrameRing K) frameBaseMap
  let p : FramePairPoint L := frameHomEquiv (k := k) i
  let g : FrameRing K →ₐ[K] L := framePointHom p
  have hf : (f.restrictScalars k).comp i = frameBaseMap :=
    (AlgHom.liftEquiv k K (FrameRing k) (FrameRing K)).symm_apply_apply _
  have hg : frameOfHom K (S := L) g = frameOfHom k (S := L) i := by
    change frameOfHom K (S := L) (framePointHom p) = p.val
    exact frameOfHom_point (k := K) (S := L) p
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply frameHomEquiv.injective
    apply Subtype.ext
    change frameOfHom K (f.comp g) = frameOfHom K (AlgHom.id K (FrameRing K))
    rw [frameOfHom_comp (k := K) (S := L) (T := FrameRing K) f g, hg]
    have he := (frameOfHom_comp (k := k) (S := L) (T := FrameRing K) (f.restrictScalars k) i).symm
    rw [hf] at he
    exact he.trans (frameOfHom_point (k := k) (frameHomEquiv (AlgHom.id K (FrameRing K))))
  · apply Algebra.TensorProduct.ext_ring
    change ((g.restrictScalars k).comp (f.restrictScalars k)).comp i = i
    rw [AlgHom.comp_assoc, hf]
    apply (frameHomEquiv (k := k) (S := L)).injective
    apply Subtype.ext
    change frameOfHom k (S := L) ((g.restrictScalars k).comp frameBaseMap) = frameOfHom k (S := L) i
    exact (frameOfHom_base (k := k) (K := K) (S := L) g).trans hg

private lemma frameBaseChange_pure (x : FrameRing k) :
    frameBaseChange (k := k) (K := K) (1 ⊗ₜ[k] x) = frameBaseMap x := by
  unfold frameBaseChange
  rw [AlgEquiv.ofAlgHom_apply]
  change AlgHom.liftEquiv k K (FrameRing k) (FrameRing K) frameBaseMap (1 ⊗ₜ[k] x) = _
  rw [AlgHom.liftEquiv_tmul, one_smul]

private lemma frameBaseMap_open {k K : Type u} [Field k] [CommRing K] [Algebra k K] :
    IsOpenMap (PrimeSpectrum.comap (frameBaseMap (k := k) (K := K)).toRingHom) := by
  let e : FrameRing k ⊗[k] K ≃ₐ[k] FrameRing K :=
    (Algebra.TensorProduct.comm k (FrameRing k) K).trans (frameBaseChange.restrictScalars k)
  have h : e.toRingHom.comp (algebraMap (FrameRing k) (FrameRing k ⊗[k] K)) =
      (frameBaseMap (k := k) (K := K)).toRingHom := by
    apply RingHom.ext
    intro a
    change frameBaseChange (k := k) (K := K) (1 ⊗ₜ[k] a) = _
    exact frameBaseChange_pure a
  rw [← h]
  change IsOpenMap (PrimeSpectrum.comap (algebraMap (FrameRing k) (FrameRing k ⊗[k] K)) ∘
    PrimeSpectrum.comap e.toRingHom)
  exact PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field.comp
    (PrimeSpectrum.isHomeomorph_comap_of_bijective e.bijective).isOpenMap

end FrameBaseChange

section GeometricOrbit

open MvPolynomial
open scoped TensorProduct

private lemma splitAuto_comp {R : Type u} [CommRing R] {g h : Model R ≃ₗ[R] Model R}
    (hg : IsSplitAutomorphism g) (hh : IsSplitAutomorphism h) : IsSplitAutomorphism (g * h) := by
  refine ⟨?_, fun x y => ?_⟩
  · change g (h cubicUnit) = cubicUnit
    rw [hh.1, hg.1]
  · change g (h (modelOp x y)) = modelOp (g (h x)) (g (h y))
    rw [hh.2, hg.2]

private def primeOfHom {A K : Type*} [CommRing A] [Field K] (f : A →+* K) : PrimeSpectrum A :=
  ⟨RingHom.ker f, RingHom.ker_isPrime f⟩

private lemma primeOfHom_comp {A B K : Type*} [CommRing A] [CommRing B] [Field K]
    (f : A →+* B) (g : B →+* K) :
    PrimeSpectrum.comap f (primeOfHom g) = primeOfHom (g.comp f) := by
  apply PrimeSpectrum.ext
  exact Ideal.comap_comap f g

theorem orderedFrameOpenOrbit : OrderedFrameOpenOrbitType.{u} := by
  intro k _ _
  refine ⟨?_, ?_⟩
  · apply isOpen_iff_mem_nhds.mpr
    intro p hp
    obtain ⟨K, _, _, f, g, hg, hfg, hp⟩ := hp
    obtain ⟨s, hs, hOpen⟩ := frameParameterOpenImage K
    let C := FrameParameterRing K
    let L := Localization.Away s
    let ι : C →ₐ[K] L := IsScalarTower.toAlgHom K C L
    let m := ι.comp (frameParameterMap K)
    let τ := frameTranslate g hg
    let b : FrameRing k →ₐ[k] FrameRing K := frameBaseMap
    let θ := ((m.comp τ).restrictScalars k).comp b
    let U := Set.range (PrimeSpectrum.comap θ.toRingHom)
    have hU : IsOpen U := by
      have hτ : IsOpenMap (PrimeSpectrum.comap τ.toRingHom) :=
        (PrimeSpectrum.isHomeomorph_comap_of_bijective (frameTranslate_bijective g hg)).isOpenMap
      have hb : IsOpenMap (PrimeSpectrum.comap b.toRingHom) := frameBaseMap_open (k := k) (K := K)
      have he : U = PrimeSpectrum.comap b.toRingHom ''
          (PrimeSpectrum.comap τ.toRingHom '' Set.range (PrimeSpectrum.comap m.toRingHom)) := by
        change Set.range (PrimeSpectrum.comap ((m.toRingHom.comp τ.toRingHom).comp b.toRingHom)) = _
        rw [PrimeSpectrum.comap_comp, Set.range_comp, PrimeSpectrum.comap_comp, Set.range_comp]
      exact he.symm ▸ hb _ (hτ _ hOpen)
    have hvalue {S : Type u} [CommRing S] [Algebra K S] (v : L →ₐ[K] S) :
        frameOfHom K (v.comp (m.comp τ)) =
          (extendFrameAuto g S (frameProduct (fun j => v (ι (X j))) (frameAxis 0)),
           extendFrameAuto g S (frameProduct (fun j => v (ι (X j))) (frameAxis 1))) := by
      rw [← AlgHom.comp_assoc, frameTranslate_eval]
      rw [show v.comp m = (v.comp ι).comp (frameParameterMap K) from rfl, frameParameterMap_eval]
      rfl
    refine mem_nhds_iff.mpr ⟨U, ?_, hU, ?_⟩
    · rintro q ⟨r, rfl⟩
      let F := r.asIdeal.ResidueField
      let v : L →ₐ[K] F := IsScalarTower.toAlgHom K L F
      let : Algebra k F := ((algebraMap K F).comp (algebraMap k K)).toAlgebra
      let : IsScalarTower k K F := .of_algebraMap_eq' rfl
      let w := frameProduct (fun j => v (ι (X j)))
      let a := extendFrameAuto g F
      let f' := ((v.comp (m.comp τ)).restrictScalars k).comp b
      refine ⟨F, inferInstance, inferInstance, f', a * w,
        splitAuto_comp (extendFrameAuto_preserves g hg) (frameWord_isAuto _ _), ?_, ?_⟩
      · exact (frameOfHom_base (v.comp (m.comp τ))).trans (hvalue v)
      · change (RingHom.ker v.toRingHom).comap θ.toRingHom = r.asIdeal.comap θ.toRingHom
        rw [show RingHom.ker v.toRingHom = r.asIdeal from r.asIdeal.ker_algebraMap_residueField]
    · let v : L →ₐ[K] K := IsLocalization.Away.liftAlgHom s (isUnit_iff_ne_zero.mpr hs)
      have hv : (fun j => v (ι (X j))) = fun _ => (0 : K) := by
        funext j
        change IsLocalization.Away.lift s (isUnit_iff_ne_zero.mpr hs)
          (algebraMap C L (X j)) = _
        rw [IsLocalization.Away.lift_eq]
        exact aeval_X _ _
      have he : frameOfHom K (v.comp (m.comp τ)) = (g (frameAxis 0), g (frameAxis 1)) := by
        rw [hvalue v, hv, frameProduct, frameWord_zero]
        change (extendFrameAuto g K (frameAxis 0), extendFrameAuto g K (frameAxis 1)) = _
        rw [extendFrameAuto_self, extendFrameAuto_self]
      have hf : ((v.comp (m.comp τ)).restrictScalars k).comp b = f := by
        apply frameHomEquiv.injective
        apply Subtype.ext
        exact (frameOfHom_base (v.comp (m.comp τ))).trans (he.trans hfg.symm)
      refine ⟨primeOfHom v.toRingHom, ?_⟩
      rw [primeOfHom_comp]
      apply PrimeSpectrum.ext
      change RingHom.ker (v.toRingHom.comp θ.toRingHom) = p.asIdeal
      exact (congrArg (fun h : FrameRing k →ₐ[k] K => RingHom.ker h.toRingHom) hf).trans hp
  · refine ⟨primeOfHom (standardFramePoint k).toRingHom, k, inferInstance, inferInstance,
      standardFramePoint k, 1, ⟨rfl, fun _ _ => rfl⟩, standardFramePoint_eval k, rfl⟩

end GeometricOrbit

end LinearAlgebraicGroups.Albert.IdempotentCharts
