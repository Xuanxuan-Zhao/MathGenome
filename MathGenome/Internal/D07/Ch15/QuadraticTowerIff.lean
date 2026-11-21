import MathGenome.Internal.Specs.D07.Ch15.QuadraticTowerIff
import MathGenome.Internal.D07.Ch15.GeometricFieldOperations
import MathGenome.Internal.D07.Ch15.QuadraticTowerIffIntersectionCoordinates
import Mathlib.FieldTheory.Minpoly.Finite
import Lean.Elab.Tactic.Omega

namespace D07.Ch15.QuadraticTowerIff

open D07.Ch15.StraightedgeCompass
open Specs.D07.Ch15.QuadraticTowerIff

/-- Every finite geometric history has all its points in one tower. -/
theorem construction_coordinates_tower {P : InitialData} {S : Set Point}
    (h : Construction P S) :
    ∃ M : IntermediateField ℚ ℝ, QuadraticTower (coordinateField P) M ∧
      ∀ p ∈ S, HasCoordinates M p := by
  induction h with
  | initial =>
    exact ⟨coordinateField P, .base, fun _ hp => coordinates_mem_coordinateField hp⟩
  | @step S p h hp ih =>
    obtain ⟨M, ht, hM⟩ := ih
    obtain ⟨d, hd, hf, hdeg, hx, hy⟩ :=
      QuadraticTowerIffIntersectionCoordinates.intersection_coordinates M S p hM hp
    let E := sqrtExtension M d
    refine ⟨E.restrictScalars ℚ, .step ht E hf hdeg, ?_⟩
    intro q hq
    rcases Set.mem_insert_iff.mp hq with rfl | hq
    · exact ⟨hx, hy⟩
    · obtain ⟨hx, hy⟩ := hM q hq
      exact ⟨E.algebraMap_mem ⟨q.1, hx⟩, E.algebraMap_mem ⟨q.2, hy⟩⟩

/-- This field records consequences of geometric constructions; its closure
laws are supplied by the proved geometric operations, not new primitives. -/
noncomputable def constructibleField (P : InitialData) : IntermediateField ℚ ℝ :=
  let F : Subfield ℝ :=
    { carrier := {a | IsConstructibleReal P a}
      zero_mem' := constructible_zero P
      one_mem' := constructible_one P
      add_mem' := fun ha hb => constructible_add P _ _ ha hb
      neg_mem' := fun ha => constructible_neg P _ ha
      mul_mem' := fun ha hb => constructible_mul P _ _ ha hb
      inv_mem' := by
        intro a ha
        by_cases hz : a = 0
        · simpa [hz] using constructible_zero P
        · change IsConstructibleReal P a⁻¹
          simpa only [one_div] using constructible_div P 1 a (constructible_one P) ha hz }
  F.toIntermediateField (fun q => SubfieldClass.ratCast_mem F q)

theorem coordinateField_le_constructibleField (P : InitialData) :
    coordinateField P ≤ constructibleField P := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro a (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
  · exact constructible_project_fst P p (isConstructible_of_mem hp)
  · exact constructible_snd_real (isConstructible_of_mem hp)

/-- Completing the square works for either real root, including a repeated
root. The equation is monic, and no sign choice is silently fixed. -/
theorem constructible_of_quadratic {P : InitialData} {x b c : ℝ}
    (hb : IsConstructibleReal P b) (hc : IsConstructibleReal P c)
    (hx : x ^ 2 + b * x + c = 0) : IsConstructibleReal P x := by
  let F := constructibleField P
  have hbF : b ∈ F := hb
  have hcF : c ∈ F := hc
  have hdF : b ^ 2 - 4 * c ∈ F :=
    F.sub_mem (pow_mem hbF 2) (F.mul_mem (F.natCast_mem 4) hcF)
  have hsq : (2 * x + b) ^ 2 = b ^ 2 - 4 * c := by nlinarith [hx]
  have hd : 0 ≤ b ^ 2 - 4 * c := hsq ▸ sq_nonneg (2*x+b)
  have hsF : Real.sqrt (b ^ 2 - 4 * c) ∈ F := constructible_sqrt P _ hdF hd
  have hs := Real.sq_sqrt hd
  have huF : 2 * x + b ∈ F := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsq.trans hs.symm) with he | he
    · exact he ▸ hsF
    · rw [he]; exact F.neg_mem hsF
  have he : x = ((2*x+b)-b)/2 := by ring
  rw [he]
  exact F.div_mem (F.sub_mem huF hbF) (F.natCast_mem 2)

/-- Every element of any real extension of degree at most two is obtained
from constructible base coefficients by the quadratic formula. -/
theorem quadratic_extension_constructible (P : InitialData)
    (M : IntermediateField ℚ ℝ) (hM : M ≤ constructibleField P)
    (E : IntermediateField M ℝ) [FiniteDimensional M E]
    (hdeg : Module.finrank M E ≤ 2) : E.restrictScalars ℚ ≤ constructibleField P := by
  intro x hx
  let u : E := ⟨x, hx⟩
  let f := minpoly M u
  have hi : IsIntegral M u := Algebra.IsIntegral.isIntegral u
  have hm : f.Monic := minpoly.monic hi
  have hn : 0 < f.natDegree := minpoly.natDegree_pos hi
  have hd : f.natDegree ≤ 2 := (minpoly.natDegree_le u).trans hdeg
  have hz : Polynomial.aeval x f = 0 := by
    change Polynomial.aeval (u : ℝ) f = 0
    rw [IntermediateField.aeval_coe]
    change ((Polynomial.aeval u f : E) : ℝ) = 0
    rw [show Polynomial.aeval u f = 0 from minpoly.aeval M u]
    rfl
  have hn' : f.natDegree = 1 ∨ f.natDegree = 2 := by omega
  rcases hn' with hn' | hn'
  · have he := hm.eq_X_add_C hn'
    rw [he] at hz
    simp only [Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C] at hz
    change x + ((f.coeff 0 : M) : ℝ) = 0 at hz
    have hx' : x = -((f.coeff 0 : M) : ℝ) := by linarith
    rw [hx']
    exact (constructibleField P).neg_mem (hM (f.coeff 0).2)
  · have hcoeff : f.coeff 2 = 1 := hn' ▸ hm.coeff_natDegree
    have he : f = Polynomial.X ^ 2 + Polynomial.C (f.coeff 1) * Polynomial.X +
        Polynomial.C (f.coeff 0) := by
      conv_lhs => rw [f.as_sum_range_C_mul_X_pow, hn']
      simp [Finset.sum_range_succ, hcoeff]
      ring
    rw [he] at hz
    simp only [Polynomial.aeval_add, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_mul, Polynomial.aeval_C] at hz
    change x ^ 2 + ((f.coeff 1 : M) : ℝ) * x + ((f.coeff 0 : M) : ℝ) = 0 at hz
    exact constructible_of_quadratic (hM (f.coeff 1).2) (hM (f.coeff 0).2) hz

/-- Induct over arbitrary finite real quadratic towers, allowing degree-one
steps and arbitrary real initial coordinates. -/
theorem tower_le_constructibleField {P : InitialData} {M : IntermediateField ℚ ℝ}
    (h : QuadraticTower (coordinateField P) M) : M ≤ constructibleField P := by
  induction h with
  | base => exact coordinateField_le_constructibleField P
  | step h E hf hd ih =>
    letI := hf
    exact quadratic_extension_constructible P _ ih E hd

theorem point_criterion : PointCriterion := by
  intro P p
  change IsConstructible P p ↔ _
  constructor
  · rintro ⟨S, hS, hp⟩
    obtain ⟨M, ht, hM⟩ := construction_coordinates_tower hS
    exact ⟨M, ht, hM p hp⟩
  · rintro ⟨M, ht, hx, hy⟩
    have hM := tower_le_constructibleField ht
    exact constructible_combine P p.1 p.2 (hM hx) (hM hy)

theorem real_criterion : RealCriterion := by
  intro P a
  constructor
  · intro ha
    obtain ⟨M, ht, hx, _⟩ := (point_criterion P (a,0)).mp ha
    exact ⟨M, ht, hx⟩
  · rintro ⟨M, ht, ha⟩
    exact (point_criterion P (a,0)).mpr ⟨M, ht, ha, M.zero_mem⟩

theorem common_tower_criterion : CommonTowerCriterion := by
  intro P a b
  constructor
  · rintro ⟨ha, hb⟩
    exact (point_criterion P (a,b)).mp (constructible_combine P a b ha hb)
  · rintro ⟨M, ht, ha, hb⟩
    exact ⟨(real_criterion P a).mpr ⟨M, ht, ha⟩,
      (real_criterion P b).mpr ⟨M, ht, hb⟩⟩

end D07.Ch15.QuadraticTowerIff
