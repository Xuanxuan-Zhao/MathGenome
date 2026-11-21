import MathGenome.Internal.Specs.D07.Ch15.DoubleCube
import MathGenome.Internal.D07.Ch11.Eisenstein
import MathGenome.Internal.D07.Ch15.DegreeObstruction

/-! The cubic volume equation has degree three over the rational coordinate
field. This contradicts the power-of-two degree forced by the actual finite
straightedge-and-compass construction histories.
-/
namespace D07.Ch15.DoubleCube

open Polynomial IntermediateField StraightedgeCompass
open Specs.D07.Ch15.DoubleCube

theorem cube_polynomial_irreducible : CubePolynomialIrreducible := by
  exact (D07.Ch11.Eisenstein.xPowSubPrime 2 3 Nat.prime_two (by decide)).2

theorem cube_root_degree : CubeRootDegree := by
  intro a ha
  have hm : (X ^ 3 - C (2 : ℚ)).Monic := monic_X_pow_sub_C _ (by decide)
  have he : aeval a (X ^ 3 - C (2 : ℚ)) = 0 := by simp [ha]
  have hi : IsIntegral ℚ a := ⟨_, hm, he⟩
  have hp : minpoly ℚ a = X ^ 3 - C (2 : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic cube_polynomial_irreducible he hm).symm
  refine ⟨hi, hp, ?_⟩
  rw [adjoin.finrank hi, hp, natDegree_X_pow_sub_C]

/-- Rational initial coordinates generate precisely the embedded rational
field, rather than a larger field supplied as extra construction data. -/
lemma coordinateField_eq_bot (P : InitialData)
    (hP : ∀ p ∈ P.points, ∃ x y : ℚ, p = ((x : ℝ), (y : ℝ))) :
    coordinateField P = ⊥ := by
  apply le_antisymm _ bot_le
  apply adjoin_le_iff.mpr
  rintro t (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
  · obtain ⟨x, y, rfl⟩ := hP p hp
    exact mem_bot.mpr ⟨x, rfl⟩
  · obtain ⟨x, y, rfl⟩ := hP p hp
    exact mem_bot.mpr ⟨y, rfl⟩

/-- The bottom real subfield is canonically isomorphic to ℚ. Transporting
Eisenstein's cubic along that equivalence keeps its degree equal to three. -/
lemma cube_root_degree_over_bot (a : ℝ) (ha : a ^ 3 = 2) :
    IsIntegral (⊥ : IntermediateField ℚ ℝ) a ∧
      Module.finrank (⊥ : IntermediateField ℚ ℝ)
        (⊥ : IntermediateField ℚ ℝ)⟮a⟯ = 3 := by
  let K : IntermediateField ℚ ℝ := ⊥
  let e := (botEquiv ℚ ℝ).symm
  have hirr : Irreducible (X ^ 3 - C (2 : K)) := by
    have h := (MulEquiv.irreducible_iff (Polynomial.mapEquiv e.toRingEquiv)).mpr
      cube_polynomial_irreducible
    simpa using h
  have hm : (X ^ 3 - C (2 : K)).Monic := monic_X_pow_sub_C _ (by decide)
  have he : aeval a (X ^ 3 - C (2 : K)) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    change a ^ 3 - 2 = 0
    rw [ha, sub_self]
  have hi : IsIntegral K a := ⟨_, hm, he⟩
  refine ⟨hi, ?_⟩
  rw [adjoin.finrank hi,
    ← minpoly.eq_of_irreducible_of_monic hirr he hm, natDegree_X_pow_sub_C]

theorem cube_root_not_constructible : CubeRootNotConstructible := by
  intro P hP a ha hc
  have hK := coordinateField_eq_bot P hP
  obtain ⟨hi, hd⟩ := cube_root_degree_over_bot a ha
  have hiP : IsIntegral (coordinateField P) a := hK ▸ hi
  obtain ⟨n, hn⟩ := DegreeObstruction.geometric_necessary_degree P a hiP hc
  change Module.finrank (coordinateField P) (coordinateField P)⟮a⟯ = 2 ^ n at hn
  rw [hK, hd] at hn
  have hdiv : 3 ∣ 2 ^ n := hn ▸ dvd_refl 3
  have : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) hdiv
  norm_num at this

theorem no_doubling : NoDoubling := by
  rintro P hP ⟨a, _, hc, ha⟩
  exact cube_root_not_constructible P hP a ha hc

/-- Compass transfer and the proved geometric field operations make any
distance between constructible endpoints a constructible real length. -/
lemma constructible_distance {P : InitialData} {p q : Point}
    (hp : IsConstructible P p) (hq : IsConstructible P q) :
    IsConstructibleReal P (Real.sqrt (squaredDistance p q)) := by
  have hx := constructible_sub (constructible_project_fst P p hp)
    (constructible_project_fst P q hq)
  have hy := constructible_sub (constructible_snd_real hp) (constructible_snd_real hq)
  apply constructible_sqrt P _
  · simpa only [squaredDistance, pow_two] using
      constructible_add P _ _ (constructible_mul P _ _ hx hx)
        (constructible_mul P _ _ hy hy)
  · exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem no_doubling_by_segment : NoDoublingBySegment := by
  rintro P hP ⟨p, q, hp, hq, hv⟩
  exact cube_root_not_constructible P hP _ hv (constructible_distance hp hq)

end D07.Ch15.DoubleCube
