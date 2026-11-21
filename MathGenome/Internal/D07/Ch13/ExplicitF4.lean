import MathGenome.Internal.Specs.D07.Ch13.ExplicitF4
import MathGenome.Internal.D07.Ch11.LowDegreeIrreducible
import MathGenome.Internal.D07.Ch13.CoordinatesArithmetic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The explicit polynomial quotient with four elements (K07.13.explicit_F4). -/

noncomputable section

namespace D07.Ch13.ExplicitF4
open Polynomial
open Specs.D07.Ch13.ExplicitF4

abbrev polynomial : ModulusType := modulus
abbrev fourElementField : FieldType := F4
abbrev generator : GeneratorType := u

theorem evaluation_values : EvaluationValues := by
  intro a
  simp only [modulus, eval_add, eval_pow, eval_X, eval_one]
  fin_cases a <;> decide

theorem monic_degree : MonicDegree := by
  have hd : modulus.natDegree = 2 := by
    simpa [modulus] using
      (Polynomial.natDegree_quadratic (R := ZMod 2) (a := 1) (b := 1) (c := 1)
        (by decide : (1 : ZMod 2) ≠ 0))
  refine ⟨?_, hd⟩
  have hl : modulus.leadingCoeff = 1 := by
    simpa [modulus] using
      (Polynomial.leadingCoeff_quadratic (R := ZMod 2) (a := 1) (b := 1) (c := 1)
        (by decide : (1 : ZMod 2) ≠ 0))
  exact hl

theorem irreducibility : Irreducibility := by
  apply (Ch11.LowDegreeIrreducible.degree_two_or_three_iff_no_root
    (ZMod 2) modulus (Or.inl ?_)).mpr
  · intro a
    rw [evaluation_values a]
    decide
  · rw [degree_eq_natDegree monic_degree.1.ne_zero, monic_degree.2]
    rfl

theorem field_cardinality : FieldCardinality := by
  change IsField F4 ∧ Finite F4 ∧ Nat.card F4 = 4
  simpa only [show 2 ^ 2 = (4 : ℕ) from rfl] using
    Ch13.CoordinatesArithmetic.fieldCardinality (ZMod 2) 2 2 modulus
      (by simp) monic_degree.2 monic_degree.1 irreducibility

theorem unique_coordinates : UniqueCoordinates := by
  obtain ⟨e, he⟩ := Ch13.CoordinatesArithmetic.coordinateBijection
    (ZMod 2) 2 modulus monic_degree.2 monic_degree.1 irreducibility
  have hec (a : Fin 2 → ZMod 2) : e a = coord (a 0, a 1) := by
    rw [he]
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      mul_one, map_add, map_mul]
    rfl
  constructor
  · intro ab cd h
    have hm (ab : ZMod 2 × ZMod 2) : e ![ab.1, ab.2] = coord ab := by
      exact hec ![ab.1, ab.2]
    have hvec := e.injective ((hm ab).trans (h.trans (hm cd).symm))
    exact Prod.ext (congrFun hvec 0) (congrFun hvec 1)
  · intro x
    obtain ⟨a, rfl⟩ := e.surjective x
    exact ⟨(a 0, a 1), (hec a).symm⟩

theorem enumeration : Enumeration := by
  intro x
  obtain ⟨⟨a, b⟩, rfl⟩ := unique_coordinates.2 x
  have h01 (z : ZMod 2) : z = 0 ∨ z = 1 := by
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl <;>
    simp [coord, add_comm]

theorem distinctness : Distinctness := by
  have hc : Function.Injective coord := unique_coordinates.1
  have hbase : ([((0,0) : ZMod 2 × ZMod 2), (1,0), (0,1), (1,1)]).Pairwise
      (fun a b => coord a ≠ coord b) := by
    have h : ([((0,0) : ZMod 2 × ZMod 2), (1,0), (0,1), (1,1)]).Pairwise (· ≠ ·) :=
      by decide
    exact h.imp (fun hab heq => hab (hc heq))
  have hs := List.pairwise_map.mpr hbase
  change ([coord (0,0), coord (1,0), coord (0,1), coord (1,1)]).Pairwise (· ≠ ·) at hs
  simpa only [Distinctness, coord, map_zero, map_one, zero_mul, one_mul, add_zero,
    zero_add, add_comm] using hs

theorem arithmetic_identities : ArithmeticIdentities := by
  have htwo : (2 : F4) = 0 := by
    have h := congrArg (algebraMap (ZMod 2) F4) (show (2 : ZMod 2) = 0 by decide)
    simpa only [map_ofNat, map_zero] using h
  have hdouble (x : F4) : x + x = 0 := by
    calc
      x + x = (2 : F4) * x := (two_mul x).symm
      _ = 0 := by rw [htwo, zero_mul]
  have hr : u ^ 2 + u + 1 = 0 := by
    have h := AdjoinRoot.eval₂_root modulus
    change (X ^ 2 + X + 1 : Polynomial (ZMod 2)).eval₂ (AdjoinRoot.of modulus) u = 0 at h
    rw [eval₂_add, eval₂_add, eval₂_pow, eval₂_X, eval₂_one] at h
    exact h
  have hu2 : u ^ 2 = u + 1 := by
    have h := congrArg (fun x : F4 => x + (u + 1)) hr
    have hcancel : u ^ 2 + u + 1 + (u + 1) = u ^ 2 := by
      calc
        _ = u ^ 2 + (u + u) + (1 + 1) := by ring
        _ = _ := by rw [hdouble u, hdouble 1]; simp
    simpa only [hcancel, zero_add] using h
  refine ⟨hu2, ?_, ?_⟩
  · calc
      u * (u + 1) = u ^ 2 + u := by ring
      _ = (u + u) + 1 := by rw [hu2]; ring
      _ = 1 := by rw [hdouble]; simp
  · calc
      (u + 1) ^ 2 = u ^ 2 + (u + u) + 1 := by ring
      _ = (u + 1) + 0 + 1 := by rw [hu2, hdouble]
      _ = u + (1 + 1) := by ring
      _ = u := by rw [hdouble]; simp

theorem coordinate_addition : CoordinateAddition := by
  intro a b c d
  simp only [coord, map_add]
  ring

theorem coordinate_multiplication : CoordinateMultiplication := by
  intro a b c d
  simp only [coord, map_add, map_mul]
  calc
    _ = algebraMap (ZMod 2) F4 a * algebraMap (ZMod 2) F4 c +
        (algebraMap (ZMod 2) F4 a * algebraMap (ZMod 2) F4 d +
        algebraMap (ZMod 2) F4 b * algebraMap (ZMod 2) F4 c) * u +
        (algebraMap (ZMod 2) F4 b * algebraMap (ZMod 2) F4 d) * u ^ 2 := by ring
    _ = _ := by rw [arithmetic_identities.1]; ring

theorem multiplicative_generator : MultiplicativeGenerator := by
  have hd : ([0, 1, u, u + 1] : List F4).Pairwise (· ≠ ·) := distinctness
  have h0 := (List.pairwise_cons.mp hd).1
  have h1 := (List.pairwise_cons.mp (List.pairwise_cons.mp hd).2).1
  have h10 : (1 : F4) ≠ 0 := (h0 1 (by simp)).symm
  have hu0 : u ≠ 0 := (h0 u (by simp)).symm
  have hu1 : u ≠ 1 := (h1 u (by simp)).symm
  have hup0 : u + 1 ≠ 0 := (h0 (u + 1) (by simp)).symm
  have hp : u ^ 3 = 1 := by
    calc
      u ^ 3 = u * u ^ 2 := by ring
      _ = 1 := by rw [arithmetic_identities.1, arithmetic_identities.2.1]
  refine ⟨hp, orderOf_eq_prime hp hu1, ?_⟩
  intro x
  constructor
  · intro hx
    rcases enumeration x with h | h | h | h
    · exact (hx h).elim
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
    · exact ⟨2, by simpa [arithmetic_identities.1] using h⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [hu0, arithmetic_identities.1, hup0, h10]

end D07.Ch13.ExplicitF4
