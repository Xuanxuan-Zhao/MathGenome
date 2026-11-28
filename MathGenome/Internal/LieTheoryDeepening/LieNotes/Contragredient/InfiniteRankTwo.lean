import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.MinimalRealization
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.ReflectionAutomorphisms
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.InfiniteRankTwo
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The infinite rank-two root orbit of Example KM07. -/

namespace LieNotes.Contragredient.InfiniteRankTwo

open CartanQuotient
open ReflectionAutomorphisms (realRoot_multiplicity)

noncomputable section

universe v

abbrev cartanMatrix := Specs.LieNotes.Contragredient.InfiniteRankTwo.cartanMatrix
abbrev reflectionProduct := Specs.LieNotes.Contragredient.InfiniteRankTwo.reflectionProduct
abbrev orbitWeight {a b : ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H]
    (R : Realization (cartanMatrix a b) H) :=
  Specs.LieNotes.Contragredient.InfiniteRankTwo.orbitWeight R

variable {a b : ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H]

theorem isCartanMatrix (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    IsGeneralizedCartanMatrix (cartanMatrix a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> rfl
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change -a ≤ 0
      omega
    · change -b ≤ 0
      omega
    · exact (hij rfl).elim
  · intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · change -a = 0 ↔ -b = 0
      omega
    · change -b = 0 ↔ -a = 0
      omega
    · rfl

private theorem corootPairing_fin_two (i : Fin 2) (q : Q (Fin 2)) :
    corootPairing (cartanMatrix a b) i q =
      q 0 * cartanMatrix a b i 0 + q 1 * cartanMatrix a b i 1 := by
  change (Finsupp.linearCombination ℤ (cartanMatrix a b i)) q = _
  rw [Finsupp.linearCombination_apply,
    Finsupp.sum_fintype q (fun j x ↦ x • cartanMatrix a b i j) (fun _ ↦ zero_smul _ _),
    Fin.sum_univ_two]
  rfl

theorem reflectionProduct_coordinates (a b : ℤ) (q : Q (Fin 2)) :
    reflectionProduct a b q 0 = (a * b - 1) * q 0 - a * q 1 ∧
    reflectionProduct a b q 1 = b * q 0 - q 1 := by
  let r := rootReflection (cartanMatrix a b)
  change r 0 (r 1 q) 0 = _ ∧ r 0 (r 1 q) 1 = _
  simp only [r, rootReflection_apply, Finsupp.sub_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide),
    Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide),
    sub_zero, corootPairing_fin_two]
  change q 0 - (q 0 * 2 + (q 1 - (q 0 * -b + q 1 * 2)) * -a) = _ ∧
    q 1 - (q 0 * -b + q 1 * 2) = _
  constructor <;> ring

theorem reflectionProduct_det_trace (a b : ℤ) :
    let T : Matrix (Fin 2) (Fin 2) ℤ := !![a * b - 1, -a; b, -1]
    T.det = 1 ∧ T.trace = a * b - 2 := by
  dsimp only
  rw [Matrix.det_fin_two_of, Matrix.trace_fin_two_of]
  constructor <;> ring

/-- The characteristic identity on the root lattice, computed in the two coordinates. -/
private theorem reflectionProduct_apply_apply (q : Q (Fin 2)) :
    reflectionProduct a b (reflectionProduct a b q) =
      (a * b - 2) • reflectionProduct a b q - q := by
  have hx (p : Q (Fin 2)) := (reflectionProduct_coordinates a b p).1
  have hy (p : Q (Fin 2)) := (reflectionProduct_coordinates a b p).2
  ext i
  fin_cases i
  · change reflectionProduct a b (reflectionProduct a b q) 0 =
      (a * b - 2) * reflectionProduct a b q 0 - q 0
    simp only [hx, hy]
    ring
  · change reflectionProduct a b (reflectionProduct a b q) 1 =
      (a * b - 2) * reflectionProduct a b q 1 - q 1
    simp only [hx, hy]
    ring

theorem reflectionProduct_at_four (a b : ℤ) (hab : a * b = 4) :
    (reflectionProduct a b - 1) ^ 2 = 0 ∧
      (reflectionProduct a b - 1) (simpleDegree 0) ≠ 0 := by
  constructor
  · apply LinearMap.ext
    intro q
    have ht : a * b - 2 = 2 := by omega
    simp only [pow_two, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      map_sub, reflectionProduct_apply_apply, ht, two_smul, LinearMap.zero_apply]
    abel
  · intro h
    have hcoord := DFunLike.congr_fun h (1 : Fin 2)
    have hb : b ≠ 0 := by
      intro hzero
      simp [hzero] at hab
    change reflectionProduct a b (simpleDegree 0) 1 - simpleDegree (0 : Fin 2) 1 = 0 at hcoord
    rw [(reflectionProduct_coordinates a b (simpleDegree 0)).2] at hcoord
    exact hb (by simpa [Specs.LieNotes.Contragredient.CartanData.simpleDegree] using hcoord)

private def orbitDegree (a b : ℤ) (n : ℕ) : Q (Fin 2) :=
  (reflectionProduct a b ^ n) (simpleDegree 0)

private theorem orbitDegree_succ (a b : ℤ) (n : ℕ) :
    orbitDegree a b (n + 1) = reflectionProduct a b (orbitDegree a b n) := by
  rw [orbitDegree, pow_succ', Module.End.mul_apply, orbitDegree]

/-- The second coordinate grows strictly, including at the boundary product four. -/
private theorem orbitDegree_second_strictMono (hb : 0 < b) (hab : 4 ≤ a * b) :
    StrictMono (fun n ↦ orbitDegree a b n 1) := by
  let y := fun n ↦ orbitDegree a b n 1
  have hy0 : y 0 = 0 := by
    simp [y, orbitDegree, Specs.LieNotes.Contragredient.CartanData.simpleDegree]
  have hy1 : y 1 = b := by
    change orbitDegree a b (0 + 1) 1 = b
    rw [orbitDegree_succ, (reflectionProduct_coordinates a b _).2]
    simp [orbitDegree, Specs.LieNotes.Contragredient.CartanData.simpleDegree]
  have recurrence (n : ℕ) : y (n + 2) = (a * b - 2) * y (n + 1) - y n := by
    change orbitDegree a b ((n + 1) + 1) 1 =
      (a * b - 2) * orbitDegree a b (n + 1) 1 - orbitDegree a b n 1
    rw [orbitDegree_succ a b (n + 1), orbitDegree_succ a b n, reflectionProduct_apply_apply]
    rfl
  suffices step : ∀ n, 0 ≤ y n ∧ y n < y (n + 1) from
    strictMono_nat_of_lt_succ fun n ↦ (step n).2
  intro n
  induction n with
  | zero => change 0 ≤ y 0 ∧ y 0 < y 1; omega
  | succ n ih =>
    have hnonneg : 0 ≤ y (n + 1) := ih.1.trans ih.2.le
    refine ⟨hnonneg, ?_⟩
    have hmul := mul_le_mul_of_nonneg_right (show (2 : ℤ) ≤ a * b - 2 by omega) hnonneg
    have hnext := recurrence n
    change y (n + 1) < y (n + 2)
    omega

private theorem rootWeight_orbitDegree (R : Realization (cartanMatrix a b) H) (n : ℕ) :
    R.rootWeight (orbitDegree a b n) = orbitWeight R n := by
  induction n with
  | zero =>
    simp [orbitDegree, orbitWeight, Specs.LieNotes.Contragredient.InfiniteRankTwo.orbitWeight]
  | succ n ih =>
    rw [orbitDegree_succ]
    change R.rootWeight (rootReflection (cartanMatrix a b) 0
      (rootReflection (cartanMatrix a b) 1 (orbitDegree a b n))) = _
    rw [Realization.rootWeight_rootReflection, Realization.rootWeight_rootReflection, ih]
    simp only [orbitWeight, Specs.LieNotes.Contragredient.InfiniteRankTwo.orbitWeight,
      pow_succ', Module.End.mul_apply]

private theorem orbitWeight_rank (hA : IsGeneralizedCartanMatrix (cartanMatrix a b))
    (R : Realization (cartanMatrix a b) H) (n : ℕ) :
    Module.rank ℂ (weightSpace (cartanAdjoint R) (orbitWeight R n)) = 1 := by
  have representable (m : ℕ) : ∃ w : List (Fin 2),
      w.foldr (fun i β ↦ R.weightReflection i β) (R.α 0) = orbitWeight R m := by
    induction m with
    | zero =>
      exact ⟨[], by simp [orbitWeight, Specs.LieNotes.Contragredient.InfiniteRankTwo.orbitWeight]⟩
    | succ m ih =>
      obtain ⟨w, hw⟩ := ih
      refine ⟨0 :: 1 :: w, ?_⟩
      simp only [List.foldr_cons, hw, orbitWeight,
        Specs.LieNotes.Contragredient.InfiniteRankTwo.orbitWeight, pow_succ', Module.End.mul_apply]
  obtain ⟨w, hw⟩ := representable n
  rw [← hw]
  exact realRoot_multiplicity hA R 0 w

theorem infiniteRootOrbit (ha : 0 < a) (hb : 0 < b) (hab : 4 ≤ a * b)
    (R : Realization (cartanMatrix a b) H) :
    Function.Injective (orbitWeight R) ∧ (∀ n, orbitWeight R n ≠ 0) ∧
      (∀ n, weightSpace (cartanAdjoint R) (orbitWeight R n) ≠ ⊥) ∧
      iSupIndep (fun n ↦ weightSpace (cartanAdjoint R) (orbitWeight R n)) := by
  have hA := isCartanMatrix a b ha hb
  have hinj : Function.Injective (orbitWeight R) := by
    intro m n hmn
    rw [← rootWeight_orbitDegree R m, ← rootWeight_orbitDegree R n] at hmn
    exact (orbitDegree_second_strictMono hb hab).injective
      (DFunLike.congr_fun (R.rootWeight_injective hmn) 1)
  refine ⟨hinj, ?_, ?_, (weightSpace_iSupIndep (cartanAdjoint R)).comp hinj⟩
  · have hp : Function.Injective
        (R.weightReflection 0 * R.weightReflection 1 : Module.End ℂ (Module.Dual ℂ H)) :=
      (R.weightReflection_involutive hA 0).injective.comp
        (R.weightReflection_involutive hA 1).injective
    intro n hn
    change ((R.weightReflection 0 * R.weightReflection 1) ^ n) (R.α 0) = 0 at hn
    rw [← map_zero ((R.weightReflection 0 * R.weightReflection 1) ^ n)] at hn
    exact R.α_independent.ne_zero 0 (Module.End.iterate_injective hp n hn)
  · intro n hn
    have hr := orbitWeight_rank hA R n
    exact zero_ne_one ((Submodule.rank_eq_zero.mpr hn).symm.trans hr)

theorem infiniteDimensional (ha : 0 < a) (hb : 0 < b) (hab : 4 ≤ a * b)
    (R : Realization (cartanMatrix a b) H) : ¬ FiniteDimensional ℂ (Algebra R) := by
  obtain ⟨_, _, hne, hind⟩ := infiniteRootOrbit ha hb hab R
  intro hfinite
  let _ := hfinite
  let _ := hind.fintypeNeBotOfFiniteDimensional
  let embed (n : ℕ) : {n : ℕ // weightSpace (cartanAdjoint R) (orbitWeight R n) ≠ ⊥} :=
    ⟨n, hne n⟩
  exact Infinite.not_finite (Finite.of_injective embed fun _ _ h ↦ congrArg Subtype.val h)

theorem minimalInfiniteDimensional (ha : 0 < a) (hb : 0 < b) (hab : 4 ≤ a * b) :
    ∃ (H : Type) (add : AddCommGroup H) (mod : @Module ℂ H _ add.toAddCommMonoid),
      letI := add
      letI := mod
      ∃ R : Realization (cartanMatrix a b) H,
        R.IsMinimal ∧ ¬ FiniteDimensional ℂ (Algebra R) := by
  obtain ⟨H, add, mod, R, hR⟩ := exists_minimal_realization (isCartanMatrix a b ha hb)
  exact ⟨H, add, mod, R, hR, infiniteDimensional ha hb hab R⟩

end
end LieNotes.Contragredient.InfiniteRankTwo
