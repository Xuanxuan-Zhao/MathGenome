import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.Actions
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.ThreeSL2Vectors
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace RepTheorySurvey.Invariants.ThreeSL2Vectors

noncomputable section

open Specs.ThreeSL2Vectors hiding action bracket bracketMap
open MvPolynomial

abbrev action {k : Type*} [Field k] [Infinite k] :
    GroupAlgebraAction k (SL₂ k) (Coordinates k) := Specs.ThreeSL2Vectors.action
abbrev bracket {k : Type*} [Field k] : Fin 3 → Coordinates k :=
  Specs.ThreeSL2Vectors.bracket

abbrev bracketMap {k : Type*} [Field k] : BracketPolynomials k →ₐ[k] Coordinates k :=
  Specs.ThreeSL2Vectors.bracketMap

variable {k : Type*} [Field k]

private def detAt (v : Triples k) (i j : Fin 3) : k :=
  v 0 i * v 1 j - v 1 i * v 0 j

@[simp] private theorem eval_minor (v : Triples k) (i j : Fin 3) :
    evalAt v (minor i j) = detAt v i j := by
  simp [minor, detAt]

private theorem detAt_act (g : SL₂ k) (v : Triples k) (i j : Fin 3) :
    detAt (act g v) i j = detAt v i j := by
  calc
    detAt (act g v) i j = g.val.det * detAt v i j := by
      simp only [detAt, act, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
      ring
    _ = detAt v i j := by rw [Matrix.SpecialLinearGroup.det_coe, one_mul]

private def normal (a b c : k) : Triples k :=
  !![1, 0, -c / a; 0, a, b]

/-- Normalize two independent columns by a determinant-one matrix. -/
private theorem exists_normalize (v : Triples k) (h : detAt v 0 1 ≠ 0) :
    ∃ g : SL₂ k, act g v = normal (detAt v 0 1) (detAt v 0 2) (detAt v 1 2) := by
  let d := detAt v 0 1
  let m : Matrix (Fin 2) (Fin 2) k := !![v 1 1 / d, -v 0 1 / d; -v 1 0, v 0 0]
  have hm : m.det = 1 := by
    simp [m, Matrix.det_fin_two]
    field_simp [show d ≠ 0 from h]
    dsimp [d, detAt]
    ring
  refine ⟨⟨m, hm⟩, Matrix.ext fun i j ↦ ?_⟩
  fin_cases i <;> fin_cases j <;>
    simp [act, m, normal, Matrix.mul_apply, Fin.sum_univ_two] <;>
    (try field_simp [show d ≠ 0 from h]) <;> (try dsimp [d, detAt]) <;> ring

private theorem eval_substitute {ι : Type*} (p : ι → Coordinates k) (v : Triples k)
    (q : MvPolynomial ι k) :
    evalAt v (aeval p q) = eval (fun i ↦ evalAt v (p i)) q := by
  exact comp_aeval_apply p (aeval fun i : Fin 2 × Fin 3 ↦ v i.1 i.2) q

private theorem normal_brackets (t : Fin 3 → k) (ht : t 0 ≠ 0) :
    (fun i ↦ evalAt (normal (t 0) (t 1) (t 2)) (bracket i)) = t := by
  funext i
  fin_cases i <;> simp [bracket, Specs.ThreeSL2Vectors.bracket, detAt, normal]
  field_simp [ht]

private theorem bracketMap_injective [Infinite k] : Function.Injective (bracketMap (k := k)) := by
  intro q r h
  apply mul_left_cancel₀ (X_ne_zero (R := k) (0 : Fin 3))
  apply MvPolynomial.funext
  intro t
  simp only [map_mul, eval_X]
  by_cases ht : t 0 = 0
  · simp [ht]
  · have he := congrArg (evalAt (normal (t 0) (t 1) (t 2))) h
    change evalAt (normal (t 0) (t 1) (t 2)) (aeval bracket q) =
      evalAt (normal (t 0) (t 1) (t 2)) (aeval bracket r) at he
    simp only [eval_substitute, normal_brackets t ht] at he
    rw [he]

theorem bracket_injective (k : Type*) [Field k] [IsAlgClosed k] :
    Function.Injective (bracketMap (k := k)) :=
  bracketMap_injective

private def reorder (σ : Equiv.Perm (Fin 3)) (v : Triples k) : Triples k :=
  Matrix.of fun i j ↦ v i (σ j)

omit [Field k] in
@[simp] private theorem reorder_inv (σ : Equiv.Perm (Fin 3)) (v : Triples k) :
    reorder σ.symm (reorder σ v) = v := by
  apply Matrix.ext
  intro i j
  simp [reorder]

private theorem reorder_act (σ : Equiv.Perm (Fin 3)) (g : SL₂ k) (v : Triples k) :
    reorder σ (act g v) = act g (reorder σ v) := rfl

private def normalNumerators : Matrix (Fin 2) (Fin 3) (BracketPolynomials k) :=
  !![X 0, 0, -X 2; 0, X 0 ^ 2, X 0 * X 1]

private theorem eval_normalNumerators (t : Fin 3 → k) (ht : t 0 ≠ 0) (i : Fin 2) (j : Fin 3) :
    eval t (normalNumerators i j) = t 0 * normal (t 0) (t 1) (t 2) i j := by
  fin_cases i <;> fin_cases j <;> simp [normalNumerators, normal, pow_two]
  field_simp [ht]

/-- A polynomial on the normal form has a single power of the first bracket as denominator. -/
private theorem clear_normal_denominators (σ : Equiv.Perm (Fin 3)) (f : Coordinates k) :
    ∃ n : ℕ, ∃ q : BracketPolynomials k, ∀ (t : Fin 3 → k), t 0 ≠ 0 →
      t 0 ^ n * evalAt (reorder σ.symm (normal (t 0) (t 1) (t 2))) f = eval t q := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    exact ⟨0, C a, fun t _ ↦ by simp⟩
  | add f h hf hh =>
    obtain ⟨m, p, hp⟩ := hf
    obtain ⟨n, q, hq⟩ := hh
    refine ⟨m + n, X 0 ^ n * p + X 0 ^ m * q, fun t ht ↦ ?_⟩
    simp only [map_add, map_mul, map_pow, eval_X, ← hp t ht, ← hq t ht, pow_add]
    ring
  | mul_X f i hf =>
    obtain ⟨n, q, hq⟩ := hf
    refine ⟨n + 1, q * normalNumerators i.1 (σ.symm i.2), fun t ht ↦ ?_⟩
    simp only [map_mul, eval_X, eval_normalNumerators t ht, ← hq t ht, pow_succ,
      reorder, Matrix.of_apply]
    ring

private def orderedBrackets (σ : Equiv.Perm (Fin 3)) : Fin 3 → Coordinates k :=
  ![minor (σ 0) (σ 1), minor (σ 0) (σ 2), minor (σ 1) (σ 2)]

private theorem eval_orderedBrackets (σ : Equiv.Perm (Fin 3)) (v : Triples k) :
    (fun i ↦ evalAt v (orderedBrackets σ i)) =
      ![detAt (reorder σ v) 0 1, detAt (reorder σ v) 0 2, detAt (reorder σ v) 1 2] := by
  funext i
  fin_cases i <;> simp [orderedBrackets, detAt, reorder]

private theorem ordered_first_ne_zero (σ : Equiv.Perm (Fin 3)) :
    (orderedBrackets σ 0 : Coordinates k) ≠ 0 := by
  let v := normal (1 : k) 0 0
  intro h
  have he := congrArg (evalAt (reorder σ.symm v)) h
  change evalAt (reorder σ.symm v) (orderedBrackets σ 0) =
    evalAt (reorder σ.symm v) 0 at he
  have heval : evalAt (reorder σ.symm v) (orderedBrackets σ 0) =
      detAt (reorder σ (reorder σ.symm v)) 0 1 :=
    congrFun (eval_orderedBrackets σ (reorder σ.symm v)) 0
  have hv : reorder σ (reorder σ.symm v) = v := by
    simpa only [Equiv.symm_symm] using reorder_inv σ.symm v
  rw [heval, hv] at he
  simp [v, normal, detAt] at he

private theorem fixed_iff [Infinite k] (f : Coordinates k) :
    f ∈ (action (k := k)).fixedSubalgebra ↔ ∀ g v, evalAt (act g v) f = evalAt v f := by
  change (∀ g : SL₂ k, pullback g f = f) ↔ _
  constructor
  · intro hf g v
    have he : evalAt v (pullback g⁻¹ f) = evalAt v f := congrArg (evalAt v) (hf g⁻¹)
    simpa [eval_pullback] using he
  · intro hf g
    apply evalAt_ext
    intro v
    rw [eval_pullback, hf]

private theorem bracket_mem [Infinite k] (i : Fin 3) :
    bracket (k := k) i ∈ (action (k := k)).fixedSubalgebra := by
  apply (fixed_iff _).mpr
  intro g v
  fin_cases i <;>
    simp [bracket, Specs.ThreeSL2Vectors.bracket, detAt_act]

/-- The numerator identity holds in the whole polynomial ring by evaluation. -/
private theorem chart_eq [Infinite k] (σ : Equiv.Perm (Fin 3)) {f : Coordinates k}
    (hf : f ∈ (action (k := k)).fixedSubalgebra) :
    ∃ n : ℕ, ∃ q : BracketPolynomials k,
      (orderedBrackets σ 0) ^ n * f = aeval (orderedBrackets σ) q := by
  obtain ⟨n, q, hq⟩ := clear_normal_denominators σ f
  refine ⟨n, q, mul_left_cancel₀ (ordered_first_ne_zero σ) (evalAt_ext fun v ↦ ?_)⟩
  let t : Fin 3 → k := fun i ↦ evalAt v (orderedBrackets σ i)
  simp only [map_mul, map_pow, eval_substitute]
  change t 0 * (t 0 ^ n * evalAt v f) = t 0 * eval t q
  by_cases ht : t 0 = 0
  · simp [ht]
  · have h0 : t 0 = detAt (reorder σ v) 0 1 :=
      congrFun (eval_orderedBrackets σ v) 0
    have h1 : t 1 = detAt (reorder σ v) 0 2 :=
      congrFun (eval_orderedBrackets σ v) 1
    have h2 : t 2 = detAt (reorder σ v) 1 2 :=
      congrFun (eval_orderedBrackets σ v) 2
    obtain ⟨g, hg⟩ := exists_normalize (reorder σ v) (h0 ▸ ht)
    rw [← reorder_act, ← h0, ← h1, ← h2] at hg
    have ha := congrArg (reorder σ.symm) hg
    rw [reorder_inv] at ha
    rw [← (fixed_iff f).mp hf g v, ha, hq t ht]

private theorem minor_flip (i j : Fin 3) :
    (minor j i : Coordinates k) = -minor i j := by
  unfold minor
  ring

private theorem orderedBrackets_swap :
    (orderedBrackets (Equiv.swap (1 : Fin 3) 2) : Fin 3 → Coordinates k) =
      ![bracket 1, bracket 0, -bracket 2] := by
  funext i
  fin_cases i <;>
    simp [orderedBrackets, bracket, Specs.ThreeSL2Vectors.bracket, Equiv.swap_apply_def,
      show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide]
  exact minor_flip 1 2

@[simp] private theorem bracketMap_X (i : Fin 3) :
    bracketMap (X i : BracketPolynomials k) = bracket i :=
  aeval_X _ _

private theorem exists_bracket_polynomial [Infinite k] {f : Coordinates k}
    (hf : f ∈ (action (k := k)).fixedSubalgebra) :
    ∃ p : BracketPolynomials k, bracketMap p = f := by
  obtain ⟨m, q, hq⟩ := chart_eq (Equiv.refl _) hf
  change bracket 0 ^ m * f = bracketMap q at hq
  obtain ⟨n, r, hr⟩ := chart_eq (Equiv.swap 1 2) hf
  rw [orderedBrackets_swap] at hr
  change bracket 1 ^ n * f = aeval ![bracket 1, bracket 0, -bracket 2] r at hr
  let s : BracketPolynomials k := aeval (![X 1, X 0, -X 2] : Fin 3 → BracketPolynomials k) r
  have hs : bracket 1 ^ n * f = bracketMap s := by
    have hmaps :
        bracketMap.comp (aeval (![X 1, X 0, -X 2] : Fin 3 → BracketPolynomials k)) =
          aeval ![bracket 1, bracket 0, -bracket 2] := by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i <;> simp
    rw [hr, ← hmaps]
    rfl
  have cross : (X 1 : BracketPolynomials k) ^ n * q = X 0 ^ m * s := by
    apply bracketMap_injective
    simp only [map_mul, map_pow, bracketMap_X, ← hq, ← hs]
    ac_rfl
  have prime : Prime (X 0 : BracketPolynomials k) := X_prime
  have hndvd : ¬ (X 0 : BracketPolynomials k) ∣ X 1 ^ n := by
    intro h
    have h01 := X_dvd_X.mp (prime.dvd_of_dvd_pow h)
    exact (show (0 : Fin 3) ≠ 1 by decide) h01
  obtain ⟨p, hp⟩ := prime.pow_dvd_of_dvd_mul_left m hndvd ⟨s, cross⟩
  rw [hp, map_mul, map_pow, bracketMap_X] at hq
  have hB : (bracket 0 : Coordinates k) ≠ 0 := ordered_first_ne_zero (Equiv.refl _)
  exact ⟨p, (mul_left_cancel₀ (pow_ne_zero m hB) hq).symm⟩

theorem bracket_presentation (k : Type*) [Field k] [IsAlgClosed k] :
    ∃ e : BracketPolynomials k ≃ₐ[k] (action (k := k)).fixedSubalgebra,
      ∀ q, (e q : Coordinates k) = bracketMap q := by
  let f : BracketPolynomials k →ₐ[k] (action (k := k)).fixedSubalgebra :=
    aeval fun i ↦ ⟨bracket i, bracket_mem i⟩
  have hf (p : BracketPolynomials k) : (f p : Coordinates k) = bracketMap p := by
    exact comp_aeval_apply _ ((action (k := k)).fixedSubalgebra.val) p
  have bij : Function.Bijective f := by
    constructor
    · intro p q h
      apply bracketMap_injective
      rw [← hf p, ← hf q, h]
    · intro y
      obtain ⟨p, hp⟩ := exists_bracket_polynomial y.property
      exact ⟨p, Subtype.ext ((hf p).trans hp)⟩
  exact ⟨AlgEquiv.ofBijective f bij, hf⟩

end

end RepTheorySurvey.Invariants.ThreeSL2Vectors
