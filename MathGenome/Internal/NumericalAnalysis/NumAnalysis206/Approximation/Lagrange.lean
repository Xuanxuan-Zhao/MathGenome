import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.Lagrange
import Mathlib.Algebra.Module.Submodule.Equiv

noncomputable section
open Polynomial

universe u v
namespace NumAnalysis206.Approximation

variable {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]

/-- The normalized product from W46, with scalar division in the field. -/
def cardinal (s : Finset ι) (x : ι → K) (i : ι) : K[X] :=
  Specs.NumAnalysis206.Approximation.cardinalValue s x i

/-- The finite Lagrange interpolation sum from W46. -/
def interpolant (s : Finset ι) (x y : ι → K) : K[X] :=
  ∑ i ∈ s, C (y i) * cardinal s x i

private theorem cardinal_eq (s : Finset ι) (x : ι → K) (i : ι) :
    cardinal s x i = Lagrange.basis s x i := rfl

private theorem interpolant_eq (s : Finset ι) (x y : ι → K) :
    interpolant s x y = Lagrange.interpolate s x y := rfl

theorem cardinal_degree (s : Finset ι) (x : ι → K) (hx : Set.InjOn x s)
    (i : ι) (hi : i ∈ s) : (cardinal s x i).degree ≤ (s.card - 1 : ℕ) := by
  rw [cardinal_eq, Lagrange.degree_basis hx hi]

theorem cardinal_eval (s : Finset ι) (x : ι → K) (hx : Set.InjOn x s)
    (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
    (cardinal s x i).eval (x j) = if i = j then 1 else 0 := by
  rw [cardinal_eq]
  by_cases hij : i = j
  · subst j
    simpa using Lagrange.eval_basis_self hx hi
  · simpa [hij] using Lagrange.eval_basis_of_ne (v := x) hij hj

theorem interpolant_eval (s : Finset ι) (x y : ι → K) (hx : Set.InjOn x s)
    (i : ι) (hi : i ∈ s) : (interpolant s x y).eval (x i) = y i := by
  rw [interpolant_eq]
  exact Lagrange.eval_interpolate_at_node y hx hi

theorem interpolant_degree_lt (s : Finset ι) (x y : ι → K) (hx : Set.InjOn x s) :
    (interpolant s x y).degree < (s.card : WithBot ℕ) := by
  rw [interpolant_eq]
  exact Lagrange.degree_interpolate_lt y hx

theorem cardinal_singleton (x : ι → K) (i : ι) : cardinal {i} x i = 1 :=
  Lagrange.basis_singleton i

theorem interpolant_empty (x y : ι → K) : interpolant ∅ x y = 0 :=
  Lagrange.interpolate_empty (v := x) y

theorem degree_le_iff_lt_card (s : Finset ι) (n : ℕ) (hs : s.card = n + 1)
    (p : K[X]) : p.degree ≤ (n : WithBot ℕ) ↔ p.degree < (s.card : WithBot ℕ) := by
  rw [← Polynomial.mem_degreeLE, ← Polynomial.degreeLT_succ_eq_degreeLE,
    Polynomial.mem_degreeLT, hs]

theorem interpolant_unique (s : Finset ι) (x y : ι → K) (n : ℕ)
    (hx : Set.InjOn x s) (hs : s.card = n + 1) (p : K[X]) :
    (p.degree ≤ (n : WithBot ℕ) ∧ ∀ i ∈ s, p.eval (x i) = y i) ↔
      p = interpolant s x y := by
  rw [degree_le_iff_lt_card s n hs p, interpolant_eq]
  exact Lagrange.eq_interpolate_iff y hx

theorem existsUnique_interpolant (s : Finset ι) (x y : ι → K) (n : ℕ)
    (hx : Set.InjOn x s) (hs : s.card = n + 1) :
    ∃! p : K[X], p.degree ≤ (n : WithBot ℕ) ∧ ∀ i ∈ s, p.eval (x i) = y i := by
  refine ⟨interpolant s x y, (interpolant_unique s x y n hx hs _).2 rfl, ?_⟩
  intro p hp
  exact (interpolant_unique s x y n hx hs p).1 hp

/-- Evaluation identifies P_n(K) with scalar data on n + 1 distinct nodes. -/
def evaluationEquiv (s : Finset ι) (x : ι → K) (n : ℕ)
    (hx : Set.InjOn x s) (hs : s.card = n + 1) :
    Polynomial.degreeLE K (n : WithBot ℕ) ≃ₗ[K] (s → K) :=
  (LinearEquiv.ofEq _ _ (by rw [hs, Polynomial.degreeLT_succ_eq_degreeLE])).trans
    (Lagrange.funEquivDegreeLT hx)

@[simp] theorem evaluationEquiv_apply (s : Finset ι) (x : ι → K) (n : ℕ)
    (hx : Set.InjOn x s) (hs : s.card = n + 1)
    (p : Polynomial.degreeLE K (n : WithBot ℕ)) (i : s) :
    evaluationEquiv s x n hx hs p i = p.val.eval (x i) := by
  unfold evaluationEquiv
  rw [LinearEquiv.trans_apply]
  change (↑(LinearEquiv.ofEq _ _ _ p) : K[X]).eval (x i) = _
  rw [LinearEquiv.coe_ofEq_apply]

theorem cardinal_basis (s : Finset ι) (x : ι → K) (n : ℕ)
    (hx : Set.InjOn x s) (hs : s.card = n + 1) :
    ∃ b : Module.Basis s K (Polynomial.degreeLE K (n : WithBot ℕ)),
      (∀ i : s, (b i).val = cardinal s x i) ∧
      (∀ (p : Polynomial.degreeLE K (n : WithBot ℕ)) (i : s),
        b.repr p i = p.val.eval (x i)) := by
  let e := evaluationEquiv s x n hx hs
  let b := Module.Basis.ofEquivFun e
  have hcoord (p : Polynomial.degreeLE K (n : WithBot ℕ)) (i : s) :
      b.repr p i = p.val.eval (x i) := by
    exact evaluationEquiv_apply s x n hx hs p i
  refine ⟨b, ?_, hcoord⟩
  intro i
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq s hx
  · exact (degree_le_iff_lt_card s n hs _).1 (Polynomial.mem_degreeLE.1 (b i).property)
  · rw [cardinal_eq, Lagrange.degree_basis hx i.property]
    exact_mod_cast Nat.sub_lt (Finset.card_pos.mpr ⟨i.val, i.property⟩) Nat.zero_lt_one
  · intro j hj
    rw [← hcoord (b i) ⟨j, hj⟩, b.repr_self_apply,
      cardinal_eval s x hx i i.property j hj]
    simp only [Subtype.ext_iff]

theorem empty_data_not_unique (x y : ι → K) (n : ℕ) :
    ¬ ∃! p : K[X], p.degree ≤ (n : WithBot ℕ) ∧
      ∀ i ∈ (∅ : Finset ι), p.eval (x i) = y i := by
  rintro ⟨p, _, hu⟩
  have h0 := hu 0 (by simp)
  have h1 := hu 1 (by simp)
  exact zero_ne_one (h0.trans h1.symm)

end NumAnalysis206.Approximation
