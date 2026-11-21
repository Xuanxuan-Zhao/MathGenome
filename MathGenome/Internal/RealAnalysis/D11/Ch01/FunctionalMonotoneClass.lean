import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.FunctionalMonotoneClass
import MathGenome.Internal.RealAnalysis.D11.Ch01.PiLambda
import MathGenome.Internal.RealAnalysis.D11.Ch04.MeasurableMapTests
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.Linarith

/-! The bounded functional monotone-class theorem. First apply π–λ to the
sets whose indicators belong to `H`. Then use finite-valued rational lower
approximants and a constant shift. Only pointwise scalar convergence is used;
no integral convergence theorem enters the proof. -/

open Set MeasurableSpace Filter MeasureTheory
open scoped Topology ENNReal
universe u

namespace D11.Ch01.FunctionalMonotoneClass

private theorem indicator_bound {X : Type u} (A : Set X) (x : X) :
    |A.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
  classical
  by_cases hx : x ∈ A <;> simp [hx]

private theorem indicator_monotone {X : Type u} {A B : Set X} (h : A ⊆ B) (x : X) :
    A.indicator (fun _ => (1 : ℝ)) x ≤ B.indicator (fun _ => (1 : ℝ)) x := by
  classical
  by_cases ha : x ∈ A
  · simp [ha, h ha]
  · by_cases hb : x ∈ B <;> simp [ha, hb]

private theorem disjoint_union_indicator_mem {X : Type u} (H : Submodule ℝ (X → ℝ))
    (hlim : ∀ (g : ℕ → X → ℝ) (f : X → ℝ),
      (∀ n, g n ∈ H) → (∀ x, Monotone (fun n => g n x)) →
      (∃ C : ℝ, ∀ n x, |g n x| ≤ C) →
      (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      (∀ x, Tendsto (fun n => g n x) atTop (𝓝 (f x))) → f ∈ H)
    (E : ℕ → Set X) (hd : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hE : ∀ n, (E n).indicator (fun _ => (1 : ℝ)) ∈ H) :
    (⋃ n, E n).indicator (fun _ => (1 : ℝ)) ∈ H := by
  classical
  let U : ℕ → Set X := fun n => ⋃ k ∈ Finset.range n, E k
  have hU : ∀ n, (U n).indicator (fun _ => (1 : ℝ)) ∈ H := by
    intro n
    induction n with
    | zero =>
      convert H.zero_mem using 1
      ext x
      simp [U]
    | succ n ih =>
      have hd' : Disjoint (U n) (E n) := by
        refine Set.disjoint_left.mpr ?_
        intro x hx hn
        obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hx
        exact Set.disjoint_left.mp (hd (Nat.ne_of_lt (Finset.mem_range.mp hk))) hxk hn
      have hu : U (n + 1) = U n ∪ E n := by
        ext x
        simp only [U, Set.mem_iUnion, Finset.mem_range, Set.mem_union]
        constructor
        · rintro ⟨k, hk, hx⟩
          rcases lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
          · exact Or.inl ⟨k, hk, hx⟩
          · exact Or.inr hx
        · rintro (⟨k, hk, hx⟩ | hx)
          · exact ⟨k, Nat.lt_succ_of_lt hk, hx⟩
          · exact ⟨n, Nat.lt_succ_self n, hx⟩
      rw [hu, Set.indicator_union_of_disjoint hd']
      exact H.add_mem ih (hE n)
  have hUm : Monotone U := by
    intro n m hnm x hx
    obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le hnm), hxk⟩
  apply hlim (fun n => (U n).indicator (fun _ => (1 : ℝ)))
    ((⋃ n, E n).indicator (fun _ => (1 : ℝ))) hU
  · exact fun x n m hnm => indicator_monotone (hUm hnm) x
  · exact ⟨1, fun n x => indicator_bound (U n) x⟩
  · exact ⟨1, indicator_bound _⟩
  · intro x
    apply tendsto_const_nhds.congr'
    by_cases hx : x ∈ ⋃ n, E n
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      filter_upwards [eventually_ge_atTop (k + 1)] with n hn
      have hxn : x ∈ U n := Set.mem_iUnion₂.mpr
        ⟨k, Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hn), hk⟩
      simp [hxn, hx]
    · filter_upwards [] with n
      have hxn : x ∉ U n := by
        intro hxU
        obtain ⟨k, _, hk⟩ := Set.mem_iUnion₂.mp hxU
        exact hx (Set.mem_iUnion.mpr ⟨k, hk⟩)
      simp [hxn, hx]

/-- Finite linear combinations of measurable indicators give all real simple functions. -/
private theorem simpleFunc_mem {X : Type u} [MeasurableSpace X]
    (H : Submodule ℝ (X → ℝ))
    (hind : ∀ A : Set X, MeasurableSet A → A.indicator (fun _ => (1 : ℝ)) ∈ H)
    (s : SimpleFunc X ℝ) : (s : X → ℝ) ∈ H := by
  classical
  induction s using SimpleFunc.induction with
  | @const c A hA =>
    have heq : (SimpleFunc.piecewise A hA (SimpleFunc.const X c) (SimpleFunc.const X 0) : X → ℝ) =
        c • A.indicator (fun _ => (1 : ℝ)) := by
      ext x
      by_cases hx : x ∈ A <;> simp [hx]
    rw [heq]
    exact H.smul_mem c (hind A hA)
  | @add s t _ hs ht => exact H.add_mem hs ht

/-- A bounded nonnegative measurable function is an increasing bounded limit
of real simple functions. Mathlib's rational lower approximation is finite
valued at each stage, lies below the function, and converges pointwise. -/
private theorem nonneg_mem {X : Type u} [MeasurableSpace X]
    (H : Submodule ℝ (X → ℝ))
    (hind : ∀ A : Set X, MeasurableSet A → A.indicator (fun _ => (1 : ℝ)) ∈ H)
    (hlim : ∀ (g : ℕ → X → ℝ) (f : X → ℝ),
      (∀ n, g n ∈ H) → (∀ x, Monotone (fun n => g n x)) →
      (∃ C : ℝ, ∀ n x, |g n x| ≤ C) →
      (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      (∀ x, Tendsto (fun n => g n x) atTop (𝓝 (f x))) → f ∈ H)
    (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) : f ∈ H := by
  let e : X → ℝ≥0∞ := fun x => ENNReal.ofReal (f x)
  have he : Measurable e := hf.ennreal_ofReal
  let s : ℕ → SimpleFunc X ℝ := fun n => (SimpleFunc.eapprox e n).map ENNReal.toReal
  have hs0 : ∀ n x, 0 ≤ s n x := fun n x => ENNReal.toReal_nonneg
  have hsle : ∀ n x, s n x ≤ f x := by
    intro n x
    have hle : SimpleFunc.eapprox e n x ≤ e x := by
      rw [← SimpleFunc.iSup_eapprox_apply he x]
      exact le_iSup (fun k => SimpleFunc.eapprox e k x) n
    exact (ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hle).trans_eq
      (ENNReal.toReal_ofReal (hf0 x))
  apply hlim (fun n => (s n : X → ℝ)) f
  · exact fun n => simpleFunc_mem H hind (s n)
  · intro x n m hnm
    exact ENNReal.toReal_mono (SimpleFunc.eapprox_lt_top e m x).ne
      (SimpleFunc.monotone_eapprox e hnm x)
  · obtain ⟨C, hC⟩ := hb
    refine ⟨C, fun n x => ?_⟩
    rw [abs_of_nonneg (hs0 n x)]
    exact (hsle n x).trans ((le_abs_self (f x)).trans (hC x))
  · exact hb
  · intro x
    have ht := (ENNReal.tendsto_toReal (show e x ≠ ⊤ from ENNReal.ofReal_ne_top)).comp
      (SimpleFunc.tendsto_eapprox he x)
    simpa only [s, SimpleFunc.coe_map, Function.comp_def, e,
      ENNReal.toReal_ofReal (hf0 x)] using ht

/-- The bounded functional monotone-class theorem, with the original
pointwise closure hypothesis and generated sigma-algebra. -/
theorem functional_monotone_class :
    Specs.D11.Ch01.FunctionalMonotoneClass.functional_monotone_class := by
  intro X P H hP _hbounded hone hgen hlim f hf hb
  classical
  let L : Set (Set X) := {A | A.indicator (fun _ => (1 : ℝ)) ∈ H}
  have hL : ∃ D : DynkinSystem X, ∀ A, D.Has A ↔ A ∈ L := by
    apply (D11.Ch01.PiLambda.lambdaSystem_iff L).mpr
    refine ⟨?_, ?_, ?_⟩
    · change Set.univ.indicator (fun _ : X => (1 : ℝ)) ∈ H
      simpa only [Set.indicator_univ] using hone
    · intro A hA
      change Aᶜ.indicator (fun _ => (1 : ℝ)) ∈ H
      rw [Set.indicator_compl]
      exact H.sub_mem hone hA
    · intro E hd hE
      exact disjoint_union_indicator_mem H hlim E hd hE
  obtain ⟨D, hD⟩ := hL
  have hDP : ∀ A ∈ P, D.Has A := fun A hA => (hD A).mpr (hgen A hA)
  let : MeasurableSpace X := generateFrom P
  have hind : ∀ A : Set X, MeasurableSet A → A.indicator (fun _ => (1 : ℝ)) ∈ H := by
    intro A hA
    have hAG : (DynkinSystem.generate P).Has A := by
      change A ∈ {s : Set X | (DynkinSystem.generate P).Has s}
      rw [D11.Ch01.PiLambda.pi_lambda P hP]
      exact hA
    exact (hD A).mp (D.generate_le hDP A hAG)
  have hconst : ∀ c : ℝ, (fun _ : X => c) ∈ H := by
    intro c
    convert H.smul_mem c hone using 1
    ext x
    simp
  obtain ⟨C, hC⟩ := hb
  have hshift0 : ∀ x, 0 ≤ f x + |C| := by
    intro x
    have hfx := neg_abs_le (f x)
    have hx := (hC x).trans (le_abs_self C)
    linarith
  have hshiftb : ∃ M : ℝ, ∀ x, |f x + abs C| ≤ M := by
    refine ⟨|C| + |C|, fun x => ?_⟩
    calc
      |f x + abs C| ≤ |f x| + |abs C| := abs_add_le _ _
      _ ≤ |C| + |C| := by
        rw [abs_abs]
        linarith [(hC x).trans (le_abs_self C)]
  have hshift : (fun x => f x + |C|) ∈ H :=
    nonneg_mem H hind hlim _ (hf.add measurable_const) hshift0 hshiftb
  convert H.sub_mem hshift (hconst |C|) using 1
  ext x
  simp

end D11.Ch01.FunctionalMonotoneClass
