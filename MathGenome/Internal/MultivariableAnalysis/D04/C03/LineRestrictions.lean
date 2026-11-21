import MathGenome.Internal.MultivariableAnalysis.D04.C03.HigherInterfaces
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.LineRestrictions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace D04
section
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Evaluate the derivative tensor on the fixed direction after the affine chain rule. -/
theorem differentialDiagonal_line_hasDerivAt (j : ℕ) (U : Set X) (f : X → Y)
    (a h : X) (t : ℝ) (hf : TimesDifferentiableAt (j+1) U f (a + t • h)) :
    HasDerivAt (fun s : ℝ => differentialDiagonal (higherDifferential j f (a + s • h)) h)
      (differentialDiagonal (higherDifferential (j+1) f (a + t • h)) h) t := by
  let ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => X) Y (fun _ => h)
  have hd := timesDifferentiableAt_hasFDerivAt j U f (a + t • h) hf
  have hl : HasDerivAt (fun s : ℝ => a + s • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add a
  have hh := (ev.hasFDerivAt.comp (a + t • h) hd).comp_hasDerivAt t hl
  convert hh using 1
  · rfl
  · change higherDifferential (j+1) f (a + t • h) (fun _ => h) =
      higherDifferential (j+1) f (a + t • h) (Fin.cons h (fun _ => h))
    congr 1
    ext i
    exact Fin.cases rfl (fun _ => rfl) i

theorem lineRestriction_iteratedDeriv (j : ℕ) (U : Set X) (f : X → Y) (a h : X) (t : ℝ)
    (hf : TimesDifferentiableAt j U f (a + t • h)) :
    iteratedDeriv j (fun s : ℝ => f (a + s • h)) t =
      differentialDiagonal (higherDifferential j f (a + t • h)) h := by
  induction j generalizing t with
  | zero => rfl
  | succ j ih =>
    have hd := differentialDiagonal_line_hasDerivAt j U f a h t hf
    obtain ⟨V, hV, htV, _, hlow, _⟩ := hf
    have hl : ContinuousAt (fun s : ℝ => a + s • h) t :=
      continuousAt_const.add (continuousAt_id.smul continuousAt_const)
    have he : iteratedDeriv j (fun s : ℝ => f (a + s • h)) =ᶠ[𝓝 t]
        (fun s : ℝ => differentialDiagonal (higherDifferential j f (a + s • h)) h) := by
      filter_upwards [hl.preimage_mem_nhds (hV.mem_nhds htV)] with s hs
      exact ih s (hlow _ hs)
    rw [iteratedDeriv_succ]
    exact (he.deriv_eq).trans hd.deriv

theorem lineRestriction_hasDerivAt (j : ℕ) (U : Set X) (f : X → Y) (a h : X) (t : ℝ)
    (hf : TimesDifferentiableAt (j+1) U f (a + t • h)) :
    HasDerivAt (iteratedDeriv j (fun s : ℝ => f (a + s • h)))
      (differentialDiagonal (higherDifferential (j+1) f (a + t • h)) h) t := by
  have hd := differentialDiagonal_line_hasDerivAt j U f a h t hf
  obtain ⟨V, hV, htV, _, hlow, _⟩ := hf
  have hl : ContinuousAt (fun s : ℝ => a + s • h) t :=
    continuousAt_const.add (continuousAt_id.smul continuousAt_const)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hl.preimage_mem_nhds (hV.mem_nhds htV)] with s hs
  exact lineRestriction_iteratedDeriv j U f a h s (hlow _ hs)

/-- Lower orders of the pointwise existence predicate. -/
theorem timesDifferentiableAt_of_le {j k : ℕ} (hjk : j ≤ k) (U : Set X)
    (f : X → Y) (a : X) (hf : TimesDifferentiableAt k U f a) :
    TimesDifferentiableAt j U f a := by
  induction hjk with
  | refl => exact hf
  | @step k h ih => exact ih (timesDifferentiableAt_lower k U f a hf)

theorem lineRestriction_segment (k : ℕ) (U : Set X) (f : X → Y) (a h : X)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, TimesDifferentiableAt k U f (a + t • h)) :
    ∀ j ≤ k, ∀ t ∈ Icc (0 : ℝ) 1,
      iteratedDeriv j (fun s : ℝ => f (a + s • h)) t =
        differentialDiagonal (higherDifferential j f (a + t • h)) h := by
  intro j hj t ht
  exact lineRestriction_iteratedDeriv j U f a h t
    (timesDifferentiableAt_of_le hj U f _ (hf t ht))

/-- Symmetry makes differentiation in each slot give the same linear map. -/
theorem symmetric_toContinuousLinearMap (j : ℕ) (T : Differential X Y (j+1))
    (hs : ∀ (σ : Equiv.Perm (Fin (j+1))) (v : Fin (j+1) → X), T (v ∘ σ) = T v)
    (x : X) (i : Fin (j+1)) :
    T.toContinuousLinearMap (fun _ => x) i =
      T.toContinuousLinearMap (fun _ => x) 0 := by
  classical
  ext v
  change T (Function.update (fun _ => x) i v) = T (Function.update (fun _ => x) 0 v)
  have hh := hs (Equiv.swap 0 i) (Function.update (fun _ => x) i v)
  rw [Function.update_comp_equiv] at hh
  simpa [Function.comp_def] using hh.symm

theorem homogeneousTerm_hasFDerivAt (j : ℕ) (T : Differential X Y (j+1))
    (hs : ∀ (σ : Equiv.Perm (Fin (j+1))) (v : Fin (j+1) → X), T (v ∘ σ) = T v)
    (x : X) : HasFDerivAt
      (fun y : X => (((j+1).factorial : ℝ)⁻¹) • differentialDiagonal T y)
      (((j.factorial : ℝ)⁻¹) • T.toContinuousLinearMap (fun _ => x) 0) x := by
  classical
  have hd := (HasFDerivAt.multilinear_comp T (fun _ : Fin (j+1) => hasFDerivAt_id x)).const_smul
    (((j+1).factorial : ℝ)⁻¹)
  simp only [id_eq] at hd
  have he : (∑ i : Fin (j+1), T.toContinuousLinearMap (fun _ => x) i ∘L
        ContinuousLinearMap.id ℝ X) =
      ((j+1 : ℕ) : ℝ) • T.toContinuousLinearMap (fun _ => x) 0 := by
    simp only [ContinuousLinearMap.comp_id]
    simp_rw [symmetric_toContinuousLinearMap j T hs x]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul]
  rw [he, smul_smul] at hd
  have hc : (((j+1).factorial : ℝ)⁻¹) * (j+1 : ℕ) = (j.factorial : ℝ)⁻¹ := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hj1 : (↑(j+1) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    field_simp
  rw [hc] at hd
  exact hd

theorem homogeneousTerm_totalDerivative_apply (j : ℕ) (T : Differential X Y (j+1))
    (hs : ∀ (σ : Equiv.Perm (Fin (j+1))) (v : Fin (j+1) → X), T (v ∘ σ) = T v)
    (x v : X) :
    totalDerivative (fun y : X => (((j+1).factorial : ℝ)⁻¹) • differentialDiagonal T y) x v =
      ((j.factorial : ℝ)⁻¹) • T (Fin.cons v (fun _ => x)) := by
  rw [show totalDerivative (fun y : X => (((j+1).factorial : ℝ)⁻¹) •
      differentialDiagonal T y) x =
      ((j.factorial : ℝ)⁻¹) • T.toContinuousLinearMap (fun _ => x) 0 from
    (homogeneousTerm_hasFDerivAt j T hs x).fderiv]
  change ((j.factorial : ℝ)⁻¹) • T (Function.update (fun _ => x) 0 v) = _
  congr 2
  ext i
  exact Fin.cases (by simp) (fun i => by simp) i

theorem homogeneousTerm_zero (T : Differential X Y 0) (x : X) :
    (((Nat.factorial 0 : ℝ)⁻¹) • differentialDiagonal T x =
      T (fun i => Fin.elim0 i)) ∧
    HasFDerivAt (fun y : X => (((Nat.factorial 0 : ℝ)⁻¹) • differentialDiagonal T y))
      (0 : X →L[ℝ] Y) x := by
  have he (y : X) : ((Nat.factorial 0 : ℝ)⁻¹) • differentialDiagonal T y =
      T (fun i => Fin.elim0 i) := by
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    exact differentialDiagonal_zero T y
  refine ⟨he x, ?_⟩
  simp_rw [he]
  exact hasFDerivAt_const _ _

end
end D04
