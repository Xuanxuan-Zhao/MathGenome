import MathGenome.Internal.MultivariableAnalysis.D04.C03.HigherInterfaces
import MathGenome.Internal.MultivariableAnalysis.D04.C03.CrossedPartials
import MathGenome.Internal.MultivariableAnalysis.D04.C02.ChainRule
import MathGenome.Internal.MultivariableAnalysis.D04.C02.CrCalculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.GroupTheory.Perm.Sign
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.Symmetry

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace D04
section Generic
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The ordinary derivative of the tensor field is the uncurried next tensor. -/
theorem timesDifferentiableAt_deriv (k : ℕ) (U : Set X) (f : X → Y) (a : X)
    (hf : TimesDifferentiableAt (k+1) U f a) :
    HasFDerivAt (higherDifferential k f) (fderiv ℝ (higherDifferential k f) a) a := by
  have h := timesDifferentiableAt_hasFDerivAt k U f a hf
  exact h.differentiableAt.hasFDerivAt

/-- The first two slots commute under pointwise iterated differentiability. -/
theorem higherDifferential_first_two (k : ℕ) (U : Set X) (f : X → Y) (a : X)
    (hf : TimesDifferentiableAt (k+2) U f a) (u v : X) (w : Fin k → X) :
    higherDifferential (k+2) f a (Fin.cons u (Fin.cons v w)) =
      higherDifferential (k+2) f a (Fin.cons v (Fin.cons u w)) := by
  let e : Differential X Y (k+1) →L[ℝ] (X →L[ℝ] Differential X Y k) :=
    (differentialSuccEquiv X Y k).symm.toContinuousLinearMap
  have hd := timesDifferentiableAt_deriv (k+1) U f a hf
  have hd' : HasFDerivAt (fun x => fderiv ℝ (higherDifferential k f) x)
      (e.comp (fderiv ℝ (higherDifferential (k+1) f) a)) a := by
    change HasFDerivAt (e ∘ higherDifferential (k+1) f) _ a
    have he : HasFDerivAt (fun T : Differential X Y (k+1) => e T) e
        (higherDifferential (k+1) f a) := e.hasFDerivAt
    exact HasFDerivAt.comp (g := fun T => e T) (g' := e) a he hd
  obtain ⟨V, hV, ha, _, hlow, _⟩ := hf
  have hnear : ∀ᶠ x in 𝓝 a, HasFDerivAt (higherDifferential k f)
      (fderiv ℝ (higherDifferential k f) x) x := by
    filter_upwards [hV.mem_nhds ha] with x hx
    exact timesDifferentiableAt_deriv k U f x (hlow x hx)
  have h := second_derivative_symmetric_of_eventually hnear hd' u v
  exact congrArg (fun T : Differential X Y k => T w) h

/-- Differentiating a permutation identity gives the identity in the tail slots. -/
theorem higherDifferential_tail (k : ℕ) (U : Set X) (f : X → Y) (a : X)
    (hf : TimesDifferentiableAt (k+1) U f a) (σ : Equiv.Perm (Fin k))
    (hs : ∀ᶠ x in 𝓝 a, ∀ w : Fin k → X,
      higherDifferential k f x (w ∘ σ) = higherDifferential k f x w)
    (u : X) (w : Fin k → X) :
    higherDifferential (k+1) f a (Fin.cons u (w ∘ σ)) =
      higherDifferential (k+1) f a (Fin.cons u w) := by
  let ev₁ := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => X) Y (w ∘ σ)
  let ev₂ := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => X) Y w
  have hd := timesDifferentiableAt_deriv k U f a hf
  have h₁ := ev₁.hasFDerivAt.comp a hd
  have h₂ := ev₂.hasFDerivAt.comp a hd
  have he : (fun x => ev₁ (higherDifferential k f x)) =ᶠ[𝓝 a]
      (fun x => ev₂ (higherDifferential k f x)) := hs.mono fun x hx => hx w
  have hh := (h₁.congr_of_eventuallyEq he.symm).unique h₂
  exact congrArg (fun A : X →L[ℝ] Y => A u) hh

/-- Full permutation symmetry, including arities zero and one. -/
theorem higherDifferential_symmetric (k : ℕ) (U : Set X) (f : X → Y) (a : X)
    (hf : TimesDifferentiableAt k U f a) (σ : Equiv.Perm (Fin k)) (v : Fin k → X) :
    higherDifferential k f a (v ∘ σ) = higherDifferential k f a v := by
  classical
  induction k using Nat.twoStepInduction generalizing a with
  | zero => exact congrArg (higherDifferential 0 f a) (Subsingleton.elim _ _)
  | one => exact congrArg (higherDifferential 1 f a) (by ext i; exact congrArg v (Subsingleton.elim _ _))
  | more k ih₀ ih =>
    let S : Submonoid (Equiv.Perm (Fin (k+2))) :=
      { carrier := {σ | ∀ v : Fin (k+2) → X,
          higherDifferential (k+2) f a (v ∘ σ) = higherDifferential (k+2) f a v}
        one_mem' := by intro v; rfl
        mul_mem' := by
          intro σ τ hσ hτ v
          exact (hτ (v ∘ σ)).trans (hσ v) }
    have hgen : Set.range (fun i : Fin (k+1) => Equiv.swap i.castSucc i.succ) ⊆ S := by
      rintro _ ⟨i, rfl⟩ w
      obtain ⟨V, hV, haV, _, hlow, _⟩ := (timesDifferentiableAt_succ (k+1) U f a).mp hf
      induction i using Fin.cases with
      | zero =>
        have h := higherDifferential_first_two k U f a hf (w 0) (w 1) (Fin.tail (Fin.tail w))
        have hw : w ∘ Equiv.swap (0 : Fin (k+2)) 1 =
            Fin.cons (w 1) (Fin.cons (w 0) (Fin.tail (Fin.tail w))) := by
          ext j
          refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
          · simp
          · simp
          · have hn : j.succ.succ ≠ (1 : Fin (k+2)) := by
              intro he; have := congrArg Fin.val he; simp only [Fin.val_succ, Fin.val_one] at this; omega
            simp [Equiv.swap_apply_def, hn, Fin.tail_def]
        change higherDifferential (k+2) f a (w ∘ Equiv.swap (0 : Fin (k+2)) 1) = _
        rw [hw]
        have hw₀ : Fin.cons (w 0) (Fin.cons (w 1) (Fin.tail (Fin.tail w))) = w := by
          ext j; refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;> rfl
        rw [hw₀] at h
        exact h.symm
      | succ i =>
        have hs : ∀ᶠ x in 𝓝 a, ∀ vs : Fin (k+1) → X,
            higherDifferential (k+1) f x (vs ∘ Equiv.swap i.castSucc i.succ) =
              higherDifferential (k+1) f x vs := by
          filter_upwards [hV.mem_nhds haV] with x hx
          exact fun vs => ih x (hlow x hx) _ vs
        have h := higherDifferential_tail (k+1) U f a hf _ hs (w 0) (Fin.tail w)
        have hw : w ∘ Equiv.swap i.succ.castSucc i.succ.succ =
            Fin.cons (w 0) (Fin.tail w ∘ Equiv.swap i.castSucc i.succ) := by
          ext j
          refine Fin.cases ?_ (fun j => ?_) j
          · simp [Function.comp_def, Equiv.swap_apply_def, Fin.castSucc_succ, Fin.succ_ne_zero, eq_comm (a := (0 : Fin (k+2)))]
          · simp only [Function.comp_def, Equiv.swap_apply_def, Fin.castSucc_succ,
              Fin.succ_inj, Fin.cons_succ, Fin.tail_def]
            split_ifs <;> rfl
        change higherDifferential (k+2) f a (w ∘ Equiv.swap i.succ.castSucc i.succ.succ) = _
        rw [hw]
        simpa only [Fin.cons_self_tail] using h
    have hle : Submonoid.closure (Set.range (fun i : Fin (k+1) => Equiv.swap i.castSucc i.succ)) ≤ S :=
      Submonoid.closure_le.mpr hgen
    have hm : σ ∈ S := hle (by rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial)
    exact hm v
end Generic

section Coordinates
variable {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Ordered coordinate differentiation equals evaluation of the tensor on its basis tuple. -/
theorem orderedPartial_eq_higherDifferential (is : List (Fin n))
    (U : Set (E n)) (f : E n → Y) (a : E n)
    (hf : TimesDifferentiableAt is.length U f a) :
    orderedPartial is f a = higherDifferential is.length f a
      (fun r => standardBasis n (is.get r)) := by
  induction is generalizing a with
  | nil => rfl
  | cons i is ih =>
    let w : Fin is.length → E n := fun r => standardBasis n (is.get r)
    let ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin is.length => E n) Y w
    have hd := ev.hasFDerivAt.comp a (timesDifferentiableAt_deriv is.length U f a hf)
    obtain ⟨V, hV, haV, _, hlow, _⟩ := hf
    have he : orderedPartial is f =ᶠ[𝓝 a] (fun x => ev (higherDifferential is.length f x)) := by
      filter_upwards [hV.mem_nhds haV] with x hx
      exact ih x (hlow x hx)
    have hp := hd.congr_of_eventuallyEq he
    have hdom := timesDifferentiableAt_domain is.length U f a (hlow a haV)
    have ht := (hasTotalDerivative_iff_hasFDerivAt U _ _ a hdom.1 hdom.2).mpr hp
    rw [orderedPartial_cons, totalDerivative_directionalDerivative U _ a (standardBasis n i) _ ht]
    change higherDifferential (is.length+1) f a (Fin.cons (standardBasis n i) w) = _
    congr 1
    ext r
    refine Fin.cases ?_ (fun j => ?_) r <;> rfl

/-- Existence of the ordered partials is proved separately from their selector values. -/
theorem orderedPartial_hasDerivative (is : List (Fin n)) (U : Set (E n))
    (f : E n → Y) (a : E n) (hf : TimesDifferentiableAt (is.length+1) U f a)
    (i : Fin n) : HasDirectionalDerivative (orderedPartial is f) a (standardBasis n i)
      (orderedPartial (i :: is) f a) := by
  let w : Fin is.length → E n := fun r => standardBasis n (is.get r)
  let ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin is.length => E n) Y w
  have hd := ev.hasFDerivAt.comp a (timesDifferentiableAt_deriv is.length U f a hf)
  obtain ⟨V, hV, haV, _, hlow, _⟩ := hf
  have he : orderedPartial is f =ᶠ[𝓝 a] (fun x => ev (higherDifferential is.length f x)) := by
    filter_upwards [hV.mem_nhds haV] with x hx
    exact orderedPartial_eq_higherDifferential is U f x (hlow x hx)
  have hp := hd.congr_of_eventuallyEq he
  have hdom := timesDifferentiableAt_domain is.length U f a (hlow a haV)
  have ht := (hasTotalDerivative_iff_hasFDerivAt U _ _ a hdom.1 hdom.2).mpr hp
  rw [orderedPartial_cons, totalDerivative_directionalDerivative U _ a (standardBasis n i) _ ht]
  exact totalDerivative_hasDirectionalDerivative U _ a (standardBasis n i) _ ht

/-- The statement in terms of an arbitrary tuple of coordinate indices. -/
theorem higherDifferential_basis (k : ℕ) (U : Set (E n)) (f : E n → Y) (a : E n)
    (hf : TimesDifferentiableAt k U f a) (j : Fin k → Fin n) :
    higherDifferential k f a (fun r => standardBasis n (j r)) =
      orderedPartial (List.ofFn j) f a := by
  have h := orderedPartial_eq_higherDifferential (List.ofFn j) U f a (by simpa using hf)
  have he : (List.ofFn j).length = k := List.length_ofFn
  generalize hword : List.ofFn j = is at h he
  subst k
  have hj : is.get = j := by
    apply List.ofFn_injective
    simpa only [List.ofFn_get] using hword.symm
  simpa only [hj] using h.symm

/-- Pointwise order independence retains the original, weaker pointwise hypothesis. -/
theorem orderedPartial_permutation (k : ℕ) (U : Set (E n)) (f : E n → Y) (a : E n)
    (hf : TimesDifferentiableAt k U f a) (j : Fin k → Fin n) (σ : Equiv.Perm (Fin k)) :
    orderedPartial (List.ofFn (j ∘ σ)) f a = orderedPartial (List.ofFn j) f a := by
  rw [← higherDifferential_basis k U f a hf, ← higherDifferential_basis k U f a hf]
  exact higherDifferential_symmetric k U f a hf σ (fun r => standardBasis n (j r))
end Coordinates

section GenericRegularity
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Continuous finite regularity implies the shared pointwise existence predicate. -/
theorem crOn_timesDifferentiableAt (k : ℕ) (U : Set X) (f : X → Y)
    (hU : IsOpen U) (hf : CrOn k U f) (a : X) (ha : a ∈ U) :
    TimesDifferentiableAt k U f a := by
  have hc := (crOn_iff_contDiffOn k U f hU).mp hf
  induction k generalizing a with
  | zero => exact ⟨hU, ha⟩
  | succ k ih =>
    refine ⟨U, hU, ha, Subset.rfl, ?_, ?_⟩
    · intro x hx
      exact ih ((crOn_iff_contDiffOn k U f hU).mpr
        (hc.of_le (by exact_mod_cast Nat.le_succ k))) x hx
        (hc.of_le (by exact_mod_cast Nat.le_succ k))
    · apply (totalDifferentiableAt_iff_differentiableAt U _ a hU ha).mpr
      exact (hc.contDiffAt (hU.mem_nhds ha)).differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k)
end GenericRegularity

/-- In particular, all order-k coordinate partials of a C^k map are independent of order. -/
theorem crOn_orderedPartial_permutation {n m : ℕ} (k : ℕ) (U : Set (E n))
    (f : E n → E m) (hU : IsOpen U) (hf : CrOn k U f) (a : E n) (ha : a ∈ U)
    (j : Fin k → Fin n) (σ : Equiv.Perm (Fin k)) :
    orderedPartial (List.ofFn (j ∘ σ)) f a = orderedPartial (List.ofFn j) f a :=
  orderedPartial_permutation k U f a (crOn_timesDifferentiableAt k U f hU hf a ha) j σ

section Hessian
abbrev hessian : Specs.D04.C03.Symmetry.hessianType :=
  @Specs.D04.C03.Symmetry.Model.hessian

theorem hessian_apply {n : ℕ} (f : E n → ℝ) (a : E n) (i j : Fin n) :
    hessian f a i j = directionalDerivative
      (fun x => directionalDerivative f x (standardBasis n j)) a (standardBasis n i) := rfl

private theorem hessian_basis {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n)
    (hf : TimesDifferentiableAt 2 U f a) (i j : Fin n) :
    higherDifferential 2 f a ![standardBasis n i, standardBasis n j] = hessian f a i j := by
  have h := higherDifferential_basis 2 U f a hf ![i,j]
  have hv : (fun r => standardBasis n (![i,j] r)) = ![standardBasis n i, standardBasis n j] := by
    ext r; fin_cases r <;> rfl
  rw [hv] at h
  simpa [hessian, Specs.D04.C03.Symmetry.Model.hessian, List.ofFn_succ] using h

theorem hessian_symmetric {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n)
    (hf : TimesDifferentiableAt 2 U f a) : (hessian f a).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  rw [← hessian_basis U f a hf j i, ← hessian_basis U f a hf i j]
  exact higherDifferential_first_two 0 U f a hf _ _ (fun i => Fin.elim0 i)

theorem higherDifferential_two_hessian {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n)
    (hf : TimesDifferentiableAt 2 U f a) (u v : E n) :
    higherDifferential 2 f a ![u,v] =
      dotProduct (coordinates n u) ((hessian f a).mulVec (coordinates n v)) := by
  classical
  let T := higherDifferential 2 f a
  have hu : u = ∑ i : Fin n, u i • standardBasis n i := by
    simpa [standardBasis, EuclideanSpace.basisFun_repr] using ((standardBasis n).sum_repr u).symm
  have hv : v = ∑ j : Fin n, v j • standardBasis n j := by
    simpa [standardBasis, EuclideanSpace.basisFun_repr] using ((standardBasis n).sum_repr v).symm
  have he : T ![u,v] = ∑ i : Fin n, ∑ j : Fin n,
      u i * v j * T ![standardBasis n i, standardBasis n j] := by
    change (T.curryLeft u).curryLeft v (fun i => Fin.elim0 i) = _
    conv_lhs => rw [hu, hv]
    simp only [map_sum, map_smul, sum_apply, smul_apply,
      ContinuousMultilinearMap.curryLeft_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro i _
    change v i * (u j * T ![standardBasis n j, standardBasis n i]) = _
    ring
  rw [he]
  simp_rw [show ∀ i j, T ![standardBasis n i, standardBasis n j] = hessian f a i j from
    fun i j => hessian_basis U f a hf i j]
  simp [dotProduct, Matrix.mulVec, coordinates, Finset.mul_sum, mul_left_comm, mul_comm]

theorem higherDifferential_diagonal_hessian {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (a : E n) (hf : TimesDifferentiableAt 2 U f a) (h : E n) :
    differentialDiagonal (higherDifferential 2 f a) h =
      dotProduct (coordinates n h) ((hessian f a).mulVec (coordinates n h)) := by
  have he : (fun _ : Fin 2 => h) = ![h,h] := by ext i; fin_cases i <;> rfl
  change higherDifferential 2 f a (fun _ => h) = _
  rw [he]
  exact higherDifferential_two_hessian U f a hf h h

theorem quadraticTaylorTerm_hessian {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (a : E n) (hf : TimesDifferentiableAt 2 U f a) (h : E n) :
    ((Nat.factorial 2 : ℝ)⁻¹) • differentialDiagonal (higherDifferential 2 f a) h =
      (1/2 : ℝ) * dotProduct (coordinates n h) ((hessian f a).mulVec (coordinates n h)) := by
  rw [higherDifferential_diagonal_hessian U f a hf h]
  norm_num

theorem taylorPolynomial_two_hessian {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (a : E n) (hf : TimesDifferentiableAt 2 U f a) (h : E n) :
    taylorPolynomial 2 f a h = f a + totalDerivative f a h +
      (1/2 : ℝ) * dotProduct (coordinates n h) ((hessian f a).mulVec (coordinates n h)) := by
  have h₂ := quadraticTaylorTerm_hessian U f a hf h
  change (∑ j ∈ Finset.range 3, ((j.factorial : ℝ)⁻¹) •
    differentialDiagonal (higherDifferential j f a) h) = _
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  rw [h₂]
  simp [differentialDiagonal, Specs.D04.C03.HigherInterfaces.Model.differentialDiagonal,
    higherDifferential, Specs.D04.C03.HigherInterfaces.Model.higherDifferential,
    iteratedFDeriv_one_apply]
  rfl
end Hessian
end D04
