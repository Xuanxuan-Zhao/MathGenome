import MathGenome.Internal.MultivariableAnalysis.D04.C03.Symmetry
import MathGenome.Internal.MultivariableAnalysis.D04.C03.LineRestrictions
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.TaylorPeano
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace D04
section Generic
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Differentiating once lowers the recursive pointwise order by one. -/
theorem timesDifferentiableAt_fderiv (k : ℕ) (U : Set X) (f : X → Y) (a : X)
    (hf : TimesDifferentiableAt (k+1) U f a) :
    TimesDifferentiableAt k U (fderiv ℝ f) a := by
  induction k generalizing a with
  | zero => exact timesDifferentiableAt_domain 1 U f a hf
  | succ k ih =>
    obtain ⟨V, hV, ha, hVU, hlow, hd⟩ := hf
    refine ⟨V, hV, ha, hVU, fun x hx => ih x (hlow x hx), ?_⟩
    apply (totalDifferentiableAt_iff_differentiableAt V _ a hV ha).mpr
    have hdiff := (totalDifferentiableAt_iff_differentiableAt V _ a hV ha).mp hd
    let e := continuousMultilinearCurryRightEquiv' ℝ k X Y
    have he : higherDifferential (k+1) f =
        e.symm ∘ higherDifferential k (fderiv ℝ f) := by
      funext x
      exact iteratedFDeriv_succ_eq_comp_right
    change DifferentiableAt ℝ (higherDifferential (k+1) f) a at hdiff
    rw [he] at hdiff
    exact e.symm.toContinuousLinearEquiv.comp_differentiableAt_iff.mp hdiff

/-- The Taylor coefficient for Df is the derivative of the next homogeneous term. -/
theorem taylorCoefficient_fderiv (j : ℕ) (U : Set X) (f : X → Y) (a x : X)
    (hf : TimesDifferentiableAt (j+1) U f a) :
    differentialDiagonal (higherDifferential j (fderiv ℝ f) a) x =
      (higherDifferential (j+1) f a).toContinuousLinearMap (fun _ => x) 0 := by
  have hs := higherDifferential_symmetric (j+1) U f a hf
  rw [← symmetric_toContinuousLinearMap j _ hs x (Fin.last j)]
  ext v
  change higherDifferential j (fderiv ℝ f) a (fun _ => x) v =
    higherDifferential (j+1) f a (Function.update (fun _ => x) (Fin.last j) v)
  rw [show higherDifferential (j+1) f a = iteratedFDeriv ℝ (j+1) f a from rfl,
    iteratedFDeriv_succ_apply_right]
  congr 2
  · ext i
    simp [Fin.init]
  · simp

/-- The polynomial derivative is the polynomial for the derivative map. -/
theorem taylorPolynomial_hasFDerivAt (k : ℕ) (U : Set X) (f : X → Y) (a x : X)
    (hf : TimesDifferentiableAt (k+1) U f a) :
    HasFDerivAt (taylorPolynomial (k+1) f a)
      (taylorPolynomial k (fderiv ℝ f) a x) x := by
  induction k with
  | zero =>
    have h₀ := (homogeneousTerm_zero (higherDifferential 0 f a) x).2
    have h₁ := homogeneousTerm_hasFDerivAt 0 (higherDifferential 1 f a)
      (higherDifferential_symmetric 1 U f a hf) x
    have he : taylorPolynomial 1 f a = fun y =>
        (((Nat.factorial 0 : ℝ)⁻¹) • differentialDiagonal (higherDifferential 0 f a) y) +
        (((Nat.factorial 1 : ℝ)⁻¹) • differentialDiagonal (higherDifferential 1 f a) y) := by
      funext y
      change (∑ j ∈ Finset.range 2, _) = _
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp
    rw [he, taylorPolynomial_zero]
    convert h₀.add h₁ using 1
    simp only [zero_add, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    exact taylorCoefficient_fderiv 0 U f a x hf
  | succ k ih =>
    have hlow := timesDifferentiableAt_lower (k+1) U f a hf
    have h₁ := ih hlow
    have h₂ := homogeneousTerm_hasFDerivAt (k+1) (higherDifferential (k+2) f a)
      (higherDifferential_symmetric (k+2) U f a hf) x
    have he : taylorPolynomial (k+2) f a = fun y => taylorPolynomial (k+1) f a y +
        (((Nat.factorial (k+2) : ℝ)⁻¹) • differentialDiagonal (higherDifferential (k+2) f a) y) := by
      funext y
      exact Finset.sum_range_succ _ _
    rw [he]
    convert h₁.add h₂ using 1
    change (∑ j ∈ Finset.range (k+1+1), _) = _
    rw [Finset.sum_range_succ]
    congr 1
    exact congrArg (fun A : X →L[ℝ] Y => ((↑(k+1).factorial : ℝ)⁻¹) • A)
      (taylorCoefficient_fderiv (k+1) U f a x hf)

theorem taylorPolynomial_one (f : X → Y) (a h : X) :
    taylorPolynomial 1 f a h = f a + fderiv ℝ f a h := by
  change (∑ j ∈ Finset.range 2, _) = _
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp [Specs.D04.C03.HigherInterfaces.Model.differentialDiagonal,
    Specs.D04.C03.HigherInterfaces.Model.higherDifferential]

/-- Peano's remainder, proved without continuity of the highest derivative. -/
theorem taylorPeano_succ (k : ℕ) (U : Set X) (f : X → Y) (a : X)
    (hf : TimesDifferentiableAt (k+1) U f a) :
    taylorRemainder (k+1) f a =o[𝓝 (0 : X)] (fun h => ‖h‖ ^ (k+1)) := by
  induction k generalizing Y with
  | zero =>
    have hdom := timesDifferentiableAt_domain 1 U f a hf
    have hd := (totalDifferentiableAt_iff_differentiableAt U f a hdom.1 hdom.2).mp
      ((timesDifferentiableAt_one U f a).mp hf)
    have hh := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hd.hasFDerivAt).norm_right
    change (fun h => f (a+h) - taylorPolynomial 1 f a h) =o[𝓝 (0 : X)] (fun h => ‖h‖ ^ 1)
    simp_rw [taylorPolynomial_one, ← sub_sub]
    simpa only [pow_one] using hh
  | succ k ih =>
    have hr := ih (f := fderiv ℝ f) (timesDifferentiableAt_fderiv (k+1) U f a hf)
    have hpol := taylorPolynomial_hasFDerivAt (k+1) U f a
    have hpol := fun h => hpol h hf
    obtain ⟨V, hV, haV, hVU, hlow, _⟩ := hf
    have hn : ∀ᶠ h in 𝓝 (0 : X), a + h ∈ V :=
      (continuousAt_const.add continuousAt_id).preimage_mem_nhds
        (by simpa using hV.mem_nhds haV)
    obtain ⟨r, hrpos, hball⟩ := Metric.mem_nhds_iff.mp hn
    let q : X → Y := taylorRemainder (k+2) f a
    let q' : X → X →L[ℝ] Y := taylorRemainder (k+1) (fderiv ℝ f) a
    have hq : ∀ h ∈ Metric.ball (0 : X) r, HasFDerivWithinAt q (q' h)
        (Metric.ball (0 : X) r) h := by
      intro h hh
      have hx := timesDifferentiableAt_of_le (Nat.succ_le_succ (Nat.zero_le k)) U f
        (a+h) (hlow _ (hball hh))
      have hdom := timesDifferentiableAt_domain 1 U f (a+h) hx
      have hd := (totalDifferentiableAt_iff_differentiableAt U f (a+h) hdom.1 hdom.2).mp
        ((timesDifferentiableAt_one U f (a+h)).mp hx)
      have ht : HasFDerivAt (fun y : X => a+y) (ContinuousLinearMap.id ℝ X) h :=
        (hasFDerivAt_id h).const_add a
      have h := (hd.hasFDerivAt.comp h ht).sub (hpol h)
      simp only [ContinuousLinearMap.comp_id] at h
      exact h.hasFDerivWithinAt
    have hs : Metric.ball (0 : X) r ∈ 𝓝 (0 : X) := Metric.ball_mem_nhds _ hrpos
    have hh := (convex_ball (0 : X) r).isLittleO_pow_succ (Metric.mem_ball_self hrpos)
      hq (by simpa only [sub_zero] using hr.mono nhdsWithin_le_nhds)
    rw [nhdsWithin_eq_nhds.mpr hs] at hh
    have hq0 : q 0 = 0 := taylorRemainder_zero_increment (k+2) f a
    simpa only [hq0, sub_zero] using hh

/-- The original punctured-increment formulation, with all positive orders. -/
theorem taylorPeano (k : ℕ) (hk : 1 ≤ k) (U : Set X) (f : X → Y) (a : X)
    (hf : TimesDifferentiableAt k U f a) :
    taylorRemainder k f a =o[𝓝[≠] (0 : X)] (fun h => ‖h‖ ^ k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact (taylorPeano_succ j U f a hf).mono nhdsWithin_le_nhds

/-- At order zero continuity is the entire analytic hypothesis. -/
theorem taylorPeano_zero (f : X → Y) (a : X) (hf : ContinuousAt f a) :
    taylorRemainder 0 f a =o[𝓝 (0 : X)] (fun h => ‖h‖ ^ 0) := by
  have ht : Tendsto (fun h : X => a+h) (𝓝 0) (𝓝 a) := by
    have ht : Tendsto (fun h : X => a+h) (𝓝 (0 : X)) (𝓝 (a+0)) :=
      tendsto_const_nhds.add tendsto_id
    rwa [add_zero] at ht
  have hh := (hf.isLittleO (F := ℝ)).comp_tendsto ht
  change (fun h => f (a+h) - taylorPolynomial 0 f a h) =o[𝓝 (0 : X)] _
  simp_rw [taylorPolynomial_zero, pow_zero]
  exact hh

/-- The exact expansion and the prescribed value at the zero increment. -/
theorem taylorPeano_expansion (k : ℕ) (f : X → Y) (a h : X) :
    f (a+h) = taylorPolynomial k f a h + taylorRemainder k f a h ∧
      taylorRemainder k f a 0 = 0 :=
  ⟨taylorRemainder_expansion k f a h, taylorRemainder_zero_increment k f a⟩

/-- Continuous derivatives are a sufficient special case. -/
theorem taylorPeano_crOn (k : ℕ) (hk : 1 ≤ k) (U : Set X) (f : X → Y) (a : X)
    (hU : IsOpen U) (ha : a ∈ U) (hf : CrOn k U f) :
    taylorRemainder k f a =o[𝓝[≠] (0 : X)] (fun h => ‖h‖ ^ k) :=
  taylorPeano k hk U f a (crOn_timesDifferentiableAt k U f hU hf a ha)

end Generic

/-- On the one-point source the remainder is identically zero. -/
theorem taylorPeano_source_zero {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (k : ℕ) (f : E 0 → Y) (a h : E 0) : taylorRemainder k f a h = 0 :=
  taylorRemainder_dimension_zero k f a h

/-- The zero-dimensional target also has identically zero remainder. -/
theorem taylorPeano_target_zero {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (k : ℕ) (f : X → E 0) (a h : X) : taylorRemainder k f a h = 0 :=
  Subsingleton.elim _ _

section Scalar
/-- The actual derivative-coordinate bridge to the ordinary scalar coefficients. -/
theorem taylorPolynomial_scalar (k : ℕ) (f : ℝ → ℝ) (a h : ℝ) :
    taylorPolynomial k f a h =
      ∑ j ∈ Finset.range (k+1), iteratedDeriv j f a / (j.factorial : ℝ) * h^j := by
  apply Finset.sum_congr rfl
  intro j hj
  change ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j f a (fun _ => h) = _
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem taylorPeano_scalar (k : ℕ) (hk : 1 ≤ k) (U : Set ℝ) (f : ℝ → ℝ) (a : ℝ)
    (hf : TimesDifferentiableAt k U f a) :
    (fun h => f (a+h) - ∑ j ∈ Finset.range (k+1),
      iteratedDeriv j f a / (j.factorial : ℝ) * h^j) =o[𝓝[≠] (0 : ℝ)] (fun h => |h|^k) := by
  have hh := taylorPeano k hk U f a hf
  change (fun h => f (a+h) - taylorPolynomial k f a h) =o[𝓝[≠] (0 : ℝ)] _ at hh
  simpa only [taylorPolynomial_scalar, Real.norm_eq_abs] using hh
end Scalar

/-- Projecting a line restriction differentiates its actual output coordinate. -/
theorem lineRestriction_coordinate_iteratedDeriv {n m : ℕ} (j : ℕ)
    (U : Set (E n)) (f : E n → E m) (a h : E n) (t : ℝ) (i : Fin m)
    (hf : TimesDifferentiableAt j U f (a + t • h)) :
    iteratedDeriv j (fun s : ℝ => f (a+s • h) i) t =
      differentialDiagonal (higherDifferential j f (a+t • h)) h i := by
  induction j generalizing t with
  | zero => rfl
  | succ j ih =>
    let pr : E m →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin m => ℝ) i
    have hd := pr.hasFDerivAt.comp_hasDerivAt t
      (differentialDiagonal_line_hasDerivAt j U f a h t hf)
    obtain ⟨V, hV, htV, _, hlow, _⟩ := hf
    have hl : ContinuousAt (fun s : ℝ => a+s • h) t :=
      continuousAt_const.add (continuousAt_id.smul continuousAt_const)
    have he : iteratedDeriv j (fun s : ℝ => f (a+s • h) i) =ᶠ[𝓝 t]
        (fun s : ℝ => differentialDiagonal (higherDifferential j f (a+s • h)) h i) := by
      filter_upwards [hl.preimage_mem_nhds (hV.mem_nhds htV)] with s hs
      exact ih s (hlow _ hs)
    rw [iteratedDeriv_succ]
    exact he.deriv_eq.trans hd.deriv

/-- In dimension one the Euclidean polynomial has precisely the ordinary
scalar coefficients of the coordinate function in the standard basis. -/
theorem taylorPolynomial_one_coordinate (k : ℕ) (U : Set (E 1))
    (f : E 1 → E 1) (a h : E 1) (hf : TimesDifferentiableAt k U f a) :
    taylorPolynomial k f a h 0 = ∑ j ∈ Finset.range (k+1),
      iteratedDeriv j (fun t : ℝ => f (a+t • standardBasis 1 0) 0) 0 /
        (j.factorial : ℝ) * (h 0)^j := by
  have hv : h = (h 0) • standardBasis 1 0 := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [standardBasis_apply]
  change (∑ j ∈ Finset.range (k+1),
    ((j.factorial : ℝ)⁻¹) • differentialDiagonal (higherDifferential j f a) h) 0 = _
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hd := lineRestriction_coordinate_iteratedDeriv j U f a (standardBasis 1 0) 0 0
    (by simpa using timesDifferentiableAt_of_le hjk U f a hf)
  simp only [zero_smul, add_zero] at hd
  change (((j.factorial : ℝ)⁻¹) •
    (higherDifferential j f a (fun _ => h))) 0 = _
  rw [hv]
  have he := (higherDifferential j f a).map_smul_univ (fun _ => h 0)
    (fun _ => standardBasis 1 0)
  rw [he]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  change (j.factorial : ℝ)⁻¹ * ((h 0)^j *
    differentialDiagonal (higherDifferential j f a) (standardBasis 1 0) 0) = _
  rw [← hd]
  simp [standardBasis_apply, div_eq_mul_inv, mul_comm, mul_left_comm]

/-- On E₁ the standard coordinate has its ordinary absolute-value norm. -/
theorem norm_one_coordinate_smul (t : ℝ) : ‖t • standardBasis 1 0‖ = |t| := by
  have he : ‖standardBasis 1 0‖ = 1 :=
    (EuclideanSpace.basisFun (Fin 1) ℝ).norm_eq_one 0
  rw [norm_smul, he, mul_one, Real.norm_eq_abs]

/-- The n=m=1 specialization in literal Euclidean coordinates. -/
theorem taylorPeano_one_coordinate (k : ℕ) (hk : 1 ≤ k) (U : Set (E 1))
    (f : E 1 → E 1) (a : E 1) (hf : TimesDifferentiableAt k U f a) :
    (fun t : ℝ => f (a+t • standardBasis 1 0) 0 - ∑ j ∈ Finset.range (k+1),
      iteratedDeriv j (fun s : ℝ => f (a+s • standardBasis 1 0) 0) 0 /
        (j.factorial : ℝ) * t^j) =o[𝓝[≠] (0 : ℝ)] (fun t => |t|^k) := by
  have hr : taylorRemainder k f a =o[𝓝 (0 : E 1)] (fun h => ‖h‖^k) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    exact taylorPeano_succ j U f a hf
  have hl : Tendsto (fun t : ℝ => t • standardBasis 1 0) (𝓝 0) (𝓝 (0 : E 1)) := by
    have hl : Tendsto (fun t : ℝ => t • standardBasis 1 0) (𝓝 0)
        (𝓝 ((0 : ℝ) • standardBasis 1 0)) := tendsto_id.smul tendsto_const_nhds
    simpa only [zero_smul] using hl
  have hh := hr.comp_tendsto hl
  let pr : E 1 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 1 => ℝ) 0
  have hp := (pr.isBigO_comp (fun t : ℝ => taylorRemainder k f a
    (t • standardBasis 1 0)) (𝓝 0)).trans_isLittleO hh
  have he (t : ℝ) : pr (taylorRemainder k f a (t • standardBasis 1 0)) =
      f (a+t • standardBasis 1 0) 0 - ∑ j ∈ Finset.range (k+1),
      iteratedDeriv j (fun s : ℝ => f (a+s • standardBasis 1 0) 0) 0 /
        (j.factorial : ℝ) * t^j := by
    change f (a+t • standardBasis 1 0) 0 - taylorPolynomial k f a (t • standardBasis 1 0) 0 = _
    rw [taylorPolynomial_one_coordinate k U f a _ hf]
    simp [PiLp.smul_apply, standardBasis_apply]
  exact (hp.congr he (fun t => by simp only [Function.comp_apply, norm_one_coordinate_smul])).mono nhdsWithin_le_nhds

/-- At scalar order zero the Euclidean coordinate statement is just continuity. -/
theorem taylorPeano_one_coordinate_zero (f : E 1 → E 1) (a : E 1)
    (hf : ContinuousAt f a) :
    (fun t : ℝ => f (a+t • standardBasis 1 0) 0 - f a 0) =o[𝓝 (0 : ℝ)]
      (fun _ => (1 : ℝ)) := by
  have hl : Tendsto (fun t : ℝ => a+t • standardBasis 1 0) (𝓝 0) (𝓝 a) := by
    have hl : Tendsto (fun t : ℝ => a+t • standardBasis 1 0) (𝓝 0)
        (𝓝 (a+(0 : ℝ) • standardBasis 1 0)) :=
      tendsto_const_nhds.add (tendsto_id.smul tendsto_const_nhds)
    simpa only [zero_smul, add_zero] using hl
  let pr : E 1 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 1 => ℝ) 0
  have hc := pr.continuous.continuousAt.comp hf
  exact (hc.isLittleO (F := ℝ)).comp_tendsto hl

end D04
