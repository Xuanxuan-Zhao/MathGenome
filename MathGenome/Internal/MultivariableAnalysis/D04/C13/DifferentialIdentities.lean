import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.DifferentialIdentities
import MathGenome.Internal.MultivariableAnalysis.D04.C13.ExteriorDerivative
import MathGenome.Internal.MultivariableAnalysis.D04.C13.PullbackCalculus
import MathGenome.Internal.MultivariableAnalysis.D04.C03.Symmetry

noncomputable section
open scoped BigOperators Classical
open Set Filter Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
namespace D04

/-- The C²/C¹ regularity assertion in the naturality theorem. -/
theorem pullback_C1 {m n k : ℕ} (U : Set (E m)) (V : Set (E n))
    (f : E m → E n) (ω : FormField n k) (hU : IsOpen U)
    (hmap : MapsTo f U V) (hf : CrOn 2 U f) (hω : IsCrForm (some 1) V ω) :
    IsCrForm (some 1) U (pullback f ω) :=
  pullback_isCrForm 1 U V f ω hU hmap hf hω

/-- Wedge a one-covector on the left, in successor-degree notation. -/
def prependCovector {n k : ℕ} (l : Covector (E n) 1) (A : Covector (E n) k) :
    Covector (E n) (k + 1) := castCovector (Nat.add_comm 1 k) (wedge l A)

@[simp] theorem castCovector_add {n a b : ℕ} (h : a = b)
    (A B : Covector (E n) a) : castCovector h (A + B) = castCovector h A + castCovector h B := by
  subst b; rfl

@[simp] theorem castCovector_smul {n a b : ℕ} (h : a = b)
    (c : ℝ) (A : Covector (E n) a) : castCovector h (c • A) = c • castCovector h A := by
  subst b; rfl

@[simp] theorem castCovector_rfl {n a : ℕ} (h : a = a) (A : Covector (E n) a) :
    castCovector h A = A := rfl

@[simp] theorem castCovector_sum {n a b : ℕ} {ι : Type*} (h : a = b)
    (s : Finset ι) (A : ι → Covector (E n) a) :
    castCovector h (∑ i ∈ s, A i) = ∑ i ∈ s, castCovector h (A i) := by
  subst b; rfl

@[simp] theorem wedge_zero_left {n p q : ℕ} (B : Covector (E n) q) :
    wedge (0 : Covector (E n) p) B = 0 := by
  ext v; simp [wedge_apply]

@[simp] theorem wedge_zero_right {n p q : ℕ} (A : Covector (E n) p) :
    wedge A (0 : Covector (E n) q) = 0 := by
  ext v; simp [wedge_apply]

theorem wedge_sum_left {n p q : ℕ} {ι : Type*} (s : Finset ι)
    (A : ι → Covector (E n) p) (B : Covector (E n) q) :
    wedge (∑ i ∈ s, A i) B = ∑ i ∈ s, wedge (A i) B := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, wedge_add_left, ih]

theorem wedge_sum_right {n p q : ℕ} {ι : Type*} (s : Finset ι)
    (A : Covector (E n) p) (B : ι → Covector (E n) q) :
    wedge A (∑ i ∈ s, B i) = ∑ i ∈ s, wedge A (B i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, wedge_add_right, ih]

theorem prependCovector_sum {n k : ℕ} {ι : Type*} (s : Finset ι)
    (l : Covector (E n) 1) (A : ι → Covector (E n) k) :
    prependCovector l (∑ i ∈ s, A i) = ∑ i ∈ s, prependCovector l (A i) := by
  simp only [prependCovector, wedge_sum_right, castCovector_sum]

@[simp] theorem prependCovector_smul {n k : ℕ} (c : ℝ)
    (l : Covector (E n) 1) (A : Covector (E n) k) :
    prependCovector l (c • A) = c • prependCovector l A := by
  simp only [prependCovector, wedge_smul_right, castCovector_smul]

/-- Replace a directional-derivative selector by a genuine derivative. -/
theorem scalarPartialDerivative_eq_fderiv {n : ℕ} (a : E n → ℝ) (x : E n)
    (ha : DifferentiableAt ℝ a x) (j : Fin n) :
    scalarPartialDerivative a x j = fderiv ℝ a x (standardBasis n j) := by
  exact scalarPartialDerivative_eq Set.univ a x _
    ((hasTotalDerivative_iff_hasFDerivAt Set.univ a _ x isOpen_univ (mem_univ x)).mpr
      ha.hasFDerivAt) j

/-- Coordinate differentiation of a finite linear combination of scalar functions. -/
theorem scalarPartialDerivative_sum_mul_const {n : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → E n → ℝ) (c : ι → ℝ) (x : E n)
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) (j : Fin n) :
    scalarPartialDerivative (fun y => ∑ i, a i y * c i) x j =
      ∑ i, scalarPartialDerivative (a i) x j * c i := by
  have hd : HasFDerivAt (fun y => ∑ i, a i y * c i)
      (∑ i, c i • fderiv ℝ (a i) x) x := by
    simpa only [Finset.sum_fn] using
      HasFDerivAt.sum (u := Finset.univ) (fun i _ => (ha i).hasFDerivAt.mul_const (c i))
  rw [scalarPartialDerivative_eq_fderiv _ _ hd.differentiableAt, hd.fderiv]
  simp only [sum_apply, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul, scalarPartialDerivative_eq_fderiv _ _ (ha _)]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exterior differentiation of a finite expansion in arbitrary constant covectors.
This is the linearity step used by the coordinate proofs. -/
theorem exteriorDerivative_sum_smul_const {n k : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → E n → ℝ) (A : ι → Covector (E n) k) (x : E n)
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) :
    exteriorDerivative (fun y => ∑ i, a i y • A i) x =
      ∑ i, ∑ j : Fin n, scalarPartialDerivative (a i) x j •
        prependCovector (coordinateOneForm n j) (A i) := by
  have hc (I : MultiIndex n k) :
      (fun y => coefficient (standardBasis n) (∑ i, a i y • A i) I) =
        fun y => ∑ i, a i y * coefficient (standardBasis n) (A i) I := by
    funext y
    simp only [coefficient, Specs.D04.C13.NormalizedFormsAndWedge.Model.coefficient,
      sum_apply, smul_apply, smul_eq_mul]
  rw [exteriorDerivative_formula]
  simp_rw [hc, scalarPartialDerivative_sum_mul_const a _ x ha]
  simp only [Finset.sum_smul]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext j
    rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  conv_rhs => rw [covector_expansion (standardBasis n) (A i)]
  simp only [prependCovector_sum, prependCovector_smul, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro I _
  rfl

@[simp] theorem wedge_cast_left {n a b q : ℕ} (h : a = b)
    (A : Covector (E n) a) (B : Covector (E n) q) :
    wedge (castCovector h A) B = castCovector (congrArg (· + q) h) (wedge A B) := by
  subst b; rfl

@[simp] theorem wedge_cast_right {n p a b : ℕ} (h : a = b)
    (A : Covector (E n) p) (B : Covector (E n) a) :
    wedge A (castCovector h B) = castCovector (congrArg (p + ·) h) (wedge A B) := by
  subst b; rfl

/-- Associating a one-form on the left involves no extra sign. -/
theorem prependCovector_wedge {n p q : ℕ} (l : Covector (E n) 1)
    (A : Covector (E n) p) (B : Covector (E n) q) :
    prependCovector l (wedge A B) =
      castCovector (by omega : (p + 1) + q = (p + q) + 1)
        (wedge (prependCovector l A) B) := by
  unfold prependCovector
  rw [← wedge_assoc l A B]
  simp only [wedge_cast_left, castCovector_trans]

/-- Moving the differentiating one-form past a p-covector produces (-1)^p. -/
theorem prependCovector_wedge_right {n p q : ℕ} (l : Covector (E n) 1)
    (A : Covector (E n) p) (B : Covector (E n) q) :
    prependCovector l (wedge A B) =
      (-1 : ℝ) ^ p • castCovector (by omega : p + (q + 1) = (p + q) + 1)
        (wedge A (prependCovector l B)) := by
  unfold prependCovector
  rw [← wedge_assoc l A B, wedge_comm l A]
  simp only [one_mul, wedge_smul_left, wedge_cast_left, castCovector_smul,
    castCovector_trans, wedge_cast_right]
  rw [← wedge_assoc A l B]
  simp only [castCovector_trans]

theorem scalarPartialDerivative_mul {n : ℕ} (a b : E n → ℝ) (x : E n)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) (j : Fin n) :
    scalarPartialDerivative (fun y => a y * b y) x j =
      scalarPartialDerivative a x j * b x + a x * scalarPartialDerivative b x j := by
  rw [scalarPartialDerivative_eq_fderiv (fun y => a y * b y) x (ha.mul hb),
    fderiv_fun_mul ha hb,
    scalarPartialDerivative_eq_fderiv _ _ ha, scalarPartialDerivative_eq_fderiv _ _ hb]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The defining coordinate expansion with the one-covector factored out. -/
theorem exteriorDerivative_expansion {n k : ℕ} (ω : FormField n k) (x : E n) :
    exteriorDerivative ω x = ∑ I : MultiIndex n k, ∑ j : Fin n,
      scalarPartialDerivative (fun y => coefficient (standardBasis n) (ω y) I) x j •
        prependCovector (coordinateOneForm n j) (dx (standardBasis n) I) := rfl

/-- C¹ coefficients give genuine differentiability at each point of the domain. -/
theorem isCrForm_coefficient_differentiableAt {n k : ℕ} (U : Set (E n))
    (ω : FormField n k) (hω : IsCrForm (some 1) U ω) (x : E n) (hx : x ∈ U)
    (I : MultiIndex n k) :
    DifferentiableAt ℝ (fun y => coefficient (standardBasis n) (ω y) I) x :=
  (totalDifferentiableAt_iff_differentiableAt U _ x hω.1 hx).mp ((hω.2 I).1 x hx)

/-- Graded Leibniz rule for the normalized coefficient exterior derivative. -/
theorem exteriorDerivative_wedge {n p q : ℕ} (U : Set (E n))
    (α : FormField n p) (β : FormField n q)
    (hα : IsCrForm (some 1) U α) (hβ : IsCrForm (some 1) U β) (x : E n) (hx : x ∈ U) :
    exteriorDerivative (fun y => wedge (α y) (β y)) x =
      castCovector (by omega : (p + 1) + q = (p + q) + 1)
        (wedge (exteriorDerivative α x) (β x)) +
      (-1 : ℝ) ^ p • castCovector (by omega : p + (q + 1) = (p + q) + 1)
        (wedge (α x) (exteriorDerivative β x)) := by
  let a (I : MultiIndex n p) (y : E n) := coefficient (standardBasis n) (α y) I
  let b (J : MultiIndex n q) (y : E n) := coefficient (standardBasis n) (β y) J
  have ha := isCrForm_coefficient_differentiableAt U α hα x hx
  have hb := isCrForm_coefficient_differentiableAt U β hβ x hx
  have hexp : (fun y => wedge (α y) (β y)) = fun y =>
      ∑ t : MultiIndex n p × MultiIndex n q, (a t.1 y * b t.2 y) •
        wedge (dx (standardBasis n) t.1) (dx (standardBasis n) t.2) := by
    funext y
    conv_lhs => rw [covector_expansion (standardBasis n) (α y),
      covector_expansion (standardBasis n) (β y)]
    simp only [wedge_sum_left, wedge_sum_right, wedge_smul_left, wedge_smul_right,
      Finset.smul_sum, smul_smul, Fintype.sum_prod_type, a, b]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I _
    apply Finset.sum_congr rfl
    intro J _
    rw [mul_comm]
  rw [hexp]
  rw [exteriorDerivative_sum_smul_const
    (fun t : MultiIndex n p × MultiIndex n q => fun y => a t.1 y * b t.2 y)
    (fun t => wedge (dx (standardBasis n) t.1) (dx (standardBasis n) t.2)) x
    (fun t => (ha t.1).mul (hb t.2))]
  simp only [Fintype.sum_prod_type]
  have hmul (I : MultiIndex n p) (J : MultiIndex n q) (j : Fin n) :=
    scalarPartialDerivative_mul (a I) (b J) x (ha I) (hb J) j
  simp_rw [hmul]
  simp only [add_smul, Finset.sum_add_distrib]
  congr 1
  · rw [exteriorDerivative_expansion]
    conv_rhs => rw [covector_expansion (standardBasis n) (β x)]
    simp only [wedge_sum_left, wedge_sum_right, wedge_smul_left, wedge_smul_right,
      Finset.smul_sum, smul_smul, castCovector_sum, castCovector_smul]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I _
    apply Finset.sum_congr rfl
    intro J _
    apply Finset.sum_congr rfl
    intro j _
    rw [prependCovector_wedge]
    congr 1
    ring
  · rw [exteriorDerivative_expansion]
    conv_rhs => rw [covector_expansion (standardBasis n) (α x)]
    simp only [wedge_sum_left, wedge_sum_right, wedge_smul_left, wedge_smul_right,
      Finset.smul_sum, smul_smul, castCovector_sum, castCovector_smul]
    conv_rhs =>
      arg 2
      ext J
      rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I _
    apply Finset.sum_congr rfl
    intro J _
    apply Finset.sum_congr rfl
    intro j _
    rw [prependCovector_wedge_right, smul_smul]
    congr 1
    ring

@[simp] theorem castCovector_neg {n a b : ℕ} (h : a = b) (A : Covector (E n) a) :
    castCovector h (-A) = -castCovector h A := by
  subst b; rfl

/-- The two leading one-covectors anticommute, at every remaining degree. -/
theorem prependCovector_swap {n k : ℕ} (l t : Covector (E n) 1)
    (A : Covector (E n) k) :
    prependCovector l (prependCovector t A) = -prependCovector t (prependCovector l A) := by
  unfold prependCovector
  simp only [wedge_cast_right, castCovector_trans]
  rw [← wedge_assoc l t A, ← wedge_assoc t l A]
  simp only [castCovector_trans]
  rw [wedge_comm l t]
  simp only [Nat.mul_one, pow_one, castCovector_rfl,
    wedge_smul_left, castCovector_smul]
  ext v
  simp only [smul_apply, neg_apply, smul_eq_mul]
  ring

/-- Continuous second partials commute for the shared coordinate selectors. -/
theorem scalarPartialDerivative_comm {n : ℕ} (U : Set (E n)) (a : E n → ℝ)
    (hU : IsOpen U) (ha : CrOn 2 U a) (x : E n) (hx : x ∈ U) (i j : Fin n) :
    scalarPartialDerivative (fun y => scalarPartialDerivative a y j) x i =
      scalarPartialDerivative (fun y => scalarPartialDerivative a y i) x j := by
  have hs := hessian_symmetric U a x (crOn_timesDifferentiableAt 2 U a hU ha x hx)
  exact hs.apply j i

/-- Nilpotence under C² regularity, including zero and excessive degrees. -/
theorem exteriorDerivative_squared {n k : ℕ} (U : Set (E n)) (ω : FormField n k)
    (hω : IsCrForm (some 2) U ω) (x : E n) (hx : x ∈ U) :
    exteriorDerivative (exteriorDerivative ω) x = 0 := by
  let a (I : MultiIndex n k) (y : E n) := coefficient (standardBasis n) (ω y) I
  have hpartial (I : MultiIndex n k) (j : Fin n) :
      DifferentiableAt ℝ (fun y => scalarPartialDerivative (a I) y j) x := by
    have hc := crOn_scalarPartialDerivative 1 U (a I) hω.1 (hω.2 I) j
    exact (totalDifferentiableAt_iff_differentiableAt U _ x hω.1 hx).mp (hc.1 x hx)
  have hexp : exteriorDerivative ω = fun y => ∑ t : MultiIndex n k × Fin n,
      scalarPartialDerivative (a t.1) y t.2 •
        prependCovector (coordinateOneForm n t.2) (dx (standardBasis n) t.1) := by
    funext y
    rw [exteriorDerivative_expansion]
    simp only [Fintype.sum_prod_type, a]
  rw [hexp, exteriorDerivative_sum_smul_const
    (fun t : MultiIndex n k × Fin n => fun y => scalarPartialDerivative (a t.1) y t.2)
    (fun t => prependCovector (coordinateOneForm n t.2) (dx (standardBasis n) t.1)) x
    (fun t => hpartial t.1 t.2)]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro I _
  let S := ∑ j : Fin n, ∑ i : Fin n,
    scalarPartialDerivative (fun y => scalarPartialDerivative (a I) y j) x i •
      prependCovector (coordinateOneForm n i)
        (prependCovector (coordinateOneForm n j) (dx (standardBasis n) I))
  change S = 0
  have hneg : S = -S := by
    dsimp [S]
    conv_rhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [scalarPartialDerivative_comm U (a I) hω.1 (hω.2 I) x hx i j,
      prependCovector_swap, smul_neg]
  have hz : (2 : ℝ) • S = 0 := by
    rw [two_smul]
    calc S + S = -S + S := congrArg (· + S) hneg
         _ = 0 := neg_add_cancel S
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

/-- Exterior differentiation respects degree transport. -/
theorem exteriorDerivative_cast {n a b : ℕ} (h : a = b) (ω : FormField n a) (x : E n) :
    exteriorDerivative (fun y => castCovector h (ω y)) x =
      castCovector (congrArg (· + 1) h) (exteriorDerivative ω x) := by
  subst b; rfl

theorem isCrForm_const {n k : ℕ} (r : ℕ) (U : Set (E n)) (hU : IsOpen U)
    (A : Covector (E n) k) : IsCrForm (some r) U (fun _ => A) := by
  refine ⟨hU, fun I => ?_⟩
  exact (crOn_iff_contDiffOn r U _ hU).mpr contDiffOn_const

@[simp] theorem exteriorDerivative_const {n k : ℕ} (A : Covector (E n) k) :
    exteriorDerivative (fun _ : E n => A) = 0 := by
  funext x
  rw [exteriorDerivative_expansion]
  apply Finset.sum_eq_zero
  intro I _
  apply Finset.sum_eq_zero
  intro j _
  rw [scalarPartialDerivative_eq_fderiv (fun _ : E n => coefficient (standardBasis n) A I) x
    (differentiableAt_const _), fderiv_fun_const]
  simp

/-- The scalar-factor version of the graded product rule. -/
theorem exteriorDerivative_function_smul {n k : ℕ} (U : Set (E n))
    (a : E n → ℝ) (ω : FormField n k) (hU : IsOpen U) (ha : CrOn 1 U a)
    (hω : IsCrForm (some 1) U ω) (x : E n) (hx : x ∈ U) :
    exteriorDerivative (fun y => a y • ω y) x =
      prependCovector (exteriorDerivative (fun y => scalarCovector (a y)) x) (ω x) +
        a x • exteriorDerivative ω x := by
  have hscalar : IsCrForm (some 1) U (fun y => scalarCovector (V := E n) (a y)) :=
    (isCrForm_zero_iff (some 1) U a).mpr ⟨hU, ha⟩
  have he : (fun y => a y • ω y) =
      fun y => castCovector (Nat.zero_add k) (wedge (scalarCovector (a y)) (ω y)) := by
    funext y
    exact (wedge_scalar_left (a y) (ω y)).symm
  rw [he, exteriorDerivative_cast, exteriorDerivative_wedge U _ _ hscalar hω x hx]
  simp only [castCovector_add, castCovector_trans,
    pow_zero, one_smul, wedge_scalar_left]
  rfl

/-- Locality holds even for the derivative selectors before regularity is imposed. -/
theorem scalarPartialDerivative_congr {n : ℕ} (U : Set (E n)) (a b : E n → ℝ)
    (hU : IsOpen U) (he : EqOn a b U) (x : E n) (hx : x ∈ U) (j : Fin n) :
    scalarPartialDerivative a x j = scalarPartialDerivative b x j := by
  have hline : Tendsto (fun t : ℝ => x + t • standardBasis n j) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x + t • standardBasis n j) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa using hc.tendsto (0 : ℝ)
  have hh : (fun t : ℝ => a (x + t • standardBasis n j)) =ᶠ[𝓝 0]
      (fun t => b (x + t • standardBasis n j)) :=
    (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) he).comp_tendsto hline
  exact hh.deriv_eq

theorem exteriorDerivative_congr {n k : ℕ} (U : Set (E n)) (α β : FormField n k)
    (hU : IsOpen U) (he : EqOn α β U) (x : E n) (hx : x ∈ U) :
    exteriorDerivative α x = exteriorDerivative β x := by
  simp only [exteriorDerivative_expansion]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro j _
  rw [scalarPartialDerivative_congr U _ _ hU (fun y hy => congrArg
    (fun A => coefficient (standardBasis n) A I) (he hy)) x hx j]

/-- Exterior differentiation commutes with a finite sum of C¹ forms. -/
theorem exteriorDerivative_sum {n k : ℕ} {ι : Type*} [Fintype ι]
    (U : Set (E n)) (ω : ι → FormField n k) (_hU : IsOpen U)
    (hω : ∀ i, IsCrForm (some 1) U (ω i)) (x : E n) (hx : x ∈ U) :
    exteriorDerivative (fun y => ∑ i, ω i y) x = ∑ i, exteriorDerivative (ω i) x := by
  have hc (I : MultiIndex n k) :
      (fun y => coefficient (standardBasis n) (∑ i, ω i y) I) =
        fun y => ∑ i, coefficient (standardBasis n) (ω i y) I * 1 := by
    funext y
    simp only [coefficient, Specs.D04.C13.NormalizedFormsAndWedge.Model.coefficient,
      sum_apply, mul_one]
  simp only [exteriorDerivative_expansion]
  simp_rw [hc, scalarPartialDerivative_sum_mul_const _ _ x
    (fun i => isCrForm_coefficient_differentiableAt U (ω i) (hω i) x hx _)]
  simp only [mul_one, Finset.sum_smul]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext j
    rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

@[simp] theorem castCovector_zero {n a b : ℕ} (h : a = b) :
    castCovector h (0 : Covector (E n) a) = 0 := by
  subst b; rfl

@[simp] theorem prependCovector_zero_left {n k : ℕ} (A : Covector (E n) k) :
    prependCovector 0 A = 0 := by simp [prependCovector]

theorem isCrForm_function_smul {n k : ℕ} (r : ℕ) (U : Set (E n))
    (a : E n → ℝ) (ω : FormField n k) (hU : IsOpen U) (ha : CrOn r U a)
    (hω : IsCrForm (some r) U ω) : IsCrForm (some r) U (fun y => a y • ω y) := by
  refine ⟨hU, fun I => ?_⟩
  apply (crOn_iff_contDiffOn r U _ hU).mpr
  exact ((crOn_iff_contDiffOn r U a hU).mp ha).mul
    ((crOn_iff_contDiffOn r U _ hU).mp (hω.2 I))

/-- A pulled-back coordinate one-form is the differential of a C² coordinate. -/
theorem pullback_coordinate_closed {m n : ℕ} (U : Set (E m)) (f : E m → E n)
    (hU : IsOpen U) (hf : CrOn 2 U f) (i : Fin n) (x : E m) (hx : x ∈ U) :
    exteriorDerivative (pullback f (fun _ => coordinateOneForm n i)) x = 0 := by
  let a : E m → ℝ := fun y => f y i
  have ha : CrOn 2 U a := by
    apply (crOn_iff_contDiffOn 2 U a hU).mpr
    exact (contDiffOn_piLp 2).mp ((crOn_iff_contDiffOn 2 U f hU).mp hf) i
  have he : EqOn (pullback f (fun _ => coordinateOneForm n i))
      (exteriorDerivative (fun y => scalarCovector (a y))) U := by
    intro y hy
    obtain ⟨A, hA⟩ := hf.1 y hy
    rw [exteriorDerivative_scalar U a y _ (component_hasTotalDerivative U f y A hA i)]
    ext v
    simp only [pullback_apply, coordinateOneForm_apply, linearCovector_apply,
      totalDerivative_eq U f A y hA]
    rfl
  rw [exteriorDerivative_congr U _ _ hU he x hx]
  exact exteriorDerivative_squared U _ ((isCrForm_zero_iff (some 2) U a).mpr ⟨hU, ha⟩) x hx

/-- Pullbacks of wedges of coordinate differentials are closed. -/
theorem pullback_coordinate_wedge_closed {m n : ℕ} (U : Set (E m)) (f : E m → E n)
    (hU : IsOpen U) (hf : CrOn 2 U f) (k : ℕ) (is : Fin k → Fin n)
    (x : E m) (hx : x ∈ U) :
    exteriorDerivative (pullback f (fun _ => wedgeList k
      (fun i => (standardBasis n).coord (is i)))) x = 0 := by
  induction k with
  | zero =>
    change exteriorDerivative (pullback f (fun _ => scalarCovector (1 : ℝ))) x = 0
    rw [pullback_zero_degree]
    exact congrFun (exteriorDerivative_const (scalarCovector (V := E m) 1)) x
  | succ k ih =>
    let A := wedgeList k (fun i => (standardBasis n).coord (is i.castSucc))
    let B := coordinateOneForm n (is (Fin.last k))
    have hA : IsCrForm (some 1) U (pullback f (fun _ => A)) :=
      pullback_C1 U univ f _ hU (fun _ _ => mem_univ _) hf (isCrForm_const 1 univ isOpen_univ A)
    have hB : IsCrForm (some 1) U (pullback f (fun _ => B)) :=
      pullback_C1 U univ f _ hU (fun _ _ => mem_univ _) hf (isCrForm_const 1 univ isOpen_univ B)
    change exteriorDerivative (pullback f (fun _ => wedge A B)) x = 0
    rw [pullback_wedge, exteriorDerivative_wedge U _ _ hA hB x hx]
    have hzA : exteriorDerivative (pullback f (fun _ => A)) x = 0 := ih _
    have hzB : exteriorDerivative (pullback f (fun _ => B)) x = 0 :=
      pullback_coordinate_closed U f hU hf _ x hx
    simp only [hzA, hzB, wedge_zero_left, wedge_zero_right, castCovector_zero, smul_zero, add_zero]

/-- Each coordinate basis covector has a closed pullback under a C² map. -/
theorem pullback_dx_closed {m n k : ℕ} (U : Set (E m)) (f : E m → E n)
    (hU : IsOpen U) (hf : CrOn 2 U f) (I : MultiIndex n k) (x : E m) (hx : x ∈ U) :
    exteriorDerivative (pullback f (fun _ => dx (standardBasis n) I)) x = 0 := by
  rw [← coordinate_wedge (standardBasis n) I]
  exact pullback_coordinate_wedge_closed U f hU hf k (indexTuple I) x hx

/-- Scalar chain rule, expressed as pullback of a differential. -/
theorem exteriorDerivative_scalar_pullback {m n : ℕ} (U : Set (E m)) (V : Set (E n))
    (f : E m → E n) (a : E n → ℝ) (_hU : IsOpen U) (_hV : IsOpen V)
    (hmap : MapsTo f U V) (hf : CrOn 1 U f) (ha : CrOn 1 V a) (x : E m) (hx : x ∈ U) :
    exteriorDerivative (fun y => scalarCovector (a (f y))) x =
      pullback f (exteriorDerivative (fun y => scalarCovector (a y))) x := by
  obtain ⟨A, hA⟩ := hf.1 x hx
  obtain ⟨B, hB⟩ := ha.1 (f x) (hmap hx)
  have hc := hasTotalDerivative_comp U V f a x A B hA hB
  change exteriorDerivative (fun y => scalarCovector ((a ∘ f) y)) x = _
  rw [exteriorDerivative_scalar U (a ∘ f) x (B.comp A) hc]
  ext v
  simp only [pullback_apply, exteriorDerivative_scalar V a (f x) B hB,
    linearCovector_apply, totalDerivative_eq U f A x hA]
  rfl

/-- The coefficient formula can equivalently be written as ∑ da_I ∧ dx_I. -/
theorem exteriorDerivative_coefficient_differentials {n k : ℕ} (U : Set (E n))
    (ω : FormField n k) (hω : IsCrForm (some 1) U ω) (x : E n) (hx : x ∈ U) :
    exteriorDerivative ω x = ∑ I : MultiIndex n k,
      prependCovector (exteriorDerivative (fun y => scalarCovector
        (coefficient (standardBasis n) (ω y) I)) x) (dx (standardBasis n) I) := by
  let a (I : MultiIndex n k) (y : E n) := coefficient (standardBasis n) (ω y) I
  have he : ω = fun y => ∑ I : MultiIndex n k, a I y • dx (standardBasis n) I :=
    funext (fun y => covector_expansion (standardBasis n) (ω y))
  have hterms (I : MultiIndex n k) : IsCrForm (some 1) U
      (fun y => a I y • dx (standardBasis n) I) :=
    isCrForm_function_smul 1 U (a I) _ hω.1 (hω.2 I)
      (isCrForm_const 1 U hω.1 _)
  calc
    exteriorDerivative ω x = exteriorDerivative
        (fun y => ∑ I : MultiIndex n k, a I y • dx (standardBasis n) I) x := congrArg
          (fun η => exteriorDerivative η x) he
    _ = ∑ I : MultiIndex n k, exteriorDerivative (fun y => a I y • dx (standardBasis n) I) x :=
      exteriorDerivative_sum U _ hω.1 hterms x hx
    _ = _ := by
      apply Finset.sum_congr rfl
      intro I _
      rw [exteriorDerivative_function_smul U (a I) _ hω.1 (hω.2 I)
        (isCrForm_const 1 U hω.1 _) x hx]
      simp only [exteriorDerivative_const, Pi.zero_apply, smul_zero, add_zero]
      rfl

/-- Pullback commutes with the harmless degree transports. -/
theorem pullback_cast {m n a b : ℕ} (h : a = b) (f : E m → E n) (ω : FormField n a)
    (x : E m) : pullback f (fun y => castCovector h (ω y)) x =
      castCovector h (pullback f ω x) := by
  subst b; rfl

theorem pullback_prepend {m n k : ℕ} (f : E m → E n) (α : FormField n 1)
    (β : FormField n k) (x : E m) :
    pullback f (fun y => prependCovector (α y) (β y)) x =
      prependCovector (pullback f α x) (pullback f β x) := by
  unfold prependCovector
  rw [pullback_cast, pullback_wedge]

theorem pullback_sum {m n k : ℕ} {ι : Type*} [Fintype ι]
    (f : E m → E n) (ω : ι → FormField n k) (x : E m) :
    pullback f (fun y => ∑ i, ω i y) x = ∑ i, pullback f (ω i) x := by
  ext v
  simp only [pullback_apply, sum_apply]

/-- Naturality of the coefficient exterior derivative at precisely C²/C¹ regularity. -/
theorem exteriorDerivative_pullback {m n k : ℕ} (U : Set (E m)) (V : Set (E n))
    (f : E m → E n) (ω : FormField n k) (hU : IsOpen U) (hmap : MapsTo f U V)
    (hf : CrOn 2 U f) (hω : IsCrForm (some 1) V ω) (x : E m) (hx : x ∈ U) :
    exteriorDerivative (pullback f ω) x = pullback f (exteriorDerivative ω) x := by
  let a (I : MultiIndex n k) (y : E n) := coefficient (standardBasis n) (ω y) I
  let B (I : MultiIndex n k) : FormField m k := pullback f (fun _ => dx (standardBasis n) I)
  have hf1 : CrOn 1 U f := (crOn_iff_contDiffOn 1 U f hU).mpr
    (((crOn_iff_contDiffOn 2 U f hU).mp hf).of_le (by norm_num))
  have hB (I : MultiIndex n k) : IsCrForm (some 1) U (B I) :=
    pullback_C1 U V f _ hU hmap hf (isCrForm_const 1 V hω.1 _)
  have hacomp (I : MultiIndex n k) : CrOn 1 U (fun y => a I (f y)) :=
    crOn_comp 1 U V f (a I) hU hω.1 hmap hf1 (hω.2 I)
  have hterms (I : MultiIndex n k) : IsCrForm (some 1) U
      (fun y => a I (f y) • B I y) :=
    isCrForm_function_smul 1 U _ _ hU (hacomp I) (hB I)
  have he : pullback f ω = fun y => ∑ I : MultiIndex n k, a I (f y) • B I y := by
    funext y
    ext v
    simp only [pullback_apply, sum_apply, smul_apply, smul_eq_mul]
    exact formField_evaluation ω (f y) (fun i => totalDerivative f y (v i))
  rw [he, exteriorDerivative_sum U _ hU hterms x hx]
  have hright : pullback f (exteriorDerivative ω) x = ∑ I : MultiIndex n k,
      prependCovector (pullback f (exteriorDerivative (fun y => scalarCovector (a I y))) x)
        (B I x) := by
    have hval := exteriorDerivative_coefficient_differentials V ω hω (f x) (hmap hx)
    change (exteriorDerivative ω (f x)).compLinearMap (totalDerivative f x).toLinearMap = _
    rw [hval]
    change pullback f (fun y => ∑ I : MultiIndex n k,
      prependCovector (exteriorDerivative (fun z => scalarCovector (a I z)) y)
        (dx (standardBasis n) I)) x = _
    rw [pullback_sum]
    apply Finset.sum_congr rfl
    intro I _
    exact pullback_prepend f _ _ x
  rw [hright]
  apply Finset.sum_congr rfl
  intro I _
  rw [exteriorDerivative_function_smul U _ _ hU (hacomp I) (hB I) x hx]
  have hz : exteriorDerivative (B I) x = 0 := pullback_dx_closed U f hU hf I x hx
  rw [hz, smul_zero, add_zero,
    exteriorDerivative_scalar_pullback U V f (a I) hU hω.1 hmap hf1 (hω.2 I) x hx]

end D04
