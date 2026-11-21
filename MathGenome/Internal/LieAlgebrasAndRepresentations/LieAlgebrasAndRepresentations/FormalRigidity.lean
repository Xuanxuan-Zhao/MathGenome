import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FormalRigidity
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.InfinitesimalDeformations
import Mathlib.Tactic.Abel

noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace LieAlgebrasAndRepresentations.FormalRigidity
open LieModule.Cohomology LieAlgebrasAndRepresentations.AbelianExtensions
variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]

/-- Divisibility by t^n, in the complete coefficient module. -/
def Vanishes (n : ℕ) (x : Series g) : Prop := ∀ i, i < n → x i = 0

def Agrees (n : ℕ) (x y : Series g) : Prop := ∀ i, i < n → x i = y i

def IsFormal (f : Series g →ₗ[k] Series g) : Prop :=
  ∀ x, f (shift k g 1 x) = shift k g 1 (f x)

@[simp] theorem shift_apply (n : ℕ) (x : Series g) (i : ℕ) :
    shift k g n x i = if n ≤ i then x (i-n) else 0 := rfl

@[simp] theorem shift_zero (x : Series g) : shift k g 0 x = x := by
  ext i; simp

@[simp] theorem shift_at (n : ℕ) (x : Series g) : shift k g n x n = x 0 := by simp

@[simp] theorem shift_one_zero (x : Series g) : shift k g 1 x 0 = 0 := by simp

@[simp] theorem shift_one_succ (x : Series g) (n : ℕ) :
    shift k g 1 x (n+1) = x n := by simp

/-- The shift is multiplication by the indicated power of the formal parameter. -/
theorem scalar_parameter_pow (n : ℕ) (x : Series g) :
    scalar ((PowerSeries.X : PowerSeries k) ^ n) x = shift k g n x := by
  funext i
  simp only [scalar, PowerSeries.coeff_X_pow, shift_apply]
  by_cases h : n ≤ i
  · rw [ite_eq_left h, Finset.sum_eq_single n]
    · simp
    · intro j _ hj
      simp [hj]
    · intro hn
      exact (hn (Finset.mem_range.mpr (Nat.lt_succ_of_le h))).elim
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro j hj
    have hjn : j ≠ n := ne_of_lt ((Finset.mem_range.mp hj).trans_le (Nat.lt_of_not_ge h))
    simp [hjn]

@[simp] theorem constant_zero (x : g) : constant k g x 0 = x := by
  simp [constant]

@[simp] theorem constant_succ (x : g) (n : ℕ) : constant k g x (n+1) = 0 := by
  simp [constant]

theorem shift_add (n m : ℕ) (x : Series g) :
    shift k g (n+m) x = shift k g n (shift k g m x) := by
  ext i
  simp only [shift_apply]
  by_cases h : n+m ≤ i
  · have hn : n ≤ i := by omega
    have hm : m ≤ i-n := by omega
    simp [h, hn, hm, Nat.sub_sub]
  · by_cases hn : n ≤ i
    · have hm : ¬ m ≤ i-n := by omega
      simp [h, hn, hm]
    · simp [h, hn]

theorem shift_vanishes (n : ℕ) (x : Series g) : Vanishes n (shift k g n x) := by
  intro i hi; simp [Nat.not_le.mpr hi]

theorem vanishes_shift (n : ℕ) {x : Series g} (hx : Vanishes n x) :
    x = shift k g n (fun i => x (i+n)) := by
  ext i
  by_cases h : n ≤ i
  · simp [h]
  · simp [h, hx i (Nat.lt_of_not_ge h)]

theorem head_tail (x : Series g) :
    x = constant k g (x 0) + shift k g 1 (fun i => x (i+1)) := by
  ext i
  cases i <;> simp

theorem formal_shift {f : Series g →ₗ[k] Series g} (hf : IsFormal f)
    (n : ℕ) (x : Series g) : f (shift k g n x) = shift k g n (f x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n+1=1+n by omega, shift_add, hf, ih, ← shift_add]

theorem formal_preserves {f : Series g →ₗ[k] Series g} (hf : IsFormal f)
    {n : ℕ} {x : Series g} (hx : Vanishes n x) : Vanishes n (f x) := by
  rw [vanishes_shift (k := k) n hx, formal_shift hf]
  exact shift_vanishes _ _

theorem formal_agrees {f : Series g →ₗ[k] Series g} (hf : IsFormal f)
    {n : ℕ} {x y : Series g} (h : Agrees n x y) : Agrees n (f x) (f y) := by
  have hz : Vanishes n (x-y) := fun i hi => sub_eq_zero.mpr (h i hi)
  have := formal_preserves hf hz
  intro i hi
  simpa only [map_sub, Pi.sub_apply, sub_eq_zero] using this i hi

theorem formal_id : IsFormal (LinearMap.id : Series g →ₗ[k] Series g) := fun _ => rfl

theorem formal_add {f h : Series g →ₗ[k] Series g} (hf : IsFormal f) (hh : IsFormal h) :
    IsFormal (f+h) := by
  intro x; simp only [LinearMap.add_apply, hf x, hh x, map_add]

theorem formal_sub {f h : Series g →ₗ[k] Series g} (hf : IsFormal f) (hh : IsFormal h) :
    IsFormal (f-h) := by
  intro x; simp only [LinearMap.sub_apply, hf x, hh x, map_sub]

theorem formal_comp {f h : Series g →ₗ[k] Series g} (hf : IsFormal f) (hh : IsFormal h) :
    IsFormal (f.comp h) := by
  intro x; simp only [LinearMap.comp_apply, hh x, hf (h x)]

theorem formal_shiftMap (n : ℕ) : IsFormal (shift k g n) := by
  intro x
  rw [← shift_add, ← shift_add, Nat.add_comm]

theorem formal_lift (a : g →ₗ[k] g) : IsFormal (lift k g a) := by
  intro x; ext i
  cases i <;> simp [lift]

/-- A formal linear map with a prescribed constant coefficient has the same
leading action on every t^n-divisible vector. -/
theorem formal_leading {f : Series g →ₗ[k] Series g} (hf : IsFormal f)
    (hzero : ∀ x, f x 0 = x 0) {n : ℕ} {x : Series g} (hx : Vanishes n x) :
    f x n = x n := by
  conv_lhs => rw [vanishes_shift (k := k) n hx, formal_shift hf]
  simp [hzero]

/-- Modulo t^(n+1), a bilinear formal map whose values are divisible by t^n
only sees the constant coefficients of its arguments. -/
theorem bilinear_leading
    (b : Series g →ₗ[k] Series g →ₗ[k] Series g)
    (hl : ∀ x y, b (shift k g 1 x) y = shift k g 1 (b x y))
    (hr : ∀ x y, b x (shift k g 1 y) = shift k g 1 (b x y))
    {n : ℕ} (hv : ∀ x y, Vanishes n (b x y)) (x y : Series g) :
    b x y n = b (constant k g (x 0)) (constant k g (y 0)) n := by
  have h1 : ∀ x y, b (shift k g 1 x) y n = 0 := by
    intro x y; rw [hl]
    cases n with
    | zero => simp
    | succ n => simpa using hv x y n (by omega)
  have h2 : ∀ x y, b x (shift k g 1 y) n = 0 := by
    intro x y; rw [hr]
    cases n with
    | zero => simp
    | succ n => simpa using hv x y n (by omega)
  conv_lhs => rw [head_tail (k := k) x, head_tail (k := k) y]
  simp only [map_add, LinearMap.add_apply, Pi.add_apply, h1, h2, add_zero]

/-- Shift-linearity already gives full formal scalar linearity. -/
theorem formal_scalar {f : Series g →ₗ[k] Series g} (hf : IsFormal f)
    (a : PowerSeries k) (x : Series g) : f (scalar a x) = scalar a (f x) := by
  have hpref : ∀ (x : Series g) (n : ℕ),
      Agrees (n+1) (scalar a x)
        (∑ i ∈ Finset.range (n+1), PowerSeries.coeff i a • shift k g i x) := by
    intro x n j hj
    simp only [Finset.sum_apply, Pi.smul_apply, shift_apply, scalar]
    symm
    calc
      _ = ∑ i ∈ Finset.range (j+1), PowerSeries.coeff i a •
          (if i ≤ j then x (j-i) else 0) := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega : j+1 ≤ n+1))
        intro i hi hin
        have hij : j < i := by simp only [Finset.mem_range] at hin; omega
        simp [Nat.not_le.mpr hij]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [show i ≤ j by simpa using hi]
  ext n
  have h := formal_agrees hf (hpref x n) n (by omega)
  rw [map_sum] at h
  simp only [map_smul, formal_shift hf] at h
  exact h.trans ((hpref (f x) n n (by omega)).symm)

/-- Linearity for the full scalar action is equivalent to commuting with the shift. -/
theorem formal_iff_scalar (f : Series g →ₗ[k] Series g) :
    IsFormal f ↔ ∀ (a : PowerSeries k) (x : Series g),
      f (scalar a x) = scalar a (f x) := by
  refine ⟨formal_scalar, fun h x => ?_⟩
  have hx := h ((PowerSeries.X : PowerSeries k) ^ 1) x
  rw [scalar_parameter_pow (k := k) 1 x, scalar_parameter_pow (k := k) 1 (f x)] at hx
  exact hx

theorem scalarLinearity_spec :
    Specs.LieAlgebrasAndRepresentations.FormalRigidity.scalarLinearityExpected.{u,v} := by
  intro k g _ _ _ B r x y
  constructor
  · let f : Series g →ₗ[k] Series g :=
      { toFun := fun z => B.bracket z y
        map_add' := fun _ _ => by simp
        map_smul' := fun _ _ => by simp }
    exact (formal_iff_scalar f).mp (fun z => B.shift_left z y) r x
  · exact (formal_iff_scalar (B.bracket x)).mp (B.shift_right x) r y

@[simp] theorem standard_apply (x y : Series g) (n : ℕ) :
    standard k g x y n = ∑ i ∈ Finset.range (n+1), ⁅x i,y (n-i)⁆ := rfl

@[simp] theorem standard_zero (x y : Series g) : standard k g x y 0 = ⁅x 0,y 0⁆ := by
  simp

@[simp] theorem standard_constants (x y : g) :
    standard k g (constant k g x) (constant k g y) = constant k g ⁅x,y⁆ := by
  ext n
  rw [standard_apply, Finset.sum_eq_single 0]
  · cases n <;> simp
  · intro i hi hi0
    simp [constant, hi0]
  · simp

theorem standard_shift_right (x y : Series g) :
    standard k g x (shift k g 1 y) = shift k g 1 (standard k g x y) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp only [standard_apply, shift_one_succ]
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, shift_one_zero, lie_zero, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    have h : n+1-i = (n-i)+1 := by simp only [Finset.mem_range] at hi; omega
    simp [h]

theorem standard_shift_left (x y : Series g) :
    standard k g (shift k g 1 x) y = shift k g 1 (standard k g x y) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp only [standard_apply, shift_one_succ]
    rw [Finset.sum_range_succ']
    simp only [shift_one_zero, zero_lie, add_zero, shift_one_succ]
    apply Finset.sum_congr rfl
    intro i hi
    simp

/-- Finite dependence of a formal bilinear operation. -/
theorem bilinear_agrees
    (b : Series g →ₗ[k] Series g →ₗ[k] Series g)
    (hl : ∀ x y, b (shift k g 1 x) y = shift k g 1 (b x y))
    (hr : ∀ x y, b x (shift k g 1 y) = shift k g 1 (b x y))
    {n : ℕ} {x x' y y' : Series g}
    (hx : Agrees n x x') (hy : Agrees n y y') : Agrees n (b x y) (b x' y') := by
  let f : Series g →ₗ[k] Series g :=
    { toFun := fun z => b z y
      map_add' := fun _ _ => by simp
      map_smul' := fun _ _ => by simp }
  have h1 := formal_agrees (f := f) (fun z => hl z y) hx
  have h2 := formal_agrees (f := b x') (hr x') hy
  exact fun i hi => (h1 i hi).trans (h2 i hi)

/-- When the second argument starts in degree n, only reduction of the
bracket and its nth input coefficient contribute in degree n. -/
theorem bracket_leading_right (B : Deformation k g) (x : Series g)
    {n : ℕ} {y : Series g} (hy : Vanishes n y) :
    B.bracket x y n = ⁅x 0,y n⁆ := by
  conv_lhs => rw [vanishes_shift (k := k) n hy, formal_shift (B.shift_right x)]
  simp [B.reduction]

theorem bracket_leading_left (B : Deformation k g) (y : Series g)
    {n : ℕ} {x : Series g} (hx : Vanishes n x) :
    B.bracket x y n = ⁅x n,y 0⁆ := by
  let f : Series g →ₗ[k] Series g :=
    { toFun := fun z => B.bracket z y
      map_add' := fun _ _ => by simp
      map_smul' := fun _ _ => by simp }
  have hf : IsFormal f := fun z => B.shift_left z y
  change f x n = _
  conv_lhs => rw [vanishes_shift (k := k) n hx, formal_shift hf]
  simp [f, B.reduction]

/-- The residual equation for a partial coordinate change. -/
def defect (B : Deformation k g) (T : Series g →ₗ[k] Series g) :
    Series g →ₗ[k] Series g →ₗ[k] Series g :=
  (B.bracket.compl₁₂ T T) - (standard k g).compr₂ T

@[simp] theorem defect_apply (B : Deformation k g) (T : Series g →ₗ[k] Series g)
    (x y : Series g) :
    defect B T x y = B.bracket (T x) (T y) - T (standard k g x y) := rfl

theorem defect_shift_left (B : Deformation k g) {T : Series g →ₗ[k] Series g}
    (hT : IsFormal T) (x y : Series g) :
    defect B T (shift k g 1 x) y = shift k g 1 (defect B T x y) := by
  simp only [defect_apply, formal_shift hT, B.shift_left, standard_shift_left, map_sub]

theorem defect_shift_right (B : Deformation k g) {T : Series g →ₗ[k] Series g}
    (hT : IsFormal T) (x y : Series g) :
    defect B T x (shift k g 1 y) = shift k g 1 (defect B T x y) := by
  simp only [defect_apply, formal_shift hT, B.shift_right, standard_shift_right, map_sub]

/-- The next residual coefficient is an alternating k-bilinear map. -/
def defectCoefficient (B : Deformation k g) (T : Series g →ₗ[k] Series g)
    (n : ℕ) : twoCochain k g g :=
  ⟨((defect B T).compl₁₂ (constant k g) (constant k g)).compr₂
    { toFun := fun x => x n
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }, by
    intro x
    simp [B.alternating]⟩

@[simp] theorem defectCoefficient_apply (B : Deformation k g)
    (T : Series g →ₗ[k] Series g) (n : ℕ) (x y : g) :
    defectCoefficient B T n x y = defect B T (constant k g x) (constant k g y) n := rfl

/-- Jacobi turns the leading residual coefficient into a genuine CE cocycle. -/
theorem defectCoefficient_cocycle (B : Deformation k g)
    {T : Series g →ₗ[k] Series g} (_hT : IsFormal T)
    (hzero : ∀ x, T x 0 = x 0) {n : ℕ}
    (hv : ∀ x y, Vanishes n (defect B T x y)) :
    d₂₃ k g g (defectCoefficient B T n) = 0 := by
  let c := defectCoefficient B T n
  have expansion : ∀ x y z : g,
      B.bracket (T (constant k g x))
        (B.bracket (T (constant k g y)) (T (constant k g z))) n =
      ⁅x,c y z⁆ + c x ⁅y,z⁆ + T (constant k g ⁅x,⁅y,z⁆⁆) n := by
    intro x y z
    have hd : B.bracket (T (constant k g y)) (T (constant k g z)) =
        defect B T (constant k g y) (constant k g z) + T (constant k g ⁅y,z⁆) := by
      simp
    rw [hd, map_add, Pi.add_apply,
      bracket_leading_right B _ (hv _ _), hzero, constant_zero]
    change ⁅x,c y z⁆ + _ = _
    have hx := congrFun (defect_apply B T (constant k g x) (constant k g ⁅y,z⁆)) n
    simp only [standard_constants, Pi.sub_apply] at hx
    change c x ⁅y,z⁆ = _ at hx
    rw [hx]
    abel
  have hj : ∀ x y z : g,
      (⁅x,c y z⁆ + c x ⁅y,z⁆) + (⁅y,c z x⁆ + c y ⁅z,x⁆) +
        (⁅z,c x y⁆ + c z ⁅x,y⁆) = 0 := by
    intro x y z
    have h := congrFun (B.jacobi (T (constant k g x)) (T (constant k g y))
      (T (constant k g z))) n
    simp only [Pi.add_apply, Pi.zero_apply, expansion] at h
    have hz : T (constant k g ⁅x,⁅y,z⁆⁆) n + T (constant k g ⁅y,⁅z,x⁆⁆) n +
        T (constant k g ⁅z,⁅x,y⁆⁆) n = 0 := by
      have hh := congrFun (congrArg (fun w => T (constant k g w)) (lie_jacobi x y z)) n
      simpa only [map_add, map_zero, Pi.add_apply, Pi.zero_apply] using hh
    have : (⁅x,c y z⁆ + c x ⁅y,z⁆) + (⁅y,c z x⁆ + c y ⁅z,x⁆) +
        (⁅z,c x y⁆ + c z ⁅x,y⁆) =
        ((⁅x,c y z⁆ + c x ⁅y,z⁆ + T (constant k g ⁅x,⁅y,z⁆⁆) n) +
        (⁅y,c z x⁆ + c y ⁅z,x⁆ + T (constant k g ⁅y,⁅z,x⁆⁆) n) +
        (⁅z,c x y⁆ + c z ⁅x,y⁆ + T (constant k g ⁅z,⁅x,y⁆⁆) n)) -
        (T (constant k g ⁅x,⁅y,z⁆⁆) n + T (constant k g ⁅y,⁅z,x⁆⁆) n +
        T (constant k g ⁅z,⁅x,y⁆⁆) n) := by abel
    rw [this, h, hz, sub_self]
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply LinearMap.ext
  intro z
  have h := hj x y z
  simp only [d₂₃_apply, LinearMap.zero_apply]
  rw [← twoCochain_skew c x z, ← lie_skew z x, map_neg] at h
  rw [← twoCochain_skew c ⁅y,z⁆ x, ← twoCochain_skew c ⁅x,z⁆ y,
    ← twoCochain_skew c ⁅x,y⁆ z] at h
  simp only [lie_neg, neg_neg] at h
  change ⁅x,c y z⁆ - ⁅y,c x z⁆ + ⁅z,c x y⁆ - c ⁅x,y⁆ z +
    c ⁅x,z⁆ y - c ⁅y,z⁆ x = 0
  convert h using 1; abel

/-- One elementary factor in the successive t-adic composition. -/
def correction (T : Series g →ₗ[k] Series g) (n : ℕ) (a : g →ₗ[k] g) :
    Series g →ₗ[k] Series g :=
  T.comp (LinearMap.id + (shift k g n).comp (lift k g a))

theorem correction_formal {T : Series g →ₗ[k] Series g} (hT : IsFormal T)
    (n : ℕ) (a : g →ₗ[k] g) : IsFormal (correction T n a) :=
  formal_comp hT (formal_add formal_id (formal_comp (formal_shiftMap n) (formal_lift a)))

theorem correction_add {T : Series g →ₗ[k] Series g} (hT : IsFormal T)
    (n : ℕ) (a : g →ₗ[k] g) (x : Series g) :
    correction T n a x = T x + shift k g n (T (lift k g a x)) := by
  simp only [correction, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.id_apply, map_add, formal_shift hT]

theorem correction_agrees {T : Series g →ₗ[k] Series g} (hT : IsFormal T)
    (n : ℕ) (a : g →ₗ[k] g) (x : Series g) :
    Agrees n (correction T n a x) (T x) := by
  intro i hi
  simp [correction_add hT, shift_vanishes (k := k) n _ i hi]

theorem correction_zero {T : Series g →ₗ[k] Series g} (hT : IsFormal T)
    (hzero : ∀ x, T x 0 = x 0) {n : ℕ} (hn : 0 < n) (a : g →ₗ[k] g)
    (x : Series g) : correction T n a x 0 = x 0 :=
  (correction_agrees hT n a x 0 hn).trans (hzero x)

theorem correction_defect_agrees (B : Deformation k g)
    {T : Series g →ₗ[k] Series g} (hT : IsFormal T)
    (n : ℕ) (a : g →ₗ[k] g) (x y : Series g) :
    Agrees n (defect B (correction T n a) x y) (defect B T x y) := by
  have hb := bilinear_agrees B.bracket B.shift_left B.shift_right
    (correction_agrees hT n a x) (correction_agrees hT n a y)
  have ht := correction_agrees hT n a (standard k g x y)
  intro i hi
  simp only [defect_apply, Pi.sub_apply]
  rw [hb i hi, ht i hi]

/-- The leading residual changes by exactly the adjoint CE coboundary. -/
theorem correction_defect_coefficient (B : Deformation k g)
    {T : Series g →ₗ[k] Series g} (hT : IsFormal T)
    (hzero : ∀ x, T x 0 = x 0) {n : ℕ} (hn : 0 < n)
    (a : g →ₗ[k] g) (x y : Series g) :
    defect B (correction T n a) x y n =
      defect B T x y n + d₁₂ k g g a (x 0) (y 0) := by
  have leadR : ∀ x y : Series g,
      B.bracket x (shift k g n (T (lift k g a y))) n = ⁅x 0,a (y 0)⁆ := by
    intro x y
    rw [bracket_leading_right B _ (shift_vanishes n _)]
    simp [hzero, lift]
  have leadL : ∀ x y : Series g,
      B.bracket (shift k g n (T (lift k g a x))) y n = ⁅a (x 0),y 0⁆ := by
    intro x y
    rw [bracket_leading_left B _ (shift_vanishes n _)]
    simp [hzero, lift]
  simp only [defect_apply, correction_add hT, map_add, LinearMap.add_apply,
    Pi.add_apply, Pi.sub_apply]
  rw [leadL, leadR, leadR]
  simp only [hzero, shift_at, shift_apply, show ¬ n ≤ 0 by omega, ↓reduceIte,
    zero_lie, add_zero, standard_zero, lift, LinearMap.coe_mk, AddHom.coe_mk,
    d₁₂_apply_apply]
  rw [← lie_skew (a (x 0)) (y 0)]
  abel

/-- H²=0 supplies an actual linear primitive of each cocycle. -/
theorem exists_killing_cochain
    (hH : Subsingleton (LowH2 (k := k) (g := g) (M := g)))
    (c : twoCocycle k g g) : ∃ a : g →ₗ[k] g, c.1 + d₁₂ k g g a = 0 := by
  let := hH
  obtain ⟨b,hb⟩ := (lowClass_eq_iff c 0).mp (Subsingleton.elim _ _)
  refine ⟨-b, ?_⟩
  have h := congrArg Subtype.val hb
  change c.1 = 0 + d₁₂ k g g b at h
  simp only [zero_add] at h
  rw [h, map_neg, add_neg_cancel]

/-- A partial composition solving the equivalence equation through degree n. -/
structure Approximation (B : Deformation k g) (n : ℕ) where
  map : Series g →ₗ[k] Series g
  formal : IsFormal map
  reduction : ∀ x, map x 0 = x 0
  vanishes : ∀ x y, Vanishes (n+1) (defect B map x y)

namespace Approximation
variable {B : Deformation k g} {n : ℕ}

def initial (B : Deformation k g) : Approximation B 0 where
  map := LinearMap.id
  formal := formal_id
  reduction := fun _ => rfl
  vanishes := by
    intro x y i hi
    have : i = 0 := by omega
    subst i
    simp [B.reduction]

def leading (A : Approximation B n) : twoCocycle k g g :=
  ⟨defectCoefficient B A.map (n+1),
    defectCoefficient_cocycle B A.formal A.reduction A.vanishes⟩

def coefficient
    (hH : Subsingleton (LowH2 (k := k) (g := g) (M := g)))
    (A : Approximation B n) : g →ₗ[k] g :=
  Classical.choose (exists_killing_cochain hH A.leading)

theorem coefficient_spec
    (hH : Subsingleton (LowH2 (k := k) (g := g) (M := g)))
    (A : Approximation B n) :
    defectCoefficient B A.map (n+1) + d₁₂ k g g (A.coefficient hH) = 0 :=
  Classical.choose_spec (exists_killing_cochain hH A.leading)

def advance
    (hH : Subsingleton (LowH2 (k := k) (g := g) (M := g)))
    (A : Approximation B n) : Approximation B (n+1) where
  map := correction A.map (n+1) (A.coefficient hH)
  formal := correction_formal A.formal _ _
  reduction := correction_zero A.formal A.reduction (by omega) _
  vanishes := by
    intro x y i hi
    by_cases hlow : i < n+1
    · rw [correction_defect_agrees B A.formal (n+1) (A.coefficient hH) x y i hlow]
      exact A.vanishes x y i hlow
    · have heq : i = n+1 := by omega
      subst i
      rw [correction_defect_coefficient B A.formal A.reduction (by omega),
        bilinear_leading (defect B A.map) (defect_shift_left B A.formal)
          (defect_shift_right B A.formal) A.vanishes]
      have h := congrArg (fun c : twoCochain k g g => c (x 0) (y 0))
        (A.coefficient_spec hH)
      exact h

end Approximation

/-- The successive partial products; the next factor begins in degree n+1. -/
def approximations (B : Deformation k g)
    (hH : Subsingleton (LowH2 (k := k) (g := g) (M := g))) :
    (n : ℕ) → Approximation B n
  | 0 => Approximation.initial B
  | n+1 => (approximations B hH n).advance hH

theorem approximations_step (B : Deformation k g)
    (hH : Subsingleton (LowH2 (k := k) (g := g) (M := g))) (n : ℕ) :
    (approximations B hH (n+1)).map =
      correction (approximations B hH n).map (n+1)
        ((approximations B hH n).coefficient hH) := rfl

theorem approximations_stable (B : Deformation k g)
    (hH : Subsingleton (LowH2 (k := k) (g := g) (M := g)))
    {n m : ℕ} (hm : n ≤ m) (x : Series g) :
    Agrees (n+1) ((approximations B hH m).map x) ((approximations B hH n).map x) := by
  induction m, hm using Nat.le_induction with
  | base => exact fun _ _ => rfl
  | succ m hm ih =>
    intro i hi
    rw [approximations_step]
    exact (correction_agrees (approximations B hH m).formal (m+1) _ x i (by omega)).trans
      (ih i hi)

/-- The coefficientwise limit of the actual partial compositions. -/
def limitMap (B : Deformation k g)
    (hH : Subsingleton (LowH2 (k := k) (g := g) (M := g))) :
    Series g →ₗ[k] Series g where
  toFun x n := (approximations B hH n).map x n
  map_add' x y := by funext n; simp
  map_smul' a x := by funext n; simp

theorem limitMap_stable (B : Deformation k g)
    (hH : Subsingleton (LowH2 (k := k) (g := g) (M := g)))
    (n : ℕ) (x : Series g) :
    Agrees (n+1) (limitMap B hH x) ((approximations B hH n).map x) := by
  intro i hi
  exact (approximations_stable B hH (by omega : i ≤ n) x i (by omega)).symm

theorem limitMap_formal (B : Deformation k g)
    (hH : Subsingleton (LowH2 (k := k) (g := g) (M := g))) : IsFormal (limitMap B hH) := by
  intro x
  ext n
  cases n with
  | zero => simp [limitMap, (approximations B hH 0).reduction]
  | succ n =>
    change (approximations B hH (n+1)).map (shift k g 1 x) (n+1) = _
    rw [(approximations B hH (n+1)).formal x, shift_one_succ, shift_one_succ]
    exact approximations_stable B hH (by omega : n ≤ n+1) x n (by omega)

theorem limitMap_zero (B : Deformation k g)
    (hH : Subsingleton (LowH2 (k := k) (g := g) (M := g)))
    (x : Series g) : limitMap B hH x 0 = x 0 := rfl

theorem limitMap_intertwines (B : Deformation k g)
    (hH : Subsingleton (LowH2 (k := k) (g := g) (M := g))) (x y : Series g) :
    B.bracket (limitMap B hH x) (limitMap B hH y) = limitMap B hH (standard k g x y) := by
  ext n
  have hb := bilinear_agrees B.bracket B.shift_left B.shift_right
    (limitMap_stable B hH n x) (limitMap_stable B hH n y)
  rw [hb n (by omega), limitMap_stable B hH n (standard k g x y) n (by omega)]
  exact sub_eq_zero.mp ((approximations B hH n).vanishes x y n (by omega))

/-- A finite prefix, used only to solve the inverse recursively. -/
def truncate (n : ℕ) (x : Series g) : Series g := fun i => if i < n then x i else 0

theorem truncate_remainder (n : ℕ) (x : Series g) :
    x = truncate n x + shift k g n (fun i => x (i+n)) := by
  ext i
  by_cases h : i < n
  · simp [truncate, h, Nat.not_le.mpr h]
  · simp [truncate, h, Nat.le_of_not_gt h]

theorem formal_coefficient {T : Series g →ₗ[k] Series g} (hT : IsFormal T)
    (hzero : ∀ x, T x 0 = x 0) (x : Series g) (n : ℕ) :
    T x n = T (truncate n x) n + x n := by
  have h := congrFun (congrArg T (truncate_remainder (k := k) n x)) n
  simpa only [map_add, formal_shift hT, Pi.add_apply, shift_at, hzero,
    Nat.zero_add] using h

/-- Formal recursion for the inverse, using only already determined coefficients. -/
def inverseCoefficients (T : Series g →ₗ[k] Series g) (y : Series g) (n : ℕ) : g :=
  y n - T (fun i => if _h : i < n then inverseCoefficients T y i else 0) n
termination_by n

theorem inverseCoefficients_eq (T : Series g →ₗ[k] Series g) (y : Series g) (n : ℕ) :
    inverseCoefficients T y n = y n - T (truncate n (inverseCoefficients T y)) n := by
  rw [inverseCoefficients]
  rfl

/-- An identity constant coefficient implies invertibility on the full complete
module, even in infinite rank. This also applies to every elementary factor. -/
theorem formal_bijective {T : Series g →ₗ[k] Series g} (hT : IsFormal T)
    (hzero : ∀ x, T x 0 = x 0) : Function.Bijective T := by
  constructor
  · intro x y h
    funext n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have ht : truncate n x = truncate n y := by
        funext i
        simp only [truncate]
        split_ifs with hi
        · exact ih i hi
        · rfl
      have hn := congrFun h n
      rw [formal_coefficient hT hzero x n, formal_coefficient hT hzero y n, ht] at hn
      exact add_left_cancel hn
  · intro y
    refine ⟨inverseCoefficients T y, ?_⟩
    funext n
    rw [formal_coefficient hT hzero, inverseCoefficients_eq]
    abel

/-- Assemble the convergent product into an invertible formal coordinate change. -/
theorem trivialization_of_lowH2
    (hH : Subsingleton (LowH2 (k := k) (g := g) (M := g)))
    (B : Deformation k g) : Trivialization B := by
  let T := limitMap B hH
  let e : Series g ≃ₗ[k] Series g := LinearEquiv.ofBijective T
    (formal_bijective (limitMap_formal B hH) (limitMap_zero B hH))
  refine ⟨e, (fun n => (approximations B hH n).coefficient hH),
    (fun n => (approximations B hH n).map), ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · exact formal_scalar (limitMap_formal B hH)
  · exact limitMap_zero B hH
  · exact limitMap_intertwines B hH
  · intro n; rfl
  · intro n x i hi
    exact (limitMap_stable B hH n x i (by omega)).symm
  · intro n x y i hi
    exact sub_eq_zero.mp ((approximations B hH n).vanishes x y i (by omega))

/-- LA-I03: vanishing of the ordinary adjoint CE H² implies formal rigidity. -/
theorem rigidity_spec :
    Specs.LieAlgebrasAndRepresentations.FormalRigidity.rigidityExpected.{u,v} := by
  intro k g _ _ _ _ δ hs hδ hH B
  obtain ⟨e, _, _, _⟩ := ceComparison_spec δ hs hδ
  have hLow : Subsingleton (LowH2 (k := k) (g := g) (M := g)) :=
    ⟨fun x y => e.injective (hH.elim (e x) (e y))⟩
  exact trivialization_of_lowH2 hLow B

end LieAlgebrasAndRepresentations.FormalRigidity
