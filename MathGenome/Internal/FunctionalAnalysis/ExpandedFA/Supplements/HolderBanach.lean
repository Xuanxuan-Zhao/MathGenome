import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.HolderBanach
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Supplements.HolderCompleteness
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set
open scoped NNReal
namespace ExpandedFA.Supplements
open HolderSpacesSpec
universe u v

/-- The completeness part of the proposition uses the accepted upstream results. -/
theorem holder_banach_completeness : HolderBanachSpec.Completeness.{u, v} :=
  ⟨cm_complete, cm_holder_complete, bounded_holder_complete⟩

namespace HolderAlgebra
variable {X 𝕜 : Type*} [MetricSpace X] [RCLike 𝕜] {α : HolderExponent}

/-- The elementary product estimate uses boundedness of both factors. -/
lemma holderWith_mul (f g : BoundedContinuousFunction X 𝕜)
    (hf : MemHolder α.val (f : X → 𝕜)) (hg : MemHolder α.val (g : X → 𝕜)) :
    HolderWith (‖f‖₊ * nnHolderNorm α.val g + ‖g‖₊ * nnHolderNorm α.val f)
      α.val (fun x => f x * g x) := by
  apply (holderWith_iff_dist _ _ _).mpr
  intro x y
  have he : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
  rw [he]
  calc
    _ ≤ ‖f x * (g x - g y)‖ + ‖g y * (f x - f y)‖ := norm_add_le _ _
    _ = ‖f x‖ * ‖g x - g y‖ + ‖g y‖ * ‖f x - f y‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖f‖ * ((nnHolderNorm α.val g : ℝ) * dist x y ^ (α.val : ℝ)) +
        ‖g‖ * ((nnHolderNorm α.val f : ℝ) * dist x y ^ (α.val : ℝ)) := by
      exact add_le_add
        (mul_le_mul (f.norm_coe_le_norm x)
          (by simpa only [dist_eq_norm] using hg.holderWith.dist_le x y)
          (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (g.norm_coe_le_norm y)
          (by simpa only [dist_eq_norm] using hf.holderWith.dist_le x y)
          (norm_nonneg _) (norm_nonneg _))
    _ = _ := by push_cast; ring

/-- Pointwise multiplication stays in the canonical bounded Hölder space. -/
def boundedMul (f g : BoundedHolder X 𝕜 α) : BoundedHolder X 𝕜 α :=
  ⟨f.val * g.val, (holderWith_mul f.val g.val f.property g.property).memHolder⟩

@[simp] lemma boundedMul_apply (f g : BoundedHolder X 𝕜 α) (x : X) :
    boundedMul f g x = f x * g x := rfl

lemma boundedMul_norm (f g : BoundedHolder X 𝕜 α) :
    ‖boundedMul f g‖ ≤ ‖f‖ * ‖g‖ := by
  have hs : holderSeminorm α (fun x => f x * g x) ≤
      ‖f.val‖ * holderSeminorm α g + ‖g.val‖ * holderSeminorm α f := by
    exact_mod_cast (holderWith_mul f.val g.val f.property g.property).nnholderNorm_le
  change ‖f.val * g.val‖ + holderSeminorm α (fun x => f x * g x) ≤ _
  rw [HolderDomain.norm_eq, HolderDomain.norm_eq]
  have hn := norm_mul_le f.val g.val
  have hpos : 0 ≤ holderSeminorm α f * holderSeminorm α g :=
    mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  dsimp only [boundedFunctionLinearMap, LinearMap.coe_mk, AddHom.coe_mk] at *
  nlinarith

/-- The bilinear product before its norm estimate is used to bundle continuity. -/
def boundedMulLinear : BoundedHolder X 𝕜 α →ₗ[𝕜]
    BoundedHolder X 𝕜 α →ₗ[𝕜] BoundedHolder X 𝕜 α where
  toFun f :=
    { toFun := boundedMul f
      map_add' := by
        intro g h
        apply Subtype.ext
        ext x
        exact mul_add (f x) (g x) (h x)
      map_smul' := by
        intro c g
        apply Subtype.ext
        ext x
        change f x * (c * g x) = c * (f x * g x)
        ring }
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro h
    apply Subtype.ext
    apply BoundedContinuousFunction.ext
    intro x
    exact add_mul (f x) (g x) (h x)
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro g
    apply Subtype.ext
    apply BoundedContinuousFunction.ext
    intro x
    change (c * f x) * g x = c * (f x * g x)
    ring

/-- Continuous bilinear multiplication, with bound one for the sum norm. -/
def boundedMulContinuous : BoundedHolder X 𝕜 α →L[𝕜]
    BoundedHolder X 𝕜 α →L[𝕜] BoundedHolder X 𝕜 α :=
  boundedMulLinear.mkContinuous₂ 1 (by
    intro f g
    change ‖boundedMul f g‖ ≤ 1 * ‖f‖ * ‖g‖
    simpa only [one_mul] using boundedMul_norm f g)

end HolderAlgebra

/-- Multiplication on arbitrary bounded metric-space Hölder spaces is continuous. -/
theorem bounded_holder_multiplication : HolderBanachSpec.BoundedHolderMultiplication := by
  intro X 𝕜 _ _ α
  exact ⟨HolderAlgebra.boundedMulContinuous, fun _ _ _ => rfl⟩

namespace DifferentiableAlgebra
variable {𝕜 : Type*} [RCLike 𝕜] {m : ℕ} {a b : ℝ} {hab : a < b}

lemma intervalExtend_mul (f g : C(Interval a b, 𝕜)) :
    intervalExtend (f * g) = intervalExtend f * intervalExtend g := by
  funext x
  by_cases hx : x ∈ Icc a b <;> simp [intervalExtend, hx]

/-- The canonical interval product, with endpoint derivatives taken within Icc. -/
def cmMul (f g : HolderSpacesSpec.Cm 𝕜 m hab) : HolderSpacesSpec.Cm 𝕜 m hab :=
  ⟨f.val * g.val, by
    change ContDiffOn ℝ m (intervalExtend (f.val * g.val)) (Icc a b)
    rw [intervalExtend_mul]
    exact f.property.mul g.property⟩

@[simp] lemma cmMul_apply (f g : HolderSpacesSpec.Cm 𝕜 m hab) (x : Interval a b) :
    cmMul f g x = f x * g x := rfl

lemma derivative_norm_le (f : HolderSpacesSpec.Cm 𝕜 m hab) (j : Fin (m + 1)) :
    ‖HolderSpacesSpec.Cm.derivative f j‖ ≤ ‖f‖ := by
  rw [HolderSpacesSpec.Cm.norm_eq]
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

lemma iteratedDerivWithin_norm_le (f : HolderSpacesSpec.Cm 𝕜 m hab)
    {j : ℕ} (hj : j ≤ m) (x : Interval a b) :
    ‖iteratedDerivWithin j (intervalExtend f.val) (Icc a b) x‖ ≤ ‖f‖ :=
  (ContinuousMap.norm_coe_le_norm (HolderSpacesSpec.Cm.derivative f
    ⟨j, Nat.lt_succ_of_le hj⟩) x).trans (derivative_norm_le f _)

/-- Leibniz's formula bounds each coordinate by a finite constant times both norms. -/
lemma cmMul_derivative_bound (f g : HolderSpacesSpec.Cm 𝕜 m hab) (j : Fin (m + 1)) :
    ‖HolderSpacesSpec.Cm.derivative (cmMul f g) j‖ ≤
      (∑ i ∈ Finset.range (j.val + 1), (j.val.choose i : ℝ)) * ‖f‖ * ‖g‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  change ‖iteratedDerivWithin j.val (intervalExtend (f.val * g.val)) (Icc a b) x‖ ≤ _
  rw [intervalExtend_mul, iteratedDerivWithin_mul x.property (uniqueDiffOn_Icc hab)
    ((f.property.of_le (by exact_mod_cast Nat.le_of_lt_succ j.isLt)) x x.property)
    ((g.property.of_le (by exact_mod_cast Nat.le_of_lt_succ j.isLt)) x x.property)]
  calc
    _ ≤ ∑ i ∈ Finset.range (j.val + 1),
        ‖(j.val.choose i : 𝕜) * iteratedDerivWithin i (intervalExtend f.val) (Icc a b) x *
          iteratedDerivWithin (j.val - i) (intervalExtend g.val) (Icc a b) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (j.val + 1), (j.val.choose i : ℝ) * ‖f‖ * ‖g‖ := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ j.val := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [norm_mul, norm_mul, RCLike.norm_natCast]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (iteratedDerivWithin_norm_le f (hi'.trans (Nat.le_of_lt_succ j.isLt)) x)
          (Nat.cast_nonneg _))
        (iteratedDerivWithin_norm_le g
          ((Nat.sub_le _ _).trans (Nat.le_of_lt_succ j.isLt)) x)
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

/-- A deliberately unsimplified finite Leibniz constant suffices for continuity. -/
def productBound (m : ℕ) : ℝ :=
  ∑ j : Fin (m + 1), ∑ i ∈ Finset.range (j.val + 1), (j.val.choose i : ℝ)

lemma cmMul_norm (f g : HolderSpacesSpec.Cm 𝕜 m hab) :
    ‖cmMul f g‖ ≤ productBound m * ‖f‖ * ‖g‖ := by
  rw [HolderSpacesSpec.Cm.norm_eq]
  calc
    _ ≤ ∑ j : Fin (m + 1),
        (∑ i ∈ Finset.range (j.val + 1), (j.val.choose i : ℝ)) * ‖f‖ * ‖g‖ :=
      Finset.sum_le_sum (fun j _ => cmMul_derivative_bound f g j)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; rfl

def cmMulLinear : HolderSpacesSpec.Cm 𝕜 m hab →ₗ[𝕜]
    HolderSpacesSpec.Cm 𝕜 m hab →ₗ[𝕜] HolderSpacesSpec.Cm 𝕜 m hab where
  toFun f :=
    { toFun := cmMul f
      map_add' := by
        intro g h
        apply Subtype.ext
        ext x
        exact mul_add (f x) (g x) (h x)
      map_smul' := by
        intro c g
        apply Subtype.ext
        ext x
        change f x * (c * g x) = c * (f x * g x)
        ring }
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro h
    apply Subtype.ext
    ext x
    exact add_mul (f x) (g x) (h x)
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro g
    apply Subtype.ext
    ext x
    change (c * f x) * g x = c * (f x * g x)
    ring

def cmMulContinuous : HolderSpacesSpec.Cm 𝕜 m hab →L[𝕜]
    HolderSpacesSpec.Cm 𝕜 m hab →L[𝕜] HolderSpacesSpec.Cm 𝕜 m hab :=
  cmMulLinear.mkContinuous₂ (productBound m) (by
    intro f g
    change ‖cmMul f g‖ ≤ _
    exact cmMul_norm f g)

end DifferentiableAlgebra

/-- Continuous pointwise multiplication in C^m with its sum norm. -/
theorem cm_multiplication : HolderBanachSpec.CmMultiplication := by
  intro 𝕜 _ m a b hab
  exact ⟨DifferentiableAlgebra.cmMulContinuous, fun _ _ _ => rfl⟩

namespace HolderInclusion
variable {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ} {hab : a < b}

/-- The interval length, as a nonnegative bound for all distances. -/
def intervalLength (hab : a < b) : ℝ≥0 := ⟨b - a, sub_nonneg.mpr hab.le⟩

lemma interval_edist_le (x y : Interval a b) : edist x y ≤ intervalLength hab := by
  rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (Real.dist_le_of_mem_Icc x.property y.property)

/-- Lowering an exponent uses only boundedness of the interval. -/
lemma holderWith_lower {r s C : ℝ≥0} {f : Interval a b → 𝕜}
    (hf : HolderWith C r f) (hsr : s ≤ r) :
    HolderWith (C * intervalLength hab ^ ((r : ℝ) - s)) s f :=
  hf.of_le (interval_edist_le (hab := hab)) hsr

/-- Every derivative below the top order is Lipschitz, with a bound from the sum norm. -/
lemma derivative_holder_one {n : ℕ} (f : HolderSpacesSpec.Cm 𝕜 n hab)
    {j : ℕ} (hj : j < n) :
    HolderWith ‖f‖₊ 1 (HolderSpacesSpec.Cm.derivative f ⟨j, by omega⟩) := by
  apply (holderWith_iff_dist _ _ _).mpr
  intro x y
  change ‖iteratedDerivWithin j (intervalExtend f.val) (Icc a b) x -
    iteratedDerivWithin j (intervalExtend f.val) (Icc a b) y‖ ≤
      ‖f‖ * dist x y ^ ((1 : ℝ≥0) : ℝ)
  have hb : ∀ t ∈ Icc a b,
      ‖intervalExtend (HolderSpacesSpec.Cm.derivative f (⟨j, hj⟩ : Fin n).succ) t‖ ≤ ‖f‖ := by
    intro t ht
    rw [show intervalExtend (HolderSpacesSpec.Cm.derivative f (⟨j, hj⟩ : Fin n).succ) t =
      HolderSpacesSpec.Cm.derivative f (⟨j, hj⟩ : Fin n).succ ⟨t, ht⟩ from
        intervalExtend_apply _ ⟨t, ht⟩]
    exact (ContinuousMap.norm_coe_le_norm _ _).trans (DifferentiableAlgebra.derivative_norm_le f _)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (DifferentiableCompleteness.derivative_chain hab f ⟨j, hj⟩) hb
    (convex_Icc a b) y.property x.property
  simpa only [intervalExtend_apply, NNReal.coe_one, Real.rpow_one, coe_nnnorm,
    Subtype.dist_eq, Real.dist_eq, Real.norm_eq_abs,
    HolderSpacesSpec.Cm.derivative, ContinuousMap.coe_mk, Fin.val_castSucc] using h

/-- Forgetting higher derivatives preserves all the original interval values. -/
def forgetOrder {m n : ℕ} (hmn : m ≤ n) :
    HolderSpacesSpec.Cm 𝕜 n hab →ₗ[𝕜] HolderSpacesSpec.Cm 𝕜 m hab where
  toFun f := ⟨f.val, f.property.of_le (by exact_mod_cast hmn)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma forgetOrder_norm {m n : ℕ} (hmn : m ≤ n) (f : HolderSpacesSpec.Cm 𝕜 n hab) :
    ‖forgetOrder hmn f‖ ≤ (m + 1 : ℕ) * ‖f‖ := by
  rw [HolderSpacesSpec.Cm.norm_eq]
  calc
    _ ≤ ∑ _j : Fin (m + 1), ‖f‖ := by
      apply Finset.sum_le_sum
      intro j _
      apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
      intro x
      exact DifferentiableAlgebra.iteratedDerivWithin_norm_le f
        ((Nat.le_of_lt_succ j.isLt).trans hmn) x
    _ = _ := by simp [nsmul_eq_mul]

/-- A same-order exponent inclusion, valid also for equal exponents. -/
def lowerExponent {n : ℕ} {α β : HolderExponent} (hαβ : α.val ≤ β.val)
    (f : CmHolder 𝕜 n hab β) : CmHolder 𝕜 n hab α :=
  ⟨f.val, (holderWith_lower (hab := hab) f.property.holderWith hαβ).memHolder⟩

lemma lowerExponent_norm {n : ℕ} {α β : HolderExponent} (hαβ : α.val ≤ β.val)
    (f : CmHolder 𝕜 n hab β) :
    ‖lowerExponent hαβ f‖ ≤
      (1 + (intervalLength hab ^ ((β.val : ℝ) - α.val) : ℝ≥0)) * ‖f‖ := by
  have hs : holderSeminorm α (Cm.topDerivativeLinearMap 𝕜 n hab f.val) ≤
      holderSeminorm β (Cm.topDerivativeLinearMap 𝕜 n hab f.val) *
        (intervalLength hab ^ ((β.val : ℝ) - α.val) : ℝ≥0) := by
    exact_mod_cast (holderWith_lower (hab := hab) f.property.holderWith hαβ).nnholderNorm_le
  change ‖f.val‖ + holderSeminorm α (Cm.topDerivativeLinearMap 𝕜 n hab f.val) ≤ _
  have hb := HolderCompleteness.base_norm_le f
  have hh := HolderCompleteness.seminorm_le f
  have hp : (0 : ℝ) ≤ (intervalLength hab ^ ((β.val : ℝ) - α.val) : ℝ≥0) := NNReal.coe_nonneg _
  nlinarith

/-- Losing a derivative gives any permitted Hölder exponent. -/
def lowerOrder {m n : ℕ} (hmn : m < n) (α β : HolderExponent)
    (f : CmHolder 𝕜 n hab β) : CmHolder 𝕜 m hab α :=
  ⟨forgetOrder hmn.le f.val,
    (holderWith_lower (hab := hab) (derivative_holder_one f.val hmn) α.property.2).memHolder⟩

lemma lowerOrder_norm {m n : ℕ} (hmn : m < n) (α β : HolderExponent)
    (f : CmHolder 𝕜 n hab β) :
    ‖lowerOrder hmn α β f‖ ≤
      ((m + 1 : ℕ) + (intervalLength hab ^ ((1 : ℝ) - α.val) : ℝ≥0)) * ‖f‖ := by
  have hs : holderSeminorm α (Cm.topDerivativeLinearMap 𝕜 m hab (forgetOrder hmn.le f.val)) ≤
      ‖f.val‖ * (intervalLength hab ^ ((1 : ℝ) - α.val) : ℝ≥0) := by
    exact_mod_cast (holderWith_lower (hab := hab) (derivative_holder_one f.val hmn)
      α.property.2).nnholderNorm_le
  have hb := forgetOrder_norm hmn.le f.val
  have hf := HolderCompleteness.base_norm_le f
  have hp : (0 : ℝ) ≤ (intervalLength hab ^ ((1 : ℝ) - α.val) : ℝ≥0) := NNReal.coe_nonneg _
  change ‖forgetOrder hmn.le f.val‖ +
    holderSeminorm α (Cm.topDerivativeLinearMap 𝕜 m hab (forgetOrder hmn.le f.val)) ≤ _
  have hmul := mul_le_mul_of_nonneg_left hf (show (0 : ℝ) ≤ (m + 1 : ℕ) by positivity)
  nlinarith

def lowerExponentLinear {n : ℕ} {α β : HolderExponent} (hαβ : α.val ≤ β.val) :
    CmHolder 𝕜 n hab β →ₗ[𝕜] CmHolder 𝕜 n hab α where
  toFun := lowerExponent hαβ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lowerExponentContinuous {n : ℕ} {α β : HolderExponent} (hαβ : α.val ≤ β.val) :
    CmHolder 𝕜 n hab β →L[𝕜] CmHolder 𝕜 n hab α :=
  (lowerExponentLinear hαβ).mkContinuous
    (1 + (intervalLength hab ^ ((β.val : ℝ) - α.val) : ℝ≥0)) (lowerExponent_norm hαβ)

def lowerOrderLinear {m n : ℕ} (hmn : m < n) (α β : HolderExponent) :
    CmHolder 𝕜 n hab β →ₗ[𝕜] CmHolder 𝕜 m hab α where
  toFun := lowerOrder hmn α β
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lowerOrderContinuous {m n : ℕ} (hmn : m < n) (α β : HolderExponent) :
    CmHolder 𝕜 n hab β →L[𝕜] CmHolder 𝕜 m hab α :=
  (lowerOrderLinear hmn α β).mkContinuous
    ((m + 1 : ℕ) + (intervalLength hab ^ ((1 : ℝ) - α.val) : ℝ≥0))
    (lowerOrder_norm hmn α β)

end HolderInclusion

/-- The exact strict regularity inequality yields continuous inclusion. -/
theorem holder_continuous_inclusion : HolderBanachSpec.ContinuousInclusion := by
  intro 𝕜 _ m n a b hab α β h
  have hmn : m ≤ n := by
    have ha : (0 : ℝ) < α.val := by exact_mod_cast α.property.1
    have hb : (β.val : ℝ) ≤ 1 := by exact_mod_cast β.property.2
    by_contra hn
    have hnat : n + 1 ≤ m := by omega
    have hreal : (n : ℝ) + 1 ≤ m := by exact_mod_cast hnat
    linarith
  rcases hmn.eq_or_lt with rfl | hmn
  · have hab' : α.val ≤ β.val := by exact_mod_cast (show (α.val : ℝ) ≤ β.val by linarith)
    exact ⟨HolderInclusion.lowerExponentContinuous hab', fun _ _ => rfl⟩
  · exact ⟨HolderInclusion.lowerOrderContinuous hmn α β, fun _ _ => rfl⟩

namespace HolderAlgebra
variable {𝕜 : Type*} [RCLike 𝕜] {m : ℕ} {a b : ℝ} {hab : a < b} {α : HolderExponent}
open HolderInclusion

/-- One constant controls the Hölder seminorm of every derivative coordinate. -/
def jetBound (hab : a < b) (α : HolderExponent) : ℝ≥0 :=
  max 1 (intervalLength hab ^ ((1 : ℝ) - α.val))

lemma derivative_holder (f : CmHolder 𝕜 m hab α) (j : Fin (m + 1)) :
    HolderWith (‖f‖₊ * jetBound hab α) α.val (HolderSpacesSpec.Cm.derivative f.val j) := by
  by_cases hj : j.val = m
  · have he : j = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext hj
    subst j
    apply f.property.holderWith.mono
    have h : nnHolderNorm α.val (Cm.topDerivativeLinearMap 𝕜 m hab f.val) ≤ ‖f‖₊ := by
      exact_mod_cast HolderCompleteness.seminorm_le f
    exact h.trans (le_mul_of_one_le_right (by positivity) (le_max_left _ _))
  · have hjm : j.val < m := by omega
    have hh := holderWith_lower (hab := hab) (derivative_holder_one f.val hjm) α.property.2
    apply hh.mono
    exact mul_le_mul
      (by exact_mod_cast HolderCompleteness.base_norm_le f)
      (le_max_right _ _) (by positivity) (by positivity)

/-- A derivative coordinate, now in the established bounded Hölder space. -/
def derivativeJet (f : CmHolder 𝕜 m hab α) (j : Fin (m + 1)) :
    BoundedHolder (Interval a b) 𝕜 α :=
  ⟨BoundedContinuousFunction.mkOfCompact (HolderSpacesSpec.Cm.derivative f.val j),
    (derivative_holder f j).memHolder⟩

@[simp] lemma derivativeJet_apply (f : CmHolder 𝕜 m hab α) (j : Fin (m + 1))
    (x : Interval a b) : derivativeJet f j x = HolderSpacesSpec.Cm.derivative f.val j x := rfl

lemma derivativeJet_norm (f : CmHolder 𝕜 m hab α) (j : Fin (m + 1)) :
    ‖derivativeJet f j‖ ≤ (1 + (jetBound hab α : ℝ)) * ‖f‖ := by
  have hb : ‖(derivativeJet f j).val‖ ≤ ‖f‖ := by
    change ‖BoundedContinuousFunction.mkOfCompact (HolderSpacesSpec.Cm.derivative f.val j)‖ ≤ ‖f‖
    rw [BoundedContinuousFunction.norm_mkOfCompact]
    exact (DifferentiableAlgebra.derivative_norm_le f.val j).trans (HolderCompleteness.base_norm_le f)
  have hs : holderSeminorm α (derivativeJet f j) ≤ ‖f‖ * (jetBound hab α : ℝ) := by
    exact_mod_cast (derivative_holder f j).nnholderNorm_le
  change ‖(derivativeJet f j).val‖ + holderSeminorm α (derivativeJet f j) ≤ _
  linarith

/-- Evaluation on the canonical bounded Hölder space is linear. -/
def boundedEval (x : Interval a b) : BoundedHolder (Interval a b) 𝕜 α →ₗ[𝕜] 𝕜 where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The Leibniz expression bundled as a bounded Hölder function. -/
def topProductJet (f g : CmHolder 𝕜 m hab α) : BoundedHolder (Interval a b) 𝕜 α :=
  ∑ i : Fin (m + 1), (m.choose i.val : 𝕜) •
    boundedMul (derivativeJet f i) (derivativeJet g ⟨m - i.val, by omega⟩)

lemma topProductJet_apply (f g : CmHolder 𝕜 m hab α) (x : Interval a b) :
    topProductJet f g x =
      Cm.topDerivativeLinearMap 𝕜 m hab (DifferentiableAlgebra.cmMul f.val g.val) x := by
  change boundedEval x (∑ i : Fin (m + 1), (m.choose i.val : 𝕜) •
    boundedMul (derivativeJet f i) (derivativeJet g ⟨m - i.val, by omega⟩)) =
      iteratedDerivWithin m (intervalExtend (f.val.val * g.val.val)) (Icc a b) x
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  change (∑ i : Fin (m + 1), (m.choose i.val : 𝕜) *
    (iteratedDerivWithin i.val (intervalExtend f.val.val) (Icc a b) x *
      iteratedDerivWithin (m - i.val) (intervalExtend g.val.val) (Icc a b) x)) = _
  rw [DifferentiableAlgebra.intervalExtend_mul,
    iteratedDerivWithin_mul x.property (uniqueDiffOn_Icc hab) (f.val.property x x.property)
      (g.val.property x x.property), Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  exact (mul_assoc _ _ _).symm

/-- A uniform bilinear estimate on the top Hölder coordinate. -/
lemma topProductJet_norm (f g : CmHolder 𝕜 m hab α) :
    ‖topProductJet f g‖ ≤
      ((∑ i : Fin (m + 1), (m.choose i.val : ℝ)) * (1 + (jetBound hab α : ℝ)) ^ 2) *
        ‖f‖ * ‖g‖ := by
  unfold topProductJet
  calc
    _ ≤ ∑ i : Fin (m + 1),
        ‖(m.choose i.val : 𝕜) • boundedMul (derivativeJet f i)
          (derivativeJet g ⟨m - i.val, by omega⟩)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin (m + 1), (m.choose i.val : ℝ) *
        (((1 + (jetBound hab α : ℝ)) * ‖f‖) * ((1 + (jetBound hab α : ℝ)) * ‖g‖)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, RCLike.norm_natCast]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply (boundedMul_norm _ _).trans
      exact mul_le_mul (derivativeJet_norm f i) (derivativeJet_norm g _)
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Multiplication in C^{m,α}; the top seminorm follows from the Hölder Leibniz jet. -/
def cmHolderMul (f g : CmHolder 𝕜 m hab α) : CmHolder 𝕜 m hab α :=
  ⟨DifferentiableAlgebra.cmMul f.val g.val, by
    have h := (topProductJet f g).property
    have he : (topProductJet f g : Interval a b → 𝕜) =
        Cm.topDerivativeLinearMap 𝕜 m hab (DifferentiableAlgebra.cmMul f.val g.val) :=
      funext (topProductJet_apply f g)
    change MemHolder α.val (topProductJet f g : Interval a b → 𝕜) at h
    rw [he] at h
    exact h⟩

@[simp] lemma cmHolderMul_apply (f g : CmHolder 𝕜 m hab α) (x : Interval a b) :
    cmHolderMul f g x = f x * g x := rfl

/-- A finite positive constant for the specified Hölder sum norm. -/
def holderProductBound (m : ℕ) (hab : a < b) (α : HolderExponent) : ℝ :=
  DifferentiableAlgebra.productBound m +
    (∑ i : Fin (m + 1), (m.choose i.val : ℝ)) * (1 + (jetBound hab α : ℝ)) ^ 2

lemma cmHolderMul_norm (f g : CmHolder 𝕜 m hab α) :
    ‖cmHolderMul f g‖ ≤ holderProductBound m hab α * ‖f‖ * ‖g‖ := by
  have hb := DifferentiableAlgebra.cmMul_norm f.val g.val
  have hf := HolderCompleteness.base_norm_le f
  have hg := HolderCompleteness.base_norm_le g
  have hbase : ‖DifferentiableAlgebra.cmMul f.val g.val‖ ≤
      DifferentiableAlgebra.productBound m * ‖f‖ * ‖g‖ := by
    apply hb.trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left hf (by
      unfold DifferentiableAlgebra.productBound; positivity)) hg (norm_nonneg _) (by
        unfold DifferentiableAlgebra.productBound; positivity)
  have hs : holderSeminorm α (Cm.topDerivativeLinearMap 𝕜 m hab
      (DifferentiableAlgebra.cmMul f.val g.val)) ≤ ‖topProductJet f g‖ := by
    have he := funext (topProductJet_apply f g)
    rw [← he]
    exact HolderCompleteness.seminorm_le (topProductJet f g)
  have ht := topProductJet_norm f g
  change ‖DifferentiableAlgebra.cmMul f.val g.val‖ +
    holderSeminorm α (Cm.topDerivativeLinearMap 𝕜 m hab
      (DifferentiableAlgebra.cmMul f.val g.val)) ≤ _
  unfold holderProductBound
  nlinarith

def cmHolderMulLinear : CmHolder 𝕜 m hab α →ₗ[𝕜]
    CmHolder 𝕜 m hab α →ₗ[𝕜] CmHolder 𝕜 m hab α where
  toFun f :=
    { toFun := cmHolderMul f
      map_add' := by
        intro g h
        apply Subtype.ext
        apply Subtype.ext
        ext x
        exact mul_add (f x) (g x) (h x)
      map_smul' := by
        intro c g
        apply Subtype.ext
        apply Subtype.ext
        ext x
        change f x * (c * g x) = c * (f x * g x)
        ring }
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro h
    apply Subtype.ext
    apply Subtype.ext
    ext x
    exact add_mul (f x) (g x) (h x)
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro g
    apply Subtype.ext
    apply Subtype.ext
    ext x
    change (c * f x) * g x = c * (f x * g x)
    ring

def cmHolderMulContinuous : CmHolder 𝕜 m hab α →L[𝕜]
    CmHolder 𝕜 m hab α →L[𝕜] CmHolder 𝕜 m hab α :=
  cmHolderMulLinear.mkContinuous₂ (holderProductBound m hab α) (by
    intro f g
    change ‖cmHolderMul f g‖ ≤ _
    exact cmHolderMul_norm f g)

end HolderAlgebra

/-- Continuous pointwise multiplication in the canonical interval Hölder spaces. -/
theorem cm_holder_multiplication : HolderBanachSpec.CmHolderMultiplication := by
  intro 𝕜 _ m a b hab α
  exact ⟨HolderAlgebra.cmHolderMulContinuous, fun _ _ _ => rfl⟩

/-- On an interval the product has the smaller Hölder exponent. -/
theorem mixed_holder_product : HolderBanachSpec.MixedHolderProduct := by
  intro 𝕜 _ a b hab α β f g
  let γ : HolderExponent := ⟨min α.val β.val,
    lt_min α.property.1 β.property.1, (min_le_left _ _).trans α.property.2⟩
  exact ⟨HolderAlgebra.cmHolderMul
    (HolderInclusion.lowerExponent (α := γ) (min_le_left _ _) f)
    (HolderInclusion.lowerExponent (α := γ) (min_le_right _ _) g), fun _ => rfl⟩

/-- All assertions of the manuscript's differentiable and Hölder Banach proposition. -/
theorem holder_banach : HolderBanachSpec.HolderBanach.{u, v} :=
  ⟨holder_banach_completeness, cm_multiplication, cm_holder_multiplication,
    bounded_holder_multiplication, mixed_holder_product, holder_continuous_inclusion⟩

end ExpandedFA.Supplements
