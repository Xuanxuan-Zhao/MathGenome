import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsAlgebra
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.RsSums
import Mathlib.Algebra.BigOperators.Fin

namespace SingleVariableAnalysis.Stieltjes
open Riemann
open scoped BigOperators
namespace A
export Specs.SingleVariableAnalysis.Ch15.RsAlgebra
  (integrandLinearity integratorLinearity intervalAdditivity)
end A

variable {K : Type} [RCLike K]

/-- Every tag stays in the original closed interval. -/
theorem tag_mem_interval {a b : ℝ} (P : Partition a b) (t : Tagging P) (i : Fin P.n) :
    (t i : ℝ) ∈ Set.Icc a b := by
  have h₁ := P.strictMono.monotone (Fin.zero_le i.castSucc)
  have h₂ := P.strictMono.monotone (Fin.le_last i.succ)
  rw [P.first] at h₁
  rw [P.last] at h₂
  exact ⟨h₁.trans (t i).property.1, (t i).property.2.trans h₂⟩

theorem stieltjes_sum_add {a b : ℝ} (P : Partition a b) (t : Tagging P)
    (f g : ℝ → K) (α : ℝ → ℝ) :
    Stieltjes.taggedSum P t (fun x => f x + g x) α = Stieltjes.taggedSum P t f α + Stieltjes.taggedSum P t g α := by
  simp [Specs.SingleVariableAnalysis.Ch15.RsSums.sumValue, smul_add, Finset.sum_add_distrib]

theorem stieltjes_sum_mul {a b : ℝ} (P : Partition a b) (t : Tagging P)
    (f : ℝ → K) (α : ℝ → ℝ) (r : K) :
    Stieltjes.taggedSum P t (fun x => r * f x) α = r * Stieltjes.taggedSum P t f α := by
  simp [Specs.SingleVariableAnalysis.Ch15.RsSums.sumValue, Finset.mul_sum]

theorem stieltjes_sum_integrator_add {a b : ℝ} (P : Partition a b) (t : Tagging P)
    (f : ℝ → K) (α β : ℝ → ℝ) :
    Stieltjes.taggedSum P t f (fun x => α x + β x) = Stieltjes.taggedSum P t f α + Stieltjes.taggedSum P t f β := by
  simp only [Specs.SingleVariableAnalysis.Ch15.RsSums.sumValue, show ∀ x y z w : ℝ, x + y - (z + w) = (x-z)+(y-w) by intros; ring,
    add_smul, Finset.sum_add_distrib]

theorem stieltjes_sum_integrator_mul {a b : ℝ} (P : Partition a b) (t : Tagging P)
    (f : ℝ → K) (α : ℝ → ℝ) (r : ℝ) :
    Stieltjes.taggedSum P t f (fun x => r * α x) = r • Stieltjes.taggedSum P t f α := by
  simp only [Specs.SingleVariableAnalysis.Ch15.RsSums.sumValue, ← mul_sub, mul_smul, Finset.smul_sum]

private theorem bounded_add {a b : ℝ} {f g : ℝ → K}
    (hf : BoundedOn a b f) (hg : BoundedOn a b g) :
    BoundedOn a b (fun x => f x + g x) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  exact ⟨M+N, fun x hx => (norm_add_le _ _).trans (add_le_add (hM x hx) (hN x hx))⟩

private theorem bounded_mul {a b : ℝ} {f : ℝ → K} (hf : BoundedOn a b f) (r : K) :
    BoundedOn a b (fun x => r * f x) := by
  obtain ⟨M, hM⟩ := hf
  refine ⟨‖r‖ * M, fun x hx => ?_⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM x hx) (norm_nonneg _)

private theorem limit_add {a b : ℝ} {f g : ℝ → K} {α : ℝ → ℝ} {I J : K}
    (hf : RefinementLimit a b f α I) (hg : RefinementLimit a b g α J) :
    RefinementLimit a b (fun x => f x + g x) α (I+J) := by
  intro ε hε
  obtain ⟨P, hP⟩ := hf (ε/2) (half_pos hε)
  obtain ⟨Q, hQ⟩ := hg (ε/2) (half_pos hε)
  obtain ⟨R, _, hRP, hRQ⟩ := common_refinement P Q
  refine ⟨R, fun T hT t => ?_⟩
  change ‖Stieltjes.taggedSum T t (fun x => f x + g x) α - (I+J)‖ < ε
  rw [stieltjes_sum_add]
  have heq : Stieltjes.taggedSum T t f α + Stieltjes.taggedSum T t g α - (I+J) =
      (Stieltjes.taggedSum T t f α-I)+(Stieltjes.taggedSum T t g α-J) := by abel
  rw [heq]
  have h₁ := hP T (hRP.trans hT) t
  have h₂ := hQ T (hRQ.trans hT) t
  exact (norm_add_le _ _).trans_lt (by linarith)

private theorem limit_mul {a b : ℝ} {f : ℝ → K} {α : ℝ → ℝ} {I : K}
    (hf : RefinementLimit a b f α I) (r : K) :
    RefinementLimit a b (fun x => r * f x) α (r*I) := by
  intro ε hε
  have hd : 0 < ‖r‖+1 := by positivity
  obtain ⟨P, hP⟩ := hf (ε/(‖r‖+1)) (div_pos hε hd)
  refine ⟨P, fun Q hQ t => ?_⟩
  change ‖Stieltjes.taggedSum Q t (fun x => r * f x) α-r*I‖ < ε
  rw [stieltjes_sum_mul, ← mul_sub, norm_mul]
  have h := hP Q hQ t
  have hn : ‖r‖ * ‖Stieltjes.taggedSum Q t f α-I‖ ≤ (‖r‖+1) * ‖Stieltjes.taggedSum Q t f α-I‖ :=
    mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  exact hn.trans_lt (by nlinarith [(lt_div_iff₀ hd).mp h])

private theorem integral_add {a b : ℝ} {f g : ℝ → K} {α : ℝ → ℝ} {I J : K}
    (hf : HasIntegral a b f α I) (hg : HasIntegral a b g α J) :
    HasIntegral a b (fun x => f x + g x) α (I+J) := by
  refine ⟨bounded_add hf.1 hg.1, hf.2.1, ?_⟩
  have h₁ := hf.2.2
  have h₂ := hg.2.2
  by_cases hab : a ≤ b
  · simp only [ite_eq_left hab] at h₁ h₂ ⊢
    exact limit_add h₁ h₂
  · simp only [ite_eq_right hab] at h₁ h₂ ⊢
    simpa only [neg_add] using limit_add h₁ h₂

private theorem integral_mul {a b : ℝ} {f : ℝ → K} {α : ℝ → ℝ} {I : K}
    (hf : HasIntegral a b f α I) (r : K) :
    HasIntegral a b (fun x => r * f x) α (r*I) := by
  refine ⟨bounded_mul hf.1 r, hf.2.1, ?_⟩
  have h := hf.2.2
  by_cases hab : a ≤ b
  · simp only [ite_eq_left hab] at h ⊢
    exact limit_mul h r
  · simp only [ite_eq_right hab] at h ⊢
    simpa only [mul_neg] using limit_mul h r

theorem integrand_linearity : A.integrandLinearity := by
  intro K _ a b f g α I J r s hf hg
  exact integral_add (integral_mul hf r) (integral_mul hg s)

private theorem limit_integrator_add {a b : ℝ} {f : ℝ → K} {α β : ℝ → ℝ} {I J : K}
    (hf : RefinementLimit a b f α I) (hg : RefinementLimit a b f β J) :
    RefinementLimit a b f (fun x => α x + β x) (I+J) := by
  intro ε hε
  obtain ⟨P, hP⟩ := hf (ε/2) (half_pos hε)
  obtain ⟨Q, hQ⟩ := hg (ε/2) (half_pos hε)
  obtain ⟨R, _, hRP, hRQ⟩ := common_refinement P Q
  refine ⟨R, fun T hT t => ?_⟩
  change ‖Stieltjes.taggedSum T t f (fun x => α x + β x) - (I+J)‖ < ε
  rw [stieltjes_sum_integrator_add]
  have heq : Stieltjes.taggedSum T t f α + Stieltjes.taggedSum T t f β - (I+J) =
      (Stieltjes.taggedSum T t f α-I)+(Stieltjes.taggedSum T t f β-J) := by abel
  rw [heq]
  have h₁ := hP T (hRP.trans hT) t
  have h₂ := hQ T (hRQ.trans hT) t
  exact (norm_add_le _ _).trans_lt (by linarith)

private theorem limit_integrator_mul {a b : ℝ} {f : ℝ → K} {α : ℝ → ℝ} {I : K}
    (hf : RefinementLimit a b f α I) (r : ℝ) :
    RefinementLimit a b f (fun x => r * α x) (r • I) := by
  intro ε hε
  have hd : 0 < ‖r‖+1 := by positivity
  obtain ⟨P, hP⟩ := hf (ε/(‖r‖+1)) (div_pos hε hd)
  refine ⟨P, fun Q hQ t => ?_⟩
  change ‖Stieltjes.taggedSum Q t f (fun x => r * α x)-r • I‖ < ε
  rw [stieltjes_sum_integrator_mul, ← smul_sub, norm_smul]
  have h := hP Q hQ t
  have hn : ‖r‖ * ‖Stieltjes.taggedSum Q t f α-I‖ ≤
      (‖r‖+1) * ‖Stieltjes.taggedSum Q t f α-I‖ :=
    mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  exact hn.trans_lt (by nlinarith [(lt_div_iff₀ hd).mp h])

private theorem integral_integrator_add {a b : ℝ} {f : ℝ → K} {α β : ℝ → ℝ} {I J : K}
    (hf : HasIntegral a b f α I) (hg : HasIntegral a b f β J) :
    HasIntegral a b f (fun x => α x + β x) (I+J) := by
  refine ⟨hf.1, bounded_add hf.2.1 hg.2.1, ?_⟩
  have h₁ := hf.2.2
  have h₂ := hg.2.2
  by_cases hab : a ≤ b
  · simp only [ite_eq_left hab] at h₁ h₂ ⊢
    exact limit_integrator_add h₁ h₂
  · simp only [ite_eq_right hab] at h₁ h₂ ⊢
    simpa only [neg_add] using limit_integrator_add h₁ h₂

private theorem integral_integrator_mul {a b : ℝ} {f : ℝ → K} {α : ℝ → ℝ} {I : K}
    (hf : HasIntegral a b f α I) (r : ℝ) :
    HasIntegral a b f (fun x => r * α x) (r • I) := by
  refine ⟨hf.1, bounded_mul hf.2.1 r, ?_⟩
  have h := hf.2.2
  by_cases hab : a ≤ b
  · simp only [ite_eq_left hab] at h ⊢
    exact limit_integrator_mul h r
  · simp only [ite_eq_right hab] at h ⊢
    simpa only [smul_neg] using limit_integrator_mul h r

theorem integrator_linearity : A.integratorLinearity := by
  intro K _ a b f α β I J r s hf hg
  exact integral_integrator_add (integral_integrator_mul hf r) (integral_integrator_mul hg s)

namespace IntervalSplit

/-- Concatenate strict endpoint lists, using the shared endpoint only once. -/
noncomputable def joinPoint {a c b : ℝ} (P : Partition a c) (Q : Partition c b)
    (i : Fin (P.n + Q.n + 1)) : ℝ :=
  if h : i.val ≤ P.n then P.point ⟨i.val, by omega⟩
  else Q.point ⟨i.val - P.n, by omega⟩

@[simp] theorem joinPoint_left {a c b : ℝ} (P : Partition a c) (Q : Partition c b)
    (i : Fin (P.n + Q.n + 1)) (h : i.val ≤ P.n) :
    joinPoint P Q i = P.point ⟨i.val, by omega⟩ := dite_eq_left h

@[simp] theorem joinPoint_right {a c b : ℝ} (P : Partition a c) (Q : Partition c b)
    (i : Fin (P.n + Q.n + 1)) (h : P.n ≤ i.val) :
    joinPoint P Q i = Q.point ⟨i.val - P.n, by omega⟩ := by
  by_cases h' : i.val ≤ P.n
  · have hi : i.val = P.n := by omega
    simp only [joinPoint, dite_eq_left h']
    have he : (⟨i.val, by omega⟩ : Fin (P.n+1)) = Fin.last P.n := Fin.ext hi
    rw [he, P.last]
    have he' : (⟨i.val-P.n, by omega⟩ : Fin (Q.n+1)) = 0 := by ext; simp [hi]
    rw [he', Q.first]
  · exact dite_eq_right h'

noncomputable abbrev join {a c b : ℝ} (P : Partition a c) (Q : Partition c b) :
    Partition a b where
  n := P.n + Q.n
  point := joinPoint P Q
  strictMono := by
    intro i j hij
    by_cases hi : i.val ≤ P.n
    · by_cases hj : j.val ≤ P.n
      · rw [joinPoint_left P Q i hi, joinPoint_left P Q j hj]
        exact P.strictMono hij
      · rw [joinPoint_left P Q i hi, joinPoint_right P Q j (by omega)]
        have hp := P.strictMono.monotone (Fin.le_last (⟨i.val, by omega⟩ : Fin (P.n+1)))
        rw [P.last] at hp
        have hq := Q.strictMono (show (0 : Fin (Q.n+1)) < ⟨j.val-P.n, by omega⟩ by
          change 0 < j.val-P.n; omega)
        rw [Q.first] at hq
        exact hp.trans_lt hq
    · rw [joinPoint_right P Q i (by omega), joinPoint_right P Q j (by omega)]
      apply Q.strictMono
      change i.val-P.n < j.val-P.n
      have := hij
      change i.val < j.val at this
      omega
  first := by
    rw [joinPoint_left P Q 0 (by simp)]
    exact P.first
  last := by
    rw [joinPoint_right P Q (Fin.last _) (by simp)]
    convert Q.last using 1
    congr 1
    ext
    simp

@[simp] theorem join_n {a c b : ℝ} (P : Partition a c) (Q : Partition c b) :
    (join P Q).n = P.n+Q.n := rfl

@[simp] theorem join_left {a c b : ℝ} (P : Partition a c) (Q : Partition c b)
    (i : Fin (P.n+1)) :
    (join P Q).point ⟨i.val, by have := i.isLt; dsimp; omega⟩ = P.point i := by
  exact joinPoint_left P Q _ (by dsimp; have := i.isLt; omega)

@[simp] theorem join_right {a c b : ℝ} (P : Partition a c) (Q : Partition c b)
    (i : Fin (Q.n+1)) :
    (join P Q).point ⟨P.n+i.val, by have := i.isLt; dsimp; omega⟩ = Q.point i := by
  rw [show (join P Q).point = joinPoint P Q from rfl, joinPoint_right P Q _ (by simp)]
  congr 1
  ext
  simp

noncomputable def joinTags {a c b : ℝ} (P : Partition a c) (Q : Partition c b)
    (t : Tagging P) (u : Tagging Q) : Tagging (join P Q) := fun i =>
  if h : i.val < P.n then
    ⟨t ⟨i.val, h⟩, by
      change (t ⟨i.val,h⟩ : ℝ) ∈ Set.Icc (joinPoint P Q _) (joinPoint P Q _)
      rw [joinPoint_left P Q _ (by dsimp; omega), joinPoint_left P Q _ (by dsimp; omega)]
      exact (t ⟨i.val,h⟩).property⟩
  else
    ⟨u ⟨i.val-P.n, by have := i.isLt; change i.val < P.n+Q.n at this; omega⟩, by
      change (u _ : ℝ) ∈ Set.Icc (joinPoint P Q _) (joinPoint P Q _)
      rw [joinPoint_right P Q _ (by dsimp; omega), joinPoint_right P Q _ (by dsimp; omega)]
      convert (u ⟨i.val-P.n, by have := i.isLt; change i.val < P.n+Q.n at this; omega⟩).property using 1
      congr 3
      dsimp
      omega⟩

@[simp] theorem joinTags_left {a c b : ℝ} (P : Partition a c) (Q : Partition c b)
    (t : Tagging P) (u : Tagging Q) (i : Fin P.n) :
    (joinTags P Q t u (i.castAdd Q.n) : ℝ) = t i := by
  simp [joinTags, i.isLt]

@[simp] theorem joinTags_right {a c b : ℝ} (P : Partition a c) (Q : Partition c b)
    (t : Tagging P) (u : Tagging Q) (i : Fin Q.n) :
    (joinTags P Q t u (i.natAdd P.n) : ℝ) = u i := by
  simp only [joinTags, Fin.val_natAdd, Nat.not_lt.mpr (Nat.le_add_right _ _), dite_false]
  exact congrArg (fun j : Fin Q.n => (u j : ℝ)) (Fin.ext (by dsimp; omega))

/-- No tag at the common endpoint is dropped: the two adjacent cells have
independent closed-cell tags. -/
theorem sum_join {a c b : ℝ} (P : Partition a c) (Q : Partition c b)
    (t : Tagging P) (u : Tagging Q) (f : ℝ → K) (α : ℝ → ℝ) :
    Stieltjes.taggedSum (join P Q) (joinTags P Q t u) f α =
      Stieltjes.taggedSum P t f α + Stieltjes.taggedSum Q u f α := by
  unfold Stieltjes.taggedSum Specs.SingleVariableAnalysis.Ch15.RsSums.sumValue
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [joinTags_left]
    congr 2 <;> congr 1
    · exact join_left P Q i.succ
    · exact join_left P Q i.castSucc
  · apply Finset.sum_congr rfl
    intro i _
    rw [joinTags_right]
    congr 2 <;> congr 1
    · exact join_right P Q i.succ
    · exact join_right P Q i.castSucc

noncomputable def takeTags {a c b : ℝ} (P : Partition a c) (Q : Partition c b)
    (t : Tagging (join P Q)) : Tagging P := fun i =>
  ⟨t (i.castAdd Q.n), by
    have ht := (t (i.castAdd Q.n)).property
    exact ⟨(join_left P Q i.castSucc).symm.trans_le ht.1,
      ht.2.trans_eq (join_left P Q i.succ)⟩⟩

noncomputable def dropTags {a c b : ℝ} (P : Partition a c) (Q : Partition c b)
    (t : Tagging (join P Q)) : Tagging Q := fun i =>
  ⟨t (i.natAdd P.n), by
    have ht := (t (i.natAdd P.n)).property
    have he : (join P Q).point (i.natAdd P.n).succ = Q.point i.succ := by
      convert join_right P Q i.succ using 1
      congr 1
    exact ⟨(join_right P Q i.castSucc).symm.trans_le ht.1, ht.2.trans_eq he⟩⟩

theorem sum_join_any {a c b : ℝ} (P : Partition a c) (Q : Partition c b)
    (t : Tagging (join P Q)) (f : ℝ → K) (α : ℝ → ℝ) :
    Stieltjes.taggedSum (join P Q) t f α =
      Stieltjes.taggedSum P (takeTags P Q t) f α +
      Stieltjes.taggedSum Q (dropTags P Q t) f α := by
  have he : joinTags P Q (takeTags P Q t) (dropTags P Q t) = t := by
    funext i
    apply Subtype.ext
    dsimp only [joinTags]
    split_ifs with h
    · dsimp [takeTags]
    · dsimp [dropTags]
      exact congrArg (fun j : Fin (P.n+Q.n) => (t j : ℝ)) (Fin.ext (by dsimp; omega))
  rw [← sum_join, he]

private theorem partition_ext {a b : ℝ} (P Q : Partition a b) (hn : P.n = Q.n)
    (hp : ∀ i j, i.val = j.val → P.point i = Q.point j) : P = Q := by
  cases P with
  | mk n p hP hPa hPb =>
    cases Q with
    | mk m q hQ hQa hQb =>
      dsimp at hn
      subst m
      have he : p = q := funext fun i => hp i i rfl
      subst q
      rfl

noncomputable abbrev leftPart {a b : ℝ} (P : Partition a b) (k : Fin (P.n+1)) :
    Partition a (P.point k) where
  n := k.val
  point := fun i => P.point ⟨i.val, by have := i.isLt; have := k.isLt; omega⟩
  strictMono := fun _ _ h => P.strictMono h
  first := P.first
  last := congrArg P.point (Fin.ext rfl)

noncomputable abbrev rightPart {a b : ℝ} (P : Partition a b) (k : Fin (P.n+1)) :
    Partition (P.point k) b where
  n := P.n-k.val
  point := fun i => P.point ⟨k.val+i.val, by have := i.isLt; have := k.isLt; omega⟩
  strictMono := by
    intro i j h
    apply P.strictMono
    change k.val+i.val < k.val+j.val
    exact Nat.add_lt_add_left h _
  first := congrArg P.point (Fin.ext (Nat.add_zero _))
  last := by
    convert P.last using 1
    congr 1
    ext
    dsimp
    have := k.isLt
    omega

theorem join_parts {a b : ℝ} (P : Partition a b) (k : Fin (P.n+1)) :
    join (leftPart P k) (rightPart P k) = P := by
  apply partition_ext
  · dsimp
    have := k.isLt
    omega
  · intro i j hij
    change joinPoint _ _ i = P.point j
    by_cases hi : i.val ≤ k.val
    · rw [joinPoint_left _ _ i hi]
      apply congrArg P.point
      exact Fin.ext hij
    · rw [joinPoint_right _ _ i (by dsimp; omega)]
      apply congrArg P.point
      apply Fin.ext
      dsimp
      omega

/-- A partition containing c is literally a concatenation at c. -/
theorem split_partition {a c b : ℝ} (P : Partition a b) (hc : c ∈ points P) :
    ∃ L : Partition a c, ∃ R : Partition c b, join L R = P := by
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hc
  subst c
  exact ⟨leftPart P k, rightPart P k, join_parts P k⟩

private theorem point_mem {a b : ℝ} (P : Partition a b) (i : Fin (P.n+1)) :
    P.point i ∈ points P := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem points_join {a c b : ℝ} (P : Partition a c) (Q : Partition c b) :
    points (join P Q) = points P ∪ points Q := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    by_cases hi : i.val ≤ P.n
    · apply Finset.mem_union_left
      rw [show (join P Q).point i = P.point ⟨i.val, by omega⟩ from joinPoint_left P Q i hi]
      exact point_mem P _
    · apply Finset.mem_union_right
      rw [show (join P Q).point i = Q.point ⟨i.val-P.n, by have hh := i.isLt; change i.val < P.n+Q.n+1 at hh; omega⟩ from
        joinPoint_right P Q i (by omega)]
      exact point_mem Q _
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      rw [← join_left P Q i]
      exact point_mem _ _
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      rw [← join_right P Q i]
      exact point_mem _ _

theorem join_refines_iff {a c b : ℝ} (L P : Partition a c) (R Q : Partition c b) :
    Refines (join L R) (join P Q) ↔ Refines L P ∧ Refines R Q := by
  change points (join P Q) ⊆ points (join L R) ↔
    points P ⊆ points L ∧ points Q ⊆ points R
  rw [points_join, points_join]
  constructor
  · intro h
    constructor
    · intro x hx
      rcases Finset.mem_union.mp (h (Finset.mem_union_left _ hx)) with hl | hr
      · exact hl
      · have hx₁ := (endpoints P).2.2 x hx
        have hx₂ := (endpoints R).2.2 x hr
        have he : x = c := le_antisymm hx₁.2 hx₂.1
        simpa only [he] using (endpoints L).2.1
    · intro x hx
      rcases Finset.mem_union.mp (h (Finset.mem_union_right _ hx)) with hl | hr
      · have hx₁ := (endpoints Q).2.2 x hx
        have hx₂ := (endpoints L).2.2 x hl
        have he : x = c := le_antisymm hx₂.2 hx₁.1
        simpa only [he] using (endpoints R).1
      · exact hr
  · rintro ⟨hL,hR⟩ x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ (hL hx)
    · exact Finset.mem_union_right _ (hR hx)

end IntervalSplit

open IntervalSplit

private theorem limit_join {a c b : ℝ} {f : ℝ → K} {α : ℝ → ℝ} {I J : K}
    (hL : RefinementLimit a c f α I) (hR : RefinementLimit c b f α J) :
    RefinementLimit a b f α (I+J) := by
  intro ε hε
  obtain ⟨P, hP⟩ := hL (ε/2) (half_pos hε)
  obtain ⟨Q, hQ⟩ := hR (ε/2) (half_pos hε)
  refine ⟨join P Q, fun T hT t => ?_⟩
  have hnode : c ∈ points (join P Q) := by
    rw [points_join]
    exact Finset.mem_union_left _ (endpoints P).2.1
  have hc : c ∈ points T := hT hnode
  obtain ⟨L,R,he⟩ := split_partition T hc
  subst T
  obtain ⟨hL,hR⟩ := (join_refines_iff L P R Q).mp hT
  change ‖Stieltjes.taggedSum (join L R) t f α-(I+J)‖ < ε
  rw [sum_join_any]
  have heq : Stieltjes.taggedSum L (takeTags L R t) f α +
      Stieltjes.taggedSum R (dropTags L R t) f α - (I+J) =
      (Stieltjes.taggedSum L (takeTags L R t) f α-I) +
      (Stieltjes.taggedSum R (dropTags L R t) f α-J) := by abel
  rw [heq]
  exact (norm_add_le _ _).trans_lt (by
    have h₁ := hP L hL (takeTags L R t)
    have h₂ := hQ R hR (dropTags L R t)
    linarith)

/-- Insert c into a controlling partition, then restrict it. -/
private theorem controlling_split {a c b : ℝ} (P : Partition a b)
    (hc : c ∈ Set.Icc a b) :
    ∃ L : Partition a c, ∃ R : Partition c b, Refines (join L R) P := by
  classical
  let T := ofPoints (insert c (points P))
    (Finset.mem_insert_of_mem (endpoints P).1)
    (Finset.mem_insert_of_mem (endpoints P).2.1)
    (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hc
        · exact (endpoints P).2.2 x hx)
  have ht : points T = insert c (points P) := points_ofPoints _ _ _ _
  obtain ⟨L,R,he⟩ := split_partition T (by rw [ht]; exact Finset.mem_insert_self _ _)
  refine ⟨L,R,?_⟩
  change points P ⊆ points (join L R)
  rw [he,ht]
  exact Finset.subset_insert _ _

private theorem cauchy_left {a c b : ℝ} {f : ℝ → K} {α : ℝ → ℝ}
    (hc : c ∈ Set.Icc a b) (h : RefinementCauchy a b f α) :
    RefinementCauchy a c f α := by
  intro ε hε
  obtain ⟨P₀,hP₀⟩ := h ε hε
  obtain ⟨L,R,hLR⟩ := controlling_split P₀ hc
  obtain ⟨u⟩ := tags_exist R
  refine ⟨L, fun P hP t Q hQ v => ?_⟩
  have h₁ := (join_refines_iff P L R R).mpr ⟨hP, Finset.Subset.refl _⟩
  have h₂ := (join_refines_iff Q L R R).mpr ⟨hQ, Finset.Subset.refl _⟩
  have he := hP₀ (join P R) (hLR.trans h₁) (joinTags P R t u)
    (join Q R) (hLR.trans h₂) (joinTags Q R v u)
  simpa only [sum_join, add_sub_add_right_eq_sub] using he

private theorem cauchy_right {a c b : ℝ} {f : ℝ → K} {α : ℝ → ℝ}
    (hc : c ∈ Set.Icc a b) (h : RefinementCauchy a b f α) :
    RefinementCauchy c b f α := by
  intro ε hε
  obtain ⟨P₀,hP₀⟩ := h ε hε
  obtain ⟨L,R,hLR⟩ := controlling_split P₀ hc
  obtain ⟨t⟩ := tags_exist L
  refine ⟨R, fun P hP u Q hQ v => ?_⟩
  have h₁ := (join_refines_iff L L P R).mpr ⟨Finset.Subset.refl _, hP⟩
  have h₂ := (join_refines_iff L L Q R).mpr ⟨Finset.Subset.refl _, hQ⟩
  have he := hP₀ (join L P) (hLR.trans h₁) (joinTags L P t u)
    (join L Q) (hLR.trans h₂) (joinTags L Q t v)
  simpa only [sum_join, add_sub_add_left_eq_sub] using he

private theorem scalar_complete (s : ℕ → K)
    (hs : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖s n-s m‖ < ε) :
    ∃ I : K, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ‖s n-I‖ < ε := by
  have hc : CauchySeq s := Metric.cauchySeq_iff.mpr (by
    intro ε hε
    obtain ⟨N,hN⟩ := hs ε hε
    exact ⟨N, fun m hm n hn => by simpa only [dist_eq_norm] using hN n hn m hm⟩)
  obtain ⟨I,hI⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨I, by simpa only [dist_eq_norm] using Metric.tendsto_atTop.mp hI⟩

private theorem bounded_restrict {E : Type*} [NormedAddCommGroup E]
    {a b c d : ℝ} {f : ℝ → E} (hf : BoundedOn a b f)
    (ha : a ≤ c) (hb : d ≤ b) : BoundedOn c d f := by
  obtain ⟨M,hM⟩ := hf
  exact ⟨M,fun x hx => hM x ⟨ha.trans hx.1, hx.2.trans hb⟩⟩

private theorem bounded_join {E : Type*} [NormedAddCommGroup E]
    {a c b : ℝ} {f : ℝ → E} (hL : BoundedOn a c f) (hR : BoundedOn c b f) :
    BoundedOn a b f := by
  obtain ⟨M,hM⟩ := hL
  obtain ⟨N,hN⟩ := hR
  refine ⟨max M N, fun x hx => ?_⟩
  by_cases hc : x ≤ c
  · exact (hM x ⟨hx.1,hc⟩).trans (le_max_left _ _)
  · exact (hN x ⟨le_of_not_ge hc,hx.2⟩).trans (le_max_right _ _)

private theorem integral_join {a c b : ℝ} {f : ℝ → K} {α : ℝ → ℝ} {I J : K}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hL : HasIntegral a c f α I) (hR : HasIntegral c b f α J) :
    HasIntegral a b f α (I+J) := by
  have hab := hac.trans hcb
  have hL := (integral_iff_of_le a c hac f α I).mp hL
  have hR := (integral_iff_of_le c b hcb f α J).mp hR
  apply (integral_iff_of_le a b hab f α (I+J)).mpr
  exact ⟨bounded_join hL.1 hR.1, bounded_join hL.2.1 hR.2.1,
    limit_join hL.2.2 hR.2.2⟩

private theorem integral_split_forward {a c b : ℝ} {f : ℝ → K} {α : ℝ → ℝ} {V : K}
    (hac : a ≤ c) (hcb : c ≤ b) (h : HasIntegral a b f α V) :
    ∃ I J : K, HasIntegral a c f α I ∧ HasIntegral c b f α J ∧ V = I+J := by
  have hab := hac.trans hcb
  have h' := (integral_iff_of_le a b hab f α V).mp h
  have hc := refinementCauchy_of_limit h'.2.2
  obtain ⟨I,hI⟩ := exists_refinementLimit_of_cauchy scalar_complete (cauchy_left ⟨hac,hcb⟩ hc)
  obtain ⟨J,hJ⟩ := exists_refinementLimit_of_cauchy scalar_complete (cauchy_right ⟨hac,hcb⟩ hc)
  have hIL : HasIntegral a c f α I := (integral_iff_of_le a c hac f α I).mpr
    ⟨bounded_restrict h'.1 le_rfl hcb, bounded_restrict h'.2.1 le_rfl hcb, hI⟩
  have hJR : HasIntegral c b f α J := (integral_iff_of_le c b hcb f α J).mpr
    ⟨bounded_restrict h'.1 hac le_rfl, bounded_restrict h'.2.1 hac le_rfl, hJ⟩
  exact ⟨I,J,hIL,hJR,integral_unique a b f α V (I+J) h (integral_join hac hcb hIL hJR)⟩

/-- Additivity and existence in both directions, retaining endpoints and signs. -/
theorem interval_additivity : A.intervalAdditivity := by
  intro K _ a b c hc f α V
  by_cases hab : a ≤ b
  · have hc' : a ≤ c ∧ c ≤ b := by simpa only [Set.uIcc_of_le hab, Set.mem_Icc] using hc
    constructor
    · exact integral_split_forward hc'.1 hc'.2
    · rintro ⟨I,J,hI,hJ,rfl⟩
      exact integral_join hc'.1 hc'.2 hI hJ
  · have hba : b ≤ a := le_of_not_ge hab
    have hc' : b ≤ c ∧ c ≤ a := by simpa only [Set.uIcc_of_ge hba, Set.mem_Icc] using hc
    constructor
    · intro h
      have hr := (reverse_orientation a b f α V).mp h
      obtain ⟨J,I,hJ,hI,he⟩ := integral_split_forward hc'.1 hc'.2 hr
      refine ⟨-I,-J,?_,?_,?_⟩
      · exact (reverse_orientation c a f α I).mp hI
      · exact (reverse_orientation b c f α J).mp hJ
      · have := congrArg Neg.neg he
        simpa only [neg_neg, neg_add, add_comm] using this
    · rintro ⟨I,J,hI,hJ,rfl⟩
      have hI' := (reverse_orientation a c f α I).mp hI
      have hJ' := (reverse_orientation c b f α J).mp hJ
      have hr := integral_join hc'.1 hc'.2 hJ' hI'
      have hh := (reverse_orientation b a f α (-J + -I)).mp hr
      simpa only [neg_add, neg_neg, add_comm] using hh

end SingleVariableAnalysis.Stieltjes
