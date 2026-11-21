import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.ShuffleBoundary
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.ShuffleModel
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Logic.Equiv.Fin.Rotate

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory Opposite
open scoped Simplicial TensorProduct
namespace P202.ShuffleBoundary
open P202Specs.SingularChains P202Specs.AlexanderWhitney P202Specs.ShuffleModel
universe u w

namespace LatticePath
variable {p q : ℕ}

/-- All inversions are counted in the actual reference step labels. -/
def inversions (s : P202Specs.ShuffleModel.LatticePath p q) :
    Finset (Fin (p+q) × Fin (p+q)) :=
  Finset.univ.filter fun ij => ij.1 < ij.2 ∧ s.stepLabel ij.2 < s.stepLabel ij.1

lemma sign_eq_inversions (s : P202Specs.ShuffleModel.LatticePath p q) :
    s.sign = (-1 : ℤ) ^ (inversions s).card := by
  have h := s.permutation.sign_eq_prod_prod_Iio
  change Equiv.Perm.sign s.permutation = ∏ j, ∏ i ∈ Finset.Iio j,
    (if s.stepLabel i < s.stepLabel j then (1 : ℤˣ) else -1) at h
  have h' : s.sign = ∏ j : Fin (p+q), ∏ i ∈ Finset.Iio j,
      (if s.stepLabel i < s.stepLabel j then (1 : ℤ) else -1) := by
    simpa only [P202Specs.ShuffleModel.LatticePath.sign, Units.coe_prod, apply_ite,
      Units.val_one, Units.val_neg] using
      congrArg (fun a : ℤˣ => (a : ℤ)) h
  rw [h']
  have hj (j : Fin (p+q)) :
      (∏ i ∈ Finset.Iio j, if s.stepLabel i < s.stepLabel j then (1 : ℤ) else -1) =
      ∏ i : Fin (p+q),
        if i < j ∧ s.stepLabel j < s.stepLabel i then (-1 : ℤ) else 1 := by
    rw [← Finset.prod_ite_mem_eq]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hij : i < j
    · have hne := s.stepLabel_injective.ne hij.ne
      simp only [Finset.mem_Iio, hij, true_and, ite_true]
      split_ifs <;> omega
    · simp [hij]
  simp_rw [hj]
  rw [Finset.prod_comm, ← Finset.prod_product']
  change (∏ ij ∈ Finset.univ ×ˢ Finset.univ,
    if ij.1 < ij.2 ∧ s.stepLabel ij.2 < s.stepLabel ij.1 then (-1 : ℤ) else 1) = _
  rw [← Finset.prod_filter]
  simp only [Finset.univ_product_univ, Finset.prod_const]
  rfl

end LatticePath

/-- Deleting a matched position and label from a permutation gives the exact
cofactor sign.  This will account for the surviving factor faces. -/
lemma sign_delete {n : ℕ} (σ : Equiv.Perm (Fin (n+1)))
    (τ : Equiv.Perm (Fin n)) (i j : Fin (n+1))
    (hij : σ i = j) (hrest : ∀ a, σ (i.succAbove a) = j.succAbove (τ a)) :
    (Equiv.Perm.sign σ : ℤ) =
      (-1 : ℤ) ^ (i.val+j.val) * (Equiv.Perm.sign τ : ℤ) := by
  have he : Fin.cycleRange j * σ * (Fin.cycleRange i).symm =
      Equiv.Perm.decomposeFin.symm (0, τ) := by
    apply Equiv.ext
    intro a
    induction a using Fin.cases with
    | zero => simp [Equiv.Perm.mul_apply, Fin.cycleRange_symm_zero, hij]
    | succ a =>
      simp [Equiv.Perm.mul_apply, Fin.cycleRange_symm_succ, hrest,
        Fin.cycleRange_succAbove]
  have hs := congrArg (fun e : Equiv.Perm (Fin (n+1)) => (Equiv.Perm.sign e : ℤ)) he
  simp only [Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange,
    Equiv.Perm.decomposeFin.symm_sign, ite_true, one_mul, Units.val_mul,
    Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at hs
  have hi : (-1 : ℤ)^i.val * (-1)^i.val = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hj : (-1 : ℤ)^j.val * (-1)^j.val = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    (Equiv.Perm.sign σ : ℤ) =
        ((-1 : ℤ)^j.val * (-1)^j.val) *
          ((-1 : ℤ)^i.val * (-1)^i.val) * (Equiv.Perm.sign σ : ℤ) := by rw [hi, hj]; ring
    _ = ((-1 : ℤ)^j.val * (Equiv.Perm.sign σ : ℤ) * (-1)^i.val) *
        ((-1 : ℤ)^i.val * (-1)^j.val) := by ring
    _ = (Equiv.Perm.sign τ : ℤ) * ((-1 : ℤ)^i.val * (-1)^j.val) := by rw [hs]
    _ = _ := by rw [pow_add]; ring

lemma sign_delete_boundary {n : ℕ} (σ : Equiv.Perm (Fin (n+1)))
    (τ : Equiv.Perm (Fin n)) (i j : Fin (n+1))
    (hij : σ i = j) (hrest : ∀ a, σ (i.succAbove a) = j.succAbove (τ a)) :
    (-1 : ℤ)^i.val * (Equiv.Perm.sign σ : ℤ) =
      (-1 : ℤ)^j.val * (Equiv.Perm.sign τ : ℤ) := by
  have hi : (-1 : ℤ)^i.val * (-1)^i.val = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [sign_delete σ τ i j hij hrest, pow_add, ← mul_assoc, ← mul_assoc, hi, one_mul]

/-! Reflecting the middle vertex exchanges two adjacent mixed steps.  The
reflection also makes sense for two equal steps, when it fixes the vertex. -/
private def reflectCoordinate {m n : ℕ} (f : Fin (n+1) →o Fin (m+1))
    (k : ℕ) (hk : k+2 ≤ n) : Fin (n+1) →o Fin (m+1) where
  toFun i := if i.val = k+1 then
    ⟨(f ⟨k, by omega⟩).val + (f ⟨k+2, by omega⟩).val -
      (f ⟨k+1, by omega⟩).val, by
        have h₀ := f.monotone (show (⟨k, by omega⟩ : Fin (n+1)) ≤ ⟨k+1, by omega⟩ by
          simp only [Fin.le_def]; omega)
        have h₁ := f.monotone (show (⟨k+1, by omega⟩ : Fin (n+1)) ≤ ⟨k+2, by omega⟩ by
          simp only [Fin.le_def]; omega)
        have h₂ := (f ⟨k+2, by omega⟩).isLt
        simp only [Fin.le_def] at h₀ h₁
        omega⟩
    else f i
  monotone' i j hij := by
    have h₀ := f.monotone (show (⟨k, by omega⟩ : Fin (n+1)) ≤ ⟨k+1, by omega⟩ by
      simp only [Fin.le_def]; omega)
    have h₁ := f.monotone (show (⟨k+1, by omega⟩ : Fin (n+1)) ≤ ⟨k+2, by omega⟩ by
      simp only [Fin.le_def]; omega)
    simp only [Fin.le_def] at h₀ h₁ hij ⊢
    split_ifs with hi hj hj
    · rfl
    · have h₂ := f.monotone (show (⟨k+2, by omega⟩ : Fin (n+1)) ≤ j by
        simp only [Fin.le_def]; omega)
      simp only [Fin.le_def] at h₂
      simp only [Fin.val_mk]
      omega
    · have h₂ := f.monotone (show i ≤ (⟨k, by omega⟩ : Fin (n+1)) by
        simp only [Fin.le_def]; omega)
      simp only [Fin.le_def] at h₂
      simp only [Fin.val_mk]
      omega
    · exact f.monotone hij

namespace LatticePath
variable {p q : ℕ}

def swapCorner (s : P202Specs.ShuffleModel.LatticePath p q)
    (k : ℕ) (hk : k+2 ≤ p+q) : P202Specs.ShuffleModel.LatticePath p q :=
  ⟨(reflectCoordinate s.horizontal k hk, reflectCoordinate s.vertical k hk), by
    intro i
    change (reflectCoordinate s.horizontal k hk i).val +
      (reflectCoordinate s.vertical k hk i).val = i.val
    simp only [reflectCoordinate, OrderHom.coe_mk]
    split_ifs with hi
    · have h₀ := s.rank ⟨k, by omega⟩
      have h₁ := s.rank ⟨k+1, by omega⟩
      have h₂ := s.rank ⟨k+2, by omega⟩
      have hx := s.horizontal.monotone
        (show (⟨k+1, by omega⟩ : Fin (p+q+1)) ≤ ⟨k+2, by omega⟩ by
          simp only [Fin.le_def]; omega)
      have hy := s.vertical.monotone
        (show (⟨k+1, by omega⟩ : Fin (p+q+1)) ≤ ⟨k+2, by omega⟩ by
          simp only [Fin.le_def]; omega)
      simp only [Fin.le_def, Fin.val_mk] at *
      omega
    · exact s.rank i⟩

lemma swapCorner_horizontal (s : P202Specs.ShuffleModel.LatticePath p q)
    (k : ℕ) (hk : k+2 ≤ p+q) (i : Fin (p+q+1)) :
    ((swapCorner s k hk).horizontal i).val =
      if i.val = k+1 then
        (s.horizontal ⟨k, by omega⟩).val + (s.horizontal ⟨k+2, by omega⟩).val -
          (s.horizontal ⟨k+1, by omega⟩).val
      else (s.horizontal i).val := by
  simp only [swapCorner, P202Specs.ShuffleModel.LatticePath.horizontal,
    reflectCoordinate, OrderHom.coe_mk, apply_ite]
  split_ifs <;> rfl

lemma swapCorner_vertical (s : P202Specs.ShuffleModel.LatticePath p q)
    (k : ℕ) (hk : k+2 ≤ p+q) (i : Fin (p+q+1)) :
    ((swapCorner s k hk).vertical i).val =
      if i.val = k+1 then
        (s.vertical ⟨k, by omega⟩).val + (s.vertical ⟨k+2, by omega⟩).val -
          (s.vertical ⟨k+1, by omega⟩).val
      else (s.vertical i).val := by
  simp only [swapCorner, P202Specs.ShuffleModel.LatticePath.vertical,
    reflectCoordinate, OrderHom.coe_mk, apply_ite]
  split_ifs <;> rfl

lemma swapCorner_involutive (k : ℕ) (hk : k+2 ≤ p+q) :
    Function.Involutive (fun s : P202Specs.ShuffleModel.LatticePath p q => swapCorner s k hk) := by
  intro s
  apply Subtype.ext
  apply Prod.ext
  · apply DFunLike.ext
    intro i
    change (swapCorner (swapCorner s k hk) k hk).horizontal i = s.horizontal i
    apply Fin.ext
    simp only [swapCorner_horizontal, Fin.val_mk,
      show ¬ k = k+1 by omega, show ¬ k+2 = k+1 by omega, ite_false]
    by_cases hi : i.val = k+1
    · simp only [hi, ite_true]
      have hx₀ := s.horizontal.monotone
        (show (⟨k, by omega⟩ : Fin (p+q+1)) ≤ ⟨k+1, by omega⟩ by
          simp only [Fin.le_def]; omega)
      have hx₁ := s.horizontal.monotone
        (show (⟨k+1, by omega⟩ : Fin (p+q+1)) ≤ ⟨k+2, by omega⟩ by
          simp only [Fin.le_def]; omega)
      have he : i = ⟨k+1, by omega⟩ := Fin.ext hi
      rw [he]
      simp only [Fin.le_def] at hx₀ hx₁
      omega
    · simp only [hi, ite_false]
  · apply DFunLike.ext
    intro i
    change (swapCorner (swapCorner s k hk) k hk).vertical i = s.vertical i
    apply Fin.ext
    simp only [swapCorner_vertical, Fin.val_mk,
      show ¬ k = k+1 by omega, show ¬ k+2 = k+1 by omega, ite_false]
    by_cases hi : i.val = k+1
    · simp only [hi, ite_true]
      have hy₀ := s.vertical.monotone
        (show (⟨k, by omega⟩ : Fin (p+q+1)) ≤ ⟨k+1, by omega⟩ by
          simp only [Fin.le_def]; omega)
      have hy₁ := s.vertical.monotone
        (show (⟨k+1, by omega⟩ : Fin (p+q+1)) ≤ ⟨k+2, by omega⟩ by
          simp only [Fin.le_def]; omega)
      have he : i = ⟨k+1, by omega⟩ := Fin.ext hi
      rw [he]
      simp only [Fin.le_def] at hy₀ hy₁
      omega
    · simp only [hi, ite_false]

/-- The adjacent steps are of different kinds exactly when both coordinates
increase once across their union. -/
def IsMixed (s : P202Specs.ShuffleModel.LatticePath p q)
    (k : ℕ) (hk : k+2 ≤ p+q) : Prop :=
  (s.horizontal ⟨k+2, by omega⟩).val = (s.horizontal ⟨k, by omega⟩).val + 1 ∧
  (s.vertical ⟨k+2, by omega⟩).val = (s.vertical ⟨k, by omega⟩).val + 1

instance (s : P202Specs.ShuffleModel.LatticePath p q) (k : ℕ) (hk : k+2 ≤ p+q) :
    Decidable (IsMixed s k hk) := by unfold IsMixed; infer_instance

lemma swapCorner_isMixed (s : P202Specs.ShuffleModel.LatticePath p q)
    (k : ℕ) (hk : k+2 ≤ p+q) :
    IsMixed (swapCorner s k hk) k hk ↔ IsMixed s k hk := by
  simp only [IsMixed, swapCorner_horizontal, swapCorner_vertical, Fin.val_mk,
    show ¬ k = k+1 by omega, show ¬ k+2 = k+1 by omega, ite_false]

lemma stepLabel_val (s : P202Specs.ShuffleModel.LatticePath p q) (i : Fin (p+q)) :
    (s.stepLabel i).val = if (s.horizontal i.succ).val = (s.horizontal i.castSucc).val + 1
      then (s.horizontal i.castSucc).val else p + (s.vertical i.castSucc).val := by
  unfold P202Specs.ShuffleModel.LatticePath.stepLabel
  split_ifs <;> rfl

lemma swapCorner_stepLabel_left (s : P202Specs.ShuffleModel.LatticePath p q)
    (k : ℕ) (hk : k+2 ≤ p+q) (hm : IsMixed s k hk) :
    (swapCorner s k hk).stepLabel ⟨k, by omega⟩ = s.stepLabel ⟨k+1, by omega⟩ := by
  have h₀ := s.step ⟨k, by omega⟩
  have h₁ := s.step ⟨k+1, by omega⟩
  simp only [Fin.succ_mk, Fin.castSucc_mk, Nat.add_assoc, Nat.reduceAdd] at h₀ h₁
  apply Fin.ext
  simp only [stepLabel_val, Fin.succ_mk, Fin.castSucc_mk, Nat.add_assoc, Nat.reduceAdd,
    swapCorner_horizontal, swapCorner_vertical, Fin.val_succ, Fin.val_castSucc,
    Fin.val_mk, show ¬ k = k+1 by omega, show ¬ k+2 = k+1 by omega,
    ite_false, ite_true]
  rcases hm with ⟨hmx,hmy⟩
  rcases h₀ with ⟨h₀x,h₀y⟩ | ⟨h₀x,h₀y⟩ <;>
    rcases h₁ with ⟨h₁x,h₁y⟩ | ⟨h₁x,h₁y⟩ <;>
    simp only [Fin.ext_iff] at h₀x h₀y h₁x h₁y <;>
    split_ifs <;> omega

lemma swapCorner_stepLabel_right (s : P202Specs.ShuffleModel.LatticePath p q)
    (k : ℕ) (hk : k+2 ≤ p+q) (hm : IsMixed s k hk) :
    (swapCorner s k hk).stepLabel ⟨k+1, by omega⟩ = s.stepLabel ⟨k, by omega⟩ := by
  have h := swapCorner_stepLabel_left (swapCorner s k hk) k hk
    ((swapCorner_isMixed s k hk).mpr hm)
  have hss : swapCorner (swapCorner s k hk) k hk = s := swapCorner_involutive k hk s
  rw [hss] at h
  exact h.symm

lemma swapCorner_stepLabel_other (s : P202Specs.ShuffleModel.LatticePath p q)
    (k : ℕ) (hk : k+2 ≤ p+q) (i : Fin (p+q))
    (hi₀ : i.val ≠ k) (hi₁ : i.val ≠ k+1) :
    (swapCorner s k hk).stepLabel i = s.stepLabel i := by
  apply Fin.ext
  simp only [stepLabel_val, Fin.succ_mk, Fin.castSucc_mk, Nat.add_assoc, Nat.reduceAdd,
    swapCorner_horizontal, swapCorner_vertical, Fin.val_succ, Fin.val_castSucc,
    show ¬ i.val+1 = k+1 by omega, hi₁, ite_false]

lemma swapCorner_permutation (s : P202Specs.ShuffleModel.LatticePath p q)
    (k : ℕ) (hk : k+2 ≤ p+q) (hm : IsMixed s k hk) :
    (swapCorner s k hk).permutation =
      s.permutation * Equiv.swap (⟨k, by omega⟩ : Fin (p+q)) ⟨k+1, by omega⟩ := by
  apply Equiv.ext
  intro i
  change (swapCorner s k hk).stepLabel i = s.stepLabel (Equiv.swap _ _ i)
  by_cases hi₀ : i = ⟨k, by omega⟩
  · subst i
    rw [Equiv.swap_apply_left]
    exact swapCorner_stepLabel_left s k hk hm
  by_cases hi₁ : i = ⟨k+1, by omega⟩
  · subst i
    rw [Equiv.swap_apply_right]
    exact swapCorner_stepLabel_right s k hk hm
  rw [Equiv.swap_apply_of_ne_of_ne hi₀ hi₁]
  exact swapCorner_stepLabel_other s k hk i
    (by intro h; exact hi₀ (Fin.ext h)) (by intro h; exact hi₁ (Fin.ext h))

lemma swapCorner_sign (s : P202Specs.ShuffleModel.LatticePath p q)
    (k : ℕ) (hk : k+2 ≤ p+q) (hm : IsMixed s k hk) :
    (swapCorner s k hk).sign = -s.sign := by
  have hne : (⟨k, by omega⟩ : Fin (p+q)) ≠ ⟨k+1, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk] at hv
    omega
  simp only [P202Specs.ShuffleModel.LatticePath.sign, swapCorner_permutation s k hk hm,
    Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne, Units.val_mul,
    Units.val_neg, Units.val_one, mul_neg_one]

lemma swapCorner_ne (s : P202Specs.ShuffleModel.LatticePath p q)
    (k : ℕ) (hk : k+2 ≤ p+q) (hm : IsMixed s k hk) :
    swapCorner s k hk ≠ s := by
  intro he
  have hperm := swapCorner_permutation s k hk hm
  rw [he] at hperm
  have hswap : Equiv.swap (⟨k, by omega⟩ : Fin (p+q)) ⟨k+1, by omega⟩ = 1 :=
    mul_left_cancel (by simpa only [mul_one] using hperm.symm)
  have h := Equiv.congr_fun hswap ⟨k, by omega⟩
  simp only [Equiv.swap_apply_left, Equiv.Perm.one_apply, Fin.ext_iff] at h
  omega

end LatticePath

lemma shuffleSimplex_restrict_eq {X Y : TopCat.{w}} {p q m : ℕ}
    (s t : P202Specs.ShuffleModel.LatticePath p q)
    (σ : Simplex X p) (τ : Simplex Y q) (α : ⦋m⦌ ⟶ ⦋p+q⦌)
    (hx : ∀ j, s.horizontal (α.toOrderHom j) = t.horizontal (α.toOrderHom j))
    (hy : ∀ j, s.vertical (α.toOrderHom j) = t.vertical (α.toOrderHom j)) :
    (TopCat.toSSet.obj (productSpace X Y)).map α.op (shuffleSimplex s σ τ) =
      (TopCat.toSSet.obj (productSpace X Y)).map α.op (shuffleSimplex t σ τ) := by
  apply (simplexEquiv (productSpace X Y) m).injective
  ext z
  change simplexEquiv (productSpace X Y) (p+q) (shuffleSimplex s σ τ)
      (z.map α.toOrderHom) =
    simplexEquiv (productSpace X Y) (p+q) (shuffleSimplex t σ τ) (z.map α.toOrderHom)
  rw [P202.ShuffleModel.simplex_formula, P202.ShuffleModel.simplex_formula]
  simp only [← Convexity.StdSimplex.map_comp]
  have hx' : s.horizontal ∘ α.toOrderHom = t.horizontal ∘ α.toOrderHom := funext hx
  have hy' : s.vertical ∘ α.toOrderHom = t.vertical ∘ α.toOrderHom := funext hy
  rw [hx', hy']

lemma swapCorner_restrict_eq {X Y : TopCat.{w}} {p q m : ℕ}
    (s : P202Specs.ShuffleModel.LatticePath p q) (k : ℕ) (hk : k+2 ≤ p+q)
    (σ : Simplex X p) (τ : Simplex Y q) (α : ⦋m⦌ ⟶ ⦋p+q⦌)
    (hα : ∀ j, (α.toOrderHom j).val ≠ k+1) :
    (TopCat.toSSet.obj (productSpace X Y)).map α.op
        (shuffleSimplex (LatticePath.swapCorner s k hk) σ τ) =
      (TopCat.toSSet.obj (productSpace X Y)).map α.op (shuffleSimplex s σ τ) := by
  apply shuffleSimplex_restrict_eq
  · intro j
    apply Fin.ext
    simp only [LatticePath.swapCorner_horizontal, hα j, ite_false]
  · intro j
    apply Fin.ext
    simp only [LatticePath.swapCorner_vertical, hα j, ite_false]

/-- The entire finite family of mixed faces at a given omitted vertex cancels.
The face map can have any domain; only avoidance of that vertex is used. -/
lemma mixed_restrictions_cancel (R : Type u) [CommRing R]
    {X Y : TopCat.{w}} {p q m : ℕ} (k : ℕ) (hk : k+2 ≤ p+q)
    (σ : Simplex X p) (τ : Simplex Y q) (α : ⦋m⦌ ⟶ ⦋p+q⦌)
    (hα : ∀ j, (α.toOrderHom j).val ≠ k+1) :
    (∑ s : P202Specs.ShuffleModel.LatticePath p q with LatticePath.IsMixed s k hk,
      s.sign • Finsupp.single
        ((TopCat.toSSet.obj (productSpace X Y)).map α.op (shuffleSimplex s σ τ)) (1:R)) = 0 := by
  classical
  apply Finset.sum_involution (fun s _ => LatticePath.swapCorner s k hk)
  · intro s hs
    have hm := (Finset.mem_filter.mp hs).2
    rw [LatticePath.swapCorner_sign s k hk hm,
      swapCorner_restrict_eq s k hk σ τ α hα]
    simp only [neg_smul, add_neg_cancel]
  · intro s hs _
    exact LatticePath.swapCorner_ne s k hk (Finset.mem_filter.mp hs).2
  · intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (LatticePath.swapCorner_isMixed s k hk).mpr (Finset.mem_filter.mp hs).2⟩
  · intro s _
    exact LatticePath.swapCorner_involutive k hk s

/-- Transport of a shared singular simplex changes only its degree index. -/
def castSimplex {X : TopCat.{w}} {m n : ℕ} (h : m=n) : Simplex X m → Simplex X n :=
  by subst n; exact id

lemma castSimplex_formula {X : TopCat.{w}} {m n : ℕ} (h : m=n)
    (σ : Simplex X m) (z : StdSimplex n) :
    simplexEquiv X n (castSimplex h σ) z =
      simplexEquiv X m σ (z.map (finCongr (congrArg (·+1) h.symm))) := by
  subst n
  change simplexEquiv X m σ z = simplexEquiv X m σ (z.map id)
  rw [Convexity.StdSimplex.map_id]

lemma face_castSimplex {X : TopCat.{w}} {m n : ℕ} (h : m=n+1)
    (i : Fin (n+2)) (σ : Simplex X m) :
    face i (castSimplex h σ) = (TopCat.toSSet.obj X).map
      (SimplexCategory.δ i ≫ eqToHom (congrArg SimplexCategory.mk h.symm)).op σ := by
  subst m
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- Mixed omitted faces of the actual singular simplices cancel, including
all coefficient and ordinary face signs. -/
lemma mixed_faces_cancel (R : Type u) [CommRing R] {X Y : TopCat.{w}} {p q n : ℕ}
    (h : p+q=n+1) (k : ℕ) (hk : k+2 ≤ p+q)
    (σ : Simplex X p) (τ : Simplex Y q) :
    (∑ s : P202Specs.ShuffleModel.LatticePath p q with LatticePath.IsMixed s k hk,
      ((-1 : ℤ)^(k+1) * s.sign) • Finsupp.single
        (face (⟨k+1, by omega⟩ : Fin (n+2)) (castSimplex h (shuffleSimplex s σ τ))) (1:R)) = 0 := by
  classical
  let i : Fin (n+2) := ⟨k+1, by omega⟩
  let α : ⦋n⦌ ⟶ ⦋p+q⦌ :=
    SimplexCategory.δ i ≫ eqToHom (congrArg SimplexCategory.mk h.symm)
  have hα (a : Fin (n+1)) : (α.toOrderHom a).val ≠ k+1 := by
    have he : (α.toOrderHom a).val = (i.succAbove a).val := by
      simp only [α, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
        Function.comp_apply, SimplexCategory.eqToHom_toOrderHom]
      rfl
    rw [he]
    intro heq
    exact Fin.succAbove_ne i a (Fin.ext heq)
  have hz := mixed_restrictions_cancel R k hk σ τ α hα
  have hz' := congrArg (fun c : Chains R (productSpace X Y) n => (-1 : ℤ)^(k+1) • c) hz
  simpa only [Finset.smul_sum, smul_smul, smul_zero, face_castSimplex, i, α] using hz'

lemma castChains_single (R : Type u) [CommRing R]
    {X : TopCat.{w}} {m n : ℕ} (h : m=n) (σ : Simplex X m) (r : R) :
    castChains R h (Finsupp.single σ r) = Finsupp.single (castSimplex h σ) r := by
  subst n
  rfl

/-- A zero-simplex in the first factor defines an actual continuous map. -/
def insertLeft {X Y : TopCat.{w}} (σ : Simplex X 0) : Y ⟶ productSpace X Y :=
  TopCat.ofHom ⟨fun y => (simplexEquiv X 0 σ (Convexity.StdSimplex.single 0), y),
    continuous_const.prodMk continuous_id⟩

def insertRight {X Y : TopCat.{w}} (τ : Simplex Y 0) : X ⟶ productSpace X Y :=
  TopCat.ofHom ⟨fun x => (x, simplexEquiv Y 0 τ (Convexity.StdSimplex.single 0)),
    continuous_id.prodMk continuous_const⟩

lemma simplex_zero_unique (z : StdSimplex 0) : z = Convexity.StdSimplex.single 0 := by
  letI : Subsingleton (Fin (0+1)) := ⟨by
    intro a b
    apply Fin.ext
    have ha := a.isLt
    have hb := b.isLt
    omega⟩
  apply Convexity.StdSimplex.ext
  ext j
  have hz : z.weights j = 1 := Convexity.StdSimplex.weights_apply_eq_one z j
  have hj : j = 0 := Subsingleton.elim _ _
  simpa [hj, Convexity.StdSimplex.single] using hz

lemma zeroLeft_simplex {X Y : TopCat.{w}} (σ : Simplex X 0)
    {q : ℕ} (τ : Simplex Y q) :
    castSimplex (Nat.zero_add q) (shuffleSimplex (zeroLeft q) σ τ) =
      postSimplex (insertLeft σ) q τ := by
  apply (simplexEquiv (productSpace X Y) q).injective
  ext z
  rw [castSimplex_formula, P202.ShuffleModel.simplex_formula]
  change _ = (simplexEquiv X 0 σ (Convexity.StdSimplex.single 0), simplexEquiv Y q τ z)
  congr 1
  · congr 1
    exact simplex_zero_unique _
  · congr 1
    rw [← Convexity.StdSimplex.map_comp]
    have hid : (zeroLeft q).vertical ∘ finCongr (congrArg (·+1) (Nat.zero_add q).symm) = id := by
      funext j
      apply Fin.ext
      rfl
    rw [hid, Convexity.StdSimplex.map_id]

lemma zeroRight_simplex {X Y : TopCat.{w}} {p : ℕ} (σ : Simplex X p)
    (τ : Simplex Y 0) :
    shuffleSimplex (zeroRight p) σ τ = postSimplex (insertRight τ) p σ := by
  apply (simplexEquiv (productSpace X Y) p).injective
  ext z
  have hf : simplexEquiv (productSpace X Y) p (shuffleSimplex (zeroRight p) σ τ) z =
      (simplexEquiv X p σ (z.map (zeroRight p).horizontal),
        simplexEquiv Y 0 τ (z.map (zeroRight p).vertical)) :=
    P202.ShuffleModel.simplex_formula (zeroRight p) σ τ z
  rw [hf]
  change _ = (simplexEquiv X p σ z, simplexEquiv Y 0 τ (Convexity.StdSimplex.single 0))
  congr 1
  · congr 1
    change z.map id = z
    rw [Convexity.StdSimplex.map_id]
  · congr 1
    exact simplex_zero_unique _

lemma component_zero_left_map (R : Type u) [CommRing R] {X Y : TopCat.{w}}
    (σ : Simplex X 0) (q : ℕ) :
    (castChains R (Nat.zero_add q)).comp
      ((shuffleComponent R X Y 0 q).comp
        ((TensorProduct.mk R (Chains R X 0) (Chains R Y q)) (Finsupp.single σ 1))) =
      ((chainMap R R (insertLeft σ)).f q).hom := by
  apply (Finsupp.basisSingleOne : Module.Basis _ R (Chains R Y q)).ext
  intro τ
  change castChains R (Nat.zero_add q)
    (shuffleComponent R X Y 0 q (Finsupp.single σ (1:R) ⊗ₜ[R] Finsupp.single τ (1:R))) = _
  have h := P202.ShuffleModel.component_zero_left R X Y q σ τ
  change shuffleComponent R X Y 0 q _ = _ at h
  rw [h, castChains_single, zeroLeft_simplex]
  exact (P202.SingularChains.chainMap_single R R (insertLeft σ) q τ 1).symm

lemma component_zero_right_map (R : Type u) [CommRing R] {X Y : TopCat.{w}}
    (τ : Simplex Y 0) (p : ℕ) :
    (shuffleComponent R X Y p 0).comp
      ((TensorProduct.mk R (Chains R X p) (Chains R Y 0)).flip (Finsupp.single τ 1)) =
      ((chainMap R R (insertRight τ)).f p).hom := by
  apply (Finsupp.basisSingleOne : Module.Basis _ R (Chains R X p)).ext
  intro σ
  change shuffleComponent R X Y p 0
    (Finsupp.single σ (1:R) ⊗ₜ[R] Finsupp.single τ (1:R)) = _
  have h := P202.ShuffleModel.component_zero_right R X Y p σ τ
  change shuffleComponent R X Y p 0 _ = _ at h
  rw [h, zeroRight_simplex]
  exact (P202.SingularChains.chainMap_single R R (insertRight τ) p σ 1).symm

/-- The full first-factor degree-zero boundary case, with arbitrary chains in
the other factor.  Only that factor's ordinary boundary occurs. -/
lemma boundary_zero_left (R : Type u) [CommRing R] {X Y : TopCat.{w}}
    (σ : Simplex X 0) (n : ℕ) (c : Chains R Y (n+1)) :
    boundary R R (productSpace X Y) n
      (castChains R (Nat.zero_add (n+1))
        (shuffleComponent R X Y 0 (n+1) (Finsupp.single σ (1:R) ⊗ₜ[R] c))) =
    castChains R (Nat.zero_add n)
      (shuffleComponent R X Y 0 n (Finsupp.single σ (1:R) ⊗ₜ[R] boundary R R Y n c)) := by
  have hc (k : ℕ) (a : Chains R Y k) :=
    LinearMap.congr_fun (component_zero_left_map R σ k) a
  change boundary R R (productSpace X Y) n
    (((castChains R (Nat.zero_add (n+1))).comp
      ((shuffleComponent R X Y 0 (n+1)).comp
        (TensorProduct.mk R _ _ (Finsupp.single σ (1:R))))) c) = _
  rw [hc (n+1) c]
  change _ = ((castChains R (Nat.zero_add n)).comp
    ((shuffleComponent R X Y 0 n).comp
      (TensorProduct.mk R _ _ (Finsupp.single σ (1:R))))) (boundary R R Y n c)
  rw [hc n (boundary R R Y n c)]
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    ((chainMap R R (insertLeft σ)).comm (n+1) n)) c

lemma boundary_zero_right (R : Type u) [CommRing R] {X Y : TopCat.{w}}
    (τ : Simplex Y 0) (n : ℕ) (c : Chains R X (n+1)) :
    boundary R R (productSpace X Y) n
      (shuffleComponent R X Y (n+1) 0 (c ⊗ₜ[R] Finsupp.single τ (1:R))) =
    shuffleComponent R X Y n 0 (boundary R R X n c ⊗ₜ[R] Finsupp.single τ (1:R)) := by
  have hc (k : ℕ) (a : Chains R X k) :=
    LinearMap.congr_fun (component_zero_right_map R τ k) a
  change boundary R R (productSpace X Y) n
    (((shuffleComponent R X Y (n+1) 0).comp
      ((TensorProduct.mk R _ _).flip (Finsupp.single τ (1:R)))) c) = _
  rw [hc (n+1) c]
  change _ = ((shuffleComponent R X Y n 0).comp
    ((TensorProduct.mk R _ _).flip (Finsupp.single τ (1:R)))) (boundary R R X n c)
  rw [hc n (boundary R R X n c)]
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    ((chainMap R R (insertRight τ)).comm (n+1) n)) c

lemma shuffle_single (R : Type u) [CommRing R] (X Y : TopCat.{w}) (n : ℕ)
    (i : Diagonal n) (z : Summand R X Y i.val.1 i.val.2) :
    shuffle R X Y n (Pi.single i z) =
      castChains R i.property (shuffleComponent R X Y i.val.1 i.val.2 z) := by
  classical
  have h := P202.ShuffleModel.total_formula R X Y n (Pi.single i z)
  change shuffle R X Y n (Pi.single i z) = _ at h
  rw [h, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
    rfl
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji]
    simp only [map_zero]
  · simp

/-- Extensionality on the finite diagonal and on both singular bases.  This
reduces the full linear identity to the generator calculation. -/
lemma total_basis_ext (R : Type u) [CommRing R] (X Y : TopCat.{w}) (n : ℕ)
    {N : Type*} [AddCommGroup N] [Module R N]
    (f g : Total R X Y n →ₗ[R] N)
    (h : ∀ i : Diagonal n, ∀ (σ : Simplex X i.val.1) (τ : Simplex Y i.val.2),
      f (Pi.single i (Finsupp.single σ (1:R) ⊗ₜ[R] Finsupp.single τ (1:R))) =
      g (Pi.single i (Finsupp.single σ (1:R) ⊗ₜ[R] Finsupp.single τ (1:R)))) : f = g := by
  classical
  apply LinearMap.pi_ext'
  intro i
  apply ((Finsupp.basisSingleOne : Module.Basis (Simplex X i.val.1) R (Chains R X i.val.1)).tensorProduct
    (Finsupp.basisSingleOne : Module.Basis (Simplex Y i.val.2) R (Chains R Y i.val.2))).ext
  intro ⟨σ,τ⟩
  simpa only [Module.Basis.tensorProduct_apply, Finsupp.coe_basisSingleOne,
    LinearMap.comp_apply, LinearMap.single_apply] using h i σ τ

lemma totalBoundary_single_zero_left (R : Type u) [CommRing R]
    (X Y : TopCat.{w}) (n : ℕ) (z : Summand R X Y 0 (n+1)) :
    totalBoundary R X Y n (Pi.single (⟨(0,n+1), by omega⟩ : Diagonal (n+1)) z) =
      Pi.single (⟨(0,n), by omega⟩ : Diagonal n) (rightBoundary R X Y 0 n z) := by
  classical
  funext i
  have hl : (⟨(i.val.1+1,i.val.2), by have := i.property; omega⟩ : Diagonal (n+1)) ≠
      ⟨(0,n+1), by omega⟩ := by
    intro h
    have h' := congrArg (fun j : Diagonal (n+1) => j.val.1) h
    simp only at h'
    omega
  by_cases hi : i = (⟨(0,n), by omega⟩ : Diagonal n)
  · rw [hi]
    simp only [hi] at hl
    simp only [totalBoundary, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_of_ne hl,
      Pi.single_eq_same, map_zero, pow_zero, one_smul, zero_add]
  · have hr : (⟨(i.val.1,i.val.2+1), by have := i.property; omega⟩ : Diagonal (n+1)) ≠
        ⟨(0,n+1), by omega⟩ := by
      intro h
      apply hi
      apply Subtype.ext
      have hp := congrArg (fun j : Diagonal (n+1) => j.val.1) h
      have hq := congrArg (fun j : Diagonal (n+1) => j.val.2) h
      apply Prod.ext <;> dsimp at * <;> omega
    simp only [totalBoundary, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hr, Pi.single_eq_of_ne hi,
      map_zero, smul_zero, zero_add]

lemma totalBoundary_single_zero_right (R : Type u) [CommRing R]
    (X Y : TopCat.{w}) (n : ℕ) (z : Summand R X Y (n+1) 0) :
    totalBoundary R X Y n (Pi.single (⟨(n+1,0), by omega⟩ : Diagonal (n+1)) z) =
      Pi.single (⟨(n,0), by omega⟩ : Diagonal n) (leftBoundary R X Y n 0 z) := by
  classical
  funext i
  have hr : (⟨(i.val.1,i.val.2+1), by have := i.property; omega⟩ : Diagonal (n+1)) ≠
      ⟨(n+1,0), by omega⟩ := by
    intro h
    have h' := congrArg (fun j : Diagonal (n+1) => j.val.2) h
    simp only at h'
    omega
  by_cases hi : i = (⟨(n,0), by omega⟩ : Diagonal n)
  · rw [hi]
    simp only [hi] at hr
    simp only [totalBoundary, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_of_ne hr,
      Pi.single_eq_same, map_zero, smul_zero, add_zero]
  · have hl : (⟨(i.val.1+1,i.val.2), by have := i.property; omega⟩ : Diagonal (n+1)) ≠
        ⟨(n+1,0), by omega⟩ := by
      intro h
      apply hi
      apply Subtype.ext
      have hp := congrArg (fun j : Diagonal (n+1) => j.val.1) h
      have hq := congrArg (fun j : Diagonal (n+1) => j.val.2) h
      apply Prod.ext <;> dsimp at * <;> omega
    simp only [totalBoundary, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hr, Pi.single_eq_of_ne hi,
      map_zero, smul_zero, zero_add]

lemma chain_identity_on_zero_left (R : Type u) [CommRing R]
    (X Y : TopCat.{w}) (σ : Simplex X 0) (n : ℕ) (c : Chains R Y (n+1)) :
    boundary R R (productSpace X Y) n
      (shuffle R X Y (n+1) (Pi.single (⟨(0,n+1), by omega⟩ : Diagonal (n+1))
        (Finsupp.single σ (1:R) ⊗ₜ[R] c))) =
    shuffle R X Y n (totalBoundary R X Y n
      (Pi.single (⟨(0,n+1), by omega⟩ : Diagonal (n+1))
        (Finsupp.single σ (1:R) ⊗ₜ[R] c))) := by
  classical
  rw [shuffle_single, totalBoundary_single_zero_left, shuffle_single]
  exact boundary_zero_left R σ n c

lemma chain_identity_on_zero_right (R : Type u) [CommRing R]
    (X Y : TopCat.{w}) (τ : Simplex Y 0) (n : ℕ) (c : Chains R X (n+1)) :
    boundary R R (productSpace X Y) n
      (shuffle R X Y (n+1) (Pi.single (⟨(n+1,0), by omega⟩ : Diagonal (n+1))
        (c ⊗ₜ[R] Finsupp.single τ (1:R)))) =
    shuffle R X Y n (totalBoundary R X Y n
      (Pi.single (⟨(n+1,0), by omega⟩ : Diagonal (n+1))
        (c ⊗ₜ[R] Finsupp.single τ (1:R)))) := by
  classical
  rw [shuffle_single, totalBoundary_single_zero_right, shuffle_single]
  exact boundary_zero_right R τ n c

/-- The lowest nonzero differential has only the two endpoint bidegrees. -/
lemma chain_identity_degree_one (R : Type u) [CommRing R] (X Y : TopCat.{w}) :
    (boundary R R (productSpace X Y) 0).comp (shuffle R X Y 1) =
      (shuffle R X Y 0).comp (totalBoundary R X Y 0) := by
  apply total_basis_ext
  intro ⟨⟨p,q⟩,hpq⟩ σ τ
  dsimp at hpq
  have hcases : (p=0 ∧ q=1) ∨ (p=1 ∧ q=0) := by omega
  rcases hcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact chain_identity_on_zero_left R X Y σ 0 (Finsupp.single τ 1)
  · exact chain_identity_on_zero_right R X Y τ 0 (Finsupp.single σ 1)

lemma chain_map_realization_iff (R : Type u) [CommRing R] (X Y : TopCat.{w}) :
    (∃ F : tensorComplex R X Y ⟶ complex R R (productSpace X Y),
      ∀ n, F.f n = ModuleCat.ofHom (shuffle R X Y n)) ↔
    (∀ n, (boundary R R (productSpace X Y) n).comp (shuffle R X Y (n+1)) =
      (shuffle R X Y n).comp (totalBoundary R X Y n)) := by
  constructor
  · rintro ⟨F,hF⟩ n
    have hc := congrArg ModuleCat.Hom.hom (F.comm (n+1) n)
    rw [hF (n+1), hF n] at hc
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, tensorComplex,
      ChainComplex.of_d] using hc
  · intro h
    refine ⟨ChainComplex.ofHom (fun n => ModuleCat.ofHom (shuffle R X Y n)) ?_, ?_⟩
    · intro n
      simp only [tensorComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      exact h n
    · intro n
      rfl

lemma ordinary_boundary_zero (R : Type u) [CommRing R] (X Y : TopCat.{w}) (n : ℕ) :
    (tensorComplex R X Y).d 0 n = 0 ∧ (complex R R (productSpace X Y)).d 0 n = 0 := by
  constructor <;> apply HomologicalComplex.shape <;> simp [ComplexShape.down_Rel]

lemma totalBoundary_single_positive (R : Type u) [CommRing R]
    (X Y : TopCat.{w}) (p q : ℕ) (z : Summand R X Y (p+1) (q+1)) :
    totalBoundary R X Y (p+q+1)
      (Pi.single (⟨(p+1,q+1), by omega⟩ : Diagonal (p+q+1+1)) z) =
      Pi.single (⟨(p,q+1), by omega⟩ : Diagonal (p+q+1))
        (leftBoundary R X Y p (q+1) z) +
      (-1 : ℤ)^(p+1) • Pi.single (⟨(p+1,q), by omega⟩ : Diagonal (p+q+1))
        (rightBoundary R X Y (p+1) q z) := by
  classical
  funext i
  have hne : (⟨(p,q+1), by omega⟩ : Diagonal (p+q+1)) ≠
      ⟨(p+1,q), by omega⟩ := by
    intro h
    have := congrArg (fun j : Diagonal (p+q+1) => j.val.1) h
    dsimp at this
    omega
  by_cases hi : i = (⟨(p,q+1), by omega⟩ : Diagonal (p+q+1))
  · rw [hi]
    have hr : (⟨(p,q+1+1), by omega⟩ : Diagonal (p+q+1+1)) ≠
        ⟨(p+1,q+1), by omega⟩ := by
      intro h
      have := congrArg (fun j : Diagonal (p+q+1+1) => j.val.1) h
      dsimp at this
      omega
    simp only [totalBoundary, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same,
      Pi.single_eq_of_ne hr, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hne,
      map_zero, smul_zero, add_zero]
  by_cases hj : i = (⟨(p+1,q), by omega⟩ : Diagonal (p+q+1))
  · rw [hj]
    have hl : (⟨(p+1+1,q), by omega⟩ : Diagonal (p+q+1+1)) ≠
        ⟨(p+1,q+1), by omega⟩ := by
      intro h
      have := congrArg (fun j : Diagonal (p+q+1+1) => j.val.1) h
      dsimp at this
      omega
    simp only [totalBoundary, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same,
      Pi.single_eq_of_ne hl, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hne.symm,
      map_zero, zero_add]
  · have hl : (⟨(i.val.1+1,i.val.2), by have := i.property; omega⟩ :
        Diagonal (p+q+1+1)) ≠ ⟨(p+1,q+1), by omega⟩ := by
      intro h
      apply hi
      apply Subtype.ext
      have hp := congrArg (fun j : Diagonal (p+q+1+1) => j.val.1) h
      have hq := congrArg (fun j : Diagonal (p+q+1+1) => j.val.2) h
      apply Prod.ext <;> dsimp at * <;> omega
    have hr : (⟨(i.val.1,i.val.2+1), by have := i.property; omega⟩ :
        Diagonal (p+q+1+1)) ≠ ⟨(p+1,q+1), by omega⟩ := by
      intro h
      apply hj
      apply Subtype.ext
      have hp := congrArg (fun j : Diagonal (p+q+1+1) => j.val.1) h
      have hq := congrArg (fun j : Diagonal (p+q+1+1) => j.val.2) h
      apply Prod.ext <;> dsimp at * <;> omega
    simp only [totalBoundary, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hr, Pi.add_apply, Pi.smul_apply,
      Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hj, map_zero, smul_zero, zero_add]

/-- After the finite diagonal has been evaluated, the remaining differential
calculation is exactly the positive-bidegree calculation on two basis simplices. -/
lemma chain_identity_on_positive_iff (R : Type u) [CommRing R]
    (X Y : TopCat.{w}) (p q : ℕ)
    (σ : Simplex X (p+1)) (τ : Simplex Y (q+1)) :
    (boundary R R (productSpace X Y) (p+q+1)
      (shuffle R X Y (p+q+1+1)
        (Pi.single (⟨(p+1,q+1), by omega⟩ : Diagonal (p+q+1+1))
          (Finsupp.single σ (1:R) ⊗ₜ[R] Finsupp.single τ (1:R)))) =
      shuffle R X Y (p+q+1) (totalBoundary R X Y (p+q+1)
        (Pi.single (⟨(p+1,q+1), by omega⟩ : Diagonal (p+q+1+1))
          (Finsupp.single σ (1:R) ⊗ₜ[R] Finsupp.single τ (1:R))))) ↔
    (boundary R R (productSpace X Y) (p+q+1)
      (castChains R (by omega : (p+1)+(q+1)=p+q+1+1)
        (shuffleGenerator R σ τ)) =
      castChains R (by omega : p+(q+1)=p+q+1)
        (shuffleComponent R X Y p (q+1)
          (boundary R R X p (Finsupp.single σ (1:R)) ⊗ₜ[R] Finsupp.single τ (1:R))) +
      (-1 : ℤ)^(p+1) • castChains R (by omega : (p+1)+q=p+q+1)
        (shuffleComponent R X Y (p+1) q
          (Finsupp.single σ (1:R) ⊗ₜ[R] boundary R R Y q (Finsupp.single τ (1:R))))) := by
  rw [shuffle_single, totalBoundary_single_positive, map_add, map_zsmul,
    shuffle_single, shuffle_single]
  have hg : shuffleComponent R X Y (p+1) (q+1)
      (Finsupp.single σ (1:R) ⊗ₜ[R] Finsupp.single τ (1:R)) = shuffleGenerator R σ τ := by
    exact (P202.ShuffleModel.component_formula R X Y (p+1) (q+1) σ τ 1 1).trans
      (by simp [shuffleGenerator])
  rw [hg]
  rfl

lemma component_basis (R : Type u) [CommRing R] (X Y : TopCat.{w}) (p q : ℕ)
    (σ : Simplex X p) (τ : Simplex Y q) :
    shuffleComponent R X Y p q
      (Finsupp.single σ (1:R) ⊗ₜ[R] Finsupp.single τ (1:R)) =
        shuffleGenerator R σ τ := by
  exact (P202.ShuffleModel.component_formula R X Y p q σ τ 1 1).trans
    (by simp [shuffleGenerator])

lemma boundary_generator_expansion (R : Type u) [CommRing R]
    {X Y : TopCat.{w}} {p q n : ℕ} (h : p+q=n+1)
    (σ : Simplex X p) (τ : Simplex Y q) :
    boundary R R (productSpace X Y) n
      (castChains R h (shuffleGenerator R σ τ)) =
      ∑ s : P202Specs.ShuffleModel.LatticePath p q, ∑ i : Fin (n+2),
        ((-1 : ℤ)^i.val * s.sign) • Finsupp.single
          (face i (castSimplex h (shuffleSimplex s σ τ))) (1:R) := by
  classical
  simp only [shuffleGenerator, map_sum, map_zsmul, castChains_single,
    P202.SingularChains.boundary_single, Finset.smul_sum, smul_smul, mul_comm]

lemma chain_identity_iff_positive_generators (R : Type u) [CommRing R]
    (X Y : TopCat.{w}) :
    (∀ n, (boundary R R (productSpace X Y) n).comp (shuffle R X Y (n+1)) =
      (shuffle R X Y n).comp (totalBoundary R X Y n)) ↔
    (∀ (p q : ℕ) (σ : Simplex X (p+1)) (τ : Simplex Y (q+1)),
      boundary R R (productSpace X Y) (p+q+1)
        (castChains R (by omega : (p+1)+(q+1)=p+q+1+1)
          (shuffleGenerator R σ τ)) =
        castChains R (by omega : p+(q+1)=p+q+1)
          (shuffleComponent R X Y p (q+1)
            (boundary R R X p (Finsupp.single σ (1:R)) ⊗ₜ[R] Finsupp.single τ (1:R))) +
        (-1 : ℤ)^(p+1) • castChains R (by omega : (p+1)+q=p+q+1)
          (shuffleComponent R X Y (p+1) q
            (Finsupp.single σ (1:R) ⊗ₜ[R] boundary R R Y q (Finsupp.single τ (1:R))))) := by
  constructor
  · intro h p q σ τ
    apply (chain_identity_on_positive_iff R X Y p q σ τ).mp
    exact LinearMap.congr_fun (h (p+q+1)) _
  · intro h n
    apply total_basis_ext
    intro ⟨⟨p,q⟩,hpq⟩ σ τ
    dsimp at hpq
    cases p with
    | zero =>
      have he : q = n+1 := by omega
      subst q
      exact chain_identity_on_zero_left R X Y σ n (Finsupp.single τ 1)
    | succ p =>
      cases q with
      | zero =>
        have he : p = n := by omega
        subst p
        exact chain_identity_on_zero_right R X Y τ n (Finsupp.single σ 1)
      | succ q =>
        have he : n = p+q+1 := by omega
        subst n
        exact (chain_identity_on_positive_iff R X Y p q σ τ).mpr (h p q σ τ)


/-- A coordinate has a singleton fiber precisely when both existing neighbors differ. -/
lemma fiberUnique_iff_neighbors {N M : ℕ} (f : Fin (N+1) →o Fin (M+1))
    (i : Fin (N+1)) :
    (∀ k, f k = f i → k = i) ↔
    ((∀ (h : 0 < i.val), f ⟨i.val-1, by omega⟩ ≠ f i) ∧
      ∀ (h : i.val < N), f ⟨i.val+1, by omega⟩ ≠ f i) := by
  constructor
  · intro hf
    constructor
    · intro h he
      have := hf _ he
      have := congrArg Fin.val this
      simp only [Fin.val_mk] at this
      omega
    · intro h he
      have := hf _ he
      have := congrArg Fin.val this
      simp only [Fin.val_mk] at this
      omega
  · rintro ⟨hl,hr⟩ k he
    apply Fin.ext
    by_contra hki
    rcases lt_or_gt_of_ne hki with h | h
    · have hi : 0 < i.val := by omega
      have hkp : k ≤ (⟨i.val-1, by omega⟩ : Fin (N+1)) := by
        change k.val ≤ i.val-1
        omega
      have hpi : (⟨i.val-1, by omega⟩ : Fin (N+1)) ≤ i := by
        change i.val-1 ≤ i.val
        omega
      apply hl hi
      exact le_antisymm (f.monotone hpi) (he ▸ f.monotone hkp)
    · have hi : i.val < N := by have := k.isLt; omega
      have hpk : (⟨i.val+1, by omega⟩ : Fin (N+1)) ≤ k := by
        change i.val+1 ≤ k.val
        omega
      have hip : i ≤ (⟨i.val+1, by omega⟩ : Fin (N+1)) := by
        change i.val ≤ i.val+1
        omega
      apply hr hi
      exact le_antisymm (he ▸ f.monotone hpk) (f.monotone hip)

lemma path_not_both_fiberUnique {p q : ℕ} (s : LatticePath p q)
    (hpos : 0 < p+q) (i : Fin (p+q+1)) :
    ¬ ((∀ k, s.horizontal k = s.horizontal i → k=i) ∧
      (∀ k, s.vertical k = s.vertical i → k=i)) := by
  rintro ⟨hh,hv⟩
  by_cases hi : i.val < p+q
  · let j : Fin (p+q) := ⟨i.val,hi⟩
    have hji : j.castSucc = i := Fin.ext rfl
    rcases s.step j with hs | hs
    · have he := hv j.succ (by simpa only [hji] using hs.2)
      have := congrArg Fin.val he
      dsimp [j] at this
      omega
    · have he := hh j.succ (by simpa only [hji] using hs.1)
      have := congrArg Fin.val he
      dsimp [j] at this
      omega
  · let j : Fin (p+q) := ⟨i.val-1,by have := i.isLt; omega⟩
    have hji : j.succ = i := Fin.ext (by dsimp [j]; omega)
    rcases s.step j with hs | hs
    · have he := hv j.castSucc (by simpa only [hji] using hs.2.symm)
      have := congrArg Fin.val he
      dsimp [j] at this
      omega
    · have he := hh j.castSucc (by simpa only [hji] using hs.1.symm)
      have := congrArg Fin.val he
      dsimp [j] at this
      omega

lemma path_fiberUnique_at_zero {p q : ℕ} (s : LatticePath p q)
    (hpos : 0 < p+q) :
    (∀ k, s.horizontal k = s.horizontal 0 → k=0) ∨
      (∀ k, s.vertical k = s.vertical 0 → k=0) := by
  let j : Fin (p+q) := ⟨0,hpos⟩
  rcases s.step j with hs | hs
  · left
    apply (fiberUnique_iff_neighbors _ _).mpr
    constructor
    · intro h; exact False.elim (by simpa using h)
    · intro h he
      have hh := congrArg Fin.val he
      dsimp [j] at hs
      simp only [Fin.val_zero] at hh
      change (s.horizontal ⟨1,by omega⟩).val = (s.horizontal 0).val at hh
      have hx := hs.1
      change (s.horizontal ⟨1,by omega⟩).val = (s.horizontal 0).val+1 at hx
      omega
  · right
    apply (fiberUnique_iff_neighbors _ _).mpr
    constructor
    · intro h; exact False.elim (by simpa using h)
    · intro h he
      have hh := congrArg Fin.val he
      dsimp [j] at hs
      simp only [Fin.val_zero] at hh
      change (s.vertical ⟨1,by omega⟩).val = (s.vertical 0).val at hh
      have hx := hs.2
      change (s.vertical ⟨1,by omega⟩).val = (s.vertical 0).val+1 at hx
      omega

lemma path_fiberUnique_at_last {p q : ℕ} (s : LatticePath p q)
    (hpos : 0 < p+q) :
    (∀ k, s.horizontal k = s.horizontal (Fin.last (p+q)) → k=Fin.last (p+q)) ∨
      (∀ k, s.vertical k = s.vertical (Fin.last (p+q)) → k=Fin.last (p+q)) := by
  let j : Fin (p+q) := ⟨p+q-1,by omega⟩
  have hj : j.succ = Fin.last (p+q) := Fin.ext (by dsimp [j]; omega)
  rcases s.step j with hs | hs
  · left
    apply (fiberUnique_iff_neighbors _ _).mpr
    constructor
    · intro h he
      have hh := congrArg Fin.val he
      have hx := hs.1
      rw [hj] at hx
      change (s.horizontal (Fin.last (p+q))).val =
        (s.horizontal ⟨p+q-1,by omega⟩).val+1 at hx
      change (s.horizontal ⟨p+q-1,by omega⟩).val =
        (s.horizontal (Fin.last (p+q))).val at hh
      omega
    · intro h; exact False.elim (by simpa using h)
  · right
    apply (fiberUnique_iff_neighbors _ _).mpr
    constructor
    · intro h he
      have hh := congrArg Fin.val he
      have hx := hs.2
      rw [hj] at hx
      change (s.vertical (Fin.last (p+q))).val =
        (s.vertical ⟨p+q-1,by omega⟩).val+1 at hx
      change (s.vertical ⟨p+q-1,by omega⟩).val =
        (s.vertical (Fin.last (p+q))).val at hh
      omega
    · intro h; exact False.elim (by simpa using h)

lemma path_neither_fiberUnique_interior {p q : ℕ} (s : LatticePath p q)
    (hpos : 0 < p+q) (i : Fin (p+q+1))
    (hh : ¬ ∀ k, s.horizontal k = s.horizontal i → k=i)
    (hv : ¬ ∀ k, s.vertical k = s.vertical i → k=i) :
    0 < i.val ∧ i.val < p+q := by
  constructor
  · by_contra hi
    have hi : i=0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    rw [hi] at hh hv
    exact (path_fiberUnique_at_zero s hpos).elim hh hv
  · by_contra hi
    have hi : i=Fin.last (p+q) := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
    rw [hi] at hh hv
    exact (path_fiberUnique_at_last s hpos).elim hh hv

lemma path_neither_fiberUnique_mixed {p q : ℕ} (s : LatticePath p q)
    (hpos : 0 < p+q) (i : Fin (p+q+1))
    (hh : ¬ ∀ k, s.horizontal k = s.horizontal i → k=i)
    (hv : ¬ ∀ k, s.vertical k = s.vertical i → k=i) :
    ∃ (hi : 0 < i.val) (hi' : i.val < p+q),
      (s.horizontal ⟨i.val+1,by omega⟩).val =
        (s.horizontal ⟨i.val-1,by omega⟩).val + 1 ∧
      (s.vertical ⟨i.val+1,by omega⟩).val =
        (s.vertical ⟨i.val-1,by omega⟩).val + 1 := by
  obtain ⟨hi,hi'⟩ := path_neither_fiberUnique_interior s hpos i hh hv
  refine ⟨hi,hi',?_⟩
  have hhc : s.horizontal ⟨i.val-1,by omega⟩ = s.horizontal i ∨
      s.horizontal ⟨i.val+1,by omega⟩ = s.horizontal i := by
    by_contra h
    rw [not_or] at h
    apply hh
    apply (fiberUnique_iff_neighbors _ _).mpr
    exact ⟨fun _ => h.1,fun _ => h.2⟩
  have hvc : s.vertical ⟨i.val-1,by omega⟩ = s.vertical i ∨
      s.vertical ⟨i.val+1,by omega⟩ = s.vertical i := by
    by_contra h
    rw [not_or] at h
    apply hv
    apply (fiberUnique_iff_neighbors _ _).mpr
    exact ⟨fun _ => h.1,fun _ => h.2⟩
  have hp := s.rank ⟨i.val-1,by omega⟩
  have hc := s.rank i
  have hn := s.rank ⟨i.val+1,by omega⟩
  simp only [Fin.val_mk] at hp hn
  rcases hhc with hhc | hhc <;> rcases hvc with hvc | hvc
  all_goals have hhc := congrArg Fin.val hhc; have hvc := congrArg Fin.val hvc
  all_goals constructor <;> omega

lemma fiber_not_unique_of_neighbors_gap_one {N M : ℕ}
    (f : Fin (N+1) →o Fin (M+1)) (i : Fin (N+1))
    (hi : 0 < i.val) (hi' : i.val < N)
    (hgap : (f ⟨i.val+1,by omega⟩).val = (f ⟨i.val-1,by omega⟩).val+1) :
    ¬ ∀ k, f k = f i → k=i := by
  intro hf
  obtain ⟨hl,hr⟩ := (fiberUnique_iff_neighbors f i).mp hf
  have hlv : (f ⟨i.val-1,by omega⟩).val ≠ (f i).val := by
    intro h
    exact hl hi (Fin.ext h)
  have hrv : (f ⟨i.val+1,by omega⟩).val ≠ (f i).val := by
    intro h
    exact hr hi' (Fin.ext h)
  have hpl := f.monotone (show (⟨i.val-1,by omega⟩ : Fin (N+1)) ≤ i from by
    change i.val-1 ≤ i.val
    omega)
  have hpr := f.monotone (show i ≤ (⟨i.val+1,by omega⟩ : Fin (N+1)) from by
    change i.val ≤ i.val+1
    omega)
  simp only [Fin.le_def] at hpl hpr
  omega

/-- The faces which survive in neither factor are precisely the mixed interior corners. -/
lemma path_neither_fiberUnique_iff_mixed {p q : ℕ} (s : LatticePath p q)
    (hpos : 0 < p+q) (i : Fin (p+q+1)) :
    ((¬ ∀ k, s.horizontal k = s.horizontal i → k=i) ∧
      (¬ ∀ k, s.vertical k = s.vertical i → k=i)) ↔
    ∃ (hi : 0 < i.val) (hi' : i.val < p+q),
      (s.horizontal ⟨i.val+1,by omega⟩).val =
        (s.horizontal ⟨i.val-1,by omega⟩).val + 1 ∧
      (s.vertical ⟨i.val+1,by omega⟩).val =
        (s.vertical ⟨i.val-1,by omega⟩).val + 1 := by
  constructor
  · rintro ⟨hh,hv⟩
    exact path_neither_fiberUnique_mixed s hpos i hh hv
  · rintro ⟨hi,hi',hh,hv⟩
    exact ⟨fiber_not_unique_of_neighbors_gap_one s.horizontal i hi hi' hh,
      fiber_not_unique_of_neighbors_gap_one s.vertical i hi hi' hv⟩

/-- Every omitted vertex is a horizontal boundary face, a vertical boundary
face, or an interior mixed corner. These three alternatives are disjoint. -/
lemma path_face_partition {p q : ℕ} (s : LatticePath p q)
    (hpos : 0 < p+q) (i : Fin (p+q+1)) :
    (∀ k, s.horizontal k = s.horizontal i → k=i) ∨
    (∀ k, s.vertical k = s.vertical i → k=i) ∨
    ∃ (hi : 0 < i.val) (hi' : i.val < p+q),
      (s.horizontal ⟨i.val+1,by omega⟩).val =
        (s.horizontal ⟨i.val-1,by omega⟩).val + 1 ∧
      (s.vertical ⟨i.val+1,by omega⟩).val =
        (s.vertical ⟨i.val-1,by omega⟩).val + 1 := by
  classical
  by_cases hh : ∀ k, s.horizontal k = s.horizontal i → k=i
  · exact Or.inl hh
  by_cases hv : ∀ k, s.vertical k = s.vertical i → k=i
  · exact Or.inr (Or.inl hv)
  exact Or.inr (Or.inr (path_neither_fiberUnique_mixed s hpos i hh hv))

lemma path_neither_fiberUnique_iff_IsMixed {p q : ℕ} (s : LatticePath p q)
    (hpos : 0 < p+q) (i : Fin (p+q+1)) :
    ((¬ ∀ a, s.horizontal a = s.horizontal i → a=i) ∧
      (¬ ∀ a, s.vertical a = s.vertical i → a=i)) ↔
    ∃ (k : ℕ) (hk : k+2 ≤ p+q), i.val=k+1 ∧ LatticePath.IsMixed s k hk := by
  rw [path_neither_fiberUnique_iff_mixed s hpos i]
  constructor
  · rintro ⟨hi,hi',hh,hv⟩
    refine ⟨i.val-1,by omega,by omega,?_⟩
    have he : i.val-1+2=i.val+1 := by omega
    simpa only [LatticePath.IsMixed,he] using And.intro hh hv
  · rintro ⟨k,hk,he,hm⟩
    refine ⟨by omega,by omega,?_⟩
    have hp : i.val-1=k := by omega
    have hn : i.val+1=k+2 := by omega
    simpa only [LatticePath.IsMixed,hp,hn] using hm

open CategoryTheory
open P202Specs.SingularChains P202Specs.AlexanderWhitney

/-- For each omitted vertex, all faces which survive in neither factor cancel. -/
lemma neither_faces_cancel (R : Type u) [CommRing R] {X Y : TopCat.{w}} {p q n : ℕ}
    (h : p+q=n+1) (i : Fin (n+2)) (σ : Simplex X p) (τ : Simplex Y q) :
    (∑ s : P202Specs.ShuffleModel.LatticePath p q with
      (¬ ∀ a, s.horizontal a = s.horizontal ⟨i.val,by omega⟩ → a=⟨i.val,by omega⟩) ∧
      (¬ ∀ a, s.vertical a = s.vertical ⟨i.val,by omega⟩ → a=⟨i.val,by omega⟩),
      ((-1 : ℤ)^i.val * s.sign) • Finsupp.single
        (face i (castSimplex h (shuffleSimplex s σ τ))) (1:R)) = 0 := by
  classical
  let j : Fin (p+q+1) := ⟨i.val,by omega⟩
  have hpos : 0 < p+q := by omega
  by_cases hi : 0 < i.val ∧ i.val < p+q
  · let k := i.val-1
    have hk : k+2 ≤ p+q := by dsimp [k]; omega
    have he : k+1=i.val := by dsimp [k]; omega
    have hpred : i.val-1=k := rfl
    have hsucc : i.val+1=k+2 := by dsimp [k]; omega
    have hfilter : (Finset.univ.filter fun s : P202Specs.ShuffleModel.LatticePath p q =>
        (¬ ∀ a, s.horizontal a = s.horizontal j → a=j) ∧
        (¬ ∀ a, s.vertical a = s.vertical j → a=j)) =
        Finset.univ.filter (fun s => LatticePath.IsMixed s k hk) := by
      apply Finset.filter_congr
      intro s _
      rw [path_neither_fiberUnique_iff_mixed s hpos j]
      constructor
      · rintro ⟨_,_,hh,hv⟩
        simpa only [LatticePath.IsMixed,j,Fin.val_mk,hpred,hsucc] using And.intro hh hv
      · intro hm
        refine ⟨hi.1,hi.2,?_⟩
        simpa only [LatticePath.IsMixed,j,Fin.val_mk,hpred,hsucc] using hm
    change (∑ s ∈ Finset.univ.filter (fun s : P202Specs.ShuffleModel.LatticePath p q =>
      (¬ ∀ a, s.horizontal a = s.horizontal j → a=j) ∧
      (¬ ∀ a, s.vertical a = s.vertical j → a=j)), _) = 0
    rw [hfilter]
    have hz := mixed_faces_cancel R h k hk σ τ
    have hi' : (⟨k+1,by omega⟩ : Fin (n+2))=i := Fin.ext he
    simpa only [he,hi'] using hz
  · apply Finset.sum_eq_zero
    intro s hs
    have hs := (Finset.mem_filter.mp hs).2
    exact False.elim (hi (path_neither_fiberUnique_interior s hpos j hs.1 hs.2))

lemma signed_faces_partition (R : Type u) [CommRing R] {X Y : TopCat.{w}} {p q n : ℕ}
    (h : p+q=n+1) (σ : Simplex X p) (τ : Simplex Y q) :
    (∑ s : P202Specs.ShuffleModel.LatticePath p q, ∑ i : Fin (n+2),
      ((-1 : ℤ)^i.val * s.sign) • Finsupp.single
        (face i (castSimplex h (shuffleSimplex s σ τ))) (1:R)) =
    (∑ s : P202Specs.ShuffleModel.LatticePath p q, ∑ i : Fin (n+2) with
      (∀ a, s.horizontal a = s.horizontal ⟨i.val,by omega⟩ → a=⟨i.val,by omega⟩),
      ((-1 : ℤ)^i.val * s.sign) • Finsupp.single
        (face i (castSimplex h (shuffleSimplex s σ τ))) (1:R)) +
    (∑ s : P202Specs.ShuffleModel.LatticePath p q, ∑ i : Fin (n+2) with
      (∀ a, s.vertical a = s.vertical ⟨i.val,by omega⟩ → a=⟨i.val,by omega⟩),
      ((-1 : ℤ)^i.val * s.sign) • Finsupp.single
        (face i (castSimplex h (shuffleSimplex s σ τ))) (1:R)) := by
  classical
  let H := fun (s : P202Specs.ShuffleModel.LatticePath p q) (i : Fin (n+2)) =>
    ∀ a, s.horizontal a = s.horizontal ⟨i.val,by omega⟩ → a=⟨i.val,by omega⟩
  let V := fun (s : P202Specs.ShuffleModel.LatticePath p q) (i : Fin (n+2)) =>
    ∀ a, s.vertical a = s.vertical ⟨i.val,by omega⟩ → a=⟨i.val,by omega⟩
  let F := fun (s : P202Specs.ShuffleModel.LatticePath p q) (i : Fin (n+2)) =>
    ((-1 : ℤ)^i.val * s.sign) • Finsupp.single
        (face i (castSimplex h (shuffleSimplex s σ τ))) (1:R)
  have hsplit (s : P202Specs.ShuffleModel.LatticePath p q) :
      (∑ i, F s i) = (∑ i with H s i, F s i) + (∑ i with V s i, F s i) +
        ∑ i with ¬H s i ∧ ¬V s i, F s i := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hdis : ¬ (H s i ∧ V s i) := path_not_both_fiberUnique s (by omega) _
    by_cases hh : H s i <;> by_cases hv : V s i <;> simp [hh,hv] at hdis ⊢
  have hzero : (∑ s, ∑ i with ¬H s i ∧ ¬V s i, F s i) = 0 := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    simpa only [Finset.sum_filter,H,V,F] using neither_faces_cancel R h i σ τ
  change (∑ s, ∑ i, F s i) = (∑ s, ∑ i with H s i, F s i) +
    ∑ s, ∑ i with V s i, F s i
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,hzero,add_zero]


 def blockSwap (p q : ℕ) : Equiv.Perm (Fin (p+q)) :=
  finAddFlip.trans (finCongr (Nat.add_comm q p))

lemma blockSwap_apply (p q : ℕ) (i : Fin (p+q)) :
    (blockSwap p q i).val = if i.val < p then q+i.val else i.val-p := by
  unfold blockSwap
  simp only [Equiv.trans_apply, Equiv.coe_fn_mk, Fin.val_cast]
  by_cases h : i.val < p
  · rw [show i = ⟨i.val, i.isLt⟩ from rfl,
      finAddFlip_apply_mk_left h]
    simp [h]
  · rw [show i = ⟨i.val, i.isLt⟩ from rfl,
      finAddFlip_apply_mk_right (Nat.le_of_not_gt h)]
    simp [h]

lemma blockSwap_eq_rotate_pow (p q : ℕ) (hp : 0 < p) :
    blockSwap p q = finRotate (p+q)^q := by
  have hq : q < p+q := by omega
  have he : blockSwap p q = finCycle (⟨q,hq⟩ : Fin (p+q)) := by
    ext i
    rw [blockSwap_apply]
    simp only [finCycle_apply, Fin.val_add, Fin.val_mk]
    split_ifs with h
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · have hmod : (i.val+q) % (p+q) = i.val-p := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      exact hmod.symm
  rw [he]
  ext i
  rw [finCycle_eq_finRotate_iterate]
  rfl

lemma sign_blockSwap (p q : ℕ) :
    (Equiv.Perm.sign (blockSwap p q) : ℤ) = (-1 : ℤ)^(p*q) := by
  by_cases hp : p = 0
  · subst p
    have he : blockSwap 0 q = 1 := by
      ext i
      simp [blockSwap_apply]
    rw [he]
    simp
  · rw [blockSwap_eq_rotate_pow p q (by omega), map_pow, sign_finRotate]
    simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← pow_mul]
    by_cases hq : q = 0
    · subst q
      simp
    · have hs : p+q-1+1 = p+q := Nat.sub_add_cancel (by omega)
      have ht : q-1+1 = q := Nat.sub_add_cancel (by omega)
      have he : (p+q-1)*q = p*q + q*(q-1) := by nlinarith
      rw [he, pow_add, (Nat.even_mul_pred_self q).neg_one_pow, mul_one]


namespace LatticePath
variable {p q : ℕ}

def transpose (s : P202Specs.ShuffleModel.LatticePath p q) :
    P202Specs.ShuffleModel.LatticePath q p :=
  ⟨(⟨fun k => s.vertical (Fin.cast (by omega) k), by
        intro i j hij
        exact s.vertical.monotone (show (Fin.cast (by omega) i : Fin (p+q+1)) ≤
          Fin.cast (by omega) j from hij)⟩,
      ⟨fun k => s.horizontal (Fin.cast (by omega) k), by
        intro i j hij
        exact s.horizontal.monotone (show (Fin.cast (by omega) i : Fin (p+q+1)) ≤
          Fin.cast (by omega) j from hij)⟩), by
    intro k
    change (s.vertical (Fin.cast (by omega) k)).val +
      (s.horizontal (Fin.cast (by omega) k)).val = k.val
    have h := s.rank (Fin.cast (by omega) k)
    simp only [Fin.val_cast] at h ⊢
    omega⟩

@[simp] lemma transpose_horizontal (s : P202Specs.ShuffleModel.LatticePath p q)
    (k : Fin (q+p+1)) :
    (transpose s).horizontal k = s.vertical (Fin.cast (by omega) k) := rfl

@[simp] lemma transpose_vertical (s : P202Specs.ShuffleModel.LatticePath p q)
    (k : Fin (q+p+1)) :
    (transpose s).vertical k = s.horizontal (Fin.cast (by omega) k) := rfl

@[simp] lemma transpose_transpose (s : P202Specs.ShuffleModel.LatticePath p q) :
    transpose (transpose s) = s := by
  apply Subtype.ext
  apply Prod.ext <;> apply DFunLike.ext <;> intro i <;> rfl

def transposeEquiv (p q : ℕ) :
    P202Specs.ShuffleModel.LatticePath p q ≃ P202Specs.ShuffleModel.LatticePath q p where
  toFun := transpose
  invFun := transpose
  left_inv := transpose_transpose
  right_inv := transpose_transpose

lemma transpose_stepLabel (s : P202Specs.ShuffleModel.LatticePath p q)
    (k : Fin (p+q)) :
    (transpose s).stepLabel (Fin.cast (Nat.add_comm p q) k) = finAddFlip (s.stepLabel k) := by
  apply Fin.ext
  have hcast₁ : (Fin.cast (by omega) (Fin.cast (Nat.add_comm p q) k).succ :
      Fin (p+q+1)) = k.succ := rfl
  have hcast₀ : (Fin.cast (by omega) (Fin.cast (Nat.add_comm p q) k).castSucc :
      Fin (p+q+1)) = k.castSucc := rfl
  rcases s.step k with hs | hs
  · have hv : ¬ (s.vertical k.succ).val = (s.vertical k.castSucc).val + 1 := by
      rw [hs.2]
      omega
    simp only [P202Specs.ShuffleModel.LatticePath.stepLabel, transpose_horizontal,
      hcast₁, hcast₀, hv, hs.1, ↓reduceDIte]
    rw [finAddFlip_apply_mk_left]
    · rfl
    · have h := (s.horizontal k.succ).isLt
      omega
  · have hx : ¬ (s.horizontal k.succ).val = (s.horizontal k.castSucc).val + 1 := by
      rw [hs.1]
      omega
    simp only [P202Specs.ShuffleModel.LatticePath.stepLabel, transpose_horizontal,
      hcast₁, hcast₀, hs.2, hx, ↓reduceDIte]
    rw [finAddFlip_apply_mk_right]
    · simp
    · omega

lemma transpose_permutation (s : P202Specs.ShuffleModel.LatticePath p q) :
    (finCongr (Nat.add_comm q p)).permCongr (transpose s).permutation =
      blockSwap p q * s.permutation := by
  apply Equiv.ext
  intro k
  apply Fin.ext
  change ((transpose s).stepLabel (Fin.cast (Nat.add_comm p q) k)).val =
    (blockSwap p q (s.stepLabel k)).val
  simpa only [blockSwap, Equiv.trans_apply, finCongr_apply_coe] using congrArg Fin.val (transpose_stepLabel s k)

lemma transpose_sign (s : P202Specs.ShuffleModel.LatticePath p q) :
    (transpose s).sign = (-1 : ℤ)^(p*q) * s.sign := by
  have hs := congrArg (fun e : Equiv.Perm (Fin (p+q)) => (Equiv.Perm.sign e : ℤ))
    (transpose_permutation s)
  simp only [Equiv.Perm.sign_permCongr, Equiv.Perm.sign_mul, Units.val_mul,
    sign_blockSwap] at hs
  exact hs

end LatticePath

def swapMap (X Y : TopCat.{w}) : productSpace X Y ⟶ productSpace Y X :=
  TopCat.ofHom ⟨Prod.swap, continuous_snd.prodMk continuous_fst⟩

lemma transpose_shuffleSimplex {X Y : TopCat.{w}} {p q : ℕ}
    (s : P202Specs.ShuffleModel.LatticePath p q) (σ : Simplex X p) (τ : Simplex Y q) :
    castSimplex (Nat.add_comm q p) (shuffleSimplex (LatticePath.transpose s) τ σ) =
      postSimplex (swapMap X Y) (p+q) (shuffleSimplex s σ τ) := by
  apply (simplexEquiv (productSpace Y X) (p+q)).injective
  apply ContinuousMap.ext
  intro z
  rw [castSimplex_formula, P202.ShuffleModel.simplex_formula]
  simp only [postSimplex, P202.SingularChains.simplexEquiv_postcomp,
    ContinuousMap.comp_apply, swapMap, TopCat.hom_ofHom]
  rw [P202.ShuffleModel.simplex_formula]
  simp only [← Convexity.StdSimplex.map_comp]
  have hh : (LatticePath.transpose s).horizontal ∘
      (finCongr (congrArg (·+1) (Nat.add_comm q p).symm)) = s.vertical := by
    funext i
    rfl
  have hv : (LatticePath.transpose s).vertical ∘
      (finCongr (congrArg (·+1) (Nat.add_comm q p).symm)) = s.horizontal := by
    funext i
    rfl
  rw [hh, hv]
  rfl

lemma castSimplex_postSimplex {X Y : TopCat.{w}} {m n : ℕ} (h : m=n)
    (f : X ⟶ Y) (σ : Simplex X m) :
    castSimplex h (postSimplex f m σ) = postSimplex f n (castSimplex h σ) := by
  subst n
  rfl

lemma castChains_comp_castChains (R : Type u) [CommRing R]
    {X : TopCat.{w}} {m n k : ℕ} (h : m=n) (h' : n=k) (c : Chains R X m) :
    castChains R h' (castChains R h c) = castChains R (h.trans h') c := by
  subst n
  subst k
  rfl

lemma castSimplex_comp_castSimplex {X : TopCat.{w}} {m n k : ℕ}
    (h : m=n) (h' : n=k) (σ : Simplex X m) :
    castSimplex h' (castSimplex h σ) = castSimplex (h.trans h') σ := by
  subst n
  subst k
  rfl


lemma transpose_shuffleGenerator (R : Type u) [CommRing R]
    {X Y : TopCat.{w}} {p q : ℕ} (σ : Simplex X p) (τ : Simplex Y q) :
    castChains R (Nat.add_comm q p) (shuffleGenerator R τ σ) =
      (-1 : ℤ)^(p*q) • ((chainMap R R (swapMap X Y)).f (p+q)).hom
        (shuffleGenerator R σ τ) := by
  classical
  simp only [shuffleGenerator, map_sum, map_zsmul, Finset.smul_sum]
  trans ∑ s : P202Specs.ShuffleModel.LatticePath p q,
    (LatticePath.transpose s).sign •
      castChains R (Nat.add_comm q p)
        (Finsupp.single (shuffleSimplex (LatticePath.transpose s) τ σ) (1:R))
  · exact ((LatticePath.transposeEquiv p q).sum_comp _).symm
  · apply Finset.sum_congr rfl
    intro s _
    rw [castChains_single, transpose_shuffleSimplex,
      LatticePath.transpose_sign, P202.SingularChains.chainMap_single]
    rw [smul_smul]
    rfl



namespace LatticePath
variable {p q : ℕ}

def UniqueAt {m n : ℕ} (f : Fin m → Fin n) (i : Fin m) : Prop :=
  ∀ k, f k = f i → k = i

instance {m n : ℕ} (f : Fin m → Fin n) (i : Fin m) : Decidable (UniqueAt f i) := by
  unfold UniqueAt; infer_instance

def omitVertex (i : Fin ((p+1)+q+1)) (k : Fin (p+q+1)) : Fin ((p+1)+q+1) :=
  i.succAbove (Fin.cast (by omega) k)

lemma omitVertex_val (i : Fin ((p+1)+q+1)) (k : Fin (p+q+1)) :
    (omitVertex i k).val = if k.val < i.val then k.val else k.val+1 := by
  simp only [omitVertex, Fin.succAbove, Fin.lt_def, Fin.val_cast, Fin.val_castSucc,
    apply_ite, Fin.val_succ]
  split_ifs <;> rfl

lemma omitVertex_ne (i : Fin ((p+1)+q+1)) (k : Fin (p+q+1)) : omitVertex i k ≠ i :=
  Fin.succAbove_ne _ _

lemma omitVertex_mono (i : Fin ((p+1)+q+1)) : Monotone (omitVertex i) := by
  intro a b hab
  apply Fin.le_iff_val_le_val.mpr
  rw [omitVertex_val, omitVertex_val]
  have hab' : a.val ≤ b.val := hab
  split_ifs <;> omega

lemma uniqueAt_lt {m n : ℕ} (f : Fin m →o Fin n) (i : Fin m) (hi : UniqueAt f i)
    (k : Fin m) (hk : k < i) : f k < f i := by
  have hle := f.monotone hk.le
  exact lt_of_le_of_ne hle (by intro he; exact hk.ne (hi k he))

lemma uniqueAt_gt {m n : ℕ} (f : Fin m →o Fin n) (i : Fin m) (hi : UniqueAt f i)
    (k : Fin m) (hk : i < k) : f i < f k := by
  have hle := f.monotone hk.le
  exact lt_of_le_of_ne hle (by intro he; exact hk.ne' (hi k he.symm))

lemma omitVertex_lt_iff (i : Fin ((p+1)+q+1)) (k : Fin (p+q+1)) :
    omitVertex i k < i ↔ k.val < i.val := by
  change (omitVertex i k).val < i.val ↔ _
  rw [omitVertex_val]
  split_ifs <;> omega

lemma omitVertex_gt_iff (i : Fin ((p+1)+q+1)) (k : Fin (p+q+1)) :
    i < omitVertex i k ↔ i.val ≤ k.val := by
  change i.val < (omitVertex i k).val ↔ _
  rw [omitVertex_val]
  split_ifs <;> omega

/-- Erase a singleton horizontal column from a path. -/
def compressHorizontal (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
    (i : Fin ((p+1)+q+1)) (hi : UniqueAt s.horizontal i) :
    P202Specs.ShuffleModel.LatticePath p q :=
  ⟨(⟨fun k => ⟨if k.val < i.val then (s.horizontal (omitVertex i k)).val
        else (s.horizontal (omitVertex i k)).val - 1, by
      have hx := (s.horizontal (omitVertex i k)).isLt
      by_cases hk : k.val < i.val
      · have hlt := uniqueAt_lt s.horizontal i hi (omitVertex i k) ((omitVertex_lt_iff i k).mpr hk)
        have hj := (s.horizontal i).isLt
        simp only [Fin.lt_def] at hlt
        simp only [hk, ite_true]
        omega
      · simp only [hk, ite_false]
        omega⟩,
      by
        intro a b hab
        have hab' : a.val ≤ b.val := hab
        have hx := s.horizontal.monotone (omitVertex_mono i hab)
        simp only [Fin.le_def] at hx ⊢
        split_ifs with ha hb hb
        · exact hx
        · have hla := uniqueAt_lt s.horizontal i hi (omitVertex i a)
            ((omitVertex_lt_iff i a).mpr ha)
          have hlb := uniqueAt_gt s.horizontal i hi (omitVertex i b)
            ((omitVertex_gt_iff i b).mpr (by omega))
          simp only [Fin.lt_def] at hla hlb
          omega
        · omega
        · omega⟩,
    ⟨fun k => s.vertical (omitVertex i k),
      fun _ _ hab => s.vertical.monotone (omitVertex_mono i hab)⟩), by
    intro k
    change (if k.val < i.val then (s.horizontal (omitVertex i k)).val
        else (s.horizontal (omitVertex i k)).val - 1) +
      (s.vertical (omitVertex i k)).val = k.val
    have hr := s.rank (omitVertex i k)
    rw [omitVertex_val] at hr
    by_cases hk : k.val < i.val
    · simp only [hk, ite_true] at *
      exact hr
    · have hgt := uniqueAt_gt s.horizontal i hi (omitVertex i k)
        ((omitVertex_gt_iff i k).mpr (by omega))
      simp only [Fin.lt_def] at hgt
      simp only [hk, ite_false] at *
      omega⟩

lemma compressHorizontal_horizontal (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
    (i : Fin ((p+1)+q+1)) (hi : UniqueAt s.horizontal i) (k : Fin (p+q+1)) :
    ((compressHorizontal s i hi).horizontal k).val =
      if k.val < i.val then (s.horizontal (omitVertex i k)).val
        else (s.horizontal (omitVertex i k)).val - 1 := rfl

lemma compressHorizontal_vertical (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
    (i : Fin ((p+1)+q+1)) (hi : UniqueAt s.horizontal i) (k : Fin (p+q+1)) :
    (compressHorizontal s i hi).vertical k = s.vertical (omitVertex i k) := rfl

lemma compressHorizontal_skip (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
    (i : Fin ((p+1)+q+1)) (hi : UniqueAt s.horizontal i) (k : Fin (p+q+1)) :
    (s.horizontal i).succAbove ((compressHorizontal s i hi).horizontal k) =
      s.horizontal (omitVertex i k) := by
  apply Fin.ext
  have hx := (s.horizontal (omitVertex i k)).isLt
  rw [Fin.succAbove]
  simp only [apply_ite, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  rw [compressHorizontal_horizontal]
  by_cases hk : k.val < i.val
  · have hlt := uniqueAt_lt s.horizontal i hi (omitVertex i k) ((omitVertex_lt_iff i k).mpr hk)
    simp only [Fin.lt_def] at hlt
    simp only [hk, ite_true]
    split_ifs <;> omega
  · have hgt := uniqueAt_gt s.horizontal i hi (omitVertex i k)
      ((omitVertex_gt_iff i k).mpr (by omega))
    simp only [Fin.lt_def] at hgt
    simp only [hk, ite_false]
    split_ifs <;> omega

lemma monotone_cut_exists {N M : ℕ} (f : Fin N →o Fin M) (j : ℕ) :
    ∃ i ≤ N, ∀ k : Fin N, k.val < i ↔ (f k).val < j := by
  induction N with
  | zero => exact ⟨0, le_rfl, fun k => Fin.elim0 k⟩
  | succ N ih =>
    by_cases h₀ : (f 0).val < j
    · let g : Fin N →o Fin M := ⟨fun k => f k.succ, fun a b h => f.monotone (show a.succ ≤ b.succ by change a.val+1 ≤ b.val+1; have hh : a.val ≤ b.val := h; omega)⟩
      obtain ⟨i, hi, hcut⟩ := ih g
      refine ⟨i+1, by omega, ?_⟩
      intro k
      induction k using Fin.cases with
      | zero => simp only [Fin.val_zero]; exact ⟨fun _ => h₀, fun _ => by omega⟩
      | succ k => simpa only [Fin.val_succ, Nat.add_lt_add_iff_right, g, OrderHom.coe_mk] using hcut k
    · refine ⟨0, Nat.zero_le _, ?_⟩
      intro k
      have hx := f.monotone (Fin.zero_le k)
      simp only [Fin.le_def] at hx
      constructor <;> intro hk <;> omega

lemma horizontal_cut_exists (t : P202Specs.ShuffleModel.LatticePath p q) (j : Fin (p+2)) :
    ∃ i : Fin ((p+1)+q+1), ∀ k : Fin (p+q+1),
      k.val < i.val ↔ (t.horizontal k).val < j.val := by
  obtain ⟨i, hi, hcut⟩ := monotone_cut_exists t.horizontal j.val
  exact ⟨⟨i, by omega⟩, hcut⟩

def horizontalCut (t : P202Specs.ShuffleModel.LatticePath p q) (j : Fin (p+2)) :
    Fin ((p+1)+q+1) := Classical.choose (horizontal_cut_exists t j)

lemma horizontalCut_spec (t : P202Specs.ShuffleModel.LatticePath p q) (j : Fin (p+2))
    (k : Fin (p+q+1)) :
    k.val < (horizontalCut t j).val ↔ (t.horizontal k).val < j.val :=
  Classical.choose_spec (horizontal_cut_exists t j) k

lemma cut_predecessor (t : P202Specs.ShuffleModel.LatticePath p q) (j : Fin (p+2))
    (i : Fin ((p+1)+q+1))
    (hc : ∀ k : Fin (p+q+1), k.val < i.val ↔ (t.horizontal k).val < j.val)
    (hi : 0 < i.val) :
    (t.horizontal ⟨i.val-1, by have := i.isLt; omega⟩).val + 1 = j.val := by
  let a : Fin (p+q+1) := ⟨i.val-1, by have := i.isLt; omega⟩
  have ha : (t.horizontal a).val < j.val := (hc a).mp (by simp only [a, Fin.val_mk]; omega)
  by_cases hlast : i.val = p+q+1
  · have halast : a = Fin.last (p+q) := Fin.ext (by simp only [a, Fin.val_mk, Fin.val_last]; omega)
    have hx := congrArg Fin.val (P202.ShuffleModel.path_terminal t).1
    rw [← halast] at hx
    simp only [Fin.val_last] at hx
    have hj := j.isLt
    change (t.horizontal a).val + 1 = _
    omega
  · let b : Fin (p+q+1) := ⟨i.val, by have := i.isLt; omega⟩
    have hb : j.val ≤ (t.horizontal b).val := by
      have hh := hc b
      simp only [b, Fin.val_mk, lt_self_iff_false, false_iff, not_lt] at hh
      exact hh
    have hr₁ := t.rank a
    have hr₂ := t.rank b
    have hy := t.vertical.monotone (show a ≤ b by change i.val-1 ≤ i.val; omega)
    simp only [Fin.le_def] at hy
    change (t.horizontal a).val + (t.vertical a).val = i.val-1 at hr₁
    change (t.horizontal b).val + (t.vertical b).val = i.val at hr₂
    change (t.horizontal a).val + 1 = _
    omega

lemma cut_successor (t : P202Specs.ShuffleModel.LatticePath p q) (j : Fin (p+2))
    (i : Fin ((p+1)+q+1))
    (hc : ∀ k : Fin (p+q+1), k.val < i.val ↔ (t.horizontal k).val < j.val)
    (hi : i.val < p+q+1) :
    (t.horizontal ⟨i.val, hi⟩).val = j.val := by
  let b : Fin (p+q+1) := ⟨i.val, hi⟩
  have hb : j.val ≤ (t.horizontal b).val := by
    have hh := hc b
    simp only [b, Fin.val_mk, lt_self_iff_false, false_iff, not_lt] at hh
    exact hh
  by_cases hzero : i.val = 0
  · have hbzero : b = 0 := Fin.ext hzero
    have hx := congrArg Fin.val (P202.ShuffleModel.path_initial t).1
    rw [← hbzero] at hx
    simp only [Fin.val_zero] at hx
    change (t.horizontal b).val = _
    omega
  · let a : Fin (p+q+1) := ⟨i.val-1, by omega⟩
    have ha := cut_predecessor t j i hc (by omega)
    have hr₁ := t.rank a
    have hr₂ := t.rank b
    have hy := t.vertical.monotone (show a ≤ b by change i.val-1 ≤ i.val; omega)
    simp only [Fin.le_def] at hy
    change (t.horizontal a).val + (t.vertical a).val = i.val-1 at hr₁
    change (t.horizontal b).val + (t.vertical b).val = i.val at hr₂
    change (t.horizontal b).val = _
    change (t.horizontal a).val + 1 = _ at ha
    omega

lemma cut_vertical_bounds (t : P202Specs.ShuffleModel.LatticePath p q) (j : Fin (p+2))
    (i : Fin ((p+1)+q+1))
    (hc : ∀ k : Fin (p+q+1), k.val < i.val ↔ (t.horizontal k).val < j.val) :
    j.val ≤ i.val ∧ i.val ≤ j.val+q ∧
      (∀ k : Fin (p+q+1), k.val < i.val → (t.vertical k).val ≤ i.val-j.val) ∧
      (∀ k : Fin (p+q+1), i.val ≤ k.val → i.val-j.val ≤ (t.vertical k).val) := by
  have hpre : ∀ (hi : 0 < i.val),
      (t.vertical ⟨i.val-1, by have := i.isLt; omega⟩).val = i.val-j.val := by
    intro hi
    have hx := cut_predecessor t j i hc hi
    have hr := t.rank ⟨i.val-1, by have := i.isLt; omega⟩
    simp only [Fin.val_mk] at hr
    omega
  have hpost : ∀ (hi : i.val < p+q+1),
      (t.vertical ⟨i.val, hi⟩).val = i.val-j.val := by
    intro hi
    have hx := cut_successor t j i hc hi
    have hr := t.rank ⟨i.val, hi⟩
    simp only [Fin.val_mk] at hr
    omega
  have hji : j.val ≤ i.val := by
    by_cases hi : i.val < p+q+1
    · have hx := cut_successor t j i hc hi
      have hr := t.rank ⟨i.val, hi⟩
      simp only [Fin.val_mk] at hr
      omega
    · have hj := j.isLt
      have hh := i.isLt
      omega
  have hiq : i.val ≤ j.val+q := by
    by_cases hi : i.val = 0
    · omega
    · have hv := hpre (by omega)
      have hlt := (t.vertical ⟨i.val-1, by have := i.isLt; omega⟩).isLt
      omega
  refine ⟨hji, hiq, ?_, ?_⟩
  · intro k hk
    have him : 0 < i.val := by omega
    have hy := t.vertical.monotone
      (show k ≤ (⟨i.val-1, by have := i.isLt; omega⟩ : Fin (p+q+1)) by
        change k.val ≤ i.val-1; omega)
    simp only [Fin.le_def] at hy
    rw [hpre him] at hy
    exact hy
  · intro k hk
    have him : i.val < p+q+1 := by have := k.isLt; omega
    have hy := t.vertical.monotone
      (show (⟨i.val, him⟩ : Fin (p+q+1)) ≤ k from hk)
    simp only [Fin.le_def] at hy
    rw [hpost him] at hy
    exact hy

def deleteVertex (i k : Fin ((p+1)+q+1)) (hk : k ≠ i) : Fin (p+q+1) :=
  ⟨if k.val < i.val then k.val else k.val-1, by
    have hi := i.isLt
    have hk' := k.isLt
    have hne : k.val ≠ i.val := by intro hh; exact hk (Fin.ext hh)
    split_ifs <;> omega⟩

lemma deleteVertex_val (i k : Fin ((p+1)+q+1)) (hk : k ≠ i) :
    (deleteVertex i k hk).val = if k.val < i.val then k.val else k.val-1 := rfl

lemma deleteVertex_lt_iff (i k : Fin ((p+1)+q+1)) (hk : k ≠ i) :
    (deleteVertex i k hk).val < i.val ↔ k.val < i.val := by
  rw [deleteVertex_val]
  have hne : k.val ≠ i.val := by intro hh; exact hk (Fin.ext hh)
  split_ifs <;> omega

lemma deleteVertex_mono (i a b : Fin ((p+1)+q+1)) (ha : a ≠ i) (hb : b ≠ i)
    (hab : a ≤ b) : deleteVertex i a ha ≤ deleteVertex i b hb := by
  change (deleteVertex i a ha).val ≤ (deleteVertex i b hb).val
  rw [deleteVertex_val, deleteVertex_val]
  have h : a.val ≤ b.val := hab
  split_ifs <;> omega

lemma omitVertex_deleteVertex (i k : Fin ((p+1)+q+1)) (hk : k ≠ i) :
    omitVertex i (deleteVertex i k hk) = k := by
  apply Fin.ext
  rw [omitVertex_val, deleteVertex_val]
  have hne : k.val ≠ i.val := by intro hh; exact hk (Fin.ext hh)
  split_ifs <;> omega

lemma deleteVertex_omitVertex (i : Fin ((p+1)+q+1)) (k : Fin (p+q+1)) :
    deleteVertex i (omitVertex i k) (omitVertex_ne i k) = k := by
  apply Fin.ext
  rw [deleteVertex_val, omitVertex_val]
  split_ifs <;> omega

lemma succAbove_val (j : Fin (p+2)) (k : Fin (p+1)) :
    (j.succAbove k).val = if k.val < j.val then k.val else k.val+1 := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, apply_ite, Fin.val_succ]
  split_ifs <;> rfl

/-- Insert a column into the unique horizontal step crossing its coordinate. -/
def insertHorizontal (t : P202Specs.ShuffleModel.LatticePath p q) (j : Fin (p+2)) :
    P202Specs.ShuffleModel.LatticePath (p+1) q :=
  let i := horizontalCut t j
  have hc := horizontalCut_spec t j
  have hv := cut_vertical_bounds t j i hc
  ⟨(⟨fun k => if hk : k = i then j else j.succAbove (t.horizontal (deleteVertex i k hk)), by
      intro a b hab
      dsimp only
      split_ifs with ha hb hb
      · exact le_rfl
      · have hb' : i.val ≤ (deleteVertex i b hb).val := by
          rw [deleteVertex_val]
          have hab' : a.val ≤ b.val := hab
          have he := congrArg Fin.val ha
          have hne : b.val ≠ i.val := by intro hh; exact hb (Fin.ext hh)
          split_ifs <;> omega
        have hx : j.val ≤ (t.horizontal (deleteVertex i b hb)).val := by
          have hh := hc (deleteVertex i b hb)
          omega
        apply Fin.le_iff_val_le_val.mpr
        rw [succAbove_val]
        split_ifs <;> omega
      · have ha' : (deleteVertex i a ha).val < i.val := by
          rw [deleteVertex_val]
          have hab' : a.val ≤ b.val := hab
          have he := congrArg Fin.val hb
          have hne : a.val ≠ i.val := by intro hh; exact ha (Fin.ext hh)
          split_ifs <;> omega
        have hx := (hc (deleteVertex i a ha)).mp ha'
        apply Fin.le_iff_val_le_val.mpr
        rw [succAbove_val]
        split_ifs <;> omega
      · exact (Fin.succAboveOrderEmb j).monotone
          (t.horizontal.monotone (deleteVertex_mono i a b ha hb hab))⟩,
    ⟨fun k => if hk : k = i then ⟨i.val-j.val, by omega⟩
      else t.vertical (deleteVertex i k hk), by
      intro a b hab
      dsimp only
      split_ifs with ha hb hb
      · exact le_rfl
      · have hb' : i.val ≤ (deleteVertex i b hb).val := by
          rw [deleteVertex_val]
          have hab' : a.val ≤ b.val := hab
          have he := congrArg Fin.val ha
          have hne : b.val ≠ i.val := by intro hh; exact hb (Fin.ext hh)
          split_ifs <;> omega
        exact hv.2.2.2 _ hb'
      · have ha' : (deleteVertex i a ha).val < i.val := by
          rw [deleteVertex_val]
          have hab' : a.val ≤ b.val := hab
          have he := congrArg Fin.val hb
          have hne : a.val ≠ i.val := by intro hh; exact ha (Fin.ext hh)
          split_ifs <;> omega
        exact hv.2.2.1 _ ha'
      · exact t.vertical.monotone (deleteVertex_mono i a b ha hb hab)⟩), by
    intro k
    simp only [OrderHom.coe_mk]
    split_ifs with hk
    · have he := congrArg Fin.val hk
      change j.val + (i.val-j.val) = k.val
      omega
    · have hr := t.rank (deleteVertex i k hk)
      have hx := hc (deleteVertex i k hk)
      change (deleteVertex i k hk).val < i.val ↔
        (t.horizontal (deleteVertex i k hk)).val < j.val at hx
      have hav := deleteVertex_val i k hk
      rw [succAbove_val]
      have hne : k.val ≠ i.val := by intro hh; exact hk (Fin.ext hh)
      by_cases hki : k.val < i.val
      · simp only [deleteVertex_val, hki, ite_true, lt_self_iff_false, true_iff] at hr hx
        rw [if_pos hx]
        exact hr
      · simp only [deleteVertex_val, hki, ite_false] at hr
        have ha : ¬ (deleteVertex i k hk).val < i.val := by
          rw [deleteVertex_val, if_neg hki]
          omega
        have hx' : ¬ (t.horizontal (deleteVertex i k hk)).val < j.val := by
          intro hh; exact ha (hx.mpr hh)
        rw [if_neg hx']
        omega⟩

lemma insertHorizontal_horizontal (t : P202Specs.ShuffleModel.LatticePath p q)
    (j : Fin (p+2)) (k : Fin ((p+1)+q+1)) :
    (insertHorizontal t j).horizontal k =
      if hk : k = horizontalCut t j then j else
        j.succAbove (t.horizontal (deleteVertex (horizontalCut t j) k hk)) := rfl

lemma insertHorizontal_vertical (t : P202Specs.ShuffleModel.LatticePath p q)
    (j : Fin (p+2)) (k : Fin ((p+1)+q+1)) :
    (insertHorizontal t j).vertical k =
      if hk : k = horizontalCut t j then ⟨(horizontalCut t j).val-j.val, by
        have hv := cut_vertical_bounds t j (horizontalCut t j) (horizontalCut_spec t j)
        omega⟩ else t.vertical (deleteVertex (horizontalCut t j) k hk) := rfl

lemma insertHorizontal_at (t : P202Specs.ShuffleModel.LatticePath p q) (j : Fin (p+2)) :
    (insertHorizontal t j).horizontal (horizontalCut t j) = j := by
  rw [insertHorizontal_horizontal, dif_pos rfl]

lemma insertHorizontal_omit_horizontal (t : P202Specs.ShuffleModel.LatticePath p q)
    (j : Fin (p+2)) (k : Fin (p+q+1)) :
    (insertHorizontal t j).horizontal (omitVertex (horizontalCut t j) k) =
      j.succAbove (t.horizontal k) := by
  rw [insertHorizontal_horizontal, dif_neg (omitVertex_ne _ _), deleteVertex_omitVertex]

lemma insertHorizontal_omit_vertical (t : P202Specs.ShuffleModel.LatticePath p q)
    (j : Fin (p+2)) (k : Fin (p+q+1)) :
    (insertHorizontal t j).vertical (omitVertex (horizontalCut t j) k) = t.vertical k := by
  rw [insertHorizontal_vertical, dif_neg (omitVertex_ne _ _), deleteVertex_omitVertex]

lemma insertHorizontal_uniqueAt (t : P202Specs.ShuffleModel.LatticePath p q) (j : Fin (p+2)) :
    UniqueAt (insertHorizontal t j).horizontal (horizontalCut t j) := by
  intro k hk
  rw [insertHorizontal_at] at hk
  by_cases he : k = horizontalCut t j
  · exact he
  · rw [insertHorizontal_horizontal, dif_neg he] at hk
    exact (Fin.succAbove_ne j _ hk).elim

lemma compressHorizontal_insertHorizontal (t : P202Specs.ShuffleModel.LatticePath p q)
    (j : Fin (p+2)) :
    compressHorizontal (insertHorizontal t j) (horizontalCut t j)
      (insertHorizontal_uniqueAt t j) = t := by
  apply Subtype.ext
  apply Prod.ext
  · apply DFunLike.ext
    intro k
    apply Fin.succAbove_right_injective (p := j)
    have hs := compressHorizontal_skip (insertHorizontal t j) (horizontalCut t j)
      (insertHorizontal_uniqueAt t j) k
    rw [insertHorizontal_at, insertHorizontal_omit_horizontal] at hs
    exact hs
  · apply DFunLike.ext
    intro k
    rw [compressHorizontal_vertical, insertHorizontal_omit_vertical]

lemma cut_unique {N : ℕ} (i j : Fin (N+1))
    (h : ∀ k : Fin N, (k.val < i.val ↔ k.val < j.val)) : i = j := by
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hij
  · have hi : i.val < N := by have := j.isLt; omega
    have hh := h ⟨i.val, hi⟩
    simp only [Fin.val_mk] at hh
    omega
  · have hj : j.val < N := by have := i.isLt; omega
    have hh := h ⟨j.val, hj⟩
    simp only [Fin.val_mk] at hh
    omega

lemma compressHorizontal_threshold (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
    (i : Fin ((p+1)+q+1)) (hi : UniqueAt s.horizontal i) (k : Fin (p+q+1)) :
    k.val < i.val ↔ ((compressHorizontal s i hi).horizontal k).val < (s.horizontal i).val := by
  rw [compressHorizontal_horizontal]
  by_cases hk : k.val < i.val
  · have hlt := uniqueAt_lt s.horizontal i hi (omitVertex i k) ((omitVertex_lt_iff i k).mpr hk)
    simp only [Fin.lt_def] at hlt
    simp only [hk, ite_true, true_iff]
    exact hlt
  · have hgt := uniqueAt_gt s.horizontal i hi (omitVertex i k)
      ((omitVertex_gt_iff i k).mpr (by omega))
    simp only [Fin.lt_def] at hgt
    simp only [hk, ite_false, false_iff, not_lt]
    omega

lemma compressHorizontal_cut (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
    (i : Fin ((p+1)+q+1)) (hi : UniqueAt s.horizontal i) :
    horizontalCut (compressHorizontal s i hi) (s.horizontal i) = i := by
  apply cut_unique
  intro k
  have hh := horizontalCut_spec (compressHorizontal s i hi) (s.horizontal i)
    (Fin.cast (by omega) k)
  have ht := compressHorizontal_threshold s i hi (Fin.cast (by omega) k)
  exact hh.trans ht.symm

lemma insertHorizontal_compressHorizontal (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
    (i : Fin ((p+1)+q+1)) (hi : UniqueAt s.horizontal i) :
    insertHorizontal (compressHorizontal s i hi) (s.horizontal i) = s := by
  apply Subtype.ext
  apply Prod.ext
  · apply DFunLike.ext
    intro k
    rw [insertHorizontal_horizontal]
    split_ifs with hk
    · have he : k = i := hk.trans (compressHorizontal_cut s i hi)
      rw [he]
    · have hki : k ≠ i := by
        intro he; apply hk; rw [he, compressHorizontal_cut]
      simp only [compressHorizontal_cut]
      rw [compressHorizontal_skip, omitVertex_deleteVertex]
  · apply DFunLike.ext
    intro k
    rw [insertHorizontal_vertical]
    split_ifs with hk
    · have he : k = i := hk.trans (compressHorizontal_cut s i hi)
      apply Fin.ext
      simp only [compressHorizontal_cut, Fin.val_mk]
      have hr := s.rank i
      rw [he]
      change i.val - (s.horizontal i).val = (s.vertical i).val
      omega
    · have hki : k ≠ i := by
        intro he; apply hk; rw [he, compressHorizontal_cut]
      simp only [compressHorizontal_cut]
      rw [compressHorizontal_vertical, omitVertex_deleteVertex]

abbrev HorizontalSurvivors (p q : ℕ) :=
  {si : P202Specs.ShuffleModel.LatticePath (p+1) q × Fin ((p+1)+q+1) //
    UniqueAt si.1.horizontal si.2}

/-- Horizontal surviving faces are exactly factor faces times smaller shuffles. -/
def horizontalSurvivorEquiv : HorizontalSurvivors p q ≃
    Fin (p+2) × P202Specs.ShuffleModel.LatticePath p q where
  toFun si := (si.val.1.horizontal si.val.2, compressHorizontal si.val.1 si.val.2 si.property)
  invFun jt := ⟨(insertHorizontal jt.2 jt.1, horizontalCut jt.2 jt.1), insertHorizontal_uniqueAt _ _⟩
  left_inv si := by
    apply Subtype.ext
    apply Prod.ext
    · exact insertHorizontal_compressHorizontal si.val.1 si.val.2 si.property
    · exact compressHorizontal_cut si.val.1 si.val.2 si.property
  right_inv jt := by
    apply Prod.ext
    · exact insertHorizontal_at _ _
    · exact compressHorizontal_insertHorizontal _ _

end LatticePath

lemma compressHorizontal_face {X Y : TopCat.{w}} {p q : ℕ}
    (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
    (i : Fin ((p+1)+q+1)) (hi : LatticePath.UniqueAt s.horizontal i)
    (σ : Simplex X (p+1)) (τ : Simplex Y q) :
    face (Fin.cast (by omega) i)
      (castSimplex (by omega : (p+1)+q = (p+q)+1) (shuffleSimplex s σ τ)) =
    shuffleSimplex (LatticePath.compressHorizontal s i hi) (face (s.horizontal i) σ) τ := by
  rw [face_castSimplex]
  apply (simplexEquiv (productSpace X Y) (p+q)).injective
  apply ContinuousMap.ext
  intro z
  let α : ⦋p+q⦌ ⟶ ⦋(p+1)+q⦌ := SimplexCategory.δ (Fin.cast (by omega) i) ≫
    eqToHom (congrArg SimplexCategory.mk (by omega : (p+q)+1 = (p+1)+q))
  change simplexEquiv (productSpace X Y) ((p+1)+q) (shuffleSimplex s σ τ)
      (z.map α.toOrderHom) =
    simplexEquiv (productSpace X Y) (p+q)
      (shuffleSimplex (LatticePath.compressHorizontal s i hi) (face (s.horizontal i) σ) τ) z
  rw [P202.ShuffleModel.simplex_formula, P202.ShuffleModel.simplex_formula]
  have hf (x : StdSimplex p) :
      simplexEquiv X p (face (s.horizontal i) σ) x =
        simplexEquiv X (p+1) σ (x.map (s.horizontal i).succAbove) := rfl
  rw [hf]
  simp only [← Convexity.StdSimplex.map_comp]
  have hα (k : Fin (p+q+1)) : α.toOrderHom k = LatticePath.omitVertex i k := by
    apply Fin.ext
    simp only [α, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
      Function.comp_apply, SimplexCategory.eqToHom_toOrderHom]
    change ((Fin.cast (by omega) i).succAbove k).val = (LatticePath.omitVertex i k).val
    rw [LatticePath.omitVertex_val]
    simp only [Fin.succAbove, Fin.lt_def, Fin.val_cast, Fin.val_castSucc,
      apply_ite, Fin.val_succ]
    split_ifs <;> rfl
  have hh : s.horizontal ∘ α.toOrderHom =
      (s.horizontal i).succAbove ∘ (LatticePath.compressHorizontal s i hi).horizontal := by
    funext k
    exact (hα k ▸ LatticePath.compressHorizontal_skip s i hi k).symm
  have hv : s.vertical ∘ α.toOrderHom =
      (LatticePath.compressHorizontal s i hi).vertical := by
    funext k
    change s.vertical (α.toOrderHom k) = _
    rw [hα]
    rfl
  rw [hh, hv]


lemma shuffle_left_boundary (R : Type u) [CommRing R]
    {X Y : TopCat.{w}} {p q : ℕ} (σ : Simplex X (p+1)) (τ : Simplex Y q) :
    shuffleComponent R X Y p q
      (boundary R R X p (Finsupp.single σ (1:R)) ⊗ₜ[R] Finsupp.single τ (1:R)) =
      ∑ i : Fin (p+2), (-1 : ℤ)^i.val • shuffleGenerator R (face i σ) τ := by
  rw [P202.SingularChains.boundary_single, TensorProduct.sum_tmul]
  simp only [← TensorProduct.smul_tmul', map_sum, map_zsmul, component_basis]

lemma shuffle_right_boundary (R : Type u) [CommRing R]
    {X Y : TopCat.{w}} {p q : ℕ} (σ : Simplex X p) (τ : Simplex Y (q+1)) :
    shuffleComponent R X Y p q
      (Finsupp.single σ (1:R) ⊗ₜ[R] boundary R R Y q (Finsupp.single τ (1:R))) =
      ∑ i : Fin (q+2), (-1 : ℤ)^i.val • shuffleGenerator R σ (face i τ) := by
  rw [P202.SingularChains.boundary_single, TensorProduct.tmul_sum]
  simp only [TensorProduct.tmul_smul, map_sum, map_zsmul, component_basis]

lemma boundary_generator_surviving (R : Type u) [CommRing R]
    {X Y : TopCat.{w}} {p q n : ℕ} (h : p+q=n+1)
    (σ : Simplex X p) (τ : Simplex Y q) :
    boundary R R (productSpace X Y) n (castChains R h (shuffleGenerator R σ τ)) =
    (∑ s : P202Specs.ShuffleModel.LatticePath p q, ∑ i : Fin (n+2) with
      (∀ a, s.horizontal a = s.horizontal ⟨i.val,by omega⟩ → a=⟨i.val,by omega⟩),
      ((-1 : ℤ)^i.val * s.sign) • Finsupp.single
        (face i (castSimplex h (shuffleSimplex s σ τ))) (1:R)) +
    (∑ s : P202Specs.ShuffleModel.LatticePath p q, ∑ i : Fin (n+2) with
      (∀ a, s.vertical a = s.vertical ⟨i.val,by omega⟩ → a=⟨i.val,by omega⟩),
      ((-1 : ℤ)^i.val * s.sign) • Finsupp.single
        (face i (castSimplex h (shuffleSimplex s σ τ))) (1:R)) := by
  rw [boundary_generator_expansion, signed_faces_partition]


lemma sum_filtered_product_eq {α β A : Type*} [Fintype α] [Fintype β]
    [AddCommMonoid A] (P : α × β → Prop) [DecidablePred P] (f : α → β → A) :
    (∑ a, ∑ b with P (a,b), f a b) =
      ∑ c : {ab : α × β // P ab}, f c.val.1 c.val.2 := by
  classical
  calc
    _ = ∑ ab : α × β with P ab, f ab.1 ab.2 := by
      simp only [Finset.sum_filter]
      exact (Fintype.sum_prod_type' _).symm
    _ = _ := Finset.sum_subtype _ (by simp) _

lemma transpose_shuffleSimplex_cast {X Y : TopCat.{w}} {p q n : ℕ}
    (h : p+q=n) (h' : q+p=n)
    (s : P202Specs.ShuffleModel.LatticePath p q) (σ : Simplex X p) (τ : Simplex Y q) :
    castSimplex h' (shuffleSimplex (LatticePath.transpose s) τ σ) =
      postSimplex (swapMap X Y) n (castSimplex h (shuffleSimplex s σ τ)) := by
  rw [← castSimplex_comp_castSimplex (Nat.add_comm q p) h, transpose_shuffleSimplex,
    castSimplex_postSimplex]

lemma face_postSimplex {X Y : TopCat.{w}} {n : ℕ} (f : X ⟶ Y)
    (i : Fin (n+2)) (σ : Simplex X (n+1)) :
    face i (postSimplex f (n+1) σ) = postSimplex f n (face i σ) := by
  exact (NatTrans.naturality_apply (TopCat.toSSet.map f) (SimplexCategory.δ i).op σ).symm

lemma transpose_shuffleSimplex_face {X Y : TopCat.{w}} {p q n : ℕ}
    (h : p+q=n+1) (h' : q+p=n+1)
    (s : P202Specs.ShuffleModel.LatticePath p q) (σ : Simplex X p) (τ : Simplex Y q)
    (i : Fin (n+2)) :
    face i (castSimplex h' (shuffleSimplex (LatticePath.transpose s) τ σ)) =
      postSimplex (swapMap X Y) n (face i (castSimplex h (shuffleSimplex s σ τ))) := by
  rw [transpose_shuffleSimplex_cast h h', face_postSimplex]



lemma horizontal_survivors_sum {p q : ℕ} {A : Type*} [AddCommMonoid A]
    (f : P202Specs.ShuffleModel.LatticePath (p+1) q → Fin ((p+1)+q+1) → A)
    (g : Fin (p+2) → P202Specs.ShuffleModel.LatticePath p q → A)
    (hf : ∀ s i (hi : LatticePath.UniqueAt s.horizontal i),
      f s i = g (s.horizontal i) (LatticePath.compressHorizontal s i hi)) :
    (∑ s, ∑ i with LatticePath.UniqueAt s.horizontal i, f s i) = ∑ j, ∑ t, g j t := by
  classical
  rw [sum_filtered_product_eq
    (fun si : P202Specs.ShuffleModel.LatticePath (p+1) q × Fin ((p+1)+q+1) =>
      LatticePath.UniqueAt si.1.horizontal si.2) f]
  change (∑ c : LatticePath.HorizontalSurvivors p q, f c.val.1 c.val.2) = _
  trans ∑ c : LatticePath.HorizontalSurvivors p q,
    g (LatticePath.horizontalSurvivorEquiv c).1 (LatticePath.horizontalSurvivorEquiv c).2
  · apply Finset.sum_congr rfl
    intro c _
    exact hf c.val.1 c.val.2 c.property
  · exact (LatticePath.horizontalSurvivorEquiv.sum_comp (fun jt => g jt.1 jt.2)).trans
      (Fintype.sum_prod_type' g)

lemma horizontal_faces_of_compression_sign (R : Type u) [CommRing R]
    {X Y : TopCat.{w}} {p q : ℕ}
    (hsign : ∀ (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
      (i : Fin ((p+1)+q+1)) (hi : LatticePath.UniqueAt s.horizontal i),
      (-1 : ℤ)^i.val * s.sign =
        (-1 : ℤ)^(s.horizontal i).val * (LatticePath.compressHorizontal s i hi).sign)
    (σ : Simplex X (p+1)) (τ : Simplex Y q) :
    (∑ s : P202Specs.ShuffleModel.LatticePath (p+1) q,
      ∑ i : Fin (p+q+2) with LatticePath.UniqueAt s.horizontal ⟨i.val,by omega⟩,
        ((-1 : ℤ)^i.val * s.sign) • Finsupp.single
          (face i (castSimplex (by omega : (p+1)+q=p+q+1) (shuffleSimplex s σ τ))) (1:R)) =
      ∑ a : Fin (p+2), (-1 : ℤ)^a.val • shuffleGenerator R (face a σ) τ := by
  classical
  let F := fun (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
      (i : Fin ((p+1)+q+1)) =>
    ((-1 : ℤ)^i.val * s.sign) • Finsupp.single
      (face (Fin.cast (by omega) i)
        (castSimplex (by omega : (p+1)+q=p+q+1) (shuffleSimplex s σ τ))) (1:R)
  have hraw : (∑ s : P202Specs.ShuffleModel.LatticePath (p+1) q,
      ∑ i : Fin (p+q+2) with LatticePath.UniqueAt s.horizontal ⟨i.val,by omega⟩,
        ((-1 : ℤ)^i.val * s.sign) • Finsupp.single
          (face i (castSimplex (by omega : (p+1)+q=p+q+1) (shuffleSimplex s σ τ))) (1:R)) =
      ∑ s, ∑ i with LatticePath.UniqueAt s.horizontal i, F s i := by
    apply Finset.sum_congr rfl
    intro s _
    simp only [Finset.sum_filter]
    exact (finCongr (by omega : p+q+2=(p+1)+q+1)).sum_comp
      (fun i => if LatticePath.UniqueAt s.horizontal i then F s i else 0)
  rw [hraw]
  trans ∑ a : Fin (p+2), ∑ t : P202Specs.ShuffleModel.LatticePath p q,
    ((-1 : ℤ)^a.val * t.sign) • Finsupp.single (shuffleSimplex t (face a σ) τ) (1:R)
  · apply horizontal_survivors_sum
    intro s i hi
    dsimp only [F]
    rw [hsign s i hi, compressHorizontal_face s i hi σ τ]
  · simp only [shuffleGenerator, Finset.smul_sum, smul_smul]


lemma castSimplex_face {X : TopCat.{w}} {m n : ℕ} (h : m=n)
    (i : Fin (m+2)) (σ : Simplex X (m+1)) :
    castSimplex h (face i σ) =
      face (Fin.cast (congrArg (·+2) h) i) (castSimplex (congrArg (·+1) h) σ) := by
  subst n
  rfl

lemma postSimplex_swapMap_twice (X Y : TopCat.{w}) (n : ℕ)
    (σ : Simplex (productSpace X Y) n) :
    postSimplex (swapMap Y X) n (postSimplex (swapMap X Y) n σ) = σ := by
  apply (simplexEquiv (productSpace X Y) n).injective
  apply ContinuousMap.ext
  intro z
  simp only [postSimplex, P202.SingularChains.simplexEquiv_postcomp,
    ContinuousMap.comp_apply]
  rfl

lemma castChains_chainMap (R : Type u) [CommRing R]
    {X Y : TopCat.{w}} {m n : ℕ} (h : m=n) (f : X ⟶ Y) (c : Chains R X m) :
    castChains R h (((chainMap R R f).f m).hom c) =
      ((chainMap R R f).f n).hom (castChains R h c) := by
  subst n
  rfl

lemma chainMap_swapMap_twice (R : Type u) [CommRing R]
    (X Y : TopCat.{w}) (n : ℕ) (c : Chains R (productSpace X Y) n) :
    ((chainMap R R (swapMap Y X)).f n).hom
      (((chainMap R R (swapMap X Y)).f n).hom c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [map_add, hc, hd]
  | single σ r =>
    rw [P202.SingularChains.chainMap_single, P202.SingularChains.chainMap_single]
    change Finsupp.single (postSimplex (swapMap Y X) n (postSimplex (swapMap X Y) n σ)) r = _
    rw [postSimplex_swapMap_twice]

lemma swap_shuffleGenerator (R : Type u) [CommRing R]
    {X Y : TopCat.{w}} {p q : ℕ} (σ : Simplex X p) (τ : Simplex Y q) :
    castChains R (Nat.add_comm q p)
      (((chainMap R R (swapMap Y X)).f (q+p)).hom (shuffleGenerator R τ σ)) =
      (-1 : ℤ)^(p*q) • shuffleGenerator R σ τ := by
  rw [castChains_chainMap, transpose_shuffleGenerator, map_zsmul, chainMap_swapMap_twice]
lemma transpose_face_swap {X Y : TopCat.{w}} {p q : ℕ}
    (s : P202Specs.ShuffleModel.LatticePath p (q+1)) (σ : Simplex X p)
    (τ : Simplex Y (q+1)) (j : Fin (q+p+2)) :
    castSimplex (Nat.add_comm q p)
      (postSimplex (swapMap Y X) (q+p)
        (face j (castSimplex (by omega : (q+1)+p = (q+p)+1)
          (shuffleSimplex (LatticePath.transpose s) τ σ)))) =
    face (Fin.cast (by omega) j)
      (castSimplex (by omega : p+(q+1)=(p+q)+1) (shuffleSimplex s σ τ)) := by
  rw [castSimplex_postSimplex, castSimplex_face,
    castSimplex_comp_castSimplex]
  rw [transpose_shuffleSimplex_cast (by omega) (by omega), face_postSimplex,
    postSimplex_swapMap_twice]

namespace LatticePath
lemma transpose_unique_horizontal {p q : ℕ}
    (s : P202Specs.ShuffleModel.LatticePath p q) (i : Fin (p+q+1)) :
    (∀ k, (transpose s).horizontal k =
      (transpose s).horizontal (Fin.cast (by omega) i) →
        k = Fin.cast (by omega) i) ↔
    (∀ k, s.vertical k = s.vertical i → k=i) := by
  constructor
  · intro h k hk
    have he := h (Fin.cast (by omega) k) hk
    exact Fin.ext (congrArg (fun a : Fin (q+p+1) => a.val) he)
  · intro h k hk
    have he := h (Fin.cast (by omega) k) hk
    exact Fin.ext (congrArg (fun a : Fin (p+q+1) => a.val) he)
end LatticePath

def horizontalFaceSum (R : Type u) [CommRing R] {X Y : TopCat.{w}} {p q : ℕ}
    (σ : Simplex X (p+1)) (τ : Simplex Y q) : Chains R (productSpace X Y) (p+q) :=
  ∑ s : P202Specs.ShuffleModel.LatticePath (p+1) q,
    ∑ i : Fin (p+q+2) with (∀ k, s.horizontal k =
      s.horizontal (Fin.cast (by omega) i) → k=Fin.cast (by omega) i),
      ((-1 : ℤ)^i.val * s.sign) • Finsupp.single
        (face i (castSimplex (by omega : (p+1)+q=(p+q)+1) (shuffleSimplex s σ τ))) 1

def verticalFaceSum (R : Type u) [CommRing R] {X Y : TopCat.{w}} {p q : ℕ}
    (σ : Simplex X p) (τ : Simplex Y (q+1)) : Chains R (productSpace X Y) (p+q) :=
  ∑ s : P202Specs.ShuffleModel.LatticePath p (q+1),
    ∑ i : Fin (p+q+2) with (∀ k, s.vertical k =
      s.vertical (Fin.cast (by omega) i) → k=Fin.cast (by omega) i),
      ((-1 : ℤ)^i.val * s.sign) • Finsupp.single
        (face i (castSimplex (by omega : p+(q+1)=(p+q)+1) (shuffleSimplex s σ τ))) 1

lemma swap_horizontalFaceSum (R : Type u) [CommRing R]
    {X Y : TopCat.{w}} {p q : ℕ} (σ : Simplex X p) (τ : Simplex Y (q+1)) :
    castChains R (Nat.add_comm q p)
      (((chainMap R R (swapMap Y X)).f (q+p)).hom (horizontalFaceSum R τ σ)) =
      (-1 : ℤ)^(p*(q+1)) • verticalFaceSum R σ τ := by
  classical
  simp only [horizontalFaceSum, verticalFaceSum, map_sum, Finset.sum_filter,
    apply_ite, map_zero, map_zsmul, Finset.smul_sum, smul_ite, smul_zero]
  rw [← (LatticePath.transposeEquiv p (q+1)).sum_comp]
  apply Finset.sum_congr rfl
  intro s _
  rw [← (finCongr (congrArg (·+2) (Nat.add_comm p q))).sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  have hcond := LatticePath.transpose_unique_horizontal s (Fin.cast (by omega) i)
  simp only [LatticePath.transposeEquiv, Equiv.coe_fn_mk, finCongr_apply,
    Fin.cast_cast] at hcond ⊢
  simp only [hcond]
  split_ifs
  · rw [P202.SingularChains.chainMap_single, castChains_single]
    have hf := transpose_face_swap s σ τ (Fin.cast (congrArg (·+2) (Nat.add_comm p q)) i)
    simp only [postSimplex] at hf
    rw [hf, LatticePath.transpose_sign]
    simp only [Fin.val_cast, smul_smul, Fin.cast_cast, Fin.cast_eq_self]
    congr 1
    ring
  · rfl


lemma verticalFaceSum_of_horizontal (R : Type u) [CommRing R]
    {X Y : TopCat.{w}} {p q : ℕ} (σ : Simplex X p) (τ : Simplex Y (q+1))
    (hH : horizontalFaceSum R τ σ =
      ∑ b : Fin (q+2), (-1 : ℤ)^b.val • shuffleGenerator R (face b τ) σ) :
    verticalFaceSum R σ τ = (-1 : ℤ)^p •
      ∑ b : Fin (q+2), (-1 : ℤ)^b.val • shuffleGenerator R σ (face b τ) := by
  have hswap := swap_horizontalFaceSum R σ τ
  rw [hH] at hswap
  have hright :
      castChains R (Nat.add_comm q p)
        (((chainMap R R (swapMap Y X)).f (q+p)).hom
          (∑ b : Fin (q+2), (-1 : ℤ)^b.val • shuffleGenerator R (face b τ) σ)) =
      (-1 : ℤ)^(p*q) •
        ∑ b : Fin (q+2), (-1 : ℤ)^b.val • shuffleGenerator R σ (face b τ) := by
    simp only [map_sum, map_zsmul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [swap_shuffleGenerator, smul_comm]
  rw [hright] at hswap
  have haa : (-1 : ℤ)^(p*(q+1)) * (-1)^(p*(q+1)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hab : (-1 : ℤ)^(p*(q+1)) * (-1)^(p*q) = (-1)^p := by
    rw [← pow_add, show p*(q+1)+p*q = p+2*(p*q) by ring, pow_add, pow_mul]
    norm_num
  have hh := congrArg (fun c : Chains R (productSpace X Y) (p+q) =>
    (-1 : ℤ)^(p*(q+1)) • c) hswap
  simp only [smul_smul, haa, hab, one_smul] at hh
  exact hh.symm



lemma horizontal_faces_at_degree (R : Type u) [CommRing R]
    {X Y : TopCat.{w}} {p q n : ℕ} (h : p+q=n)
    (σ : Simplex X (p+1)) (τ : Simplex Y q) :
    (∑ s : P202Specs.ShuffleModel.LatticePath (p+1) q, ∑ i : Fin (n+2) with
      (∀ a, s.horizontal a = s.horizontal ⟨i.val,by omega⟩ → a=⟨i.val,by omega⟩),
      ((-1 : ℤ)^i.val * s.sign) • Finsupp.single
        (face i (castSimplex (by omega : (p+1)+q=n+1) (shuffleSimplex s σ τ))) (1:R)) =
      castChains R h (horizontalFaceSum R σ τ) := by
  subst n
  rfl

lemma vertical_faces_at_degree (R : Type u) [CommRing R]
    {X Y : TopCat.{w}} {p q n : ℕ} (h : p+q=n)
    (σ : Simplex X p) (τ : Simplex Y (q+1)) :
    (∑ s : P202Specs.ShuffleModel.LatticePath p (q+1), ∑ i : Fin (n+2) with
      (∀ a, s.vertical a = s.vertical ⟨i.val,by omega⟩ → a=⟨i.val,by omega⟩),
      ((-1 : ℤ)^i.val * s.sign) • Finsupp.single
        (face i (castSimplex (by omega : p+(q+1)=n+1) (shuffleSimplex s σ τ))) (1:R)) =
      castChains R h (verticalFaceSum R σ τ) := by
  subst n
  rfl

lemma chain_identity_of_horizontal_formulas (R : Type u) [CommRing R]
    (X Y : TopCat.{w})
    (hH : ∀ (p q : ℕ) (σ : Simplex X (p+1)) (τ : Simplex Y q),
      horizontalFaceSum R σ τ = ∑ a : Fin (p+2), (-1 : ℤ)^a.val • shuffleGenerator R (face a σ) τ)
    (hHswap : ∀ (p q : ℕ) (τ : Simplex Y (p+1)) (σ : Simplex X q),
      horizontalFaceSum R τ σ = ∑ a : Fin (p+2), (-1 : ℤ)^a.val • shuffleGenerator R (face a τ) σ) :
    ∀ n, (boundary R R (productSpace X Y) n).comp (shuffle R X Y (n+1)) =
      (shuffle R X Y n).comp (totalBoundary R X Y n) := by
  apply (chain_identity_iff_positive_generators R X Y).mpr
  intro p q σ τ
  have hleft : horizontalFaceSum R σ τ =
      shuffleComponent R X Y p (q+1)
        (boundary R R X p (Finsupp.single σ (1:R)) ⊗ₜ[R] Finsupp.single τ (1:R)) := by
    rw [hH p (q+1) σ τ, shuffle_left_boundary]
  have hright : verticalFaceSum R σ τ = (-1 : ℤ)^(p+1) •
      shuffleComponent R X Y (p+1) q
        (Finsupp.single σ (1:R) ⊗ₜ[R] boundary R R Y q (Finsupp.single τ (1:R))) := by
    rw [verticalFaceSum_of_horizontal R σ τ (hHswap q (p+1) τ σ), shuffle_right_boundary]
  rw [boundary_generator_surviving,
    horizontal_faces_at_degree R (by omega : p+(q+1)=p+q+1),
    vertical_faces_at_degree R (by omega : (p+1)+q=p+q+1), hleft, hright, map_zsmul]

lemma chain_identity_of_compression_sign (R : Type u) [CommRing R]
    (X Y : TopCat.{w})
    (hsign : ∀ {p q : ℕ} (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
      (i : Fin ((p+1)+q+1)) (hi : LatticePath.UniqueAt s.horizontal i),
      (-1 : ℤ)^i.val * s.sign =
        (-1 : ℤ)^(s.horizontal i).val * (LatticePath.compressHorizontal s i hi).sign) :
    ∀ n, (boundary R R (productSpace X Y) n).comp (shuffle R X Y (n+1)) =
      (shuffle R X Y n).comp (totalBoundary R X Y n) := by
  apply chain_identity_of_horizontal_formulas R X Y
  · intro p q σ τ
    exact horizontal_faces_of_compression_sign R hsign σ τ
  · intro p q τ σ
    exact horizontal_faces_of_compression_sign R hsign τ σ


namespace LatticePath
open P202Specs.ShuffleModel
variable {p q : ℕ}

lemma uniqueHorizontal_next (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
    (i : Fin ((p+1)+q+1)) (hi : UniqueAt s.horizontal i)
    (hn : i.val < (p+1)+q) :
    (s.horizontal ⟨i.val+1,by omega⟩).val = (s.horizontal i).val+1 ∧
      s.vertical ⟨i.val+1,by omega⟩ = s.vertical i := by
  let k : Fin ((p+1)+q) := ⟨i.val,hn⟩
  have hk : k.castSucc=i := Fin.ext rfl
  rcases s.step k with hs | hs
  · simpa only [hk,k,Fin.succ_mk,Fin.castSucc_mk] using hs
  · have he := hi k.succ (by simpa only [hk,k,Fin.succ_mk,Fin.castSucc_mk] using hs.1)
    have := congrArg Fin.val he
    dsimp [k] at this
    omega

lemma uniqueHorizontal_prev (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
    (i : Fin ((p+1)+q+1)) (hi : UniqueAt s.horizontal i)
    (hn : 0 < i.val) :
    (s.horizontal i).val = (s.horizontal ⟨i.val-1,by omega⟩).val+1 ∧
      s.vertical i = s.vertical ⟨i.val-1,by omega⟩ := by
  let k : Fin ((p+1)+q) := ⟨i.val-1,by have := i.isLt; omega⟩
  have hk : k.succ=i := Fin.ext (by dsimp [k]; omega)
  rcases s.step k with hs | hs
  · simpa only [hk,k,Fin.succ_mk,Fin.castSucc_mk] using hs
  · have he := hi k.castSucc (by simpa only [hk,k,Fin.succ_mk,Fin.castSucc_mk] using hs.1.symm)
    have := congrArg Fin.val he
    dsimp [k] at this
    omega

lemma compressHorizontal_stepLabel_nonterminal
    (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
    (i : Fin ((p+1)+q+1)) (hi : UniqueAt s.horizontal i)
    (hn : i.val < (p+1)+q) (a : Fin (p+q)) :
    (s.stepLabel ⟨if a.val < i.val then a.val else a.val+1,by have := a.isLt; split_ifs <;> omega⟩).val =
      if ((compressHorizontal s i hi).stepLabel a).val < (s.horizontal i).val
      then ((compressHorizontal s i hi).stepLabel a).val
      else ((compressHorizontal s i hi).stepLabel a).val+1 := by
  let A : Fin ((p+1)+q+1) := ⟨a.val,by have := a.isLt; omega⟩
  let B : Fin ((p+1)+q+1) := ⟨a.val+1,by have := a.isLt; omega⟩
  let C : Fin ((p+1)+q+1) := ⟨a.val+2,by have := a.isLt; omega⟩
  have hsA := s.step (⟨a.val,by have := a.isLt; omega⟩ : Fin ((p+1)+q))
  have hsB := s.step (⟨a.val+1,by have := a.isLt; omega⟩ : Fin ((p+1)+q))
  have hA : ∀ h : a.val < i.val, (s.horizontal A).val < (s.horizontal i).val := by
    intro h
    exact uniqueAt_lt s.horizontal i hi A h
  have hB₁ : ∀ h : a.val+1 < i.val, (s.horizontal B).val < (s.horizontal i).val := by
    intro h
    exact uniqueAt_lt s.horizontal i hi B h
  have hB₂ : ∀ h : i.val < a.val+1, (s.horizontal i).val < (s.horizontal B).val := by
    intro h
    exact uniqueAt_gt s.horizontal i hi B h
  have hC : ∀ h : i.val < a.val+2, (s.horizontal i).val < (s.horizontal C).val := by
    intro h
    exact uniqueAt_gt s.horizontal i hi C h
  have hBi : a.val+1=i.val → s.horizontal B=s.horizontal i := by
    intro h; congr 1; exact Fin.ext h
  have hj := (s.horizontal i).isLt
  have hlast := uniqueHorizontal_next s i hi hn
  have hjp : (s.horizontal i).val ≤ p := by
    have ht := (s.horizontal ⟨i.val+1,by omega⟩).isLt
    omega
  have hOa : omitVertex i a.castSucc = (if a.val < i.val then A else B) := by
    apply Fin.ext
    rw [omitVertex_val]
    simp only [Fin.val_castSucc]
    split_ifs <;> rfl
  have hOb : omitVertex i a.succ = (if a.val+1 < i.val then B else C) := by
    apply Fin.ext
    rw [omitVertex_val]
    simp only [Fin.val_succ]
    split_ifs <;> rfl
  by_cases ha : a.val < i.val
  · by_cases hb : a.val+1 < i.val
    · have hAl := hA ha
      simp only [stepLabel_val,compressHorizontal_horizontal,compressHorizontal_vertical,
        Fin.val_castSucc,Fin.val_succ,hOa,hOb,ha,hb,ite_true,ite_false,
        Fin.succ_mk,Fin.castSucc_mk]
      change (if (s.horizontal B).val=(s.horizontal A).val+1 then
        (s.horizontal A).val else p+1+(s.vertical A).val) =
        if (if (s.horizontal B).val=(s.horizontal A).val+1 then
          (s.horizontal A).val else p+(s.vertical A).val) < (s.horizontal i).val
        then (if (s.horizontal B).val=(s.horizontal A).val+1 then
          (s.horizontal A).val else p+(s.vertical A).val)
        else (if (s.horizontal B).val=(s.horizontal A).val+1 then
          (s.horizontal A).val else p+(s.vertical A).val)+1
      by_cases hstep : (s.horizontal B).val=(s.horizontal A).val+1
      · simp only [hstep,ite_true]
        split_ifs <;> omega
      · simp only [hstep,ite_false]
        split_ifs <;> omega
    · have he : a.val+1=i.val := by omega
      have hBi' : B=i := Fin.ext he
      have hAi : A=(⟨i.val-1,by omega⟩ : Fin ((p+1)+q+1)) :=
        Fin.ext (by dsimp [A]; omega)
      have hCi : C=(⟨i.val+1,by omega⟩ : Fin ((p+1)+q+1)) :=
        Fin.ext (by dsimp [C]; omega)
      have hinc := (uniqueHorizontal_prev s i hi (by omega)).1
      have hout := (uniqueHorizontal_next s i hi hn).1
      rw [← hAi] at hinc
      rw [← hCi] at hout
      have hAl := hA ha
      simp only [stepLabel_val,compressHorizontal_horizontal,compressHorizontal_vertical,
        Fin.val_castSucc,Fin.val_succ,hOa,hOb,ha,hb,ite_true,ite_false,
        Fin.succ_mk,Fin.castSucc_mk]
      change (if (s.horizontal B).val=(s.horizontal A).val+1 then
        (s.horizontal A).val else p+1+(s.vertical A).val) =
        if (if (s.horizontal C).val-1=(s.horizontal A).val+1 then
          (s.horizontal A).val else p+(s.vertical A).val) < (s.horizontal i).val
        then (if (s.horizontal C).val-1=(s.horizontal A).val+1 then
          (s.horizontal A).val else p+(s.vertical A).val)
        else (if (s.horizontal C).val-1=(s.horizontal A).val+1 then
          (s.horizontal A).val else p+(s.vertical A).val)+1
      have h₁ : (s.horizontal B).val=(s.horizontal A).val+1 := by rw [hBi']; exact hinc
      have h₂ : (s.horizontal C).val-1=(s.horizontal A).val+1 := by omega
      simp only [h₁,h₂,ite_true]
      split_ifs <;> omega
  · have hb : ¬ a.val+1 < i.val := by omega
    have hBl := hB₂ (by omega)
    simp only [stepLabel_val,compressHorizontal_horizontal,compressHorizontal_vertical,
      Fin.val_castSucc,Fin.val_succ,hOa,hOb,ha,hb,ite_true,ite_false,
      Fin.succ_mk,Fin.castSucc_mk,Nat.add_assoc,Nat.reduceAdd]
    change (if (s.horizontal C).val=(s.horizontal B).val+1 then
      (s.horizontal B).val else p+(1+(s.vertical B).val)) =
      if (if (s.horizontal C).val-1=(s.horizontal B).val-1+1 then
        (s.horizontal B).val-1 else p+(s.vertical B).val) < (s.horizontal i).val
      then (if (s.horizontal C).val-1=(s.horizontal B).val-1+1 then
        (s.horizontal B).val-1 else p+(s.vertical B).val)
      else (if (s.horizontal C).val-1=(s.horizontal B).val-1+1 then
        (s.horizontal B).val-1 else p+(s.vertical B).val)+1
    change ((s.horizontal C).val = (s.horizontal B).val+1 ∧ s.vertical C=s.vertical B) ∨
      (s.horizontal C=s.horizontal B ∧ (s.vertical C).val=(s.vertical B).val+1) at hsB
    rcases hsB with hsB | hsB
    · have hcomp : (s.horizontal C).val-1=(s.horizontal B).val-1+1 := by omega
      simp only [hsB.1,hcomp,ite_true]
      split_ifs <;> omega
    · have hconst := congrArg Fin.val hsB.1
      have hn₁ : ¬ (s.horizontal C).val=(s.horizontal B).val+1 := by omega
      have hn₂ : ¬ (s.horizontal C).val-1=(s.horizontal B).val-1+1 := by omega
      simp only [hn₁,hn₂,ite_false]
      split_ifs <;> omega

lemma succAbove_val_if {N : ℕ} (j : Fin (N+1)) (a : Fin N) :
    (j.succAbove a).val = if a.val < j.val then a.val else a.val+1 := by
  unfold Fin.succAbove
  split_ifs <;> simp only [Fin.lt_def,Fin.val_castSucc,Fin.val_succ] at * <;> omega

lemma compressHorizontal_sign_nonterminal
    (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
    (i : Fin ((p+1)+q+1)) (hi : UniqueAt s.horizontal i)
    (hn : i.val < (p+1)+q) :
    (-1 : ℤ)^i.val * s.sign = (-1 : ℤ)^(s.horizontal i).val *
      (compressHorizontal s i hi).sign := by
  let e : Fin ((p+1)+q) ≃ Fin (p+q+1) := finCongr (by omega)
  let σ : Equiv.Perm (Fin (p+q+1)) := e.permCongr s.permutation
  let τ := (compressHorizontal s i hi).permutation
  let r : Fin (p+q+1) := ⟨i.val,by omega⟩
  have hjp : (s.horizontal i).val ≤ p := by
    have hn' := (uniqueHorizontal_next s i hi hn).1
    have ht := (s.horizontal ⟨i.val+1,by omega⟩).isLt
    omega
  let j : Fin (p+q+1) := ⟨(s.horizontal i).val,by omega⟩
  have hσr : σ r=j := by
    apply Fin.ext
    change (s.stepLabel (e.symm r)).val = (s.horizontal i).val
    have he : e.symm r = (⟨i.val,hn⟩ : Fin ((p+1)+q)) := Fin.ext rfl
    rw [he,stepLabel_val]
    have hnext := (uniqueHorizontal_next s i hi hn).1
    have hnext' : (s.horizontal (⟨i.val,hn⟩ : Fin ((p+1)+q)).succ).val =
        (s.horizontal (⟨i.val,hn⟩ : Fin ((p+1)+q)).castSucc).val+1 := hnext
    simp only [hnext',ite_true]
    rfl
  have hrest : ∀ a, σ (r.succAbove a) = j.succAbove (τ a) := by
    intro a
    apply Fin.ext
    change (s.stepLabel (e.symm (r.succAbove a))).val = (j.succAbove (τ a)).val
    have hpos : e.symm (r.succAbove a) =
        (⟨if a.val < i.val then a.val else a.val+1,by have := a.isLt; split_ifs <;> omega⟩ : Fin ((p+1)+q)) := by
      apply Fin.ext
      change (r.succAbove a).val = if a.val < i.val then a.val else a.val+1
      rw [succAbove_val_if]
    rw [hpos]
    have hz := compressHorizontal_stepLabel_nonterminal s i hi hn a
    change (s.stepLabel _).val = (j.succAbove ((compressHorizontal s i hi).stepLabel a)).val
    rw [hz]
    rw [succAbove_val_if]
  have hz := sign_delete_boundary σ τ r j hσr hrest
  simpa only [σ,τ,r,j,P202Specs.ShuffleModel.LatticePath.sign,
    Equiv.Perm.sign_permCongr] using hz


end LatticePath

namespace LatticePath
open P202Specs.ShuffleModel
variable {p q : ℕ}

lemma compressHorizontal_terminal_horizontal
    (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
    (i : Fin ((p+1)+q+1)) (hi : UniqueAt s.horizontal i)
    (hn : i.val = (p+1)+q) (k : Fin (p+q+1)) :
    ((compressHorizontal s i hi).horizontal k).val =
      (s.horizontal ⟨k.val, by have := k.isLt; omega⟩).val := by
  rw [compressHorizontal_horizontal, if_pos (by have := k.isLt; omega)]
  have he : omitVertex i k = (⟨k.val, by have := k.isLt; omega⟩ : Fin ((p+1)+q+1)) := by
    apply Fin.ext
    rw [omitVertex_val, if_pos (by have := k.isLt; omega)]
  rw [he]

lemma compressHorizontal_terminal_vertical
    (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
    (i : Fin ((p+1)+q+1)) (hi : UniqueAt s.horizontal i)
    (hn : i.val = (p+1)+q) (k : Fin (p+q+1)) :
    (compressHorizontal s i hi).vertical k =
      s.vertical ⟨k.val, by have := k.isLt; omega⟩ := by
  rw [compressHorizontal_vertical]
  congr 1
  apply Fin.ext
  rw [omitVertex_val, if_pos (by have := k.isLt; omega)]

lemma compressHorizontal_stepLabel_terminal
    (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
    (i : Fin ((p+1)+q+1)) (hi : UniqueAt s.horizontal i)
    (hn : i.val = (p+1)+q) (a : Fin (p+q)) :
    (s.stepLabel ⟨a.val,by have := a.isLt; omega⟩).val =
      if ((compressHorizontal s i hi).stepLabel a).val < p
      then ((compressHorizontal s i hi).stepLabel a).val
      else ((compressHorizontal s i hi).stepLabel a).val+1 := by
  have ht := ((compressHorizontal s i hi).horizontal a.succ).isLt
  rw [compressHorizontal_terminal_horizontal s i hi hn] at ht
  simp only [Fin.val_succ, Fin.val_castSucc] at ht
  simp only [stepLabel_val, compressHorizontal_terminal_horizontal s i hi hn,
    compressHorizontal_terminal_vertical s i hi hn, Fin.val_castSucc, Fin.val_succ,
    Fin.succ_mk, Fin.castSucc_mk]
  split_ifs <;> omega

lemma terminal_horizontal (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
    (i : Fin ((p+1)+q+1)) (hn : i.val = (p+1)+q) :
    (s.horizontal i).val = p+1 := by
  have he : i = Fin.last ((p+1)+q) := Fin.ext hn
  rw [he, (P202.ShuffleModel.path_terminal s).1]
  rfl

lemma terminal_horizontal_stepLabel
    (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
    (i : Fin ((p+1)+q+1)) (hi : UniqueAt s.horizontal i)
    (hn : i.val = (p+1)+q) :
    (s.stepLabel ⟨p+q, by omega⟩).val = p := by
  let a : Fin ((p+1)+q) := ⟨p+q, by omega⟩
  have ha : a.succ = i := Fin.ext (by simp only [a, Fin.val_succ, Fin.val_mk]; omega)
  have hs := s.step a
  have hx := terminal_horizontal s i hn
  rcases hs with hs | hs
  · have hlabel : (s.stepLabel a).val = (s.horizontal a.castSucc).val := by
      rw [stepLabel_val, if_pos hs.1]
    change (s.stepLabel a).val = p
    rw [hlabel]
    rw [ha] at hs
    omega
  · have he := hi a.castSucc (by rw [← ha]; exact hs.1.symm)
    have heval := congrArg Fin.val he
    simp only [a, Fin.val_castSucc, Fin.val_mk] at heval
    omega

lemma compressHorizontal_sign_terminal
    (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
    (i : Fin ((p+1)+q+1)) (hi : UniqueAt s.horizontal i)
    (hn : i.val = (p+1)+q) :
    (-1 : ℤ)^i.val * s.sign =
      (-1 : ℤ)^(s.horizontal i).val * (compressHorizontal s i hi).sign := by
  let e : Fin ((p+1)+q) ≃ Fin (p+q+1) := finCongr (by omega)
  let σ : Equiv.Perm (Fin (p+q+1)) := e.permCongr s.permutation
  let τ := (compressHorizontal s i hi).permutation
  let a : Fin (p+q+1) := Fin.last (p+q)
  let b : Fin (p+q+1) := ⟨p, by omega⟩
  have hσ (k : Fin (p+q+1)) : (σ k).val =
      (s.stepLabel ⟨k.val, by have := k.isLt; omega⟩).val := by
    rfl
  have hab : σ a = b := by
    apply Fin.ext
    rw [hσ]
    exact terminal_horizontal_stepLabel s i hi hn
  have hrest (k : Fin (p+q)) : σ (a.succAbove k) = b.succAbove (τ k) := by
    apply Fin.ext
    rw [hσ]
    have hav : (a.succAbove k).val = k.val := by
      simp only [a, Fin.succAbove_last, Fin.val_castSucc]
    have he : (⟨(a.succAbove k).val, by have := (a.succAbove k).isLt; omega⟩ : Fin ((p+1)+q)) =
        ⟨k.val, by have := k.isLt; omega⟩ := Fin.ext hav
    rw [he]
    have hlabels := compressHorizontal_stepLabel_terminal s i hi hn k
    change (s.stepLabel ⟨k.val, _⟩).val =
      (b.succAbove ((compressHorizontal s i hi).stepLabel k)).val
    simp only [Fin.succAbove, apply_ite, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
    simpa only [b, Fin.val_mk, apply_ite] using hlabels
  have hs := P202.ShuffleBoundary.sign_delete_boundary σ τ a b hab hrest
  have hsign : (Equiv.Perm.sign σ : ℤ) = s.sign := by
    change ((Equiv.Perm.sign (e.permCongr s.permutation) : ℤˣ) : ℤ) = _
    rw [Equiv.Perm.sign_permCongr]
    rfl
  rw [hsign] at hs
  change (-1 : ℤ)^(p+q) * s.sign = (-1 : ℤ)^p * (compressHorizontal s i hi).sign at hs
  rw [hn, terminal_horizontal s i hn]
  have he : (p+1)+q = (p+q)+1 := by omega
  rw [he, pow_succ, pow_succ]
  calc
    (-1 : ℤ)^(p+q) * (-1) * s.sign = -((-1 : ℤ)^(p+q) * s.sign) := by ring
    _ = -((-1 : ℤ)^p * (compressHorizontal s i hi).sign) := by rw [hs]
    _ = (-1 : ℤ)^p * (-1) * (compressHorizontal s i hi).sign := by ring


end LatticePath


namespace LatticePath
lemma compressHorizontal_boundary_sign {p q : ℕ}
    (s : P202Specs.ShuffleModel.LatticePath (p+1) q)
    (i : Fin ((p+1)+q+1)) (hi : UniqueAt s.horizontal i) :
    (-1 : ℤ)^i.val * s.sign = (-1 : ℤ)^(s.horizontal i).val *
      (compressHorizontal s i hi).sign := by
  by_cases hn : i.val < (p+1)+q
  · exact compressHorizontal_sign_nonterminal s i hi hn
  · exact compressHorizontal_sign_terminal s i hi (by have := i.isLt; omega)
end LatticePath

/-- The actual finite signed lattice-path shuffle commutes with the ordinary
singular and total tensor differentials in every nonnegative degree. -/
theorem chain_identity (R : Type u) [CommRing R] (X Y : TopCat.{w}) (n : ℕ) :
    (boundary R R (productSpace X Y) n).comp (shuffle R X Y (n+1)) =
      (shuffle R X Y n).comp (totalBoundary R X Y n) :=
  chain_identity_of_compression_sign R X Y LatticePath.compressHorizontal_boundary_sign n

/-- The prescribed graded maps are a genuine chain map on the accepted complexes. -/
theorem chain_map_realization (R : Type u) [CommRing R] (X Y : TopCat.{w}) :
    ∃ F : tensorComplex R X Y ⟶ complex R R (productSpace X Y),
      ∀ n, F.f n = ModuleCat.ofHom (shuffle R X Y n) :=
  (chain_map_realization_iff R X Y).mpr (chain_identity R X Y)

end P202.ShuffleBoundary
