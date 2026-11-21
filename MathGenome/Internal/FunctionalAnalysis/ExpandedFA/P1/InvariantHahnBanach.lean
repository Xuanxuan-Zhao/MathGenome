import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05RealHahnBanach
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.InvariantHahnBanach
import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Agnew–Morse invariant Hahn–Banach, `paper.tex:5282–5314`.
We close the commuting semigroup under identity, composition, and convex
combinations. The infimum of the resulting bounds is sublinear. Cesàro
averages force that bound to be nonpositive on every difference `x - S x`.
Ordinary algebraic Hahn–Banach then gives the required invariant extension. -/

universe u

namespace ExpandedFA.P1
namespace InvariantHB

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Operators built by adjoining identity, products, and convex averages. -/
inductive Averaging (S : Set (Module.End ℝ E)) : Module.End ℝ E → Prop
  | one : Averaging S 1
  | basic {A} : A ∈ S → Averaging S A
  | mul {A B} : Averaging S A → Averaging S B → Averaging S (A * B)
  | convex {A B} (a b : ℝ) : Averaging S A → Averaging S B →
      0 ≤ a → 0 ≤ b → a + b = 1 → Averaging S (a • A + b • B)

variable {S : Set (Module.End ℝ E)}

lemma averaging_commute_generator
    (hcomm : ∀ A ∈ S, ∀ B ∈ S, Commute A B)
    {A : Module.End ℝ E} (hA : Averaging S A) {B} (hB : B ∈ S) : Commute A B := by
  induction hA with
  | one => exact Commute.one_left B
  | basic hA => exact hcomm _ hA _ hB
  | mul _ _ ihA ihB => exact ihA.mul_left ihB
  | convex a b _ _ _ _ _ ihA ihB => exact (ihA.smul_left a).add_left (ihB.smul_left b)

lemma averaging_commute
    (hcomm : ∀ A ∈ S, ∀ B ∈ S, Commute A B)
    {A B : Module.End ℝ E} (hA : Averaging S A) (hB : Averaging S B) : Commute A B := by
  induction hB with
  | one => exact Commute.one_right A
  | basic hB => exact averaging_commute_generator hcomm hA hB
  | mul _ _ ihA ihB => exact ihA.mul_right ihB
  | convex a b _ _ _ _ _ ihA ihB => exact (ihA.smul_right a).add_right (ihB.smul_right b)

lemma averaging_contract {p : E → ℝ} (hp : IsSublinear p)
    (hcontract : ∀ A ∈ S, ∀ x, p (A x) ≤ p x)
    {A : Module.End ℝ E} (hA : Averaging S A) (x : E) : p (A x) ≤ p x := by
  induction hA generalizing x with
  | one => exact le_rfl
  | basic hA => exact hcontract _ hA x
  | mul hA hB ihA ihB => exact (ihA _).trans (ihB _)
  | @convex A B a b hA hB ha hb hab ihA ihB =>
    change p (a • A x + b • B x) ≤ p x
    calc
      _ ≤ p (a • _) + p (b • _) := hp.1 _ _
      _ = a * p (A x) + b * p (B x) := by rw [hp.2 a ha, hp.2 b hb]
      _ ≤ a * p x + b * p x := add_le_add (mul_le_mul_of_nonneg_left (ihA x) ha)
        (mul_le_mul_of_nonneg_left (ihB x) hb)
      _ = p x := by rw [← add_mul, hab, one_mul]

lemma averaging_preserve (Y : Submodule ℝ E) (f : Y →ₗ[ℝ] ℝ)
    (hY : ∀ A ∈ S, ∀ y ∈ Y, A y ∈ Y)
    (hf : ∀ (A : Module.End ℝ E) (hA : A ∈ S) (y : Y),
      f ⟨A y, hY A hA y y.property⟩ = f y)
    {A : Module.End ℝ E} (hA : Averaging S A) :
    ∀ y : Y, ∃ z : Y, A y = (z : E) ∧ f z = f y := by
  induction hA with
  | one => intro y; exact ⟨y, rfl, rfl⟩
  | basic hA => intro y; exact ⟨⟨_, hY _ hA y y.property⟩, rfl, hf _ hA y⟩
  | @mul A B hA hB ihA ihB =>
    intro y
    obtain ⟨z, hz, hfz⟩ := ihB y
    obtain ⟨w, hw, hfw⟩ := ihA z
    exact ⟨w, by change A (B y) = _; rw [hz, hw], hfw.trans hfz⟩
  | @convex A B a b hA hB ha hb hab ihA ihB =>
    intro y
    obtain ⟨z, hz, hfz⟩ := ihA y
    obtain ⟨w, hw, hfw⟩ := ihB y
    refine ⟨a • z + b • w, ?_, ?_⟩
    · change a • A y + b • B y = a • (z : E) + b • (w : E)
      rw [hz, hw]
    · simp only [map_add, map_smul, smul_eq_mul, hfz, hfw, ← add_mul, hab, one_mul]

instance averaging_nonempty : Nonempty {A // Averaging S A} := ⟨⟨1, .one⟩⟩

/-- The infimum of the averaged sublinear bounds. -/
noncomputable def envelope (S : Set (Module.End ℝ E)) (p : E → ℝ) (x : E) : ℝ :=
  ⨅ A : {A // Averaging S A}, p (A.1 x)

lemma envelope_bdd {p : E → ℝ} (hp : IsSublinear p)
    (hcontract : ∀ A ∈ S, ∀ x, p (A x) ≤ p x) (x : E) :
    BddBelow (Set.range fun A : {A // Averaging S A} => p (A.1 x)) := by
  refine ⟨-p (-x), ?_⟩
  rintro _ ⟨A, rfl⟩
  have h := averaging_contract hp hcontract A.2 (-x)
  rw [map_neg] at h
  exact (neg_le_neg h).trans (hp.neg_le (A.1 x))

lemma envelope_le {p : E → ℝ} (hp : IsSublinear p)
    (hcontract : ∀ A ∈ S, ∀ x, p (A x) ≤ p x)
    {A : Module.End ℝ E} (hA : Averaging S A) (x : E) : envelope S p x ≤ p (A x) :=
  ciInf_le (envelope_bdd hp hcontract x) ⟨A, hA⟩

lemma envelope_le_self {p : E → ℝ} (hp : IsSublinear p)
    (hcontract : ∀ A ∈ S, ∀ x, p (A x) ≤ p x) (x : E) : envelope S p x ≤ p x :=
  envelope_le hp hcontract Averaging.one x

lemma envelope_sublinear {p : E → ℝ} (hp : IsSublinear p)
    (hcomm : ∀ A ∈ S, ∀ B ∈ S, Commute A B)
    (hcontract : ∀ A ∈ S, ∀ x, p (A x) ≤ p x) : IsSublinear (envelope S p) := by
  constructor
  · intro x y
    have h (A B : {A // Averaging S A}) :
        envelope S p (x + y) ≤ p (A.1 x) + p (B.1 y) := by
      calc
        _ ≤ p ((A.1 * B.1) (x + y)) := envelope_le hp hcontract (.mul A.2 B.2) _
        _ ≤ p ((A.1 * B.1) x) + p ((A.1 * B.1) y) := by
          rw [map_add]; exact hp.1 _ _
        _ = p (B.1 (A.1 x)) + p (A.1 (B.1 y)) := by
          exact congrArg (fun T : Module.End ℝ E => p (T x) + p (A.1 (B.1 y)))
            (averaging_commute hcomm A.2 B.2).eq
        _ ≤ p (A.1 x) + p (B.1 y) :=
          add_le_add (averaging_contract hp hcontract B.2 _) (averaging_contract hp hcontract A.2 _)
    have h' (A : {A // Averaging S A}) :
        envelope S p (x + y) - p (A.1 x) ≤ envelope S p y := by
      exact le_ciInf fun B => by linarith [h A B]
    have : envelope S p (x + y) - envelope S p y ≤ envelope S p x :=
      le_ciInf fun A => by linarith [h' A]
    linarith
  · intro t ht x
    by_cases ht0 : t = 0
    · subst t
      simp only [zero_smul, zero_mul]
      apply le_antisymm
      · exact (envelope_le_self hp hcontract 0).trans_eq hp.map_zero
      · exact le_ciInf fun A => by simp [hp.map_zero]
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      apply le_antisymm
      · have : envelope S p (t • x) / t ≤ envelope S p x := by
          apply le_ciInf
          intro A
          apply (div_le_iff₀ htpos).2
          calc
            envelope S p (t • x) ≤ p (A.1 (t • x)) := envelope_le hp hcontract A.2 _
            _ = p (A.1 x) * t := by rw [map_smul, hp.2 t ht, mul_comm]
        exact (div_le_iff₀ htpos).1 this |>.trans_eq (mul_comm _ _)
      · apply le_ciInf
        intro A
        rw [map_smul, hp.2 t ht]
        exact mul_le_mul_of_nonneg_left (envelope_le hp hcontract A.2 x) ht

lemma le_envelope_on_subspace {p : E → ℝ}
    (Y : Submodule ℝ E) (f : Y →ₗ[ℝ] ℝ)
    (hY : ∀ A ∈ S, ∀ y ∈ Y, A y ∈ Y)
    (hf : ∀ y : Y, f y ≤ p (y : E))
    (hfinv : ∀ (A : Module.End ℝ E) (hA : A ∈ S) (y : Y),
      f ⟨A y, hY A hA y y.property⟩ = f y) (y : Y) :
    f y ≤ envelope S p y := by
  apply le_ciInf
  intro A
  obtain ⟨z, hz, hfz⟩ := averaging_preserve Y f hY hfinv A.2 y
  rw [hz, ← hfz]
  exact hf z

lemma averaging_pow {A : Module.End ℝ E} (hA : Averaging S A) (n : ℕ) :
    Averaging S (A ^ n) := by
  induction n with
  | zero => simpa using (Averaging.one : Averaging S 1)
  | succ n ih => simpa only [pow_succ] using Averaging.mul ih hA

lemma averaging_convex : Convex ℝ {A : Module.End ℝ E | Averaging S A} := by
  intro A hA B hB a b ha hb hab
  exact Averaging.convex a b hA hB ha hb hab

/-- Every finite Cesàro average is one of our averaging operators. -/
lemma averaging_cesaro {A : Module.End ℝ E} (hA : Averaging S A)
    (n : ℕ) (hn : 0 < n) : Averaging S ((n : ℝ)⁻¹ • ∑ j ∈ Finset.range n, A ^ j) := by
  rw [Finset.smul_sum]
  apply averaging_convex.sum_mem
  · intro j hj; positivity
  · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
  · intro j hj; exact averaging_pow hA j

/-- Averaging a difference telescopes to two endpoint terms. -/
lemma cesaro_difference (A : Module.End ℝ E) (n : ℕ) (x : E) :
    ((n : ℝ)⁻¹ • ∑ j ∈ Finset.range n, A ^ j) (x - A x) =
      (n : ℝ)⁻¹ • (x - (A ^ n) x) := by
  have h := congrArg (fun T : Module.End ℝ E => T x) (geom_sum_mul_neg A n)
  change (n : ℝ)⁻¹ • ((∑ j ∈ Finset.range n, A ^ j) (x - A x)) = _
  exact congrArg (fun y : E => (n : ℝ)⁻¹ • y) h

lemma envelope_difference_le_div {p : E → ℝ} (hp : IsSublinear p)
    (hcontract : ∀ A ∈ S, ∀ x, p (A x) ≤ p x)
    {A : Module.End ℝ E} (hA : A ∈ S) (x : E) (n : ℕ) (hn : 0 < n) :
    envelope S p (x - A x) ≤ (p x + p (-x)) / (n : ℝ) := by
  have hpow := averaging_contract hp hcontract (averaging_pow (.basic hA) n) (-x)
  rw [map_neg] at hpow
  have hsub : p (x - (A ^ n) x) ≤ p x + p (-x) := by
    simpa only [sub_eq_add_neg] using
      (hp.1 x (-((A ^ n) x))).trans (add_le_add le_rfl hpow)
  calc
    _ ≤ p (((n : ℝ)⁻¹ • ∑ j ∈ Finset.range n, A ^ j) (x - A x)) :=
      envelope_le hp hcontract (averaging_cesaro (.basic hA) n hn) _
    _ = (n : ℝ)⁻¹ * p (x - (A ^ n) x) := by
      rw [cesaro_difference, hp.2 _ (by positivity)]
    _ ≤ (n : ℝ)⁻¹ * (p x + p (-x)) := mul_le_mul_of_nonneg_left hsub (by positivity)
    _ = (p x + p (-x)) / (n : ℝ) := by rw [div_eq_mul_inv, mul_comm]

lemma envelope_difference_nonpos {p : E → ℝ} (hp : IsSublinear p)
    (hcontract : ∀ A ∈ S, ∀ x, p (A x) ≤ p x)
    {A : Module.End ℝ E} (hA : A ∈ S) (x : E) : envelope S p (x - A x) ≤ 0 := by
  by_contra h
  have hpos : 0 < envelope S p (x - A x) := lt_of_not_ge h
  obtain ⟨n, hn⟩ := exists_nat_gt ((p x + p (-x)) / envelope S p (x - A x))
  have hn' : (p x + p (-x)) / envelope S p (x - A x) < ((n + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hlt := (div_lt_iff₀ hpos).1 hn'
  have hdiv : (p x + p (-x)) / ((n + 1 : ℕ) : ℝ) < envelope S p (x - A x) := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))).2
    nlinarith
  exact (not_lt_of_ge (envelope_difference_le_div hp hcontract hA x (n + 1) (Nat.succ_pos n))) hdiv

end InvariantHB
/-- A dominated invariant real linear functional extends invariantly, without
any norm, topology, closedness, or identity hypothesis on the semigroup. -/
theorem invariant_hahn_banach {E : Type u} [AddCommGroup E] [Module ℝ E]
    (p : E → ℝ) (hp : IsSublinear p)
    (S : Subsemigroup (Module.End ℝ E))
    (hcomm : ∀ A ∈ S, ∀ B ∈ S, Commute A B)
    (hcontract : ∀ A ∈ S, ∀ x : E, p (A x) ≤ p x)
    (Y : Submodule ℝ E)
    (hY : ∀ A ∈ S, ∀ y ∈ Y, A y ∈ Y)
    (f : Y →ₗ[ℝ] ℝ) (hf : ∀ y : Y, f y ≤ p (y : E))
    (hfinv : ∀ (A : Module.End ℝ E) (hA : A ∈ S) (y : Y),
      f ⟨A y, hY A hA y y.property⟩ = f y) :
    ∃ F : E →ₗ[ℝ] ℝ,
      (∀ y : Y, F (y : E) = f y) ∧
      (∀ x : E, F x ≤ p x) ∧
      (∀ A ∈ S, ∀ x : E, F (A x) = F x) := by
  obtain ⟨F, hFext, hF⟩ := real_hahn_banach Y (InvariantHB.envelope (S : Set _) p)
    (InvariantHB.envelope_sublinear hp hcomm hcontract) f
    (InvariantHB.le_envelope_on_subspace Y f hY hf hfinv)
  refine ⟨F, hFext, fun x => (hF x).trans (InvariantHB.envelope_le_self hp hcontract x), ?_⟩
  intro A hA x
  have h₁ := (hF (x - A x)).trans (InvariantHB.envelope_difference_nonpos hp hcontract hA x)
  have h₂ := (hF (-x - A (-x))).trans
    (InvariantHB.envelope_difference_nonpos hp hcontract hA (-x))
  simp only [map_sub, map_neg] at h₁ h₂
  linarith

end ExpandedFA.P1
