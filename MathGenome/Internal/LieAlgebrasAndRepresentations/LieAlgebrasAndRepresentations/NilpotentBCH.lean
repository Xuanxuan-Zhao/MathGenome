import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.NilpotentBCH
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FormalBCH
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.DerivedLowerSeries

/-! LA-A09: finite BCH on nilpotent Lie algebras over characteristic-zero fields.
Homogeneous bracket polynomials represent the actual formal BCH coefficients.
Finite-jet descent proves the group laws without dimension assumptions.
Directional derivatives use affine-line coefficients of these finite polynomials. -/
noncomputable section
namespace LieAlgebrasAndRepresentations.NilpotentBCH
universe u v w z

variable {k : Type u} {ι : Type v} {L : Type w} {M : Type z}
  [Field k] [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]

theorem Word.length_pos (a : Word ι) : 0 < a.length := by
  induction a with
  | letter i => exact Nat.zero_lt_one
  | bracket a b ha hb => exact Nat.add_pos_left ha _

theorem Word.eval_map (F : L →ₗ⁅k⁆ M) (f : ι → L) (a : Word ι) :
    F (a.eval (k := k) f) = a.eval (k := k) (fun i => F (f i)) := by
  induction a with
  | letter i => rfl
  | bracket a b ha hb => simp only [Word.eval, LieHom.map_lie, ha, hb]

theorem Polynomial.eval_map (F : L →ₗ⁅k⁆ M) (f : ι → L) (P : Polynomial k ι) :
    F (P.eval f) = P.eval (fun i => F (f i)) := by
  induction P with
  | nil => simp [Polynomial.eval]
  | cons a P ih =>
    simpa only [Polynomial.eval, List.map_cons, List.sum_cons, map_add, map_smul,
      Word.eval_map] using congrArg (fun z => a.1 • a.2.eval (k := k) (fun i => F (f i)) + z) ih

@[simp] theorem Polynomial.eval_append (f : ι → L) (P Q : Polynomial k ι) :
    (P ++ Q).eval f = P.eval f + Polynomial.eval f Q := by
  simp [Polynomial.eval]

@[simp] theorem Polynomial.eval_scale (f : ι → L) (r : k) (P : Polynomial k ι) :
    (P.scale r).eval f = r • P.eval f := by
  induction P with
  | nil => simp [Polynomial.eval, Polynomial.scale]
  | cons a P ih =>
    simpa [Polynomial.eval, Polynomial.scale, mul_smul, smul_add] using
      congrArg (fun z => r • (a.1 • a.2.eval (k := k) f) + z) ih

@[simp] theorem Polynomial.eval_bracket (f : ι → L) (P Q : Polynomial k ι) :
    (P.bracket Q).eval f = ⁅P.eval f, Polynomial.eval f Q⁆ := by
  have h (a : k × Word ι) :
      Polynomial.eval f (Q.map fun b => (a.1 * b.1, Word.bracket a.2 b.2)) =
        ⁅a.1 • a.2.eval (k := k) f, Polynomial.eval f Q⁆ := by
    induction Q with
    | nil => simp [Polynomial.eval]
    | cons b Q ih =>
      change (a.1 * b.1) • ⁅a.2.eval (k := k) f, b.2.eval (k := k) f⁆ +
        Polynomial.eval f (Q.map fun b => (a.1 * b.1, Word.bracket a.2 b.2)) =
        ⁅a.1 • a.2.eval (k := k) f, b.1 • b.2.eval (k := k) f + Polynomial.eval f Q⁆
      rw [ih, lie_add]
      congr 1
      simp only [smul_lie, lie_smul, smul_smul, mul_comm]
  induction P with
  | nil => simp [Polynomial.bracket, Polynomial.eval]
  | cons a P ih =>
    change Polynomial.eval f
      ((Q.map fun b => (a.1 * b.1, Word.bracket a.2 b.2)) ++ Polynomial.bracket P Q) = _
    rw [Polynomial.eval_append, h, ih]
    simp [Polynomial.eval, add_lie]

/-- A bracket tree with r leaves evaluates in gamma_r, regardless of its shape. -/
theorem Word.eval_mem_lowerCentralSeries (f : ι → L) (a : Word ι) :
    a.eval (k := k) f ∈ lowerCentralSeries k L a.length := by
  induction a with
  | letter i => simp [Word.eval, Word.length, lowerCentralSeries_one]
  | bracket a b ha hb =>
    exact lowerCentralSeries_bracket a.length b.length a.length_pos b.length_pos
      (LieSubmodule.lie_mem_lie ha hb)

theorem Word.eval_eq_zero (c : ℕ) (hc : lowerCentralSeries k L (c + 1) = ⊥)
    (f : ι → L) (a : Word ι) (ha : c < a.length) : a.eval (k := k) f = 0 := by
  have hle : lowerCentralSeries k L a.length ≤ lowerCentralSeries k L (c + 1) :=
    LieModule.antitone_lowerCentralSeries k L L (by omega)
  have h := hle (a.eval_mem_lowerCentralSeries (k := k) f)
  simpa [hc] using h

theorem Polynomial.eval_eq_zero_of_homogeneous (c n : ℕ)
    (hc : lowerCentralSeries k L (c + 1) = ⊥) (hn : c < n)
    (f : ι → L) (P : Polynomial k ι) (hP : P.Homogeneous n) : P.eval f = 0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  rw [Word.eval_eq_zero c hc f a.2 (by rw [hP a ha]; exact hn), smul_zero]

theorem Word.curve_zero (f g : ι → L) (a : Word ι) :
    a.curve (k := k) f g 0 = a.eval (k := k) f := by
  induction a with
  | letter i => simp [Word.curve, Word.eval]
  | bracket a b ha hb => simp [Word.curve, Word.eval, ha, hb]

/-- The affine-line substitution has finitely many nonzero coefficients. -/
theorem Word.curve_eq_zero (f g : ι → L) (a : Word ι) (n : ℕ)
    (hn : a.length < n) : a.curve (k := k) f g n = 0 := by
  induction a generalizing n with
  | letter i => simp only [Word.length] at hn; simp [Word.curve, show n ≠ 0 by omega,
      show n ≠ 1 by omega]
  | bracket a b ha hb =>
    apply Finset.sum_eq_zero
    intro ij hij
    have hs := Finset.mem_antidiagonal.mp hij
    by_cases h : a.length < ij.1
    · rw [ha _ h, zero_lie]
    · rw [hb _ (by simp only [Word.length] at hn; omega), lie_zero]

theorem Polynomial.curve_zero (f g : ι → L) (P : Polynomial k ι) :
    P.curve f g 0 = P.eval f := by
  simp only [Polynomial.curve, Polynomial.eval, Word.curve_zero]

theorem Polynomial.curve_eq_zero (f g : ι → L) (P : Polynomial k ι) (c n : ℕ)
    (hP : ∀ a ∈ P, a.2.length ≤ c) (hn : c < n) : P.curve f g n = 0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  rw [Word.curve_eq_zero f g a.2 n (lt_of_le_of_lt (hP a ha) hn), smul_zero]

theorem Word.derivation_curve_one (D : LieDerivation k L L) (f : ι → L) (a : Word ι) :
    D (a.eval (k := k) f) = a.curve (k := k) f (fun i => D (f i)) 1 := by
  induction a with
  | letter i => simp [Word.eval, Word.curve]
  | bracket a b ha hb =>
    rw [Word.eval, D.apply_lie_eq_add, ha, hb]
    simp [Word.curve, Finset.Nat.antidiagonal_succ, Word.curve_zero]

theorem Polynomial.derivation_directionalDerivative (D : LieDerivation k L L)
    (f : ι → L) (P : Polynomial k ι) :
    D (P.eval f) = P.directionalDerivative f (fun i => D (f i)) := by
  induction P with
  | nil => simp [Polynomial.eval, Polynomial.directionalDerivative, Polynomial.curve]
  | cons a P ih =>
    simpa only [Polynomial.eval, Polynomial.directionalDerivative, Polynomial.curve,
      List.map_cons, List.sum_cons, map_add, map_smul, Word.derivation_curve_one] using
      congrArg (fun z => a.1 • a.2.curve (k := k) f (fun i => D (f i)) 1 + z) ih

theorem inputMap_map (F : L →ₗ⁅k⁆ M) (x y : L) :
    (fun a => F (inputMap (k := k) x y a)) = inputMap (k := k) (F x) (F y) := by
  funext a
  simp [inputMap]

theorem product_naturality_same_cutoff [CharZero k] (c : ℕ)
    (F : L →ₗ⁅k⁆ M) (x y : L) :
    F (product (k := k) c x y) = product (k := k) c (F x) (F y) := by
  unfold product
  rw [Polynomial.eval_map, inputMap_map]

theorem derivation_spec :
    Specs.LieAlgebrasAndRepresentations.NilpotentBCH.derivationExpected.{u,w} := by
  intro k L _ _ _ _ c _ D x y
  unfold product derivative
  rw [Polynomial.derivation_directionalDerivative]
  congr 1
  funext a
  simp [inputMap]

theorem vanishing_spec :
    Specs.LieAlgebrasAndRepresentations.NilpotentBCH.vanishingExpected.{u,w,v} := by
  intro k L _ _ _ _ c hc ι f a ha
  exact Word.eval_eq_zero c hc f a ha

theorem Polynomial.component_cons (f : ι → L) (a : k × Word ι)
    (P : Polynomial k ι) (n : ℕ) :
    Polynomial.eval f (Polynomial.component (a :: P) n) =
      (if a.2.length = n then a.1 • a.2.eval (k := k) f else 0) +
        (P.component n).eval f := by
  by_cases h : a.2.length = n <;> simp [Polynomial.component, Polynomial.eval, h]

/-- Evaluating a finite expression in a class-c algebra discards precisely the
homogeneous components above c. -/
theorem Polynomial.eval_eq_sum_components (c : ℕ)
    (hc : lowerCentralSeries k L (c + 1) = ⊥) (f : ι → L) (P : Polynomial k ι) :
    P.eval f = ∑ n ∈ Finset.range (c + 1), (P.component n).eval f := by
  induction P with
  | nil => simp [Polynomial.eval, Polynomial.component]
  | cons a P ih =>
    simp_rw [Polynomial.component_cons, Finset.sum_add_distrib]
    change a.1 • a.2.eval (k := k) f + Polynomial.eval f P = _
    rw [ih]
    congr 1
    by_cases h : a.2.length ≤ c
    · simp [Finset.sum_ite_eq', h, Nat.lt_succ_iff]
    · rw [Word.eval_eq_zero c hc f a.2 (by omega), smul_zero]
      simp [Finset.sum_ite_eq', h, Nat.lt_succ_iff]

section Substitution
variable {κ : Type*}

def Word.substitute (σ : ι → Polynomial k κ) : Word ι → Polynomial k κ
  | .letter i => σ i
  | .bracket a b => (a.substitute σ).bracket (b.substitute σ)

def Polynomial.substitute (σ : ι → Polynomial k κ) (P : Polynomial k ι) :
    Polynomial k κ := P.flatMap fun a => (a.2.substitute σ).scale a.1

theorem Polynomial.eval_flatMap {J : Type*} (f : ι → L) (l : List J)
    (g : J → Polynomial k ι) :
    Polynomial.eval f (l.flatMap g) = (l.map fun j => (g j).eval f).sum := by
  induction l with
  | nil => simp [Polynomial.eval]
  | cons j l ih => simpa only [List.flatMap_cons, Polynomial.eval_append,
      List.map_cons, List.sum_cons] using congrArg (fun z => (g j).eval f + z) ih

theorem Word.eval_substitute (σ : ι → Polynomial k κ) (f : κ → L) (a : Word ι) :
    (a.substitute σ).eval f = a.eval (k := k) (fun i => (σ i).eval f) := by
  induction a with
  | letter i => rfl
  | bracket a b ha hb => simp only [Word.substitute, Polynomial.eval_bracket, ha, hb, Word.eval]

theorem Polynomial.eval_substitute (σ : ι → Polynomial k κ) (f : κ → L)
    (P : Polynomial k ι) :
    (P.substitute σ).eval f = P.eval (fun i => (σ i).eval f) := by
  unfold Polynomial.substitute
  rw [Polynomial.eval_flatMap]
  simp only [Polynomial.eval_scale, Word.eval_substitute]
  rfl

/-- Substitution at two finite bracket polynomials, linear in the two-generator
vector space used for the universal BCH coefficients. -/
def Polynomial.substituteTwo (P : Polynomial k (FormalBCH.Two k))
    (A B : Polynomial k ι) : Polynomial k ι :=
  P.substitute fun v => A.scale (v 0) ++ B.scale (v 1)

@[simp] theorem Polynomial.eval_substituteTwo (P : Polynomial k (FormalBCH.Two k))
    (A B : Polynomial k ι) (f : ι → L) :
    (P.substituteTwo A B).eval f = P.eval (inputMap (k := k) (A.eval f) (B.eval f)) := by
  rw [Polynomial.substituteTwo, Polynomial.eval_substitute]
  congr 1
  funext v
  simp [inputMap]

end Substitution

section TensorInterpretation
open CompletedPrimitives
attribute [local instance 100] LieRing.ofAssociativeRing
variable {V : Type v} [AddCommGroup V] [Module k V]

theorem Word.tensor_mem_degree (a : Word V) :
    a.eval (k := k) (TensorAlgebra.ι k) ∈ degree k V a.length := by
  induction a with
  | letter v => exact generator_mem_degree_one k V v
  | bracket a b ha hb =>
    change a.eval (TensorAlgebra.ι k) * b.eval (TensorAlgebra.ι k) -
      b.eval (TensorAlgebra.ι k) * a.eval (TensorAlgebra.ι k) ∈ _
    apply Submodule.sub_mem
    · rw [Word.length, degree, pow_add]
      exact Submodule.mul_mem_mul ha hb
    · rw [Word.length, Nat.add_comm, degree, pow_add]
      exact Submodule.mul_mem_mul hb ha

theorem Polynomial.component_homogeneous (P : Polynomial k V) (n : ℕ) :
    (P.component n).Homogeneous n := by
  intro a ha
  simpa [Polynomial.component] using (List.mem_filter.mp ha).2

/-- Filtering bracket trees by their leaf count is precisely tensor projection. -/
theorem Polynomial.component_tensor (P : Polynomial k V) (n : ℕ) :
    (P.component n).eval (TensorAlgebra.ι k) =
      PowerSeries.coeff n (ordinaryInclusion k V (P.eval (TensorAlgebra.ι k))).val := by
  induction P with
  | nil => simp [Polynomial.component, Polynomial.eval]
  | cons a P ih =>
    have h := ordinaryInclusion_coeff_homogeneous k V (a.2.tensor_mem_degree (k := k)) n
    simp only [Polynomial.component, List.filter_cons, beq_iff_eq, Polynomial.eval,
      List.map_cons, List.sum_cons, map_add, map_smul, Subalgebra.coe_add,
      Subalgebra.coe_smul, PowerSeries.coeff_smul] at *
    by_cases hn : a.2.length = n
    · simp [hn, h, ih]
    · simp [hn, h, ih, Ne.symm hn]

/-- Every element of the actual tensor free Lie subalgebra is represented by a
finite linear combination of bracket trees on V. -/
theorem Polynomial.exists_of_mem_tensorLie {x : A k V} (hx : x ∈ tensorLie k V) :
    ∃ P : Polynomial k V, P.eval (TensorAlgebra.ι k) = x := by
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact ⟨[(1, Word.letter v)], by simp [Polynomial.eval, Word.eval]⟩
  | zero => exact ⟨[], by simp [Polynomial.eval]⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨P, rfl⟩ := ihx
    obtain ⟨Q, rfl⟩ := ihy
    exact ⟨P ++ Q, Polynomial.eval_append _ _ _⟩
  | smul r x hx ih =>
    obtain ⟨P, rfl⟩ := ih
    exact ⟨P.scale r, Polynomial.eval_scale _ _ _⟩
  | lie x y hx hy ihx ihy =>
    obtain ⟨P, rfl⟩ := ihx
    obtain ⟨Q, rfl⟩ := ihy
    exact ⟨P.bracket Q, Polynomial.eval_bracket _ _ _⟩

/-- Tensor equality of bracket polynomials descends to every linear assignment
in every Lie algebra, using the faithful free Lie inclusion from LA-A07. -/
theorem Polynomial.eval_eq_of_tensor_eq (f : V →ₗ[k] L) (P Q : Polynomial k V)
    (h : P.eval (TensorAlgebra.ι k) = Q.eval (TensorAlgebra.ι k)) :
    P.eval f = Q.eval f := by
  have hmap (R : Polynomial k V) :
      FreeLie.tensorLieMap k V (R.eval (FreeLie.generator k V)) =
        R.eval (TensorAlgebra.ι k) := by
    rw [Polynomial.eval_map]
    congr 1
    funext v
    exact FreeLie.tensorLieMap_generator_apply k V v
  have hfree : P.eval (FreeLie.generator k V) = Q.eval (FreeLie.generator k V) :=
    FreeLie.tensorLieMap_injective k V ((hmap P).trans (h.trans (hmap Q).symm))
  have hext (R : Polynomial k V) :
      FreeLie.extend k V f (R.eval (FreeLie.generator k V)) = R.eval f := by
    rw [Polynomial.eval_map]
    congr 1
    funext v
    exact LinearMap.congr_fun (FreeLie.extend_generator k V f) v
  rw [← hext P, ← hext Q, hfree]

/-- A nilpotent evaluation depends only on the finite tensor jet through its
class bound. This does not require finite-dimensionality of V or the target. -/
theorem Polynomial.eval_eq_of_jet_eq (c : ℕ)
    (hc : lowerCentralSeries k L (c + 1) = ⊥) (f : V →ₗ[k] L)
    (P Q : Polynomial k V)
    (h : ∀ n ≤ c,
      PowerSeries.coeff n (ordinaryInclusion k V (P.eval (TensorAlgebra.ι k))).val =
      PowerSeries.coeff n (ordinaryInclusion k V (Q.eval (TensorAlgebra.ι k))).val) :
    P.eval f = Q.eval f := by
  rw [P.eval_eq_sum_components c hc, Q.eval_eq_sum_components c hc]
  apply Finset.sum_congr rfl
  intro n hn
  apply Polynomial.eval_eq_of_tensor_eq f
  rw [Polynomial.component_tensor, Polynomial.component_tensor]
  exact h n (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn)

end TensorInterpretation

theorem coefficient_spec :
    Specs.LieAlgebrasAndRepresentations.NilpotentBCH.coefficientExpected.{u} := by
  intro k _ _ n
  apply Classical.epsilon_spec
  have hLie := (FormalBCH.lie_spec k).2
  have hmem := (CompletedPrimitives.completedLie_iff_coeff _ _ _).mp hLie n
  obtain ⟨P, hP⟩ := Polynomial.exists_of_mem_tensorLie hmem
  refine ⟨P.component n, P.component_homogeneous n, ?_⟩
  rw [Polynomial.component_tensor, hP]
  simpa using CompletedPrimitives.ordinaryInclusion_coeff_homogeneous k (FormalBCH.Two k)
    ((FormalBCH.universalBCH k).property n) n

section FiniteCutoffs
variable [CharZero k]

theorem truncatedPolynomial_length_le (c : ℕ) :
    ∀ a ∈ truncatedPolynomial k c, a.2.length ≤ c := by
  intro a ha
  obtain ⟨n, hn, ha⟩ := List.mem_flatMap.mp ha
  have hn' : n < c + 1 := List.mem_range.mp hn
  rw [(coefficient_spec k n).1 a ha]
  omega

/-- The actual affine-line coefficient sequence is a finite vector-valued
polynomial of degree at most c. Its coefficient one defines the derivative. -/
theorem polynomial_curve_finite (c : ℕ) (x y dx dy : L) (n : ℕ) (hn : c < n) :
    (truncatedPolynomial k c).curve (inputMap (k := k) x y)
      (inputMap (k := k) dx dy) n = 0 :=
  Polynomial.curve_eq_zero _ _ _ c n (truncatedPolynomial_length_le c) hn

theorem product_succ (c : ℕ) (x y : L) :
    product (k := k) (c + 1) x y = product (k := k) c x y +
      (coefficientPolynomial k (c + 1)).eval (inputMap (k := k) x y) := by
  unfold product truncatedPolynomial
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
  exact Polynomial.eval_append _ _ _

theorem product_stable (c d : ℕ) (hc : lowerCentralSeries k L (c + 1) = ⊥)
    (hd : c ≤ d) (x y : L) :
    product (k := k) d x y = product (k := k) c x y := by
  induction d, hd using Nat.le_induction with
  | base => rfl
  | succ d hd ih =>
    rw [product_succ, ih]
    rw [Polynomial.eval_eq_zero_of_homogeneous c (d + 1) hc (by omega)
      (inputMap (k := k) x y) _ (coefficient_spec k (d + 1)).1, add_zero]

theorem cutoff_spec :
    Specs.LieAlgebrasAndRepresentations.NilpotentBCH.cutoffExpected.{u,w} := by
  intro k L _ _ _ _ c d hcd hc x y
  exact (product_stable c d hc hcd x y).symm

theorem naturality_spec :
    Specs.LieAlgebrasAndRepresentations.NilpotentBCH.naturalityExpected.{u,w,z} := by
  intro k L M _ _ _ _ _ _ c d hc hd F x y
  calc
    F (product (k := k) c x y) = F (product (k := k) (max c d) x y) :=
      congrArg F (cutoff_spec c (max c d) (le_max_left _ _) hc x y)
    _ = product (k := k) (max c d) (F x) (F y) :=
      product_naturality_same_cutoff _ F x y
    _ = product (k := k) d (F x) (F y) :=
      product_stable d (max c d) hd (le_max_right _ _) _ _

section FormalJets
open CompletedPrimitives FormalBCH FormalExpLog
attribute [local instance 100] LieRing.ofAssociativeRing
variable {V : Type v} [AddCommGroup V] [Module k V]

theorem Polynomial.eval_tensor_lift {B : Type*} [Ring B] [Algebra k B]
    (f : V →ₗ[k] B) (P : Polynomial k V) :
    TensorAlgebra.lift k f (P.eval (TensorAlgebra.ι k)) = P.eval f := by
  calc
    _ = P.eval (fun v => TensorAlgebra.lift k f (TensorAlgebra.ι k v)) :=
      Polynomial.eval_map (TensorAlgebra.lift k f : TensorAlgebra k V →ₗ⁅k⁆ B) _ P
    _ = _ := by simp only [TensorAlgebra.lift_ι_apply]

theorem truncated_tensor (c : ℕ) :
    (truncatedPolynomial k c).eval (TensorAlgebra.ι k) =
      tensorTruncation (c + 1) (universalBCH k) := by
  have h (N : ℕ) :
      Polynomial.eval (TensorAlgebra.ι k) ((List.range N).flatMap (coefficientPolynomial k)) =
        ∑ n ∈ Finset.range N, PowerSeries.coeff n (universalBCH k).val := by
    induction N with
    | zero => simp [Polynomial.eval]
    | succ N ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
        Polynomial.eval_append, ih, (coefficient_spec k N).2, Finset.sum_range_succ]
  exact h (c + 1)

/-- Finite BCH polynomial evaluation agrees with formal BCH in the finite jet
through the cutoff, for arbitrary positive completed arguments. -/
theorem polynomial_bch_jet (c : ℕ) (p q : Completion k V)
    (hp : Positive k V p) (hq : Positive k V q) :
    Jets.project (k := k) (c + 1)
        ((truncatedPolynomial k c).eval (inputMap (k := k) p q)).val =
      Jets.project (k := k) (c + 1) (bch k V p q).val := by
  let f := twoInputMap p q
  have hp' : PowerSeries.coeff 0 p.val = 0 := hp
  have hq' : PowerSeries.coeff 0 q.val = 0 := hq
  have hf : ∀ v, Positive k V (f v) := by
    intro v
    change PowerSeries.coeff 0 (v 0 • p.val + v 1 • q.val) = 0
    simp only [map_add, PowerSeries.coeff_smul, hp', hq', smul_zero, add_zero]
  change Jets.project (k := k) (c + 1) ((truncatedPolynomial k c).eval f).val = _
  rw [← Polynomial.eval_tensor_lift, truncated_tensor]
  rw [← project_substitute f hf]
  exact congrArg (fun z : Completion k V => Jets.project (k := k) (c + 1) z.val)
    (evaluation_spec k V p q hp hq)

theorem Polynomial.eval_jet_congr (N : ℕ) (P : Polynomial k (Two k))
    (p q p' q' : Completion k V)
    (hp : Jets.project (k := k) N p.val = Jets.project (k := k) N p'.val)
    (hq : Jets.project (k := k) N q.val = Jets.project (k := k) N q'.val) :
    Jets.project (k := k) N (P.eval (inputMap (k := k) p q)).val =
      Jets.project (k := k) N (P.eval (inputMap (k := k) p' q')).val := by
  let F : Completion k V →ₐ[k] Jets.Jet (A k V) N :=
    (Jets.project (k := k) N).comp (degreeSeries (generators k V)).val
  change F (P.eval (inputMap (k := k) p q)) = F (P.eval (inputMap (k := k) p' q'))
  have hm (f : Two k → Completion k V) :
      F (P.eval f) = P.eval (fun i => F (f i)) :=
    Polynomial.eval_map (F : Completion k V →ₗ⁅k⁆ Jets.Jet (A k V) N) f P
  rw [hm, hm]
  congr 1
  funext v
  change F (v 0 • p + v 1 • q) = F (v 0 • p' + v 1 • q')
  simp only [map_add, map_smul]
  rw [show F p = F p' from hp, show F q = F q' from hq]

def Polynomial.completedEval (P : Polynomial k V) : Completion k V :=
  ordinaryInclusion k V (P.eval (TensorAlgebra.ι k))

theorem Word.tensor_mem_lie (a : Word V) :
    a.eval (k := k) (TensorAlgebra.ι k) ∈ tensorLie k V := by
  induction a with
  | letter v => exact LieSubalgebra.subset_lieSpan (Set.mem_range_self v)
  | bracket a b ha hb => exact (tensorLie k V).lie_mem ha hb

theorem Polynomial.tensor_mem_lie (P : Polynomial k V) :
    P.eval (TensorAlgebra.ι k) ∈ tensorLie k V := by
  apply (tensorLie k V).toSubmodule.list_sum_mem
  intro a ha
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
  exact (tensorLie k V).smul_mem r.1 r.2.tensor_mem_lie

theorem Polynomial.completedEval_positive (P : Polynomial k V) :
    Positive k V P.completedEval :=
  tensorLie_constant_zero k V P.tensor_mem_lie

theorem Polynomial.completedEval_eq (P : Polynomial k V) :
    P.completedEval = P.eval (fun v => ordinaryInclusion k V (TensorAlgebra.ι k v)) :=
  Polynomial.eval_map (ordinaryInclusion k V : A k V →ₗ⁅k⁆ Completion k V) _ P

@[simp] theorem Polynomial.completedEval_substituteTwo
    (P : Polynomial k (Two k)) (A B : Polynomial k V) :
    (P.substituteTwo A B).completedEval = P.eval (inputMap (k := k) A.completedEval B.completedEval) := by
  rw [Polynomial.completedEval_eq, Polynomial.eval_substituteTwo,
    ← Polynomial.completedEval_eq, ← Polynomial.completedEval_eq]

/-- The finite associator has zero jet through c, by formal associativity.
All three finite input polynomials have positive degree. -/
theorem associator_jet (c : ℕ) (A B C : Polynomial k V) :
    Jets.project (k := k) (c + 1)
      (((truncatedPolynomial k c).substituteTwo
        ((truncatedPolynomial k c).substituteTwo A B) C).completedEval).val =
    Jets.project (k := k) (c + 1)
      (((truncatedPolynomial k c).substituteTwo A
        ((truncatedPolynomial k c).substituteTwo B C)).completedEval).val := by
  let P := truncatedPolynomial k c
  simp only [Polynomial.completedEval_substituteTwo]
  calc
    _ = Jets.project (k := k) (c + 1)
        (P.eval (inputMap (k := k) (bch k V A.completedEval B.completedEval) C.completedEval)).val :=
      P.eval_jet_congr (c + 1) _ _ _ _
        (polynomial_bch_jet c _ _ A.completedEval_positive B.completedEval_positive) rfl
    _ = Jets.project (k := k) (c + 1)
        (bch k V (bch k V A.completedEval B.completedEval) C.completedEval).val :=
      polynomial_bch_jet c _ _ (bch_positive _ _ _ _) C.completedEval_positive
    _ = Jets.project (k := k) (c + 1)
        (bch k V A.completedEval (bch k V B.completedEval C.completedEval)).val := by
      rw [bch_associative]
    _ = Jets.project (k := k) (c + 1)
        (P.eval (inputMap (k := k) A.completedEval (bch k V B.completedEval C.completedEval))).val :=
      (polynomial_bch_jet c _ _ A.completedEval_positive (bch_positive _ _ _ _)).symm
    _ = _ :=
      P.eval_jet_congr (c + 1) _ _ _ _ rfl
        (polynomial_bch_jet c _ _ B.completedEval_positive C.completedEval_positive).symm

theorem formal_exponential_zero :
    exponential (generators k V) (0 : Completion k V) = 1 := by
  apply Subtype.ext
  apply PowerSeries.ext
  intro n
  simp only [exponential, seriesEval_coeff, Subalgebra.coe_zero, PowerSeries.coeff_one]
  rw [Finset.sum_eq_single 0]
  · simp [expCoefficients]
  · intro m hm hm0
    simp [zero_pow hm0]
  · simp

theorem formal_bch_zero_left (p : Completion k V) (hp : Positive k V p) :
    bch k V 0 p = p := by
  unfold bch
  rw [formal_exponential_zero, one_mul]
  exact (Jets.inverse_laws _).1 p hp

theorem formal_bch_zero_right (p : Completion k V) (hp : Positive k V p) :
    bch k V p 0 = p := by
  unfold bch
  rw [formal_exponential_zero, mul_one]
  exact (Jets.inverse_laws _).1 p hp

theorem formal_bch_neg_right (p : Completion k V) (hp : Positive k V p) :
    bch k V p (-p) = 0 := by
  have hn : Positive k V (-p) := by
    change PowerSeries.coeff 0 (-p.val) = 0
    rw [map_neg, hp, neg_zero]
  have he := Jets.commutingExp_laws (generators k V) p (-p) hp hn
    ((Commute.refl p).neg_right)
  rw [add_neg_cancel, formal_exponential_zero] at he
  unfold bch
  rw [← he]
  have hz := (Jets.inverse_laws (generators k V)).1 0 (by simp)
  rw [formal_exponential_zero] at hz
  exact hz

theorem formal_bch_neg_left (p : Completion k V) (hp : Positive k V p) :
    bch k V (-p) p = 0 := by
  have hn : Positive k V (-p) := by
    change PowerSeries.coeff 0 (-p.val) = 0
    rw [map_neg, hp, neg_zero]
  simpa only [neg_neg] using formal_bch_neg_right (-p) hn

@[simp] theorem Polynomial.completedEval_nil :
    (Polynomial.completedEval ([] : Polynomial k V)) = 0 := by
  simp [Polynomial.completedEval, Polynomial.eval]

@[simp] theorem Polynomial.completedEval_scale (P : Polynomial k V) (r : k) :
    (P.scale r).completedEval = r • P.completedEval := by
  simp [Polynomial.completedEval]

/-- Transfer a formal binary identity to a finite nilpotent evaluation. -/
theorem binary_identity_descends (c : ℕ) (hc : lowerCentralSeries k L (c + 1) = ⊥)
    (A B C : Polynomial k V) (f : V →ₗ[k] L)
    (h : bch k V A.completedEval B.completedEval = C.completedEval) :
    product (k := k) c (A.eval f) (B.eval f) = C.eval f := by
  have hj : Jets.project (k := k) (c + 1)
      (((truncatedPolynomial k c).substituteTwo A B).completedEval).val =
        Jets.project (k := k) (c + 1) C.completedEval.val := by
    rw [Polynomial.completedEval_substituteTwo, ← h]
    exact polynomial_bch_jet c _ _ A.completedEval_positive B.completedEval_positive
  have he := Polynomial.eval_eq_of_jet_eq c hc f
    ((truncatedPolynomial k c).substituteTwo A B) C (fun n hn =>
      (Jets.project_eq_iff (k := k) (c + 1) _ _).mp hj n (by omega))
  rw [Polynomial.eval_substituteTwo] at he
  exact he

end FormalJets

/-- Formal associativity descends through finite jets to every nilpotent target. -/
theorem product_associative (c : ℕ) (hc : lowerCentralSeries k L (c + 1) = ⊥)
    (x y z : L) :
    product (k := k) c (product (k := k) c x y) z =
      product (k := k) c x (product (k := k) c y z) := by
  let P := truncatedPolynomial k c
  let X : Polynomial k L := [(1, Word.letter x)]
  let Y : Polynomial k L := [(1, Word.letter y)]
  let Z : Polynomial k L := [(1, Word.letter z)]
  have hj := associator_jet c X Y Z
  have h := Polynomial.eval_eq_of_jet_eq c hc (LinearMap.id : L →ₗ[k] L)
    (P.substituteTwo (P.substituteTwo X Y) Z)
    (P.substituteTwo X (P.substituteTwo Y Z)) (fun n hn =>
      (FormalExpLog.Jets.project_eq_iff (k := k) (c + 1) _ _).mp hj n (by omega))
  simp only [Polynomial.eval_substituteTwo] at h
  have hX : X.eval (LinearMap.id : L →ₗ[k] L) = x := by simp [X, Polynomial.eval, Word.eval]
  have hY : Y.eval (LinearMap.id : L →ₗ[k] L) = y := by simp [Y, Polynomial.eval, Word.eval]
  have hZ : Z.eval (LinearMap.id : L →ₗ[k] L) = z := by simp [Z, Polynomial.eval, Word.eval]
  rw [hX, hY, hZ] at h
  exact h



theorem product_unit_inverse (c : ℕ) (hc : lowerCentralSeries k L (c + 1) = ⊥)
    (x : L) :
    (product (k := k) c 0 x = x ∧ product (k := k) c x 0 = x) ∧
    (product (k := k) c (-x) x = 0 ∧ product (k := k) c x (-x) = 0) := by
  let X : Polynomial k L := [(1, Word.letter x)]
  let O : Polynomial k L := []
  let N := X.scale (-1)
  have hx : X.eval (LinearMap.id : L →ₗ[k] L) = x := by
    simp [X, Polynomial.eval, Word.eval]
  have ho : O.eval (LinearMap.id : L →ₗ[k] L) = 0 := rfl
  have hn : N.eval (LinearMap.id : L →ₗ[k] L) = -x := by
    change (X.scale (-1)).eval (LinearMap.id : L →ₗ[k] L) = -x
    rw [Polynomial.eval_scale, hx, neg_one_smul]
  have hO : O.completedEval = 0 := Polynomial.completedEval_nil
  have hN : N.completedEval = -X.completedEval := by simp [N]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have h := binary_identity_descends c hc O X X LinearMap.id (by
      rw [hO]; exact formal_bch_zero_left _ X.completedEval_positive)
    simpa only [hx, ho] using h
  · have h := binary_identity_descends c hc X O X LinearMap.id (by
      rw [hO]; exact formal_bch_zero_right _ X.completedEval_positive)
    simpa only [hx, ho] using h
  · have h := binary_identity_descends c hc N X O LinearMap.id (by
      rw [hN, hO]; exact formal_bch_neg_left _ X.completedEval_positive)
    simpa only [hx, ho, hn] using h
  · have h := binary_identity_descends c hc X N O LinearMap.id (by
      rw [hN, hO]; exact formal_bch_neg_right _ X.completedEval_positive)
    simpa only [hx, ho, hn] using h

theorem group_spec :
    Specs.LieAlgebrasAndRepresentations.NilpotentBCH.groupExpected.{u,w} := by
  intro k L _ _ _ _ c hc
  exact ⟨product_associative c hc, fun x => (product_unit_inverse c hc x).1,
    fun x => (product_unit_inverse c hc x).2⟩

end FiniteCutoffs

def finiteBCH :
    Specs.LieAlgebrasAndRepresentations.NilpotentBCH.productExpectedType.{u,w} := @product

def bchDerivative :
    Specs.LieAlgebrasAndRepresentations.NilpotentBCH.derivativeExpectedType.{u,w} := @derivative

def bchCoefficient :
    Specs.LieAlgebrasAndRepresentations.NilpotentBCH.polynomialExpectedType.{u} := coefficientPolynomial

end LieAlgebrasAndRepresentations.NilpotentBCH
