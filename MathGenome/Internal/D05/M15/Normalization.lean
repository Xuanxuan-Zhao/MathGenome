import MathGenome.Internal.D05.M15.Exterior
import MathGenome.Internal.D05.M15.Symmetric
import MathGenome.Internal.D05.M15.Symmetrizers
import MathGenome.Internal.Specs.D05.M15.Normalization
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace D05.M15.Normalization
open scoped TensorProduct
open Specs.D05.M15.Normalization
open D05.M15.PermutationActions D05.M15.Symmetrizers D05.Foundations
universe u v w
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [CharZero K]

/-- Right translation permutes the summands of the finite-group average. -/
theorem groupAverage_right {E G : Type*} [AddCommGroup E] [Module K E]
    [Group G] [Fintype G] (ρ : G → E →ₗ[K] E)
    (hmul : ∀ g h, (ρ g).comp (ρ h) = ρ (g * h)) (g : G) (x : E) :
    groupAverage ρ (ρ g x) = groupAverage ρ x := by
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply]
  congr 1
  calc
    ∑ h : G, ρ h (ρ g x) = ∑ h : G, ρ (h * g) x := by
      apply Finset.sum_congr rfl
      intro h _
      exact LinearMap.congr_fun (hmul h g) x
    _ = ∑ h : G, ρ h x :=
      Fintype.sum_bijective (· * g) (Group.mulRight_bijective g) _ _ (fun _ => rfl)

private theorem symP_right (p : ℕ) (σ : Equiv.Perm (Fin p)) (t : TensorPower K p V) :
    symP p (permutationOperator p σ t) = symP p t := by
  have h := groupAverage_right (permutationOperator (K := K) (V := V) p)
    (operator_mul p) σ t
  simpa only [groupAverage, Fintype.card_perm, Fintype.card_fin,
    Specs.D05.M15.Symmetrizers.symmetricProjector] using h

private theorem altP_right (p : ℕ) (σ : Equiv.Perm (Fin p)) (t : TensorPower K p V) :
    altP p (permutationOperator p σ t) = (permutationSign σ : K) • altP p t := by
  have h := groupAverage_right (signedOperator (K := K) (V := V) p)
    (signedOperator_mul p) σ t
  have hh := congrArg (fun t => (permutationSign σ : K) • t) h
  simpa only [groupAverage, Fintype.card_perm, Fintype.card_fin,
    Specs.D05.M15.Symmetrizers.alternatingProjector, signedOperator,
    LinearMap.smul_apply, map_smul, smul_smul, ← mul_assoc, scalarSign_square,
    one_mul, one_smul] using hh

theorem symmetric_permutation : Specs.D05.M15.Normalization.symmetric_permutation := by
  intro K V _ _ _ _ p σ
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change symQ (K := K) (V := V) p (permutationOperator p σ (PiTensorProduct.tprod K x)) =
    symQ (K := K) (V := V) p (PiTensorProduct.tprod K x)
  rw [operator_apply]
  exact D05.M15.Symmetric.elementary_symmetric p x σ⁻¹

theorem exterior_permutation : Specs.D05.M15.Normalization.exterior_permutation := by
  intro K V _ _ _ _ p σ
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change extQ p (permutationOperator p σ (PiTensorProduct.tprod K x)) =
    (permutationSign σ : K) • extQ p (PiTensorProduct.tprod K x)
  rw [operator_apply, D05.M15.Exterior.projection_elementary,
    D05.M15.Exterior.projection_elementary]
  change (exteriorPower.ιMulti K p) (x ∘ (σ⁻¹ : Equiv.Perm (Fin p))) = _
  rw [AlternatingMap.map_perm]
  rw [D05.Foundations.PermutationSign.signIdentification]
  simp only [Equiv.Perm.sign_inv]
  simp only [Units.smul_def]
  exact (Int.cast_smul_eq_zsmul K _ _).symm

theorem quotient_averages : Specs.D05.M15.Normalization.quotient_averages := by
  intro K V _ _ _ _ p
  have hp : (p.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr p.factorial_ne_zero
  constructor
  · apply LinearMap.ext
    intro t
    change symQ (K := K) (V := V) p (symP p t) = symQ (K := K) (V := V) p t
    simp only [symP, Specs.D05.M15.Symmetrizers.symmetricProjector,
      LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
    have he (σ : Equiv.Perm (Fin p)) :
        symQ (K := K) (V := V) p (permutationOperator p σ t) =
          symQ (K := K) (V := V) p t :=
      LinearMap.congr_fun (symmetric_permutation p σ) t
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hp, one_smul]
  · apply LinearMap.ext
    intro t
    change extQ p (altP p t) = extQ p t
    simp only [altP, Specs.D05.M15.Symmetrizers.alternatingProjector,
      LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
    have he (σ : Equiv.Perm (Fin p)) : extQ p (permutationOperator p σ t) =
        (permutationSign σ : K) • extQ p t :=
      LinearMap.congr_fun (exterior_permutation p σ) t
    simp only [he, smul_smul, scalarSign_square, one_smul,
      Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hp, one_smul]

theorem repeated_slots : Specs.D05.M15.Normalization.repeated_slots := by
  intro K V _ _ _ _ p x i j hx hij
  have hfix : permutationOperator p (Equiv.swap i j) (PiTensorProduct.tprod K x) =
      PiTensorProduct.tprod K x := by
    rw [operator_apply]
    congr 1
    funext k
    simpa only [Equiv.swap_inv] using (Equiv.apply_swap_eq_self hx k)
  have h := altP_right p (Equiv.swap i j) (PiTensorProduct.tprod K x)
  rw [hfix, D05.Foundations.PermutationSign.signTransposition p i j hij] at h
  have hz : (2 : K) • altP p (PiTensorProduct.tprod K x) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp (by simpa using h)
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

private theorem sym_kills (p : ℕ) :
    Specs.D05.M15.Symmetric.adjacentRelations K V p ≤ LinearMap.ker (symP p) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, i, j, _, rfl⟩
  change symP p (_ - _) = 0
  rw [map_sub, sub_eq_zero]
  have h := symP_right p (Equiv.swap i j) (PiTensorProduct.tprod K x)
  rw [operator_apply] at h
  simpa only [Equiv.swap_inv, Function.comp_def] using h.symm

/-- The averaged elementary map is alternating, so its linearization descends
through the existing exterior power's universal property. -/
def averagedAlternating (p : ℕ) : AlternatingMap K V (TensorPower K p V) (Fin p) :=
  ⟨(altP p).compMultilinearMap (PiTensorProduct.tprod K), repeated_slots p⟩

def exteriorSection (p : ℕ) : (⋀[K]^p V) →ₗ[K] TensorPower K p V :=
  exteriorPower.alternatingMapLinearEquiv (averagedAlternating p)

theorem exteriorSection_projection (p : ℕ) :
    (exteriorSection (K := K) (V := V) p).comp (extQ p) = altP p := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change exteriorSection p (extQ p (PiTensorProduct.tprod K x)) = _
  rw [D05.M15.Exterior.projection_elementary]
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (averagedAlternating p) x

theorem annihilates_relations : Specs.D05.M15.Normalization.annihilates_relations := by
  intro K V _ _ _ _ p
  refine ⟨sym_kills p, ?_⟩
  change D05.M15.Exterior.degreeRelations K V p ≤ _
  rw [← D05.M15.Exterior.projection_kernel p]
  intro t ht
  change altP p t = 0
  rw [← exteriorSection_projection, LinearMap.comp_apply, LinearMap.mem_ker.mp ht, map_zero]

def symmetricSection (p : ℕ) : Specs.D05.M15.Symmetric.symmetricPower K V p →ₗ[K]
    TensorPower K p V :=
  (Specs.D05.M15.Symmetric.adjacentRelations K V p).liftQ (symP p) (sym_kills p)

theorem symmetricSection_projection (p : ℕ) :
    (symmetricSection (K := K) (V := V) p).comp (symQ (K := K) (V := V) p) = symP p := by
  ext t
  rfl

/-- A quotient and a descending projector give an actual equivalence with
its image. Surjectivity, rather than a dimension comparison, proves both inverses. -/
theorem quotientAverageEquiv {E Q : Type*} [AddCommGroup E] [Module K E]
    [AddCommGroup Q] [Module K Q] (q : E →ₗ[K] Q) (s : Q →ₗ[K] E)
    (P : E →ₗ[K] E) (hq : Function.Surjective q)
    (hs : s.comp q = P) (hP : q.comp P = q) :
    ∃ e : Q ≃ₗ[K] LinearMap.range P,
      ((LinearMap.range P).subtype.comp e.toLinearMap).comp q = P ∧
      q.comp ((LinearMap.range P).subtype.comp e.toLinearMap) = LinearMap.id := by
  have hqs : q.comp s = LinearMap.id := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := hq y
    change q (s (q x)) = q x
    exact (congrArg q (LinearMap.congr_fun hs x)).trans (LinearMap.congr_fun hP x)
  let f : Q →ₗ[K] LinearMap.range P := s.codRestrict _ (by
    intro y
    obtain ⟨x, rfl⟩ := hq y
    exact ⟨x, (LinearMap.congr_fun hs x).symm⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have hh := congrArg (fun z : LinearMap.range P => q z) h
      change q (s x) = q (s y) at hh
      simpa only [← LinearMap.comp_apply, hqs, LinearMap.id_apply] using hh
    · rintro ⟨_, x, rfl⟩
      refine ⟨q x, Subtype.ext ?_⟩
      exact LinearMap.congr_fun hs x
  refine ⟨LinearEquiv.ofBijective f hf, ?_, ?_⟩
  · exact hs
  · exact hqs

theorem symmetric_bridge : Specs.D05.M15.Normalization.symmetric_bridge := by
  intro K V _ _ _ _ p
  exact quotientAverageEquiv (symQ (K := K) (V := V) p) (symmetricSection p) (symP p)
    (Submodule.mkQ_surjective _) (symmetricSection_projection p) (quotient_averages p).1

theorem exterior_bridge : Specs.D05.M15.Normalization.exterior_bridge := by
  intro K V _ _ _ _ p
  exact quotientAverageEquiv (extQ (K := K) (V := V) p) (exteriorSection p) (altP p)
    (D05.M15.Exterior.projection_surjective p) (exteriorSection_projection p)
    (quotient_averages p).2

def symmetricEmbedding (p : ℕ) : Specs.D05.M15.Symmetric.symmetricPower K V p →ₗ[K]
    _root_.SymmetricAlgebra K V :=
  (Specs.D05.M15.Symmetric.adjacentRelations K V p).liftQ (symH p) (by
    rw [← D05.M15.Symmetric.homogeneous_kernel p])

theorem symmetricEmbedding_projection (p : ℕ) (t : TensorPower K p V) :
    symmetricEmbedding (K := K) (V := V) p (symQ (K := K) (V := V) p t) = symH p t := rfl

theorem symH_average (p : ℕ) (t : TensorPower K p V) :
    symH p (symP p t) = symH p t := by
  have h := LinearMap.congr_fun (quotient_averages (K := K) (V := V) p).1 t
  exact congrArg (symmetricEmbedding (K := K) (V := V) p) h

theorem extH_average (p : ℕ) (t : TensorPower K p V) :
    extH p (altP p t) = extH p t := by
  exact congrArg Subtype.val (LinearMap.congr_fun
    (quotient_averages (K := K) (V := V) p).2 t)

theorem extH_tensor (p : ℕ) (t : TensorPower K p V) :
    extH p t = _root_.TensorAlgebra.toExterior (TensorPower.toTensorAlgebra t) :=
  D05.M15.Exterior.projection_compatibility p t

theorem products : Specs.D05.M15.Normalization.products := by
  intro K V _ _ _ _ p q x y
  constructor
  · rw [symH_average]
    change _root_.SymmetricAlgebra.algHom K V (TensorPower.toTensorAlgebra (concat x y)) =
      _root_.SymmetricAlgebra.algHom K V (TensorPower.toTensorAlgebra x) *
      _root_.SymmetricAlgebra.algHom K V (TensorPower.toTensorAlgebra y)
    rw [← D05.M15.TensorAlgebra.homogeneous_multiplication p q x y]
    exact map_mul _ _ _
  · rw [extH_average, extH_tensor, extH_tensor, extH_tensor]
    rw [← D05.M15.TensorAlgebra.homogeneous_multiplication p q x y]
    exact map_mul _ _ _

theorem product_transport : Specs.D05.M15.Normalization.product_transport := by
  intro K V _ _ _ _ p q
  obtain ⟨es, hs, _⟩ := symmetric_bridge (K := K) (V := V) (p + q)
  obtain ⟨ea, ha, _⟩ := exterior_bridge (K := K) (V := V) (p + q)
  have hs' (t : TensorPower K (p + q) V) :
      (es (symQ (K := K) (V := V) (p + q) t) : TensorPower K (p + q) V) =
        symP (p + q) t := LinearMap.congr_fun hs t
  have ha' (t : TensorPower K (p + q) V) :
      (ea (extQ (p + q) t) : TensorPower K (p + q) V) = altP (p + q) t :=
    LinearMap.congr_fun ha t
  refine ⟨es, ea, hs', ha', ?_, ?_⟩
  · intro x y
    rw [hs']
    exact (products p q x y).1
  · intro x y
    rw [ha']
    exact (products p q x y).2

theorem symP_eq_of_homogeneous_eq (p : ℕ) (x y : TensorPower K p V)
    (h : symH p x = symH p y) : symP p x = symP p y := by
  have hr : x - y ∈ Specs.D05.M15.Symmetric.adjacentRelations K V p := by
    rw [← D05.M15.Symmetric.homogeneous_kernel p]
    change symH p (x - y) = 0
    rw [map_sub, h, sub_self]
  have hh := (annihilates_relations (K := K) (V := V) p).1 hr
  change symP p (x - y) = 0 at hh
  simpa only [map_sub, sub_eq_zero] using hh

theorem altP_eq_of_homogeneous_eq (p : ℕ) (x y : TensorPower K p V)
    (h : extH p x = extH p y) : altP p x = altP p y := by
  have hq : extQ p x = extQ p y := Subtype.ext h
  have hs := congrArg (exteriorSection (K := K) (V := V) p) hq
  simpa only [← LinearMap.comp_apply, exteriorSection_projection] using hs

/-- Associativity can be checked after an injective quotient restriction.
This general lemma handles the degree cast explicitly and applies equally to
the symmetric and exterior quotient algebras. -/
theorem averaged_associativity {B : Type*} [Ring B] [Algebra K B]
    (P : (n : ℕ) → TensorPower K n V →ₗ[K] TensorPower K n V)
    (H : (n : ℕ) → TensorPower K n V →ₗ[K] B)
    (hprod : ∀ p q x y, H (p + q) (P (p + q) (concat x y)) = H p x * H q y)
    (hsep : ∀ n x y, H n x = H n y → P n x = P n y)
    (hidem : ∀ n, (P n).comp (P n) = P n)
    (p q r : ℕ) (x : TensorPower K p V) (y : TensorPower K q V)
    (z : TensorPower K r V) :
    TensorPower.toTensorAlgebra (P (p + q + r) (concat (P (p + q) (concat x y)) z)) =
      TensorPower.toTensorAlgebra (P (p + (q + r)) (concat x (P (q + r) (concat y z)))) := by
  let L := P (p + q + r) (concat (P (p + q) (concat x y)) z)
  let R := P (p + (q + r)) (concat x (P (q + r) (concat y z)))
  have hc (i j : ℕ) (h : i = j) (t : TensorPower K i V) :
      H j (TensorPower.cast K V h t) = H i t := by
    subst j
    simp only [TensorPower.cast_refl, LinearEquiv.refl_apply]
  have hp (i j : ℕ) (h : i = j) (t : TensorPower K i V) :
      P j (TensorPower.cast K V h t) = TensorPower.cast K V h (P i t) := by
    subst j
    simp only [TensorPower.cast_refl, LinearEquiv.refl_apply]
  have ht (i j : ℕ) (h : i = j) (t : TensorPower K i V) :
      TensorPower.toTensorAlgebra (TensorPower.cast K V h t) =
        TensorPower.toTensorAlgebra t := by
    subst j
    simp only [TensorPower.cast_refl, LinearEquiv.refl_apply]
  have he : H (p + (q + r)) (TensorPower.cast K V (Nat.add_assoc p q r) L) =
      H (p + (q + r)) R := by
    rw [hc]
    dsimp only [L, R]
    rw [hprod, hprod, hprod, hprod, mul_assoc]
  have hidL : P (p + q + r) L = L := LinearMap.congr_fun (hidem _) _
  have hidR : P (p + (q + r)) R = R := LinearMap.congr_fun (hidem _) _
  have heq := hsep _ _ _ he
  rw [hp, hidL, hidR] at heq
  calc
    TensorPower.toTensorAlgebra L =
        TensorPower.toTensorAlgebra (TensorPower.cast K V (Nat.add_assoc p q r) L) :=
      (ht _ _ _ _).symm
    _ = TensorPower.toTensorAlgebra R := congrArg TensorPower.toTensorAlgebra heq

theorem associativity : Specs.D05.M15.Normalization.associativity := by
  intro K V _ _ _ _ p q r x y z
  constructor
  · exact averaged_associativity (fun n => symP n) (fun n => symH n)
      (fun p q x y => (products p q x y).1) symP_eq_of_homogeneous_eq
      (fun n => (projectors_idempotent n (Nat.cast_ne_zero.mpr n.factorial_ne_zero)).1)
      p q r x y z
  · exact averaged_associativity (fun n => altP n) (fun n => extH n)
      (fun p q x y => (products p q x y).2) altP_eq_of_homogeneous_eq
      (fun n => (projectors_idempotent n (Nat.cast_ne_zero.mpr n.factorial_ne_zero)).2)
      p q r x y z

noncomputable abbrev dividedPower : dividedPower_type.{u,w} := dividedPower_value

private theorem inverse_factorials (r s : ℕ) :
    (r.factorial : K)⁻¹ * (s.factorial : K)⁻¹ =
      ((r + s).choose r : K) * ((r + s).factorial : K)⁻¹ := by
  rw [Nat.cast_add_choose K]
  have hr : (r.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr r.factorial_ne_zero
  have hs : (s.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr s.factorial_ne_zero
  have ht : ((r + s).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (r + s).factorial_ne_zero
  field_simp

theorem dividedPower_mul : Specs.D05.M15.Normalization.dividedPower_mul := by
  intro K B _ _ _ _ x r s
  simp only [dividedPower_value, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    smul_smul, ← pow_add]
  congr 1
  exact (mul_comm _ _).trans (inverse_factorials r s)

theorem dividedPower_add : Specs.D05.M15.Normalization.dividedPower_add := by
  intro K B _ _ _ _ x y h n
  simp only [dividedPower_value, h.add_pow', Finset.smul_sum,
    ← Nat.cast_smul_eq_nsmul K, smul_smul,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  apply Finset.sum_congr rfl
  intro rs hrs
  have hrs' : rs.1 + rs.2 = n := Finset.mem_antidiagonal.mp hrs
  rw [← hrs']
  congr 1
  calc
    _ = ((rs.1 + rs.2).choose rs.1 : K) * ((rs.1 + rs.2).factorial : K)⁻¹ := mul_comm _ _
    _ = (rs.1.factorial : K)⁻¹ * (rs.2.factorial : K)⁻¹ := (inverse_factorials _ _).symm
    _ = _ := mul_comm _ _

end D05.M15.Normalization
