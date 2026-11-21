import MathGenome.Internal.Specs.D05.M15.InteriorProduct
import MathGenome.Internal.D05.M15.Exterior
import MathGenome.Internal.D05.M07.Dual

/-! Signed deletion on the tensor algebra and its exterior quotient. -/
noncomputable section
namespace D05.M15.InteriorProduct
open Specs.D05.M15.InteriorProduct (tensorAction word deletion)
universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

abbrev tensorInterior := @Specs.D05.M15.InteriorProduct.tensorInterior
abbrev interior := @Specs.D05.M15.InteriorProduct.interior

private theorem action_fst (φ : Module.Dual K V) (t : _root_.TensorAlgebra K V)
    (z : _root_.TensorAlgebra K V × _root_.TensorAlgebra K V) :
    ((_root_.TensorAlgebra.lift K (tensorAction φ) t) z).1 = t * z.1 := by
  induction t using _root_.TensorAlgebra.induction generalizing z with
  | algebraMap r => simp [Algebra.algebraMap_eq_smul_one]
  | ι v => simp [_root_.TensorAlgebra.lift_ι_apply, tensorAction]
  | add a b ha hb => simp [map_add, ha, hb, add_mul]
  | mul a b ha hb =>
      rw [map_mul]
      change ((_root_.TensorAlgebra.lift K (tensorAction φ) a)
        ((_root_.TensorAlgebra.lift K (tensorAction φ) b) z)).1 = _
      rw [ha, hb, mul_assoc]

@[simp] theorem tensor_scalar (φ : Module.Dual K V) (r : K) :
    tensorInterior φ (algebraMap K (_root_.TensorAlgebra K V) r) = 0 := by
  simp [tensorInterior, Specs.D05.M15.InteriorProduct.tensorInterior,
    Algebra.algebraMap_eq_smul_one]

theorem tensor_cons (φ : Module.Dual K V) (v : V) (a : _root_.TensorAlgebra K V) :
    tensorInterior φ (_root_.TensorAlgebra.ι K v * a) =
      φ v • a - _root_.TensorAlgebra.ι K v * tensorInterior φ a := by
  change ((_root_.TensorAlgebra.lift K (tensorAction φ)
    (_root_.TensorAlgebra.ι K v * a)) (1,0)).2 = _
  rw [map_mul, _root_.TensorAlgebra.lift_ι_apply]
  change φ v • ((_root_.TensorAlgebra.lift K (tensorAction φ) a) (1,0)).1 - _ = _
  rw [action_fst, mul_one]
  rfl

@[simp] theorem tensor_one : Specs.D05.M15.InteriorProduct.tensor_one := by
  intro K V _ _ _ φ
  simpa using tensor_scalar φ 1

@[simp] theorem exterior_one : Specs.D05.M15.InteriorProduct.exterior_one := by
  intro K V _ _ _ φ
  exact CliffordAlgebra.contractLeft_one _ φ

@[simp] theorem exterior_scalar (φ : Module.Dual K V) (r : K) :
    interior φ (algebraMap K (_root_.ExteriorAlgebra K V) r) = 0 :=
  CliffordAlgebra.contractLeft_algebraMap _ φ r

theorem exterior_cons (φ : Module.Dual K V) (v : V) (a : _root_.ExteriorAlgebra K V) :
    interior φ (_root_.ExteriorAlgebra.ι K v * a) =
      φ v • a - _root_.ExteriorAlgebra.ι K v * interior φ a :=
  CliffordAlgebra.contractLeft_ι_mul φ v a

/-- Induction by scalar words and prepending generators, with linear closure. -/
theorem tensor_left_induction {P : _root_.TensorAlgebra K V → Prop}
    (hs : ∀ r, P (algebraMap K (_root_.TensorAlgebra K V) r))
    (ha : ∀ a b, P a → P b → P (a+b))
    (hc : ∀ (r : K) a, P a → P (r • a))
    (hv : ∀ v a, P a → P (_root_.TensorAlgebra.ι K v * a)) (t) : P t := by
  have h : ∀ x : _root_.TensorAlgebra K V, ∀ y, P y → P (x*y) := by
    intro x
    induction x using _root_.TensorAlgebra.induction with
    | algebraMap r => intro y hy; simpa only [← Algebra.smul_def] using hc r y hy
    | ι v => exact hv v
    | add a b ha' hb' => intro y hy; rw [add_mul]; exact ha _ _ (ha' y hy) (hb' y hy)
    | mul a b ha' hb' => intro y hy; rw [mul_assoc]; exact ha' _ (hb' y hy)
  simpa only [mul_one, map_one] using h t 1 (by simpa using hs 1)

section GeneralAlgebra
variable {A : Type*} [Ring A] [Algebra K A]

private theorem homogeneous_rule (ι : V →ₗ[K] A) (φ : Module.Dual K V)
    (D : A →ₗ[K] A) (hs : ∀ r, D (algebraMap K A r) = 0)
    (hv : ∀ v a, D (ι v * a) = φ v • a - ι v * D a)
    {p : ℕ} {a : A} (h : a ∈ LinearMap.range ι ^ p) (b : A) :
    D (a*b) = D a*b + (-1:K)^p • (a*D b) := by
  induction h using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [← Algebra.smul_def, hs]
  | add x y n hx hy ix iy => simp only [add_mul, map_add, ix, iy, smul_add]; abel
  | mem_mul m hm n x hx ih =>
      obtain ⟨v,rfl⟩ := hm
      rw [mul_assoc, hv, ih, hv]
      simp only [pow_succ, mul_neg_one, neg_smul, mul_add, sub_mul,
        smul_mul_assoc, mul_smul_comm, mul_assoc]
      abel

private theorem lowering_rule (ι : V →ₗ[K] A) (φ : Module.Dual K V)
    (D : A →ₗ[K] A) (hs : ∀ r, D (algebraMap K A r) = 0)
    (hv : ∀ v a, D (ι v * a) = φ v • a - ι v * D a)
    {n : ℕ} {a : A} (h : a ∈ LinearMap.range ι ^ n) :
    D a ∈ LinearMap.range ι ^ (n-1) ∧ (n=0 → D a=0) := by
  induction h using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [hs]
  | add x y n hx hy ix iy =>
      rw [map_add]
      exact ⟨Submodule.add_mem _ ix.1 iy.1, fun hn => by rw [ix.2 hn, iy.2 hn, add_zero]⟩
  | mem_mul m hm n x hx ih =>
      obtain ⟨v,rfl⟩ := hm
      rw [hv]
      refine ⟨?_, by omega⟩
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      apply Submodule.sub_mem
      · exact Submodule.smul_mem _ _ hx
      · cases n with
        | zero => rw [ih.2 rfl, mul_zero]; exact Submodule.zero_mem _
        | succ n =>
            rw [pow_succ']
            exact Submodule.mul_mem_mul (Set.mem_range_self v) ih.1

end GeneralAlgebra

theorem tensor_leibniz : Specs.D05.M15.InteriorProduct.tensor_leibniz := by
  intro K V _ _ _ φ p a b ha
  exact homogeneous_rule _ φ (tensorInterior φ) (tensor_scalar φ) (tensor_cons φ) ha b

theorem exterior_leibniz : Specs.D05.M15.InteriorProduct.exterior_leibniz := by
  intro K V _ _ _ φ p a b ha
  exact homogeneous_rule _ φ (interior φ) (exterior_scalar φ) (exterior_cons φ) ha b

theorem tensor_degree : Specs.D05.M15.InteriorProduct.tensor_degree := by
  intro K V _ _ _ φ p a ha
  exact (lowering_rule _ φ (tensorInterior φ) (tensor_scalar φ) (tensor_cons φ) ha).1

theorem exterior_degree : Specs.D05.M15.InteriorProduct.exterior_degree := by
  intro K V _ _ _ φ p a ha
  exact (lowering_rule _ φ (interior φ) (exterior_scalar φ) (exterior_cons φ) ha).1

theorem tensor_square_generator : Specs.D05.M15.InteriorProduct.tensor_square_generator := by
  intro K V _ _ _ φ v
  rw [tensor_cons]
  have hv : tensorInterior φ (_root_.TensorAlgebra.ι K v) = φ v • 1 := by
    simpa only [mul_one, tensor_one φ, mul_zero, sub_zero] using tensor_cons φ v 1
  rw [hv, mul_smul_comm, mul_one, sub_self]

theorem exterior_square_zero : Specs.D05.M15.InteriorProduct.exterior_square_zero := by
  intro K V _ _ _ φ a
  exact CliffordAlgebra.contractLeft_contractLeft φ a

theorem exterior_anticommutation : Specs.D05.M15.InteriorProduct.exterior_anticommutation := by
  intro K V _ _ _ φ ψ a
  exact eq_neg_iff_add_eq_zero.mp (CliffordAlgebra.contractLeft_comm φ ψ a)

theorem cartan_identity : Specs.D05.M15.InteriorProduct.cartan_identity := by
  intro K V _ _ _ φ v a
  rw [exterior_cons, sub_add_cancel]

theorem tensor_square_zero : Specs.D05.M15.InteriorProduct.tensor_square_zero := by
  intro K V _ _ _ φ a
  induction a using tensor_left_induction with
  | hs r => simp only [tensor_scalar, map_zero, add_zero]
  | ha x y hx hy => simp only [map_add, hx, hy, add_zero]
  | hc r x hx => simp only [map_smul, hx, smul_zero]
  | hv v x hx =>
      rw [tensor_cons, map_sub, map_smul, tensor_cons, hx, mul_zero, sub_zero, sub_self]

theorem tensor_anticommutation : Specs.D05.M15.InteriorProduct.tensor_anticommutation := by
  intro K V _ _ _ φ ψ a
  induction a using tensor_left_induction with
  | hs r => simp only [tensor_scalar, map_zero, add_zero]
  | ha x y hx hy =>
      simp only [map_add]
      rw [add_add_add_comm, hx, hy, add_zero]
  | hc r x hx => simp only [map_smul, ← smul_add, hx, smul_zero]
  | hv v x hx =>
      simp only [tensor_cons, map_sub, map_smul]
      calc
        _ = _root_.TensorAlgebra.ι K v *
            (tensorInterior φ (tensorInterior ψ x) + tensorInterior ψ (tensorInterior φ x)) := by
          rw [mul_add]; abel
        _ = 0 := by rw [hx, mul_zero]

theorem quotient_compatibility : Specs.D05.M15.InteriorProduct.quotient_compatibility := by
  intro K V _ _ _ φ t
  induction t using tensor_left_induction with
  | hs r => simp only [tensor_scalar, exterior_scalar, map_zero, AlgHom.commutes]
  | ha x y hx hy => simp only [map_add, hx, hy]
  | hc r x hx => simp only [map_smul, hx]
  | hv v x hx =>
      rw [tensor_cons, map_sub, map_smul, map_mul,
        _root_.TensorAlgebra.toExterior_ι, hx, map_mul,
        _root_.TensorAlgebra.toExterior_ι, exterior_cons]

theorem preserves_ideal : Specs.D05.M15.InteriorProduct.preserves_ideal := by
  intro K V _ _ _ φ t ht
  apply (D05.M15.Exterior.quotient_kernel _).mp
  rw [quotient_compatibility, (D05.M15.Exterior.quotient_kernel t).mpr ht, map_zero]

theorem descent_unique : Specs.D05.M15.InteriorProduct.descent_unique := by
  intro K V _ _ _ φ
  refine ⟨interior φ, fun t => (quotient_compatibility φ t).symm, ?_⟩
  intro D hD
  apply LinearMap.ext
  intro a
  obtain ⟨t,rfl⟩ := D05.M15.Exterior.quotient_surjective a
  exact (hD t).trans (quotient_compatibility φ t)

section Words
variable {A : Type*} [Ring A] [Algebra K A]

@[simp] theorem word_nil (ι : V →ₗ[K] A) : word ι [] = 1 := rfl
@[simp] theorem word_cons (ι : V →ₗ[K] A) (v : V) (l : List V) :
    word ι (v::l) = ι v * word ι l := rfl

private theorem deletion_cons (ι : V →ₗ[K] A) (φ : Module.Dual K V) (v : V) (l : List V) :
    deletion ι φ (v::l) = φ v • word ι l - ι v * deletion ι φ l := by
  simp only [deletion, List.length_cons, Fin.sum_univ_succ]
  simp [word, pow_succ, Finset.mul_sum, Finset.sum_neg_distrib, sub_eq_add_neg]

private theorem word_rule (ι : V →ₗ[K] A) (φ : Module.Dual K V)
    (D : A →ₗ[K] A) (h1 : D 1 = 0)
    (hv : ∀ v a, D (ι v * a) = φ v • a - ι v * D a) (l : List V) :
    D (word ι l) = deletion ι φ l := by
  induction l with
  | nil => simpa [deletion] using h1
  | cons v l ih => rw [word_cons, hv, ih, deletion_cons]

end Words

theorem tensor_word : Specs.D05.M15.InteriorProduct.tensor_word := by
  intro K V _ _ _ φ l
  exact word_rule _ φ _ (tensor_one φ) (tensor_cons φ) l

theorem exterior_word : Specs.D05.M15.InteriorProduct.exterior_word := by
  intro K V _ _ _ φ l
  exact word_rule _ φ _ (exterior_one φ) (exterior_cons φ) l

theorem tensor_power_formula : Specs.D05.M15.InteriorProduct.tensor_power_formula := by
  intro K V _ _ _ φ p x
  rw [D05.M15.TensorAlgebra.elementary_word]
  simpa only [word, List.map_ofFn, Function.comp_def] using tensor_word φ (List.ofFn x)

theorem exterior_power_formula : Specs.D05.M15.InteriorProduct.exterior_power_formula := by
  intro K V _ _ _ φ p x
  rw [_root_.ExteriorAlgebra.ιMulti_apply]
  simpa only [word, List.map_ofFn, Function.comp_def] using exterior_word φ (List.ofFn x)

abbrev higherInterior := @Specs.D05.M15.InteriorProduct.higherInterior

theorem higher_generator : Specs.D05.M15.InteriorProduct.higher_generator := by
  intro K V _ _ _ φ
  change MulOpposite.unop (Specs.D05.M15.InteriorProduct.higherInteriorOpp
    (_root_.ExteriorAlgebra.ι K φ)) = _
  rw [Specs.D05.M15.InteriorProduct.higherInteriorOpp, _root_.ExteriorAlgebra.lift_ι_apply]
  rfl

theorem higher_product : Specs.D05.M15.InteriorProduct.higher_product := by
  intro K V _ _ _ α β
  change MulOpposite.unop (Specs.D05.M15.InteriorProduct.higherInteriorOpp (α*β)) = _
  rw [map_mul]
  rfl

theorem higher_unit : Specs.D05.M15.InteriorProduct.higher_unit := by
  intro K V _ _ _
  change MulOpposite.unop (Specs.D05.M15.InteriorProduct.higherInteriorOpp 1) = _
  rw [map_one]
  rfl

@[simp] theorem exterior_generator (φ : Module.Dual K V) (v : V) :
    interior φ (_root_.ExteriorAlgebra.ι K v) = algebraMap K _ (φ v) :=
  CliffordAlgebra.contractLeft_ι _ φ v

theorem higher_guard : Specs.D05.M15.InteriorProduct.higher_guard := by
  intro K V _ _ _ φ ψ v w hφv hφw hψv hψw
  dsimp only
  rw [higher_product, higher_generator, higher_generator]
  simp only [LinearMap.comp_apply, exterior_cons, exterior_generator,
    hφv, hφw, hψw, one_smul, map_one, map_zero,
    zero_mul, mul_zero, sub_zero, exterior_one ψ]
  simp only [one_ne_zero, ne_eq, not_false_eq_true, and_self]

theorem higher_word : Specs.D05.M15.InteriorProduct.higher_word := by
  intro K V _ _ _ l a
  induction l generalizing a with
  | nil => rw [word_nil, higher_unit]; rfl
  | cons φ l ih =>
      rw [word_cons, higher_product, higher_generator, LinearMap.comp_apply, ih]
      rfl

theorem higher_counterexample : Specs.D05.M15.InteriorProduct.higher_counterexample := by
  intro K _
  let φ := LinearMap.fst K K K
  let ψ := LinearMap.snd K K K
  refine ⟨_root_.ExteriorAlgebra.ι K φ * _root_.ExteriorAlgebra.ι K ψ,
    _root_.ExteriorAlgebra.ι K (1,0), _root_.ExteriorAlgebra.ι K (0,1), ?_⟩
  exact (higher_guard φ ψ (1,0) (0,1) rfl rfl rfl rfl).2.2.2

/-- Augmentation of the exterior algebra: projection to its scalar part. -/
def scalarPart : _root_.ExteriorAlgebra K V →ₐ[K] K :=
  _root_.ExteriorAlgebra.lift K ⟨0, by simp⟩

private theorem iota_succ (n : ℕ) (x : Fin (n+1) → V) :
    _root_.ExteriorAlgebra.ιMulti K (n+1) x =
      _root_.ExteriorAlgebra.ι K (x 0) *
        _root_.ExteriorAlgebra.ιMulti K n (fun i => x i.succ) := by
  simp only [_root_.ExteriorAlgebra.ιMulti_apply, List.ofFn_succ, List.prod_cons]

/-- The deletion formula with each remaining tuple indexed by `succAbove`. -/
theorem exterior_delete (φ : Module.Dual K V) (n : ℕ) (x : Fin (n+1) → V) :
    interior φ (_root_.ExteriorAlgebra.ιMulti K (n+1) x) =
      ∑ j : Fin (n+1), ((-1:K)^(j:ℕ) * φ (x j)) •
        _root_.ExteriorAlgebra.ιMulti K n (fun i => x (j.succAbove i)) := by
  induction n with
  | zero =>
    rw [iota_succ]
    simp [_root_.ExteriorAlgebra.ιMulti_zero_apply, exterior_generator, Algebra.algebraMap_eq_smul_one]
  | succ n ih =>
    rw [iota_succ, exterior_cons, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.zero_succAbove]
    rw [sub_eq_add_neg]
    congr 1
    simp only [Fin.val_succ, pow_succ, mul_neg_one, neg_mul, neg_smul,
      Finset.sum_neg_distrib, Finset.mul_sum, mul_smul_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [iota_succ]
    simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]

/-- Contracting equal-length elementary wedges gives the unnormalized determinant. -/
theorem scalar_contraction_elementary (n : ℕ)
    (f : Fin n → Module.Dual K V) (x : Fin n → V) :
    scalarPart (higherInterior (_root_.ExteriorAlgebra.ιMulti K n f)
      (_root_.ExteriorAlgebra.ιMulti K n x)) =
        Matrix.det (Matrix.of (fun i j => f i (x j))) := by
  induction n with
  | zero =>
    simp only [_root_.ExteriorAlgebra.ιMulti_zero_apply]
    rw [higher_unit]
    simpa only [LinearMap.id_apply, Matrix.det_isEmpty] using
      map_one (scalarPart (K := K) (V := V))
  | succ n ih =>
    rw [iota_succ, higher_product, higher_generator, LinearMap.comp_apply, exterior_delete]
    simp only [map_sum, map_smul, ih, smul_eq_mul]
    simpa only [Matrix.submatrix, Matrix.of_apply] using
      (Matrix.det_succ_row_zero (Matrix.of (fun i j => f i (x j)))).symm

/-- The scalar obtained by full contraction agrees with Mathlib's determinant
pairing, whose matrix is the transpose of the paper's evaluation matrix. -/
theorem scalar_contraction_pairing (n : ℕ)
    (α : ⋀[K]^n (Module.Dual K V)) (u : ⋀[K]^n V) :
    scalarPart (higherInterior (α : _root_.ExteriorAlgebra K (Module.Dual K V))
      (u : _root_.ExteriorAlgebra K V)) = exteriorPower.pairingDual K V n α u := by
  let C : (⋀[K]^n (Module.Dual K V)) →ₗ[K] Module.Dual K (⋀[K]^n V) :=
    ((higherInterior.compr₂ scalarPart.toLinearMap).compl₂
      (Submodule.subtype (⋀[K]^n V))).comp
      (Submodule.subtype (⋀[K]^n (Module.Dual K V)))
  have h : C = exteriorPower.pairingDual K V n := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro f
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    change scalarPart (higherInterior (_root_.ExteriorAlgebra.ιMulti K n f)
      (_root_.ExteriorAlgebra.ιMulti K n x)) = _
    simp only [LinearMap.compAlternatingMap_apply]
    rw [exteriorPower.pairingDual_ιMulti_ιMulti, scalar_contraction_elementary]
    exact (Matrix.det_transpose _).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h α) u

/-- Higher contraction lowers a homogeneous degree by the degree of its covector. -/
theorem higher_degree (r : ℕ) (α : _root_.ExteriorAlgebra K (Module.Dual K V))
    (hα : α ∈ ⋀[K]^r (Module.Dual K V)) :
    ∀ (q : ℕ) (u : _root_.ExteriorAlgebra K V), u ∈ ⋀[K]^(r+q) V →
      higherInterior α u ∈ ⋀[K]^q V := by
  induction hα using Submodule.pow_induction_on_left' with
  | algebraMap c =>
    intro q u hu
    rw [Algebra.algebraMap_eq_smul_one, map_smul, higher_unit]
    exact Submodule.smul_mem _ c (by simpa only [Nat.zero_add, LinearMap.id_apply] using hu)
  | add a b n ha hb ia ib =>
    intro q u hu
    simp only [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ (ia q u hu) (ib q u hu)
  | mem_mul m hm n a ha ih =>
    obtain ⟨φ, rfl⟩ := hm
    intro q u hu
    rw [higher_product, higher_generator, LinearMap.comp_apply]
    apply ih q
    apply exterior_degree φ (n+q) u
    convert hu using 1
    congr 1
    omega

/-- Adjointness to left multiplication under the determinant pairing. -/
theorem higher_pairing : Specs.D05.M15.InteriorProduct.higher_pairing := by
  intro K V _ _ _ _ r q α β u
  let v : ⋀[K]^q V := ⟨higherInterior α u, higher_degree (K := K) (V := V) r
    (α : _root_.ExteriorAlgebra K (Module.Dual K V)) α.property q
    (u : _root_.ExteriorAlgebra K V) u.property⟩
  refine ⟨v, rfl, ?_⟩
  rw [← scalar_contraction_pairing, ← scalar_contraction_pairing]
  change scalarPart (higherInterior (β : _root_.ExteriorAlgebra K (Module.Dual K V))
    (higherInterior (α : _root_.ExteriorAlgebra K (Module.Dual K V))
      (u : _root_.ExteriorAlgebra K V))) =
    scalarPart (higherInterior ((α : _root_.ExteriorAlgebra K (Module.Dual K V)) *
      (β : _root_.ExteriorAlgebra K (Module.Dual K V))) (u : _root_.ExteriorAlgebra K V))
  rw [higher_product]
  rfl

end D05.M15.InteriorProduct
