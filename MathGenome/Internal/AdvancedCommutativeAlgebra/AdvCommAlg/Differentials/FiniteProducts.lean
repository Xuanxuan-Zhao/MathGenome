import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Universal
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.FiniteProducts

/-! Finite products of algebras (KD-20).
Coordinate idempotents cut out coefficient summands. The universal property
supplies inclusions from the factor differential modules, and their finite sum
is inverse to the map induced by projections. All sums also admit empty index
sets, and no nontriviality hypothesis is used. -/
namespace AdvCommAlg.Differentials

universe u v w z
noncomputable section
open scoped BigOperators
open scoped Specs.AdvCommAlg.Differentials.ProductDifferentials

namespace FiniteProduct

variable {A : Type u} [CommRing A]
variable {ι : Type v} {B : ι → Type w} [∀ i, CommRing (B i)]
variable [∀ i, Algebra A (B i)]

/-- Every derivation kills idempotents, in any characteristic. -/
lemma derivation_idempotent {R S M : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [Module S M]
    (D : Derivation R S M) {e : S} (he : e * e = e) : D e = 0 := by
  have h : D e = e • D e + e • D e := by
    simpa only [he] using D.leibniz e e
  have hh := congrArg (fun x : M => e • x) h
  simp only [smul_add, smul_smul, he] at hh
  have hz : e • D e = 0 := add_eq_left.mp hh.symm
  simpa only [hz, add_zero] using h

variable (B)
variable [DecidableEq ι]

/-- A coordinate idempotent. -/
def coordinateIdempotent (i : ι) : ∀ j, B j := Pi.single i 1

lemma coordinateIdempotent_mul (i : ι) :
    coordinateIdempotent B i * coordinateIdempotent B i = coordinateIdempotent B i := by
  simp [coordinateIdempotent, ← Pi.single_mul]

variable {B}
variable (M : Type z) [AddCommGroup M] [Module (∀ i, B i) M]

/-- The summand of a module supported on one coordinate. -/
def supported (i : ι) : Submodule (∀ j, B j) M where
  carrier := {m | coordinateIdempotent B i • m = m}
  zero_mem' := smul_zero _
  add_mem' {x} {y} hx hy := by
    change coordinateIdempotent B i • x = x at hx
    change coordinateIdempotent B i • y = y at hy
    change coordinateIdempotent B i • (x + y) = x + y
    rw [smul_add, hx, hy]
  smul_mem' b m hm := by
    change coordinateIdempotent B i • b • m = b • m
    rw [smul_comm, hm]

instance supportedSMul (i : ι) : SMul (B i) (supported (B := B) M i) where
  smul c m := ⟨Pi.single i c • m.val, by
    change coordinateIdempotent B i • Pi.single i c • m.val = Pi.single i c • m.val
    rw [smul_smul]
    simp [coordinateIdempotent, ← Pi.single_mul]⟩

lemma supported_eval_smul (i : ι) (b : ∀ j, B j) (m : supported (B := B) M i) :
    (b i • m : supported (B := B) M i) = b • m := by
  apply Subtype.ext
  change Pi.single i (b i) • m.val = b • m.val
  rw [← m.prop, smul_smul, smul_smul]
  congr 1
  ext j
  by_cases h : j = i
  · subst j; simp [coordinateIdempotent]
  · simp [coordinateIdempotent, Pi.single_eq_of_ne h]

instance supportedModule (i : ι) : Module (B i) (supported (B := B) M i) :=
  Function.Surjective.moduleLeft (Pi.evalRingHom B i) (Function.surjective_eval i)
    (supported_eval_smul M i)

instance supportedTower (i : ι) [Module A M] [IsScalarTower A (∀ j, B j) M] :
    IsScalarTower A (B i) (supported (B := B) M i) where
  smul_assoc a c m := by
    apply Subtype.ext
    change Pi.single i (a • c) • m.val = a • (Pi.single i c • m.val)
    rw [Pi.single_smul, smul_assoc]

variable [Module A M] [IsScalarTower A (∀ j, B j) M]

omit [IsScalarTower A (∀ j, B j) M] in
lemma derivation_single_supported (D : Derivation A (∀ j, B j) M) (i : ι) (x : B i) :
    coordinateIdempotent B i • D (Pi.single i x) = D (Pi.single i x) := by
  have he := derivation_idempotent D (coordinateIdempotent_mul B i)
  have hx : coordinateIdempotent B i * Pi.single i x = Pi.single i x := by
    simp [coordinateIdempotent, ← Pi.single_mul]
  have h := D.leibniz (coordinateIdempotent B i) (Pi.single i x)
  rw [hx, he, smul_zero, add_zero] at h
  exact h.symm

/-- Restrict a derivation to the i-th coordinate, with values in its supported summand. -/
def singleDerivation (D : Derivation A (∀ j, B j) M) (i : ι) :
    Derivation A (B i) (supported (B := B) M i) where
  toFun x := ⟨D (Pi.single i x), derivation_single_supported M D i x⟩
  map_add' x y := by
    apply Subtype.ext
    change D (Pi.single i (x + y)) = D (Pi.single i x) + D (Pi.single i y)
    rw [Pi.single_add, map_add]
  map_smul' a x := by
    apply Subtype.ext
    change D (Pi.single i (a • x)) = a • D (Pi.single i x)
    rw [Pi.single_smul, D.map_smul]
  map_one_eq_zero' := by
    apply Subtype.ext
    exact derivation_idempotent D (coordinateIdempotent_mul B i)
  leibniz' x y := by
    apply Subtype.ext
    change D (Pi.single i (x * y)) =
      Pi.single i x • D (Pi.single i y) + Pi.single i y • D (Pi.single i x)
    rw [Pi.single_mul, D.leibniz]

/-- The inclusion of the differential module of a factor into that of the product. -/
def coordinateLift (i : ι) :
    KaehlerDifferential A (B i) →ₗ[∀ j, B j] KaehlerDifferential A (∀ j, B j) where
  toFun x := (singleDerivation _ (KaehlerDifferential.D A (∀ j, B j)) i).liftKaehlerDifferential x
  map_add' x y := by simp only [map_add, Submodule.coe_add]
  map_smul' b x := by
    change ((singleDerivation _ (KaehlerDifferential.D A (∀ j, B j)) i).liftKaehlerDifferential
      (b i • x) : KaehlerDifferential A (∀ j, B j)) = _
    rw [map_smul, supported_eval_smul]
    rfl

@[simp]
lemma coordinateLift_D (i : ι) (x : B i) :
    coordinateLift (A := A) i (KaehlerDifferential.D A (B i) x) =
      KaehlerDifferential.D A (∀ j, B j) (Pi.single i x) := by
  change ((singleDerivation _ (KaehlerDifferential.D A (∀ j, B j)) i).liftKaehlerDifferential
    (KaehlerDifferential.D A (B i) x) : KaehlerDifferential A (∀ j, B j)) = _
  rw [Derivation.liftKaehlerDifferential_comp_D]
  rfl

instance componentTower (i : ι) :
    IsScalarTower A (∀ j, B j) (KaehlerDifferential A (B i)) where
  smul_assoc a b x := by
    change (a • b i) • x = a • (b i • x)
    exact smul_assoc a (b i) x

/-- The coordinatewise derivation of the product algebra. -/
def productDerivation : Derivation A (∀ i, B i) (∀ i, KaehlerDifferential A (B i)) where
  toFun b i := KaehlerDifferential.D A (B i) (b i)
  map_add' b c := by ext i; exact map_add _ _ _
  map_smul' a b := by
    ext i
    exact (KaehlerDifferential.D A (B i)).map_smul a (b i)
  map_one_eq_zero' := by ext i; exact (KaehlerDifferential.D A (B i)).map_one_eq_zero
  leibniz' b c := by
    ext i
    exact (KaehlerDifferential.D A (B i)).leibniz (b i) (c i)

/-- The map induced by the projections. -/
def projectionMap : KaehlerDifferential A (∀ i, B i) →ₗ[∀ i, B i]
    (∀ i, KaehlerDifferential A (B i)) :=
  (productDerivation (A := A) (B := B)).liftKaehlerDifferential

omit [DecidableEq ι] in
@[simp]
lemma projectionMap_D (b : ∀ i, B i) (i : ι) :
    projectionMap (KaehlerDifferential.D A (∀ i, B i) b) i =
      KaehlerDifferential.D A (B i) (b i) := by
  change (productDerivation (A := A) (B := B)).liftKaehlerDifferential
    (KaehlerDifferential.D A (∀ i, B i) b) i = _
  rw [Derivation.liftKaehlerDifferential_comp_D]
  rfl

lemma projectionMap_coordinateLift (i : ι) (x : KaehlerDifferential A (B i)) :
    projectionMap (coordinateLift (A := A) i x) = Pi.single i x := by
  have hx : x ∈ Submodule.span (B i) (Set.range (KaehlerDifferential.D A (B i))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    rw [coordinateLift_D]
    ext j
    rw [projectionMap_D]
    by_cases h : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne h]
  | zero => simp
  | add x y hx hy ex ey => simp only [map_add, ex, ey, Pi.single_add]
  | smul c x hx ex =>
    have hc : c • x = (Pi.single i c : ∀ j, B j) • x := by
      change c • x = (Pi.single i c i) • x
      simp
    conv_lhs => rw [hc, map_smul, map_smul, ex]
    ext j
    by_cases h : j = i
    · subst j
      simp only [Pi.smul_apply', Pi.single_eq_same]
    · simp only [Pi.smul_apply', Pi.single_eq_of_ne h, smul_zero]

variable [Fintype ι]

/-- Assemble the factor inclusions by finite summation. -/
def sumLift : (∀ i, KaehlerDifferential A (B i)) →ₗ[∀ i, B i]
    KaehlerDifferential A (∀ i, B i) where
  toFun x := ∑ i, coordinateLift (A := A) i (x i)
  map_add' x y := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' b x := by
    change (∑ i, coordinateLift (A := A) i (b • x i)) =
      b • ∑ i, coordinateLift (A := A) i (x i)
    simp only [map_smul, Finset.smul_sum]

lemma sumLift_projectionMap :
    (sumLift (A := A) (B := B)).comp projectionMap = LinearMap.id := by
  apply Derivation.liftKaehlerDifferential_unique
  ext b
  change sumLift (projectionMap (KaehlerDifferential.D A (∀ i, B i) b)) =
    KaehlerDifferential.D A (∀ i, B i) b
  change (∑ i, coordinateLift (A := A) i
    (projectionMap (KaehlerDifferential.D A (∀ i, B i) b) i)) = _
  simp only [projectionMap_D, coordinateLift_D]
  rw [← map_sum, LinearMap.sum_single_apply]

lemma projectionMap_sumLift :
    (projectionMap (A := A) (B := B)).comp sumLift = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change projectionMap (∑ i, coordinateLift (A := A) i (x i)) = x
  simp only [map_sum, projectionMap_coordinateLift, LinearMap.sum_single_apply]

end FiniteProduct

/-- The finite product theorem for canonical relative differentials. -/
theorem finite_products : Specs.AdvCommAlg.Differentials.finiteProducts.{u,v,w} := by
  intro A ι B _ _ _ _
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let p := FiniteProduct.projectionMap (A := A) (B := B)
  let q := FiniteProduct.sumLift (A := A) (B := B)
  let e : KaehlerDifferential A (∀ i, B i) ≃ₗ[∀ i, B i]
      (∀ i, KaehlerDifferential A (B i)) :=
    { p with
      invFun := q
      left_inv := fun x => congrArg (fun L : _ →ₗ[∀ i, B i] _ => L x)
        FiniteProduct.sumLift_projectionMap
      right_inv := fun x => congrArg (fun L : _ →ₗ[∀ i, B i] _ => L x)
        FiniteProduct.projectionMap_sumLift }
  exact ⟨e, FiniteProduct.projectionMap_D⟩

end
end AdvCommAlg.Differentials
