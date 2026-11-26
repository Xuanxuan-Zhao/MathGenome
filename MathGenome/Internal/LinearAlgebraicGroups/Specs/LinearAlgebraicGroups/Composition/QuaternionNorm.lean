import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.OrthogonalDoubling
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.AlternativeIdentities
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.ReducedNorm
import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Norm.Defs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.Basic.Real.Basic

namespace LinearAlgebraicGroups.Composition.QuaternionSpecification

open scoped Matrix TensorProduct
open AdjointSpecification Specification

set_option linter.checkUnivs false

universe u v w

section Cyclic

variable {k : Type u} {D : Type v} [Field k] [CommRing D] [Algebra k D]

/-- The regular cyclic representation with coordinates in the quadratic algebra. -/
def cyclicMatrix (σ : D ≃ₐ[k] D) (param : k) (x y : D) : Matrix (Fin 2) (Fin 2) D :=
  !![x, algebraMap k D param * y; σ y, σ x]

/-- The associative cyclic algebra in its regular cyclic representation. -/
def cyclicAlgebra (σ : D ≃ₐ[k] D) (hσ : Function.Involutive σ) (param : k) :
    Subalgebra k (Matrix (Fin 2) (Fin 2) D) where
  carrier := {M | ∃ x y, cyclicMatrix σ param x y = M}
  zero_mem' := ⟨0, 0, by ext i j; fin_cases i <;> fin_cases j <;> simp [cyclicMatrix]⟩
  add_mem' := by
    rintro _ _ ⟨x, y, rfl⟩ ⟨z, t, rfl⟩
    refine ⟨x + z, y + t, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cyclicMatrix, mul_add]
  one_mem' := ⟨1, 0, by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cyclicMatrix]⟩
  mul_mem' := by
    rintro _ _ ⟨x, y, rfl⟩ ⟨z, t, rfl⟩
    refine ⟨x * z + algebraMap k D param * (σ t * y), t * x + y * σ z, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cyclicMatrix, Matrix.mul_apply, Fin.sum_univ_two, hσ z, hσ t] <;> ring
  algebraMap_mem' := by
    intro a
    refine ⟨algebraMap k D a, 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cyclicMatrix, Matrix.algebraMap_matrix_apply]

/-- The element (x+yj) of the cyclic algebra. -/
def cyclicPair (σ : D ≃ₐ[k] D) (hσ : Function.Involutive σ) (param : k) (x y : D) :
    cyclicAlgebra σ hσ param :=
  ⟨cyclicMatrix σ param x y, x, y, rfl⟩

def cyclicAlgebraType :=
  ∀ {k : Type u} {D : Type v} [Field k] [CommRing D] [Algebra k D]
    (σ : D ≃ₐ[k] D) (_ : Function.Involutive σ) (_ : k),
    Subalgebra k (Matrix (Fin 2) (Fin 2) D)

def cyclicPairType :=
  ∀ {k : Type u} {D : Type v} [Field k] [CommRing D] [Algebra k D]
    (σ : D ≃ₐ[k] D) (hσ : Function.Involutive σ) (param : k), D → D → cyclicAlgebra σ hσ param

def cyclicProduct : Prop :=
  ∀ {k : Type u} {D : Type v} [Field k] [CommRing D] [Algebra k D]
    (σ : D ≃ₐ[k] D) (hσ : Function.Involutive σ) (param : k) (x y z t : D),
    cyclicPair σ hσ param x y * cyclicPair σ hσ param z t =
      cyclicPair σ hσ param (x * z + param • (σ t * y)) (t * x + y * σ z)

def cyclicGenerators : Prop :=
  ∀ {k : Type u} {D : Type v} [Field k] [CommRing D] [Algebra k D]
    (σ : D ≃ₐ[k] D) (hσ : Function.Involutive σ) (param : k),
    (cyclicPair σ hσ param 1 0 = 1) ∧
    ((cyclicPair σ hσ param 0 1) ^ 2 = algebraMap k (cyclicAlgebra σ hσ param) param) ∧
    (∀ x : D, cyclicPair σ hσ param 0 1 * cyclicPair σ hσ param x 0 =
      cyclicPair σ hσ param (σ x) 0 * cyclicPair σ hσ param 0 1) ∧
    (∀ q : cyclicAlgebra σ hσ param, ∃! xy : D × D, cyclicPair σ hσ param xy.1 xy.2 = q)

def conjugationAutomorphism : Prop :=
  ∀ {k : Type u} {D : Type v} [Field k] [CommRing D] [Algebra k D]
    {n : QuadraticForm k D}, FieldNormConditions n →
    ∃ σ : D ≃ₐ[k] D, Function.Involutive σ ∧ ∀ x, σ x = conjugate n x

/-- The orthogonal sum of the quadratic norm on the two cyclic coordinates. -/
def cyclicNorm (n : QuadraticForm k D) (σ : D ≃ₐ[k] D)
    (hσ : Function.Involutive σ) (param : k) :
    QuadraticForm k (cyclicAlgebra σ hσ param) :=
  let row (i j : Fin 2) : cyclicAlgebra σ hσ param →ₗ[k] D :=
    { toFun := fun q => (q : Matrix (Fin 2) (Fin 2) D) i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  n.comp (row 0 0) - param • n.comp (σ.symm.toLinearMap.comp (row 1 0))

def cyclicNormType :=
  ∀ {k : Type u} {D : Type v} [Field k] [CommRing D] [Algebra k D]
    (_ : QuadraticForm k D) (σ : D ≃ₐ[k] D) (hσ : Function.Involutive σ) (param : k),
    QuadraticForm k (cyclicAlgebra σ hσ param)

def cyclicNormOnPairs : Prop :=
  ∀ {k : Type u} {D : Type v} [Field k] [CommRing D] [Algebra k D]
    (σ : D ≃ₐ[k] D) (hσ : Function.Involutive σ) (param : k) (n : QuadraticForm k D) (x y : D),
    cyclicNorm n σ hσ param (cyclicPair σ hσ param x y) = n x - param * n y

def matrixSplitting : Prop :=
  ∀ {k : Type u} {D : Type v} [Field k] [CommRing D] [Algebra k D] [Algebra.Etale k D]
    {n : QuadraticForm k D} (_ : FieldNormConditions n) (_ : Module.finrank k D = 2)
    (σ : D ≃ₐ[k] D) (hσ : Function.Involutive σ) (_ : ∀ x, σ x = conjugate n x)
    (param : k) (_ : param ≠ 0),
    let K := SeparableClosure k
    ∃ e : K ⊗[k] cyclicAlgebra σ hσ param ≃ₐ[K] Matrix (Fin 2) (Fin 2) K,
      ∀ q : cyclicAlgebra σ hσ param,
        (e (1 ⊗ₜ[k] q)).det = algebraMap k K (cyclicNorm n σ hσ param q)

def quaternionNormAndSplitting : Prop :=
  ∀ {k : Type u} {D : Type v} [Field k] [CommRing D] [Algebra k D] [Algebra.Etale k D]
    {n : QuadraticForm k D} (_ : FieldNormConditions n) (_ : Module.finrank k D = 2)
    (σ : D ≃ₐ[k] D) (hσ : Function.Involutive σ) (_ : ∀ x, σ x = conjugate n x)
    (param : k) (_ : param ≠ 0),
    let Q := cyclicAlgebra σ hσ param
    let N := cyclicNorm n σ hσ param
    ∃ hQ : RM03.CSA.IsCentralSimple k Q,
      Module.finrank k Q = 4 ∧ RM03.CSA.degree k Q = 2 ∧
      FieldNormConditions N ∧ (∀ q : Q, RM03.CSA.reducedNorm hQ q = N q) ∧
      (isotropic N ↔ Nonempty (Q ≃ₐ[k] Matrix (Fin 2) (Fin 2) k))

def quaternionNoncommutative : Prop :=
  ∀ {k : Type u} {Q : Type v} [Field k] [Ring Q] [Algebra k Q],
    RM03.CSA.IsCentralSimple k Q → RM03.CSA.degree k Q = 2 → ∃ x y : Q, x * y ≠ y * x

def quadraticNormIsAlgebraNorm : Prop :=
  ∀ {k : Type u} {D : Type v} [Field k] [CommRing D] [Algebra k D] [Algebra.Etale k D]
    {n : QuadraticForm k D}, FieldNormConditions n → Module.finrank k D = 2 →
    ∀ x : D, n x = Algebra.norm k x

/-- In the local cyclic presentation the field part uses the ordinary quadratic
field norm, and the element normalizing the quadratic field has norm `-param`. -/
def localCyclicNorm : Prop :=
  ∀ {k : Type u} {D : Type v} {B : Type w}
    [Field k] [Field D] [Algebra k D] [Algebra.Etale k D] [Ring B] [Algebra k B]
    {n : QuadraticForm k D} (_ : FieldNormConditions n) (_ : Module.finrank k D = 2)
    (σ : D ≃ₐ[k] D) (hσ : Function.Involutive σ) (_ : ∀ x, σ x = conjugate n x)
    (param : k) (_ : param ≠ 0)
    (e : cyclicAlgebra σ hσ param ≃ₐ[k] B) (hB : RM03.CSA.IsCentralSimple k B),
    (∀ x y : D, RM03.CSA.reducedNorm hB (e (cyclicPair σ hσ param x y)) =
      Algebra.norm k x - param * Algebra.norm k y) ∧
    RM03.CSA.reducedNorm hB (e (cyclicPair σ hσ param 0 1)) = -param

/-- Reduced norm in a cyclic presentation over a separable quadratic field. -/
def localQuadraticFieldCyclicNorm : Prop :=
  ∀ {k : Type u} {D : Type v} {B : Type w}
    [Field k] [Field D] [Algebra k D] [Algebra.IsSeparable k D] [Ring B] [Algebra k B],
    Module.finrank k D = 2 →
    ∀ (σ : D ≃ₐ[k] D), σ ≠ AlgEquiv.refl → ∀ (param : k), param ≠ 0 →
    ∃ hσ : Function.Involutive σ,
      ∀ (e : cyclicAlgebra σ hσ param ≃ₐ[k] B) (hB : RM03.CSA.IsCentralSimple k B),
        (∀ x y : D, RM03.CSA.reducedNorm hB (e (cyclicPair σ hσ param x y)) =
          Algebra.norm k x - param * Algebra.norm k y) ∧
        RM03.CSA.reducedNorm hB (e (cyclicPair σ hσ param 0 1)) = -param

end Cyclic

section Models

variable {k : Type u} [Field k]

/-- The scalar double with generator of square `α`. -/
abbrev scalarDouble (α : k) := QuadraticAlgebra k α 0

/-- The norm on the scalar double in the basis `1, ω`. -/
def scalarDoubleNorm (α : k) : QuadraticForm k (scalarDouble α) :=
  (QuadraticMap.sq (R := k)).comp (QuadraticAlgebra.reₗ α 0) -
    α • (QuadraticMap.sq (R := k)).comp (QuadraticAlgebra.imₗ α 0)

/-- The scalar double involution fixes scalars and negates its generator. -/
def scalarDoubleInvolution (α : k) : scalarDouble α ≃ₐ[k] scalarDouble α :=
  let f := QuadraticAlgebra.lift
    (a := α) (b := 0) ⟨-QuadraticAlgebra.omega, by
      simp [QuadraticAlgebra.omega_mul_omega_eq_add]⟩
  have hf : f (QuadraticAlgebra.omega : scalarDouble α) = -QuadraticAlgebra.omega := by
    simp [f]
  have hff : f.comp f = AlgHom.id k (scalarDouble α) :=
    QuadraticAlgebra.algHom_ext (by simp [hf])
  AlgEquiv.ofAlgHom f f hff hff

theorem scalarDoubleInvolution_involutive (α : k) :
    Function.Involutive (scalarDoubleInvolution α) :=
  (scalarDoubleInvolution α).symm_apply_apply

/-- The second, associative double, realized in the cyclic coordinates. -/
abbrev quaternionModel (α β : k) :=
  cyclicAlgebra (scalarDoubleInvolution α) (scalarDoubleInvolution_involutive α) β

abbrev quaternionModelPair (α β : k) :=
  cyclicPair (scalarDoubleInvolution α) (scalarDoubleInvolution_involutive α) β

def quaternionModelNorm (α β : k) : QuadraticForm k (quaternionModel α β) :=
  cyclicNorm (scalarDoubleNorm α) (scalarDoubleInvolution α)
    (scalarDoubleInvolution_involutive α) β

/-- The ordered pair realization of an external Cayley–Dickson double. -/
def CayleyDickson {A : Type v} [Ring A] [Algebra k A]
    (_n : QuadraticForm k A) (_γ : k) := A × A

namespace CayleyDickson

variable {A : Type v} [Ring A] [Algebra k A] (n : QuadraticForm k A) (γ : k)

instance : AddCommGroup (CayleyDickson n γ) := inferInstanceAs (AddCommGroup (A × A))
instance : Module k (CayleyDickson n γ) := inferInstanceAs (Module k (A × A))

def pair (x y : A) : CayleyDickson n γ := (x, y)
def fst (x : CayleyDickson n γ) : A := (show A × A from x).1
def snd (x : CayleyDickson n γ) : A := (show A × A from x).2

instance : Mul (CayleyDickson n γ) :=
  ⟨fun x y => pair n γ
    (fst n γ x * fst n γ y + γ • (conjugate n (snd n γ y) * snd n γ x))
    (snd n γ y * fst n γ x + snd n γ x * conjugate n (fst n γ y))⟩

instance : Zero (CayleyDickson n γ) := inferInstanceAs (Zero (A × A))

def norm : QuadraticForm k (CayleyDickson n γ) :=
  n.comp (show CayleyDickson n γ →ₗ[k] A from LinearMap.fst k A A) -
    γ • n.comp (show CayleyDickson n γ →ₗ[k] A from LinearMap.snd k A A)

/-- The ring operations on the external double when conjugation fixes the unit. -/
abbrev ring (hne : conjugate n 1 = 1) : NonAssocRing (CayleyDickson n γ) :=
  { (CayleyDickson.instAddCommGroup n γ) with
    one := pair n γ 1 0
    natCast := fun i => pair n γ i 0
    natCast_zero := by
      change ((↑(0 : ℕ) : A), (0 : A)) = (0, 0)
      simp
    natCast_succ := fun i => by
      change ((↑(i + 1) : A), (0 : A)) = ((i : A) + 1, 0 + 0)
      simp
    intCast := fun i => pair n γ i 0
    intCast_ofNat := fun i => by
      change ((↑(i : ℤ) : A), (0 : A)) = ((i : A), 0)
      simp
    intCast_negSucc := fun i => by
      change ((↑(Int.negSucc i) : A), (0 : A)) = (-(↑(i + 1) : A), -0)
      simp
    zero_mul := fun x => by
      change (0 * fst n γ x + γ • (conjugate n (snd n γ x) * 0),
        snd n γ x * 0 + 0 * conjugate n (fst n γ x)) = ((0 : A), (0 : A))
      simp
    mul_zero := fun x => by
      change (fst n γ x * 0 + γ • (conjugate n 0 * snd n γ x),
        0 * fst n γ x + snd n γ x * conjugate n 0) = ((0 : A), (0 : A))
      simp
    one_mul := fun x => by
      change (1 * fst n γ x + γ • (conjugate n (snd n γ x) * 0),
        snd n γ x * 1 + 0 * conjugate n (fst n γ x)) = (show A × A from x)
      simpa [fst, snd] using (Prod.eta (show A × A from x))
    mul_one := fun x => by
      change (fst n γ x * 1 + γ • (conjugate n 0 * snd n γ x),
        0 * fst n γ x + snd n γ x * conjugate n 1) = (show A × A from x)
      simpa [hne, fst, snd] using (Prod.eta (show A × A from x))
    left_distrib := by
      rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨z₁, z₂⟩
      change (x₁ * (y₁ + z₁) + γ • (conjugate n (y₂ + z₂) * x₂),
        (y₂ + z₂) * x₁ + x₂ * conjugate n (y₁ + z₁)) =
        (x₁ * y₁ + γ • (conjugate n y₂ * x₂) + (x₁ * z₁ + γ • (conjugate n z₂ * x₂)),
          y₂ * x₁ + x₂ * conjugate n y₁ + (z₂ * x₁ + x₂ * conjugate n z₁))
      simp only [map_add, add_mul, mul_add, smul_add, Prod.mk.injEq]
      exact ⟨by abel, by abel⟩
    right_distrib := by
      rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨z₁, z₂⟩
      change ((x₁ + y₁) * z₁ + γ • (conjugate n z₂ * (x₂ + y₂)),
        z₂ * (x₁ + y₁) + (x₂ + y₂) * conjugate n z₁) =
        (x₁ * z₁ + γ • (conjugate n z₂ * x₂) + (y₁ * z₁ + γ • (conjugate n z₂ * y₂)),
          z₂ * x₁ + x₂ * conjugate n z₁ + (z₂ * y₁ + y₂ * conjugate n z₁))
      simp only [add_mul, mul_add, smul_add, Prod.mk.injEq]
      exact ⟨by abel, by abel⟩ }

@[simp]
theorem mul_pair (x y z t : A) :
    pair n γ x y * pair n γ z t =
      pair n γ (x * z + γ • (conjugate n t * y)) (t * x + y * conjugate n z) := rfl

@[simp]
theorem smul_pair (c : k) (x y : A) :
    c • pair n γ x y = pair n γ (c • x) (c • y) := rfl

abbrev scalarTower (h : conjugate n 1 = 1) :
    letI := ring n γ h
    IsScalarTower k (CayleyDickson n γ) (CayleyDickson n γ) := by
  constructor
  rintro c ⟨x, y⟩ ⟨z, t⟩
  change (c • pair n γ x y) * pair n γ z t = c • (pair n γ x y * pair n γ z t)
  simp only [smul_pair, mul_pair, smul_mul_assoc, mul_smul_comm, smul_add]
  rw [smul_comm γ c]

abbrev scalarComm (h : conjugate n 1 = 1) :
    letI := ring n γ h
    SMulCommClass k (CayleyDickson n γ) (CayleyDickson n γ) := by
  constructor
  rintro c ⟨x, y⟩ ⟨z, t⟩
  change c • (pair n γ x y * pair n γ z t) = pair n γ x y * (c • pair n γ z t)
  simp only [smul_pair, mul_pair, map_smul, smul_mul_assoc, mul_smul_comm, smul_add]
  rw [smul_comm γ c]

end CayleyDickson

def scalarDoubleModel : Prop :=
  ∀ {k : Type u} [Field k] (α : k), (2 : k) ≠ 0 → α ≠ 0 →
    Algebra.Etale k (scalarDouble α) ∧ Module.finrank k (scalarDouble α) = 2 ∧
    FieldNormConditions (scalarDoubleNorm α) ∧
    (QuadraticAlgebra.omega : scalarDouble α) ^ 2 = algebraMap k (scalarDouble α) α ∧
    (∀ s t : k, scalarDoubleNorm α ⟨s,t⟩ = s ^ 2 - α * t ^ 2) ∧
    (∀ x : scalarDouble α, x = x.re • 1 + x.im • QuadraticAlgebra.omega)

/-- The three consecutive doubles in their scalar, cyclic, and ordered-pair coordinates. -/
def consecutiveDoublingModels : Prop :=
  ∀ {k : Type u} [Field k] (α β γ : k), (2 : k) ≠ 0 → α ≠ 0 → β ≠ 0 → γ ≠ 0 →
    let Q := quaternionModel α β
    let nQ := quaternionModelNorm α β
    let i := quaternionModelPair α β QuadraticAlgebra.omega 0
    let j := quaternionModelPair α β 0 1
    Module.finrank k Q = 4 ∧ FieldNormConditions nQ ∧
    i * i = α • (1 : Q) ∧ j * j = β • (1 : Q) ∧ i * j = -(j * i) ∧ i * j ≠ j * i ∧
    (∀ x y, nQ (quaternionModelPair α β x y) = scalarDoubleNorm α x - β * scalarDoubleNorm α y) ∧
    ∃ h : conjugate nQ 1 = 1,
      let C := CayleyDickson nQ γ
      letI : NonAssocRing C := CayleyDickson.ring nQ γ h
      letI : IsScalarTower k C C := CayleyDickson.scalarTower nQ γ h
      letI : SMulCommClass k C C := CayleyDickson.scalarComm nQ γ h
      let a := CayleyDickson.pair nQ γ 0 1
      Module.finrank k C = 8 ∧ FieldNormConditions (CayleyDickson.norm nQ γ) ∧
      a * a = γ • (1 : C) ∧
      (∀ x y : Q, CayleyDickson.pair nQ γ x y =
        CayleyDickson.pair nQ γ x 0 + CayleyDickson.pair nQ γ y 0 * a) ∧
      (∀ x y : Q, CayleyDickson.norm nQ γ (CayleyDickson.pair nQ γ x y) = nQ x - γ * nQ y) ∧
      Specs.LinearAlgebraicGroups.Composition.AlternativeIdentities.isAlternative C ∧
      ∃ x y z : C, (x * y) * z ≠ x * (y * z)

/-- The negative unit parameters give Hamilton's quaternions and the real octonion division algebra. -/
def realDoublingDivision : Prop :=
  let Q := quaternionModel (-1 : ℝ) (-1)
  let nQ := quaternionModelNorm (-1 : ℝ) (-1)
  let C := CayleyDickson nQ (-1)
  let nC := CayleyDickson.norm nQ (-1)
  ∃ e : Q ≃ₐ[ℝ] Quaternion ℝ,
    (∀ x : Q, nQ x = Quaternion.normSq (e x)) ∧
    (∀ x : Q, x ≠ 0 → 0 < nQ x ∧ Function.Bijective (fun y => x * y) ∧
      Function.Bijective (fun y => y * x)) ∧
    (∀ x : C, x ≠ 0 → 0 < nC x ∧ Function.Bijective (fun y => x * y) ∧
      Function.Bijective (fun y => y * x))

end Models

section Internal

variable {k : Type u} {C : Type v} [Field k] [NonAssocRing C] [Module k C]
variable [IsScalarTower k C C] [SMulCommClass k C C]

/-- Use the inherited operations on an associative unital subalgebra. -/
abbrev associativeSubalgebraRing (D : UnitalSubalgebra k C)
    (ha : ∀ x y z : D, (x * y) * z = x * (y * z)) : Ring D :=
  { (inferInstance : NonAssocRing D) with mul_assoc := ha }

/-- Use the inherited operations on an associative, commutative unital subalgebra. -/
abbrev commutativeSubalgebraRing (D : UnitalSubalgebra k C)
    (ha : ∀ x y z : D, (x * y) * z = x * (y * z)) (hc : ∀ x y : D, x * y = y * x) :
    CommRing D :=
  { (inferInstance : NonAssocRing D) with mul_assoc := ha, mul_comm := hc }

def orthogonalQuaternionModel : Prop :=
  ∀ {k : Type u} {C : Type v} [Field k] [NonAssocRing C] [Module k C]
    [IsScalarTower k C C] [SMulCommClass k C C]
    {n : QuadraticForm k C} {D : UnitalSubalgebra k C} {a : C},
    FieldNormConditions n → FieldNormConditions (D.restrictNorm n) →
    a ∈ D.toSubmodule.orthogonalBilin n.polarBilin → n a ≠ 0 →
    ∀ (ha : ∀ x y z : D, (x * y) * z = x * (y * z)) (hc : ∀ x y : D, x * y = y * x),
    letI : CommRing D := commutativeSubalgebraRing D ha hc
    letI : Algebra k D := Algebra.ofModule (R := k) (A := D) smul_mul_assoc mul_smul_comm
    Algebra.Etale k D → Module.finrank k D = 2 →
    ∃ (E : UnitalSubalgebra k C),
      E.toSubmodule = D.toSubmodule ⊔ D.rightMultiple a ∧
      ∃ (σ : D ≃ₐ[k] D) (hσ : Function.Involutive σ),
        (∀ x, σ x = conjugate (D.restrictNorm n) x) ∧
        let Q := cyclicAlgebra σ hσ (-n a)
        ∃ he : ∀ x y z : E, (x * y) * z = x * (y * z),
          letI : Ring E := associativeSubalgebraRing E he
          letI : Algebra k E := Algebra.ofModule (R := k) (A := E) smul_mul_assoc mul_smul_comm
          ∃ (f : Q ≃ₐ[k] E) (hE : RM03.CSA.IsCentralSimple k E),
            Module.finrank k E = 4 ∧ RM03.CSA.degree k E = 2 ∧
            (∀ x y : D, (f (cyclicPair σ hσ (-n a) x y) : C) = (x : C) + (y : C) * a) ∧
            (∀ z : E, n (z : C) = RM03.CSA.reducedNorm hE z) ∧
            (isotropic (E.restrictNorm n) ↔ Nonempty (E ≃ₐ[k] Matrix (Fin 2) (Fin 2) k))

/-- Intrinsic quaternion theorem for a regular four-dimensional composition algebra. -/
def abstractQuaternion : Prop :=
  ∀ {k : Type u} {Q : Type v} [Field k] [NonAssocRing Q] [Module k Q]
    [IsScalarTower k Q Q] [SMulCommClass k Q Q] {n : QuadraticForm k Q},
    (2 : k) ≠ 0 → FieldNormConditions n → Module.finrank k Q = 4 →
    ∃ ha : ∀ x y z : Q, (x * y) * z = x * (y * z),
      letI : Ring Q := { (inferInstance : NonAssocRing Q) with mul_assoc := ha }
      letI : Algebra k Q := Algebra.ofModule (R := k) (A := Q) smul_mul_assoc mul_smul_comm
      ∃ hQ : RM03.CSA.IsCentralSimple k Q,
        RM03.CSA.degree k Q = 2 ∧
        (∀ x : Q, n x = RM03.CSA.reducedNorm hQ x) ∧
        (isotropic n ↔ Nonempty (Q ≃ₐ[k] Matrix (Fin 2) (Fin 2) k))

end Internal

end LinearAlgebraicGroups.Composition.QuaternionSpecification
