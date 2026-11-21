import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.BaseChange
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.ProjectiveClassification
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! Scalar obstruction and its coefficient cohomology in RM03-C04.13. -/

open scoped TensorProduct MatrixGroups Kronecker

namespace RM03.Brauer.ScalarObstruction

open Matrix ProjectiveClassification groupCohomology

universe u v w

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]

/-- Multiplicative two-cocycles for the natural Galois action. -/
def cocycles : Subgroup ((Gal(K/k) × Gal(K/k)) → Kˣ) where
  carrier := {c | IsMulCocycle₂ c}
  one_mem' := by intro g h j; simp
  mul_mem' {a b} ha hb := by
    intro g h j
    change (a (g*h,j) * b (g*h,j)) * (a (g,h) * b (g,h)) =
      g • (a (h,j) * b (h,j)) * (a (g,h*j) * b (g,h*j))
    rw [smul_mul', mul_mul_mul_comm, ha g h j, hb g h j, mul_mul_mul_comm]
  inv_mem' {a} ha := by
    intro g h j
    change (a (g*h,j))⁻¹ * (a (g,h))⁻¹ = g • (a (h,j))⁻¹ * (a (g,h*j))⁻¹
    simpa only [mul_inv, smul_inv'] using congrArg Inv.inv (ha g h j)

abbrev ScalarCocycle := ↥(cocycles k K)

/-- The coboundary of a scalar one-cochain. -/
def coboundary : (Gal(K/k) → Kˣ) →* ScalarCocycle k K where
  toFun a := ⟨fun p => p.1 • a p.2 / a (p.1 * p.2) * a p.1, by
    intro g h j
    simp only [div_eq_mul_inv, smul_mul', smul_inv', mul_smul, mul_assoc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel⟩
  map_one' := by apply Subtype.ext; funext p; simp
  map_mul' a b := by
    apply Subtype.ext
    funext p
    change p.1 • (a p.2 * b p.2) / (a (p.1 * p.2) * b (p.1 * p.2)) *
        (a p.1 * b p.1) = (p.1 • a p.2 / a (p.1 * p.2) * a p.1) *
          (p.1 • b p.2 / b (p.1 * p.2) * b p.1)
    simp only [smul_mul', div_eq_mul_inv, mul_inv]
    ac_rfl

/-- Second cohomology as the quotient of multiplicative cocycles by coboundaries. -/
abbrev H2 := ScalarCocycle k K ⧸ (coboundary k K).range

/-- Send a scalar cocycle to its class. -/
def cocycleClass : ScalarCocycle k K →* H2 k K :=
  QuotientGroup.mk' (coboundary k K).range

variable {k K} {n : ℕ}

/-- Entrywise coefficient automorphism acting on invertible matrices. -/
def mapGL (g : Gal(K/k)) : GL (Fin n) K →* GL (Fin n) K :=
  GeneralLinearGroup.map g.toRingHom

/-- A lift of a projective cocycle to invertible matrices. -/
def IsLift (c : Cocycle k K n) (G : Gal(K/k) → GL (Fin n) K) : Prop :=
  ∀ g, ProjGenLinGroup.mk (G g) = c.val g

/-- The scalar recovered from the defect of a lifted projective cocycle in positive degree. -/
noncomputable def scalarDefect (G : Gal(K/k) → GL (Fin n) K) :
    (Gal(K/k) × Gal(K/k)) → Kˣ :=
  fun (g,h) => Function.invFun (GeneralLinearGroup.scalar (Fin n) : Kˣ → GL (Fin n) K)
    (G g * mapGL g (G h) * (G (g*h))⁻¹)

/-- Kronecker product of invertible matrices, with indices flattened to `Fin (m*n)`. -/
def kroneckerLift {K : Type v} [Field K] {m n : ℕ}
    (G : GL (Fin m) K) (H : GL (Fin n) K) : GL (Fin (m*n)) K :=
  Units.map (Matrix.reindexAlgEquiv K K finProdFinEquiv).toAlgHom.toMonoidHom
    (G.kronecker H)

end RM03.Brauer.ScalarObstruction

namespace Specs.RM03.Brauer.ScalarObstruction

open _root_.RM03.Brauer.ProjectiveClassification
open _root_.RM03.Brauer.ScalarObstruction
open _root_.RM03.Brauer.SemilinearDescent
open Matrix groupCohomology

universe u v w x

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ}

/-- A scalar cocycle records the stated lift defect. -/
def RecordsDefect (G : Gal(K/k) → GL (Fin n) K) (c : ScalarCocycle k K) : Prop :=
  ∀ g h, GeneralLinearGroup.scalar (Fin n) (c.val (g,h)) =
    G g * mapGL g (G h) * (G (g*h))⁻¹

/-- Witnesses for the projective cocycle and its lifts for the particular splitting. -/
def Presents {A : Type w} [Ring A] [Algebra k A]
    (s : (K ⊗[k] A) ≃ₐ[K] Mat K n) (G : Gal(K/k) → GL (Fin n) K) : Prop :=
  ∃ (ρ : AlgebraAction k K (Mat K n)) (p : Cocycle k K n),
    IsTransport ρ s ∧ Implements ρ p ∧ IsLift p G

def CoefficientActionFormula : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (g : Gal(K/k)) (a : Kˣ), ((g • a : Kˣ) : K) = g (a : K)

def CocycleClassEqIff : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (a b : ScalarCocycle k K),
    cocycleClass k K a = cocycleClass k K b ↔
      IsMulCoboundary₂ (fun p => b.val p / a.val p)

def CocycleClassEqOneIff : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (a : ScalarCocycle k K),
    cocycleClass k K a = 1 ↔ IsMulCoboundary₂ a.val

def CocycleClassSurjective : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K],
    Function.Surjective (cocycleClass k K)

def LiftDefect : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (_hn : 0 < n) (p : Cocycle k K n) (G : Gal(K/k) → GL (Fin n) K), IsLift p G →
    (∀ g h, GeneralLinearGroup.scalar (Fin n) (scalarDefect G (g,h)) =
      G g * mapGL g (G h) * (G (g*h))⁻¹) ∧
      IsMulCocycle₂ (scalarDefect G)

def LiftCocycleLaw : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ},
    0 < n → ∀ (p : Cocycle k K n) (G : Gal(K/k) → GL (Fin n) K), IsLift p G →
      ∀ g h j : Gal(K/k), scalarDefect G (g,h) * scalarDefect G (g*h,j) =
        g • scalarDefect G (h,j) * scalarDefect G (g,h*j)

def RecordsDefectUnique : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ},
    0 < n → ∀ {G : Gal(K/k) → GL (Fin n) K} {a b : ScalarCocycle k K},
      RecordsDefect G a → RecordsDefect G b → a = b

def StacksInverse : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (_hn : 0 < n) (p : Cocycle k K n) (G : Gal(K/k) → GL (Fin n) K),
    IsLift p G → ∀ g h,
      (G g)⁻¹ * G (g*h) * mapGL g (G h)⁻¹ =
        GeneralLinearGroup.scalar (Fin n) ((scalarDefect G (g,h))⁻¹)

def CohomologousLiftClasses : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (_hn : 0 < n) (p q : Cocycle k K n), Cohomologous k K n p q →
    ∀ (G H : Gal(K/k) → GL (Fin n) K), IsLift p G → IsLift q H →
    ∀ (a b : ScalarCocycle k K), RecordsDefect G a → RecordsDefect H b →
      cocycleClass k K a = cocycleClass k K b


def ExistsPresentation : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ}
    {A : Type w} [Ring A] [Algebra k A],
    0 < n → ∀ s : (K ⊗[k] A) ≃ₐ[K] Mat K n,
      ∃ G : Gal(K/k) → GL (Fin n) K, Presents s G

def ExistsRecordedDefect : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ}
    {A : Type w} [Ring A] [Algebra k A],
    0 < n → ∀ {s : (K ⊗[k] A) ≃ₐ[K] Mat K n} {G : Gal(K/k) → GL (Fin n) K},
      Presents s G → ∃ c : ScalarCocycle k K, RecordsDefect G c

def SplittingLiftClasses : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ}
    {A : Type w} [Ring A] [Algebra k A], 0 < n →
    ∀ (s t : (K ⊗[k] A) ≃ₐ[K] Mat K n) (G H : Gal(K/k) → GL (Fin n) K),
      Presents s G → Presents t H → ∀ (a b : ScalarCocycle k K),
      RecordsDefect G a → RecordsDefect H b → cocycleClass k K a = cocycleClass k K b

def TensorLiftDefect : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ}
    {A : Type w} [Ring A] [Algebra k A] {B : Type x} [Ring B] [Algebra k B] {m : ℕ},
    0 < m → 0 < n →
    ∀ (s : (K ⊗[k] A) ≃ₐ[K] Mat K m) (t : (K ⊗[k] B) ≃ₐ[K] Mat K n)
      (G : Gal(K/k) → GL (Fin m) K) (H : Gal(K/k) → GL (Fin n) K),
      Presents s G → Presents t H → ∀ (a b : ScalarCocycle k K),
      RecordsDefect G a → RecordsDefect H b →
      ∃ st : (K ⊗[k] (A ⊗[k] B)) ≃ₐ[K] Mat K (m*n),
        Presents st (fun g => kroneckerLift (G g) (H g)) ∧
        RecordsDefect (fun g => kroneckerLift (G g) (H g)) (a*b)

def EnlargementLiftDefect : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ}
    {A : Type w} [Ring A] [Algebra k A] {m : ℕ},
    0 < m → 0 < n → ∀ (s : (K ⊗[k] A) ≃ₐ[K] Mat K n) (G : Gal(K/k) → GL (Fin n) K),
      Presents s G → ∀ a : ScalarCocycle k K, RecordsDefect G a →
      ∃ t : (K ⊗[k] Matrix (Fin m) (Fin m) A) ≃ₐ[K] Mat K (m*n),
        Presents t (fun g => kroneckerLift (1 : GL (Fin m) K) (G g)) ∧
        RecordsDefect (fun g => kroneckerLift (1 : GL (Fin m) K) (G g)) a

def EquivalentLiftClasses : Prop :=
  ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ}
    {A : Type w} [Ring A] [Algebra k A] {B : Type x} [Ring B] [Algebra k B] {m : ℕ},
    0 < m → 0 < n → equivalent k A B →
    ∀ (s : (K ⊗[k] A) ≃ₐ[K] Mat K m) (t : (K ⊗[k] B) ≃ₐ[K] Mat K n)
      (G : Gal(K/k) → GL (Fin m) K) (H : Gal(K/k) → GL (Fin n) K),
      Presents s G → Presents t H → ∀ (a b : ScalarCocycle k K),
      RecordsDefect G a → RecordsDefect H b → cocycleClass k K a = cocycleClass k K b

/-- The representative formula determines the map out of the relative subgroup. -/
def IsObstructionHom
    [AddCommGroup (BrauerGroup.{u, max u v w} k)]
    [AddCommGroup (BrauerGroup.{v, max u v w} K)]
    (f : BrauerGroup.{u, max u v w} k →+ BrauerGroup.{v, max u v w} K)
    (φ : relativeSubgroup f →+ Additive (H2 k K)) : Prop :=
  ∀ (A : _root_.CSA.{u, max u v w} k) (hA : classOf A ∈ relativeSubgroup f)
    {n : ℕ}, 0 < n →
    ∀ (s : (K ⊗[k] A) ≃ₐ[K] Mat K n) (G : Gal(K/k) → GL (Fin n) K),
      Presents s G → ∀ c : ScalarCocycle k K, RecordsDefect G c →
      φ ⟨classOf A, hA⟩ = Additive.ofMul (cocycleClass k K c)

/-- The homomorphism from the kernel of base change for the prescribed Brauer operations. -/
def ObstructionHom : Prop :=
  ∀ (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (gk : AddCommGroup (BrauerGroup.{u, max u v w} k))
    (gK : AddCommGroup (BrauerGroup.{v, max u v w} K)),
    GroupLaws.{u, max v w} k gk → GroupLaws.{v, max u w} K gK →
    letI := gk
    letI := gK
    ∀ (f : BrauerGroup.{u, max u v w} k →+ BrauerGroup.{v, max u v w} K),
      IsScalarExtension k K f →
      ∃! φ : relativeSubgroup f →+ Additive (H2 k K), IsObstructionHom.{u,v,w} f φ

end Specs.RM03.Brauer.ScalarObstruction
