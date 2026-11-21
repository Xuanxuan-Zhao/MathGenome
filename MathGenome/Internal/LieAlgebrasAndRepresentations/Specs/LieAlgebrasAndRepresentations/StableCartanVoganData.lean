import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SerreRelations
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SerreTriangularConstruction
import Mathlib.Algebra.Lie.CartanSubalgebra

/-! LA-J05, Lie volume, lines 4811–4863. The Cartan matrix has entries
`aᵢⱼ = αⱼ(hᵢ)`. A diagram automorphism preserves these directed entries. -/

namespace Specs.LieAlgebrasAndRepresentations.StableCartanVoganData

open _root_.LieAlgebrasAndRepresentations.RealForms
open _root_.LieAlgebrasAndRepresentations.Serre
open CartanDecompositionSignature (complexFixed)
open PolarRealStructures (IsCompact)
open RootDecomposition RootForm SerreRelations

universe u v

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

/-- The fixed part of the stable Cartan, as a subalgebra of the fixed algebra. -/
def fixedCartan (a : L ≃ₗ⁅ℂ⁆ L) (H : LieSubalgebra ℂ L) :
    LieSubalgebra ℂ (complexFixed a) :=
  H.comap (complexFixed a).incl

/-- The two eigenspaces inside the Cartan. -/
def cartanEigenspace (a : L ≃ₗ⁅ℂ⁆ L) (H : LieSubalgebra ℂ L) (r : ℂ) :
    Submodule ℂ H :=
  LinearMap.ker (a.toLinearEquiv.toLinearMap.comp H.toSubmodule.subtype -
    r • H.toSubmodule.subtype)

/-- Pullback by the involution on the Cartan. -/
def rootAction (a : L ≃ₗ⁅ℂ⁆ L) (H : LieSubalgebra ℂ L)
    (ha : ∀ x ∈ H, a x ∈ H) (α : Module.Dual ℂ H) : Module.Dual ℂ H :=
  α.comp ((a.toLinearEquiv.toLinearMap.comp H.toSubmodule.subtype).codRestrict
    H.toSubmodule (fun x => ha x x.property))

/-- The order on roots from evaluation at a regular element of the Cartan. -/
noncomputable def evaluation (H : LieSubalgebra ℂ L) (z : H) : Module.Dual ℂ H →ₗ[ℝ] ℝ :=
  Complex.reLm.comp ((Module.Dual.eval ℂ H z).restrictScalars ℝ)

structure StableCartan (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L)
    (H : LieSubalgebra ℂ L) : Prop where
  toral : MaximalTori.IsMaximalToral_value H
  cartan : H.IsCartanSubalgebra
  stable : ∀ x ∈ H, a x ∈ H
  compact_stable : ∀ x ∈ H, ω.map x ∈ H
  fixed_cartan : (fixedCartan a H).IsCartanSubalgebra
  decomposition : IsCompl (cartanEigenspace a H 1) (cartanEigenspace a H (-1))
  root_nonvanishing : ∀ α ∈ rootSet_value H,
    ∃ x : H, a x = (x : L) ∧ α x ≠ 0

structure PositiveOrder (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L)
    (H : LieSubalgebra ℂ L) (h : StableCartan ω a H) (z : H) : Prop where
  fixed : a z = (z : L)
  imaginary : ω.map z = -(z : L)
  real_values : ∀ α ∈ rootSet_value H, (evaluation H z α : ℂ) = α z
  regular : ∀ α ∈ rootSet_value H, evaluation H z α ≠ 0
  preserved : ∀ α, rootAction a H h.stable α ∈ positive H (evaluation H z) ↔
    α ∈ positive H (evaluation H z)

variable {ι : Type v}

/-- A Cartan-matrix-preserving involution, with signs on fixed vertices
and unit multipliers on each two-element orbit. -/
structure DiagramData (A : Matrix ι ι ℤ) where
  perm : ι ≃ ι
  involutive : Function.Involutive perm
  preserves : ∀ i j, A (perm i) (perm j) = A i j
  sign : ι → ℂ
  sign_cases : ∀ i, sign i = 1 ∨ sign i = -1
  paired : ∀ i, perm i ≠ i → sign i = 1

variable [DecidableEq ι]

/-- Normalized triples identifying an actual Lie algebra with the Serre model. -/
def Presents (A : Matrix ι ι ℤ) (E F C : ι → L) : Prop :=
  ∃ p : Algebra A ≃ₗ⁅ℂ⁆ L,
    (∀ i, p (e A i) = E i) ∧ (∀ i, p (f A i) = F i) ∧ (∀ i, p (h A i) = C i)

/-- Both the stable Cartan and the choice of its invariant positive system. -/
def stable_order_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (ω : Conjugation L), IsCompact ω →
    ∀ (a : L ≃ₗ⁅ℂ⁆ L), Intertwines ω ω a → Function.Involutive a →
    ∃ (H : LieSubalgebra ℂ L) (h : StableCartan ω a H) (z : H), PositiveOrder ω a H h z

/-- Encoding on the complete set of simple roots for the invariant order.
The conjugation identities use the same triples as the Serre presentation. -/
def Encoded [FiniteDimensional ℂ L] (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L) : Prop :=
    ∃ (H : LieSubalgebra ℂ L) (hH : StableCartan ω a H) (z : H),
    PositiveOrder ω a H hH z ∧
    let I := simple H (evaluation H z)
    letI : DecidableEq I := Classical.decEq _
    let C : I → L := fun i => coroot_value H i.val
    ∃ (A : Matrix I I ℤ) (d : DiagramData A) (E F : I → L),
      Presents A E F C ∧
      (∀ i j, i ≠ j → A i j ≤ 0) ∧
      (∀ i j, (A i j : ℂ) = j.val (coroot_value H i.val)) ∧
      (∀ i, (d.perm i).val = rootAction a H hH.stable i.val) ∧
      (∀ i, E i ∈ rootSpace_value H i.val ∧ F i ∈ rootSpace_value H (-i.val) ∧
        E i ≠ 0 ∧ F i ≠ 0 ∧ ⁅E i, F i⁆ = C i) ∧
      (∀ i, ω.map (E i) = -F i ∧ ω.map (F i) = -E i ∧ ω.map (C i) = -C i) ∧
      (∀ i, a (E i) = d.sign i • E (d.perm i) ∧
        a (F i) = d.sign i • F (d.perm i) ∧ a (C i) = C (d.perm i))

def encode_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (ω : Conjugation L), IsCompact ω →
    ∀ (a : L ≃ₗ⁅ℂ⁆ L), Intertwines ω ω a → Function.Involutive a → Encoded ω a

/-- Encoding for an involution specified on the real compact algebra. -/
def encode_compact_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (ω : Conjugation L), IsCompact ω →
    ∀ (θ : ω.fixed ≃ₗ⁅ℝ⁆ ω.fixed), Function.Involutive θ →
    ∃ a : L ≃ₗ⁅ℂ⁆ L, (∀ x : ω.fixed, a (x : L) = (θ x : L)) ∧
      Intertwines ω ω a ∧ Function.Involutive a ∧ Encoded ω a

/-- The converse in any compact realization of the Serre presentation.
The result is independent of connectedness and includes the empty matrix. -/
def realize_type : Prop :=
  ∀ {ι : Type v} [DecidableEq ι] (A : Matrix ι ι ℤ),
    (∀ i j, i ≠ j → A i j ≤ 0) →
    ∀ (d : DiagramData A) {L : Type u} [LieRing L] [LieAlgebra ℂ L]
      (ω : Conjugation L) (E F C : ι → L),
      Presents A E F C →
      (∀ i, ω.map (E i) = -F i ∧ ω.map (F i) = -E i ∧ ω.map (C i) = -C i) →
    let E' : ι → L := fun i => d.sign i • E (d.perm i)
    let F' : ι → L := fun i => d.sign i • F (d.perm i)
    let C' : ι → L := C ∘ d.perm
    RelationsHold A E' F' C' ∧
    ∃ a : L ≃ₗ⁅ℂ⁆ L, Intertwines ω ω a ∧ Function.Involutive a ∧
      (∀ i, a (E i) = E' i ∧ a (F i) = F' i ∧ a (C i) = C' i) ∧
      ∃ θ : ω.fixed ≃ₗ⁅ℝ⁆ ω.fixed, Function.Involutive θ ∧
        ∀ x : ω.fixed, a x = (θ x : L)

end Specs.LieAlgebrasAndRepresentations.StableCartanVoganData
