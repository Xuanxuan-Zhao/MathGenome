import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.RationalRepresentations
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.Algebra.DirectSum.Module

open LinearAlgebraicGroups
open scoped TensorProduct

universe u v w

set_option linter.checkUnivs false

namespace RepTheorySurvey.Invariants.Specs

noncomputable section

/-- An abstract group acts by algebra automorphisms over the ground field. -/
abbrev GroupAlgebraAction (k : Type u) (G : Type v) (A : Type w)
    [Field k] [Group G] [Ring A] [Algebra k A] :=
  G →* (A ≃ₐ[k] A)

def GroupAlgebraActionType :=
  ∀ (k : Type u) (G : Type v) (A : Type w) [Field k] [Group G] [Ring A] [Algebra k A],
    Type (max v w)

section GroupAlgebra

variable {k : Type u} {G : Type v} {A : Type w}
  [Field k] [Group G] [Ring A] [Algebra k A]

def GroupRepresentationType :=
  ∀ {k : Type u} {G : Type v} {A : Type w} [Field k] [Group G] [Ring A] [Algebra k A],
    GroupAlgebraAction k G A → Representation k G A

def groupRepresentation (ρ : GroupAlgebraAction k G A) : Representation k G A :=
  (AlgEquiv.toLinearMapHom k A).comp ρ

def GroupFixedSubalgebraType :=
  ∀ {k : Type u} {G : Type v} {A : Type w} [Field k] [Group G] [Ring A] [Algebra k A],
    GroupAlgebraAction k G A → Subalgebra k A

/-- The fixed vectors of the underlying representation form a subalgebra. -/
def groupFixedSubalgebra (ρ : GroupAlgebraAction k G A) : Subalgebra k A where
  carrier := groupRepresentation ρ |>.invariants
  zero_mem' := (groupRepresentation ρ).invariants.zero_mem
  add_mem' := (groupRepresentation ρ).invariants.add_mem
  one_mem' := fun g ↦ map_one (ρ g)
  mul_mem' := by
    intro a b ha hb g
    change ρ g (a * b) = a * b
    exact (map_mul (ρ g) a b).trans (congrArg₂ (· * ·) (ha g) (hb g))
  algebraMap_mem' := fun c g ↦ (ρ g).commutes c

def GroupFixedSubalgebraToSubmodule : Prop :=
  ∀ {k : Type u} {G : Type v} {A : Type w} [Field k] [Group G] [Ring A] [Algebra k A]
    (ρ : GroupAlgebraAction k G A), (groupFixedSubalgebra ρ).toSubmodule =
      (groupRepresentation ρ).invariants

def GroupIsReynoldsType :=
  ∀ {k : Type u} {G : Type v} {A : Type w} [Field k] [Group G] [Ring A] [Algebra k A]
    (ρ : GroupAlgebraAction k G A), (A →ₗ[k] groupFixedSubalgebra ρ) → Prop

/-- The invariant target has the trivial action and acts on the source by left multiplication. -/
def groupIsReynolds (ρ : GroupAlgebraAction k G A) (R : A →ₗ[k] groupFixedSubalgebra ρ) : Prop :=
  (groupRepresentation ρ).IsIntertwiningMap
      (Representation.trivial k G (groupFixedSubalgebra ρ)) R ∧
    (∀ a : groupFixedSubalgebra ρ, ∀ x : A, R ((a : A) * x) = a * R x) ∧
    (∀ a : groupFixedSubalgebra ρ, R (a : A) = a)

end GroupAlgebra

section GroupRepresentation

variable {k : Type u} {G : Type v} {V : Type w}
  [Field k] [Group G] [AddCommGroup V] [Module k V]

def GroupLocallyFiniteType :=
  ∀ {k : Type u} {G : Type v} {V : Type w}
    [Field k] [Group G] [AddCommGroup V] [Module k V], Representation k G V → Prop

def groupLocallyFinite (ρ : Representation k G V) : Prop :=
  ∀ x : V, ∃ W : Subrepresentation ρ, x ∈ W ∧ FiniteDimensional k W.toSubmodule

def FiniteGroupLocallyFinite : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w}
    [Field k] [Group G] [Finite G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V), groupLocallyFinite ρ

def GroupLinearlyReductiveType := ∀ (k : Type u) (G : Type v) [Field k] [Group G], Prop

/-- Every finite-dimensional representation is an internal direct sum of finitely many
nonzero subrepresentations with no proper nonzero subrepresentation. -/
def groupLinearlyReductive (k : Type u) (G : Type v) [Field k] [Group G] : Prop :=
  ∀ (V : Type w) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V), ∃ (n : ℕ) (S : Fin n → Subrepresentation ρ),
      (∀ i, IsAtom (S i)) ∧ DirectSum.IsInternal (fun i ↦ (S i).toSubmodule)

end GroupRepresentation

section Rational

variable {k : Type u} [Field k]

/-- A right coaction on an algebra with a unital multiplicative coaction map. -/
structure RationalAlgebraAction (H : HopfAlgebraCategory k) (A : Type u) [Ring A] [Algebra k A] where
  coaction : A →ₐ[k] A ⊗[k] H
  coassoc (x : A) :
    TensorProduct.assoc k A H H (coaction.toLinearMap.rTensor H (coaction x)) =
      (Coalgebra.comul (R := k) (A := H)).lTensor A (coaction x)
  counit (x : A) :
    TensorProduct.rid k A ((Coalgebra.counit (R := k) (A := H)).lTensor A (coaction x)) = x

abbrev rationalAlgebraAction := @RationalAlgebraAction

def RationalAlgebraActionType :=
  ∀ {k : Type u} [Field k] (_H : HopfAlgebraCategory k) (A : Type u) [Ring A] [Algebra k A], Type u

variable {H : HopfAlgebraCategory k} {A V W : Type u}
  [Ring A] [Algebra k A] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

def RationalToRightComoduleType :=
  ∀ {k : Type u} [Field k] {H : HopfAlgebraCategory k} {A : Type u} [Ring A] [Algebra k A],
    RationalAlgebraAction H A → RightComodule k H A

def rationalToRightComodule (ρ : RationalAlgebraAction H A) : RightComodule k H A where
  coaction := ρ.coaction.toLinearMap
  coassoc := ρ.coassoc
  counit := ρ.counit

def RationalTrivialType :=
  ∀ {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
    (H : HopfAlgebraCategory k), RightComodule k H V

/-- The trivial coaction sends `x` to `x ⊗ₜ 1`. -/
def rationalTrivial (H : HopfAlgebraCategory k) : RightComodule k H V where
  coaction := RationalRepresentations.trivialLinearMap H
  coassoc x := by
    change TensorProduct.assoc k V H H ((RationalRepresentations.trivialLinearMap H).rTensor H
      (x ⊗ₜ[k] (1 : H))) = (Coalgebra.comul (R := k) (A := H)).lTensor V (x ⊗ₜ[k] (1 : H))
    simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, Bialgebra.comul_one,
      Algebra.TensorProduct.one_def]
    rfl
  counit x := by
    change TensorProduct.rid k V ((Coalgebra.counit (R := k) (A := H)).lTensor V
      (x ⊗ₜ[k] (1 : H))) = x
    simp only [LinearMap.lTensor_tmul, Bialgebra.counit_one, TensorProduct.rid_tmul, one_smul]

def IsComoduleMapType :=
  ∀ {k : Type u} [Field k] {H : HopfAlgebraCategory k} {V W : Type u}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W],
    RightComodule k H V → RightComodule k H W → (V →ₗ[k] W) → Prop

/-- Equivariance for right coactions is commutation with the coaction maps. -/
def isComoduleMap (ρ : RightComodule k H V) (σ : RightComodule k H W) (f : V →ₗ[k] W) : Prop :=
  (f.rTensor H).comp ρ.coaction = σ.coaction.comp f

private theorem mem_invariants_iff (ρ : RationalAlgebraAction H A) (a : A) :
    a ∈ RationalRepresentations.invariants H (rationalToRightComodule ρ) ↔
      ρ.coaction a = a ⊗ₜ[k] (1 : H) := by
  change ρ.coaction a - a ⊗ₜ[k] (1 : H) = 0 ↔ _
  exact sub_eq_zero

def RationalFixedSubalgebraType :=
  ∀ {k : Type u} [Field k] {H : HopfAlgebraCategory k} {A : Type u} [Ring A] [Algebra k A],
    RationalAlgebraAction H A → Subalgebra k A

/-- The coaction invariants are closed under multiplication, the unit and scalars. -/
def rationalFixedSubalgebra (ρ : RationalAlgebraAction H A) : Subalgebra k A where
  carrier := RationalRepresentations.invariants H (rationalToRightComodule ρ)
  zero_mem' := (RationalRepresentations.invariants H (rationalToRightComodule ρ)).zero_mem
  add_mem' := (RationalRepresentations.invariants H (rationalToRightComodule ρ)).add_mem
  one_mem' := (mem_invariants_iff ρ 1).mpr (by rw [map_one, Algebra.TensorProduct.one_def])
  mul_mem' := by
    intro a b ha hb
    apply (mem_invariants_iff ρ (a * b)).mpr
    rw [map_mul, (mem_invariants_iff ρ a).mp ha, (mem_invariants_iff ρ b).mp hb,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  algebraMap_mem' c := (mem_invariants_iff ρ _).mpr
    ((ρ.coaction.commutes c).trans
      ((Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] H).commutes c).symm)

def RationalFixedSubalgebraToSubmodule : Prop :=
  ∀ {k : Type u} [Field k] {H : HopfAlgebraCategory k} {A : Type u} [Ring A] [Algebra k A]
    (ρ : RationalAlgebraAction H A), (rationalFixedSubalgebra ρ).toSubmodule =
      RationalRepresentations.invariants H (rationalToRightComodule ρ)

def RationalIsReynoldsType :=
  ∀ {k : Type u} [Field k] {H : HopfAlgebraCategory k} {A : Type u} [Ring A] [Algebra k A]
    (ρ : RationalAlgebraAction H A), (A →ₗ[k] rationalFixedSubalgebra ρ) → Prop

def rationalIsReynolds (ρ : RationalAlgebraAction H A)
    (R : A →ₗ[k] rationalFixedSubalgebra ρ) : Prop :=
  isComoduleMap (rationalToRightComodule ρ) (rationalTrivial H) R ∧
    (∀ a : rationalFixedSubalgebra ρ, ∀ x : A, R ((a : A) * x) = a * R x) ∧
    (∀ a : rationalFixedSubalgebra ρ, R (a : A) = a)

def RationalLocallyFiniteType :=
  ∀ {k : Type u} [Field k] {H : HopfAlgebraCategory k} {V : Type u}
    [AddCommGroup V] [Module k V], RightComodule k H V → Prop

def rationalLocallyFinite (ρ : RightComodule k H V) : Prop :=
  ∀ x : V, ∃ W : ρ.FiniteSubcomodule, x ∈ W.val

def RationalLocallyFinite : Prop :=
  ∀ {k V : Type u} [Field k] {H : HopfAlgebraCategory k}
    [AddCommGroup V] [Module k V] (ρ : RightComodule k H V), rationalLocallyFinite ρ

def RationalIsSimpleSubcomoduleType :=
  ∀ {k : Type u} [Field k] {H : HopfAlgebraCategory k} {V : Type u}
    [AddCommGroup V] [Module k V], RightComodule k H V → Submodule k V → Prop

/-- A simple subcomodule is a nonzero subcomodule with no proper nonzero subcomodule. -/
def rationalIsSimpleSubcomodule (ρ : RightComodule k H V) (S : Submodule k V) : Prop :=
  ρ.IsSubcomodule S ∧ S ≠ ⊥ ∧
    ∀ T : Submodule k V, T ≤ S → ρ.IsSubcomodule T → T = ⊥ ∨ T = S

def RationalLinearlyReductiveType := ∀ {k : Type u} [Field k], HopfAlgebraCategory k → Prop

/-- Every finite-dimensional right comodule is an internal direct sum of finitely many
simple subcomodules. -/
def rationalLinearlyReductive (H : HopfAlgebraCategory k) : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RightComodule k H V), ∃ (n : ℕ) (S : Fin n → Submodule k V),
      (∀ i, rationalIsSimpleSubcomodule ρ (S i)) ∧ DirectSum.IsInternal S

end Rational

end

end RepTheorySurvey.Invariants.Specs
