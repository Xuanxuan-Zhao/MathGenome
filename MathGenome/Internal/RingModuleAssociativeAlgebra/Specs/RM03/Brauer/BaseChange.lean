import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.Group
import Mathlib.Algebra.Group.Subgroup.Ker

/-! Scalar extension and relative Brauer subgroups in RM03-C04.11 and RM03-C04.13. -/

namespace Specs.RM03.Brauer

open scoped TensorProduct

universe u w x v

/-- The specified value on every representative of the Brauer quotient. -/
def IsScalarExtension (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L]
    (f : BrauerGroup.{u, v} k → BrauerGroup.{w, max w v} L) : Prop :=
  ∀ A : _root_.CSA.{u, v} k, ∃ B : _root_.CSA.{w, max w v} L,
    B.toAlgCat = AlgCat.of L (CSA.baseChange k L A) ∧ f (classOf A) = classOf B

def ScalarExtensionMatrix : Prop :=
  ∀ (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L]
    (n : ℕ) (A : Type v) [Ring A] [Algebra k A],
    ∃ e : L ⊗[k] Matrix (Fin n) (Fin n) A ≃ₐ[L] Matrix (Fin n) (Fin n) (L ⊗[k] A),
      ∀ (l : L) (M : Matrix (Fin n) (Fin n) A) (i j : Fin n),
        e (l ⊗ₜ[k] M) i j = l ⊗ₜ[k] M i j

def ScalarExtensionTensor : Prop :=
  ∀ (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L]
    (A : Type v) [Ring A] [Algebra k A] (B : Type x) [Ring B] [Algebra k B],
    ∃ e : L ⊗[k] (A ⊗[k] B) ≃ₐ[L] (L ⊗[k] A) ⊗[L] (L ⊗[k] B),
      ∀ (l : L) (a : A) (b : B),
        e (l ⊗ₜ[k] (a ⊗ₜ[k] b)) = (l ⊗ₜ[k] a) ⊗ₜ[L] ((1 : L) ⊗ₜ[k] b)

def ScalarExtensionTowerEquiv : Prop :=
  ∀ (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L]
    (F : Type x) [Field F] [Algebra k F] [Algebra L F] [IsScalarTower k L F]
    (A : Type v) [Ring A] [Algebra k A],
    ∃ e : F ⊗[L] (L ⊗[k] A) ≃ₐ[F] F ⊗[k] A,
      ∀ (f : F) (l : L) (a : A), e (f ⊗ₜ[L] (l ⊗ₜ[k] a)) = (l • f) ⊗ₜ[k] a

def ScalarExtensionRespectsEquivalence : Prop :=
  ∀ (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L]
    {A : Type v} [Ring A] [Algebra k A] {B : Type x} [Ring B] [Algebra k B],
    equivalent k A B → equivalent L (CSA.baseChange k L A) (CSA.baseChange k L B)

def ScalarExtensionOnClasses : Prop :=
  ∀ (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L],
    ∃! f : BrauerGroup.{u, v} k → BrauerGroup.{w, max w v} L, IsScalarExtension k L f

-- The source and target groups may have independent universes.
set_option linter.checkUnivs false in
def RelativeSubgroupType :=
  ∀ {B : Type u} {C : Type w} [AddGroup B] [AddGroup C], (B →+ C) → AddSubgroup B

/-- The relative subgroup is the kernel of the specified scalar-extension map.
This definition also applies to extensions that are infinite or non-Galois. -/
def relativeSubgroup {B : Type u} {C : Type w} [AddGroup B] [AddGroup C]
    (f : B →+ C) : AddSubgroup B :=
  f.ker

/-- The group map has the prescribed representative formula, and its kernel consists exactly
of the classes whose representatives the extension splits. The group laws pin both group
structures to the original Brauer operations. -/
def ScalarExtensionGroupLaw : Prop :=
  ∀ (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L],
    ∃ gk : AddCommGroup (BrauerGroup.{u, max u w v} k),
    ∃ gL : AddCommGroup (BrauerGroup.{w, max u w v} L),
      GroupLaws.{u, max w v} k gk ∧ GroupLaws.{w, max u v} L gL ∧
      letI := gk
      letI := gL
      ∃ f : BrauerGroup.{u, max u w v} k →+ BrauerGroup.{w, max u w v} L,
        IsScalarExtension k L f ∧
        ∀ A : _root_.CSA.{u, max u w v} k, classOf A ∈ relativeSubgroup f ↔ CSA.splits k L A

def ScalarExtensionIdentity : Prop :=
  ∀ (k : Type u) [Field k] (f : BrauerGroup.{u, max u v} k → BrauerGroup.{u, max u v} k),
    IsScalarExtension k k f → f = id

def ScalarExtensionTower : Prop :=
  ∀ (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L]
    (F : Type x) [Field F] [Algebra k F] [Algebra L F] [IsScalarTower k L F]
    (f : BrauerGroup.{u, max u w x v} k → BrauerGroup.{w, max u w x v} L)
    (g : BrauerGroup.{w, max u w x v} L → BrauerGroup.{x, max u w x v} F)
    (h : BrauerGroup.{u, max u w x v} k → BrauerGroup.{x, max u w x v} F),
    IsScalarExtension k L f → IsScalarExtension L F g → IsScalarExtension k F h → g ∘ f = h

/-- In particular for a finite Galois tower, the relative inclusion acts by the identity on the
class in the ambient Brauer group of the base field. -/
def RelativeSubgroupTower : Prop :=
  ∀ (k : Type u) [Field k] (L : Type w) [Field L] [Algebra k L]
    (F : Type x) [Field F] [Algebra k F] [Algebra L F] [IsScalarTower k L F]
    [AddCommGroup (BrauerGroup.{u, max u w x v} k)]
    [AddCommGroup (BrauerGroup.{w, max u w x v} L)]
    [AddCommGroup (BrauerGroup.{x, max u w x v} F)]
    (f : BrauerGroup.{u, max u w x v} k →+ BrauerGroup.{w, max u w x v} L)
    (g : BrauerGroup.{w, max u w x v} L →+ BrauerGroup.{x, max u w x v} F)
    (h : BrauerGroup.{u, max u w x v} k →+ BrauerGroup.{x, max u w x v} F),
    IsScalarExtension k L f → IsScalarExtension L F g → IsScalarExtension k F h →
    ∃ i : relativeSubgroup f →+ relativeSubgroup h, Function.Injective i ∧
      ∀ a, (i a : BrauerGroup.{u, max u w x v} k) = a

end Specs.RM03.Brauer
