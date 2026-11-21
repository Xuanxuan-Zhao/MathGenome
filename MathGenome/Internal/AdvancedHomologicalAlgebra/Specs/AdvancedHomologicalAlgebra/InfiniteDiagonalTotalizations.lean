import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DoubleTotalization
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! The infinite-diagonal example following HA-B02 (source lines 815–821).
The objects and the two totalizations below are the actual categorical ones.
No finite-diagonal hypothesis is imposed. -/

open CategoryTheory CategoryTheory.Limits
open AdvancedHomologicalAlgebra.DoubleTotalization

universe u
namespace AdvancedHomologicalAlgebra.InfiniteDiagonalTotalizations
variable (k : Type u) [Field k]

/-- The field on the antidiagonal, and the zero module elsewhere. -/
def term (p q : ℤ) : ModuleCat.{u} k :=
  if p + q = 0 then ModuleCat.of k k else ModuleCat.of k PUnit

/-- Both differentials vanish, in the commuting convention of HA-B01. -/
def bicomplex : HomologicalComplex₂ (ModuleCat.{u} k) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) :=
  HomologicalComplex₂.ofGradedObject _ _ (fun i => term k i.1 i.2)
    (fun _ _ _ => 0) (fun _ _ _ => 0)
    (by intros; rfl) (by intros; rfl) (by intros; simp) (by intros; simp)
    (by intros; simp)

noncomputable instance : (bicomplex k).HasTotal (ComplexShape.up ℤ) := by
  intro n
  infer_instance
noncomputable instance : HasProductTotal (bicomplex k) := by
  intro n
  infer_instance

noncomputable abbrev sumComplex := sumTotal (bicomplex k)
noncomputable abbrev productComplex := productTotal (bicomplex k)

/-- The tautological identification of each nonzero component with k. -/
def termIso (p q : ℤ) (h : p + q = 0) : term k p q ≅ ModuleCat.of k k :=
  eqToIso (ite_eq_left h)

/-- Degree-zero diagonal injections, indexed by p rather than (p,-p). -/
noncomputable def sumι (p : ℤ) : ModuleCat.of k k ⟶ (sumComplex k).X 0 :=
  (termIso k p (-p) (by omega)).inv ≫ sumInjection (bicomplex k) p (-p) 0 (by omega)

/-- Degree-zero diagonal projections, with the same indexing. -/
noncomputable def productπ (p : ℤ) : (productComplex k).X 0 ⟶ ModuleCat.of k k :=
  productProjection (bicomplex k) p (-p) 0 (by omega) ≫
    (termIso k p (-p) (by omega)).hom

/-- The usual inclusion of finitely supported sequences in all sequences. -/
noncomputable def sequenceInclusion : ModuleCat.of k (ℤ →₀ k) ⟶ ModuleCat.of k (ℤ → k) :=
  ModuleCat.ofHom { toFun := fun f => (f : ℤ → k)
                    map_add' := by intros; rfl
                    map_smul' := by intros; rfl }

namespace Specs
/-- Component equations uniquely characterize the canonical diagonal comparison,
including its zero components away from degree zero. -/
def IsComparison (f : sumComplex k ⟶ productComplex k) : Prop :=
  ∀ n p q p' q' (h : p + q = n) (h' : p' + q' = n),
    sumInjection (bicomplex k) p q n h ≫ f.f n ≫
      productProjection (bicomplex k) p' q' n h' =
    if e : (p, q) = (p', q') then
      eqToHom (congrArg (fun i : ℤ × ℤ => term k i.1 i.2) e) else 0

/-- Full conclusion of the example. The comparison on actual H⁰ is the proper
inclusion, expressed by a commuting square of module isomorphisms. The two
cohomology modules are moreover not isomorphic, even abstractly. -/
def Result : Prop :=
  (∀ p q, ((bicomplex k).X p).X q = term k p q) ∧
  (∀ p p' q, ((bicomplex k).d p p').f q = 0) ∧
  (∀ p q q', ((bicomplex k).X p).d q q' = 0) ∧
  (∀ i j, (sumComplex k).d i j = 0) ∧
  (∀ i j, (productComplex k).d i j = 0) ∧
  Set.Infinite {i : ℤ × ℤ | i.1 + i.2 = 0 ∧ ¬ IsZero (term k i.1 i.2)} ∧
  ∃ (comparison : sumComplex k ⟶ productComplex k)
    (s : (sumComplex k).homology 0 ≅ ModuleCat.of k (ℤ →₀ k))
    (t : (productComplex k).homology 0 ≅ ModuleCat.of k (ℤ → k)),
    IsComparison k comparison ∧
    (∀ f, IsComparison k f → f = comparison) ∧
    HomologicalComplex.homologyMap comparison 0 ≫ t.hom = s.hom ≫ sequenceInclusion k ∧
    Function.Injective (sequenceInclusion k) ∧
    ¬ Function.Surjective (sequenceInclusion k) ∧
    ¬ IsIso (HomologicalComplex.homologyMap comparison 0) ∧
    ¬ Nonempty ((sumComplex k).homology 0 ≅ (productComplex k).homology 0)

/-- Closed contract, retaining every field universe and the full field hypothesis. -/
def ExpectedResult : Prop := ∀ (k : Type u) [Field k], Result k
end Specs
end AdvancedHomologicalAlgebra.InfiniteDiagonalTotalizations
