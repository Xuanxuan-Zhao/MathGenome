import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.AlgebraRepresentations
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.Representations
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! The direct sum construction from quiver representations to left path algebra modules. -/

open CategoryTheory
open scoped DirectSum BigOperators Classical

namespace RM03.PathOperatorsSpec

universe u v w d

open Quivers.AlgebraRepresentations (CompatibleModule)

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
variable {F G : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q}

abbrev Total (F : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q) :=
  ⨁ i : Q, (QuiverRepresentationSpec.vertex F i : Type d)

/-- The inclusion of one vertex space into the direct sum. -/
noncomputable def inclusion (F : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q) (i : Q) :
    QuiverRepresentationSpec.vertex F i →ₗ[k] Total F :=
  DirectSum.lof k Q (fun i => QuiverRepresentationSpec.vertex F i) i

/-- The coordinate projection onto one vertex space. -/
def projection (F : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q) (i : Q) :
    Total F →ₗ[k] QuiverRepresentationSpec.vertex F i :=
  DirectSum.component k Q (fun i => QuiverRepresentationSpec.vertex F i) i

/-- Project to the initial vertex, apply the path map, and include at the terminal vertex. -/
noncomputable def operator (F : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q)
    (p : Path Q) : Module.End k (Total F) :=
  (inclusion F p.target).comp
    ((QuiverRepresentationSpec.mapPath F p.2.2).comp (projection F p.source))

/-- The operator of a finite linear combination of paths. -/
noncomputable def linearExtension (F : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q) :
    PathAlgebraSpec.Carrier k Q →ₗ[k] Module.End k (Total F) :=
  (PathAlgebraSpec.basis k Q).constr k (operator F)

/-- The direct sum of the components of a morphism of representations. -/
def sumMap (f : F ⟶ G) : Total F →ₗ[k] Total G :=
  DirectSum.lmap (QuiverRepresentationSpec.component f)

/-- Package the specified left action on the direct sum as an object of the module category. -/
def bundledModule {A : Type*} [Ring A] [Algebra k A]
    (F : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q)
    (M : CompatibleModule k A (Total F)) : ModuleCat.{max u d} A :=
  letI := M.module
  ModuleCat.of A (Total F)

section Signatures
set_option linter.checkUnivs false

abbrev TotalSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q],
    QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q → Type (max u d)

abbrev InclusionSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
    (F : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q) (i : Q),
    QuiverRepresentationSpec.vertex F i →ₗ[k] Total F

abbrev ProjectionSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
    (F : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q) (i : Q),
    Total F →ₗ[k] QuiverRepresentationSpec.vertex F i

abbrev OperatorSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
    (F : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q), Path Q → Module.End k (Total F)

abbrev ExtensionSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
    (F : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q),
    PathAlgebraSpec.Carrier k Q →ₗ[k] Module.End k (Total F)

abbrev SumMapSignature :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
    {F G : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q}, (F ⟶ G) → Total F →ₗ[k] Total G

end Signatures

def OperatorProduct : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
    (F : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q) (p q : Path Q),
    operator F p * operator F q =
      if h : p.source = q.target then operator F (p.concat q h) else 0

def VertexSum : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]
    (F : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q),
    (∑ i : Q, operator F (Path.vertex i)) = 1

def ExtensionFormula : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
    (F : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q)
    (a : PathAlgebraSpec.Carrier k Q) (x : Total F),
    linearExtension F a x =
      (show Path Q →₀ k from a).sum (fun p c => c • operator F p x)

/-- The witnesses for the path algebra structure must use the specified operations. -/
def IsPathAlgebra [Fintype Q] (r : Ring (PathAlgebraSpec.Carrier k Q))
    (a : @Algebra k (PathAlgebraSpec.Carrier k Q) _ r.toSemiring) : Prop :=
  r.toAddCommGroup = inferInstanceAs (AddCommGroup (PathAlgebraSpec.Carrier k Q)) ∧
  r.toSemiring.toMonoidWithZero.toMonoid.toMulOneClass.toMul =
    inferInstanceAs (Mul (PathAlgebraSpec.Carrier k Q)) ∧
  r.toSemiring.toMonoidWithZero.toMonoid.toMulOneClass.toOne =
    inferInstanceAs (One (PathAlgebraSpec.Carrier k Q)) ∧
  a.toSMul = inferInstanceAs (SMul k (PathAlgebraSpec.Carrier k Q)) ∧
  ∀ c, a.algebraMap c = PathAlgebraSpec.scalarMap k Q c

/-- The specified operators give a compatible unital action and a linear functor whose
underlying morphism functions are the direct sums of the vertex components. -/
def Construction : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q],
    ∃ (r : Ring (PathAlgebraSpec.Carrier k Q))
      (a : @Algebra k (PathAlgebraSpec.Carrier k Q) _ r.toSemiring),
      IsPathAlgebra r a ∧
      letI : Ring (PathAlgebraSpec.Carrier k Q) := r
      letI : Algebra k (PathAlgebraSpec.Carrier k Q) := a
      ∃ (ρ : ∀ F : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q,
          PathAlgebraSpec.Carrier k Q →ₐ[k] Module.End k (Total F))
        (M : ∀ F : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q,
          CompatibleModule k (PathAlgebraSpec.Carrier k Q) (Total F))
        (T : QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q ⥤
          ModuleCat.{max u d} (PathAlgebraSpec.Carrier k Q)),
        (∀ F b, ρ F b = linearExtension F b) ∧
        (∀ F b x, (M F).act b x = ρ F b x) ∧
        (∀ F, T.obj F = bundledModule F (M F)) ∧
        (∀ F p x, (M F).act (PathAlgebraSpec.ofPath k Q p) x = operator F p x) ∧
        (∀ ⦃F G⦄ (f : F ⟶ G), HEq ((T.map f).hom : T.obj F → T.obj G)
          (sumMap f : Total F → Total G)) ∧
        T.Additive ∧ T.Linear k

end RM03.PathOperatorsSpec
