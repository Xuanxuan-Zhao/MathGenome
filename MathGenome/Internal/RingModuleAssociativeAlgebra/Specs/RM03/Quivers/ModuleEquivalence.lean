import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.ModuleVertices
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.PathOperators
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! The equivalence with the category of all left path algebra modules. -/

open CategoryTheory
open scoped ModuleCat

namespace RM03.QuiverModuleEquivalenceSpec

universe u v w d

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]

abbrev Coefficients := PathAlgebraSpec.Carrier k Q

abbrev Rep := QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q

variable [Ring (Coefficients (k := k) (Q := Q))]
variable [Algebra k (Coefficients (k := k) (Q := Q))]

abbrev Mod := ModuleCat.{d} (Coefficients (k := k) (Q := Q))

def finiteModules : ObjectProperty (Mod.{u, v, w, d} (k := k) (Q := Q)) :=
  fun M => FiniteDimensional k M

def finiteRepresentations : ObjectProperty (Rep.{u, v, w, d} (k := k) (Q := Q)) :=
  fun V => ∀ i : Q, FiniteDimensional k (QuiverRepresentationSpec.vertex V i)

open ModuleVerticesSpec (representation restrictMap sumMap)
open PathOperatorsSpec (Total inclusion operator linearExtension)

/-- In the coordinates of the direct sum, the inverse functor uses the prescribed
path operators and the direct sum of the maps at the vertices. -/
def InverseFormula (G : Rep.{u, v, w, d} (k := k) (Q := Q) ⥤ Mod.{u, v, w, d} (k := k) (Q := Q))
    (J : ∀ V, G.obj V ≃ₗ[k] Total V) : Prop :=
  (∀ V (b : Coefficients (k := k) (Q := Q)) (x : G.obj V),
    J V (b • x) = linearExtension V b (J V x)) ∧
  (∀ V (p : Path Q) (x : G.obj V),
    J V (PathAlgebraSpec.ofPath k Q p • x) = operator V p (J V x)) ∧
  (∀ {V W} (f : V ⟶ W) (x : G.obj V),
    J W (G.map f x) = PathOperatorsSpec.sumMap f (J V x))

/-- The natural isomorphisms are the sum of the vertex inclusions on a module
and the recovery of each vertex summand on a representation. -/
def EquivalenceFormulas
    (E : Mod.{u, v, w, d} (k := k) (Q := Q) ≌ Rep)
    (h : ∀ M, E.functor.obj M = representation M)
    (J : ∀ V, E.inverse.obj V ≃ₗ[k] Total V) : Prop :=
  (∀ {M N} (f : M ⟶ N) (i : Q),
    QuiverRepresentationSpec.component (eqToHom (h M).symm ≫ E.functor.map f ≫ eqToHom (h N)) i =
      restrictMap f i) ∧
  (∀ (M : Mod.{u, v, w, d} (k := k) (Q := Q)) (x : E.inverse.obj (E.functor.obj M)),
    E.unitIso.inv.app M x = sumMap M (J (representation M) (E.inverse.map (eqToHom (h M)) x))) ∧
  (∀ (M : Mod.{u, v, w, d} (k := k) (Q := Q)) (m : M) (i : Q),
    (show ModuleVerticesSpec.vertexSpace M i from
      J (representation M) (E.inverse.map (eqToHom (h M)) (E.unitIso.hom.app M m)) i).val =
      PathAlgebraSpec.vertex k Q i • m) ∧
  (∀ V (i : Q) (x : QuiverRepresentationSpec.vertex V i),
    J V (show ModuleVerticesSpec.vertexSpace (E.inverse.obj V) i from
      QuiverRepresentationSpec.component
        (E.counitIso.inv.app V ≫ eqToHom (h (E.inverse.obj V))) i x) = inclusion V i x)

/-- A linear equivalence with the indicated object and morphism formulas, its restriction
to finite-dimensional objects, and exactness at every vertex. The universe of the
modules and vertex spaces is arbitrary and independent of the vertex universe. -/
def Conclusion : Prop :=
  ∀ (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Fintype Q],
    ∃ (r : Ring (Coefficients (k := k) (Q := Q)))
      (a : @Algebra k Coefficients _ r.toSemiring),
      PathOperatorsSpec.IsPathAlgebra r a ∧
      letI := r
      letI := a
      ∃ (E : Mod.{u, v, w, d} (k := k) (Q := Q) ≌ Rep)
        (h : ∀ M, E.functor.obj M = representation M)
        (J : ∀ V, E.inverse.obj V ≃ₗ[k] Total V),
        E.functor.Additive ∧ E.functor.Linear k ∧ E.inverse.Additive ∧ E.inverse.Linear k ∧
        InverseFormula E.inverse J ∧ EquivalenceFormulas E h J ∧
        (∀ M, finiteModules (k := k) M ↔ finiteRepresentations (E.functor.obj M)) ∧
        (∀ V, finiteModules (k := k) (E.inverse.obj V) ↔ finiteRepresentations V) ∧
        (∃ E₀ : (finiteModules (k := k) (Q := Q)).FullSubcategory ≌
            (finiteRepresentations (k := k) (Q := Q)).FullSubcategory,
          E₀.functor.Additive ∧ E₀.functor.Linear k ∧ E₀.inverse.Additive ∧ E₀.inverse.Linear k ∧
          E₀.functor ⋙ (finiteRepresentations (k := k) (Q := Q)).ι =
            (finiteModules (k := k) (Q := Q)).ι ⋙ E.functor ∧
          E₀.inverse ⋙ (finiteModules (k := k) (Q := Q)).ι =
            (finiteRepresentations (k := k) (Q := Q)).ι ⋙ E.inverse) ∧
        ∀ {M N P : Mod.{u, v, w, d} (k := k) (Q := Q)} (f : M ⟶ N) (g : N ⟶ P),
          (∃ hz : f ≫ g = 0, (ShortComplex.mk f g hz).Exact) ↔
            ∀ i : Q, (restrictMap f i).range = (restrictMap g i).ker

end RM03.QuiverModuleEquivalenceSpec
