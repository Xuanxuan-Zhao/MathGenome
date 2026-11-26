import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.GrassmannianCharts
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Products

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.FlagIncidence

open GrassmannianCharts

noncomputable section

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  {m : ℕ} (ranks : Fin m → ℕ)

/-- A flag on an affine test algebra, in the submodule convention. -/
def AffineFlag (R : TestAlgebra k) :=
  { L : ∀ i : Fin m, Plane k V (ranks i) R //
    ∀ ⦃i j⦄, i < j → (L i).toSubmodule ≤ (L j).toSubmodule }

/-- A flag over a scheme, with containment in the ambient sheaf of modules. -/
def BundleFlag (S : SchemeOver k) :=
  { L : ∀ i : Fin m, Subbundles k V (ranks i) S //
    ∀ ⦃i j⦄, i < j → (L i).val ≤ (L j).val }

variable {k V} {idx : Type u} [Fintype idx] [DecidableEq idx]
  (b : Module.Basis idx k V)
  (C : ∀ i : Fin m, ChartSystem (k := k) (V := V) b (ranks i))

/-- The incidence construction uses the product of the given chart Grassmannians. -/
abbrev GrassmannianProduct : SchemeOver k :=
  ∏ᶜ fun i ↦ (C i).scheme

/-- The affine coordinates of a morphism to the Grassmannian product. -/
def productPlanes {R : TestAlgebra k}
    (p : Points (GrassmannianProduct ranks b C) R) (i : Fin m) :
    Plane k V (ranks i) R :=
  (C i).affinePoints.hom.app R (p ≫ Pi.π _ i)

/-- A map to the Grassmannian product pulls back each tautological subbundle. -/
def productSubbundles
    (P : ∀ i : Fin m, SchemePoints (k := k) (V := V) (ranks i)
      (C i).scheme (C i).affinePoints)
    {S : SchemeOver k} (p : S ⟶ GrassmannianProduct ranks b C) (i : Fin m) :
    Subbundles k V (ranks i) S :=
  (P i).subbundle S ((P i).family S (p ≫ Pi.π _ i))

/-- The equations on an affine test ring cut out containment of the pulled
back planes after every change of test algebra. -/
def IncidenceIdealProperty {R : TestAlgebra k}
    (L : ∀ i : Fin m, Plane k V (ranks i) R) (I : Ideal R) : Prop :=
  ∀ {A : TestAlgebra k} (a : R ⟶ A),
    I ≤ RingHom.ker a.hom.toRingHom ↔
      ∀ ⦃i j⦄, i < j →
        (Module.Grassmannian.map a.hom (L i)).toSubmodule ≤
          (Module.Grassmannian.map a.hom (L j)).toSubmodule

def AffineIncidenceEquations : Prop :=
  ∀ (k V idx : Type u) [Field k] [AddCommGroup V] [Module k V]
    [Fintype idx] [DecidableEq idx] (_b : Module.Basis idx k V)
    (m : ℕ) (ranks : Fin m → ℕ) (R : TestAlgebra k)
    (L : ∀ i : Fin m, Plane k V (ranks i) R),
    ∃! I : Ideal R, IncidenceIdealProperty ranks L I

/-- The finite product contains the locus of nested direct summands, with
the indicated affine and all-scheme universal properties. -/
structure Presentation
    (P : ∀ i : Fin m, SchemePoints (k := k) (V := V) (ranks i)
      (C i).scheme (C i).affinePoints) where
  scheme : SchemeOver k
  inclusion : scheme ⟶ GrassmannianProduct ranks b C
  closed : IsClosedImmersion inclusion.left
  affine_comparison : ∀ (R : TestAlgebra k) (p : Points (GrassmannianProduct ranks b C) R)
      (i : Fin m),
    IsTildePlane V b R (productPlanes ranks b C p i) (productSubbundles ranks b C P p i)
  factor_affine : ∀ (R : TestAlgebra k) (p : Points (GrassmannianProduct ranks b C) R),
    (∃ q : Points scheme R, q ≫ inclusion = p) ↔
      ∀ ⦃i j : Fin m⦄, i < j →
        (productPlanes ranks b C p i).toSubmodule ≤ (productPlanes ranks b C p j).toSubmodule
  factor_iff_zero : ∀ (S : SchemeOver k) (p : S ⟶ GrassmannianProduct ranks b C),
    (∃ q : S ⟶ scheme, q ≫ inclusion = p) ↔
      ∀ ⦃i j : Fin m⦄, i.val + 1 = j.val →
        (productSubbundles ranks b C P p i).val.arrow ≫
          cokernel.π (productSubbundles ranks b C P p j).val.arrow = 0
  families : ∀ S : SchemeOver k, (S ⟶ scheme) ≃ BundleFlag k V ranks S
  families_apply : ∀ (S : SchemeOver k) (p : S ⟶ scheme) (i : Fin m),
    (families S p).val i = productSubbundles ranks b C P (p ≫ inclusion) i
  pullback : ∀ {S T : SchemeOver k} (f : T ⟶ S) (p : S ⟶ scheme) (i : Fin m),
    IsPullbackSubbundle k V f ((families S p).val i) ((families T (f ≫ p)).val i)
  empty_terminal : m = 0 → Nonempty (IsTerminal scheme)

/-- Matrix transport in the base change of the specified basis. -/
def matrixTransport (R : TestAlgebra k) (g : Matrix.GeneralLinearGroup idx R) :
    (R ⊗[k] V) ≃ₗ[R] (R ⊗[k] V) :=
  (coordinates b R).trans
    ((Matrix.GeneralLinearGroup.toLin g).toLinearEquiv.trans (coordinates b R).symm)

def Construction : Prop :=
  ∀ (k V idx : Type u) [Field k] [AddCommGroup V] [Module k V]
    [Fintype idx] [DecidableEq idx] (b : Module.Basis idx k V)
    (m : ℕ) (ranks : Fin m → ℕ), StrictMono ranks →
    (∀ i, ranks i ≤ Module.finrank k V) →
    ∃ (C : ∀ i : Fin m, ChartSystem (k := k) (V := V) b (ranks i))
      (P : ∀ i : Fin m, SchemePoints (k := k) (V := V) (ranks i)
        (C i).scheme (C i).affinePoints),
      Nonempty (Presentation ranks b C P)

/-- The submodule spanned by the first d vectors of the scalar-extended basis. -/
def prefixSubmodule {n : ℕ} (β : Module.Basis (Fin n) k V) (R : TestAlgebra k) (d : ℕ) :
    Submodule R (R ⊗[k] V) :=
  Submodule.span R ((β.baseChange R) '' { i | i.val < d })

/-- The basis point of the same closed incidence presentation, from any
ordered basis of V. -/
def HasBasisPoints {F : SchemeOver k}
    (j : F ⟶ GrassmannianProduct ranks b C) : Prop :=
  ∀ (n : ℕ) (β : Module.Basis (Fin n) k V),
    ∃ p : Points F (CommAlgCat.of k k), ∀ i : Fin m,
      (productPlanes ranks b C (p ≫ j) i).toSubmodule =
        prefixSubmodule β (CommAlgCat.of k k) (ranks i)

/-- The ambient product action acts by linear transport and restricts to the
flag scheme as a group action. -/
structure Action {F : SchemeOver k} (j : F ⟶ GrassmannianProduct ranks b C)
    (G : GroupScheme k)
    (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k idx) where
  onProduct : G.X ⨯ GrassmannianProduct ranks b C ⟶ GrassmannianProduct ranks b C
  onFlags : G.X ⨯ F ⟶ F
  restricts : onFlags ≫ j = prod.map (𝟙 G.X) j ≫ onProduct
  transport : ∀ (R : TestAlgebra k) (p : Points (G.X ⨯ GrassmannianProduct ranks b C) R)
    (i : Fin m),
    (productPlanes ranks b C (p ≫ onProduct) i).toSubmodule =
      (productPlanes ranks b C (p ≫ prod.snd) i).toSubmodule.map
        (matrixTransport b R (E.hom.app R (p ≫ prod.fst))).toLinearMap
  one_onProduct : ∀ (S : SchemeOver k) (p : S ⟶ GrassmannianProduct ranks b C),
    prod.lift (1 : S ⟶ G.X) p ≫ onProduct = p
  mul_onProduct : ∀ (S : SchemeOver k) (g h : S ⟶ G.X)
      (p : S ⟶ GrassmannianProduct ranks b C),
    prod.lift (g * h) p ≫ onProduct =
      prod.lift g (prod.lift h p ≫ onProduct) ≫ onProduct
  one : ∀ (S : SchemeOver k) (p : S ⟶ F), prod.lift (1 : S ⟶ G.X) p ≫ onFlags = p
  mul : ∀ (S : SchemeOver k) (g h : S ⟶ G.X) (p : S ⟶ F),
    prod.lift (g * h) p ≫ onFlags =
      prod.lift g (prod.lift h p ≫ onFlags) ≫ onFlags

def ConstructionWithAction : Prop :=
  ∀ (k V idx : Type u) [Field k] [AddCommGroup V] [Module k V]
    [Fintype idx] [DecidableEq idx] (b : Module.Basis idx k V)
    (m : ℕ) (ranks : Fin m → ℕ), StrictMono ranks →
    (∀ i, ranks i ≤ Module.finrank k V) →
    ∃ (C : ∀ i : Fin m, ChartSystem (k := k) (V := V) b (ranks i))
      (P : ∀ i : Fin m, SchemePoints (k := k) (V := V) (ranks i)
        (C i).scheme (C i).affinePoints)
      (D : Presentation ranks b C P) (G : GroupScheme k)
      (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k idx),
      Nonempty (Action ranks b C D.inclusion G E) ∧ HasBasisPoints ranks b C D.inclusion

/-- Each family admits an adapted ordered basis on an affine open
neighborhood of every point of its base. -/
def HasLocalAdaptedBases {F : SchemeOver k}
    (j : F ⟶ GrassmannianProduct ranks b C) : Prop :=
  ∀ (S : SchemeOver k) (p : S ⟶ F) (x : S.left),
    ∃ (R : TestAlgebra k) (a : Points S R), IsOpenImmersion a.left ∧ x ∈ Set.range a.left ∧
      ∃ B : Module.Basis (Fin (Module.finrank k V)) R (R ⊗[k] V),
        ∀ i : Fin m, (productPlanes ranks b C ((a ≫ p) ≫ j) i).toSubmodule =
          Submodule.span R (B '' { l | l.val < ranks i })

/-- The local orbit of the rational point of any ordered basis contains
every flag family. -/
def HasLocalTransitivity {F : SchemeOver k} (j : F ⟶ GrassmannianProduct ranks b C)
    (G : GroupScheme k) (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k idx)
    (A : Action ranks b C j G E) : Prop :=
  ∀ (n : ℕ) (β : Module.Basis (Fin n) k V),
    ∃ z : Points F (CommAlgCat.of k k),
      (∀ i : Fin m, (productPlanes ranks b C (z ≫ j) i).toSubmodule =
        prefixSubmodule β (CommAlgCat.of k k) (ranks i)) ∧
      ∀ (S : SchemeOver k) (p : S ⟶ F) (x : S.left),
        ∃ (R : TestAlgebra k) (a : Points S R) (g : Points G.X R),
          IsOpenImmersion a.left ∧ x ∈ Set.range a.left ∧
          prod.lift g (mapPoints (CommAlgCat.ofHom (Algebra.ofId k R)) z) ≫ A.onFlags = a ≫ p

def CompleteConstruction : Prop :=
  ∀ (k V idx : Type u) [Field k] [AddCommGroup V] [Module k V]
    [Fintype idx] [DecidableEq idx] (b : Module.Basis idx k V)
    (m : ℕ) (ranks : Fin m → ℕ), StrictMono ranks →
    (∀ i, ranks i ≤ Module.finrank k V) →
    ∃ (C : ∀ i : Fin m, ChartSystem (k := k) (V := V) b (ranks i))
      (P : ∀ i : Fin m, SchemePoints (k := k) (V := V) (ranks i)
        (C i).scheme (C i).affinePoints)
      (D : Presentation ranks b C P) (G : GroupScheme k)
      (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k idx)
      (A : Action ranks b C D.inclusion G E),
      HasLocalAdaptedBases ranks b C D.inclusion ∧
        HasLocalTransitivity ranks b C D.inclusion G E A

end

end LinearAlgebraicGroups.Specs.FlagIncidence
