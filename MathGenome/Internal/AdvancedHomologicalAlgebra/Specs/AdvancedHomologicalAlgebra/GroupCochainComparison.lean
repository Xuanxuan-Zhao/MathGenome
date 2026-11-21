import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupBarResolution
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! HA-A02, source lines 2899–2953. The complex on natural-number degrees
uses unsigned precomposition. `Large` uses the original ring and group,
with a bar object in the universe of the coefficient category. -/
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra MonoidAlgebra
universe u
namespace Specs.AdvancedHomologicalAlgebra.GroupCochainComparison
variable (k G : Type u) [CommRing k] [Group G]

abbrev Coeff := ModuleCat.{u} k[G]
abbrev representation (M : Coeff k G) : Rep.{u} k G := Rep.ofModuleMonoidAlgebra.obj M
abbrev cochains (M : Coeff k G) := groupCohomology.inhomogeneousCochains (representation k G M)
abbrev homCochains (M : Coeff k G) := (GroupBar.complex k G).linearYonedaObj k (representation k G M)

abbrev cochainsFunctor : Coeff k G ⥤ CochainComplex (ModuleCat.{u} k) ℕ :=
  Rep.ofModuleMonoidAlgebra ⋙ groupCohomology.cochainsFunctor k G

/-- Hom from the fixed homogeneous resolution, with postcomposition in M. -/
def homogeneousCochainsFunctor : Coeff k G ⥤ CochainComplex (ModuleCat.{u} k) ℕ where
  obj M := homCochains k G M
  map b :=
    { f n := ((linearYoneda k (Rep k G)).map (Rep.ofModuleMonoidAlgebra.map b)).app
        (Opposite.op (GroupBar.B k G n))
      comm' i j _ := by ext φ; rfl }
  map_id M := by ext n φ; rfl
  map_comp b c := by ext n φ; rfl

/-- The coefficient action is the pointwise action induced by module maps. -/
abbrev cochainCohomology (n : ℕ) : Coeff k G ⥤ ModuleCat.{u} k :=
  cochainsFunctor k G ⋙ HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) n

/-- Hom over k[G], transported along the standard equivalence with representations. -/
def moduleCoordinatesType : Prop := ∀ (M : Coeff k G) (n : ℕ),
  ∃ e : ((Rep.toModuleMonoidAlgebra.obj (GroupBar.B k G n)) ⟶ M) ≃ₗ[k]
      ((Fin n → G) → representation k G M),
    ∀ φ g, e φ g = φ.hom ((GroupBar.B k G n).ρ.asModuleEquiv.symm
      (MonoidAlgebra.single (Fin.partialProd g) 1))

/-- The vertex tuple of the source's basis [g₁|⋯|gₙ]. -/
def vertices {n : ℕ} (g : Fin n → G) : Fin (n+1) → G := Fin.partialProd g

/-- The last term is written separately. `contractNth` multiplies adjacent
entries at an internal position, and drops the last entry at the last position. -/
def differentialFormula (M : Coeff k G) (n : ℕ)
    (f : (Fin n → G) → representation k G M) (g : Fin (n+1) → G) : representation k G M :=
  (representation k G M).ρ (g 0) (f (fun i => g i.succ)) +
    (∑ i : Fin n, (-1 : k) ^ (i.val+1) • f (Fin.contractNth i.castSucc (· * ·) g)) +
    (-1 : k) ^ (n+1) • f (fun i => g i.castSucc)

def coordinatesType : Prop := ∀ (M : Coeff k G) (n : ℕ),
  ∃ e : (GroupBar.B k G n ⟶ representation k G M) ≃ₗ[k]
      ((Fin n → G) → representation k G M),
    ∀ φ g, e φ g = φ.hom (MonoidAlgebra.single (vertices G g) 1)

def complexType : Prop :=
  ∃ e : homogeneousCochainsFunctor k G ≅ cochainsFunctor k G,
    ∀ (M : Coeff k G) (n : ℕ)
      (φ : GroupBar.B k G n ⟶ representation k G M) (g : Fin n → G),
      (((e.hom.app M).f n).hom φ) g = φ.hom (MonoidAlgebra.single (vertices G g) 1)

def differentialType : Prop := ∀ (M : Coeff k G) (n : ℕ)
    (f : (Fin n → G) → representation k G M) (g : Fin (n+1) → G),
  ((cochains k G M).d n (n+1)).hom f g = differentialFormula k G M n f g

def zeroType : Prop := ∀ M : Coeff k G,
  ∃ e : (cochains k G M).X 0 ≃ₗ[k] M,
    ∀ f, e f = f Fin.elim0

/-- The coefficient map is actual postcomposition on every cochain. -/
def naturalCoordinatesType : Prop := ∀ (M N : Coeff k G) (b : M ⟶ N) (n : ℕ)
    (φ : GroupBar.B k G n ⟶ representation k G M) (g : Fin n → G),
  (φ ≫ Rep.ofModuleMonoidAlgebra.map b).hom (MonoidAlgebra.single (vertices G g) 1) =
    (Rep.ofModuleMonoidAlgebra.map b).hom
      (φ.hom (MonoidAlgebra.single (vertices G g) 1))

/-- The comparison uses the full augmented free resolution from HA-A02-Bar. -/
def resolutionComparisonType : Prop := GroupBar.Resolution k G ∧ complexType k G

local instance canonicalDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

/-- Comparison with HA-A01's actual derived invariants, natural in every
coefficient homomorphism, as an isomorphism of k-module-valued functors. -/
def cohomologyType : Prop := ∀ n : ℕ,
  Nonempty (GroupDerivedInvariants.cohomology.{u,u,0} k G n ≅ cochainCohomology k G n)

-- Closed interfaces for independent declaration checking.
def coordinates_specExpected : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G], coordinatesType k G

def moduleCoordinates_specExpected : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G], moduleCoordinatesType k G

def complexComparisonExpected : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G], complexType k G

def differentialExpected : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G], differentialType k G

def degreeZeroExpected : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G], zeroType k G

def naturalCoordinatesExpected : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G], naturalCoordinatesType k G

def resolutionComparisonExpected : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G], resolutionComparisonType k G

def cohomologyExpected : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G], cohomologyType k G

end Specs.AdvancedHomologicalAlgebra.GroupCochainComparison

namespace Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large
universe v w
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

abbrev Coeff := GroupDerivedInvariants.GroupModule.{u,v,w} k G
abbrev representation (M : Coeff.{u,v,w} k G) : Rep.{max u v w} k G :=
  Rep.ofModuleMonoidAlgebra.obj M

/-- Postcomposition in the original coefficient, on Hom from the lifted
presentation of the actual bar complex. -/
def repHomogeneousFunctor : Rep.{max u v w} k G ⥤ CochainComplex (ModuleCat.{max u v w} k) ℕ where
  obj M := (GroupBar.Large.complex.{u,v,w} k G).linearYonedaObj k M
  map f :=
    { f n := ((linearYoneda k (Rep k G)).map f).app
        (Opposite.op (GroupBar.Large.B k G n))
      comm' _ _ _ := by ext φ; rfl }
  map_id _ := by ext n φ; rfl
  map_comp _ _ := by ext n φ; rfl

abbrev homogeneousFunctor : Coeff.{u,v,w} k G ⥤ CochainComplex (ModuleCat.{max u v w} k) ℕ :=
  Rep.ofModuleMonoidAlgebra ⋙ repHomogeneousFunctor.{u,v,w} k G

abbrev repHomogeneousCohomology (n : ℕ) : Rep.{max u v w} k G ⥤ ModuleCat.{max u v w} k :=
  repHomogeneousFunctor.{u,v,w} k G ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} k) (.up ℕ) n

abbrev repDerivedCohomology (n : ℕ) : Rep.{max u v w} k G ⥤ ModuleCat.{max u v w} k :=
  Rep.toModuleMonoidAlgebra ⋙ GroupDerivedInvariants.cohomology.{u,v,w} k G n

abbrev coordinates (M : Coeff.{u,v,w} k G) (n : ℕ) :=
  (Fin n → G) → representation k G M

def differential (M : Coeff.{u,v,w} k G) (n : ℕ)
    (f : coordinates k G M n) (g : Fin (n+1) → G) : representation k G M :=
  (representation k G M).ρ (g 0) (f (fun i => g i.succ)) +
    (∑ i : Fin n, (-1 : k) ^ (i.val+1) • f (Fin.contractNth i.castSucc (· * ·) g)) +
    (-1 : k) ^ (n+1) • f (fun i => g i.castSucc)

/-- Identifies the cochains with functions on the original `G^n` and checks
the signed differential and coefficient action in these same coordinates. -/
def comparisonType : Prop :=
  ∃ e : ∀ (M : Coeff.{u,v,w} k G) (n : ℕ),
      ((homogeneousFunctor k G).obj M).X n ≃ₗ[k] coordinates k G M n,
    (∀ (M : Coeff.{u,v,w} k G) (n : ℕ)
      (φ : GroupBar.Large.B k G n ⟶ representation k G M) (g : Fin n → G),
      e M n φ g = φ.hom (GroupBar.Large.single k G (Fin.partialProd g) 1)) ∧
    (∀ (M : Coeff.{u,v,w} k G) (n : ℕ) φ (g : Fin (n+1) → G),
      e M (n+1) ((((homogeneousFunctor k G).obj M).d n (n+1)).hom φ) g =
        differential k G M n (e M n φ) g) ∧
    (∀ (M N : Coeff.{u,v,w} k G) (a : M ⟶ N) (n : ℕ) φ (g : Fin n → G),
      e N n ((((homogeneousFunctor k G).map a).f n).hom φ) g =
        (Rep.ofModuleMonoidAlgebra.map a).hom (e M n φ g)) ∧
    (∀ M : Coeff.{u,v,w} k G,
      ∃ e₀ : coordinates k G M 0 ≃ₗ[k] representation k G M,
        ∀ f, e₀ f = f Fin.elim0) ∧
    (∀ (M : Coeff.{u,v,w} k G) (n : ℕ),
      ∃ eR : ((Rep.toModuleMonoidAlgebra.obj (GroupBar.Large.B.{u,v,w} k G n)) ⟶ M) ≃ₗ[k]
          coordinates k G M n,
        ∀ φ g, eR φ g = φ.hom ((GroupBar.Large.B.{u,v,w} k G n).ρ.asModuleEquiv.symm
          (GroupBar.Large.single k G (Fin.partialProd g) 1)))

/-- The very same homogeneous cochain functor computes right-derived
invariants in HA-A01, in the original group-algebra module category. -/
def cohomologyType : Prop := ∀ n : ℕ,
  Nonempty (GroupDerivedInvariants.cohomology.{u,v,w} k G n ≅
    homogeneousFunctor.{u,v,w} k G ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} k) (.up ℕ) n)

def comparisonExpected : Prop := ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
  comparisonType.{u,v,w} k G

def cohomologyExpected : Prop := ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
  cohomologyType.{u,v,w} k G

end Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large
