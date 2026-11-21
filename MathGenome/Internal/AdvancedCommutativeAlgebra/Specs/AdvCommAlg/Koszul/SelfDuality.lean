import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.Resolution
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Pi

/-! Independent definitions and expected propositions for RK-10,
`paper.tex:2345–2378`. Negative reversed degrees mean zero, rather than
truncated natural subtraction. The degree-family formulation below includes
every term and every nonzero possible differential of the bounded complex.
All goal-local declarations use a dedicated namespace so independently compiled
coefficient-cohomology specifications can be imported alongside this module. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
universe u v
namespace AdvCommAlg.Koszul.SelfDuality
variable {R : Type u} [CommRing R]

/-- Hom into an arbitrary coefficient module. The source modules can be small,
while the coefficients may lie in a larger universe. -/
def homCoefficient (M : Type v) [AddCommGroup M] [Module R M] :
    (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{max u v} R where
  obj N := ModuleCat.of R (N.unop →ₗ[R] M)
  map f := ModuleCat.ofHom (f.unop.hom.lcomp R M)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

instance (M : Type v) [AddCommGroup M] [Module R M] :
    (homCoefficient (R := R) M).Additive where
  map_add := by
    intros X Y f g
    apply ModuleCat.hom_ext
    change (f.unop.hom + g.unop.hom).lcomp R M =
      f.unop.hom.lcomp R M + g.unop.hom.lcomp R M
    ext z n
    simp

/-- The cochain complex Hom_R(K(x),M); its differential is precomposition. -/
def cochainComplex (M : Type v) [AddCommGroup M] [Module R M] (x : List R) :
    CochainComplex (ModuleCat.{max u v} R) ℕ :=
  (((homCoefficient M).rightOp.mapHomologicalComplex _).obj (listComplex x)).unop

/-- Koszul cohomology of the actual Hom complex. -/
def cohomology (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (q : ℕ) :
    ModuleCat.{max u v} R := (cochainComplex M x).homology q

/-- Ext derived in the first argument of Hom, with unrestricted coefficient
universe. `ordinaryExtComparison` below also specifies its bridge to Mathlib Ext. -/
def quotientExt (M : Type v) [AddCommGroup M] [Module R M] (I : Ideal R) (q : ℕ) :
    ModuleCat.{max u v} R :=
  (((homCoefficient M).rightOp.leftDerived q).obj (ModuleCat.of R (R ⧸ I))).unop

/-- Determinant line of the finite free module with its ordered list basis. -/
abbrev determinantLine (x : List R) := ⋀[R]^x.length (Fin x.length → R)

/-- The unique top-degree subset, including when the list is empty. -/
def topSubset (x : List R) : Set.powersetCard (Fin x.length) x.length :=
  ⟨Finset.univ, by simp⟩

instance topSubsetsUnique (x : List R) :
    Unique (Set.powersetCard (Fin x.length) x.length) where
  default := topSubset x
  uniq s := Subtype.ext (Finset.eq_univ_of_card _ (by simpa using s.property))

/-- The ordered basis orientation sends its full increasing wedge to 1. -/
def orientation (x : List R) : determinantLine x ≃ₗ[R] R :=
  (listBasis x x.length).equivFun.trans (LinearEquiv.funUnique _ R R)

/-- Exterior multiplication into the determinant line, with its actual degrees. -/
def topWedge (x : List R) (q p : ℕ) (h : q + p = x.length) :
    (⋀[R]^q (Fin x.length → R)) →ₗ[R]
      (⋀[R]^p (Fin x.length → R)) →ₗ[R] determinantLine x :=
  (exteriorPower.wedge R _ q p).compr₂
    (LinearEquiv.ofEq _ _ (congrArg (fun n => ⋀[R]^n (Fin x.length → R)) h)).toLinearMap

/-- Oriented scalar-valued exterior multiplication. -/
def scalarWedge (x : List R) (q p : ℕ) (h : q + p = x.length) :
    (⋀[R]^q (Fin x.length → R)) →ₗ[R]
      (⋀[R]^p (Fin x.length → R)) →ₗ[R] R :=
  (topWedge x q p h).compr₂ (orientation x).toLinearMap

/-- The sign converting precomposition by d to the unsigned reversed d. -/
def dualitySign (R : Type u) [CommRing R] (q : ℕ) : R := (-1 : R) ^ (q * (q-1) / 2)

/-- All degree maps, their signed exterior formula, and their differential
compatibility. Degrees above the length are separately specified to be zero.
This is the bounded cochain-isomorphism data, with the determinant twist. -/
structure SignedDualityData (M : Type v) [AddCommGroup M] [Module R M] (x : List R) where
  equiv : ∀ q p (h : q+p=x.length),
    ((⋀[R]^p (Fin x.length → R)) ⊗[R] (M ⊗[R] Module.Dual R (determinantLine x))) ≃ₗ[R]
      ((⋀[R]^q (Fin x.length → R)) →ₗ[R] M)
  formula : ∀ q p h a m φ w,
    equiv q p h (a ⊗ₜ[R] (m ⊗ₜ[R] φ)) w =
      dualitySign R q • (φ (topWedge x q p h w a) • m)
  comm : ∀ q p (h : q + (p+1) = x.length)
    (z : (⋀[R]^(p+1) (Fin x.length → R)) ⊗[R]
      (M ⊗[R] Module.Dual R (determinantLine x)))
    (w : ⋀[R]^(q+1) (Fin x.length → R)),
    equiv (q+1) p (by omega)
        (coefficientDifferential (M ⊗[R] Module.Dual R (determinantLine x)) x p z) w =
      equiv q (p+1) h z (differential (listForm x) q w)

end AdvCommAlg.Koszul.SelfDuality

namespace Specs.AdvCommAlg.Koszul.SelfDuality
open _root_.AdvCommAlg.Koszul _root_.AdvCommAlg.Koszul.SelfDuality

def cochainComplexType := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R),
  CochainComplex (ModuleCat.{max u v} R) ℕ

def cochainComplexValue : cochainComplexType.{u,v} := @cochainComplex

def cohomologyType := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (q : ℕ), ModuleCat.{max u v} R

def cohomologyValue : cohomologyType.{u,v} := @cohomology

def cochainDifferential : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (q : ℕ)
  (f : (⋀[R]^q (Fin x.length → R)) →ₗ[R] M),
  ((cochainComplex M x).d q (q+1)).hom f = f.comp (differential (listForm x) q)

def signedSelfDuality : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R),
  Nonempty (SignedDualityData M x)

def cochainBounded : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (q : ℕ),
  x.length < q → Subsingleton ((cochainComplex M x).X q)

def cohomologyDuality : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (q : ℕ),
  (q ≤ x.length → Nonempty (cohomology M x q ≃ₗ[R] homology M x (x.length-q))) ∧
    (x.length < q → Subsingleton (cohomology M x q))

def cohomologyExt : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R),
  RingTheory.Sequence.IsRegular R x → ∀ q : ℕ,
  Nonempty (cohomology M x q ≅ quotientExt M (listIdeal x) q)

def ordinaryExtComparison : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type u) [AddCommGroup M] [Module R M] (I : Ideal R) (q : ℕ),
  Nonempty (quotientExt M I q ≅
    ((Ext R (ModuleCat.{u} R) q).obj (op (ModuleCat.of R (R ⧸ I)))).obj (ModuleCat.of R M))

def extConcentration : Prop := ∀ {R : Type u} [CommRing R] (x : List R),
  RingTheory.Sequence.IsRegular R x →
  (∀ q : ℕ, q ≠ x.length → IsZero (quotientExt R (listIdeal x) q)) ∧
    Nonempty (quotientExt R (listIdeal x) x.length ≃ₗ[R] (R ⧸ listIdeal x))

end Specs.AdvCommAlg.Koszul.SelfDuality
