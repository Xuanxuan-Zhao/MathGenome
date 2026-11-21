import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FiniteFiltrationConvergence
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Subobject

/-! Independent contract for HA-S06, source lines 616–670.
The input is an associative, possibly noncommutative and nonunital DGA.
All pages are the fixed categorical quotients of HA-F03. Indices `(p,n)`
mean filtration and total degree; hence products add both bidegrees.
No flatness, boundedness, or convergence assumption is used before the
stable-product comparison. `HEq` is used only to align equal integer indices.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe u v
namespace AdvancedHomologicalAlgebra
namespace MultiplicativePages
variable {R : Type u} [CommRing R]

/-- Transport in a family of modules along equality of the grading indices. -/
def reindex (E : ℤ → ℤ → ModuleCat.{v} R) {p n s m : ℤ}
    (hp : p = s) (hn : n = m) : E p n →ₗ[R] E s m :=
  (eqToHom (by subst s; subst m; rfl : E p n = E s m)).hom

/-- The sign uses parity of the integer total degree, including negative degrees. -/
def sign (n : ℤ) : R := (-1 : R) ^ n.natAbs

/-- Homogeneous multiplication on a cochain complex of modules. -/
structure Algebra (K : CochainComplex (ModuleCat.{v} R) ℤ) where
  mul : ∀ n m, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n+m)
  assoc : ∀ n m l (x : K.X n) (y : K.X m) (z : K.X l),
    HEq (mul (n+m) l (mul n m x y) z) (mul n (m+l) x (mul m l y z))
  leibniz : ∀ n m (x : K.X n) (y : K.X m),
    K.d (n+m) (n+m+1) (mul n m x y) =
      (eqToHom (congrArg K.X (by omega : (n+1)+m = n+m+1)))
        (mul (n+1) m (K.d n (n+1) x) y) +
      sign (R := R) n •
        (eqToHom (congrArg K.X (by omega : n+(m+1) = n+m+1)))
          (mul n (m+1) x (K.d m (m+1) y))

variable {K : CochainComplex (ModuleCat.{v} R) ℤ}

/-- The optional unit is closed, as required for a unital cochain DGA. -/
structure Unit (B : Algebra K) where
  one : K.X 0
  closed : K.d 0 1 one = 0
  left : ∀ n (x : K.X n), HEq (B.mul 0 n one x) x
  right : ∀ n (x : K.X n), HEq (B.mul n 0 x one) x

/-- Membership in an actual subobject, via its canonical range submodule. -/
abbrev carrier {M : ModuleCat.{v} R} (S : Subobject M) : Submodule R M :=
  ModuleCat.subobjectModule M S

/-- Exactly the multiplicativity hypothesis on the given decreasing filtration. -/
structure Compatible (B : Algebra K) (F : Filtration K) : Prop where
  mul_mem : ∀ p n s m (x : K.X n) (y : K.X m),
    x ∈ carrier (F.piece p n) → y ∈ carrier (F.piece s m) →
      B.mul n m x y ∈ carrier (F.piece (p+s) (n+m))

variable (B : Algebra K) (F : Filtration K) (D : F03Specs.PageData F)
open FilteredPage

abbrev pageObject (r p n : ℤ) : ModuleCat.{v} R := PageCohomology.object F D r p n

/-- Associative products on the actual page objects, with the representative
formula, Leibniz rule, and the optional unit assertion at every nonnegative page. -/
structure Products where
  mul : ∀ r, 0 ≤ r → ∀ p n s m,
    pageObject F D r p n →ₗ[R] pageObject F D r s m →ₗ[R]
      pageObject F D r (p+s) (n+m)
  representative : ∀ r hr p n s m
    (x : (almost F r p n : ModuleCat R)) (y : (almost F r s m : ModuleCat R)),
    ∃ z : (almost F r (p+s) (n+m) : ModuleCat R),
      (almost F r (p+s) (n+m)).arrow z =
        B.mul n m ((almost F r p n).arrow x) ((almost F r s m).arrow y) ∧
      mul r hr p n s m (toPage F r p n (D.containment r p n) x)
        (toPage F r s m (D.containment r s m) y) =
          toPage F r (p+s) (n+m) (D.containment r (p+s) (n+m)) z
  assoc : ∀ r hr p n s m t l (x : pageObject F D r p n)
    (y : pageObject F D r s m) (z : pageObject F D r t l),
    HEq (mul r hr (p+s) (n+m) t l (mul r hr p n s m x y) z)
      (mul r hr p n (s+t) (m+l) x (mul r hr s m t l y z))
  leibniz : ∀ r hr p n s m (x : pageObject F D r p n) (y : pageObject F D r s m),
    D.differential r hr (p+s) (n+m) (mul r hr p n s m x y) =
      reindex (pageObject F D r) (by omega : (p+r)+s = (p+s)+r)
        (by omega : (n+1)+m = (n+m)+1)
        (mul r hr (p+r) (n+1) s m (D.differential r hr p n x) y) +
      sign (R := R) n •
        reindex (pageObject F D r) (by omega : p+(s+r) = (p+s)+r)
          (by omega : n+(m+1) = (n+m)+1)
          (mul r hr p n (s+r) (m+1) x (D.differential r hr s m y))
  unit : ∀ (U : Unit B), U.one ∈ carrier (F.piece 0 0) → ∀ r hr,
    ∃ a : (almost F r 0 0 : ModuleCat R), (almost F r 0 0).arrow a = U.one ∧
      (∀ p n (x : pageObject F D r p n),
        HEq (mul r hr 0 0 p n (toPage F r 0 0 (D.containment r 0 0) a) x) x) ∧
      (∀ p n (x : pageObject F D r p n),
        HEq (mul r hr p n 0 0 x (toPage F r 0 0 (D.containment r 0 0) a)) x)

variable (P : Products B F D)

/-- The product induced on page cohomology is specified on all cycles,
and the actual HA-F04 canonical next-page isomorphisms preserve it. -/
structure NextCompatibility (C : PageCohomology.Data F D) where
  mul : ∀ r (hr : 0 ≤ r) p n s m,
    (PageCohomology.shortComplex F D r hr p n).homology →ₗ[R]
    (PageCohomology.shortComplex F D r hr s m).homology →ₗ[R]
    (PageCohomology.shortComplex F D r hr (p+s+r) (n+m+1)).homology
  cycle_formula : ∀ r hr p n s m
    (x : (PageCohomology.shortComplex F D r hr p n).cycles)
    (y : (PageCohomology.shortComplex F D r hr s m).cycles),
    ∃ z : (PageCohomology.shortComplex F D r hr (p+s+r) (n+m+1)).cycles,
      HEq ((PageCohomology.shortComplex F D r hr (p+s+r) (n+m+1)).iCycles z)
        (P.mul r hr (p+r) (n+1) (s+r) (m+1)
          ((PageCohomology.shortComplex F D r hr p n).iCycles x)
          ((PageCohomology.shortComplex F D r hr s m).iCycles y)) ∧
      mul r hr p n s m
        ((PageCohomology.shortComplex F D r hr p n).homologyπ x)
        ((PageCohomology.shortComplex F D r hr s m).homologyπ y) =
          (PageCohomology.shortComplex F D r hr (p+s+r) (n+m+1)).homologyπ z
  next_formula : ∀ r hr p n s m
    (x : pageObject F D (r+1) (p+r) (n+1))
    (y : pageObject F D (r+1) (s+r) (m+1)),
    mul r hr p n s m ((C.nextIso r hr p n).hom x) ((C.nextIso r hr s m).hom y) =
      (C.nextIso r hr (p+s+r) (n+m+1)).hom
        (reindex (pageObject F D (r+1)) (by omega) (by omega)
          (P.mul (r+1) (by omega) (p+r) (n+1) (s+r) (m+1) x y))

open FiniteFiltrationConvergence

/-- Cohomology products, their actual image filtration, and its associated
graded products are specified by the original closed representatives. -/
structure CohomologyProducts where
  mul : ∀ n m, K.homology n →ₗ[R] K.homology m →ₗ[R] K.homology (n+m)
  representative : ∀ n m (x : K.cycles n) (y : K.cycles m),
    ∃ z : K.cycles (n+m), K.iCycles (n+m) z = B.mul n m (K.iCycles n x) (K.iCycles m y) ∧
      mul n m (K.homologyπ n x) (K.homologyπ m y) = K.homologyπ (n+m) z
  filtered : ∀ p n s m (x : (cohomologyPiece F p n : ModuleCat R))
    (y : (cohomologyPiece F s m : ModuleCat R)),
    ∃ z : (cohomologyPiece F (p+s) (n+m) : ModuleCat R),
      (cohomologyPiece F (p+s) (n+m)).arrow z =
        mul n m ((cohomologyPiece F p n).arrow x) ((cohomologyPiece F s m).arrow y)
  gradedMul : ∀ p n s m, (gradedCohomology F p n : ModuleCat R) →ₗ[R]
    (gradedCohomology F s m : ModuleCat R) →ₗ[R]
    (gradedCohomology F (p+s) (n+m) : ModuleCat R)
  graded_formula : ∀ p n s m (x : (cohomologyPiece F p n : ModuleCat R))
    (y : (cohomologyPiece F s m : ModuleCat R))
    (z : (cohomologyPiece F (p+s) (n+m) : ModuleCat R)),
    (cohomologyPiece F (p+s) (n+m)).arrow z =
      mul n m ((cohomologyPiece F p n).arrow x) ((cohomologyPiece F s m).arrow y) →
    gradedMul p n s m (cokernel.π (Subobject.ofLE _ _ (cohomologyPiece_decreasing F p n)) x)
      (cokernel.π (Subobject.ofLE _ _ (cohomologyPiece_decreasing F s m)) y) =
      cokernel.π (Subobject.ofLE _ _ (cohomologyPiece_decreasing F (p+s) (n+m))) z

/-- Finite convergence is used only for this comparison. The isomorphisms
are precisely the HA-S01 isomorphisms fixed by their closed-class formula. -/
def StableCompatibility (H : CohomologyProducts B F) : Prop :=
  DegreewiseFinite F → ∀ r (hr : 0 ≤ r) p n s m,
    Stabilized F r p n → Stabilized F r s m → Stabilized F r (p+s) (n+m) →
    ∀ (L : LimitIso F D r p n) (M : LimitIso F D r s m)
      (N : LimitIso F D r (p+s) (n+m))
      (x : pageObject F D r p n) (y : pageObject F D r s m),
    H.gradedMul p n s m (L.iso.hom x) (M.iso.hom y) = N.iso.hom (P.mul r hr p n s m x y)

end MultiplicativePages
namespace S06Specs
open MultiplicativePages

/-- Numerator closure, a proved part of the representative construction. -/
def NumeratorClosure : Prop := ∀ {R : Type u} [CommRing R]
  {K : CochainComplex (ModuleCat.{v} R) ℤ}
  (B : Algebra K) (F : Filtration K), Compatible B F →
  ∀ (r p n s m : ℤ) (x : K.X n) (y : K.X m),
    x ∈ carrier (FilteredPage.almost F r p n) →
    y ∈ carrier (FilteredPage.almost F r s m) →
    B.mul n m x y ∈ carrier (FilteredPage.almost F r (p+s) (n+m))

/-- Elementwise version of the actual page's alternate quotient presentation. -/
def PageZeroCriterion : Prop := ∀ {R : Type u} [CommRing R]
  {K : CochainComplex (ModuleCat.{v} R) ℤ} (F : Filtration K) (r p n : ℤ)
  (h : FilteredPage.boundaries F r p n ≤ FilteredPage.cycles F r p n)
  (x : (FilteredPage.almost F r p n : ModuleCat R)),
  FilteredPage.toPage F r p n h x = 0 ↔
    (FilteredPage.almost F r p n).arrow x ∈ carrier (FilteredPage.denominator F r p n)

/-- The all-page construction, including associativity, derivations and units. -/
def PageProducts : Prop := ∀ {R : Type u} [CommRing R]
  {K : CochainComplex (ModuleCat.{v} R) ℤ} (B : Algebra K) (F : Filtration K),
  Compatible B F → ∀ D : F03Specs.PageData F, Nonempty (Products B F D)

/-- Full original scope: every associative cochain DGA, any compatible decreasing
filtration, all nonnegative pages, optional units, next-page and stable products. -/
def FullStatement : Prop := ∀ {R : Type u} [CommRing R]
  {K : CochainComplex (ModuleCat.{v} R) ℤ} (B : Algebra K) (F : Filtration K),
  Compatible B F → ∀ (D : F03Specs.PageData F) (C : PageCohomology.Data F D),
    ∃ P : Products B F D, Nonempty (NextCompatibility B F D P C) ∧
      ∃ H : CohomologyProducts B F, StableCompatibility B F D P H

end S06Specs
end AdvancedHomologicalAlgebra
