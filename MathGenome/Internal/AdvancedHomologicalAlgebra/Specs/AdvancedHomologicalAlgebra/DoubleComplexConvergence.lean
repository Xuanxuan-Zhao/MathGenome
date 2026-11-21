import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DoubleComplexFirstPages
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FiniteTargetComparison
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.QuasiIso

/-! HA-B04, convergence and comparison, source lines 886–898 and 910–929.
The augmentation assertions are allocated separately to HA-B04-Assembly.
The example of distinct cohomology filtrations witnesses lines 701–703.
All bounds are degreewise. -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra.DoubleComplexConvergence
open DoubleTotalization FiniteDiagonalFiltrations FiniteFiltrationConvergence
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Convergence of the actual filtered pages to the associated graded of the
image filtration on cohomology, including canonical representative formulas. -/
structure Converges {T : CochainComplex A ℤ} (F : Filtration T) : Prop where
  finite : FiniteFiltrationConvergence.DegreewiseFinite F
  target : CohomologyFiltrationData F
  stabilization : ∀ n, ∃ R : ℤ, 0 ≤ R ∧
    ∀ r, R ≤ r → ∀ p, Stabilized F r p n
  limit : ∀ (D : F03Specs.PageData F) r p n, 0 ≤ r → Stabilized F r p n →
    Nonempty (LimitIso F D r p n)
  differential : ∀ (D : F03Specs.PageData F) n, ∃ R : ℤ, 0 ≤ R ∧
    ∀ r (hr : 0 ≤ r), R ≤ r → ∀ p, D.differential r hr p n = 0

namespace Specs
/-- Every realization of each of the two prescribed filtrations converges.
Their existence and the existence of totalization are provided by HA-B02. -/
def Convergence : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  (K : Bicomplex A), FiniteDiagonals K → ∀ [K.HasTotal (ComplexShape.up ℤ)]
  (Fc Fr : Filtration (sumTotal K)),
  HasFiltrationFormula K Prod.fst Fc → HasFiltrationFormula K Prod.snd Fr →
  Converges Fc ∧ Converges Fr

/-- Naturality for each filtration separately, for arbitrary induced page maps
and canonical limiting identifications satisfying their representative formulas. -/
def Naturality : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  (K L : Bicomplex A), FiniteDiagonals K → FiniteDiagonals L →
  ∀ [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
  (axis : ℤ × ℤ → ℤ), (axis = Prod.fst ∨ axis = Prod.snd) →
  ∀ (F : Filtration (sumTotal K)) (G : Filtration (sumTotal L)),
  HasFiltrationFormula K axis F → HasFiltrationFormula L axis G →
  ∀ (f : K ⟶ L) (g : FilteredMap ⟨sumTotal K,F⟩ ⟨sumTotal L,G⟩),
  g.hom = HomologicalComplex₂.total.map f (ComplexShape.up ℤ) →
  ∀ (D : F03Specs.PageData F) (E : F03Specs.PageData G)
  (M : FilteredPageFunctoriality.MapData g D E) r p n
  (I : LimitIso F D r p n) (J : LimitIso G E r p n),
  Stabilized F r p n → Stabilized G r p n →
  M.map r p n ≫ J.iso.hom = I.iso.hom ≫ gradedCohomologyMap g p n

/-- Either columnwise or rowwise quasi-isomorphisms suffice. -/
def Comparison : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  (K L : Bicomplex A), FiniteDiagonals K → FiniteDiagonals L →
  ∀ [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)] (f : K ⟶ L),
  ((∀ p, QuasiIso (f.f p)) ∨
    (∀ p, QuasiIso
      (((HomologicalComplex₂.flipFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f).f p))) →
  QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.up ℤ))

/-- Exactness means acyclicity in every integer degree, with no global bounds. -/
def Acyclicity : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  (K : Bicomplex A), FiniteDiagonals K → ∀ [K.HasTotal (ComplexShape.up ℤ)],
  ((∀ p, (K.X p).Acyclic) ∨ (∀ p, (K.flip.X p).Acyclic)) → (sumTotal K).Acyclic

/-- The double complex with one rational line in bidegree (0,1). -/
def singleBicomplex : Bicomplex (ModuleCat.{0} ℚ) :=
  HomologicalComplex₂.ofGradedObject _ _
    (fun i => if i = ((0 : ℤ), (1 : ℤ)) then ModuleCat.of ℚ ℚ else ModuleCat.of ℚ PUnit)
    (fun _ _ _ => 0) (fun _ _ _ => 0)
    (by intros; rfl) (by intros; rfl) (by intros; simp) (by intros; simp)
    (by intros; simp)

local instance : singleBicomplex.HasTotal (ComplexShape.up ℤ) := by
  intro n
  infer_instance

/-- The actual degree-one images for the two standard filtrations differ. -/
def DistinctCohomologyFiltrations : Prop :=
  FiniteDiagonals singleBicomplex ∧
  Nonempty ((sumTotal singleBicomplex).homology 1 ≅ ModuleCat.of ℚ ℚ) ∧
  ∃ Fc Fr : Filtration (sumTotal singleBicomplex),
    HasFiltrationFormula singleBicomplex Prod.fst Fc ∧
    HasFiltrationFormula singleBicomplex Prod.snd Fr ∧
    cohomologyPiece Fc 1 1 = ⊥ ∧
    cohomologyPiece Fr 1 1 = ⊤ ∧
    cohomologyPiece Fc 1 1 ≠ cohomologyPiece Fr 1 1

end Specs
end AdvancedHomologicalAlgebra.DoubleComplexConvergence
