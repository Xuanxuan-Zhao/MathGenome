import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FilteredPageFunctoriality

/-! HA-S01: degreewise finite decreasing filtrations in an arbitrary abelian
category. Indices `(p,n)` mean filtration and total cochain degree. Finiteness
is degreewise: there is no bound on the complex or a bound shared by degrees.
Completeness below is the universal property of the inverse limit of the
quotients; it does not postulate existence of other infinite limits in A. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra
namespace FiniteFiltrationConvergence
open FilteredPage
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex A ℤ} (F : Filtration K)

/-- The source hypothesis, with bounds allowed to depend on n. -/
def DegreewiseFinite : Prop := ∀ n : ℤ, ∃ a b : ℤ,
  (∀ p, p ≤ a → F.piece p n = ⊤) ∧ (∀ p, b ≤ p → F.piece p n = ⊥)

/-- Actual closed representatives in filtration degree p. -/
abbrev closed (p n : ℤ) : Subobject (K.X n) :=
  F.piece p n ⊓ kernelSubobject (K.d n (n+1))

/-- Ambient boundaries lying in the filtration step. -/
abbrev exactPart (p n : ℤ) : Subobject (K.X n) :=
  F.piece p n ⊓ imageSubobject (K.d (n-1) n)

abbrev stableCycles (p n : ℤ) : Subobject ((F.graded p).X n) :=
  imageSubobject (gradedRepresentative F p n (closed F p n) inf_le_left)

abbrev stableBoundaries (p n : ℤ) : Subobject ((F.graded p).X n) :=
  imageSubobject (gradedRepresentative F p n (exactPart F p n) inf_le_left)

/-- Stabilization is asserted for the actual cycle and boundary subobjects,
not merely existence of some abstractly isomorphic page objects. -/
def Stabilized (r p n : ℤ) : Prop :=
  cycles F r p n = stableCycles F p n ∧
  boundaries F r p n = stableBoundaries F p n

/-- The filtration on cohomology specified in the source. -/
abbrev cohomologyPiece (p n : ℤ) : Subobject (K.homology n) :=
  imageSubobject (HomologicalComplex.homologyMap (F.inclusion p) n)

theorem cohomologyPiece_decreasing (p n : ℤ) :
    cohomologyPiece F (p+1) n ≤ cohomologyPiece F p n := by
  have h : F.transition p ≫ F.inclusion p = F.inclusion (p+1) := by
    ext i
    exact Subobject.ofLE_arrow _
  have hh := imageSubobject_comp_le
    (HomologicalComplex.homologyMap (F.transition p) n)
    (HomologicalComplex.homologyMap (F.inclusion p) n)
  rw [← HomologicalComplex.homologyMap_comp, h] at hh
  exact hh

abbrev gradedCohomology (p n : ℤ) : A :=
  cokernel (Subobject.ofLE _ _ (cohomologyPiece_decreasing F p n))

/-- A quotient tower for any decreasing integer filtration of an object. -/
abbrev quotientMap {H : A} (P : ℤ → Subobject H)
    {p q : ℤ} (h : P q ≤ P p) : cokernel (P q).arrow ⟶ cokernel (P p).arrow :=
  cokernel.map _ _ (Subobject.ofLE _ _ h) (𝟙 H) (by simp)

/-- Completeness, expressed without requiring arbitrary limits in A. -/
def Complete {H : A} (P : ℤ → Subobject H) : Prop :=
  ∀ (T : A) (z : ∀ p, T ⟶ cokernel (P p).arrow),
    (∀ p q, p ≤ q → ∀ h : P q ≤ P p, z q ≫ quotientMap P h = z p) →
    ∃! f : T ⟶ H, ∀ p, f ≫ cokernel.π (P p).arrow = z p

/-- Finite, decreasing, exhaustive, separated, and complete, in each degree.
The last two order properties avoid assuming an infinite subobject lattice. -/
structure CohomologyFiltrationData : Prop where
  decreasing : ∀ p n, cohomologyPiece F (p+1) n ≤ cohomologyPiece F p n
  finite : ∀ n, ∃ a b : ℤ,
    (∀ p, p ≤ a → cohomologyPiece F p n = ⊤) ∧
    (∀ p, b ≤ p → cohomologyPiece F p n = ⊥)
  exhaustive : ∀ n (S : Subobject (K.homology n)),
    (∀ p, cohomologyPiece F p n ≤ S) → S = ⊤
  separated : ∀ n (S : Subobject (K.homology n)),
    (∀ p, S ≤ cohomologyPiece F p n) → S = ⊥
  complete : ∀ n, Complete (fun p => cohomologyPiece F p n)

/-- The canonical closed representative is a cycle in the filtration step. -/
theorem closed_step_d (p n : ℤ) :
    Subobject.ofLE _ _ (inf_le_left : closed F p n ≤ F.piece p n) ≫
      (F.step p).d n (n+1) = 0 := by
  apply (cancel_mono (F.piece p (n+1)).arrow).1
  simp only [Category.assoc, Filtration.step, Filtration.differential_arrow,
    Subobject.ofLE_arrow_assoc, zero_comp]
  rw [← Subobject.ofLE_arrow (inf_le_right : closed F p n ≤ kernelSubobject (K.d n (n+1))),
    Category.assoc, kernelSubobject_arrow_comp, comp_zero]

/-- The canonical map from closed representatives to the cohomology step. -/
def closedClass (p n : ℤ) : (closed F p n : A) ⟶ (cohomologyPiece F p n : A) :=
  (F.step p).liftCycles (Subobject.ofLE _ _ inf_le_left) (n+1) (by simp)
    (closed_step_d F p n) ≫ (F.step p).homologyπ n ≫
      factorThruImageSubobject (HomologicalComplex.homologyMap (F.inclusion p) n)

def gradedClass (p n : ℤ) : (closed F p n : A) ⟶ gradedCohomology F p n :=
  closedClass F p n ≫ cokernel.π (Subobject.ofLE _ _ (cohomologyPiece_decreasing F p n))

theorem closed_le_almost (r p n : ℤ) : closed F p n ≤ almost F r p n := by
  apply le_inf inf_le_left
  apply Subobject.le_of_factors
  apply pullback_factors
  have h : (closed F p n).arrow ≫ K.d n (n+1) = 0 := by
    rw [← Subobject.ofLE_arrow (inf_le_right : closed F p n ≤ kernelSubobject (K.d n (n+1))),
      Category.assoc, kernelSubobject_arrow_comp, comp_zero]
  rw [h]
  exact Subobject.factors_zero

def closedToPage (D : F03Specs.PageData F) (r p n : ℤ) :
    (closed F p n : A) ⟶ PageCohomology.object F D r p n :=
  Subobject.ofLE _ _ (closed_le_almost F r p n) ≫ toPage F r p n (D.containment r p n)

/-- The representative formula fixes the canonical limiting isomorphism. -/
structure LimitIso (D : F03Specs.PageData F) (r p n : ℤ) where
  iso : PageCohomology.object F D r p n ≅ gradedCohomology F p n
  representative_formula : closedToPage F D r p n ≫ iso.hom = gradedClass F p n

section Maps
variable {X Y : FilteredComplex A}

/-- The commuting square on the two cohomology maps whose images define
filtration degree p. -/
def cohomologySquare (f : FilteredMap X Y) (p n : ℤ) :
    Arrow.mk (HomologicalComplex.homologyMap (X.filtration.inclusion p) n) ⟶
      Arrow.mk (HomologicalComplex.homologyMap (Y.filtration.inclusion p) n) where
  left := HomologicalComplex.homologyMap (f.stepMap p) n
  right := HomologicalComplex.homologyMap f.hom n
  w := by
    change HomologicalComplex.homologyMap (f.stepMap p) n ≫
      HomologicalComplex.homologyMap (Y.filtration.inclusion p) n =
      HomologicalComplex.homologyMap (X.filtration.inclusion p) n ≫
        HomologicalComplex.homologyMap f.hom n
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    congr 1
    ext i
    exact f.component_arrow p i

/-- The induced map on the actual image filtration of cohomology. -/
def cohomologyStepMap (f : FilteredMap X Y) (p n : ℤ) :
    (cohomologyPiece X.filtration p n : A) ⟶ (cohomologyPiece Y.filtration p n : A) :=
  imageSubobjectMap (cohomologySquare f p n)

@[reassoc (attr := simp)]
theorem cohomologyStepMap_arrow (f : FilteredMap X Y) (p n : ℤ) :
    cohomologyStepMap f p n ≫ (cohomologyPiece Y.filtration p n).arrow =
      (cohomologyPiece X.filtration p n).arrow ≫ HomologicalComplex.homologyMap f.hom n :=
  imageSubobjectMap_arrow _

theorem cohomologyStepMap_comm (f : FilteredMap X Y) (p n : ℤ) :
    Subobject.ofLE _ _ (cohomologyPiece_decreasing X.filtration p n) ≫ cohomologyStepMap f p n =
      cohomologyStepMap f (p+1) n ≫
        Subobject.ofLE _ _ (cohomologyPiece_decreasing Y.filtration p n) := by
  apply (cancel_mono (cohomologyPiece Y.filtration p n).arrow).1
  simp [Category.assoc]

/-- The induced map on the associated graded of the cohomology filtration. -/
def gradedCohomologyMap (f : FilteredMap X Y) (p n : ℤ) :
    gradedCohomology X.filtration p n ⟶ gradedCohomology Y.filtration p n :=
  cokernel.map _ _ (cohomologyStepMap f (p+1) n) (cohomologyStepMap f p n)
    (cohomologyStepMap_comm f p n)

/-- The restriction of a filtered map to closed representatives. -/
def closedMap (f : FilteredMap X Y) (p n : ℤ) :
    (closed X.filtration p n : A) ⟶ (closed Y.filtration p n : A) :=
  (closed Y.filtration p n).factorThru ((closed X.filtration p n).arrow ≫ f.hom.f n) (by
    apply (Subobject.inf_factors _).2
    constructor
    · apply (Subobject.factors_iff _ _).2
      refine ⟨Subobject.ofLE _ _ inf_le_left ≫ f.component p n, ?_⟩
      simp [Category.assoc]
    · apply kernelSubobject_factors
      rw [Category.assoc, f.hom.comm, ← Category.assoc,
        ← Subobject.ofLE_arrow (inf_le_right :
          closed X.filtration p n ≤ kernelSubobject (X.complex.d n (n+1))),
        Category.assoc, Category.assoc, kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero])

@[reassoc (attr := simp)]
theorem closedMap_arrow (f : FilteredMap X Y) (p n : ℤ) :
    closedMap f p n ≫ (closed Y.filtration p n).arrow =
      (closed X.filtration p n).arrow ≫ f.hom.f n :=
  Subobject.factorThru_arrow _ _ _
end Maps

end FiniteFiltrationConvergence
namespace S01Specs
open FiniteFiltrationConvergence FilteredPage

def UniformStabilization : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K), DegreewiseFinite F →
  ∀ n, ∃ R : ℤ, 0 ≤ R ∧ ∀ r, R ≤ r → ∀ p, Stabilized F r p n

def CohomologyFiltration : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K), DegreewiseFinite F → CohomologyFiltrationData F

/-- The stable page is canonically identified with graded cohomology. -/
def CanonicalLimit : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K), DegreewiseFinite F →
  ∀ (D : F03Specs.PageData F) r p n, 0 ≤ r → Stabilized F r p n →
    Nonempty (LimitIso F D r p n)

/-- Every sufficiently late differential on a fixed total degree is zero. -/
def DifferentialStabilization : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K), DegreewiseFinite F →
  ∀ (D : F03Specs.PageData F) n, ∃ R : ℤ, 0 ≤ R ∧
    ∀ r (hr : 0 ≤ r), R ≤ r → ∀ p, D.differential r hr p n = 0

/-- The canonical limiting identifications commute with the page maps from
HA-F06 and the quotient maps induced on cohomology. This is independent of
all choices satisfying the upstream representative formulas. -/
def Naturality : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {X Y : FilteredComplex A} (f : FilteredMap X Y),
  DegreewiseFinite X.filtration → DegreewiseFinite Y.filtration →
  ∀ (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    (M : FilteredPageFunctoriality.MapData f D E) r p n
    (L : LimitIso X.filtration D r p n) (L' : LimitIso Y.filtration E r p n),
    Stabilized X.filtration r p n → Stabilized Y.filtration r p n →
      M.map r p n ≫ L'.iso.hom = L.iso.hom ≫ gradedCohomologyMap f p n

/-- Full HA-S01, including its post-theorem filtration conclusions. The stable
page is any of the actual eventually stationary quotients of HA-F03. -/
def FullStatement : Prop := UniformStabilization.{v,u} ∧ CohomologyFiltration.{v,u} ∧
  CanonicalLimit.{v,u} ∧ DifferentialStabilization.{v,u} ∧ Naturality.{v,u}

end S01Specs
end AdvancedHomologicalAlgebra
