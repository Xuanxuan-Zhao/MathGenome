import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ColumnHypercohomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.RowHypercohomology

/-! HA-G03, source 2565–2645. The row filtration is the actual second-axis
filtration of Tot(FI), and its target is the fixed total right derived functor.
All pages from E₂, their differentials, and every target filtration step are
bundled into one diagram before localization. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.checkUnivs false
set_option linter.unusedVariables false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.HypercohomologyDerivedNaturality
open CartanEilenbergData CartanEilenbergTotalization DoubleTotalization
open FiniteDiagonalFiltrations FiniteFiltrationConvergence DoubleComplexFirstPages
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B]

/-- A realization by the row filtration of the actual image double complex.
Finiteness, every page, the first two page calculations, and convergence are
all conclusions; no certificate of them is assumed of the input. -/
structure RowModel (F : A ⥤ B) [F.Additive] {K : CochainComplex A ℤ}
    (R : ResolutionData K) where
  total : ((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)
  filtration : @Filtration B _ _ (sumTotal ((mapDouble F).obj R.bicomplex))
  formula : HasFiltrationFormula ((mapDouble F).obj R.bicomplex) Prod.snd filtration
  pages : F03Specs.PageData filtration
  next : PageCohomology.Data filtration pages
  row : RowData ((mapDouble F).obj R.bicomplex) filtration formula pages
  convergence : DoubleComplexConvergence.Converges filtration

abbrev term (F : A ⥤ B) [F.Additive] {K : CochainComplex A ℤ}
    {R : ResolutionData K} (M : RowModel F R) (r p q : ℤ) : B :=
  letI := M.total
  page M.filtration M.pages r p q

abbrev modelComplex (F : A ⥤ B) [F.Additive] {K : CochainComplex A ℤ}
    {R : ResolutionData K} (M : RowModel F R) : CochainComplex B ℤ :=
  letI := M.total
  sumTotal ((mapDouble F).obj R.bicomplex)

abbrev modelFiltered (F : A ⥤ B) [F.Additive] {K : CochainComplex A ℤ}
    {R : ResolutionData K} (M : RowModel F R) : FilteredComplex B :=
  ⟨modelComplex F M, M.filtration⟩

section Derived
variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive]

abbrev target (K : CochainComplex.Plus A) (n : ℤ) : B :=
  ColumnHypercohomology.target F K n
abbrev targetMap {K L : CochainComplex.Plus A} (f : K ⟶ L) (n : ℤ) :=
  ColumnHypercohomology.targetMap F f n

/-- The row second page is the ordinary derived value. The target comparison
transports the actual image filtration to RF. Negative filtration degrees have
zero second page; R^pF uses its usual natural-number index. -/
structure Data (K : CochainComplex.Plus A) (R : ResolutionData K.obj)
    extends RowModel F R where
  secondComparison : RowHypercohomology.SecondPageComputation F R filtration formula pages next
  secondIso : ∀ (p : ℕ) (q : ℤ), term F toRowModel 2 (p : ℤ) q ≅
    (rightValue F p).obj (K.obj.homology q)
  secondIso_eq : ∀ (p : ℕ) (q : ℤ), secondIso p q =
    secondComparison.iso F R filtration formula pages (p : ℤ) q
  negative : ∀ p q : ℤ, p < 0 → IsZero (term F toRowModel 2 p q)
  [sourceTotal : R.bicomplex.HasTotal (.up ℤ)]
  targetComparison : DerivedTotalComparison F K R
  targetIso : ∀ n : ℤ,
    (sumTotal ((mapDouble F).obj R.bicomplex)).homology n ≅ target F K n
  targetIso_eq : ∀ n, targetIso n = (targetComparison.homologyIso n).symm

/-- The actual image filtration transported to Hⁿ(RF K). -/
def targetPiece {K : CochainComplex.Plus A} {R : ResolutionData K.obj}
    (M : Data F K R) (p n : ℤ) : Subobject (target F K n) :=
  (Subobject.map (M.targetIso n).hom).obj (cohomologyPiece M.filtration p n)

/-- Maps induced by a double-complex lift, on the actual filtered complexes. -/
structure LiftData {K L : CochainComplex.Plus A}
    {R : ResolutionData K.obj} {S : ResolutionData L.obj}
    (M : Data F K R) (N : Data F L S) (a : R.bicomplex ⟶ S.bicomplex) where
  filtered : FilteredMap (modelFiltered F M.toRowModel) (modelFiltered F N.toRowModel)
  hom_eq : letI := M.total; letI := N.total
    filtered.hom = HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ)
  maps : FilteredPageFunctoriality.MapData filtered M.pages N.pages

/-- A simultaneous system, for every resolution of every bounded-below K.
`lift` is not a hypothesis on inputs: the construction must supply it for all
maps of double complexes. Independence of the chosen lift starts at E₂;
identity and composition for double-complex maps hold on every page. -/
structure System where
  data : ∀ (K : CochainComplex.Plus A) (R : ResolutionData K.obj), Data F K R
  resolution : ∀ K : CochainComplex.Plus A, Nonempty (ResolutionData K.obj)
  comparison : ∀ {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj) (f : K ⟶ L),
    ∃ a : R.bicomplex ⟶ S.bicomplex, CartanEilenbergComparison.IsLift R S f.hom a
  lift : ∀ {K L : CochainComplex.Plus A} (R : ResolutionData K.obj)
    (S : ResolutionData L.obj) (a : R.bicomplex ⟶ S.bicomplex),
    LiftData F (data K R) (data L S) a
  second_naturality : ∀ {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj)
    (f : K ⟶ L) (a : R.bicomplex ⟶ S.bicomplex),
    CartanEilenbergComparison.IsLift R S f.hom a → ∀ (p : ℕ) (q : ℤ),
      ((lift R S a).maps.map 2 (p : ℤ) ((p : ℤ)+q)) ≫ ((data L S).secondIso p q).hom =
        ((data K R).secondIso p q).hom ≫
          (rightValue F p).map (HomologicalComplex.homologyMap f.hom q)
  next_naturality : ∀ {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj)
    (a : R.bicomplex ⟶ S.bicomplex) r (hr : 0 ≤ r) p n,
    ((lift R S a).maps.map (r+1) (p+r) (n+1)) ≫
        ((data L S).next.nextIso r hr p n).hom =
      ((data K R).next.nextIso r hr p n).hom ≫ ShortComplex.homologyMap
        (FilteredPageFunctoriality.shortComplexMap (lift R S a).maps r hr p n)
  target_naturality : ∀ {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj)
    (f : K ⟶ L) (a : R.bicomplex ⟶ S.bicomplex),
    CartanEilenbergComparison.IsLift R S f.hom a → ∀ n,
      HomologicalComplex.homologyMap (lift R S a).filtered.hom n ≫
        ((data L S).targetIso n).hom =
      ((data K R).targetIso n).hom ≫ targetMap F f n
  limit_naturality : ∀ {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj)
    (a : R.bicomplex ⟶ S.bicomplex) r p n
    (I : LimitIso (data K R).filtration (data K R).pages r p n)
    (J : LimitIso (data L S).filtration (data L S).pages r p n),
    Stabilized (data K R).filtration r p n →
    Stabilized (data L S).filtration r p n →
    (lift R S a).maps.map r p n ≫ J.iso.hom =
      I.iso.hom ≫ gradedCohomologyMap (lift R S a).filtered p n
  target_decreasing : ∀ (K : CochainComplex.Plus A) (R : ResolutionData K.obj) p n,
    targetPiece F (data K R) (p+1) n ≤ targetPiece F (data K R) p n
  target_finite : ∀ (K : CochainComplex.Plus A) (R : ResolutionData K.obj) n,
    ∃ a b : ℤ,
      (∀ p, p ≤ a → targetPiece F (data K R) p n = ⊤) ∧
      (∀ p, b ≤ p → targetPiece F (data K R) p n = ⊥)
  target_preserves : ∀ {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj) (f : K ⟶ L) p n,
    (targetPiece F (data L S) p n).Factors
      ((targetPiece F (data K R) p n).arrow ≫ targetMap F f n)
  target_resolution_independent : ∀ (K : CochainComplex.Plus A)
    (R S : ResolutionData K.obj) p n,
    targetPiece F (data K R) p n = targetPiece F (data K S) p n
  independent : ∀ {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj)
    (f : K ⟶ L) (a b : R.bicomplex ⟶ S.bicomplex),
    CartanEilenbergComparison.IsLift R S f.hom a →
    CartanEilenbergComparison.IsLift R S f.hom b → ∀ r, 2 ≤ r → ∀ p n,
      (lift R S a).maps.map r p n = (lift R S b).maps.map r p n
  map_id : ∀ (K : CochainComplex.Plus A) (R : ResolutionData K.obj) r p n,
    (lift R R (𝟙 R.bicomplex)).maps.map r p n = 𝟙 _
  map_comp : ∀ {K L T : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj) (U : ResolutionData T.obj)
    (a : R.bicomplex ⟶ S.bicomplex) (b : S.bicomplex ⟶ U.bicomplex) r p n,
    (lift R U (a ≫ b)).maps.map r p n =
      (lift R S a).maps.map r p n ≫ (lift S U b).maps.map r p n
  homotopy_compatible : ∀ {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj)
    (f g : K ⟶ L) (h : Homotopy f.hom g.hom)
    (a b : R.bicomplex ⟶ S.bicomplex),
    CartanEilenbergComparison.IsLift R S f.hom a →
    CartanEilenbergComparison.IsLift R S g.hom b → ∀ r, 2 ≤ r → ∀ p n,
      (lift R S a).maps.map r p n = (lift R S b).maps.map r p n
  quasiIso_comparison : ∀ {K L : CochainComplex.Plus A}
    (R : ResolutionData K.obj) (S : ResolutionData L.obj)
    (f : K ⟶ L) (a : R.bicomplex ⟶ S.bicomplex),
    CartanEilenbergComparison.IsLift R S f.hom a → QuasiIso f.hom →
      (∀ r, 2 ≤ r → ∀ p n, IsIso ((lift R S a).maps.map r p n)) ∧
      S03Specs.TargetIsomorphisms (lift R S a).filtered
  resolution_independence : ∀ (K : CochainComplex.Plus A)
    (R S : ResolutionData K.obj),
    ∃ (a : R.bicomplex ⟶ S.bicomplex) (b : S.bicomplex ⟶ R.bicomplex),
      CartanEilenbergComparison.IsLift R S (𝟙 K.obj) a ∧
      CartanEilenbergComparison.IsLift S R (𝟙 K.obj) b ∧
      (∀ r, 2 ≤ r → ∀ p n, IsIso ((lift R S a).maps.map r p n)) ∧
      S03Specs.TargetIsomorphisms (lift R S a).filtered
end Derived

/-- A row spectral sequence from E₂ with its target filtration diagram.
The index `r : ℕ` denotes page `r+2`; `n` is total degree. -/
structure RowDiagram (B : Type u') [Category.{v'} B] [Abelian B] where
  page : ℕ → ℤ → ℤ → B
  differential : ∀ r p n, page r p n ⟶ page r (p+((r:ℤ)+2)) (n+1)
  square_zero : ∀ r p n,
    differential r p n ≫ differential r (p+((r:ℤ)+2)) (n+1) = 0
  nextIso : ∀ r p n, page (r+1) (p+((r:ℤ)+2)) (n+1) ≅
    (ShortComplex.mk (differential r p n)
      (differential r (p+((r:ℤ)+2)) (n+1)) (square_zero r p n)).homology
  target : ℤ → B
  step : ℤ → ℤ → B
  inclusion : ∀ p n, step p n ⟶ target n
  down : ∀ p n, step (p+1) n ⟶ step p n

namespace RowDiagram
/-- The three-term complex on a page, centered at its middle bidegree. -/
abbrev pageComplex (X : RowDiagram B) (r : ℕ) (p n : ℤ) : ShortComplex B :=
  ShortComplex.mk (X.differential r p n)
    (X.differential r (p+((r:ℤ)+2)) (n+1)) (X.square_zero r p n)

/-- A map of these three-term page complexes. -/
def pageComplexMap {X Y : RowDiagram B}
    (f : ∀ r p n, X.page r p n ⟶ Y.page r p n)
    (h : ∀ r p n, f r p n ≫ Y.differential r p n =
      X.differential r p n ≫ f r (p+((r:ℤ)+2)) (n+1))
    (r : ℕ) (p n : ℤ) : pageComplex X r p n ⟶ pageComplex Y r p n where
  τ₁ := f r p n
  τ₂ := f r (p+((r:ℤ)+2)) (n+1)
  τ₃ := f r ((p+((r:ℤ)+2))+((r:ℤ)+2)) ((n+1)+1)
  comm₁₂ := h r p n
  comm₂₃ := h r (p+((r:ℤ)+2)) (n+1)

@[ext] structure Hom (X Y : RowDiagram B) where
  page : ∀ r p n, X.page r p n ⟶ Y.page r p n
  target : ∀ n, X.target n ⟶ Y.target n
  step : ∀ p n, X.step p n ⟶ Y.step p n
  differential_comm : ∀ r p n,
    page r p n ≫ Y.differential r p n =
      X.differential r p n ≫ page r (p+((r:ℤ)+2)) (n+1)
  next_comm : ∀ r p n,
    page (r+1) (p+((r:ℤ)+2)) (n+1) ≫ (Y.nextIso r p n).hom =
      (X.nextIso r p n).hom ≫
        ShortComplex.homologyMap (pageComplexMap page differential_comm r p n)
  inclusion_comm : ∀ p n, step p n ≫ Y.inclusion p n = X.inclusion p n ≫ target n
  down_comm : ∀ p n, step (p+1) n ≫ Y.down p n = X.down p n ≫ step p n

instance : Category (RowDiagram B) where
  Hom := Hom
  id X := {
    page := fun _ _ _ => 𝟙 _
    target := fun _ => 𝟙 _
    step := fun _ _ => 𝟙 _
    differential_comm := by intros; simp
    next_comm := by
      intro r p n
      have h : pageComplexMap (X := X) (Y := X) (fun _ _ _ => 𝟙 _) (by intros; simp) r p n =
          𝟙 (pageComplex X r p n) := by ext <;> rfl
      rw [h, ShortComplex.homologyMap_id, Category.id_comp, Category.comp_id]
    inclusion_comm := by intros; simp
    down_comm := by intros; simp }
  comp f g := {
    page := fun r p n => f.page r p n ≫ g.page r p n
    target := fun n => f.target n ≫ g.target n
    step := fun p n => f.step p n ≫ g.step p n
    differential_comm := by intros; rw [Category.assoc, g.differential_comm,
      ← Category.assoc, f.differential_comm, Category.assoc]
    next_comm := by
      intro r p n
      have h : pageComplexMap (fun r p n => f.page r p n ≫ g.page r p n)
          (by intros; rw [Category.assoc, g.differential_comm,
            ← Category.assoc, f.differential_comm, Category.assoc]) r p n =
          pageComplexMap f.page f.differential_comm r p n ≫
            pageComplexMap g.page g.differential_comm r p n := by ext <;> rfl
      rw [Category.assoc, g.next_comm, ← Category.assoc, f.next_comm,
        Category.assoc, h, ShortComplex.homologyMap_comp]
    inclusion_comm := by intros; rw [Category.assoc, g.inclusion_comm,
      ← Category.assoc, f.inclusion_comm, Category.assoc]
    down_comm := by intros; rw [Category.assoc, g.down_comm,
      ← Category.assoc, f.down_comm, Category.assoc] }

end RowDiagram

section Descent
variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive]

/-- The diagram is made from the actual pages and image filtration, with
its inclusion transported to the RF target. -/
def diagram {K : CochainComplex.Plus A} {R : ResolutionData K.obj}
    (M : Data F K R) : RowDiagram B :=
  letI := M.total
  { page := fun r p n => PageCohomology.object M.filtration M.pages ((r:ℤ)+2) p n
    differential := fun r p n => M.pages.differential ((r:ℤ)+2) (by omega) p n
    square_zero := fun r p n => M.pages.square_zero ((r:ℤ)+2) (by omega) p n
    nextIso := fun r p n =>
      eqToIso (by congr 1 <;> omega) ≪≫ M.next.nextIso ((r:ℤ)+2) (by omega) p n
    target := ColumnHypercohomology.target F K
    step := fun p n => (cohomologyPiece M.filtration p n : B)
    inclusion := fun p n => (cohomologyPiece M.filtration p n).arrow ≫ (M.targetIso n).hom
    down := fun p n => Subobject.ofLE _ _ (cohomologyPiece_decreasing M.filtration p n) }

/-- Map of the full diagram supplied by any actual CE lift. -/
def diagramMap (S : System F) {K L : CochainComplex.Plus A}
    (f : K ⟶ L) {R : ResolutionData K.obj} {U : ResolutionData L.obj}
    (a : R.bicomplex ⟶ U.bicomplex) (ha : CartanEilenbergComparison.IsLift R U f.hom a) :
    diagram F (S.data K R) ⟶ diagram F (S.data L U) where
  page := fun r p n => (S.lift R U a).maps.map ((r:ℤ)+2) p n
  target := fun n => targetMap F f n
  step := fun p n => cohomologyStepMap (S.lift R U a).filtered p n
  differential_comm := by
    intros; exact (S.lift R U a).maps.differential_comm _ _ _ _
  next_comm := by
    intro r p n
    dsimp only [diagram, Iso.trans_hom, eqToIso.hom]
    have hnext := S.next_naturality R U a ((r:ℤ)+2) (by omega) p n
    have transport (s t : ℤ) (h : s = t) :
        (S.lift R U a).maps.map s (p+((r:ℤ)+2)) (n+1) ≫ eqToHom
            (congrArg (fun s => PageCohomology.object (S.data L U).filtration
              (S.data L U).pages s (p+((r:ℤ)+2)) (n+1)) h) =
          eqToHom (congrArg (fun s => PageCohomology.object (S.data K R).filtration
              (S.data K R).pages s (p+((r:ℤ)+2)) (n+1)) h) ≫
            (S.lift R U a).maps.map t (p+((r:ℤ)+2)) (n+1) := by
      subst t; simp
    rw [← Category.assoc, transport _ _ (by omega), Category.assoc, hnext]
    simp only [Category.assoc]
    rfl
  inclusion_comm := by
    intros; dsimp [diagram]
    rw [← Category.assoc, cohomologyStepMap_arrow, Category.assoc,
      S.target_naturality R U f a ha, Category.assoc]
  down_comm := by
    intros; exact (cohomologyStepMap_comm (S.lift R U a).filtered _ _).symm

/-- Descent of the whole diagram, not just its underlying target. The
descent isomorphism simultaneously compares all pages, differentials,
filtration steps, their inclusions, and the decreasing filtration maps. -/
def Descends (S : System F) : Prop :=
  ∃ (R : ∀ K : CochainComplex.Plus A, ResolutionData K.obj)
    (T : CochainComplex.Plus A ⥤ RowDiagram B)
    (D : DerivedCategory.Plus A ⥤ RowDiagram B),
    (∀ K, T.obj K = diagram F (S.data K (R K))) ∧
    (∀ {K L : CochainComplex.Plus A} (f : K ⟶ L),
      ∃ (a : (R K).bicomplex ⟶ (R L).bicomplex)
        (ha : CartanEilenbergComparison.IsLift (R K) (R L) f.hom a),
        HEq (T.map f)
          (diagramMap F S f a ha)) ∧
    Nonempty (DerivedCategory.Plus.Q ⋙ D ≅ T) ∧
    (∀ {K L : CochainComplex.Plus A} (f g : K ⟶ L),
      Nonempty (Homotopy f.hom g.hom) → T.map f = T.map g) ∧
    (∀ {K L : CochainComplex.Plus A} (f : K ⟶ L),
      QuasiIso f.hom → IsIso (T.map f)) ∧
    (∀ (E : DerivedCategory.Plus A ⥤ RowDiagram B),
      Nonempty (DerivedCategory.Plus.Q ⋙ E ≅ T) → Nonempty (E ≅ D))
end Descent

namespace Specs
/-- Both source spectral sequences and the full row descent assertion. -/
def FullStatement : Prop :=
  ColumnHypercohomology.Specs.FullStatement.{u,v,u',v',w,w'} ∧
  ∀ (A : Type u) (B : Type u') [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F],
    ∃ S : System F, Descends F S
end Specs
end AdvancedHomologicalAlgebra.HypercohomologyDerivedNaturality
