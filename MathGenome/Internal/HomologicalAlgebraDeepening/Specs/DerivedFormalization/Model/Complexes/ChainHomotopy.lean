import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.Projective

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomotopicalAlgebra

universe u w

namespace DerivedFormalization.Specs.ComplexChainHomotopy

open Model.Complexes

variable {A : Type u} [Ring A]

/-- The three summands of the cochain path complex in degree `n`. -/
abbrev PathTerm (Y : Cochains A) (n : ℤ) :=
  ModuleCat.of A (Y.X n × Y.X n × Y.X (n - 1))

/-- Transport between two equal degrees of a complex. -/
def degreeCast (Y : Cochains A) {i j : ℤ} (h : i = j) : Y.X i ⟶ Y.X j :=
  eqToHom (congrArg Y.X h)

@[simp]
theorem d_degreeCast (Y : Cochains A) {i j k : ℤ} (h : i = j) (x : Y.X i) :
    Y.d j k (degreeCast Y h x) = Y.d i k x := by
  subst j
  simp [degreeCast]

@[simp]
theorem degreeCast_d (Y : Cochains A) {i j k : ℤ} (h : j = k) (x : Y.X i) :
    degreeCast Y h (Y.d i j x) = Y.d i k x := by
  subst k
  simp [degreeCast]

@[simp]
theorem d_apply_d (Y : Cochains A) (i j k : ℤ) (x : Y.X i) :
    Y.d j k (Y.d i j x) = 0 := by
  change (Y.d i j ≫ Y.d j k) x = 0
  rw [HomologicalComplex.d_comp_d]
  rfl

/-- The differential sends `(y₀, y₁, b)` to `(dy₀, dy₁, y₁ - y₀ - db)`. -/
def pathStep (Y : Cochains A) (n : ℤ) : PathTerm Y n ⟶ PathTerm Y (n + 1) :=
  ModuleCat.ofHom
    { toFun := fun x =>
        (Y.d n (n + 1) x.1, Y.d n (n + 1) x.2.1,
          degreeCast Y (by omega : n = (n + 1) - 1) (x.2.1 - x.1) -
            Y.d (n - 1) ((n + 1) - 1) x.2.2)
      map_add' := by
        intro x y
        simp only [Prod.fst_add, Prod.snd_add, map_add, map_sub, Prod.mk_add_mk]
        congr 2
        abel
      map_smul' := by
        intro a x
        simp [smul_sub] }

theorem pathStep_apply (Y : Cochains A) (n : ℤ) (x : PathTerm Y n) :
    pathStep Y n x =
      (Y.d n (n + 1) x.1, Y.d n (n + 1) x.2.1,
        degreeCast Y (by omega : n = (n + 1) - 1) (x.2.1 - x.1) -
          Y.d (n - 1) ((n + 1) - 1) x.2.2) := rfl

abbrev pathComplexType := ∀ {A : Type u} [Ring A], Cochains A → Cochains A

/-- The explicit path complex of unbounded cochains. -/
abbrev pathComplexValue : pathComplexType.{u} :=
  fun {_} [_] Y => CochainComplex.of (PathTerm Y) (pathStep Y) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change pathStep Y (n + 1) (pathStep Y n x) = 0
    rw [pathStep_apply Y (n + 1), pathStep_apply Y n]
    simp only [d_apply_d, map_sub, d_degreeCast, sub_zero, degreeCast_d, sub_self]
    rfl)

@[simp]
theorem pathComplex_d (Y : Cochains A) (n : ℤ) :
    (pathComplexValue Y).d n (n + 1) = pathStep Y n :=
  CochainComplex.of_d _ _ _

abbrev evaluationType :=
  ∀ {A : Type u} [Ring A] (Y : Cochains A), pathComplexValue Y ⟶ Y

/-- Projection to the first endpoint. -/
def firstEvaluationValue : evaluationType.{u} :=
  fun {_} [_] Y => CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (LinearMap.fst _ _ _)) (by
      intro n
      rw [pathComplex_d]
      rfl)

/-- Projection to the second endpoint. -/
def secondEvaluationValue : evaluationType.{u} :=
  fun {_} [_] Y => CochainComplex.ofHom
    (fun n => ModuleCat.ofHom ((LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _))) (by
      intro n
      rw [pathComplex_d]
      rfl)

abbrev sectionType :=
  ∀ {A : Type u} [Ring A] (Y : Cochains A), Y ⟶ pathComplexValue Y

/-- The diagonal section sends `y` to `(y, y, 0)`. -/
def diagonalSectionValue : sectionType.{u} :=
  fun {_} [_] Y => CochainComplex.ofHom
    (fun _ => ModuleCat.ofHom (LinearMap.id.prod (LinearMap.id.prod 0))) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rw [pathComplex_d]
      change pathStep Y n (x, x, 0) = (Y.d n (n + 1) x, Y.d n (n + 1) x, 0)
      rw [pathStep_apply Y n (x, x, 0)]
      simp)

def projectivePathType : Prop :=
  ∀ {A : Type u} [Ring A] (M : ProjectiveModel A),
    letI := M.model
    ∀ Y : Cochains A,
      let s := diagonalSectionValue Y
      let e₀ := firstEvaluationValue Y
      let e₁ := secondEvaluationValue Y
      s ≫ prod.lift e₀ e₁ = diag Y ∧
        weakEquivalences (Cochains A) s ∧ fibrations (Cochains A) (prod.lift e₀ e₁)

/-- The equation `g - f = dh + hd` for a degree minus one family. -/
def HomotopyEquation {X Y : Cochains A} (f g : X ⟶ Y)
    (h : ∀ n : ℤ, X.X n ⟶ Y.X (n - 1)) : Prop :=
  ∀ (n : ℤ) (x : X.X n),
    g.f n x - f.f n x =
      Y.d (n - 1) n (h n x) +
        degreeCast Y (by omega : (n + 1) - 1 = n) (h (n + 1) (X.d n (n + 1) x))

def pathLiftType : Prop :=
  ∀ {A : Type u} [Ring A] {X Y : Cochains A} (f g : X ⟶ Y)
    (h : ∀ n : ℤ, X.X n ⟶ Y.X (n - 1)),
    HomotopyEquation f g h ↔
      ∃ K : X ⟶ pathComplexValue Y, ∀ (n : ℤ) (x : X.X n),
        K.f n x = ((f.f n x, g.f n x, h n x) : PathTerm Y n)

def pathHomotopyType : Prop :=
  ∀ {A : Type u} [Ring A] {X Y : Cochains A} (f g : X ⟶ Y),
    Nonempty (Homotopy f g) ↔
      ∃ K : X ⟶ pathComplexValue Y,
        K ≫ firstEvaluationValue Y = f ∧ K ≫ secondEvaluationValue Y = g

def contractibleKernelType : Prop :=
  ∀ {A : Type u} [Ring A] (Y : Cochains A),
    Nonempty (Homotopy (𝟙 (kernel (firstEvaluationValue Y))) 0)

abbrev cochainQuotient (A : Type u) [Ring A] :=
  HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)

set_option linter.checkUnivs false in
abbrev comparisonType :=
  ∀ {A : Type u} [Ring A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {X Y : Cochains A},
    ((cochainQuotient A).obj X ⟶ (cochainQuotient A).obj Y) →
      (DerivedCategory.Q.obj X ⟶ DerivedCategory.Q.obj Y)

/-- The localization map on ordinary cochain homotopy classes. -/
noncomputable def comparisonValue : comparisonType.{u, w} :=
  fun {A} [_] [_] {X Y} f =>
    (DerivedCategory.quotientCompQhIso (ModuleCat A)).inv.app X ≫
      DerivedCategory.Qh.map f ≫
      (DerivedCategory.quotientCompQhIso (ModuleCat A)).hom.app Y

def comparisonMapType : Prop :=
  ∀ {A : Type u} [Ring A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {X Y : Cochains A} (f : X ⟶ Y),
    comparisonValue ((cochainQuotient A).map f) = DerivedCategory.Q.map f

def comparisonBijectiveType : Prop :=
  ∀ {A : Type u} [Ring A] (M : ProjectiveModel A)
    [HasDerivedCategory.{w} (ModuleCat.{u} A)],
    letI := M.model
    ∀ (X Y : Cochains A) [IsCofibrant X],
      Function.Bijective (comparisonValue (X := X) (Y := Y))

/-- Compatibility with the maps on both Hom sets induced by source and target maps. -/
def comparisonNaturalType : Prop :=
  ∀ {A : Type u} [Ring A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {X' X Y Y' : Cochains A} (k : X' ⟶ X) (l : Y ⟶ Y')
    (f : (cochainQuotient A).obj X ⟶ (cochainQuotient A).obj Y),
    comparisonValue ((cochainQuotient A).map k ≫ f ≫ (cochainQuotient A).map l) =
      DerivedCategory.Q.map k ≫ comparisonValue f ≫ DerivedCategory.Q.map l

end DerivedFormalization.Specs.ComplexChainHomotopy
