import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.ResolvedCotangentSequence
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.RelativePathComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.LocalizedBimoduleExactness

open CategoryTheory

universe u v

namespace Specs.DerivedFormalization.Affine.CotangentDiagramComparison

open _root_.DerivedFormalization.Affine
open ResolvedCotangentSequence
open CotangentComplex (Model)
open PolynomialPath (AlgebraPathModel RelativePathModel)
open Tensor (ModuleTensor term regular)
open FlatFiltration (GradedSplit)
open Specs.DerivedFormalization.DG.HomComplex (gradedHom component HomotopyEquation)

variable {k : Type u} [Field k] [CharZero k]

structure Chain (k : Type u) [Field k] [CharZero k] where
  A : NonpositiveCDGA.{u,v} k
  B : NonpositiveCDGA.{u,v} k
  C : NonpositiveCDGA.{u,v} k
  first : A ⟶ B
  second : B ⟶ C

variable {X Y Z : Chain.{u,v} k}

structure ChainMap (X Y : Chain.{u,v} k) where
  a : X.A ⟶ Y.A
  b : X.B ⟶ Y.B
  c : X.C ⟶ Y.C
  first_comm : X.first ≫ b = a ≫ Y.first
  second_comm : X.second ≫ c = b ≫ Y.second

def ChainMap.id (X : Chain.{u,v} k) : ChainMap X X where
  a := 𝟙 _
  b := 𝟙 _
  c := 𝟙 _
  first_comm := by simp
  second_comm := by simp

def ChainMap.comp (f : ChainMap X Y) (g : ChainMap Y Z) : ChainMap X Z where
  a := f.a ≫ g.a
  b := f.b ≫ g.b
  c := f.c ≫ g.c
  first_comm := by rw [← Category.assoc, f.first_comm, Category.assoc, g.first_comm, Category.assoc]
  second_comm := by rw [← Category.assoc, f.second_comm, Category.assoc, g.second_comm, Category.assoc]

structure Resolution (X : Chain.{u,v} k) where
  P : Model X.first
  Q : Model (P.augmentation ≫ X.second)
  absolute : Differentials (P.base ≫ Q.base)

variable {R : Resolution X} {S : Resolution Y} {V : Resolution Z}

structure Lift (f : ChainMap X Y) (R : Resolution X) (S : Resolution Y) where
  p : R.P.algebra ⟶ S.P.algebra
  q : R.Q.algebra ⟶ S.Q.algebra
  p_base : R.P.base ≫ p = f.a ≫ S.P.base
  p_aug : p ≫ S.P.augmentation = R.P.augmentation ≫ f.b
  q_base : R.Q.base ≫ q = p ≫ S.Q.base
  q_aug : q ≫ S.Q.augmentation = R.Q.augmentation ≫ f.c

def Lift.id (R : Resolution X) : Lift (ChainMap.id X) R R where
  p := 𝟙 _
  q := 𝟙 _
  p_base := by simp [ChainMap.id]
  p_aug := by simp [ChainMap.id]
  q_base := by simp
  q_aug := by simp [ChainMap.id]

def Lift.comp {f : ChainMap X Y} {g : ChainMap Y Z} (l : Lift f R S) (m : Lift g S V) :
    Lift (f.comp g) R V where
  p := l.p ≫ m.p
  q := l.q ≫ m.q
  p_base := by
    dsimp only [ChainMap.comp]
    rw [← Category.assoc, l.p_base, Category.assoc, m.p_base, Category.assoc]
  p_aug := by
    dsimp only [ChainMap.comp]
    rw [Category.assoc, m.p_aug, ← Category.assoc, l.p_aug, Category.assoc]
  q_base := by rw [← Category.assoc, l.q_base, Category.assoc, m.q_base, Category.assoc]
  q_aug := by
    dsimp only [ChainMap.comp]
    rw [Category.assoc, m.q_aug, ← Category.assoc, l.q_aug, Category.assoc]

/-- Lift both cdga maps and keep the square between the resolutions strict. -/
def LiftsExist : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {X Y : Chain.{u,v} k}
    (f : ChainMap X Y) (R : Resolution X) (S : Resolution Y), Nonempty (Lift f R S)

abbrev PQPath (S : Resolution Y) {UP : AlgebraPathModel S.P.algebra.toCommDGAlgebra}
    {UB : AlgebraPathModel Y.B.toCommDGAlgebra}
    {UQ : AlgebraPathModel S.Q.algebra.toCommDGAlgebra}
    {UC : AlgebraPathModel Y.C.toCommDGAlgebra}
    (P : RelativePathModel S.P.augmentation UP UB) (Q : RelativePathModel S.Q.augmentation UQ UC)
    (j : P.truncated ⟶ Q.truncated) : Prop :=
  ∀ (n : ℤ) (x : P.truncated.complex.X n),
    let z := UP.coordinates n ((P.includeTruncation ≫ P.includeRelative).chainMap.f n x)
    UQ.coordinates n ((Q.includeTruncation ≫ Q.includeRelative).chainMap.f n (j.chainMap.f n x)) =
      (PolynomialPath.mapCoefficients (S.Q.base.chainMap.f n).hom z.1,
        PolynomialPath.mapCoefficients (S.Q.base.chainMap.f (n-1)).hom z.2)

/-- A relative path on the two resolutions with its required coefficientwise compatibility. -/
structure Paths {f : ChainMap X Y} (l₀ l₁ : Lift f R S)
    {UP : AlgebraPathModel S.P.algebra.toCommDGAlgebra}
    {UB : AlgebraPathModel Y.B.toCommDGAlgebra}
    {UQ : AlgebraPathModel S.Q.algebra.toCommDGAlgebra}
    {UC : AlgebraPathModel Y.C.toCommDGAlgebra}
    (P : RelativePathModel S.P.augmentation UP UB) (Q : RelativePathModel S.Q.augmentation UQ UC) where
  changePath : P.truncated ⟶ Q.truncated
  change_coordinates : PQPath S P Q changePath
  p : R.P.algebra ⟶ P.truncated
  q : R.Q.algebra ⟶ Q.truncated
  p_base : R.P.base ≫ p = f.a ≫ S.P.base ≫ P.constants
  q_base : R.Q.base ≫ q = p ≫ changePath
  p_zero : p ≫ P.endpoints ≫ P.first = l₀.p
  p_one : p ≫ P.endpoints ≫ P.second = l₁.p
  q_zero : q ≫ Q.endpoints ≫ Q.first = l₀.q
  q_one : q ≫ Q.endpoints ≫ Q.second = l₁.q

def PathsExist : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {X Y : Chain.{u,v} k}
    {f : ChainMap X Y} {R : Resolution X} {S : Resolution Y} (l₀ l₁ : Lift f R S),
    ∃ (UP : AlgebraPathModel S.P.algebra.toCommDGAlgebra)
      (UB : AlgebraPathModel Y.B.toCommDGAlgebra)
      (UQ : AlgebraPathModel S.Q.algebra.toCommDGAlgebra)
      (UC : AlgebraPathModel Y.C.toCommDGAlgebra)
      (P : RelativePathModel S.P.augmentation UP UB)
      (Q : RelativePathModel S.Q.augmentation UQ UC), Nonempty (Paths l₀ l₁ P Q)

/-- The unaugmented sequence attached to a resolved chain. -/
abbrev Sequence (T : ModuleTensor.{u,v} k) (R : Resolution X) :=
  DifferentialSequence T R.P.base R.Q.base R.P.differentials R.absolute R.Q.differentials

/-- All three strict maps in a comparison of short exact sequences. -/
structure SequenceMap {E : CommDGAlgebra.{u,v} k}
    {L M N L' M' N' : E.Module} (i : L ⟶ M) (p : M ⟶ N) (i' : L' ⟶ M') (p' : M' ⟶ N') where
  left : L ⟶ L'
  middle : M ⟶ M'
  right : N ⟶ N'
  incl_comm : i ≫ middle = left ≫ i'
  proj_comm : p ≫ right = middle ≫ p'

/-- A homotopy of sequence comparisons respects both structure maps in each degree. -/
structure SequenceHomotopy {E : CommDGAlgebra.{u,v} k}
    {L M N L' M' N' : E.Module} {i : L ⟶ M} {p : M ⟶ N} {i' : L' ⟶ M'} {p' : M' ⟶ N'}
    (f g : SequenceMap i p i' p') where
  left : gradedHom L L' (-1)
  middle : gradedHom M M' (-1)
  right : gradedHom N N' (-1)
  left_eq : HomotopyEquation f.left g.left left
  middle_eq : HomotopyEquation f.middle g.middle middle
  right_eq : HomotopyEquation f.right g.right right
  incl_comm (n m : ℤ) (e : n+(-1)=m) (x : term L n) :
    component middle () n m e ((i.app ()).f n x) =
      (i'.app ()).f m (component left () n m e x)
  proj_comm (n m : ℤ) (e : n+(-1)=m) (x : term M n) :
    component right () n m e ((p.app ()).f n x) =
      (p'.app ()).f m (component middle () n m e x)


noncomputable section

variable {T : ModuleTensor.{u,v} k} {E : NonpositiveCDGA.{u,v} k}

abbrev inclusionAt (F : Sequence T R) (e : X.C ⟶ E) :=
  (extend T (R.Q.augmentation ≫ e)).map F.incl

abbrev projectionAt (F : Sequence T R) (e : X.C ⟶ E) :=
  (extend T (R.Q.augmentation ≫ e)).map F.proj

abbrev MapAt (F : Sequence T R) (G : Sequence T S) (e : X.C ⟶ E) (d : Y.C ⟶ E) :=
  SequenceMap (inclusionAt F e) (projectionAt F e) (inclusionAt G d) (projectionAt G d)

/-- The generator of the left term at the final coefficients is the successive tensor
of the differential symbol with the two units. -/
abbrev leftSymbol (T : ModuleTensor.{u,v} k) (R : Resolution X) (e : X.C ⟶ E)
    (n : ℤ) (x : R.P.algebra.complex.X n) :=
  T.tmul (underlying (R.Q.augmentation ≫ e)) (N := regular E.toCommDGAlgebra)
    n 0 n (add_zero n)
    (extendedSymbol T R.P.differentials R.Q.base n 0 n (add_zero n) x R.Q.algebra.one) E.one

abbrev middleSymbol (T : ModuleTensor.{u,v} k) (R : Resolution X) (e : X.C ⟶ E)
    (n : ℤ) (x : R.Q.algebra.complex.X n) :=
  extendedSymbol T R.absolute (R.Q.augmentation ≫ e) n 0 n (add_zero n) x E.one

abbrev rightSymbol (T : ModuleTensor.{u,v} k) (R : Resolution X) (e : X.C ⟶ E)
    (n : ℤ) (x : R.Q.algebra.complex.X n) :=
  extendedSymbol T R.Q.differentials (R.Q.augmentation ≫ e) n 0 n (add_zero n) x E.one

def Induces {f : ChainMap X Y} (l : Lift f R S) {F : Sequence T R} {G : Sequence T S}
    {e : X.C ⟶ E} {d : Y.C ⟶ E} (m : MapAt F G e d) : Prop :=
  (∀ n x, (m.left.app ()).f n (leftSymbol T R e n x) =
    leftSymbol T S d n (l.p.chainMap.f n x)) ∧
  (∀ n x, (m.middle.app ()).f n (middleSymbol T R e n x) =
    middleSymbol T S d n (l.q.chainMap.f n x)) ∧
  (∀ n x, (m.right.app ()).f n (rightSymbol T R e n x) =
    rightSymbol T S d n (l.q.chainMap.f n x))

def SequenceMap.id {E : CommDGAlgebra.{u,v} k} {L M N : E.Module} {i : L ⟶ M} {p : M ⟶ N} :
    SequenceMap i p i p :=
  ⟨𝟙 _, 𝟙 _, 𝟙 _, by simp, by simp⟩

def SequenceMap.comp {E : CommDGAlgebra.{u,v} k} {L M N L' M' N' L'' M'' N'' : E.Module}
    {i : L ⟶ M} {p : M ⟶ N} {i' : L' ⟶ M'} {p' : M' ⟶ N'}
    {i'' : L'' ⟶ M''} {p'' : M'' ⟶ N''}
    (f : SequenceMap i p i' p') (g : SequenceMap i' p' i'' p'') :
    SequenceMap i p i'' p'' where
  left := f.left ≫ g.left
  middle := f.middle ≫ g.middle
  right := f.right ≫ g.right
  incl_comm := by rw [← Category.assoc, f.incl_comm, Category.assoc, g.incl_comm, Category.assoc]
  proj_comm := by rw [← Category.assoc, f.proj_comm, Category.assoc, g.proj_comm, Category.assoc]

/-- The canonical strict comparisons at common final coefficients. -/
structure ComparisonSystem (T : ModuleTensor.{u,v} k) (E : NonpositiveCDGA.{u,v} k) where
  map : ∀ {X Y : Chain.{u,v} k} {R : Resolution X} {S : Resolution Y}
    {f : ChainMap X Y}, Lift f R S → (F : Sequence T R) → (G : Sequence T S) →
    (e : X.C ⟶ E) → (d : Y.C ⟶ E) → e = f.c ≫ d → MapAt F G e d
  induced : ∀ {X Y : Chain.{u,v} k} {R : Resolution X} {S : Resolution Y}
    {f : ChainMap X Y} (l : Lift f R S) (F : Sequence T R) (G : Sequence T S)
    (e : X.C ⟶ E) (d : Y.C ⟶ E) (h : e = f.c ≫ d),
    Induces l (map l F G e d h)
  identity : ∀ {X : Chain.{u,v} k} {R : Resolution X} (F : Sequence T R) (e : X.C ⟶ E),
    map (Lift.id R) F F e e (Category.id_comp e).symm = SequenceMap.id
  composition : ∀ {X Y Z : Chain.{u,v} k} {R : Resolution X} {S : Resolution Y} {V : Resolution Z}
    {f : ChainMap X Y} {g : ChainMap Y Z} (l : Lift f R S) (r : Lift g S V)
    (F : Sequence T R) (G : Sequence T S) (H : Sequence T V)
    (e : X.C ⟶ E) (d : Y.C ⟶ E) (c : Z.C ⟶ E) (hf : e = f.c ≫ d) (hg : d = g.c ≫ c),
    map (l.comp r) F H e c (by rw [hf, hg]; exact (Category.assoc _ _ _).symm) =
      (map l F G e d hf).comp (map r G H d c hg)

def StrictSequenceComparisons : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k), TensorFormulas T →
    T.Comparisons → ∀ (E : NonpositiveCDGA.{u,v} k), Nonempty (ComparisonSystem T E)

/-- Different lifts of the same chain map give compatible homotopies on the
canonical comparisons of the three terms. -/
def SequenceComparisons : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k), TensorFormulas T →
    T.Comparisons → ∀ (E : NonpositiveCDGA.{u,v} k) (m : ComparisonSystem T E),
    ∀ {X Y : Chain.{u,v} k} {R : Resolution X} {S : Resolution Y}
      {f : ChainMap X Y} (l₀ l₁ : Lift f R S) (F : Sequence T R) (G : Sequence T S)
      (e : X.C ⟶ E) (d : Y.C ⟶ E) (h : e = f.c ≫ d),
      Nonempty (SequenceHomotopy (m.map l₁ F G e d h) (m.map l₀ F G e d h))

open Specs.DerivedFormalization.DG
open KProjective (isKProjective)

/-- The chosen sequence has good terms at its own coefficients, stays split at arbitrary
extended coefficients, and is defined for every chain. -/
def SequencesExist : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k],
    ∀ (T : ModuleTensor.{u,v} k), TensorFormulas T → T.Comparisons → T.AlgebraCoproducts →
      ∀ X : Chain.{u,v} k,
        ∃ (R : Resolution X) (F : Sequence T R),
          (∀ {E : CommDGAlgebra.{u,v} k} (e : R.Q.algebra.toCommDGAlgebra ⟶ E), F.extendedSplit e) ∧
          GoodTerm T (leftTerm T R.P R.Q) ∧ GoodTerm T (middleTerm T R.P R.Q R.absolute) ∧
          GoodTerm T (rightTerm T R.P R.Q)

/-- Reassociate successive scalar extensions through the given augmentations.
The equation specifies the usual balanced-tensor associator. -/
structure ExtensionAssociator (T : ModuleTensor.{u,v} k) {P C E D : NonpositiveCDGA.{u,v} k}
    (p : P ⟶ C) (e : C ⟶ E) (w : E ⟶ D) where
  iso : extend T (p ≫ e) ⋙ extend T w ≅ extend T (p ≫ e ≫ w)
  pure (M : P.Module) (i j l m n : ℤ) (hm : i+j=m) (hn : m+l=n)
      (x : term M i) (b : E.complex.X j) (c : D.complex.X l) :
    ((iso.hom.app M).app ()).f n
      (T.tmul (underlying w) (N := regular D.toCommDGAlgebra) m l n hn
        (T.tmul (underlying (p ≫ e)) (N := regular E.toCommDGAlgebra) i j m hm x b) c) =
      T.tmul (underlying (p ≫ e ≫ w)) (N := regular D.toCommDGAlgebra) i (j+l) n (by omega) x
        (D.mul j l (j+l) rfl (w.chainMap.f j b) c)

abbrev resolutionLeft (T : ModuleTensor.{u,v} k) (R : Resolution X) : R.Q.algebra.Module :=
  (extend T R.Q.base).obj R.P.differentials.module

/-- The comparisons computed at common final coefficients agree with the
ordinary extension of the comparisons at the earlier coefficients. -/
def ScalarCoherence : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k),
    TensorFormulas T → T.Comparisons →
    ∀ {X Y : Chain.{u,v} k} {R : Resolution X} {S : Resolution Y}
      {E D : NonpositiveCDGA.{u,v} k}
      {f : ChainMap X Y} (l : Lift f R S) (F : Sequence T R) (G : Sequence T S)
      (e : X.C ⟶ E) (d : Y.C ⟶ E) (w : E ⟶ D)
      (m : MapAt F G e d) (m' : MapAt F G (e ≫ w) (d ≫ w)),
      Induces l m → Induces l m' →
      ∃ (a : ExtensionAssociator T R.Q.augmentation e w)
        (b : ExtensionAssociator T S.Q.augmentation d w),
        (extend T w).map m.left ≫ b.iso.hom.app (resolutionLeft T S) =
          a.iso.hom.app (resolutionLeft T R) ≫ m'.left ∧
        (extend T w).map m.middle ≫ b.iso.hom.app S.absolute.module =
          a.iso.hom.app R.absolute.module ≫ m'.middle ∧
        (extend T w).map m.right ≫ b.iso.hom.app S.Q.differentials.module =
          a.iso.hom.app R.Q.differentials.module ≫ m'.right

open ShiftCone (cone coneInclusion coneProjection coneTerm shift shiftMap)

/-- The strict comparison with the right term of the sequence induces the connecting arrow
by inverting a quasi-isomorphism and then applying the signed cone projection. -/
def IsConeQuotient {E : CommDGAlgebra.{u,v} k} {L M N : E.Module}
    {i : L ⟶ M} (p : M ⟶ N) (q : cone i ⟶ N) : Prop :=
  (∀ n (x : coneTerm L M () n), (q.app ()).f n x = (p.app ()).f n x.1) ∧ Specs.DerivedFormalization.DG.Module.quasiIsomorphism q

def ConeComparisons : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {E : CommDGAlgebra.{u,v} k}
    {L M N L' M' N' : E.Module} {i : L ⟶ M} {p : M ⟶ N} {i' : L' ⟶ M'} {p' : M' ⟶ N'},
    GradedSplit i p → GradedSplit i' p' →
    ∃ (q : cone i ⟶ N) (q' : cone i' ⟶ N')
      (co : SequenceMap i p i' p' → (cone i ⟶ cone i')),
      IsConeQuotient p q ∧ IsConeQuotient p' q' ∧
      (∀ f, (∀ n (x : coneTerm L M () n), ((co f).app ()).f n x =
        ((f.middle.app ()).f n x.1, (f.left.app ()).f (n+1) x.2)) ∧
        coneInclusion i ≫ co f = f.middle ≫ coneInclusion i' ∧
        co f ≫ coneProjection i' = coneProjection i ≫ shiftMap 1 f.left ∧
        co f ≫ q' = q ≫ f.right) ∧
      ∀ f g, SequenceHomotopy f g →
        ∃ h : gradedHom (cone i) (cone i') (-1), HomotopyEquation (co f) (co g) h

/-- The graded split, the signed cone quotient and the connecting arrow extend by
ordinary scalar extension. The two isomorphisms use the canonical tensor coordinates. -/
def StrictExtension : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k), TensorFormulas T →
    ∀ {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B) {L M N : A.Module}
      {i : L ⟶ M} {p : M ⟶ N} (q : cone i ⟶ N), GradedSplit i p → IsConeQuotient p q →
      let F := T.baseChange f
      ∃ (C : cone (F.map i) ≅ F.obj (cone i)) (S : F.obj (shift L 1) ≅ shift (F.obj L) 1),
        Nonempty (GradedSplit (F.map i) (F.map p)) ∧
        IsConeQuotient (F.map p) (C.hom ≫ F.map q) ∧
        coneInclusion (F.map i) ≫ C.hom = F.map (coneInclusion i) ∧
        C.hom ≫ F.map (coneProjection i) ≫ S.hom = coneProjection (F.map i)

open Derived (HomotopyCategoryLaws quotient)
open DerivedKProjective (derivedCategoryInstance)
open HomComplex (homotopyClass)
open Tensor (dgCat)

/-- The ordinary complex of a K-projective term computes scalar extension in the localized
category, with the same arrow on any strict map between the chosen terms. -/
def DerivedExtensionComparison : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {T : ModuleTensor.{u,v} k}
    {A B : CommDGAlgebra.{u,v} k} {f : A ⟶ B}
    (hA : HomotopyCategoryLaws (dgCat A)) (hB : HomotopyCategoryLaws (dgCat B))
    (F : DerivedTensor.ScalarExtension T f hA hB),
    letI := Derived.homotopyCategory (dgCat A) hA
    letI := Derived.homotopyCategory (dgCat B) hB
    letI := derivedCategoryInstance (dgCat A) hA
    letI := derivedCategoryInstance (dgCat B) hB
    let QA := quotient (dgCat A) hA
    let QB := quotient (dgCat B) hB
    ∀ {M N : A.Module} (m : M ⟶ N) (hM : isKProjective M) (hN : isKProjective N),
      F.functor.map (QA.map (homotopyClass m)) ≫ (F.onProjective N hN).hom =
        (F.onProjective M hM).hom ≫ QB.map (homotopyClass ((T.baseChange f).map m))


open LocalizedBimoduleExactness (ConeLocalization classOfMap)
open CategoryTheory.Pretriangulated

/-- The data used by the derived scalar-extension comparison. -/
abbrev adjunctionConeLocalization {E : CommDGAlgebra.{u,v} k}
    {h : HomotopyCategoryLaws (dgCat E)} (K : ConeLocalization (dgCat E) h) :
    DerivedBimoduleAdjunction.ConeLocalization (dgCat E) h where
  shiftK := K.shiftK
  addK := K.addK
  zeroK := K.zeroK
  addShiftK := K.addShiftK
  shiftObj := K.shiftObj
  shiftMap := K.shiftMap
  trianglesK := K.trianglesK
  shiftD := K.shiftD
  addD := K.addD
  zeroD := K.zeroD
  addShiftD := K.addShiftD
  quotientShift := K.quotientShift
  trianglesD := K.trianglesD
  isTriangulated := K.isTriangulated
  coneTriangles := K.coneTriangles
  localizedConeTriangles := K.localizedConeTriangles

/-- The localized triangle of the resolved short exact sequence. Its last
arrow is the signed cone boundary composed with the inverse of the cone quotient. -/
abbrev localizedSequenceTriangle {E : CommDGAlgebra.{u,v} k}
    (h : HomotopyCategoryLaws (dgCat E)) (K : DerivedBimoduleAdjunction.ConeLocalization (dgCat E) h)
    {L M N : E.Module} (i : L ⟶ M) (p : M ⟶ N)
    (q : letI := Derived.homotopyCategory (dgCat E) h
         letI := derivedCategoryInstance (dgCat E) h
         let Q : HomComplex.homotopyCategory (dgCat E) ⥤ Derived.derivedCategory (dgCat E) h :=
           quotient (dgCat E) h
         Q.obj (cone i) ≅ Q.obj N) :
    letI := derivedCategoryInstance (dgCat E) h
    letI := K.shiftD
    Triangle (Derived.derivedCategory (dgCat E) h) := by
  letI := Derived.homotopyCategory (dgCat E) h
  letI := derivedCategoryInstance (dgCat E) h
  letI := K.shiftK
  letI := K.shiftD
  let Q : HomComplex.homotopyCategory (dgCat E) ⥤ Derived.derivedCategory (dgCat E) h :=
    quotient (dgCat E) h
  letI : Q.CommShift ℤ := K.quotientShift
  let C := Q.mapTriangle.obj (DerivedTriangles.coneTriangle h K.shiftK (K.shiftObj L 1) i)
  exact Triangle.mk (Q.map (classOfMap h i)) (Q.map (classOfMap h p)) (q.inv ≫ C.mor₃)

/-- In the same localization, the strict comparison gives a morphism of the
actual distinguished triangles, independent of the compatible homotopy choices. -/
def LocalizedSequenceComparisons : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {E : CommDGAlgebra.{u,v} k}
    (h : HomotopyCategoryLaws (dgCat E)) (K : ConeLocalization (dgCat E) h)
    {L M N L' M' N' : E.Module} {i : L ⟶ M} {p : M ⟶ N} {i' : L' ⟶ M'} {p' : M' ⟶ N'},
    GradedSplit i p → GradedSplit i' p' →
    letI := Derived.homotopyCategory (dgCat E) h
    letI := derivedCategoryInstance (dgCat E) h
    letI := K.shiftD
    letI := K.addD
    letI := K.zeroD
    letI := K.addShiftD
    letI := K.trianglesD
    let Q : HomComplex.homotopyCategory (dgCat E) ⥤ Derived.derivedCategory (dgCat E) h :=
      quotient (dgCat E) h
    ∃ (q : cone i ⟶ N) (q' : cone i' ⟶ N')
      (e : Q.obj (cone i) ≅ Q.obj N) (e' : Q.obj (cone i') ≅ Q.obj N'),
      IsConeQuotient p q ∧ IsConeQuotient p' q' ∧
      e.hom = Q.map (classOfMap h q) ∧ e'.hom = Q.map (classOfMap h q') ∧
      let U := localizedSequenceTriangle h (adjunctionConeLocalization K) i p e
      let V := localizedSequenceTriangle h (adjunctionConeLocalization K) i' p' e'
      U ∈ distTriang (Derived.derivedCategory (dgCat E) h) ∧
      V ∈ distTriang (Derived.derivedCategory (dgCat E) h) ∧
      ∃ m : SequenceMap i p i' p' → (U ⟶ V),
        (∀ f, (m f).hom₁ = Q.map (classOfMap h f.left) ∧
          (m f).hom₂ = Q.map (classOfMap h f.middle) ∧
          (m f).hom₃ = Q.map (classOfMap h f.right)) ∧
        ∀ f g, SequenceHomotopy f g → m f = m g


/-- For the resolved terms, the exact derived extension of the localized
sequence triangle is its ordinary scalar extension, including the boundary. -/
def DerivedTriangleExtension : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {T : ModuleTensor.{u,v} k}, TensorFormulas T →
    ∀ {A B : CommDGAlgebra.{u,v} k} {f : A ⟶ B}
      (hA : HomotopyCategoryLaws (dgCat A)) (hB : HomotopyCategoryLaws (dgCat B))
      (E : DerivedTensor.ScalarExtension T f hA hB)
      {L M N : A.Module} {i : L ⟶ M} {p : M ⟶ N}
      (q : cone i ⟶ N), GradedSplit i p → IsConeQuotient p q →
      ∀ (hL : isKProjective L) (hM : isKProjective M) (hN : isKProjective N),
      letI := Derived.homotopyCategory (dgCat A) hA
      letI := Derived.homotopyCategory (dgCat B) hB
      letI := derivedCategoryInstance (dgCat A) hA
      letI := derivedCategoryInstance (dgCat B) hB
      let QA : HomComplex.homotopyCategory (dgCat A) ⥤ Derived.derivedCategory (dgCat A) hA :=
        quotient (dgCat A) hA
      let QB : HomComplex.homotopyCategory (dgCat B) ⥤ Derived.derivedCategory (dgCat B) hB :=
        quotient (dgCat B) hB
      let G := BimoduleAdjunction.ordinaryTensor E.models.tensor
      ∃ (KA : DerivedBimoduleAdjunction.ConeLocalization (dgCat A) hA) (KB : DerivedBimoduleAdjunction.ConeLocalization (dgCat B) hB),
        letI := KA.shiftD
        letI := KB.shiftD
        ∃ (s : E.functor.CommShift ℤ),
          letI := s
          ∃ (q' : cone (G.map i) ⟶ G.obj N)
            (e : QA.obj (cone i) ≅ QA.obj N) (e' : QB.obj (cone (G.map i)) ≅ QB.obj (G.obj N)),
            IsConeQuotient (G.map p) q' ∧ e.hom = QA.map (classOfMap hA q) ∧
            e'.hom = QB.map (classOfMap hB q') ∧
            let U := localizedSequenceTriangle hA KA i p e
            let V := localizedSequenceTriangle hB KB (G.map i) (G.map p) e'
            ∃ j : E.functor.mapTriangle.obj U ≅ V,
              j.hom.hom₁ = (E.data.onProjective L hL).hom ∧
              j.hom.hom₂ = (E.data.onProjective M hM).hom ∧
              j.hom.hom₃ = (E.data.onProjective N hN).hom

end
end Specs.DerivedFormalization.Affine.CotangentDiagramComparison
