import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ExtBoundarySigns

/-!
HA-R13's injective horseshoe, with the endpoint coaugmentations of HA-R11.
See notes/002/advanced-homological-algebra.tex:2060–2089 and 2114–2135.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits
open CochainComplex HomComplex Specs.AdvancedHomologicalAlgebra.ExtShiftedHom

namespace Specs.AdvancedHomologicalAlgebra.ExtInjectiveHorseshoe

variable {A : Type u} [Category.{v} A] [Abelian A]

noncomputable abbrev Stalk (X : A) := (CochainComplex.singleFunctor A 0).obj X

def BoundedInjective (I : CochainComplex A ℤ) : Prop :=
  (∃ b : ℤ, ∀ i < b, IsZero (I.X i)) ∧ (∀ i : ℤ, Injective (I.X i))

def SplitsDegreewise (T : ShortComplex (CochainComplex A ℤ)) : Prop :=
  ∀ n : ℤ, Nonempty (T.map (HomologicalComplex.eval A (.up ℤ) n)).Splitting

/-- A compatible row with the two prescribed complexes as literal endpoints. -/
structure ResolvingRow (S : ShortComplex A) {I J : CochainComplex A ℤ}
    (i : Stalk S.X₁ ⟶ I) (j : Stalk S.X₃ ⟶ J) where
  middle : CochainComplex A ℤ
  inclusion : I ⟶ middle
  projection : middle ⟶ J
  zero : inclusion ≫ projection = 0
  augmentation : Stalk S.X₂ ⟶ middle
  comm_left : i ≫ inclusion = (CochainComplex.singleFunctor A 0).map S.f ≫ augmentation
  comm_right : augmentation ≫ projection = (CochainComplex.singleFunctor A 0).map S.g ≫ j

namespace ResolvingRow

variable {S : ShortComplex A} {I J : CochainComplex A ℤ}
  {i : Stalk S.X₁ ⟶ I} {j : Stalk S.X₃ ⟶ J}

abbrev row (R : ResolvingRow S i j) := ShortComplex.mk R.inclusion R.projection R.zero

noncomputable abbrev map (R : ResolvingRow S i j) :
    S.map (CochainComplex.singleFunctor A 0) ⟶ R.row where
  τ₁ := i
  τ₂ := R.augmentation
  τ₃ := j
  comm₁₂ := R.comm_left
  comm₂₃ := R.comm_right

def IsHorseshoe (R : ResolvingRow S i j) : Prop :=
  R.row.ShortExact ∧ BoundedInjective R.middle ∧ QuasiIso R.augmentation ∧
    SplitsDegreewise R.row

end ResolvingRow

def existsHorseshoeType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] (S : ShortComplex A) (_ : S.ShortExact)
    (I J : CochainComplex A ℤ)
    (i : Stalk S.X₁ ⟶ I) (j : Stalk S.X₃ ⟶ J),
    QuasiIso i → QuasiIso j → BoundedInjective I → BoundedInjective J →
    ∃ R : ResolvingRow S i j, R.IsHorseshoe

abbrev HomClass (X : A) (I : CochainComplex A ℤ) (n : ℤ) :=
  CohomologyClass (Stalk X) I n

def Lifts {T : ShortComplex (CochainComplex A ℤ)} {X : A} {n : ℤ}
    (z : Cocycle (Stalk X) T.X₃ n) (b : Cochain (Stalk X) T.X₂ n) : Prop :=
  b.comp (Cochain.ofHom T.g) (add_zero n) = z.1

def Descends {T : ShortComplex (CochainComplex A ℤ)} {X : A} {n : ℤ}
    (b : Cochain (Stalk X) T.X₂ n) (a : Cocycle (Stalk X) T.X₁ (n+1)) : Prop :=
  δ n (n+1) b = (a.postcomp T.f).1

/-- The ordinary connecting map is characterized by the unsigned differential of a lift. -/
def IsOrdinaryConnector (T : ShortComplex (CochainComplex A ℤ)) (X : A) (n : ℤ)
    (d : HomClass X T.X₃ n →+ HomClass X T.X₁ (n+1)) : Prop :=
  ∀ (z : Cocycle (Stalk X) T.X₃ n) (b : Cochain (Stalk X) T.X₂ n)
    (a : Cocycle (Stalk X) T.X₁ (n+1)), Lifts z b → Descends b a →
      d (CohomologyClass.mk z) = CohomologyClass.mk a

def liftsType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] (T : ShortComplex (CochainComplex A ℤ))
    (_ : T.ShortExact)
    (_ : SplitsDegreewise T)
    (X : A) (n : ℤ) (z : Cocycle (Stalk X) T.X₃ n),
    (∃ b : Cochain (Stalk X) T.X₂ n, Lifts z b) ∧
    ∀ (b : Cochain (Stalk X) T.X₂ n), Lifts z b →
      ∃! a : Cocycle (Stalk X) T.X₁ (n+1), Descends b a

def ordinaryConnectorType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] (T : ShortComplex (CochainComplex A ℤ))
    (_ : T.ShortExact)
    (_ : SplitsDegreewise T)
    (X : A) (n : ℤ), ∃! d : HomClass X T.X₃ n →+ HomClass X T.X₁ (n+1),
      IsOrdinaryConnector T X n d

def connectorComparisonType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (S : ShortComplex A) (hS : S.ShortExact) (I J : CochainComplex A ℤ)
    (i : Stalk S.X₁ ⟶ I) (j : Stalk S.X₃ ⟶ J)
    (hi : QuasiIso i) (hj : QuasiIso j) (R : ResolvingRow S i j)
    (_ : R.row.ShortExact) (_ : SplitsDegreewise R.row)
    (X : A) (n : ℤ) (d : HomClass X J n →+ HomClass X I (n+1)),
    IsOrdinaryConnector R.row X n d → ∀ x : HomClass X J n,
      injectiveClassMap X S.X₁ I i hi (n+1) (d x) =
        ShiftedHom.comp (injectiveClassMap X S.X₃ J j hj n x) hS.singleδ (add_comm 1 n)

def connectorIndependenceType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (S : ShortComplex A) (_ : S.ShortExact) (I J : CochainComplex A ℤ)
    (i : Stalk S.X₁ ⟶ I) (j : Stalk S.X₃ ⟶ J),
    QuasiIso i → QuasiIso j → BoundedInjective I → BoundedInjective J →
    ∀ (R R' : ResolvingRow S i j),
    R.row.ShortExact → SplitsDegreewise R.row →
    R'.row.ShortExact → SplitsDegreewise R'.row →
    ∀ (X : A) (n : ℤ) (d d' : HomClass X J n →+ HomClass X I (n+1)),
      IsOrdinaryConnector R.row X n d → IsOrdinaryConnector R'.row X n d' → d = d'

end Specs.AdvancedHomologicalAlgebra.ExtInjectiveHorseshoe
