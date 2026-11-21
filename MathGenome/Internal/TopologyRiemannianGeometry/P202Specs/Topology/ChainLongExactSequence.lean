import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Interfaces for paper.tex, Lemma `lem:p202-chain-les` (1157–1184).

The shape is arbitrary, so the same constructions apply to ordinary complexes
(`ComplexShape.down ℕ`), integer graded complexes (`ComplexShape.down ℤ`),
and augmented complexes with their coefficient object in degree -1.
No boundedness, freeness, or splitting is required.  `Ab` and `ModuleCat R`
are instances of the categories below; in particular the ring need not be a field.
-/

open CategoryTheory HomologicalComplex

universe u v w

namespace P202Specs.ChainLES

/-- On abelian groups, forgetting to abelian groups is the identity. -/
instance abForgetSelf : HasForget₂ Ab.{v} Ab.{v} where
  forget₂ := 𝟭 _
  forget_comp := rfl

instance abForgetSelf_additive : (forget₂ Ab.{v} Ab.{v}).Additive :=
  inferInstanceAs (𝟭 Ab.{v}).Additive

noncomputable instance abForgetSelf_preservesHomology :
    (forget₂ Ab.{v} Ab.{v}).PreservesHomology :=
  inferInstanceAs (𝟭 Ab.{v}).PreservesHomology

section Abelian
variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} {shape : ComplexShape ι}

/-- The hypothesis is short exactness in every degree. -/
def DegreewiseShortExact (S : ShortComplex (HomologicalComplex C shape)) : Prop :=
  ∀ n, (S.map (HomologicalComplex.eval C shape n)).ShortExact

/-- The connecting map has the positive boundary-of-a-lift convention. -/
noncomputable def connecting {S : ShortComplex (HomologicalComplex C shape)}
    (h : DegreewiseShortExact S) (i j : ι) (hij : shape.Rel i j) :
    S.X₃.homology i ⟶ S.X₁.homology j :=
  (HomologicalComplex.shortExact_of_degreewise_shortExact S h).δ i j hij

/-- All finite overlapping six-term pieces of the long sequence. -/
noncomputable def segment {S : ShortComplex (HomologicalComplex C shape)}
    (h : DegreewiseShortExact S) (i j : ι) (hij : shape.Rel i j) :
    ComposableArrows C 5 :=
  ComposableArrows.mk₅ (homologyMap S.f i) (homologyMap S.g i)
    (connecting h i j hij) (homologyMap S.f j) (homologyMap S.g j)

end Abelian

/-- Exactness at every kind of term, including the middle term in any degree. -/
def ExactnessType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] {ι : Type w} {shape : ComplexShape ι}
    (S : ShortComplex (HomologicalComplex C shape)) (h : DegreewiseShortExact S),
    (∀ n, (HomologicalComplex.HomologySequence.composableArrows₂ S n).Exact) ∧
    (∀ i j (hij : shape.Rel i j), (segment h i j hij).Exact)

/-- Naturality of all three sorts of arrows for every morphism of short sequences. -/
def NaturalityType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] {ι : Type w} {shape : ComplexShape ι}
    {S T : ShortComplex (HomologicalComplex C shape)} (φ : S ⟶ T)
    (hS : DegreewiseShortExact S) (hT : DegreewiseShortExact T),
    (∀ n, homologyMap S.f n ≫ homologyMap φ.τ₂ n =
      homologyMap φ.τ₁ n ≫ homologyMap T.f n) ∧
    (∀ n, homologyMap S.g n ≫ homologyMap φ.τ₃ n =
      homologyMap φ.τ₂ n ≫ homologyMap T.g n) ∧
    (∀ i j (hij : shape.Rel i j), connecting hS i j hij ≫ homologyMap φ.τ₁ j =
      homologyMap φ.τ₃ i ≫ connecting hT i j hij)

/-- The ordinary sequence ends in `H₀(M) ⟶ 0`. -/
def OrdinaryEndpointType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex (ChainComplex C ℕ)) (h : DegreewiseShortExact S),
    Epi (homologyMap S.g 0)

/-- Explicit consecutive degree interfaces, also covering the augmented 0 to -1 map. -/
def IntegerIndexType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex (ChainComplex C ℤ)) (h : DegreewiseShortExact S) (n : ℤ),
    (segment h (n + 1) n (by simp)).Exact

def NaturalIndexType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex (ChainComplex C ℕ)) (h : DegreewiseShortExact S) (n : ℕ),
    (segment h (n + 1) n (by simp)).Exact

section Concrete
variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
  [HasForget₂ C Ab.{v}] [Abelian C] [(forget₂ C Ab).Additive]
  [(forget₂ C Ab).PreservesHomology] {ι : Type w} {shape : ComplexShape ι}

/-- The actual homology class of a cycle, through the categorical kernel and quotient. -/
noncomputable def cycleClass (K : HomologicalComplex C shape) {i : ι}
    (j : ι) (hj : shape.next i = j) (z : (forget₂ C Ab).obj (K.X i))
    (hz : (forget₂ C Ab).map (K.d i j) z = 0) :
    (forget₂ C Ab).obj (K.homology i) :=
  (forget₂ C Ab).map (K.homologyπ i) (K.cyclesMk z j hj hz)

/-- No lift or inverse image is assumed to exist: both are conclusions.
The inverse image is unique and is a cycle in every outgoing degree. -/
def LiftsExist (S : ShortComplex (HomologicalComplex C shape))
    (h : DegreewiseShortExact S) : Prop :=
  ∀ i j (hij : shape.Rel i j) (z : (forget₂ C Ab).obj (S.X₃.X i))
    (hz : (forget₂ C Ab).map (S.X₃.d i j) z = 0),
    ∃ c : (forget₂ C Ab).obj (S.X₂.X i),
      (forget₂ C Ab).map (S.g.f i) c = z ∧
      ∃! x : (forget₂ C Ab).obj (S.X₁.X j),
        (forget₂ C Ab).map (S.f.f j) x = (forget₂ C Ab).map (S.X₂.d i j) c ∧
        ∀ k, (forget₂ C Ab).map (S.X₁.d j k) x = 0

/-- The lift formula holds for every lift and every inverse image of its boundary.
The two cycle conditions merely make the displayed classes well typed;
`LiftsExist` supplies the target cycle condition without an extra hypothesis. -/
def LiftFormula (S : ShortComplex (HomologicalComplex C shape))
    (h : DegreewiseShortExact S) : Prop :=
  ∀ i j (hij : shape.Rel i j) (z : (forget₂ C Ab).obj (S.X₃.X i))
    (hz : (forget₂ C Ab).map (S.X₃.d i j) z = 0)
    (c : (forget₂ C Ab).obj (S.X₂.X i))
    (hc : (forget₂ C Ab).map (S.g.f i) c = z)
    (x : (forget₂ C Ab).obj (S.X₁.X j))
    (hx : (forget₂ C Ab).map (S.f.f j) x = (forget₂ C Ab).map (S.X₂.d i j) c)
    (hxcycle : (forget₂ C Ab).map (S.X₁.d j (shape.next j)) x = 0),
    (forget₂ C Ab).map (connecting h i j hij)
      (cycleClass S.X₃ j (shape.next_eq' hij) z hz) =
      cycleClass S.X₁ (shape.next j) rfl x hxcycle

/-- Independence of both the lift and the cycle representative.
Representatives are equivalent precisely when their actual homology classes agree. -/
def Independence (S : ShortComplex (HomologicalComplex C shape))
    (h : DegreewiseShortExact S) : Prop :=
  ∀ i j (hij : shape.Rel i j)
    (z z' : (forget₂ C Ab).obj (S.X₃.X i))
    (hz : (forget₂ C Ab).map (S.X₃.d i j) z = 0)
    (hz' : (forget₂ C Ab).map (S.X₃.d i j) z' = 0)
    (heq : cycleClass S.X₃ j (shape.next_eq' hij) z hz =
      cycleClass S.X₃ j (shape.next_eq' hij) z' hz')
    (c c' : (forget₂ C Ab).obj (S.X₂.X i))
    (hc : (forget₂ C Ab).map (S.g.f i) c = z)
    (hc' : (forget₂ C Ab).map (S.g.f i) c' = z')
    (x x' : (forget₂ C Ab).obj (S.X₁.X j))
    (hx : (forget₂ C Ab).map (S.f.f j) x = (forget₂ C Ab).map (S.X₂.d i j) c)
    (hx' : (forget₂ C Ab).map (S.f.f j) x' = (forget₂ C Ab).map (S.X₂.d i j) c')
    (hxc : (forget₂ C Ab).map (S.X₁.d j (shape.next j)) x = 0)
    (hxc' : (forget₂ C Ab).map (S.X₁.d j (shape.next j)) x' = 0),
    cycleClass S.X₁ (shape.next j) rfl x hxc =
      cycleClass S.X₁ (shape.next j) rfl x' hxc'

end Concrete

/-- Concrete theorem for arbitrary modules, with no finiteness assumptions. -/
def ModuleLiftType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {shape : ComplexShape ι}
    (S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) shape))
    (h : DegreewiseShortExact S), LiftsExist S h ∧ LiftFormula S h ∧ Independence S h

/-- The abelian group specialization uses the category of all abelian groups. -/
def AbelianGroupLiftType : Prop :=
  ∀ {ι : Type w} {shape : ComplexShape ι}
    (S : ShortComplex (HomologicalComplex Ab.{v} shape))
    (h : DegreewiseShortExact S), LiftsExist S h ∧ LiftFormula S h ∧ Independence S h

/-- The categorical hypothesis agrees with ordinary elementwise short exactness. -/
def ModuleHypothesisType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {shape : ComplexShape ι}
    (S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) shape)),
    DegreewiseShortExact S ↔ ∀ n,
      Function.Injective (S.f.f n) ∧
      (∀ y, S.g.f n y = 0 → ∃ x, S.f.f n x = y) ∧
      Function.Surjective (S.g.f n)

end P202Specs.ChainLES
