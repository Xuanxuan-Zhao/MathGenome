import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.Complexes
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Data.ZMod.Basic

/-!
Homotopy invariance and contraction, paper.tex 2260–2296.
The ring is arbitrary, including the zero ring. Right modules are covered by
using the opposite ring. Homology is the upstream explicit quotient.
The generic homotopy is Mathlib's `Homotopy`; the chain and cochain interfaces
below state the manuscript's single-index formulas. The `eqToHom` maps
only identify (n-1)+1 and (n+1)-1 with n.
-/
namespace P103.Specs.Ch10.HomotopyAndContraction
open CategoryTheory
open P103.Specs.Ch10.Complexes
noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false
universe u v w

variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}

/-- The incoming differential, with codomain restricted to the cycles. -/
def cycleDifferential (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι) :
    C.X (c.prev n) →ₗ[R] cycles C n :=
  (C.d (c.prev n) n).hom.codRestrict (cycles C n) (by
    intro x
    exact boundaryInclusion C n ⟨x, rfl⟩)

/-- Identity homotopic to zero, with no boundedness condition. -/
def Contractible (C : HomologicalComplex (ModuleCat.{v} R) c) : Prop :=
  Nonempty (Homotopy (𝟙 C) 0)

/-- All cycle sequences are split short exact. This uses the incoming index:
`0 → Z_(prev n) → C_(prev n) → Z_n → 0`.
For integer chains put n=m-1 to obtain the manuscript's sequence at m;
for integer cochains put n=m+1. -/
def SplitExactCycles (C : HomologicalComplex (ModuleCat.{v} R) c) : Prop :=
  ∀ n, Function.Injective (cycles C (c.prev n)).subtype ∧
    Function.Exact (cycles C (c.prev n)).subtype (cycleDifferential C n) ∧
    Function.Surjective (cycleDifferential C n) ∧
    ∃ s : cycles C n →ₗ[R] C.X (c.prev n),
      (cycleDifferential C n).comp s = LinearMap.id

abbrev cycleDifferentialValue := @cycleDifferential.{u,v,w}
def cycleDifferentialType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
  (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι),
  C.X (c.prev n) →ₗ[R] cycles C n
abbrev ContractibleValue := @Contractible.{u,v,w}
def ContractibleType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
  (C : HomologicalComplex (ModuleCat.{v} R) c), Prop
abbrev SplitExactCyclesValue := @SplitExactCycles.{u,v,w}
def SplitExactCyclesType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
  (C : HomologicalComplex (ModuleCat.{v} R) c), Prop

def homotopy_homologyMapType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {C D : HomologicalComplex (ModuleCat.{v} R) c} {f g : C ⟶ D}
    (h : Homotopy f g) (n : ι), homologyMap f n = homologyMap g n

def chain_homotopy_homologyMapType : Prop :=
  ∀ {R : Type u} [Ring R] {C D : Chain.{u,v} R} (f g : C ⟶ D)
    (s : ∀ n : ℤ, C.X n →ₗ[R] D.X (n + 1))
    (hs : ∀ n, (f.f n).hom - (g.f n).hom =
      (D.d (n + 1) n).hom.comp (s n) +
        ((eqToHom (congrArg D.X (sub_add_cancel n 1))).hom.comp (s (n - 1))).comp
          (C.d n (n - 1)).hom)
    (n : ℤ), homologyMap f n = homologyMap g n

def cochain_homotopy_homologyMapType : Prop :=
  ∀ {R : Type u} [Ring R] {C D : Cochain.{u,v} R} (f g : C ⟶ D)
    (s : ∀ n : ℤ, C.X n →ₗ[R] D.X (n - 1))
    (hs : ∀ n, (f.f n).hom - (g.f n).hom =
      (D.d (n - 1) n).hom.comp (s n) +
        ((eqToHom (congrArg D.X (add_sub_cancel_right n 1))).hom.comp (s (n + 1))).comp
          (C.d n (n + 1)).hom)
    (n : ℤ), homologyMap f n = homologyMap g n

/-- Both chain and cochain homotopy equivalences induce the specified linear
isomorphisms of the explicit homology quotients. -/
def homotopyEquiv_homologyType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {C D : HomologicalComplex (ModuleCat.{v} R) c}
    (h : HomotopyEquiv C D) (n : ι),
    ∃ e : Homology C n ≃ₗ[R] Homology D n,
      e.toLinearMap = homologyMap h.hom n ∧ e.symm.toLinearMap = homologyMap h.inv n

def homotopyEquiv_quasiIsomorphismType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {C D : HomologicalComplex (ModuleCat.{v} R) c}
    (h : HomotopyEquiv C D), QuasiIsomorphism h.hom

def contractible_acyclicType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c), Contractible C → Acyclic C

def chain_contractible_iffType : Prop :=
  ∀ {R : Type u} [Ring R] (C : Chain.{u,v} R),
    Contractible C ↔ Acyclic C ∧ SplitExactCycles C

def cochain_contractible_iffType : Prop :=
  ∀ {R : Type u} [Ring R] (C : Cochain.{u,v} R),
    Contractible C ↔ Acyclic C ∧ SplitExactCycles C

/-- The source's map sending 1 mod 2 to 2 mod 4. -/
def doubleModTwo : ZMod 2 →ₗ[ℤ] ZMod 4 :=
  ({ toFun := fun x => if x = 0 then 0 else 2
     map_zero' := by decide
     map_add' := by decide } : ZMod 2 →+ ZMod 4).toIntLinearMap

/-- Reduction modulo 2. -/
def reductionModTwo : ZMod 4 →ₗ[ℤ] ZMod 2 :=
  (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toAddMonoidHom.toIntLinearMap

abbrev doubleModTwoValue := doubleModTwo
def doubleModTwoType := ZMod 2 →ₗ[ℤ] ZMod 4
abbrev reductionModTwoValue := reductionModTwo
def reductionModTwoType := ZMod 4 →ₗ[ℤ] ZMod 2

def modTwo_shortExactType : Prop :=
  Function.Injective doubleModTwo ∧ Function.Exact doubleModTwo reductionModTwo ∧
    Function.Surjective reductionModTwo

def modTwo_no_additive_sectionType : Prop :=
  ¬ ∃ s : ZMod 2 →+ ZMod 4,
    reductionModTwo.toAddMonoidHom.comp s = AddMonoidHom.id (ZMod 2)

/-- A complex in degrees 2,1,0, with exactly the stated modules and maps.
The identifications make the representative maps unambiguous; the support
condition supplies the zero terms in every other integer degree. -/
def acyclic_noncontractible_exampleType : Prop :=
  ∃ (C : Chain.{0,0} ℤ)
    (e₂ : C.X 2 ≃ₗ[ℤ] ZMod 2) (e₁ : C.X 1 ≃ₗ[ℤ] ZMod 4)
    (e₀ : C.X 0 ≃ₗ[ℤ] ZMod 2),
    SupportedIn C ({0, 1, 2} : Set ℤ) ∧
    e₁.toLinearMap.comp (C.d 2 1).hom = doubleModTwo.comp e₂.toLinearMap ∧
    e₀.toLinearMap.comp (C.d 1 0).hom = reductionModTwo.comp e₁.toLinearMap ∧
    Acyclic C ∧ ¬ Contractible C

end
end P103.Specs.Ch10.HomotopyAndContraction
