import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.HomologySequence
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.HomotopyAndContraction
import Mathlib.Algebra.Homology.HomotopyCofiber
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! Shifts and cones, paper.tex 2338–2373. The general shape below has an
outgoing arrow at every degree. Integer chain and cochain shapes both satisfy
this condition. The coordinate order is the manuscript's (target, source).
All module statements allow arbitrary unital rings, and right modules by
specializing the ring to the opposite ring. Homology is the shared quotient.
-/
namespace P103.Specs.Ch10.ShiftsAndCones
open CategoryTheory CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.HomologySequence
open HomologicalComplex.homotopyCofiber
noncomputable section
universe u v w
variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}

/-- Translation by the outgoing degree, with the negative differential. -/
def shift (C : HomologicalComplex (ModuleCat.{v} R) c)
    (hn : ∀ n, c.Rel n (c.next n)) : HomologicalComplex (ModuleCat.{v} R) c where
  X n := C.X (c.next n)
  d i j := -C.d (c.next i) (c.next j)
  shape i j hij := by
    rw [C.shape, neg_zero]
    intro h
    have he : c.next i = j := c.prev_eq h (hn j)
    exact hij (he ▸ hn i)
  d_comp_d' i j k _ _ := by simp

/-- The shift term in any explicitly specified adjacent degree. -/
def shiftTermEquiv (C : HomologicalComplex (ModuleCat.{v} R) c)
    (hn : ∀ n, c.Rel n (c.next n)) (n m : ι) (h : c.Rel n m) :
    (shift C hn).X n ≃ₗ[R] C.X m :=
  (eqToIso (congrArg C.X (c.next_eq' h))).toLinearEquiv

variable [DecidableRel c.Rel]

/-- The library homotopy cofiber, with its standard negative source block. -/
abbrev cone {C D : HomologicalComplex (ModuleCat.{v} R) c} (f : C ⟶ D) :=
  HomologicalComplex.homotopyCofiber f

variable {C D : HomologicalComplex (ModuleCat.{v} R) c}

/-- Coordinates in the order (target, shifted source). -/
def coneTermEquiv (f : C ⟶ D) (n m : ι) (hn : c.Rel n m) :
    (cone f).X n ≃ₗ[R] D.X n × C.X m :=
  (((XIsoBiprod f n m hn) ≪≫
    ModuleCat.biprodIsoProd _ _).toLinearEquiv).trans (LinearEquiv.prodComm R _ _)

def coneInclusion (f : C ⟶ D) : D ⟶ cone f := inr f

def coneProjection (f : C ⟶ D) (hn : ∀ n, c.Rel n (c.next n)) :
    cone f ⟶ shift C hn where
  f n := fstX f n (c.next n) (hn n)
  comm' i j hij := by
    obtain rfl := c.next_eq' hij
    change fstX f i (c.next i) (hn i) ≫ (-C.d (c.next i) (c.next (c.next i))) =
      HomologicalComplex.homotopyCofiber.d f i (c.next i) ≫
        fstX f (c.next i) (c.next (c.next i)) (hn (c.next i))
    rw [d_fstX f _ _ _ (hn i) (hn (c.next i))]
    simp

/-- Negating the differential leaves the cycles unchanged. -/
def shiftCyclesEquiv (C : HomologicalComplex (ModuleCat.{v} R) c)
    (hn : ∀ n, c.Rel n (c.next n)) (n : ι) :
    cycles (shift C hn) n ≃ₗ[R] cycles C (c.next n) where
  toFun z := ⟨z.val, by
    have h := z.property
    change -((C.d (c.next n) (c.next (c.next n))).hom z.val) = 0 at h
    change (C.d (c.next n) (c.next (c.next n))).hom z.val = 0
    exact neg_eq_zero.mp h⟩
  invFun z := ⟨z.val, by
    have h := z.property
    change (C.d (c.next n) (c.next (c.next n))).hom z.val = 0 at h
    change -((C.d (c.next n) (c.next (c.next n))).hom z.val) = 0
    exact neg_eq_zero.mpr h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem shiftBoundary_iff (C : HomologicalComplex (ModuleCat.{v} R) c)
    (hn : ∀ n, c.Rel n (c.next n)) (hp : ∀ n, c.Rel (c.prev n) n)
    (n : ι) (x : C.X (c.next n)) :
    x ∈ boundaries (shift C hn) n ↔ x ∈ boundaries C (c.next n) := by
  change (∃ y : C.X (c.next (c.prev n)),
    (-C.d (c.next (c.prev n)) (c.next n)).hom y = x) ↔
    (∃ y : C.X (c.prev (c.next n)), (C.d (c.prev (c.next n)) (c.next n)).hom y = x)
  rw [c.next_eq' (hp n), c.prev_eq' (hn n)]
  constructor <;> rintro ⟨y, hy⟩ <;> exact ⟨-y, by simpa using hy⟩

/-- Shifted homology, constructed on the explicit quotient by boundaries. -/
def shiftHomologyEquiv (C : HomologicalComplex (ModuleCat.{v} R) c)
    (hn : ∀ n, c.Rel n (c.next n)) (hp : ∀ n, c.Rel (c.prev n) n) (n : ι) :
    Homology (shift C hn) n ≃ₗ[R] Homology C (c.next n) :=
  Submodule.Quotient.equiv _ _ (shiftCyclesEquiv C hn n) (by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (shiftBoundary_iff C hn hp n x.val).mp hx
    · intro hz
      refine ⟨(shiftCyclesEquiv C hn n).symm z, ?_, by simp⟩
      exact (shiftBoundary_iff C hn hp n z.val).mpr hz)

/-- The connecting map with the positive sign fixed by the source. -/
def coneConnecting (f : C ⟶ D) (hn : ∀ n, c.Rel n (c.next n))
    (hp : ∀ n, c.Rel (c.prev n) n) (n : ι) :
    Homology (shift C hn) n →ₗ[R] Homology D (c.next n) :=
  (homologyMap f (c.next n)).comp (shiftHomologyEquiv C hn hp n).toLinearMap

/-- Integer chain and cochain shapes have no missing adjacent degrees. -/
theorem chainOutgoing (n : ℤ) : (ComplexShape.down ℤ).Rel n ((ComplexShape.down ℤ).next n) := by
  change (ComplexShape.down ℤ).next n + 1 = n
  simp

theorem chainIncoming (n : ℤ) : (ComplexShape.down ℤ).Rel ((ComplexShape.down ℤ).prev n) n := by
  change n + 1 = (ComplexShape.down ℤ).prev n
  simp

theorem cochainOutgoing (n : ℤ) : (ComplexShape.up ℤ).Rel n ((ComplexShape.up ℤ).next n) := by
  change n + 1 = (ComplexShape.up ℤ).next n
  simp

theorem cochainIncoming (n : ℤ) : (ComplexShape.up ℤ).Rel ((ComplexShape.up ℤ).prev n) n := by
  change (ComplexShape.up ℤ).prev n + 1 = n
  simp

abbrev chainShift (C : Chain.{u,v} R) := shift C chainOutgoing
abbrev cochainShift (C : Cochain.{u,v} R) := shift C cochainOutgoing

def chainShiftTermEquiv (C : Chain.{u,v} R) (n : ℤ) :
    (chainShift C).X n ≃ₗ[R] C.X (n - 1) :=
  shiftTermEquiv C chainOutgoing n (n - 1) (by change n - 1 + 1 = n; omega)

def cochainShiftTermEquiv (C : Cochain.{u,v} R) (n : ℤ) :
    (cochainShift C).X n ≃ₗ[R] C.X (n + 1) :=
  shiftTermEquiv C cochainOutgoing n (n + 1) rfl

def chainConeTermEquiv {C D : Chain.{u,v} R} (f : C ⟶ D) (n : ℤ) :
    (cone f).X n ≃ₗ[R] D.X n × C.X (n - 1) :=
  coneTermEquiv f n (n - 1) (by change n - 1 + 1 = n; omega)

def cochainConeTermEquiv {C D : Cochain.{u,v} R} (f : C ⟶ D) (n : ℤ) :
    (cone f).X n ≃ₗ[R] D.X n × C.X (n + 1) :=
  coneTermEquiv f n (n + 1) rfl

def chainShiftHomologyEquiv (C : Chain.{u,v} R) (n : ℤ) :
    Homology (chainShift C) n ≃ₗ[R] Homology C (n - 1) :=
  (shiftHomologyEquiv C chainOutgoing chainIncoming n).trans
    (LinearEquiv.cast (M := fun m => Homology C m) (ChainComplex.next ℤ n))

def cochainShiftHomologyEquiv (C : Cochain.{u,v} R) (n : ℤ) :
    Homology (cochainShift C) n ≃ₗ[R] Homology C (n + 1) :=
  (shiftHomologyEquiv C cochainOutgoing cochainIncoming n).trans
    (LinearEquiv.cast (M := fun m => Homology C m) (CochainComplex.next ℤ n))

end
end P103.Specs.Ch10.ShiftsAndCones

namespace P103.Specs.Ch10.ShiftsAndCones
open CategoryTheory CategoryTheory.Limits
open P103.Specs.Ch10.Complexes
noncomputable section

def integerDouble : ℤ →ₗ[ℤ] ℤ := 2 • LinearMap.id

def integerModTwo : ℤ →ₗ[ℤ] ZMod 2 := (Int.castAddHom (ZMod 2)).toIntLinearMap

def augmentationSourceTerm (n : ℤ) : ModuleCat.{0} ℤ :=
  if n = 0 then ModuleCat.of ℤ ℤ
  else if n = 1 then ModuleCat.of ℤ ℤ
  else ModuleCat.of ℤ PUnit

def augmentationSourceDelta (n : ℤ) :
    augmentationSourceTerm (n + 1) ⟶ augmentationSourceTerm n := by
  by_cases h : n = 0
  · subst n
    exact ModuleCat.ofHom integerDouble
  exact 0

theorem augmentationSourceDelta_sq (n : ℤ) :
    augmentationSourceDelta (n + 1) ≫ augmentationSourceDelta n = 0 := by
  by_cases h : n = 0
  · subst n
    have he : augmentationSourceDelta 1 = 0 := by simp [augmentationSourceDelta]
    change augmentationSourceDelta 1 ≫ augmentationSourceDelta 0 = 0
    rw [he, zero_comp]
  have he : augmentationSourceDelta n = 0 := by simp [augmentationSourceDelta, h]
  rw [he, comp_zero]

def augmentationSource : Chain.{0,0} ℤ :=
  ChainComplex.of augmentationSourceTerm augmentationSourceDelta augmentationSourceDelta_sq

def augmentationTargetTerm (n : ℤ) : ModuleCat.{0} ℤ :=
  if n = 0 then ModuleCat.of ℤ (ZMod 2) else ModuleCat.of ℤ PUnit

def augmentationTarget : Chain.{0,0} ℤ :=
  ChainComplex.of augmentationTargetTerm (fun _ => 0) (fun _ => by simp)

def augmentationComponent (n : ℤ) : augmentationSourceTerm n ⟶ augmentationTargetTerm n := by
  by_cases h : n = 0
  · subst n
    exact ModuleCat.ofHom integerModTwo
  exact 0

def augmentation : augmentationSource ⟶ augmentationTarget :=
  ChainComplex.ofHom augmentationComponent (by
    intro n
    dsimp only [augmentationSource, augmentationTarget]
    rw [ChainComplex.of_d, ChainComplex.of_d, comp_zero]
    by_cases h : n = 0
    · subst n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change ℤ at x
      change (0 : ZMod 2) = integerModTwo (integerDouble x)
      change (0 : ZMod 2) = ((2 * (x : ℤ) : ℤ) : ZMod 2)
      simp only [Int.cast_mul, Int.cast_ofNat]
      rw [show (2 : ZMod 2) = 0 by decide, zero_mul]
    have he : augmentationSourceDelta n = 0 := by simp [augmentationSourceDelta, h]
    rw [he, zero_comp])
end
end P103.Specs.Ch10.ShiftsAndCones

namespace P103.Specs.Ch10.ShiftsAndCones
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.HomologySequence
noncomputable section
universe u v w
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! Full independent expected declaration types and canonical construction values. -/
abbrev shiftValue := @shift.{u,v,w}
def shiftType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
  (C : HomologicalComplex (ModuleCat.{v} R) c)
  (hn : ∀ n, c.Rel n (c.next n)), HomologicalComplex (ModuleCat.{v} R) c

abbrev shiftTermEquivValue := @shiftTermEquiv.{u,v,w}
def shiftTermEquivType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
  (C : HomologicalComplex (ModuleCat.{v} R) c)
  (hn : ∀ n, c.Rel n (c.next n)) (n m : ι) (h : c.Rel n m),
  (shift C hn).X n ≃ₗ[R] C.X m

abbrev coneValue := @cone.{u,v,w}
def coneType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
  [DecidableRel c.Rel] {C D : HomologicalComplex (ModuleCat.{v} R) c}
  (f : C ⟶ D), HomologicalComplex (ModuleCat.{v} R) c

abbrev coneTermEquivValue := @coneTermEquiv.{u,v,w}
def coneTermEquivType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
  [DecidableRel c.Rel] {C D : HomologicalComplex (ModuleCat.{v} R) c}
  (f : C ⟶ D) (n m : ι) (hn : c.Rel n m),
  (cone f).X n ≃ₗ[R] D.X n × C.X m

abbrev coneInclusionValue := @coneInclusion.{u,v,w}
def coneInclusionType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
  [DecidableRel c.Rel] {C D : HomologicalComplex (ModuleCat.{v} R) c}
  (f : C ⟶ D), D ⟶ cone f

abbrev coneProjectionValue := @coneProjection.{u,v,w}
def coneProjectionType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
  [DecidableRel c.Rel] {C D : HomologicalComplex (ModuleCat.{v} R) c}
  (f : C ⟶ D) (hn : ∀ n, c.Rel n (c.next n)), cone f ⟶ shift C hn

abbrev shiftCyclesEquivValue := @shiftCyclesEquiv.{u,v,w}
def shiftCyclesEquivType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
  (C : HomologicalComplex (ModuleCat.{v} R) c)
  (hn : ∀ n, c.Rel n (c.next n)) (n : ι),
  cycles (shift C hn) n ≃ₗ[R] cycles C (c.next n)

abbrev shiftHomologyEquivValue := @shiftHomologyEquiv.{u,v,w}
def shiftHomologyEquivType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
  [DecidableRel c.Rel] (C : HomologicalComplex (ModuleCat.{v} R) c)
  (hn : ∀ n, c.Rel n (c.next n)) (hp : ∀ n, c.Rel (c.prev n) n) (n : ι),
  Homology (shift C hn) n ≃ₗ[R] Homology C (c.next n)

abbrev coneConnectingValue := @coneConnecting.{u,v,w}
def coneConnectingType := ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
  [DecidableRel c.Rel] {C D : HomologicalComplex (ModuleCat.{v} R) c}
  (f : C ⟶ D) (hn : ∀ n, c.Rel n (c.next n))
  (hp : ∀ n, c.Rel (c.prev n) n) (n : ι),
  Homology (shift C hn) n →ₗ[R] Homology D (c.next n)

abbrev chainShiftValue := @chainShift.{u,v}
def chainShiftType := ∀ {R : Type u} [Ring R] (C : Chain.{u,v} R), Chain.{u,v} R

abbrev cochainShiftValue := @cochainShift.{u,v}
def cochainShiftType := ∀ {R : Type u} [Ring R] (C : Cochain.{u,v} R), Cochain.{u,v} R

abbrev chainShiftTermEquivValue := @chainShiftTermEquiv.{u,v}
def chainShiftTermEquivType := ∀ {R : Type u} [Ring R] (C : Chain.{u,v} R) (n : ℤ),
  (chainShift C).X n ≃ₗ[R] C.X (n - 1)

abbrev cochainShiftTermEquivValue := @cochainShiftTermEquiv.{u,v}
def cochainShiftTermEquivType := ∀ {R : Type u} [Ring R] (C : Cochain.{u,v} R) (n : ℤ),
  (cochainShift C).X n ≃ₗ[R] C.X (n + 1)

abbrev chainConeTermEquivValue := @chainConeTermEquiv.{u,v}
def chainConeTermEquivType := ∀ {R : Type u} [Ring R] {C D : Chain.{u,v} R}
  (f : C ⟶ D) (n : ℤ), (cone f).X n ≃ₗ[R] D.X n × C.X (n - 1)

abbrev cochainConeTermEquivValue := @cochainConeTermEquiv.{u,v}
def cochainConeTermEquivType := ∀ {R : Type u} [Ring R] {C D : Cochain.{u,v} R}
  (f : C ⟶ D) (n : ℤ), (cone f).X n ≃ₗ[R] D.X n × C.X (n + 1)

abbrev chainShiftHomologyEquivValue := @chainShiftHomologyEquiv.{u,v}
def chainShiftHomologyEquivType := ∀ {R : Type u} [Ring R] (C : Chain.{u,v} R) (n : ℤ),
  Homology (chainShift C) n ≃ₗ[R] Homology C (n - 1)

abbrev cochainShiftHomologyEquivValue := @cochainShiftHomologyEquiv.{u,v}
def cochainShiftHomologyEquivType := ∀ {R : Type u} [Ring R] (C : Cochain.{u,v} R) (n : ℤ),
  Homology (cochainShift C) n ≃ₗ[R] Homology C (n + 1)

abbrev integerDoubleValue := integerDouble
def integerDoubleType := ℤ →ₗ[ℤ] ℤ

abbrev integerModTwoValue := integerModTwo
def integerModTwoType := ℤ →ₗ[ℤ] ZMod 2

abbrev augmentationSourceValue := augmentationSource
def augmentationSourceType := Chain.{0,0} ℤ

abbrev augmentationTargetValue := augmentationTarget
def augmentationTargetType := Chain.{0,0} ℤ

abbrev augmentationValue := augmentation
def augmentationType := augmentationSource ⟶ augmentationTarget

end
end P103.Specs.Ch10.ShiftsAndCones

namespace P103.Specs.Ch10.ShiftsAndCones
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.HomologySequence
noncomputable section
universe u v w
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! Theorems: full propositions, with no assumed certificates. -/

def cone_d_coordinatesType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
  {C D : HomologicalComplex (ModuleCat.{v} R) c},
  ∀ (f : C ⟶ D) (i j k : ι)
    (hij : c.Rel i j) (hjk : c.Rel j k) (z : (cone f).X i),
    coneTermEquiv f j k hjk (((cone f).d i j).hom z) =
      ((D.d i j).hom (coneTermEquiv f i j hij z).1 +
        (f.f j).hom (coneTermEquiv f i j hij z).2,
      -(C.d j k).hom (coneTermEquiv f i j hij z).2)

def coneInclusion_coordinatesType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
  {C D : HomologicalComplex (ModuleCat.{v} R) c},
  ∀ (f : C ⟶ D) (n m : ι) (hn : c.Rel n m) (y : D.X n),
    coneTermEquiv f n m hn (((coneInclusion f).f n).hom y) = (y, 0)

def coneProjection_coordinatesType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
  {C D : HomologicalComplex (ModuleCat.{v} R) c},
  ∀ (f : C ⟶ D) (hn : ∀ n, c.Rel n (c.next n))
    (n : ι) (z : (cone f).X n),
    ((coneProjection f hn).f n).hom z = (coneTermEquiv f n (c.next n) (hn n) z).2

def coneTermEquiv_symm_applyType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
  {C D : HomologicalComplex (ModuleCat.{v} R) c},
  ∀ (f : C ⟶ D) (n m : ι) (hn : c.Rel n m)
    (y : D.X n) (x : C.X m),
    (coneTermEquiv f n m hn).symm (y, x) =
      (HomologicalComplex.homotopyCofiber.inrX f n).hom y +
        (HomologicalComplex.homotopyCofiber.inlX f m n hn).hom x

def cone_degreewise_exactType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
  {C D : HomologicalComplex (ModuleCat.{v} R) c},
  ∀ (f : C ⟶ D) (hn : ∀ n, c.Rel n (c.next n)),
    DegreewiseExact (coneInclusion f) (coneProjection f hn)

def cone_degreewise_splitType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
  {C D : HomologicalComplex (ModuleCat.{v} R) c},
  ∀ (f : C ⟶ D) (hn : ∀ n, c.Rel n (c.next n)),
    ∀ n, ∃ s : (shift C hn).X n →ₗ[R] (cone f).X n,
      ((coneProjection f hn).f n).hom.comp s = LinearMap.id

def shiftHomologyEquiv_classType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
  {C : HomologicalComplex (ModuleCat.{v} R) c},
  ∀ (hn : ∀ n, c.Rel n (c.next n))
    (hp : ∀ n, c.Rel (c.prev n) n) (n : ι) (z : cycles (shift C hn) n),
    shiftHomologyEquiv C hn hp n (homologyClass (shift C hn) n z) =
      homologyClass C (c.next n) (shiftCyclesEquiv C hn n z)

def cone_connectingType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
  {C D : HomologicalComplex (ModuleCat.{v} R) c},
  ∀ (f : C ⟶ D) (hn : ∀ n, c.Rel n (c.next n))
    (hp : ∀ n, c.Rel (c.prev n) n) (n : ι),
    Connecting (coneInclusion f) (coneProjection f hn) n (c.next n)
      ((homologyMap f (c.next n)).comp (shiftHomologyEquiv C hn hp n).toLinearMap)

def cone_sequence_exactType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
  {C D : HomologicalComplex (ModuleCat.{v} R) c},
  ∀ (f : C ⟶ D)
    (hn : ∀ n, c.Rel n (c.next n)) (hp : ∀ n, c.Rel (c.prev n) n) (n : ι),
    SequenceExact (coneInclusion f) (coneProjection f hn) n (c.next n)
      (coneConnecting f hn hp n)

def cone_criterionType : Prop :=
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
  {C D : HomologicalComplex (ModuleCat.{v} R) c},
  ∀ (f : C ⟶ D)
    (hn : ∀ n, c.Rel n (c.next n)) (hp : ∀ n, c.Rel (c.prev n) n),
    QuasiIsomorphism f ↔ Acyclic (cone f)

def shift_d_coordinatesType : Prop :=
  ∀ {R : Type u} [Ring R],
  ∀ {ι : Type w} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c) (hn : ∀ n, c.Rel n (c.next n))
    (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k) (z : (shift C hn).X i),
    shiftTermEquiv C hn j k hjk (((shift C hn).d i j).hom z) =
      -(C.d j k).hom (shiftTermEquiv C hn i j hij z)

def chain_shift_differentialType : Prop :=
  ∀ {R : Type u} [Ring R],
  ∀ (C : Chain.{u,v} R) (n : ℤ)
    (z : (chainShift C).X n),
    chainShiftTermEquiv C (n - 1) (((chainShift C).d n (n - 1)).hom z) =
      -(C.d (n - 1) ((n - 1) - 1)).hom (chainShiftTermEquiv C n z)

def cochain_shift_differentialType : Prop :=
  ∀ {R : Type u} [Ring R],
  ∀ (C : Cochain.{u,v} R) (n : ℤ)
    (z : (cochainShift C).X n),
    cochainShiftTermEquiv C (n + 1) (((cochainShift C).d n (n + 1)).hom z) =
      -(C.d (n + 1) ((n + 1) + 1)).hom (cochainShiftTermEquiv C n z)

def chain_cone_differentialType : Prop :=
  ∀ {R : Type u} [Ring R],
  ∀ {C D : Chain.{u,v} R} (f : C ⟶ D) (n : ℤ)
    (z : (cone f).X n),
    chainConeTermEquiv f (n - 1) (((cone f).d n (n - 1)).hom z) =
      ((D.d n (n - 1)).hom (chainConeTermEquiv f n z).1 +
        (f.f (n - 1)).hom (chainConeTermEquiv f n z).2,
      -(C.d (n - 1) ((n - 1) - 1)).hom (chainConeTermEquiv f n z).2)

def cochain_cone_differentialType : Prop :=
  ∀ {R : Type u} [Ring R],
  ∀ {C D : Cochain.{u,v} R} (f : C ⟶ D) (n : ℤ)
    (z : (cone f).X n),
    cochainConeTermEquiv f (n + 1) (((cone f).d n (n + 1)).hom z) =
      ((D.d n (n + 1)).hom (cochainConeTermEquiv f n z).1 +
        (f.f (n + 1)).hom (cochainConeTermEquiv f n z).2,
      -(C.d (n + 1) ((n + 1) + 1)).hom (cochainConeTermEquiv f n z).2)

def chain_cone_criterionType : Prop :=
  ∀ {R : Type u} [Ring R],
  ∀ {C D : Chain.{u,v} R} (f : C ⟶ D),
    QuasiIsomorphism f ↔ Acyclic (cone f)

def cochain_cone_criterionType : Prop :=
  ∀ {R : Type u} [Ring R],
  ∀ {C D : Cochain.{u,v} R} (f : C ⟶ D),
    QuasiIsomorphism f ↔ Acyclic (cone f)

def identityCone_contractionType : Prop :=
  ∀ {R : Type u} [Ring R],
  ∀ {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
    (C : HomologicalComplex (ModuleCat.{v} R) c) (hn : ∀ n, c.Rel n (c.next n))
    (hp : ∀ n, c.Rel (c.prev n) n),
    ∃ h : Homotopy (𝟙 (cone (𝟙 C))) 0,
      ∀ (i j k : ι) (hji : c.Rel j i) (hik : c.Rel i k) (z : (cone (𝟙 C)).X i),
        coneTermEquiv (𝟙 C) j i hji ((h.hom i j).hom z) =
          (0, (coneTermEquiv (𝟙 C) i k hik z).1)

def chain_cone_connectingType : Prop :=
  ∀ {R : Type u} [Ring R] {C D : Chain.{u,v} R} (f : C ⟶ D) (n : ℤ),
    Connecting (coneInclusion f) (coneProjection f chainOutgoing) n (n - 1)
      ((homologyMap f (n - 1)).comp (chainShiftHomologyEquiv C n).toLinearMap)

def cochain_cone_connectingType : Prop :=
  ∀ {R : Type u} [Ring R] {C D : Cochain.{u,v} R} (f : C ⟶ D) (n : ℤ),
    Connecting (coneInclusion f) (coneProjection f cochainOutgoing) n (n + 1)
      ((homologyMap f (n + 1)).comp (cochainShiftHomologyEquiv C n).toLinearMap)

def augmentationSource_dType : Prop :=
  (augmentationSource.d 1 0).hom = integerDouble

def augmentation_zeroType : Prop :=
  (augmentation.f 0).hom = integerModTwo

def augmentationSource_degree_zeroType : Prop :=
  augmentationSource.X 0 = ModuleCat.of ℤ ℤ

def augmentationSource_degree_oneType : Prop :=
  augmentationSource.X 1 = ModuleCat.of ℤ ℤ

def augmentationTarget_degree_zeroType : Prop :=
  augmentationTarget.X 0 = ModuleCat.of ℤ (ZMod 2)

def augmentationSource_supportedType : Prop :=
  SupportedIn augmentationSource ({0, 1} : Set ℤ)

def augmentationTarget_supportedType : Prop :=
  SupportedIn augmentationTarget ({0} : Set ℤ)

def augmentation_reverse_zeroType : Prop :=
  ∀ (g : augmentationTarget ⟶ augmentationSource),
    g = 0

def augmentation_quasiIsomorphismType : Prop :=
  QuasiIsomorphism augmentation

def augmentation_not_homotopyEquivType : Prop :=
  ¬ Nonempty (HomotopyEquiv augmentationSource augmentationTarget)

end
end P103.Specs.Ch10.ShiftsAndCones
