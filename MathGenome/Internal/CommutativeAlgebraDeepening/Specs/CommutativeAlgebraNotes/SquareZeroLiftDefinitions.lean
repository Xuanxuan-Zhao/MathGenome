import Mathlib.RingTheory.Extension.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Module.End
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! The data of Theorem 6.1, for an arbitrary square-zero surjection of commutative rings. -/

noncomputable section

namespace CommutativeAlgebraNotes.SquareZeroLift

universe u v w n l t

section KernelModule

variable {R S : Type*} [CommRing R] [CommRing S]
  (f : R →+* S) (hf : Function.Surjective f) (hs : RingHom.ker f ^ 2 = ⊥)

private theorem ker_le_ker_action (hs : RingHom.ker f ^ 2 = ⊥) :
    RingHom.ker f ≤ RingHom.ker (Module.toAddMonoidEnd R (RingHom.ker f)) := by
  intro r hr
  rw [RingHom.mem_ker]
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  change r * (x : R) = 0
  have h := Ideal.mul_mem_mul hr x.property
  simpa only [← pow_two, hs, Ideal.mem_bot] using h

/-- The target of a square-zero surjection acts on its kernel by multiplication by a lift. -/
@[instance_reducible]
def kernelModule (hf : Function.Surjective f) (hs : RingHom.ker f ^ 2 = ⊥) :
    Module S (RingHom.ker f) :=
  Module.compHom _ (f.liftOfSurjective hf ⟨_, ker_le_ker_action f hs⟩)

theorem kernelModule_smul (r : R) (x : RingHom.ker f) :
    letI := kernelModule f hf hs
    f r • x = r • x := by
  change (f.liftOfSurjective hf ⟨_, ker_le_ker_action f hs⟩) (f r) x = r • x
  rw [RingHom.liftOfSurjective_comp_apply]
  rfl

end KernelModule

/-- The prescribed base surjection, with its stated square-zero hypothesis. -/
structure BaseExtension (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] where
  hom : A' →+* A
  surjective : Function.Surjective hom
  squareZero : RingHom.ker hom ^ 2 = ⊥

variable {A' : Type u} {A : Type v} {B : Type w} {N : Type n}
  [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup N] [Module B N] (e : BaseExtension A' A)

namespace BaseExtension

/-- The square-zero ideal (I) in the base. -/
abbrev I : Ideal A' := RingHom.ker e.hom

instance : Module A e.I := kernelModule e.hom e.surjective e.squareZero

@[simp] theorem hom_smul (a : A') (x : e.I) : e.hom a • x = a • x :=
  kernelModule_smul e.hom e.surjective e.squareZero a x

/-- The algebra structure on (A) specified by the base surjection. -/
abbrev baseAlgebra : Algebra A' A := e.hom.toAlgebra

theorem kernelTower :
    letI := e.baseAlgebra
    IsScalarTower A' A e.I :=
  letI := e.baseAlgebra
  IsScalarTower.of_algebraMap_smul e.hom_smul

/-- The prescribed composite algebra structure on (B). -/
abbrev targetAlgebra (B : Type w) [CommRing B] [Algebra A B] : Algebra A' B :=
  ((algebraMap A B).comp e.hom).toAlgebra

variable (N) in
/-- The given (A)-linear coefficient map (I → N), using restriction along (A → B). -/
abbrev CoefficientMap :=
  letI : Module A N := Module.compHom N (algebraMap A B)
  e.I →ₗ[A] N

end BaseExtension

/-- A marked lift along (A' → A). Its structure map to (B) is over (A'). -/
structure Lift (c : e.CoefficientMap (B := B) N) where
  Ring : Type l
  [commRing : CommRing Ring]
  [algebra : Algebra A' Ring]
  map : Ring →+* B
  over : ∀ a : A', map (algebraMap A' Ring a) = algebraMap A B (e.hom a)
  surjective : Function.Surjective map
  squareZero : RingHom.ker map ^ 2 = ⊥
  marking :
    letI := kernelModule map surjective squareZero
    RingHom.ker map ≃ₗ[B] N
  induces :
    ∀ i : e.I, marking ⟨algebraMap A' Ring i, by
      rw [RingHom.mem_ker, over, RingHom.mem_ker.mp i.property, map_zero]⟩ = c i

namespace Lift

attribute [instance] commRing algebra

variable {e} {c : e.CoefficientMap (B := B) N} (L : Lift.{u,v,w,n,l} e c)

/-- The reduction map as an algebra homomorphism for the prescribed base action. -/
def algHom : letI := e.targetAlgebra B; L.Ring →ₐ[A'] B :=
  letI := e.targetAlgebra B
  { __ := L.map, commutes' := L.over }

abbrev ker : Ideal L.Ring := RingHom.ker L.map

instance : Module B L.ker := kernelModule L.map L.surjective L.squareZero

@[simp] theorem map_smul (r : L.Ring) (x : L.ker) : L.map r • x = r • x :=
  kernelModule_smul L.map L.surjective L.squareZero r x

/-- The map on kernels given by an equivalence that commutes with reduction. -/
def mapKer {M : Lift.{u,v,w,n,t} e c} (f : L.Ring ≃ₐ[A'] M.Ring)
    (h : ∀ x, M.map (f x) = L.map x) (x : L.ker) : M.ker :=
  ⟨f x, (h x).trans (RingHom.mem_ker.mp x.property)⟩

/-- Isomorphisms preserve the (A')-structure, the map to (B), and the identification with (N). -/
structure Iso (M : Lift.{u,v,w,n,t} e c) where
  equiv : L.Ring ≃ₐ[A'] M.Ring
  over : ∀ x, M.map (equiv x) = L.map x
  marked : ∀ x : L.ker, M.marking (L.mapKer equiv over x) = L.marking x

def Iso.refl : L.Iso L where
  equiv := AlgEquiv.refl
  over _ := rfl
  marked _ := rfl

def Iso.symm {L : Lift.{u,v,w,n,l} e c} {M : Lift.{u,v,w,n,t} e c} (f : L.Iso M) : M.Iso L where
  equiv := f.equiv.symm
  over x := by rw [← f.over, f.equiv.apply_symm_apply]
  marked x := by
    rw [← f.marked]
    congr 1
    exact Subtype.ext (f.equiv.apply_symm_apply x)

def Iso.trans {L : Lift.{u,v,w,n,l} e c} {M : Lift.{u,v,w,n,t} e c}
    {W : Lift e c} (f : L.Iso M) (g : M.Iso W) :
    L.Iso W where
  equiv := f.equiv.trans g.equiv
  over x := (g.over (f.equiv x)).trans (f.over x)
  marked x := (g.marked (L.mapKer f.equiv f.over x)).trans (f.marked x)

/-- The equivalence relation used for isomorphism classes of marked lifts. -/
def isoSetoid : Setoid (Lift.{u,v,w,n,l} e c) where
  r L M := Nonempty (L.Iso M)
  iseqv := ⟨fun L => ⟨Iso.refl L⟩, fun ⟨f⟩ => ⟨f.symm⟩, fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩

/-- Isomorphism classes of lifts with underlying ring in universe `l`. -/
def Classes {e : BaseExtension A' A} (c : e.CoefficientMap (B := B) N) :=
  Quotient (isoSetoid (c := c) : Setoid (Lift.{u,v,w,n,l} e c))

end Lift

/-- A surjective polynomial presentation over (A'), with any type of variables. -/
structure Presentation (e : BaseExtension A' A) (B : Type w) [CommRing B] [Algebra A B]
    (σ : Type t) where
  map : MvPolynomial σ A' →+* B
  over : ∀ a : A', map (MvPolynomial.C a) = algebraMap A B (e.hom a)
  surjective : Function.Surjective map

namespace Presentation

variable {e} {σ : Type t} (p : Presentation e B σ)

/-- The polynomial presentation viewed as an algebra extension of (B). -/
def extension : Algebra.Extension.{max t u} ℤ B :=
  Algebra.Extension.ofSurjective p.map.toIntAlgHom p.surjective

/-- The underlying ring of the presentation is the multivariate polynomial ring. -/
def polynomialEquiv : MvPolynomial σ A' ≃+* p.extension.Ring := RingEquiv.refl _

/-- The presentation map on the underlying ring of the Mathlib extension. -/
abbrev ringHom : p.extension.Ring →+* B := algebraMap p.extension.Ring B

@[simp] theorem ringHom_polynomialEquiv (x : MvPolynomial σ A') :
    p.ringHom (p.polynomialEquiv x) = p.map x := rfl

/-- The ideal of relations (Q). -/
abbrev Q : Ideal p.extension.Ring := p.extension.ker

/-- The extended ideal (IP'). -/
def IP : Ideal p.extension.Ring :=
  Ideal.map (MvPolynomial.C : A' →+* p.extension.Ring) e.I

theorem IP_le_Q : p.IP ≤ p.Q := by
  change Ideal.map (MvPolynomial.C : A' →+* MvPolynomial σ A') e.I ≤ RingHom.ker p.map
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change p.map (MvPolynomial.C x) = 0
  rw [p.over, RingHom.mem_ker.mp hx, map_zero]

/-- The reduced polynomial ring (P'/IP'). -/
abbrev Bar := p.extension.Ring ⧸ p.IP

/-- The reduction map from (P') to (P'/IP'). -/
abbrev reduce : p.extension.Ring →+* p.Bar := Ideal.Quotient.mk p.IP

instance barAlgebra : Algebra A p.Bar :=
  (e.hom.liftOfSurjective e.surjective ⟨p.reduce.comp MvPolynomial.C, by
    intro a ha
    change Ideal.Quotient.mk p.IP (MvPolynomial.C a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem MvPolynomial.C ha)⟩).toAlgebra

@[simp] theorem algebraMap_bar_hom (a : A') :
    algebraMap A p.Bar (e.hom a) = p.reduce (MvPolynomial.C a) :=
  RingHom.liftOfSurjective_comp_apply e.hom e.surjective _ a

/-- The induced surjection (P̄ → B) over (A). -/
def barMap : p.Bar →ₐ[A] B where
  __ := Ideal.Quotient.lift p.IP p.map p.IP_le_Q
  commutes' a := by
    obtain ⟨a, rfl⟩ := e.surjective a
    rw [p.algebraMap_bar_hom]
    exact p.over a

@[simp] theorem barMap_reduce (x : p.extension.Ring) : p.barMap (p.reduce x) = p.ringHom x := rfl

theorem barMap_surjective : Function.Surjective p.barMap :=
  fun b => let ⟨x, hx⟩ := p.surjective b; ⟨p.reduce x, hx⟩

/-- The reduced presentation viewed as an algebra extension over (A). -/
def barExtension : Algebra.Extension A B :=
  Algebra.Extension.ofSurjective p.barMap p.barMap_surjective

/-- Reduction as a morphism between the two algebra extensions of B. -/
def reductionHom : p.extension.Hom p.barExtension where
  toRingHom := p.reduce
  toRingHom_algebraMap z := by
    change p.reduce (z : p.extension.Ring) = algebraMap A p.Bar (z : A)
    simp
  algebraMap_toRingHom x := p.barMap_reduce x

/-- The ideal of relations (J) in (P̄). -/
abbrev J : Ideal p.barExtension.Ring := p.barExtension.ker

/-- The conormal module (Q/Q^2) with its (B)-action. -/
abbrev Conormal := p.extension.Cotangent

/-- The conormal module (J/J^2) with its (B)-action. -/
abbrev BarConormal := p.barExtension.Cotangent

/-- The canonical map (IP' → Q/Q²), as a (P')-linear map. -/
def toConormal : p.IP →ₗ[p.extension.Ring] p.Conormal :=
  Algebra.Extension.Cotangent.mk.comp (Submodule.inclusion p.IP_le_Q)

/-- Its image (K), a submodule over (B) by surjectivity of (P' → B). -/
def K : Submodule B p.Conormal :=
  letI : RingHomSurjective (algebraMap p.extension.Ring B) := ⟨p.surjective⟩
  LinearMap.range
    (⟨p.toConormal.toAddMonoidHom, fun r x => by
      change p.toConormal (r • x) = algebraMap p.extension.Ring B r • p.toConormal x
      rw [map_smul, algebraMap_smul]⟩ :
      p.IP →ₛₗ[algebraMap p.extension.Ring B] p.Conormal)

theorem mem_K (x : p.Conormal) : x ∈ p.K ↔ ∃ y : p.IP, p.toConormal y = x := Iff.rfl

/-- The map onto (K) through which the prescribed map may factor. -/
def toK : p.IP →ₗ[p.extension.Ring] p.K where
  toFun x := ⟨p.toConormal x, (p.mem_K _).2 ⟨x, rfl⟩⟩
  map_add' x y := Subtype.ext (p.toConormal.map_add x y)
  map_smul' r x := Subtype.ext (p.toConormal.map_smul r x)

theorem toK_surjective : Function.Surjective p.toK := by
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := (p.mem_K x).mp hx
  exact ⟨y, rfl⟩

/-- Reduce the coefficients of the polynomial ring along the base surjection. -/
def coeffReduction : p.extension.Ring →+* MvPolynomial σ A := MvPolynomial.map e.hom

theorem coeffReduction_surjective : Function.Surjective p.coeffReduction :=
  MvPolynomial.map_surjective _ e.surjective

/-- The coefficient ideal consists precisely of the polynomials reducing to zero over (A). -/
theorem ker_coeffReduction :
    RingHom.ker p.coeffReduction = p.IP :=
  MvPolynomial.ker_map e.hom

/-- The quotient by the coefficient ideal is the polynomial ring over (A). -/
def barPolynomialEquiv : p.Bar ≃ₐ[A] MvPolynomial σ A :=
  AlgEquiv.ofRingEquiv
    (f := (Ideal.quotEquivOfEq p.ker_coeffReduction.symm).trans
      (p.coeffReduction.quotientKerEquivOfSurjective p.coeffReduction_surjective)) (by
    intro a
    obtain ⟨a, rfl⟩ := e.surjective a
    rw [p.algebraMap_bar_hom]
    change MvPolynomial.map e.hom (MvPolynomial.C a) = MvPolynomial.C (e.hom a)
    exact MvPolynomial.map_C _ _)

@[simp] theorem barPolynomialEquiv_reduce (x : p.extension.Ring) :
    p.barPolynomialEquiv (p.reduce x) = p.coeffReduction x := by
  change p.coeffReduction.quotientKerEquivOfSurjective p.coeffReduction_surjective
    (Ideal.quotEquivOfEq p.ker_coeffReduction.symm (p.reduce x)) = p.coeffReduction x
  rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- View (N) as a (P')-module through the presentation map. -/
abbrev targetModule (N : Type n) [AddCommGroup N] [Module B N] :
    Module p.extension.Ring N := Module.compHom N p.ringHom

theorem targetTower :
    letI := p.targetModule N
    IsScalarTower p.extension.Ring B N :=
  letI := p.targetModule N
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

private def coefficients : p.IP →+ ((σ →₀ ℕ) →₀ e.I) where
  toFun x := Finsupp.ofSupportFinite
    (fun i => ⟨x.val.coeff i, MvPolynomial.mem_map_C_iff.mp x.property i⟩)
    (x.val.support.finite_toSet.subset fun i hi =>
      MvPolynomial.mem_support_iff.mpr (fun hz => hi (Subtype.ext hz)))
  map_zero' := by ext i; rfl
  map_add' x y := by
    apply Finsupp.ext
    intro i
    exact Subtype.ext (map_add (MvPolynomial.coeffAddMonoidHom i) x.val y.val)

/-- A monomial whose coefficient belongs to the base kernel, viewed in IP'. -/
def idealMonomial (i : σ →₀ ℕ) (x : e.I) : p.IP :=
  ⟨MvPolynomial.monomial i x.val, by
    rw [← mul_one x.val, ← MvPolynomial.C_mul_monomial]
    exact p.IP.mul_mem_right _ (Ideal.mem_map_of_mem MvPolynomial.C x.property)⟩

private theorem coefficients_idealMonomial (i : σ →₀ ℕ) (x : e.I) :
    p.coefficients (p.idealMonomial i x) = Finsupp.single i x := by
  classical
  apply Finsupp.ext
  intro j
  apply Subtype.ext
  change (MvPolynomial.monomial i x.val).coeff j = ((Finsupp.single i x) j).val
  rw [MvPolynomial.coeff_monomial, Finsupp.single_apply]
  split <;> rfl

private theorem sum_idealMonomial (x : p.IP) :
    (∑ i ∈ x.val.support, p.idealMonomial i (p.coefficients x i)) = x := by
  classical
  apply Subtype.ext
  change p.IP.subtype (∑ i ∈ x.val.support, p.idealMonomial i (p.coefficients x i)) = x.val
  rw [map_sum]
  change (∑ i ∈ x.val.support, MvPolynomial.monomial i (x.val.coeff i)) = x.val
  exact (MvPolynomial.as_sum x.val).symm

variable (c : e.CoefficientMap (B := B) N)

private def prescribedAdd : p.IP →+ N :=
  (Finsupp.liftAddHom (fun i => (DistribSMul.toAddMonoidHom N
    (p.map (MvPolynomial.monomial i 1))).comp c.toAddMonoidHom)).comp p.coefficients

private theorem prescribedAdd_idealMonomial (i : σ →₀ ℕ) (x : e.I) :
    p.prescribedAdd c (p.idealMonomial i x) =
      p.map (MvPolynomial.monomial i 1) • c x := by
  simp only [prescribedAdd, AddMonoidHom.comp_apply, coefficients_idealMonomial,
    Finsupp.liftAddHom_apply_single, DistribSMul.toAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe]

private theorem prescribedAdd_smul_monomials (i j : σ →₀ ℕ) (a : A') (x : e.I) :
    p.prescribedAdd c (p.polynomialEquiv (MvPolynomial.monomial i a) • p.idealMonomial j x) =
      p.map (MvPolynomial.monomial i a) • p.prescribedAdd c (p.idealMonomial j x) := by
  have hmul : p.polynomialEquiv (MvPolynomial.monomial i a) • p.idealMonomial j x =
      p.idealMonomial (i + j) (a • x) := by
    apply Subtype.ext
    exact MvPolynomial.monomial_mul_monomial
  let : Module A N := Module.compHom N (algebraMap A B)
  have hc : c (a • x) = p.map (MvPolynomial.C a) • c x := by
    rw [p.over, ← e.hom_smul]
    exact c.map_smul _ _
  rw [hmul, prescribedAdd_idealMonomial, prescribedAdd_idealMonomial, hc,
    smul_smul, smul_smul, ← map_mul, ← map_mul,
    mul_comm _ (MvPolynomial.C a), MvPolynomial.C_mul_monomial,
    MvPolynomial.monomial_mul_monomial, mul_one]

/-- The induced (P')-linear map, given by summing the contributions (m(X)c(a_m)). -/
def prescribed :
    letI := p.targetModule N
    p.IP →ₗ[p.extension.Ring] N := by
  letI := p.targetModule N
  refine { __ := p.prescribedAdd c, map_smul' := ?_ }
  intro r x
  change p.prescribedAdd c (r • x) = p.ringHom r • p.prescribedAdd c x
  obtain ⟨r, rfl⟩ := p.polynomialEquiv.surjective r
  induction r using MvPolynomial.induction_on' with
  | monomial i a =>
    nth_rw 1 2 [← p.sum_idealMonomial x]
    simp only [Finset.smul_sum, map_sum, p.prescribedAdd_smul_monomials, p.ringHom_polynomialEquiv]
  | add r s hr hs =>
    rw [map_add p.polynomialEquiv, add_smul, map_add, hr, hs, map_add p.ringHom, add_smul]

/-- The constant polynomial of an element of the base kernel, viewed in IP'. -/
abbrev constant (i : e.I) : p.IP :=
  ⟨MvPolynomial.C i.val, Ideal.mem_map_of_mem MvPolynomial.C i.property⟩

theorem idealMonomial_eq_smul_constant (i : σ →₀ ℕ) (x : e.I) :
    p.idealMonomial i x = p.polynomialEquiv (MvPolynomial.monomial i 1) • p.constant x := by
  apply Subtype.ext
  change MvPolynomial.monomial i x.val = MvPolynomial.monomial i 1 * MvPolynomial.C x.val
  rw [mul_comm, MvPolynomial.C_mul_monomial, mul_one]

/-- The prescribed map is characterized by its values on constants from I. -/
def PrescribedUnique : Prop :=
  letI := p.targetModule N
  ∀ f : p.IP →ₗ[p.extension.Ring] N,
    (∀ i : e.I, f (p.constant i) = c i) → f = p.prescribed c

/-- The prescribed map sends the constant polynomial of (i ∈ I) to (c(i)). -/
theorem prescribed_C (i : e.I) :
    letI := p.targetModule N
    p.prescribed c (p.constant i) =
      c i := by
  let := p.targetModule N
  change p.prescribedAdd c (p.idealMonomial 0 i) = c i
  simp [prescribedAdd_idealMonomial]

end Presentation
end CommutativeAlgebraNotes.SquareZeroLift

namespace Specs.CommutativeAlgebraNotes.SquareZeroLiftDefinitions

open CommutativeAlgebraNotes.SquareZeroLift

section ExpectedTypes
set_option linter.checkUnivs false

def BaseExtensionType := type_of% @BaseExtension
def BaseExtensionValue := @BaseExtension
def baseKernelModuleType := type_of% @kernelModule
def CoefficientMapType := type_of% @BaseExtension.CoefficientMap
def LiftType := type_of% @Lift
def LiftValue := @Lift
def LiftIsoType := type_of% @Lift.Iso
def LiftIsoValue := @Lift.Iso
def LiftClassesType := type_of% @Lift.Classes
def PresentationType := type_of% @Presentation
def PresentationValue := @Presentation
def relationIdealType := type_of% @Presentation.Q
def coefficientIdealType := type_of% @Presentation.IP
def ReducedPolynomialRingType := type_of% @Presentation.Bar
def reducedPresentationMapType := type_of% @Presentation.barMap
def reducedRelationIdealType := type_of% @Presentation.J
def ConormalType := type_of% @Presentation.Conormal
def ReducedConormalType := type_of% @Presentation.BarConormal
def conormalImageType := type_of% @Presentation.K
def toConormalType := type_of% @Presentation.toConormal
def prescribedMapType := type_of% @Presentation.prescribed

end ExpectedTypes

universe u v w t n

def prescribedUniqueType : Prop :=
  ∀ {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
    [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
    (p : Presentation e B σ) (c : e.CoefficientMap (B := B) N), p.PrescribedUnique c

end Specs.CommutativeAlgebraNotes.SquareZeroLiftDefinitions
