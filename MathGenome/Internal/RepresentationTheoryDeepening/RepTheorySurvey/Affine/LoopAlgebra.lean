import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.LoopAlgebra
import Mathlib.Algebra.Lie.SemiDirect
import Mathlib.Algebra.Lie.TransferInstance
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CartanEqualsToral

/-! The central extension and the degree derivation for untwisted affine Lie algebras. -/

noncomputable section

open scoped TensorProduct LaurentPolynomial
open LieAlgebra LieModule
open Specs.RepTheorySurvey.Affine.LoopAlgebra

universe u

namespace RepTheorySurvey.Affine

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G]

abbrev loopVector := @loopVector_value
abbrev centralExtension := @centralExtension_value
abbrev centralCoordinates := @centralCoordinates_value
abbrev affineCoordinates := @affineCoordinates_value
abbrev centralLoopIncl := @centralLoopIncl_value
abbrev centralLineIncl := @centralLineIncl_value
abbrev loopDegree := @loopDegree_value

/-- The two constructions of a homogeneous loop agree. -/
@[simp] theorem loopVector_laurent (m : ℤ) (x : G) :
    loopAlgebraEquivLaurent ℂ G (loopVector m x) = LaurentPolynomial.T m ⊗ₜ[ℂ] x := rfl

@[simp] theorem loopVector_coefficients (m : ℤ) (x : G) :
    LoopAlgebra.toFinsupp ℂ ℤ G (loopVector m x) = Finsupp.single m x :=
  LoopAlgebra.toFinsupp_single_tmul ℂ ℤ G m x

@[simp] theorem loopVector_bracket (m n : ℤ) (x y : G) :
    ⁅loopVector m x, loopVector n y⁆ = loopVector (m + n) ⁅x, y⁆ := by
  change ⁅AddMonoidAlgebra.single m (1 : ℂ) ⊗ₜ[ℂ] x,
    AddMonoidAlgebra.single n (1 : ℂ) ⊗ₜ[ℂ] y⁆ = _
  rw [LieAlgebra.ExtendScalars.bracket_tmul, AddMonoidAlgebra.single_mul_single, one_mul]
  rfl

@[simp] theorem loopDegree_loopVector (m : ℤ) (x : G) :
    loopDegree G (loopVector m x) = (m : ℂ) • loopVector m x := by
  simp only [loopDegree, loopDegree_value, LinearMap.comp_apply, LinearEquiv.coe_coe,
    loopVector_coefficients, Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply]
  rw [map_smul, LoopAlgebra.toFinsupp_symm_single]
  rfl

/-- Evaluation of the signed cocycle on homogeneous loops. -/
private theorem cocycle_loopVector (B : InvariantForm G) (m n : ℤ) (x y : G) :
    (((loopCocycle B).val (loopVector m x) (loopVector n y) : ScalarLine G) : ℂ) =
      if m = -n then (m : ℂ) * B.form x y else 0 := by
  change (((-1 : ℂ) • LoopAlgebra.twoCochainOfBilinear ℂ ℤ G B.form B.symmetric)
    (loopVector m x) (loopVector n y) : ScalarLine G) = _
  rw [Cohomology.smul_apply_apply, LoopAlgebra.twoCochainOfBilinear_apply_apply]
  change (-1 : ℂ) • (LoopAlgebra.residuePairing ℂ ℤ G B.form (loopVector m x) (loopVector n y)) = _
  rw [neg_one_smul]
  rw [LoopAlgebra.residuePairing_apply_apply, loopVector_coefficients, loopVector_coefficients,
    Finsupp.sum_single_index (by simp)]
  by_cases h : m = -n
  · subst m
    simp [zsmul_eq_mul]
  · simp [h]

/-- Central coordinates of the bracket of any two lifts. -/
theorem centralBracket_coordinates (B : InvariantForm G) (x y : LoopCentral B) :
    centralCoordinates B ⁅x, y⁆ =
      (⁅(centralCoordinates B x).1, (centralCoordinates B y).1⁆,
        ((loopCocycle B).val (centralCoordinates B x).1 (centralCoordinates B y).1 : ℂ)) := by
  change (ofProd (loopCocycle B)).symm ⁅x, y⁆ = _
  rw [bracket_ofTwoCocycle, Equiv.symm_apply_apply]
  simp only [trivial_lie_zero, add_zero, sub_zero]
  rfl

@[simp] theorem centralLoopIncl_coordinates (B : InvariantForm G) (f : Loop G) :
    centralCoordinates B (centralLoopIncl B f) = (f, 0) :=
  (centralCoordinates B).apply_symm_apply (f, 0)

@[simp] theorem centralExtension_incl_coordinates (B : InvariantForm G) (k : ScalarLine G) :
    centralCoordinates B ((centralExtension B).incl k) = (0, (k : ℂ)) := rfl

@[simp] theorem centralExtension_proj_coordinates (B : InvariantForm G) (x : LoopCentral B) :
    (centralExtension B).proj x = (centralCoordinates B x).1 := rfl

@[simp] theorem centralLineIncl_bracket (B : InvariantForm G)
    (k : ℂ) (x : LoopCentral B) :
    ⁅centralLineIncl B k, x⁆ = 0 := by
  apply (centralCoordinates B).injective
  rw [centralBracket_coordinates]
  simp [centralLineIncl_value]
  apply Prod.ext
  · change ⁅(0 : Loop G), (centralCoordinates B x).1⁆ = (0 : Loop G)
    exact zero_lie ((centralCoordinates B x).1)
  · rfl

/-- The kernel of the loop projection lies in the center of the extension. -/
theorem centralExtension_central (B : InvariantForm G) (k : ScalarLine G) (x : LoopCentral B) :
    let z : LoopCentral B := (centralExtension B).incl k
    ⁅z, x⁆ = 0 :=
  centralLineIncl_bracket B (k : ℂ) x

theorem centralBracket (B : InvariantForm G) (m n : ℤ) (x y : G) :
    ⁅centralLoopIncl B (loopVector m x), centralLoopIncl B (loopVector n y)⁆ =
      centralLoopIncl B (loopVector (m + n) ⁅x, y⁆) +
        (if m = -n then (m : ℂ) * B.form x y else 0) •
          centralLineIncl B 1 := by
  apply (centralCoordinates B).injective
  rw [centralBracket_coordinates, centralLoopIncl_coordinates, centralLoopIncl_coordinates]
  simp only [loopVector_bracket, cocycle_loopVector, map_add, map_smul, centralLoopIncl_coordinates,
    centralLineIncl_value, LinearEquiv.apply_symm_apply, Prod.smul_mk, smul_zero, smul_eq_mul,
    mul_one, Prod.mk_add_mk, add_zero, zero_add]
  rfl

private theorem loop_induction {P : Loop G → Prop} (f : Loop G)
    (zero : P 0) (add : ∀ x y, P x → P y → P (x + y))
    (single : ∀ m x, P (loopVector m x)) : P f := by
  let e := LoopAlgebra.toFinsupp ℂ ℤ G
  have h (p : ℤ →₀ G) : P (e.symm p) := by
    induction p using Finsupp.induction_linear with
    | zero => simpa only [map_zero] using zero
    | add p q hp hq => simpa only [map_add] using add _ _ hp hq
    | single m x =>
        rw [show e.symm (Finsupp.single m x) = loopVector m x from
          LoopAlgebra.toFinsupp_symm_single ℂ ℤ G m x]
        exact single m x
  simpa only [LinearEquiv.symm_apply_apply, e] using h (e f)

@[simp] theorem degreeCentral_coordinates (B : InvariantForm G) (x : LoopCentral B) :
    centralCoordinates B (degreeCentral_value B x) = (loopDegree G (centralCoordinates B x).1, 0) :=
  centralLoopIncl_coordinates B _

@[simp] theorem degreeCentral_incl (B : InvariantForm G) (k : ℂ) :
    degreeCentral_value B (centralLineIncl_value B k) = 0 := by
  apply (centralCoordinates B).injective
  simp [centralLineIncl_value]

@[simp] theorem degreeCentral_loopIncl (B : InvariantForm G) (f : Loop G) :
    degreeCentral_value B (centralLoopIncl B f) = centralLoopIncl B (loopDegree G f) := by
  change centralLoopIncl B (loopDegree G ((centralExtension B).proj (centralLoopIncl B f))) = _
  simp

private theorem degreeCentral_leibniz (B : InvariantForm G) (x y : LoopCentral B) :
    degreeCentral_value B ⁅x, y⁆ =
      ⁅degreeCentral_value B x, y⁆ + ⁅x, degreeCentral_value B y⁆ := by
  suffices h : ∀ f g : Loop G,
      degreeCentral_value B ⁅centralLoopIncl B f, centralLoopIncl B g⁆ =
        ⁅degreeCentral_value B (centralLoopIncl B f), centralLoopIncl B g⁆ +
        ⁅centralLoopIncl B f, degreeCentral_value B (centralLoopIncl B g)⁆ by
    apply (centralCoordinates B).injective
    have eq := congrArg (centralCoordinates B) (h (centralCoordinates B x).1 (centralCoordinates B y).1)
    simpa only [map_add, centralBracket_coordinates, degreeCentral_coordinates,
      centralLoopIncl_coordinates] using eq
  intro f g
  induction f using loop_induction with
  | zero => simp
  | add a b ha hb =>
      simp only [map_add, add_lie, ha, hb]
      abel
  | single m x =>
      induction g using loop_induction with
      | zero => simp
      | add a b ha hb =>
          simp only [map_add, lie_add, ha, hb]
          abel
      | single n y =>
          simp only [degreeCentral_loopIncl, loopDegree_loopVector, map_smul, smul_lie, lie_smul,
            ← add_smul, centralBracket, map_add, degreeCentral_incl, smul_zero, add_zero]
          rw [smul_add, smul_smul, ← Int.cast_add]
          by_cases h : m = -n
          · have hz : m + n = 0 := by omega
            simp [hz]
          · simp [h]

/-- The degree derivation on the central extension vanishes on the central line. -/
def degreeDerivation (B : InvariantForm G) : LieDerivation ℂ (LoopCentral B) (LoopCentral B) where
  __ := degreeCentral_value B
  leibniz' x y := by rw [degreeCentral_leibniz, sub_eq_add_neg, lie_skew, add_comm]

def degreeCentral (B : InvariantForm G) : LoopCentral B →ₗ[ℂ] LoopCentral B :=
  (degreeDerivation B).toLinearMap

abbrev scalarCoordinates (G : Type u) [LieRing G] [LieAlgebra ℂ G] :=
  TrivialLieModule.equiv ℂ (Loop G) ℂ

/-- The abelian degree line acts by scalar multiples of the degree derivation. -/
private def degreeAction (B : InvariantForm G) :
    ScalarLine G →ₗ⁅ℂ⁆ LieDerivation ℂ (LoopCentral B) (LoopCentral B) where
  toFun a := scalarCoordinates G a • degreeDerivation B
  map_add' a b := by rw [map_add, add_smul]
  map_smul' r a := by rw [map_smul, smul_assoc, RingHom.id_apply]
  map_lie' {a b} := by
    change (0 : ℂ) • degreeDerivation B =
      ⁅scalarCoordinates G a • degreeDerivation B, scalarCoordinates G b • degreeDerivation B⁆
    simp

private def toSemidirect (B : InvariantForm G) :
    AffineAlgebra B ≃ₗ[ℂ] (LoopCentral B ⋊⁅degreeAction B⁆ ScalarLine G) :=
  (SemiDirectSum.toProdl (degreeAction B)).symm

instance (B : InvariantForm G) : LieRing (AffineAlgebra B) :=
  (toSemidirect B).toAddEquiv.lieRing

instance (B : InvariantForm G) : LieAlgebra ℂ (AffineAlgebra B) :=
  (toSemidirect B).lieAlgebra

/-- The affine bracket with respect to the loop, central and degree coordinates. -/
def affineBracket (B : InvariantForm G) (x y : AffineAlgebra B) : AffineAlgebra B :=
  ⁅x, y⁆

theorem affineBracket_eq (B : InvariantForm G) (x y : AffineAlgebra B) :
    ⁅x, y⁆ = affineBracket_value B x y := rfl

theorem affineStructure (B : InvariantForm G) :
    ∃ lieRing : LieRing (AffineAlgebra B),
      ∃ lieAlgebra : @LieAlgebra ℂ (AffineAlgebra B) _ lieRing,
        lieRing.toAddCommGroup = (inferInstance : AddCommGroup (AffineAlgebra B)) ∧
          HEq lieAlgebra.toModule (inferInstance : Module ℂ (AffineAlgebra B)) ∧
          ∀ x y, lieRing.toBracket.bracket x y = affineBracket_value B x y :=
  ⟨inferInstance, inferInstance, rfl, HEq.rfl, affineBracket_eq B⟩

/-- The Lie embedding of the loop-central extension into the affine algebra. -/
def centralIncl (B : InvariantForm G) : LoopCentral B →ₗ⁅ℂ⁆ AffineAlgebra B :=
  { centralInclLinear_value B with
    map_lie' := by
      intro x y
      change (⁅x, y⁆, (0 : ℂ)) =
        (⁅x, y⁆ + (0 : ℂ) • degreeCentral_value B y - (0 : ℂ) • degreeCentral_value B x, 0)
      simp }

theorem centralIncl_injective (B : InvariantForm G) : Function.Injective (centralIncl B) :=
  fun _ _ h ↦ congrArg Prod.fst h

def centralInclLinear (B : InvariantForm G) : LoopCentral B →ₗ[ℂ] AffineAlgebra B :=
  (centralIncl B).toLinearMap

def loopIncl (B : InvariantForm G) : Loop G →ₗ[ℂ] AffineAlgebra B :=
  (centralInclLinear B).comp (centralLoopIncl B)

theorem centralIncl_range (B : InvariantForm G) (x : AffineAlgebra B) :
    (∃ y : LoopCentral B, centralIncl B y = x) ↔ (affineCoordinates B x).2 = 0 := by
  rcases (show LoopCentral B × ℂ from x) with ⟨y, a⟩
  change (∃ z : LoopCentral B, (z, (0 : ℂ)) = (y, a)) ↔ a = 0
  constructor
  · rintro ⟨z, e⟩
    exact (congrArg Prod.snd e).symm
  · rintro rfl
    exact ⟨y, rfl⟩

/-- The Lie embedding of the one-dimensional degree algebra. -/
def degreeIncl (B : InvariantForm G) : ScalarLine G →ₗ⁅ℂ⁆ AffineAlgebra B where
  __ := degreeIncl_value B
  map_lie' {a b} := by
    change ((0 : LoopCentral B), (0 : ℂ)) =
      (⁅(0 : LoopCentral B), 0⁆ + scalarCoordinates G a • degreeCentral_value B 0 -
        scalarCoordinates G b • degreeCentral_value B 0, (0 : ℂ))
    simp

def degreeInclLinear (B : InvariantForm G) : ScalarLine G →ₗ[ℂ] AffineAlgebra B :=
  (degreeIncl B).toLinearMap

abbrev K := @K_value
abbrev d := @d_value
abbrev homogeneous := @homogeneous_value

theorem homogeneousBracket (B : InvariantForm G) (m n : ℤ) (x y : G) :
    ⁅homogeneous B m x, homogeneous B n y⁆ =
      homogeneous B (m + n) ⁅x, y⁆ +
        (if m = -n then (m : ℂ) * B.form x y else 0) • K B := by
  change ((⁅centralLoopIncl B (loopVector m x), centralLoopIncl B (loopVector n y)⁆ +
    (0 : ℂ) • degreeCentral_value B (centralLoopIncl B (loopVector n y)) -
    (0 : ℂ) • degreeCentral_value B (centralLoopIncl B (loopVector m x)), 0) :
      LoopCentral B × ℂ) = _
  rw [zero_smul, zero_smul, add_zero, sub_zero, centralBracket]
  change _ = ((centralLoopIncl B (loopVector (m + n) ⁅x, y⁆), (0 : ℂ)) +
    (if m = -n then (m : ℂ) * B.form x y else 0) • (centralLineIncl_value B 1, (0 : ℂ)))
  simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]

theorem degreeBracket (B : InvariantForm G) (m : ℤ) (x : G) :
    ⁅d B, homogeneous B m x⁆ = (m : ℂ) • homogeneous B m x := by
  change ((⁅(0 : LoopCentral B), centralLoopIncl B (loopVector m x)⁆ +
    (1 : ℂ) • degreeCentral_value B (centralLoopIncl B (loopVector m x)) -
    (0 : ℂ) • degreeCentral_value B 0, 0) : LoopCentral B × ℂ) = _
  simp only [zero_lie, one_smul, zero_smul, sub_zero, zero_add, degreeCentral_loopIncl,
    loopDegree_loopVector, map_smul]
  change _ = (m : ℂ) • (centralLoopIncl B (loopVector m x), (0 : ℂ))
  rw [Prod.smul_mk, smul_zero]

theorem centralGenerator (B : InvariantForm G) (x : AffineAlgebra B) : ⁅K B, x⁆ = 0 := by
  let p : LoopCentral B × ℂ := x
  change ((⁅(centralLineIncl_value B 1), p.1⁆ +
    (0 : ℂ) • degreeCentral_value B p.1 -
    p.2 • degreeCentral_value B (centralLineIncl_value B 1), 0) :
      LoopCentral B × ℂ) = (0, 0)
  simp

/-- The copy of the original Lie algebra consisting of constant loops. -/
def constantIncl (B : InvariantForm G) : G →ₗ⁅ℂ⁆ AffineAlgebra B where
  __ := (loopIncl B).comp (loopVector 0)
  map_lie' {x y} := by
    change homogeneous B 0 ⁅x, y⁆ = ⁅homogeneous B 0 x, homogeneous B 0 y⁆
    rw [homogeneousBracket]
    simp

def constantInclLinear (B : InvariantForm G) : G →ₗ[ℂ] AffineAlgebra B :=
  (constantIncl B).toLinearMap

@[simp] theorem loopIncl_loopVector (B : InvariantForm G) (m : ℤ) (x : G) :
    loopIncl B (loopVector m x) = homogeneous B m x := rfl

@[simp] theorem centralIncl_centralGenerator (B : InvariantForm G) :
    centralIncl B ((centralExtension B).incl ((scalarCoordinates G).symm 1)) = K B := rfl

@[simp] theorem degreeIncl_degreeGenerator (B : InvariantForm G) :
    degreeIncl B ((scalarCoordinates G).symm 1) = d B := rfl

theorem coordinateEmbeddings (B : InvariantForm G) :
    Function.Injective (centralLoopIncl B) ∧
    Function.Injective (centralInclLinear B) ∧
    Function.Injective (loopIncl B) ∧
    Function.Injective (degreeInclLinear B) ∧
    Function.Injective (constantInclLinear B) ∧
    (∀ f, affineCoordinates B (loopIncl B f) = ((f, 0), 0)) ∧
    (∀ k : ScalarLine G, affineCoordinates B (centralIncl B ((centralExtension B).incl k)) =
      ((0, (k : ℂ)), 0)) ∧
    (∀ k : ScalarLine G, affineCoordinates B (degreeIncl B k) = ((0, 0), (k : ℂ))) := by
  have h : Function.Injective (centralLoopIncl B) := by
    intro f g e
    exact congrArg Prod.fst ((centralLoopIncl_coordinates B f).symm.trans <|
      (congrArg (centralCoordinates B) e).trans (centralLoopIncl_coordinates B g))
  have hloop := (centralIncl_injective B).comp h
  have hzero : Function.Injective (loopVector (G := G) 0) := by
    intro x y e
    have hc := congrArg (LoopAlgebra.toFinsupp ℂ ℤ G) e
    rw [loopVector_coefficients, loopVector_coefficients] at hc
    exact Finsupp.single_injective _ hc
  exact ⟨h, centralIncl_injective B, hloop, fun _ _ e ↦ congrArg Prod.snd e, hloop.comp hzero,
    fun f ↦ congrArg (fun p : Loop G × ℂ ↦ (p, (0 : ℂ))) (centralLoopIncl_coordinates B f),
    fun _ ↦ rfl, fun _ ↦ rfl⟩

private theorem cartanMaximalToral [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G]
    (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra] :
    LieAlgebrasAndRepresentations.IsMaximalToral H := by
  open LieAlgebrasAndRepresentations in
  exact (isCartan_iff_maximal_toral (show LieAlgebrasAndRepresentations.IsSemisimple ℂ G from LieAlgebra.radical_eq_bot) H).mp
    ((isCartan_iff_isCartanSubalgebra H).mpr inferInstance)

theorem cartanAbelian [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G]
    (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra] : IsLieAbelian H :=
  (cartanMaximalToral H).1.1

open LieAlgebrasAndRepresentations (mem_rootSpace rootSpace_zero iSup_rootSpace_eq_top) in
theorem cartanNondegenerate [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G]
    (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra] (B : InvariantForm G)
    (hB : B.form.Nondegenerate) : (B.form.restrict H.toSubmodule).Nondegenerate := by
  have hH := cartanMaximalToral H
  have hzero : LieAlgebrasAndRepresentations.rootSpace H 0 = H.toSubmodule :=
    rootSpace_zero (show LieAlgebrasAndRepresentations.IsSemisimple ℂ G from
      LieAlgebra.radical_eq_bot) H hH
  have hleft (x : H) (hx : ∀ y : H, B.form (x : G) (y : G) = 0) : x = 0 := by
    apply Subtype.ext
    change (x : G) = 0
    apply hB.1
    intro y
    have hy : y ∈ ⨆ α, LieAlgebrasAndRepresentations.rootSpace H α := by
      rw [iSup_rootSpace_eq_top H hH.1]
      trivial
    refine Submodule.iSup_induction (LieAlgebrasAndRepresentations.rootSpace H) (motive := fun z ↦ B.form (x : G) z = 0)
      hy (fun α z hz ↦ ?_) (by simp) (fun a b ha hb ↦ by simp [ha, hb])
    by_cases hα : α = 0
    · subst α
      rw [hzero] at hz
      exact hx ⟨z, hz⟩
    · obtain ⟨a, ha⟩ : ∃ a : H, α a ≠ 0 := by
        by_contra! h
        exact hα (LinearMap.ext h)
      have hcomm : ⁅(a : G), (x : G)⁆ = 0 := by
        let : IsLieAbelian H := hH.1.1
        exact congrArg Subtype.val (trivial_lie_zero H H a x)
      have h := B.invariant (a : G) (x : G) z
      rw [hcomm, (mem_rootSpace H α z).mp hz a] at h
      simp only [map_zero, LinearMap.zero_apply, map_smul, smul_eq_mul] at h
      exact (mul_eq_zero.mp (neg_eq_zero.mp h.symm)).resolve_left ha
  exact ⟨hleft, fun x hx ↦ hleft x fun y ↦ (B.symmetric.eq _ _).trans (hx y)⟩

theorem cartanNontrivial [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G]
    (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra] : Nontrivial H := by
  have : Nontrivial G := by
    by_contra! h
    exact LieAlgebra.IsSimple.non_abelian ℂ (⟨fun x y ↦ Subsingleton.elim _ _⟩ : IsLieAbelian G)
  infer_instance

/-- The representative formulation of normalization agrees with the inverse
bilinear form on the dual of the fixed Cartan. -/
theorem normalizedRootLengths [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G]
    (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra] (B : InvariantForm G)
    (hH : (B.form.restrict H.toSubmodule).Nondegenerate) :
    B.IsNormalized H ↔ B.form.Nondegenerate ∧
      ∀ α : LieAlgebrasAndRepresentations.rootSet H, IsLongRoot α →
        α.val (((B.form.restrict H.toSubmodule).toDual hH).symm α.val) = 2 := by
  let e := (B.form.restrict H.toSubmodule).toDual hH
  constructor
  · rintro ⟨hB, h⟩
    refine ⟨hB, fun α hα ↦ ?_⟩
    obtain ⟨a, ha, ha₂⟩ := h α hα
    have ea : e a = α.val := LinearMap.ext ha
    change α.val (e.symm α.val) = 2
    have he : e.symm α.val = a := by rw [← ea, e.symm_apply_apply]
    exact he ▸ ha₂
  · rintro ⟨hB, h⟩
    refine ⟨hB, fun α hα ↦ ⟨e.symm α.val, fun y ↦ ?_, h α hα⟩⟩
    change (B.form.restrict H.toSubmodule) (e.symm α.val) y = α.val y
    exact LinearMap.BilinForm.apply_toDual_symm_apply α.val y

end RepTheorySurvey.Affine
