import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.KrullLayers
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.FiniteFrobenius
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.ProfiniteIntegers.IntegerDensity
import Mathlib.RingTheory.Finiteness.Cardinality

/-! Arithmetic Frobenius on the chosen separable closure of a finite field. -/

namespace GaloisFormalization.GH.FiniteFrobenius

open KrullLayers
open AdvancedFieldTheory (finiteRootField finiteRootField_finite_galois
  frobeniusExponentCoordinates)
open AdvancedFieldTheory.ProfiniteIntegers (Zhat π ι)

universe u v

noncomputable section

variable (k : Type u) (S : Type v) [Field k] [Fintype k] [Field S] [Algebra k S]
  [IsSepClosure k S]

/-- The `q`-power automorphism on the specified closure. -/
def arithmeticFrobenius : AbsoluteGaloisGroup k S :=
  FiniteField.frobeniusAlgEquivOfAlgebraic k S

/-- The degree-`d` finite Galois layer of roots inside the specified closure. -/
def rootLayer (d : ℕ+) : FiniteGaloisIntermediateField k S where
  toIntermediateField := finiteRootField k S d
  finiteDimensional := (finiteRootField_finite_galois k S d d.pos).1
  isGalois := (finiteRootField_finite_galois k S d d.pos).2

/-- A residue acts on the layer by the corresponding power of Frobenius. -/
def exponentEquiv (d : ℕ+) : Multiplicative (ZMod (d : ℕ)) ≃* LayerGroup (rootLayer k S d) :=
  frobeniusExponentCoordinates k S d d.pos

/-- Restriction in the exponent coordinate at a positive modulus. -/
def reduction (d : ℕ+) : AbsoluteGaloisGroup k S →ₜ* Multiplicative (ZMod (d : ℕ)) where
  toMonoidHom := (exponentEquiv k S d).symm.toMonoidHom.comp
    (restrict (rootLayer k S d)).toMonoidHom
  continuous_toFun :=
    (continuous_of_discreteTopology (f := (exponentEquiv k S d).symm)).comp
      (restrict (rootLayer k S d)).continuous

@[simp]
theorem arithmeticFrobenius_apply (x : S) :
    arithmeticFrobenius k S x = x ^ Fintype.card k := rfl

theorem arithmeticFrobenius_orderOf : orderOf (arithmeticFrobenius k S) = 0 :=
  AdvancedFieldTheory.globalFrobenius_orderOf k S

theorem rootLayer_spec (d : ℕ+) :
    Module.finrank k (rootLayer k S d) = (d : ℕ) ∧
    ∀ x : S, x ∈ (rootLayer k S d).toIntermediateField ↔
      x ^ (Fintype.card k ^ (d : ℕ)) = x :=
  ⟨AdvancedFieldTheory.finiteRootField_finrank k S d d.pos,
    AdvancedFieldTheory.mem_finiteRootField k S d⟩

theorem restrict_frobenius_apply (E : FiniteGaloisIntermediateField k S) (x : E) :
    restrict E (arithmeticFrobenius k S) x = x ^ Fintype.card k := by
  apply Subtype.ext
  rw [restrict_apply, arithmeticFrobenius_apply]
  exact (SubmonoidClass.coe_pow x _).symm

private theorem restrict_frobenius_eq (E : FiniteGaloisIntermediateField k S) :
    restrict E (arithmeticFrobenius k S) = FiniteField.frobeniusAlgEquivOfAlgebraic k E :=
  AlgEquiv.ext (restrict_frobenius_apply k S E)

theorem restrict_frobenius_orderOf (E : FiniteGaloisIntermediateField k S) :
    orderOf (restrict E (arithmeticFrobenius k S)) = Module.finrank k E := by
  let : Finite E := Module.finite_of_finite k
  rw [restrict_frobenius_eq, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]

theorem restrict_frobenius_generates (E : FiniteGaloisIntermediateField k S) :
    Subgroup.zpowers (restrict E (arithmeticFrobenius k S)) = ⊤ := by
  let : Finite E := Module.finite_of_finite k
  rw [restrict_frobenius_eq]
  apply (Subgroup.zpowers _).eq_top_iff'.mpr
  intro σ
  obtain ⟨i, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k E).2 σ
  exact Subgroup.npow_mem_zpowers _ _

theorem frobenius_cyclic_dense :
    Dense (Subgroup.zpowers (arithmeticFrobenius k S) : Set (AbsoluteGaloisGroup k S)) :=
  AdvancedFieldTheory.frobenius_cyclic_dense k S

theorem exponentEquiv_intCast (d : ℕ+) (a : ℤ) :
    exponentEquiv k S d (Multiplicative.ofAdd (a : ZMod (d : ℕ))) =
      restrict (rootLayer k S d) (arithmeticFrobenius k S) ^ a := by
  rw [restrict_frobenius_eq]
  exact AdvancedFieldTheory.frobeniusExponentCoordinates_intCast k S d d.pos a

theorem reduction_restrict (d : ℕ+) (σ : AbsoluteGaloisGroup k S) :
    exponentEquiv k S d (reduction k S d σ) = restrict (rootLayer k S d) σ :=
  (exponentEquiv k S d).apply_symm_apply _

theorem reduction_surjective (d : ℕ+) : Function.Surjective (reduction k S d) :=
  (exponentEquiv k S d).symm.surjective.comp (restrict_surjective (rootLayer k S d))

theorem reduction_frobenius (d : ℕ+) :
    reduction k S d (arithmeticFrobenius k S) = Multiplicative.ofAdd (1 : ZMod (d : ℕ)) := by
  apply (exponentEquiv k S d).injective
  rw [reduction_restrict]
  simpa only [Int.cast_one, zpow_one] using (exponentEquiv_intCast k S d 1).symm

/-- In the profinite integer model, the degree-`d` residue is the
Frobenius exponent of restriction to the degree-`d` root field. -/
theorem absoluteGaloisEquiv :
    ∃! e : AbsoluteGaloisGroup k S ≃ₜ* Multiplicative Zhat,
      e (arithmeticFrobenius k S) = Multiplicative.ofAdd (ι 1) ∧
      ∀ (d : ℕ+) (σ : AbsoluteGaloisGroup k S),
        Multiplicative.ofAdd (π d (e σ).toAdd) = reduction k S d σ := by
  obtain ⟨coords, hcoords, e, ⟨he_action, he_frobenius⟩, _⟩ :=
    AdvancedFieldTheory.AbsoluteGalois.absoluteGaloisGroup k S
  have coords_agree (d : ℕ+) (r : Multiplicative (ZMod (d : ℕ))) :
      exponentEquiv k S d r = coords d r := by
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective r.toAdd
    have hr : Multiplicative.ofAdd (a : ZMod (d : ℕ)) = r :=
      congrArg Multiplicative.ofAdd ha
    rw [← hr, exponentEquiv_intCast, hcoords,
      restrict_frobenius_eq]
    rfl
  have he_reduction (d : ℕ+) (σ : AbsoluteGaloisGroup k S) :
      Multiplicative.ofAdd (π d (e σ).toAdd) = reduction k S d σ := by
    apply (exponentEquiv k S d).injective
    rw [reduction_restrict, coords_agree]
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    exact (he_action σ d x).trans (restrict_apply (rootLayer k S d) σ x).symm
  refine ⟨e, ⟨he_frobenius, he_reduction⟩, ?_⟩
  intro f hf
  apply ContinuousMulEquiv.ext
  intro σ
  apply Multiplicative.toAdd.injective
  apply AdvancedFieldTheory.ProfiniteIntegers.ext
  intro d
  apply Multiplicative.ofAdd.injective
  exact (hf.2 d σ).trans (he_reduction d σ).symm

end

end GaloisFormalization.GH.FiniteFrobenius
