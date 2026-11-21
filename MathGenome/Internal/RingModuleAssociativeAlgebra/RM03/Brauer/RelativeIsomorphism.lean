import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.RelativeIsomorphism
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ScalarInjective
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Algebra.Group.Pi.Units
import Batteries.Tactic.OpenPrivate

/-! The twisted regular representation gives the preimage of a scalar cocycle. -/

open scoped TensorProduct MatrixGroups

namespace RM03.Brauer.RelativeIsomorphism

open Matrix groupCohomology
open ProjectiveClassification ScalarObstruction ScalarInjective SemilinearDescent
open Specs.RM03.Brauer.ScalarObstruction

universe u v w

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

theorem normalized_representative :
    Specs.RM03.Brauer.RelativeIsomorphism.NormalizedRepresentative.{u,v} := by
  intro k K _ _ _ a
  obtain ⟨c, rfl⟩ := cocycleClass_surjective a
  let b : Gal(K/k) → Kˣ := fun _ => (c.val (1, 1))⁻¹
  let d := coboundary k K b * c
  have hc : IsMulCocycle₂ c.val := c.property
  have hb : ∀ g h, (coboundary k K b).val (g, h) = g • (c.val (1, 1))⁻¹ := by
    intro g h
    change g • (c.val (1, 1))⁻¹ / (c.val (1, 1))⁻¹ * (c.val (1, 1))⁻¹ = _
    rw [div_mul_cancel]
  refine ⟨d, ?_, fun g => ?_⟩
  · change cocycleClass k K (coboundary k K b * c) = cocycleClass k K c
    rw [map_mul, show cocycleClass k K (coboundary k K b) = 1 from
      (QuotientGroup.eq_one_iff _).mpr ⟨b, rfl⟩]
    exact one_mul (cocycleClass k K c)
  · change (coboundary k K b).val (1, g) * c.val (1, g) = 1 ∧
      (coboundary k K b).val (g, 1) * c.val (g, 1) = 1
    simp only [hb, map_one_fst_of_isMulCocycle₂ hc g, map_one_snd_of_isMulCocycle₂ hc g,
      one_smul, smul_inv', inv_mul_cancel, and_self]

section Matrices

variable {n : ℕ} (index : Fin n ≃ Gal(K/k)) (c : ScalarCocycle k K)

private def leftPerm (g : Gal(K/k)) : Equiv.Perm (Fin n) :=
  (index.trans (Equiv.mulLeft g)).trans index.symm

private noncomputable def regularLift (g : Gal(K/k)) : GL (Fin n) K :=
  (Matrix.permMatrixHom (R := K)).toHomUnits (leftPerm index g) *
    Units.map (Matrix.diagonalRingHom (Fin n) K).toMonoidHom
      (MulEquiv.piUnits.symm (fun j => c.val (g, index j)))

private theorem regularLift_apply (g : Gal(K/k)) (i j : Fin n) :
    regularLift index c g i j =
      if i = leftPerm index g j then (c.val (g, index j) : K) else 0 := by
  classical
  change (((leftPerm index g)⁻¹.permMatrix K) *
    diagonal (fun j => (c.val (g, index j) : K))) i j = _
  rw [mul_diagonal]
  change (if j ∈ ((leftPerm index g)⁻¹).toPEquiv i then (1 : K) else 0) *
    (c.val (g, index j) : K) = _
  simp [Equiv.toPEquiv_apply, Equiv.eq_symm_apply, eq_comm]

private theorem leftPerm_apply (g : Gal(K/k)) (j : Fin n) :
    index (leftPerm index g j) = g * index j :=
  index.apply_symm_apply _

private theorem regularLift_mul (g h : Gal(K/k)) :
    regularLift index c g * mapGL g (regularLift index c h) =
      GeneralLinearGroup.scalar (Fin n) (c.val (g, h)) * regularLift index c (g * h) := by
  classical
  apply GeneralLinearGroup.ext
  intro i j
  change ((regularLift index c g : Mat K n) *
      (regularLift index c h : Mat K n).map g) i j =
    (Matrix.scalar (Fin n) (c.val (g, h) : K) * (regularLift index c (g * h) : Mat K n)) i j
  rw [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_mul]
  simp only [Matrix.map_apply, regularLift_apply, apply_ite, map_zero, mul_zero]
  rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _)]
  have hperm : leftPerm index g (leftPerm index h j) = leftPerm index (g * h) j := by
    apply index.injective
    simp only [leftPerm_apply, mul_assoc]
  rw [hperm, leftPerm_apply]
  have hc : IsMulCocycle₂ c.val := c.property
  have heq := congrArg (fun a : Kˣ => (a : K)) (hc g h (index j))
  change (c.val (g * h, index j) : K) * (c.val (g, h) : K) =
    g (c.val (h, index j) : K) * (c.val (g, h * index j) : K) at heq
  split_ifs <;> simp_all [mul_comm]

end Matrices

theorem regular_descent : Specs.RM03.Brauer.RelativeIsomorphism.RegularDescent.{u,v} := by
  intro k K _ _ _ _ _ c
  classical
  let : Fintype Gal(K/k) := Fintype.ofFinite _
  let n := Fintype.card Gal(K/k)
  let index : Fin n ≃ Gal(K/k) := (Fintype.equivFin _).symm
  have hn : 0 < n := Fintype.card_pos
  let G := regularLift index c
  have hmul := regularLift_mul index c
  let p : Cocycle k K n :=
    ⟨fun g => ProjGenLinGroup.mk (G g), fun g h => by
      have he := congrArg ProjGenLinGroup.mk (hmul g h)
      simpa only [map_mul, mk_mapGL, ProjGenLinGroup.mk_scalar, one_mul] using he.symm⟩
  have hG : IsLift p G := fun _ => rfl
  have hc : RecordsDefect G c := by
    intro g h
    rw [hmul, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨e, he⟩ := action_correspondence (k := k) (K := K) hn
  let ρ := e p
  have hp : Implements ρ p := (he p ρ).mpr rfl
  obtain ⟨hCSA, hdeg, s, hρ, hs⟩ := descended_form hn p ρ hp
  refine ⟨n, index, hn, G, p, ρ, ?_, hG, hc, hp, hCSA, hdeg, s, hρ, hs⟩
  intro g i j
  exact regularLift_apply index c g i j

open private splittingOfEquiv presents_of_equiv from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ScalarObstruction
open private csa_eq_of_toAlgCat_eq from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.BaseChange

private theorem centralSimple_ulift {A : Type v} [Ring A] [Algebra k A]
    (hA : CSA.IsCentralSimple k A) : CSA.IsCentralSimple k (ULift.{w} A) := by
  let e : ULift.{w} A ≃ₐ[k] A := ULift.algEquiv
  let : IsSimpleRing A := hA.1
  let : Algebra.IsCentral k A := hA.2.1
  let : FiniteDimensional k A := hA.2.2
  refine ⟨?_, ?_, FiniteDimensional.of_injective e.toLinearMap e.injective⟩
  · apply (IsSimpleRing.iff_injective_ringHom _).mpr
    intro S _ _ f
    have hf := (f.comp e.symm.toRingHom).injective
    exact fun a b hab => e.injective (hf (by simpa using hab))
  · refine ⟨fun x hx => ?_⟩
    obtain ⟨a, ha⟩ := hA.2.1.out ((MulEquivClass.apply_mem_center_iff e).mpr hx)
    exact Algebra.mem_bot.mpr ⟨a, e.injective (by simpa using ha)⟩

variable [FiniteDimensional k K] [IsGalois k K]

private theorem surjective_of_formula
    [AddCommGroup (BrauerGroup.{u, max u v w} k)] [AddCommGroup (BrauerGroup.{v, max u v w} K)]
    (f : BrauerGroup.{u, max u v w} k →+ BrauerGroup.{v, max u v w} K)
    (hSplit : ∀ A : _root_.CSA.{u, max u v w} k,
      classOf A ∈ relativeSubgroup f ↔ CSA.Splits k K A)
    (φ : relativeSubgroup f →+ Additive (H2 k K)) (hφ : IsObstructionHom.{u,v,w} f φ) :
    Function.Surjective φ := by
  intro a
  obtain ⟨c, hclass, _⟩ := normalized_representative a.toMul
  obtain ⟨n, _, hn, G, p, ρ, _, hG, hc, hp, hCSA, _, s, hρ, _⟩ := regular_descent c
  let A : _root_.CSA.{u, max u v w} k := CSA.toCSA (centralSimple_ulift.{u,v,max u w} hCSA)
  let e : (A : Type (max u v w)) ≃ₐ[k] ρ.fixedSubalgebra := ULift.algEquiv
  let t := splittingOfEquiv e s
  have ht : Presents t G := presents_of_equiv hn e ⟨ρ, p, hρ, hp, hG⟩
  have hA : classOf A ∈ relativeSubgroup f := (hSplit A).mpr ⟨n, hn, ⟨t⟩⟩
  exact ⟨⟨classOf A, hA⟩, (hφ A hA hn t G ht c hc).trans (congrArg Additive.ofMul hclass)⟩

/-- Surjectivity and the group isomorphism for the homomorphism with the
prescribed scalar-defect formula. -/
theorem scalar_obstruction_isomorphism :
    Specs.RM03.Brauer.RelativeIsomorphism.ScalarObstructionIsomorphism.{u,v,w} := by
  intro k K _ _ _ _ _ gk gK hk hK
  let _ := gk
  let _ := gK
  intro f hf φ hφ
  have hSplit (A : _root_.CSA.{u, max u v w} k) :
      classOf A ∈ relativeSubgroup f ↔ CSA.Splits k K A := by
    obtain ⟨B, hB, hF⟩ := hf A
    have he : B = baseChangeCSA k K A := csa_eq_of_toAlgCat_eq hB
    change f (Specs.RM03.Brauer.classOf A) = 0 ↔ _
    rw [hF, he]
    exact hK.2.2.2 (baseChangeCSA k K A)
  have hs := surjective_of_formula f hSplit φ hφ
  have hi := obstruction_injective k K gk gK hk hK f hf φ hφ
  exact ⟨hs, AddEquiv.ofBijective φ ⟨hi, hs⟩, rfl⟩

/-- Surjectivity for the canonical scalar obstruction. -/
theorem obstruction_surjective : Function.Surjective (obstruction.{u,v,w} k K) :=
  surjective_of_formula (baseChange.{u,v,w} k K)
    (classOf_mem_relativeBrauerGroup_iff k K) _ (obstruction_formula k K)

/-- The canonical relative Brauer isomorphism with the scalar-defect convention. -/
noncomputable def relativeBrauerEquiv :
    relativeBrauerGroup.{u,v,w} k K ≃+ Additive (H2 k K) :=
  AddEquiv.ofBijective (obstruction.{u,v,w} k K)
    ⟨canonical_obstruction_injective, obstruction_surjective⟩

@[simp] theorem relativeBrauerEquiv_toAddMonoidHom :
    (relativeBrauerEquiv.{u,v,w} (k := k) (K := K)).toAddMonoidHom = obstruction.{u,v,w} k K :=
  rfl

end RM03.Brauer.RelativeIsomorphism
