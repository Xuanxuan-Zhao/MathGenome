import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.AdditiveGaloisCohomology
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.FiniteLayerCohomology
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.KrullLayers
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.TraceContraction
import Mathlib.Algebra.Module.TransferInstance

namespace GaloisFormalization.GH.AdditiveGaloisCohomology

universe u v w

open Model
open Specs.GaloisFormalization.GH.AdditiveGaloisCohomology
open Specs.GaloisFormalization.GH.FiniteLayerCohomology

/-- The finite semilinear vanishing assertion of GH08. -/
theorem finite_semilinear_vanishing : FiniteSemilinearVanishing.{u,v,w} :=
  GaloisFormalization.GH.semilinear_cohomology_subsingleton

section Layers

variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L]

/-- The fixed additive coefficients and the layer field have the same elements in `L`. -/
private def additiveLayerEquiv (E : FiniteGaloisIntermediateField k L) :
    LayerCoefficients L E ≃+ E where
  toFun m := ⟨m, by
    rw [← KrullLayers.fixedField_layerKernel E, IntermediateField.mem_fixedField_iff]
    exact (mem_fixedCoefficients _ _ _ _).mp m.property⟩
  invFun x := ⟨x, (mem_fixedCoefficients _ _ _ _).mpr fun g hg =>
    (IntermediateField.mem_fixingSubgroup_iff E.toIntermediateField g).mp hg x x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

private theorem additiveLayerEquiv_smul (E : FiniteGaloisIntermediateField k L)
    (g : Gal(E/k)) (m : LayerCoefficients L E) :
    additiveLayerEquiv E (g • m) = g (additiveLayerEquiv E m) := by
  obtain ⟨σ, rfl⟩ := KrullLayers.restrict_surjective E g
  apply Subtype.ext
  change ((Specs.GaloisFormalization.GH.KrullLayers.restrict E σ • m :
    LayerCoefficients L E) : L) = (KrullLayers.restrict E σ (additiveLayerEquiv E m) : L)
  rw [layerAction_restrict, KrullLayers.restrict_apply]
  rfl

private theorem layerCohomology_subsingleton (E : FiniteGaloisIntermediateField k L)
    (q : ℕ) (hq : 0 < q) : Subsingleton (LayerH L E q) := by
  let e := additiveLayerEquiv E
  let : Module E (LayerCoefficients L E) := e.module E
  have scalar (a : E) (m : LayerCoefficients L E) : e (a • m) = a • e m :=
    (e.linearEquiv E).map_smul a m
  refine finite_semilinear_vanishing k E (LayerCoefficients L E) (fun g a m => ?_) q hq
  apply e.injective
  have equivariant (g : Gal(E/k)) (m : LayerCoefficients L E) : e (g • m) = g (e m) :=
    additiveLayerEquiv_smul E g m
  simp only [equivariant, scalar, smul_eq_mul, map_mul]

end Layers

/-- The additive group of a discrete Galois extension has zero continuous cohomology
in every positive degree. -/
theorem continuous_additive_vanishing : ContinuousAdditiveVanishing.{u,v} := by
  intro k L _ _ _ _ _ _ q hq
  let : ContinuousSMul Gal(L/k) L := KrullLayers.continuous_fieldAction k L
  obtain ⟨e, -⟩ := FiniteLayerCohomology.finiteLayerComparison (k := k) (L := L) L q
  have limit_eq_zero (x : LayerLimit (k := k) (L := L) L q) : x = 0 := by
    let : DecidableEq (FiniteGaloisIntermediateField k L) := Classical.decEq _
    obtain ⟨E, a, ha⟩ := Module.DirectLimit.exists_of (R := ℤ) x
    change limitOf L E q a = x at ha
    have := layerCohomology_subsingleton E q hq
    rw [← ha, Subsingleton.elim a 0, map_zero]
  exact ⟨fun x y => e.symm.injective
    ((limit_eq_zero (e.symm x)).trans (limit_eq_zero (e.symm y)).symm)⟩

end GaloisFormalization.GH.AdditiveGaloisCohomology
