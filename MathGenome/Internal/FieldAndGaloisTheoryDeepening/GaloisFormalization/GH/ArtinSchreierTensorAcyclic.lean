import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.ArtinSchreierTensorAcyclic
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.ArtinSchreierTensor
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.FiniteCochainDescent
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.TraceContraction
import Mathlib.GroupTheory.GroupAction.OfQuotient

namespace GaloisFormalization.GH.ArtinSchreierTensorAcyclic

open KrullLayers
open Model

universe u v w

noncomputable section

section FixedCoefficients

variable {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S]
variable {W : Type w} [AddCommGroup W] [Module S W] [DistribMulAction Gal(S/k) W]
variable (E : FiniteGaloisIntermediateField k S)

local instance : Module E W := Module.compHom W (algebraMap E S)

/-- The layer kernel fixes the scalars in the layer, so its fixed coefficients
form a vector space over that layer. -/
private def fixedSubmodule
    (hsemi : ∀ (g : Gal(S/k)) (a : S) (x : W), g • (a • x) = g a • (g • x)) :
    Submodule E W where
  carrier := MulAction.fixedPoints (layerKernel E) W
  zero_mem' g := smul_zero (g : Gal(S/k))
  add_mem' {x y} hx hy g := by
    have hxg : (g : Gal(S/k)) • x = x := hx g
    have hyg : (g : Gal(S/k)) • y = y := hy g
    change (g : Gal(S/k)) • (x + y) = x + y
    rw [smul_add, hxg, hyg]
  smul_mem' a x hx g := by
    have ha : (g : Gal(S/k)) (a : S) = a :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp g.property a a.property
    have hxg : (g : Gal(S/k)) • x = x := hx g
    change (g : Gal(S/k)) • ((a : S) • x) = (a : S) • x
    rw [hsemi, ha, hxg]

end FixedCoefficients

/-- A discrete semilinear module over a Galois extension is acyclic in positive degrees.
The finite stage uses the kernel-fixed coefficients with scalars restricted to the layer. -/
private theorem semilinear_acyclic
    {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S] [IsGalois k S]
    {W : Type w} [AddCommGroup W] [Module S W] [DistribMulAction Gal(S/k) W]
    [TopologicalSpace W] [DiscreteTopology W] [ContinuousSMul Gal(S/k) W]
    (hsemi : ∀ (g : Gal(S/k)) (a : S) (x : W), g • (a • x) = g a • (g • x))
    (n : ℕ) : Subsingleton (ContinuousH Gal(S/k) W (n + 1)) := by
  constructor
  suffices ∀ a : ContinuousH Gal(S/k) W (n + 1), a = 0 from
    fun a b => (this a).trans (this b).symm
  intro a
  obtain ⟨c, rfl⟩ := continuousClass_surjective (G := Gal(S/k)) (M := W) (n + 1) a
  obtain ⟨E, _, cE, hcE⟩ :=
    FiniteCochainDescent.finiteCochainFactorization c.val.val c.val.property
      (⊥ : FiniteGaloisIntermediateField k S)
  obtain ⟨e, he, _⟩ := quotient_restriction E
  let : Module E W := Module.compHom W (algebraMap E S)
  let V := fixedSubmodule E hsemi
  let i : V →+ W := V.subtype.toAddMonoidHom
  have hi : Function.Injective i := Subtype.val_injective
  let quotientAction : MulAction (Gal(S/k) ⧸ layerKernel E)
      (MulAction.fixedPoints (layerKernel E) W) := inferInstance
  let layerAction : MulAction (LayerGroup E) V :=
    MulAction.compHom (MulAction.fixedPoints (layerKernel E) W) e.symm.toMulEquiv.toMonoidHom
  have hact (g : Gal(S/k)) (x : V) :
      i (layerAction.smul (restrict E g) x) = g • i x := by
    have hg : e.symm (restrict E g) = QuotientGroup.mk g := e.symm_apply_eq.mpr (he g).symm
    change i (quotientAction.smul (e.symm (restrict E g)) x) = g • i x
    rw [hg]
    rfl
  let : DistribMulAction (LayerGroup E) V :=
    { layerAction with
      smul_zero := fun σ => by
        obtain ⟨g, rfl⟩ := restrict_surjective E σ
        exact hi ((hact g 0).trans (smul_zero g))
      smul_add := fun σ x y => by
        obtain ⟨g, rfl⟩ := restrict_surjective E σ
        apply hi
        change i (layerAction.smul (restrict E g) (x + y)) =
          i (layerAction.smul (restrict E g) x + layerAction.smul (restrict E g) y)
        rw [hact, map_add i, map_add i, hact, hact, smul_add] }
  let : TopologicalSpace V := ⊥
  let : DiscreteTopology V := discreteTopology_bot _
  have hsemiE (σ : LayerGroup E) (r : E) (x : V) : σ • (r • x) = σ r • (σ • x) := by
    obtain ⟨g, rfl⟩ := restrict_surjective E σ
    apply hi
    change i (layerAction.smul (restrict E g) (r • x)) =
      ((restrict E g r : E) : S) • i (layerAction.smul (restrict E g) x)
    rw [hact, hact, restrict_apply]
    exact hsemi g r (i x)
  let inflate (m : ℕ) := continuousCochainMap (restrict E).toMonoidHom (restrict E).continuous i m
  have hcomm (m : ℕ) (b : continuousCochains (LayerGroup E) V m) :
      inflate (m + 1) (continuousDifferential (LayerGroup E) V m b) =
        continuousDifferential Gal(S/k) W m (inflate m b) :=
    Model.continuousCochainMap_d _ _ _ hact m b
  have hinj (m : ℕ) : Function.Injective (inflate m) := by
    intro b d hbd
    apply Subtype.ext
    funext x
    obtain ⟨y, rfl⟩ := (Function.Surjective.piMap (fun _ : Fin m => restrict_surjective E)) x
    exact hi (congrArg (fun f : continuousCochains Gal(S/k) W m => f.val y) hbd)
  let c' : continuousCochains (LayerGroup E) V (n + 1) :=
    ⟨cE, continuous_of_discreteTopology⟩
  have hc' : inflate (n + 1) c' = c.val := Subtype.ext (funext hcE)
  have hz : continuousDifferential (LayerGroup E) V (n + 1) c' = 0 := by
    apply hinj
    rw [hcomm, hc', LinearMap.mem_ker.mp c.property, map_zero]
  let z : continuousCocycles (LayerGroup E) V (n + 1) := ⟨c', hz⟩
  have hvan := discrete_semilinear_cohomology_subsingleton k E V hsemiE (n + 1)
    (Nat.zero_lt_succ n)
  obtain ⟨b, hb⟩ := (continuousClass_succ_eq_iff z 0).mp (hvan.elim _ _)
  have hdb : continuousDifferential (LayerGroup E) V n b = c' := by
    simpa only [Submodule.coe_zero, sub_zero] using hb
  rw [← (continuousClass Gal(S/k) W (n + 1)).map_zero]
  apply (continuousClass_succ_eq_iff c 0).mpr
  refine ⟨inflate n b, ?_⟩
  rw [← hcomm, hdb, hc', Submodule.coe_zero, sub_zero]

open ArtinSchreierTensor
open Specs.GaloisFormalization.GH.ArtinSchreierTensorAcyclic (tensorAcyclic_type)

/-- The Artin–Schreier diagonal tensor has zero positive-degree continuous cohomology. -/
theorem tensorAcyclic : tensorAcyclic_type.{u,v,w} := by
  intro p k S _ _ _ _ _ _ M _ _ _ _ _ h
  let : CharP S p := charP_of_injective_algebraMap' k p
  let : Module (ZMod p) M := primeFieldModule p M h
  let W := Tensor p S M
  let : DistribMulAction (AbsoluteGaloisGroup k S) W := diagonalAction p S M
  change ∀ [TopologicalSpace W] [DiscreteTopology W],
    ∃ hW : ContinuousSMul (AbsoluteGaloisGroup k S) W,
      letI := hW
      ∀ q : ℕ, 0 < q → Subsingleton (ContinuousH (AbsoluteGaloisGroup k S) W q)
  intro _ _
  let hW : ContinuousSMul (AbsoluteGaloisGroup k S) W :=
    continuous_diagonalAction p k S M h
  refine ⟨hW, ?_⟩
  intro q hq
  cases q with
  | zero => exact (Nat.not_lt_zero _ hq).elim
  | succ n => exact semilinear_acyclic (k := k) (S := S) (W := W) (semilinear p k S M h) n

end

end GaloisFormalization.GH.ArtinSchreierTensorAcyclic
