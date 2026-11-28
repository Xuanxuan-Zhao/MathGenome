import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.TruncatedProjectives
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.BorelInduction
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.Category
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.WeightBounds
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.WeightExactness
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.FiniteLength
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory Module UniversalEnvelopingAlgebra
open scoped Classical ModuleCat.Algebra TensorProduct

namespace RepTheorySurvey.CategoryO.TruncatedProjectives
attribute [local instance 100] LieRing.ofAssociativeRing

open BorelInduction (U Induced inclusion induceTensor restrictModule)
open Specs.LieAlgebrasAndRepresentations.SerreRelations (positive)
open Specs.RepTheorySurvey.CategoryO.WeightBounds
  (restrictedBorelAction restrictedBorelTower)
open BorelInduction (balance balance_tensor smul_tensor mapInduced mapInduced_tensor
  inducedPBWEquiv inducedPBWEquiv_tensor pbwNaturality)
open Specs.LieAlgebrasAndRepresentations.VermaModules (envelopingMap weightModule_value)
open Shared.Lie.PBW
open private exists_positive_basis positive_basis_root_mem_cone sum_roots_mem_cone
  bounds_of_pbw_span monomial_smul_weight weightSpace_independent local_finite_of_bounds weight_fibres
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.WeightBounds
open private exists_negative_basis finite_wordRoot_fibre wordRoot wordRoot_mem_cone
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaWeightsUniversal
open private quotientExt from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.BorelInduction
open private envelopingMap_ι envelopingMap_comp from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaModules

universe u v

variable {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
variable (D : Setup g)

theorem mem_borelWeightSpace {V : Type v} [AddCommGroup V] [Module ℂ V]
    [Module (U D.borel) V] [IsScalarTower ℂ (U D.borel) V] (ν : D.Weight) (x : V) :
    x ∈ borelWeightSpace D V ν ↔ ∀ h : D.cartan,
      (ι ℂ (cartanInBorel D h)) • x = ν h • x := by
  simp only [borelWeightSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  rfl

/-- The ordinary weight-space functor preserves the short exact sequences of cutoff objects. -/
theorem weightExact : Expected.WeightExactType.{u, v} := by
  intro g _ _ _ D μ Λ X Y Z f q hf hExact hq
  let := restrictedLieRingModule X.obj (g := g)
  let := restrictedLieModule X.obj (g := g)
  let := restrictedLieRingModule Y.obj (g := g)
  let := restrictedLieModule Y.obj (g := g)
  let := restrictedLieRingModule Z.obj (g := g)
  let := restrictedLieModule Z.obj (g := g)
  let fH : X.obj →ₗ⁅ℂ,D.cartan⁆ Y.obj :=
    { f.restrictScalars ℂ with
      map_lie' := fun {h x} => f.map_smul (ι ℂ (h : g)) x }
  let qH : Y.obj →ₗ⁅ℂ,D.cartan⁆ Z.obj :=
    { q.restrictScalars ℂ with
      map_lie' := fun {h x} => q.map_smul (ι ℂ (h : g)) x }
  exact WeightExactness.shortExact fH qH Y.property.1.2.1 hf hExact hq μ

private abbrev borelCartan := (cartanInBorel D).range
private abbrev borelPositive := (positiveInBorel D).range

private theorem borelParts_compl :
    IsCompl (borelPositive D).toSubmodule (borelCartan D).toSubmodule := by
  refine ⟨disjoint_iff.mpr (eq_bot_iff.mpr ?_), codisjoint_iff.mpr (top_unique ?_)⟩
  · intro x hx
    obtain ⟨⟨p, hp⟩, ⟨h, hh⟩⟩ :=
      (show (∃ p, positiveInBorel D p = x) ∧ (∃ h, cartanInBorel D h = x) from hx)
    have hp' : (x : g) ∈ D.nPlus.toSubmodule := by
      rw [← hp]
      exact p.property
    have hh' : (x : g) ∈ D.cartan.toSubmodule := by
      rw [← hh]
      exact h.property
    have hz : (x : g) = 0 :=
      (Submodule.disjoint_def.mp (cartan_borel D).2.1) _ hh' hp'
    exact (Submodule.mem_bot ℂ).mpr (Subtype.ext hz)
  · intro x _
    have hx : (x : g) ∈ D.cartan.toSubmodule ⊔ D.nPlus.toSubmodule :=
      (cartan_borel D).1 ▸ x.property
    obtain ⟨h, hh, p, hp, he⟩ := Submodule.mem_sup.mp hx
    refine Submodule.mem_sup.mpr
      ⟨positiveInBorel D ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩,
        cartanInBorel D ⟨h, hh⟩, ⟨⟨h, hh⟩, rfl⟩, Subtype.ext ?_⟩
    change p + h = (x : g)
    rwa [add_comm]

section RawMaps

variable {V : Type v} [AddCommGroup V] [Module ℂ V] [Module (U D.borel) V]
  [IsScalarTower ℂ (U D.borel) V]

private def actionMap (x : V) : U D.borel →ₗ[U D.borel] V where
  toFun a := a • x
  map_add' a b := add_smul a b x
  map_smul' a b := mul_smul a b x

private def rawLift {μ : D.Weight} (x : V) (hx : x ∈ borelWeightSpace D V μ) :
    Raw D μ →ₗ[U D.borel] V :=
  (cartanRelations D μ).liftQ (actionMap D x) (by
    apply Submodule.span_le.mpr
    rintro _ ⟨h, rfl⟩
    change (ι ℂ (cartanInBorel D h) - algebraMap ℂ (U D.borel) (μ h)) • x = 0
    rw [sub_smul, algebraMap_smul, (mem_borelWeightSpace D μ x).mp hx h, sub_self])

@[simp] private theorem rawLift_generator {μ : D.Weight} (x : V)
    (hx : x ∈ borelWeightSpace D V μ) : rawLift D x hx (rawGenerator D μ) = x := by
  change (1 : U D.borel) • x = x
  exact one_smul _ _

private theorem rawGenerator_weight (μ : D.Weight) :
    rawGenerator D μ ∈ borelWeightSpace D (Raw D μ) μ := by
  apply (mem_borelWeightSpace D _ _).mpr
  intro h
  apply sub_eq_zero.mp
  rw [← algebraMap_smul (U D.borel) (μ h), ← sub_smul]
  change (ι ℂ (cartanInBorel D h) - algebraMap ℂ (U D.borel) (μ h)) •
    (cartanRelations D μ).mkQ 1 = 0
  rw [← map_smul, smul_eq_mul, mul_one]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨h, rfl⟩)

private theorem raw_eq_smul (μ : D.Weight) (y : Raw D μ) :
    ∃ a : U D.borel, a • rawGenerator D μ = y := by
  obtain ⟨a, rfl⟩ := (cartanRelations D μ).mkQ_surjective y
  refine ⟨a, ?_⟩
  change a • (cartanRelations D μ).mkQ 1 = _
  rw [← map_smul, smul_eq_mul, mul_one]

private theorem map_borelWeight {W : Type*} [AddCommGroup W] [Module ℂ W]
    [Module (U D.borel) W] [IsScalarTower ℂ (U D.borel) W]
    (f : V →ₗ[U D.borel] W) {ν : D.Weight} {x : V}
    (hx : x ∈ borelWeightSpace D V ν) : f x ∈ borelWeightSpace D W ν := by
  refine (mem_borelWeightSpace D _ _).mpr fun h => ?_
  rw [← f.map_smul, (mem_borelWeightSpace D _ _).mp hx h]
  exact (f.restrictScalars ℂ).map_smul _ _

end RawMaps

private def cartanCharacter (μ : D.Weight) : U (borelCartan D) →ₐ[ℂ] ℂ :=
  (character D μ).comp (inclusion (borelCartan D))

private theorem rawGenerator_cartan_smul (μ : D.Weight) (a : U (borelCartan D)) :
    inclusion (borelCartan D) a • rawGenerator D μ =
      cartanCharacter D μ a • rawGenerator D μ := by
  induction a using Shared.Lie.enveloping_induction ℂ (borelCartan D) with
  | scalar c =>
    rw [(inclusion (borelCartan D)).commutes, (cartanCharacter D μ).commutes,
      algebraMap_smul, Algebra.algebraMap_self_apply]
  | generator h =>
    obtain ⟨a, ha⟩ := h.property
    have hh : ((h : borelCartan D) : D.borel) = cartanInBorel D a := ha.symm
    rw [Shared.Lie.inclusion, cartanCharacter, AlgHom.comp_apply, BorelInduction.inclusion_ι, hh]
    change ι ℂ (cartanInBorel D a) • rawGenerator D μ =
      character D μ (ι ℂ (cartanInBorel D a)) • rawGenerator D μ
    rw [(character_unique D μ).1.1 a]
    exact (mem_borelWeightSpace D _ _).mp (rawGenerator_weight D μ) a
  | add a b ha hb =>
    rw [map_add, map_add, add_smul, add_smul, ha, hb]
  | mul a b ha hb =>
    rw [map_mul, map_mul, mul_smul, hb, smul_comm, ha, smul_smul, mul_comm]

private def positiveEquiv : D.nPlus ≃ₗ⁅ℂ⁆ borelPositive D :=
  (positiveInBorel D).equivRangeOfInjective (fun _ _ h =>
    Subtype.ext (congrArg (fun x : D.borel => (x : g)) h))

private def positiveEnvelopingEquiv : U D.nPlus ≃ₗ[ℂ] U (borelPositive D) := by
  let η := positiveEquiv D
  let j := envelopingMap (η : D.nPlus →ₗ⁅ℂ⁆ borelPositive D)
  have hj : Function.Bijective j := by
    let k := envelopingMap (η.symm : borelPositive D →ₗ⁅ℂ⁆ D.nPlus)
    have kl : k.comp j = AlgHom.id ℂ _ := by
      apply UniversalEnvelopingAlgebra.hom_ext
      apply DFunLike.ext
      intro x
      change k (j (ι ℂ x)) = ι ℂ x
      dsimp only [j, k]
      rw [envelopingMap_ι, envelopingMap_ι]
      simp
    have kr : j.comp k = AlgHom.id ℂ _ := by
      apply UniversalEnvelopingAlgebra.hom_ext
      apply DFunLike.ext
      intro x
      change j (k (ι ℂ x)) = ι ℂ x
      dsimp only [j, k]
      rw [envelopingMap_ι, envelopingMap_ι]
      simp
    exact ⟨Function.LeftInverse.injective (DFunLike.congr_fun kl),
      Function.RightInverse.surjective (DFunLike.congr_fun kr)⟩
  exact LinearEquiv.ofBijective j.toLinearMap hj

@[simp] private theorem positiveEnvelopingEquiv_apply (a : U D.nPlus) :
    inclusion (borelPositive D) (positiveEnvelopingEquiv D a) =
      envelopingMap (positiveInBorel D) a := by
  change ((envelopingMap (borelPositive D).incl).comp
    (envelopingMap (positiveEquiv D).toLieHom)) a = _
  rw [envelopingMap_comp]
  rfl

private theorem rawPBW (μ : D.Weight) :
    ∃ F : U D.nPlus ≃ₗ[ℂ] Raw D μ,
      ∀ a, F a = envelopingMap (positiveInBorel D) a • rawGenerator D μ := by
  let i := inclusion (borelCartan D)
  let χ := cartanCharacter D μ
  let : Module (U (borelCartan D)) ℂ := Module.compHom ℂ χ.toRingHom
  let : IsScalarTower ℂ (U (borelCartan D)) ℂ :=
    IsScalarTower.of_algebraMap_smul (fun c z => by
      change χ (algebraMap ℂ (U (borelCartan D)) c) * z = c * z
      rw [χ.commutes, Algebra.algebraMap_self_apply])
  let Y := Induced i ℂ
  let y : Y := induceTensor i 1 1
  have hy : y ∈ borelWeightSpace D Y μ := by
    refine (mem_borelWeightSpace D μ y).mpr fun h => ?_
    let h' : borelCartan D := ⟨cartanInBorel D h, ⟨h, rfl⟩⟩
    rw [← show i (ι ℂ h') = ι ℂ (cartanInBorel D h) from BorelInduction.inclusion_ι _ _]
    rw [show y = induceTensor i 1 (1 : ℂ) from rfl, BorelInduction.smul_tensor, mul_one,
      ← one_mul (i (ι ℂ h')), BorelInduction.balance_tensor]
    have hχ : (ι ℂ h') • (1 : ℂ) = μ h := by
      change character D μ (i (ι ℂ h')) * 1 = μ h
      rw [BorelInduction.inclusion_ι, mul_one]
      exact (character_unique D μ).1.1 h
    rw [hχ]
    change (BorelInduction.balance i ℂ).mkQ ((1 : U D.borel) ⊗ₜ[ℂ] μ h) = _
    calc
      _ = (BorelInduction.balance i ℂ).mkQ ((1 : U D.borel) ⊗ₜ[ℂ] (μ h • (1 : ℂ))) := by simp
      _ = _ := by
        rw [TensorProduct.tmul_smul]
        exact ((BorelInduction.balance i ℂ).mkQ.restrictScalars ℂ).map_smul _ _
  let f := rawLift D y hy
  let := restrictModule i (Raw D μ)
  let L : ℂ →ₗ[U (borelCartan D)] Raw D μ :=
    { toFun := fun c => c • rawGenerator D μ
      map_add' := fun c d => add_smul c d _
      map_smul' := fun a c => by
        change (χ a * c) • rawGenerator D μ = i a • (c • rawGenerator D μ)
        rw [smul_comm (i a), rawGenerator_cartan_smul D μ, smul_smul, mul_comm] }
  let e := BorelInduction.extend i L
  have hey : e y = rawGenerator D μ := by
    rw [BorelInduction.extend_tensor]
    change (1 : U D.borel) • ((1 : ℂ) • rawGenerator D μ) = _
    simp
  have hef : Function.LeftInverse e f := by
    intro z
    obtain ⟨a, rfl⟩ := raw_eq_smul D μ z
    rw [f.map_smul, rawLift_generator, e.map_smul, hey]
  have hfe : Function.RightInverse e f := by
    have h : f.comp e = LinearMap.id := by
      apply quotientExt i
      intro a c
      change f (e (induceTensor i a c)) = induceTensor i a c
      rw [BorelInduction.extend_tensor, f.map_smul]
      change a • (f.restrictScalars ℂ) (c • rawGenerator D μ) = _
      rw [map_smul]
      change a • c • f (rawGenerator D μ) = _
      rw [rawLift_generator, smul_comm, BorelInduction.smul_tensor, mul_one]
      let q := (BorelInduction.balance i ℂ).mkQ.restrictScalars ℂ
      change c • q (a ⊗ₜ[ℂ] (1 : ℂ)) = q (a ⊗ₜ[ℂ] c)
      rw [← q.map_smul,
        ← TensorProduct.tmul_smul, smul_eq_mul, mul_one]
    intro z
    exact LinearMap.congr_fun h z
  let Q : Y ≃ₗ[ℂ] Raw D μ :=
    (LinearEquiv.ofBijective e ⟨hfe.injective, hef.surjective⟩).restrictScalars ℂ
  obtain ⟨F, hF⟩ := BorelInduction.inducedPBW (borelPositive D) (borelCartan D)
    (E := ℂ) (borelParts_compl D)
  let J := positiveEnvelopingEquiv D
  refine ⟨J.trans ((TensorProduct.rid ℂ _).symm.trans (F.trans Q)), fun a => ?_⟩
  have hright : (TensorProduct.rid ℂ (U (borelPositive D))).symm (J a) =
      J a ⊗ₜ[ℂ] (1 : ℂ) := rfl
  change e (F ((TensorProduct.rid ℂ _).symm (J a))) = _
  rw [hright, hF]
  change e (induceTensor i ((inclusion (borelPositive D)) (J a)) (1 : ℂ)) = _
  rw [← mul_one ((inclusion (borelPositive D)) (J a)), ← BorelInduction.smul_tensor]
  change e (((inclusion (borelPositive D)) (J a)) • y) = _
  rw [e.map_smul, hey, positiveEnvelopingEquiv_apply D a]

section BorelWeights

variable (V : Type v) [AddCommGroup V] [Module ℂ V] [Module (U D.borel) V]
  [IsScalarTower ℂ (U D.borel) V]

private theorem borelWeight_independent : iSupIndep (borelWeightSpace D V) := by
  let := restrictedLieRingModule V (g := D.borel)
  let := restrictedLieModule V (g := D.borel)
  let := LieRingModule.compLieHom V (cartanInBorel D)
  let := LieModule.compLieHom V (cartanInBorel D)
  have heq : borelWeightSpace D V = WeightExactness.weightSpace V (H := D.cartan) := by
    funext ν
    ext x
    rw [mem_borelWeightSpace, WeightExactness.weightSpace, LieSubmodule.mem_toSubmodule,
      LieModule.mem_weightSpace]
    rfl
  rw [heq]
  exact WeightExactness.weightSpaces_independent

private theorem borelWeight_map_eq {W : Type*} [AddCommGroup W] [Module ℂ W]
    [Module (U D.borel) W] [IsScalarTower ℂ (U D.borel) W]
    (f : V →ₗ[U D.borel] W) (hf : Function.Surjective f)
    (hV : DirectSum.IsInternal (borelWeightSpace D V)) :
    (fun ν => (borelWeightSpace D V ν).map (f.restrictScalars ℂ)) = borelWeightSpace D W := by
  have htop : (⨆ ν, (borelWeightSpace D V ν).map (f.restrictScalars ℂ)) = ⊤ := by
    rw [← Submodule.map_iSup, hV.submodule_iSup_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hf
  refine (iSupIndep.le_iff_eq_of_iSup_eq_top (borelWeight_independent D W) htop).mp ?_
  intro ν
  rintro _ ⟨x, hx, rfl⟩
  exact map_borelWeight D f hx

private theorem borelWeight_fibres {I : Type*} (f : I → V) (wt : I → D.Weight)
    (hw : ∀ i, f i ∈ borelWeightSpace D V (wt i))
    (hf : Submodule.span ℂ (Set.range f) = ⊤) :
    (fun ν => Submodule.span ℂ (f '' {i | wt i = ν})) = borelWeightSpace D V := by
  let S (ν : D.Weight) := Submodule.span ℂ (f '' {i | wt i = ν})
  have hS : S ≤ borelWeightSpace D V := by
    intro ν
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi : wt i = ν, rfl⟩
    exact hi ▸ hw i
  have htop : iSup S = ⊤ := by
    apply top_unique
    rw [← hf]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_iSup_of_mem (wt i) (Submodule.subset_span ⟨i, rfl, rfl⟩)
  exact ((borelWeight_independent D V).le_iff_eq_of_iSup_eq_top htop).mp hS

private theorem borel_root_smul (α ν : D.Weight) (x : D.nPlus) (y : V)
    (hx : (x : g) ∈ Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSpace_value D.cartan α)
    (hy : y ∈ borelWeightSpace D V ν) :
    (ι ℂ (positiveInBorel D x)) • y ∈ borelWeightSpace D V (ν + α) := by
  apply (mem_borelWeightSpace D _ _).mpr
  intro h
  let a := ι ℂ (cartanInBorel D h)
  let b := ι ℂ (positiveInBorel D x)
  have hab : a * b - b * a = α h • b := by
    have hRoot : ⁅(h : g), (x : g)⁆ = α h • (x : g) :=
      (_root_.LieAlgebrasAndRepresentations.mem_rootSpace D.cartan α x).mp hx h
    have hB : ⁅cartanInBorel D h, positiveInBorel D x⁆ = α h • positiveInBorel D x :=
      Subtype.ext hRoot
    calc
      a * b - b * a = ι ℂ ⁅cartanInBorel D h, positiveInBorel D x⁆ :=
        ((ι ℂ).map_lie _ _).symm
      _ = _ := by rw [hB, map_smul]
  change a • (b • y) = (ν h + α h) • (b • y)
  rw [← mul_smul, show a * b = b * a + α h • b by rw [← hab]; abel,
    add_smul, mul_smul, (show a • y = ν h • y from (mem_borelWeightSpace D _ _).mp hy h),
    smul_comm b, smul_assoc, ← add_smul]

private theorem borel_monomial_smul {I : Type*} (b : Basis I ℂ D.nPlus) (α : I → D.Weight)
    (hb : ∀ i, (b i : g) ∈
      Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSpace_value D.cartan (α i))
    {ν : D.Weight} {y : V} (hy : y ∈ borelWeightSpace D V ν) (l : List I) :
    envelopingMap (positiveInBorel D) (Shared.Lie.PBW.monomial b l) • y ∈
      borelWeightSpace D V (ν + (l.map α).sum) := by
  induction l with
  | nil => simpa [Shared.Lie.PBW.monomial, Shared.Lie.word] using hy
  | cons i l ih =>
    change envelopingMap (positiveInBorel D) (ι ℂ (b i) * Shared.Lie.PBW.monomial b l) • y ∈ _
    rw [map_mul, mul_smul, envelopingMap_ι]
    convert borel_root_smul D V (α i) (ν + (l.map α).sum) (b i) _ (hb i) ih using 2
    simp only [List.map_cons, List.sum_cons]
    abel

end BorelWeights

private theorem cartan_preserves_positive (h : D.cartan) (x : borelPositive D) :
    ⁅cartanInBorel D h, (x : D.borel)⁆ ∈ borelPositive D := by
  obtain ⟨p, hp⟩ := x.property
  let T : g →ₗ[ℂ] g := LieModule.toEnd ℂ g g (h : g)
  have hle : D.nPlus.toSubmodule ≤ D.nPlus.toSubmodule.comap T := by
    conv_lhs => rw [(root_parts D).1]
    apply iSup_le
    intro α y hy
    have hyP : y ∈ D.nPlus := by
      change y ∈ D.nPlus.toSubmodule
      rw [(root_parts D).1]
      exact Submodule.mem_iSup_of_mem α hy
    change ⁅(h : g), y⁆ ∈ D.nPlus
    rw [(_root_.LieAlgebrasAndRepresentations.mem_rootSpace D.cartan α.val y).mp hy h]
    exact D.nPlus.smul_mem _ hyP
  let q : D.nPlus := ⟨⁅(h : g), (p : g)⁆, hle p.property⟩
  exact ⟨q, Subtype.ext (congrArg (fun z : D.borel => ⁅(h : g), (z : g)⁆) hp)⟩

private theorem rawCartanFormula (μ : D.Weight) (F : U D.nPlus ≃ₗ[ℂ] Raw D μ)
    (hF : ∀ a, F a = envelopingMap (positiveInBorel D) a • rawGenerator D μ)
    (a : U D.nPlus) (ν : D.Weight) :
    F a ∈ borelWeightSpace D (Raw D μ) ν ↔ ∀ h : D.cartan,
      ι ℂ (cartanInBorel D h) * envelopingMap (positiveInBorel D) a -
        envelopingMap (positiveInBorel D) a * ι ℂ (cartanInBorel D h) =
      (ν - μ) h • envelopingMap (positiveInBorel D) a := by
  rw [mem_borelWeightSpace]
  apply forall_congr'
  intro h
  let A := envelopingMap (positiveInBorel D)
  let H := ι ℂ (cartanInBorel D h)
  let b := (positiveEnvelopingEquiv D).symm
    (BorelInduction.cartanCommutator (borelPositive D) (borelCartan D) (borelParts_compl D)
      ⟨cartanInBorel D h, ⟨h, rfl⟩⟩ (cartan_preserves_positive D h) (positiveEnvelopingEquiv D a))
  have hbr : A b = H * A a - A a * H := by
    dsimp only [A, b]
    rw [← positiveEnvelopingEquiv_apply, LinearEquiv.apply_symm_apply,
      BorelInduction.inclusion_cartanCommutator, positiveEnvelopingEquiv_apply]
  have hH : H • rawGenerator D μ = μ h • rawGenerator D μ :=
    (mem_borelWeightSpace D _ _).mp (rawGenerator_weight D μ) h
  have hFa : H • F a = F b + μ h • F a := by
    rw [hF b, hF a, hbr, sub_smul, mul_smul, mul_smul, hH, smul_comm (A a)]
    abel
  change (H • F a = ν h • F a) ↔ (H * A a - A a * H = (ν - μ) h • A a)
  rw [hFa, ← hbr, LinearMap.sub_apply]
  constructor
  · intro he
    have hf : F b = (ν h - μ h) • F a := by
      rw [sub_smul, eq_sub_iff_add_eq]
      exact he
    have hab : b = (ν h - μ h) • a :=
      F.injective (by simpa only [map_smul] using hf)
    calc
      A b = A ((ν h - μ h) • a) := congrArg A hab
      _ = _ := A.toLinearMap.map_smul _ _
  · intro he
    have hf : F b = (ν h - μ h) • F a := by
      rw [hF b, hF a]
      rw [show A b = (ν h - μ h) • A a from he, smul_assoc]
    rw [hf, ← add_smul, sub_add_cancel]

/-- PBW identifies the untruncated Borel module with the positively generated algebra. -/
theorem raw : Expected.RawType.{u} := by
  intro g _ _ _ D μ
  obtain ⟨F, hF⟩ := rawPBW D μ
  refine ⟨F, hF, rawCartanFormula D μ F hF, ?_⟩
  let I := positive D.cartan (-D.direction)
  let : LinearOrder I := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨b, hb⟩ := exists_positive_basis D
  let basis : Basis (OrderedWord I) ℂ (Raw D μ) := (orderedBasis b).map F
  let α (i : I) : D.Weight := -i.val
  let wt (l : OrderedWord I) : D.Weight := μ + (l.val.map α).sum
  have hw (l : OrderedWord I) : basis l ∈ borelWeightSpace D (Raw D μ) (wt l) := by
    rw [show basis l = F (orderedMonomial b l) by simp [basis]]
    rw [hF]
    exact borel_monomial_smul D _ b α hb (rawGenerator_weight D μ) l.val
  have hfib := borelWeight_fibres D _ basis wt hw basis.span_eq
  have htop : (⨆ ν, borelWeightSpace D (Raw D μ) ν) = ⊤ := by
    apply top_unique
    rw [← basis.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    exact Submodule.mem_iSup_of_mem (wt l) (hw l)
  refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (borelWeight_independent D _) htop, ?_, ?_⟩
  · intro ν
    have hword (l : List I) : (l.map α).sum = -wordRoot D.cartan (-D.direction) l := by
      induction l with
      | nil =>
        change (0 : D.Weight) = -0
        rw [neg_zero]
      | cons i l ih =>
        change α i + (l.map α).sum = -(i.val + wordRoot D.cartan (-D.direction) l)
        rw [ih, neg_add]
    rw [← congrFun hfib ν]
    apply FiniteDimensional.span_of_finite
    apply Set.Finite.image
    apply (finite_wordRoot_fibre D.cartan (-D.direction) D.semisimple (μ - ν)).subset
    intro l (hl : wt l = ν)
    change μ + (l.val.map α).sum = ν at hl
    rw [hword, ← sub_eq_add_neg] at hl
    change wordRoot D.cartan (-D.direction) l.val = μ - ν
    rw [← hl, sub_sub_cancel]
  · intro ν hν
    have hf : {l | wt l = ν}.Nonempty := by
      by_contra hn
      rw [Set.not_nonempty_iff_eq_empty] at hn
      exact hν (by rw [← congrFun hfib ν, hn, Set.image_empty, Submodule.span_empty])
    obtain ⟨l, (hl : wt l = ν)⟩ := hf
    change ν - μ ∈ QPlus D
    rw [← hl, show wt l - μ = (l.val.map α).sum by simp [wt]]
    exact sum_roots_mem_cone D α (positive_basis_root_mem_cone D) l.val

private theorem le_add_root (ν α : D.Weight) (hα : α ∈ QPlus D) :
    weightLE D ν (ν + α) := by
  change ν + α - ν ∈ QPlus D
  simpa only [add_sub_cancel_left] using hα

section WeightSpan

variable (V : Type v) [AddCommGroup V] [Module ℂ V] [Module (U D.borel) V]
  [IsScalarTower ℂ (U D.borel) V]

private abbrev weightSpan (s : Set D.Weight) : Submodule ℂ V :=
  ⨆ ν : s, borelWeightSpace D V ν.val

private theorem mem_weightSpan_of_weight {s : Set D.Weight} {ν : D.Weight} {x : V}
    (hν : ν ∈ s) (hx : x ∈ borelWeightSpace D V ν) :
    x ∈ weightSpan D V s :=
  Submodule.mem_iSup_of_mem (⟨ν, hν⟩ : s) hx

private theorem smul_mem_weightSpan (s : Set D.Weight)
    (hs : ∀ ν ∈ s, ∀ α ∈ QPlus D, borelWeightSpace D V (ν + α) ≠ ⊥ → ν + α ∈ s)
    (a : U D.borel) (x : V) (hx : x ∈ weightSpan D V s) :
    a • x ∈ weightSpan D V s := by
  induction a using Shared.Lie.enveloping_induction ℂ D.borel generalizing x with
  | scalar c =>
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ hx
  | add a b ha hb =>
    rw [add_smul]
    exact Submodule.add_mem _ (ha x hx) (hb x hx)
  | mul a b ha hb =>
    rw [mul_smul]
    exact ha _ (hb x hx)
  | generator z =>
    rw [Shared.Lie.inclusion]
    let S := weightSpan D V s
    let L : V →ₗ[ℂ] V := Algebra.lsmul ℂ ℂ V (ι ℂ z)
    have hle : S ≤ S.comap L := by
      apply iSup_le
      intro ν y hy
      change (ι ℂ z) • y ∈ S
      have hz : (z : g) ∈ D.cartan.toSubmodule ⊔ D.nPlus.toSubmodule :=
        (cartan_borel D).1 ▸ z.property
      obtain ⟨h, hh, p, hp, he⟩ := Submodule.mem_sup.mp hz
      have hz' : z = cartanInBorel D ⟨h, hh⟩ + positiveInBorel D ⟨p, hp⟩ :=
        Subtype.ext he.symm
      rw [hz', map_add, add_smul, (mem_borelWeightSpace D _ _).mp hy ⟨h, hh⟩]
      apply S.add_mem (S.smul_mem _ (mem_weightSpan_of_weight D V ν.property hy))
      obtain ⟨b, hb⟩ := exists_positive_basis D
      let action : U D.borel →ₗ[ℂ] Module.End ℂ V := (Algebra.lsmul ℂ ℂ V).toLinearMap
      let T : D.nPlus →ₗ[ℂ] V :=
        ((action.comp (ι ℂ).toLinearMap).comp (positiveInBorel D).toLinearMap).flip y
      have hpos : (⊤ : Submodule ℂ D.nPlus) ≤ S.comap T := by
        rw [← b.span_eq]
        apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        have hw := borel_root_smul D V (-i.val) ν.val (b i) y (hb i) hy
        by_cases hbot : borelWeightSpace D V (ν.val + -i.val) = ⊥
        · rw [hbot, Submodule.mem_bot] at hw
          change (ι ℂ (positiveInBorel D (b i))) • y ∈ S
          rw [hw]
          exact S.zero_mem
        · exact mem_weightSpan_of_weight D V
            (hs ν.val ν.property _ (positive_basis_root_mem_cone D i) hbot) hw
      exact hpos (Submodule.mem_top (x := (⟨p, hp⟩ : D.nPlus)))
    exact hle hx

private def weightSpanSubmodule (s : Set D.Weight)
    (hs : ∀ ν ∈ s, ∀ α ∈ QPlus D, borelWeightSpace D V (ν + α) ≠ ⊥ → ν + α ∈ s) :
    Submodule (U D.borel) V where
  toAddSubmonoid := (weightSpan D V s).toAddSubmonoid
  smul_mem' := fun a x hx => smul_mem_weightSpan D V s hs a x hx

end WeightSpan

set_option maxHeartbeats 800000 in
/-- Exactly the forbidden direct summands form the discarded Borel submodule. -/
theorem discarded_eq (μ Λ : D.Weight) :
    (discarded D μ Λ).restrictScalars ℂ =
      ⨆ ν : {ν : D.Weight // ¬ weightLE D ν Λ}, borelWeightSpace D (Raw D μ) ν.val := by
  let s : Set D.Weight := {ν | ¬ weightLE D ν Λ}
  let S := weightSpanSubmodule D (Raw D μ) s (fun ν hν α hα _ h =>
    hν (_root_.LieAlgebrasAndRepresentations.HighestWeight.weightLE_trans D.alpha (le_add_root D ν α hα) h))
  have heq : discarded D μ Λ = S := by
    change Submodule.span (U D.borel) (↑(weightSpan D (Raw D μ) s) : Set _) = S
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro x hx
      exact hx
    · intro x hx
      apply Submodule.subset_span
      exact hx
  rw [heq]
  rfl

private theorem generatorE_spans (μ Λ : D.Weight) :
    Submodule.span (U D.borel) {generatorE D μ Λ} = ⊤ := by
  apply (Submodule.span_singleton_eq_top_iff (U D.borel) _).mpr
  intro x
  obtain ⟨y, rfl⟩ := (discarded D μ Λ).mkQ_surjective x
  obtain ⟨a, rfl⟩ := raw_eq_smul D μ y
  exact ⟨a, ((discarded D μ Λ).mkQ.map_smul a _).symm⟩

set_option maxHeartbeats 1000000 in
/-- The cutoff removes the forbidden weights and leaves a finite-dimensional Borel module. -/
theorem truncation : Expected.TruncationType.{u} := by
  intro g _ _ _ D μ Λ _
  obtain ⟨_, _, _, hInt, hFin, hBounds⟩ := raw D μ
  let q := (discarded D μ Λ).mkQ
  have hm := borelWeight_map_eq D (Raw D μ) q (discarded D μ Λ).mkQ_surjective hInt
  have htop : (⨆ ν, borelWeightSpace D (E D μ Λ) ν) = ⊤ := by
    rw [← hm, ← Submodule.map_iSup, hInt.submodule_iSup_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (discarded D μ Λ).mkQ_surjective
  have hb (ν : D.Weight) (hν : borelWeightSpace D (E D μ Λ) ν ≠ ⊥) :
      weightLE D μ ν ∧ weightLE D ν Λ := by
    rw [← congrFun hm ν] at hν
    constructor
    · apply hBounds ν
      intro h
      exact hν (by rw [h, Submodule.map_bot])
    · by_contra hn
      apply hν
      apply bot_unique
      rw [Submodule.map_le_iff_le_comap]
      intro x hx
      change q x = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      change x ∈ (discarded D μ Λ).restrictScalars ℂ
      rw [discarded_eq]
      exact Submodule.mem_iSup_of_mem (⟨ν, hn⟩ : {ν : D.Weight // ¬ weightLE D ν Λ}) hx
  have hfinite (ν : D.Weight) : FiniteDimensional ℂ (borelWeightSpace D (E D μ Λ) ν) := by
    rw [← congrFun hm ν]
    let := hFin ν
    exact Module.Finite.map _ _
  have hE : FiniteDimensional ℂ (E D μ Λ) := by
    let T : Set D.Weight := {ν | weightLE D μ ν ∧ weightLE D ν Λ}
    let : Finite T := ((finiteUpward D {Λ} μ).subset
      (show T ⊆ _ from fun ν hν => ⟨hν.1, Λ, Finset.mem_singleton_self Λ, hν.2⟩)).to_subtype
    let (ν : T) : FiniteDimensional ℂ (borelWeightSpace D (E D μ Λ) ν.val) := hfinite ν.val
    have heq : weightSpan D (E D μ Λ) T = ⊤ := by
      rw [← htop]
      refine le_antisymm ?_ ?_
      · exact iSup_le fun ν : T => le_iSup (borelWeightSpace D (E D μ Λ)) ν.val
      · apply iSup_le
        intro ν
        by_cases hν : borelWeightSpace D (E D μ Λ) ν = ⊥
        · rw [hν]
          exact bot_le
        · exact le_iSup (fun i : T => borelWeightSpace D (E D μ Λ) i.val) ⟨ν, hb ν hν⟩
    have h := Submodule.finite_iSup (fun i : T => borelWeightSpace D (E D μ Λ) i.val)
    change FiniteDimensional ℂ (weightSpan D (E D μ Λ) T) at h
    rw [heq] at h
    let := h
    let e : E D μ Λ ≃ₗ[ℂ] (⊤ : Submodule ℂ (E D μ Λ)) := Submodule.topEquiv.symm
    exact FiniteDimensional.of_injective e.toLinearMap e.injective
  exact ⟨discarded_eq D μ Λ, hE,
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (borelWeight_independent D _) htop,
    fun ν _ => congrFun hm ν, hb, map_borelWeight D q (rawGenerator_weight D μ),
    generatorE_spans D μ Λ⟩

private theorem induced_spanned_by_units {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Module (U D.borel) V] (S : Submodule (U g) (Induced (inclusion D.borel) V))
    (hS : ∀ e : V, induceTensor (inclusion D.borel) 1 e ∈ S) : S = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨z, rfl⟩ := (balance (inclusion D.borel) V).mkQ_surjective x
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add]; exact S.add_mem hx hy
  | tmul a e =>
    change induceTensor (inclusion D.borel) a e ∈ S
    rw [← mul_one a, ← smul_tensor]
    exact S.smul_mem _ (hS e)

private theorem tensor_unit_weight {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Module (U D.borel) V] [IsScalarTower ℂ (U D.borel) V]
    (e : V) (η : D.Weight) (he : e ∈ borelWeightSpace D V η) :
    let Y := ModuleCat.of (U g) (Induced (inclusion D.borel) V)
    (induceTensor (inclusion D.borel) 1 e : Y) ∈ weightSpace D.cartan Y η := by
  let i := inclusion D.borel
  let Y := ModuleCat.of (U g) (Induced i V)
  apply (mem_weightSpace D.cartan Y η (induceTensor i 1 e)).mpr
  intro h
  have hh : i (ι ℂ (cartanInBorel D h)) = ι ℂ (h : g) :=
    BorelInduction.inclusion_ι D.borel (cartanInBorel D h)
  change (ι ℂ (h : g)) • induceTensor i 1 e = η h • (induceTensor i 1 e : Y)
  rw [smul_tensor, mul_one, ← hh, ← one_mul (i (ι ℂ (cartanInBorel D h))), balance_tensor,
    (mem_borelWeightSpace D _ _).mp he h]
  let q := (balance i V).mkQ.restrictScalars ℂ
  change q ((1 : U g) ⊗ₜ[ℂ] (η h • e)) = η h • q ((1 : U g) ⊗ₜ[ℂ] e)
  rw [TensorProduct.tmul_smul, map_smul]

private theorem generatorP_weight (μ Λ : D.Weight) :
    generatorP D μ Λ ∈ weightSpace D.cartan (P D μ Λ) μ :=
  tensor_unit_weight D _ μ
    (map_borelWeight D (discarded D μ Λ).mkQ (rawGenerator_weight D μ))

private theorem generatorP_spans (μ Λ : D.Weight) :
    Submodule.span (U g) {generatorP D μ Λ} = ⊤ := by
  apply induced_spanned_by_units
  intro e
  obtain ⟨a, rfl⟩ := (Submodule.span_singleton_eq_top_iff (U D.borel) _).mp (generatorE_spans D μ Λ) e
  change induceTensor (inclusion D.borel) 1 (a • generatorE D μ Λ) ∈ _
  rw [← balance_tensor, one_mul, ← mul_one (inclusion D.borel a), ← smul_tensor]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

private theorem exists_homogeneousBasis (μ Λ : D.Weight) (h : weightLE D μ Λ) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℂ (E D μ Λ)) (η : Fin n → D.Weight),
      ∀ i, b i ∈ borelWeightSpace D (E D μ Λ) (η i) ∧ weightLE D (η i) Λ := by
  obtain ⟨_, hfin, hi, _, hb, _, _⟩ := truncation D μ Λ h
  let V := E D μ Λ
  let W := borelWeightSpace D V
  let b (ν : D.Weight) : Basis (Fin (finrank ℂ (W ν))) ℂ (W ν) :=
    Module.finBasis ℂ (W ν)
  let B := hi.collectedBasis b
  let := Module.Finite.finite_basis B
  let := Fintype.ofFinite (Σ ν : D.Weight, Fin (finrank ℂ (W ν)))
  let e := Fintype.equivFin (Σ ν : D.Weight, Fin (finrank ℂ (W ν)))
  refine ⟨_, B.reindex e, fun i => (e.symm i).1, fun i => ?_⟩
  rw [Basis.reindex_apply]
  have hB : B (e.symm i) ∈ W (e.symm i).1 := hi.collectedBasis_mem b _
  refine ⟨hB, (hb _ ?_).2⟩
  intro hzero
  change borelWeightSpace D V (e.symm i).1 = ⊥ at hzero
  rw [show W (e.symm i).1 = ⊥ from hzero, Submodule.mem_bot] at hB
  exact B.ne_zero _ hB

set_option maxHeartbeats 900000 in
/-- The induction of the finite Borel truncation belongs to the specified cutoff. -/
theorem inCutoff : Expected.InCutoffType.{u} := by
  intro g _ _ _ D μ Λ h
  let I := positive D.cartan D.direction
  let : LinearOrder I := WellOrderingRel.isWellOrder.linearOrder
  let X := P D μ Λ
  obtain ⟨n, b, η, hb⟩ := exists_homogeneousBasis D μ Λ h
  obtain ⟨bNeg, hbNeg⟩ := exists_negative_basis D.cartan D.direction D.semisimple
  obtain ⟨F, hF⟩ := BorelInduction.inducedPBW D.nMinus D.borel (E := E D μ Λ)
    (cartan_borel D).2.2
  let B : Basis (OrderedWord I × Fin n) ℂ X := ((orderedBasis bNeg).tensorProduct b).map F
  let wt (p : OrderedWord I × Fin n) := η p.2 - wordRoot D.cartan D.direction p.1.val
  have hB (p : OrderedWord I × Fin n) : B p ∈ weightSpace D.cartan X (wt p) := by
    obtain ⟨l, j⟩ := p
    have hTensor : B (l, j) = induceTensor (inclusion D.borel)
        (inclusion D.nMinus (orderedMonomial bNeg l)) (b j) := by
      simp only [B, Basis.map_apply, Basis.tensorProduct_apply, orderedBasis_apply, hF]
    rw [hTensor]
    have hword (l : List I) : (l.map (fun a : I => -a.val)).sum =
        -wordRoot D.cartan D.direction l := by
      induction l with
      | nil => change (0 : D.Weight) = -0; rw [neg_zero]
      | cons a k ih =>
        change -a.val + (k.map (fun a : I => -a.val)).sum =
          -(a.val + wordRoot D.cartan D.direction k)
        rw [ih, neg_add]
    have h' := monomial_smul_weight D X bNeg (fun a => -a.val) hbNeg (η j)
      (induceTensor (inclusion D.borel) 1 (b j)) (tensor_unit_weight D (b j) (η j) (hb j).1) l.val
    rw [hword, ← sub_eq_add_neg, smul_tensor, mul_one] at h'
    exact h'
  have hi : DirectSum.IsInternal (weightSpace D.cartan X) := by
    refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (weightSpace_independent D X) (top_unique ?_)
    rw [← B.span_eq]
    exact Submodule.span_le.mpr (by
      rintro _ ⟨p, rfl⟩
      exact Submodule.mem_iSup_of_mem (wt p) (hB p))
  have hBounds := bounds_of_pbw_span D X η B B.span_eq hB
  have hspan := generatorP_spans D μ Λ
  have hfinite : Module.Finite (U g) X := by
    apply Module.Finite.of_fg_top
    rw [← hspan]
    exact Submodule.fg_span_singleton _
  refine ⟨⟨⟨hfinite, hi, local_finite_of_bounds D X hi hBounds⟩, ?_⟩,
    hspan, generatorP_weight D μ Λ, hBounds.1⟩
  intro ν hν
  have hfibre : {p | wt p = ν}.Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty] at hn
    apply hν
    change weightSpace D.cartan X ν = ⊥
    rw [weight_fibres D X B wt hB B.span_eq ν, hn, Set.image_empty, Submodule.span_empty]
  obtain ⟨⟨l, j⟩, (hEq : η j - wordRoot D.cartan D.direction l.val = ν)⟩ := hfibre
  apply _root_.LieAlgebrasAndRepresentations.HighestWeight.weightLE_trans D.alpha _ (hb j).2
  change η j - ν ∈ QPlus D
  rw [← hEq, sub_sub_cancel]
  exact wordRoot_mem_cone D.cartan D.direction D.semisimple l.val

private theorem eval_generator_injective (μ Λ : D.Weight) (X : ModuleCat.{v} (U g)) :
    Function.Injective (fun f : P D μ Λ →ₗ[U g] X => f (generatorP D μ Λ)) := by
  intro f k hk
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := (Submodule.span_singleton_eq_top_iff (U g) _).mp (generatorP_spans D μ Λ) x
  change f (generatorP D μ Λ) = k (generatorP D μ Λ) at hk
  rw [f.map_smul, k.map_smul, hk]

private theorem weight_representative (μ Λ : D.Weight) (X : Cutoff.{u, v} D Λ)
    (x : weightSpace D.cartan X.obj μ) :
    ∃ f : P D μ Λ →ₗ[U g] X.obj, f (generatorP D μ Λ) = x := by
  let := restrictedBorelAction D X.obj
  let := restrictedBorelTower D X.obj
  have hcompare (ν : D.Weight) :
      borelWeightSpace D X.obj ν = weightSpace D.cartan X.obj ν := by
    ext z
    rw [mem_borelWeightSpace, mem_weightSpace]
    apply forall_congr'
    intro h
    change inclusion D.borel (ι ℂ (cartanInBorel D h)) • z = ν h • z ↔ _
    rw [BorelInduction.inclusion_ι]
    rfl
  have hx : (x : X.obj) ∈ borelWeightSpace D X.obj μ := by
    rw [hcompare]
    exact x.property
  let L := rawLift D (x : X.obj) hx
  have hL : discarded D μ Λ ≤ L.ker := by
    intro y hy
    change y ∈ (discarded D μ Λ).restrictScalars ℂ at hy
    rw [discarded_eq] at hy
    change L y = 0
    have hle : weightSpan D (Raw D μ) {ν | ¬ weightLE D ν Λ} ≤
        (L.restrictScalars ℂ).ker := by
      apply iSup_le
      intro ν z hz
      have hw := map_borelWeight D L hz
      rw [hcompare] at hw
      have hbot : weightSpace D.cartan X.obj ν.val = ⊥ := by
        by_contra hne
        exact ν.property (X.property.2 ν.val hne)
      rw [hbot, Submodule.mem_bot] at hw
      exact hw
    exact hle hy
  let f := (discarded D μ Λ).liftQ L hL
  refine ⟨BorelInduction.extend (inclusion D.borel) f, ?_⟩
  change BorelInduction.extend (inclusion D.borel) f
    (induceTensor (inclusion D.borel) 1 (generatorE D μ Λ)) = x.val
  rw [BorelInduction.extend_tensor, one_smul]
  exact rawLift_generator D (x : X.obj) hx

/-- Evaluation at the distinguished generator represents the ordinary weight functor. -/
theorem represents : Expected.RepresentsType.{u, v} := by
  intro g _ _ _ D μ Λ _ X
  let L0 : (P D μ Λ →ₗ[U g] X.obj) →ₗ[ℂ] X.obj :=
    { toFun := fun f => f (generatorP D μ Λ)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let L := L0.codRestrict (weightSpace D.cartan X.obj μ) fun f =>
    (weightMap D f μ ⟨_, generatorP_weight D μ Λ⟩).property
  refine ⟨LinearEquiv.ofBijective L ⟨?_, ?_⟩, fun _ => rfl⟩
  · exact fun _ _ he => eval_generator_injective D μ Λ X.obj (congrArg Subtype.val he)
  · intro x
    obtain ⟨f, hf⟩ := weight_representative D μ Λ X x
    exact ⟨f, Subtype.ext hf⟩

private theorem weightMap_surjective {X Y : ModuleCat.{v} (U g)}
    (hX : DirectSum.IsInternal (weightSpace D.cartan X))
    (f : X →ₗ[U g] Y) (hf : Function.Surjective f) (ν : D.Weight) :
    Function.Surjective (weightMap D f ν) := by
  let := restrictedLieRingModule X (g := g)
  let := restrictedLieModule X (g := g)
  let := restrictedLieRingModule Y (g := g)
  let := restrictedLieModule Y (g := g)
  let fH : X →ₗ⁅ℂ,D.cartan⁆ Y :=
    { f.restrictScalars ℂ with
      map_lie' := fun {h x} => f.map_smul (ι ℂ (h : g)) x }
  exact WeightExactness.weightMap_surjective fH hX hf ν

set_option maxHeartbeats 800000 in
private theorem cutoff_epi_surjective (Λ : D.Weight) {X Y : Cutoff.{u, v} D Λ}
    (e : X ⟶ Y) [Epi e] : Function.Surjective e.hom.hom := by
  let S := LinearMap.range e.hom.hom
  let Z := ModuleCat.of (U g) (Y.obj ⧸ S)
  let q : Y.obj →ₗ[U g] Z := S.mkQ
  have hq : Function.Surjective q := S.mkQ_surjective
  let : Epi (ModuleCat.ofHom q) := (ModuleCat.epi_iff_surjective _).mpr hq
  have hzO : objects D Z := ObjectProperty.prop_of_epi (P := objects D)
    (ModuleCat.ofHom q) Y.property.1
  have hz : cutoffObjects D Λ Z := ⟨hzO, by
    intro ν hν
    apply Y.property.2 ν
    intro hzero
    apply hν
    apply bot_unique
    intro z hz
    obtain ⟨y, hy⟩ := weightMap_surjective D Y.property.1.2.1 q hq ν ⟨z, hz⟩
    have hyzero : (y : Y.obj) = 0 := (Submodule.mem_bot ℂ).mp (hzero ▸ y.property)
    have heq : q (y : Y.obj) = z := congrArg Subtype.val hy
    rw [hyzero, map_zero] at heq
    exact (Submodule.mem_bot ℂ).mpr heq.symm⟩
  let Z' : Cutoff D Λ := ⟨Z, hz⟩
  let q' : Y ⟶ Z' := ObjectProperty.homMk (ModuleCat.ofHom q)
  have hzero : q' = 0 := by
    apply (cancel_epi e).mp
    apply ObjectProperty.hom_ext (cutoffObjects D Λ)
    ext x
    change q (e.hom.hom x) = _
    change q (e.hom.hom x) = 0
    exact (Submodule.Quotient.mk_eq_zero S).mpr ⟨x, rfl⟩
  intro y
  have hqy : q y = 0 := by
    have h := congrArg (fun f : Y ⟶ Z' => f.hom.hom y) hzero
    exact h
  exact (Submodule.Quotient.mk_eq_zero S).mp hqy

/-- The representing object is projective in the full cutoff category. -/
theorem projective : Expected.ProjectiveType.{u} := by
  intro g _ _ _ D μ Λ h
  let hP := (inCutoff D μ Λ h).1
  refine ⟨hP, ⟨fun {Y X} f e _ => ?_⟩⟩
  let x := weightMap D f.hom.hom μ ⟨generatorP D μ Λ, generatorP_weight D μ Λ⟩
  obtain ⟨y, hy⟩ := weightMap_surjective D Y.property.1.2.1 e.hom.hom
    (cutoff_epi_surjective D Λ e) μ x
  obtain ⟨f', hf'⟩ := weight_representative D μ Λ Y y
  refine ⟨ObjectProperty.homMk (ModuleCat.ofHom f'), ?_⟩
  apply ObjectProperty.hom_ext (cutoffObjects D Λ)
  apply ModuleCat.hom_ext
  apply eval_generator_injective D μ Λ X.obj
  change e.hom.hom (f' (generatorP D μ Λ)) = f.hom.hom (generatorP D μ Λ)
  rw [hf']
  exact congrArg Subtype.val hy

private theorem direction_pos_of_cone {α : D.Weight} (hα : α ∈ QPlus D) (hn : α ≠ 0) :
    0 < D.direction α := by
  suffices hs : α = 0 ∨ 0 < D.direction α from hs.resolve_left hn
  clear hn
  change α ∈ Submodule.span ℕ (Set.range D.alpha) at hα
  induction hα using Submodule.span_induction with
  | mem α hα =>
    obtain ⟨i, rfl⟩ := hα
    exact Or.inr i.property.1.2
  | zero => exact Or.inl rfl
  | add a b _ _ ha hb =>
    rcases ha with rfl | ha
    · simpa only [zero_add] using hb
    rcases hb with rfl | hb
    · simpa only [add_zero] using Or.inr ha
    exact Or.inr (by rw [map_add]; exact add_pos ha hb)
  | smul n a _ ha =>
    rcases ha with rfl | ha
    · exact Or.inl (smul_zero _)
    by_cases hn : n = 0
    · exact Or.inl (hn ▸ zero_smul ℕ a)
    · exact Or.inr (by rw [map_nsmul]; exact nsmul_pos ha hn)

private theorem direction_lt_of_weightLE {ν ξ : D.Weight}
    (h : weightLE D ν ξ) (hn : ν ≠ ξ) : D.direction ν < D.direction ξ := by
  have hp := direction_pos_of_cone D h (sub_ne_zero.mpr hn.symm)
  rwa [map_sub, sub_pos] at hp

private theorem ordered_weights (μ Λ : D.Weight) (h : weightLE D μ Λ) :
    ∃ (n : ℕ) (ν : Fin n → D.Weight),
      Function.Injective ν ∧
      (∀ ξ, ξ ∈ Set.range ν ↔ borelWeightSpace D (E D μ Λ) ξ ≠ ⊥) ∧
      (∀ i j, D.direction (ν i) < D.direction (ν j) → j < i) := by
  obtain ⟨_, _, _, _, hb, _, _⟩ := truncation D μ Λ h
  let s : Set D.Weight := {ν | borelWeightSpace D (E D μ Λ) ν ≠ ⊥}
  have hs : s.Finite := (finiteUpward D {Λ} μ).subset (by
    intro ξ hξ
    exact ⟨(hb ξ hξ).1, Λ, Finset.mem_singleton_self Λ, (hb ξ hξ).2⟩)
  let le (a b : D.Weight) : Bool := decide (D.direction b ≤ D.direction a)
  let l := hs.toFinset.toList.mergeSort le
  have hperm : l.Perm hs.toFinset.toList := List.mergeSort_perm _ _
  have hpair : l.Pairwise (fun a b => D.direction b ≤ D.direction a) := by
    have hp : l.Pairwise (fun a b => le a b = true) := by
      apply List.pairwise_mergeSort
      · intro a b c ha hb
        exact decide_eq_true ((of_decide_eq_true hb).trans (of_decide_eq_true ha))
      · intro a b
        rw [Bool.or_eq_true]
        rcases le_total (D.direction b) (D.direction a) with h | h
        · exact Or.inl (decide_eq_true h)
        · exact Or.inr (decide_eq_true h)
    exact hp.imp (fun h => of_decide_eq_true h)
  refine ⟨l.length, l.get, (hperm.nodup_iff.mpr (Finset.nodup_toList _)).injective_get, ?_, ?_⟩
  · intro ξ
    change (∃ i : Fin l.length, l.get i = ξ) ↔ ξ ∈ s
    rw [← List.mem_iff_get, hperm.mem_iff, Finset.mem_toList, hs.mem_toFinset]
  · intro i j hlt
    by_contra! hn
    rcases lt_or_eq_of_le hn with hij | he
    · exact hlt.not_ge (hpair.rel_get_of_lt hij)
    · subst j
      exact lt_irrefl _ hlt

private theorem mem_initialWeights {n : ℕ} (ν : Fin n → D.Weight) (k : Fin (n + 1))
    (ξ : D.Weight) :
    ξ ∈ initialWeights D ν k ↔ ∃ i, i.val < k.val ∧ ν i = ξ := by
  simp [initialWeights]

private theorem initialSpace_le {μ Λ : D.Weight} {s t : Finset D.Weight} (h : s ⊆ t) :
    initialSpace D μ Λ s ≤ initialSpace D μ Λ t := by
  apply iSup_le
  intro ν
  exact le_iSup (fun ξ : (t : Set D.Weight) => borelWeightSpace D (E D μ Λ) ξ.val)
    ⟨ν.val, h ν.property⟩

private theorem initialSpace_succ {μ Λ : D.Weight} {n : ℕ} (ν : Fin n → D.Weight) (i : Fin n) :
    initialSpace D μ Λ (initialWeights D ν i.succ) =
      initialSpace D μ Λ (initialWeights D ν i.castSucc) ⊔ borelWeightSpace D (E D μ Λ) (ν i) := by
  apply le_antisymm
  · apply iSup_le
    intro ξ
    obtain ⟨j, hj, hjξ⟩ := (mem_initialWeights D ν i.succ ξ.val).mp ξ.property
    by_cases hij : j = i
    · subst j
      rw [← hjξ]
      exact le_sup_right
    · have hj' : j.val < i.castSucc.val := by
        have hn : j.val ≠ i.val := fun h => hij (Fin.ext h)
        change j.val < i.val + 1 at hj
        change j.val < i.val
        omega
      exact (le_iSup (fun k : (initialWeights D ν i.castSucc : Set D.Weight) =>
        borelWeightSpace D (E D μ Λ) k.val) ⟨ξ.val, (mem_initialWeights D ν _ _).mpr ⟨j, hj', hjξ⟩⟩).trans le_sup_left
  · apply sup_le
    · apply initialSpace_le
      intro ξ hξ
      obtain ⟨j, hj, rfl⟩ := (mem_initialWeights D ν _ _).mp hξ
      exact (mem_initialWeights D ν _ _).mpr ⟨j, Nat.lt_succ_of_lt hj, rfl⟩
    · exact le_iSup (fun ξ : (initialWeights D ν i.succ : Set D.Weight) =>
        borelWeightSpace D (E D μ Λ) ξ.val)
        ⟨ν i, (mem_initialWeights D ν _ _).mpr ⟨i, Nat.lt_succ_self _, rfl⟩⟩

private def initialBorelTerm {μ Λ : D.Weight} {n : ℕ} (ν : Fin n → D.Weight)
    (hs : ∀ ξ, ξ ∈ Set.range ν ↔ borelWeightSpace D (E D μ Λ) ξ ≠ ⊥)
    (horder : ∀ i j, D.direction (ν i) < D.direction (ν j) → j < i)
    (k : Fin (n + 1)) : Submodule (U D.borel) (E D μ Λ) :=
  weightSpanSubmodule D (E D μ Λ) (initialWeights D ν k : Set D.Weight) (by
    intro ξ hξ α hα hν
    obtain ⟨i, hi, rfl⟩ := (mem_initialWeights D ν k ξ).mp hξ
    by_cases hzero : α = 0
    · simpa [hzero] using hξ
    · obtain ⟨j, hj⟩ := (hs (ν i + α)).mpr hν
      have hj' : j < i := horder i j (by rw [hj, map_add]; exact lt_add_of_pos_right _ (direction_pos_of_cone D hα hzero))
      exact (mem_initialWeights D ν _ _).mpr ⟨j, (show j.val < i.val from hj').trans hi, hj⟩)

section InducedLayers

variable {V W : Type u} [AddCommGroup V] [Module ℂ V] [Module (U D.borel) V]
  [IsScalarTower ℂ (U D.borel) V]
  [AddCommGroup W] [Module ℂ W] [Module (U D.borel) W]
  [IsScalarTower ℂ (U D.borel) W]

private theorem induction_injective (f : V →ₗ[U D.borel] W) (hf : Function.Injective f) :
    Function.Injective (mapInduced (inclusion D.borel) f) := by
  let h := (cartan_borel D).2.2
  let F := inducedPBWEquiv D.nMinus D.borel (E := V) h
  let G := inducedPBWEquiv D.nMinus D.borel (E := W) h
  have hnat := pbwNaturality D.nMinus D.borel V f (mapInduced (inclusion D.borel) f)
    (mapInduced_tensor _ f) F G (inducedPBWEquiv_tensor D.nMinus D.borel h)
    (inducedPBWEquiv_tensor D.nMinus D.borel h)
  have hflat := Module.Flat.lTensor_preserves_injective_linearMap
    (M := U D.nMinus) (f.restrictScalars ℂ) hf
  intro x y hxy
  obtain ⟨x, rfl⟩ := F.surjective x
  obtain ⟨y, rfl⟩ := F.surjective y
  apply congrArg F
  apply hflat
  apply G.injective
  exact (LinearMap.congr_fun hnat x).symm.trans (hxy.trans (LinearMap.congr_fun hnat y))

private theorem induction_range (S : Submodule (U D.borel) V) :
    LinearMap.range (mapInduced (inclusion D.borel) S.subtype) =
      Submodule.span (U g) (induceTensor (inclusion D.borel) 1 '' (S : Set V)) := by
  let i := inclusion D.borel
  let f := mapInduced i S.subtype
  let T := Submodule.span (U g) (induceTensor i 1 '' (S : Set V))
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    suffices hin : T.comap f = ⊤ by
      change x ∈ T.comap f
      exact hin ▸ Submodule.mem_top
    apply induced_spanned_by_units
    intro z
    change f (induceTensor i 1 z) ∈ T
    rw [mapInduced_tensor]
    exact Submodule.subset_span ⟨z.val, z.property, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨induceTensor i 1 ⟨x, hx⟩, mapInduced_tensor _ _ _ _⟩

private theorem induced_layer (S T : Submodule (U D.borel) V) (hST : S ≤ T) :
    let A := LinearMap.range (mapInduced (inclusion D.borel) S.subtype)
    let B := LinearMap.range (mapInduced (inclusion D.borel) T.subtype)
    Nonempty ((B ⧸ A.comap B.subtype) ≃ₗ[U g]
      Induced (inclusion D.borel) (T ⧸ S.comap T.subtype)) := by
  dsimp only
  let i := inclusion D.borel
  let f := Submodule.inclusion hST
  let Q := S.comap T.subtype
  let q := Q.mkQ
  let F := mapInduced i f
  let G := mapInduced i q
  have hq : Function.Surjective q := Q.mkQ_surjective
  have hex : Function.Exact f q := by
    intro x
    change Submodule.Quotient.mk x = 0 ↔ x ∈ Set.range f
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hx
      exact ⟨⟨x.val, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact x.property
  obtain ⟨_, hFG, hG⟩ := BorelInduction.exactInduction D.nMinus D.borel S (cartan_borel D).2.2
    f q F G (mapInduced_tensor _ _) (mapInduced_tensor _ _)
    (Submodule.inclusion_injective hST) hex hq
  let J := mapInduced i T.subtype
  let K := mapInduced i S.subtype
  have hJK : J.comp F = K := by
    apply quotientExt i
    intro a s
    change J (F (induceTensor i a s)) = K (induceTensor i a s)
    simp only [J, F, K, mapInduced_tensor]
    rfl
  let e := LinearEquiv.ofInjective J (induction_injective D T.subtype T.injective_subtype)
  let G' := G.comp e.symm.toLinearMap
  have hG' : Function.Surjective G' := hG.comp e.symm.surjective
  have hKer : (LinearMap.range K).comap (LinearMap.range J).subtype = G'.ker := by
    ext z
    obtain ⟨y, rfl⟩ := e.surjective z
    have he : (e y).val = J y := rfl
    change J y ∈ LinearMap.range K ↔ G (e.symm (e y)) = 0
    rw [LinearEquiv.symm_apply_apply, hFG y]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (induction_injective D T.subtype T.injective_subtype)
        ((LinearMap.congr_fun hJK x).trans hx)⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, (LinearMap.congr_fun hJK x).symm⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ hKer).trans (G'.quotKerEquivOfSurjective hG')⟩

private theorem induce_scalar_character (ν : D.Weight) [FiniteDimensional ℂ V]
    (hV : ∀ (a : U D.borel) (x : V), a • x = character D ν a • x) :
    Nonempty (Induced (inclusion D.borel) V ≃ₗ[U g]
      (Fin (finrank ℂ V) → M D ν)) := by
  let := weightModule_value D.cartan D.direction (character D ν)
  let : IsScalarTower ℂ (U D.borel) ℂ := IsScalarTower.of_algebraMap_smul (fun c x => by
    change character D ν (algebraMap ℂ (U D.borel) c) * x = c * x
    rw [AlgHom.commutes, Algebra.algebraMap_self_apply])
  let b := Module.finBasis ℂ V
  let I := Fin (finrank ℂ V)
  let i := inclusion D.borel
  let q (j : I) : V →ₗ[U D.borel] ℂ :=
    { b.coord j with
      map_smul' := fun a x => by
        change b.coord j (a • x) = character D ν a * b.coord j x
        rw [hV, map_smul, smul_eq_mul] }
  obtain ⟨e, _⟩ := BorelInduction.finiteVerma D.cartan D.direction (character D ν)
  let F := inducedPBWEquiv D.nMinus D.borel (E := V) (cartan_borel D).2.2
  let G := inducedPBWEquiv D.nMinus D.borel (E := ℂ) (cartan_borel D).2.2
  let L : Induced i V →ₗ[U g] (I → M D ν) :=
    LinearMap.pi (fun j => e.toLinearMap.comp (mapInduced i (q j)))
  let eC : V ≃ₗ[ℂ] (I → ℂ) := b.equivFun
  let E1 := TensorProduct.congr (LinearEquiv.refl ℂ (U D.nMinus)) eC
  let E2 := TensorProduct.piRight ℂ ℂ (U D.nMinus) (fun _ : I => ℂ)
  let E3 : (I → U D.nMinus ⊗[ℂ] ℂ) ≃ₗ[ℂ] (I → M D ν) :=
    LinearEquiv.piCongrRight (fun _ => G.trans (e.restrictScalars ℂ))
  let K := E1.trans (E2.trans E3)
  have hLK : (L.restrictScalars ℂ).comp F.toLinearMap = K.toLinearMap := by
    apply TensorProduct.ext'
    intro a x
    funext j
    change e (mapInduced i (q j) (F (a ⊗ₜ[ℂ] x))) = (K (a ⊗ₜ[ℂ] x)) j
    rw [inducedPBWEquiv_tensor, mapInduced_tensor]
    have hK : (K (a ⊗ₜ[ℂ] x)) j = e (G (a ⊗ₜ[ℂ] q j x)) := by
      change e (G ((E2 (E1 (a ⊗ₜ[ℂ] x))) j)) = _
      rw [show E1 (a ⊗ₜ[ℂ] x) = a ⊗ₜ[ℂ] eC x from TensorProduct.congr_tmul _ _ _ _,
        TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
      rfl
    rw [hK, inducedPBWEquiv_tensor]
  have hLF (x) : L (F x) = K x := LinearMap.congr_fun hLK x
  refine ⟨LinearEquiv.ofBijective L ⟨?_, ?_⟩⟩
  · intro x y hxy
    obtain ⟨x, rfl⟩ := F.surjective x
    obtain ⟨y, rfl⟩ := F.surjective y
    rw [hLF, hLF] at hxy
    exact congrArg F (K.injective hxy)
  · intro y
    obtain ⟨x, rfl⟩ := K.surjective y
    exact ⟨F x, hLF x⟩

end InducedLayers

section BorelLayers

variable {V : Type u} [AddCommGroup V] [Module ℂ V] [Module (U D.borel) V]
  [IsScalarTower ℂ (U D.borel) V]

private theorem borel_layer (S T : Submodule (U D.borel) V) (ν : D.Weight)
    (hT : T.restrictScalars ℂ = S.restrictScalars ℂ ⊔ borelWeightSpace D V ν)
    (hdisj : Disjoint (borelWeightSpace D V ν) (S.restrictScalars ℂ))
    (hpos : ∀ (p : D.nPlus) (x : borelWeightSpace D V ν),
      ι ℂ (positiveInBorel D p) • (x : V) ∈ S) :
    ∃ _e : borelWeightSpace D V ν ≃ₗ[ℂ] (T ⧸ S.comap T.subtype),
      ∀ (a : U D.borel) (y : T ⧸ S.comap T.subtype), a • y = character D ν a • y := by
  let Q := S.comap T.subtype
  let q := Q.mkQ
  let W := borelWeightSpace D V ν
  have hWT : W ≤ T.restrictScalars ℂ := by rw [hT]; exact le_sup_right
  let j : W →ₗ[ℂ] T := Submodule.inclusion hWT
  let L := (q.restrictScalars ℂ).comp j
  have hLin : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    have hxq : Submodule.Quotient.mk (j x) = (0 : T ⧸ Q) := hx
    have hxS : (x : V) ∈ S := (Submodule.Quotient.mk_eq_zero Q).mp hxq
    apply (Submodule.mem_bot ℂ).mpr
    exact Subtype.ext ((Submodule.disjoint_def.mp hdisj) _ x.property hxS)
  have hLsur : Function.Surjective L := by
    intro z
    obtain ⟨y, rfl⟩ := Q.mkQ_surjective z
    have hy : (y : V) ∈ S.restrictScalars ℂ ⊔ W := by
      rw [← hT]
      exact y.property
    obtain ⟨s, hs, w, hw, heq⟩ := Submodule.mem_sup.mp hy
    use ⟨w, hw⟩
    let s' : T := ⟨s, by
      change s ∈ T.restrictScalars ℂ
      rw [hT]
      exact (le_sup_left : S.restrictScalars ℂ ≤ S.restrictScalars ℂ ⊔ W) hs⟩
    have heq' : s' + j ⟨w, hw⟩ = y := Subtype.ext heq
    change q (j ⟨w, hw⟩) = q y
    rw [← heq', map_add]
    rw [show q s' = 0 from (Submodule.Quotient.mk_eq_zero Q).mpr hs, zero_add]
  refine ⟨LinearEquiv.ofBijective L ⟨hLin, hLsur⟩, ?_⟩
  intro a y
  induction a using Shared.Lie.enveloping_induction ℂ D.borel generalizing y with
  | scalar c => rw [algebraMap_smul, AlgHom.commutes, Algebra.algebraMap_self_apply]
  | add a b ha hb => rw [add_smul, ha, hb, map_add, add_smul]
  | mul a b ha hb => rw [mul_smul, ha, hb, map_mul, mul_smul]
  | generator z =>
    obtain ⟨x, rfl⟩ := hLsur y
    rw [Shared.Lie.inclusion]
    have hz : (z : g) ∈ D.cartan.toSubmodule ⊔ D.nPlus.toSubmodule :=
      (cartan_borel D).1 ▸ z.property
    obtain ⟨h, hh, p, hp, he⟩ := Submodule.mem_sup.mp hz
    let h' : D.cartan := ⟨h, hh⟩
    let p' : D.nPlus := ⟨p, hp⟩
    have hz' : z = cartanInBorel D h' + positiveInBorel D p' := Subtype.ext he.symm
    have hχ := (character_unique D ν).1
    rw [hz', map_add (ι ℂ), add_smul, map_add (character D ν), hχ.1 h', hχ.2 p', add_zero]
    have hH : ι ℂ (cartanInBorel D h') • j x = ν h' • j x := by
      apply Subtype.ext
      exact (mem_borelWeightSpace D _ _).mp x.property h'
    have hP : ι ℂ (positiveInBorel D p') • L x = 0 := by
      change ι ℂ (positiveInBorel D p') • q (j x) = 0
      rw [← q.map_smul]
      exact (Submodule.Quotient.mk_eq_zero Q).mpr (hpos p' x)
    rw [hP, add_zero]
    change (ι ℂ (cartanInBorel D h')) • q (j x) = ν h' • q (j x)
    rw [← q.map_smul, hH]
    exact (q.restrictScalars ℂ).map_smul _ _

end BorelLayers

private theorem initial_pos_previous {μ Λ : D.Weight} {n : ℕ} (ν : Fin n → D.Weight)
    (hs : ∀ ξ, ξ ∈ Set.range ν ↔ borelWeightSpace D (E D μ Λ) ξ ≠ ⊥)
    (horder : ∀ i j, D.direction (ν i) < D.direction (ν j) → j < i)
    (i : Fin n) (p : D.nPlus) (x : borelWeightSpace D (E D μ Λ) (ν i)) :
    ι ℂ (positiveInBorel D p) • (x : E D μ Λ) ∈ initialBorelTerm D ν hs horder i.castSucc := by
  obtain ⟨b, hb⟩ := exists_positive_basis D
  let T : D.nPlus →ₗ[ℂ] E D μ Λ :=
    ((((Algebra.lsmul ℂ ℂ (E D μ Λ)).toLinearMap.comp (ι ℂ).toLinearMap).comp
      (positiveInBorel D).toLinearMap)).flip x.val
  let S := initialSpace D μ Λ (initialWeights D ν i.castSucc)
  have hle : (⊤ : Submodule ℂ D.nPlus) ≤ S.comap T := by
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    let ξ := ν i + -j.val
    have hweight := borel_root_smul D (E D μ Λ) (-j.val) (ν i) (b j) x.val (hb j) x.property
    change T (b j) ∈ S
    by_cases hbot : borelWeightSpace D (E D μ Λ) ξ = ⊥
    · change T (b j) ∈ borelWeightSpace D (E D μ Λ) ξ at hweight
      rw [hbot, Submodule.mem_bot] at hweight
      rw [hweight]
      exact S.zero_mem
    · obtain ⟨k, hk⟩ := (hs ξ).mpr hbot
      have hk' : k < i := horder i k (by
        rw [hk, show ξ = ν i + -j.val from rfl, map_add, map_neg]
        exact lt_add_of_pos_right _ (neg_pos.mpr (by
          have hj := j.property.2
          simpa only [LinearMap.neg_apply, neg_pos] using hj)))
      exact mem_weightSpan_of_weight D (E D μ Λ)
        ((mem_initialWeights D ν i.castSucc ξ).mpr ⟨k, hk', hk⟩) hweight
  exact hle (Submodule.mem_top (x := p))

set_option maxHeartbeats 1400000 in
/-- Full weight spaces in decreasing order induce the grouped Verma filtration. -/
theorem groupedFiltration : Expected.FiltrationType.{u} := by
  intro g _ _ _ D μ Λ h
  obtain ⟨_, hfin, hInt, _, hb, _, _⟩ := truncation D μ Λ h
  obtain ⟨n, ν, hν, hs, horder⟩ := ordered_weights D μ Λ h
  let iB := inclusion D.borel
  let V := E D μ Λ
  let B := initialBorelTerm D ν hs horder
  let A (k : Fin (n + 1)) : Submodule (U g) (P D μ Λ) :=
    LinearMap.range (mapInduced iB (B k).subtype)
  have hB (k) : (B k).restrictScalars ℂ = initialSpace D μ Λ (initialWeights D ν k) := rfl
  have hA (k) : A k = initialInduced D μ Λ (initialWeights D ν k) :=
    induction_range D (B k)
  have hmonoB : Monotone B := by
    intro j k hjk
    have hset : initialWeights D ν j ⊆ initialWeights D ν k := by
      intro ξ hξ
      obtain ⟨l, hl, rfl⟩ := (mem_initialWeights D ν j ξ).mp hξ
      exact (mem_initialWeights D ν k _).mpr ⟨l, hl.trans_le (show j.val ≤ k.val from hjk), rfl⟩
    change (B j).restrictScalars ℂ ≤ (B k).restrictScalars ℂ
    rw [hB j, hB k]
    exact initialSpace_le D hset
  have hmonoA : Monotone A := by
    intro j k hjk
    change LinearMap.range (mapInduced (inclusion D.borel) (B j).subtype) ≤
      LinearMap.range (mapInduced (inclusion D.borel) (B k).subtype)
    rw [induction_range D (B j), induction_range D (B k)]
    exact Submodule.span_mono (Set.image_mono (hmonoB hjk))
  have hzero : initialSpace D μ Λ (initialWeights D ν 0) = ⊥ := by
    apply bot_unique
    apply iSup_le
    intro ξ
    obtain ⟨j, hj, _⟩ := (mem_initialWeights D ν 0 ξ.val).mp ξ.property
    exact (Nat.not_lt_zero _ hj).elim
  have hend : initialSpace D μ Λ (initialWeights D ν (Fin.last n)) = ⊤ := by
    apply top_unique
    rw [← hInt.submodule_iSup_eq_top]
    apply iSup_le
    intro ξ
    by_cases hz : borelWeightSpace D V ξ = ⊥
    · rw [hz]
      exact bot_le
    · obtain ⟨j, hj⟩ := (hs ξ).mpr hz
      apply le_iSup_of_le (⟨ξ, (mem_initialWeights D ν (Fin.last n) ξ).mpr
        ⟨j, j.isLt, hj⟩⟩ : (initialWeights D ν (Fin.last n) : Set D.Weight))
      exact le_rfl
  refine ⟨{
    length := n
    weight := ν
    distinct := hν
    weights := hs
    bounded := fun j => hb _ ((hs _).mp ⟨j, rfl⟩)
    higher_first := fun j k hjk hne => horder j k
      (direction_lt_of_weightLE D hjk (fun he => hne (hν he)))
    borelTerm := B
    borel_initial := hB
    term := A
    induced_initial := hA
    induced_inclusion := fun k => ⟨mapInduced iB (B k).subtype,
      induction_injective D _ (B k).injective_subtype, rfl, mapInduced_tensor _ _⟩
    monotone := hmonoA
    first := ?_
    last := ?_
    factors := ?_ }⟩
  · rw [hA]
    apply bot_unique
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    change x ∈ initialSpace D μ Λ (initialWeights D ν 0) at hx
    rw [hzero, Submodule.mem_bot] at hx
    subst x
    simp [induceTensor]
  · apply induced_spanned_by_units
    intro e
    rw [hA]
    exact Submodule.subset_span ⟨e, by rw [hend]; exact Submodule.mem_top, rfl⟩
  · intro j
    let S := B j.castSucc
    let T := B j.succ
    have hST : S ≤ T := hmonoB (show j.castSucc ≤ j.succ from Nat.le_succ _)
    have hT : T.restrictScalars ℂ = S.restrictScalars ℂ ⊔ borelWeightSpace D V (ν j) := by
      rw [hB j.succ, hB j.castSucc]
      exact initialSpace_succ D ν j
    have hnot : ν j ∉ initialWeights D ν j.castSucc := by
      intro hmem
      obtain ⟨k, hk, he⟩ := (mem_initialWeights D ν j.castSucc (ν j)).mp hmem
      have he' : k = j := hν he
      subst k
      exact (lt_irrefl j.val) hk
    have hdisj : Disjoint (borelWeightSpace D V (ν j)) (S.restrictScalars ℂ) := by
      rw [hB j.castSucc, initialSpace, iSup_subtype'']
      exact (borelWeight_independent D V).disjoint_biSup hnot
    obtain ⟨e, he⟩ := borel_layer D S T (ν j) hT hdisj (initial_pos_previous D ν hs horder j)
    let Q := S.comap T.subtype
    let : FiniteDimensional ℂ V := hfin
    let : FiniteDimensional ℂ (T ⧸ Q) := FiniteDimensional.of_surjective e.toLinearMap e.surjective
    obtain ⟨F⟩ := induced_layer D S T hST
    obtain ⟨G⟩ := induce_scalar_character D (ν j) he
    have hdim : finrank ℂ (T ⧸ Q) = finrank ℂ (borelWeightSpace D V (ν j)) :=
      e.finrank_eq.symm
    exact ⟨F.trans (G.trans (LinearEquiv.piCongrLeft' (R := U g)
      (fun _ : Fin (finrank ℂ (T ⧸ Q)) => M D (ν j)) (finCongr hdim)))⟩

end RepTheorySurvey.CategoryO.TruncatedProjectives
