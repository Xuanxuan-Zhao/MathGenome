import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CentralActionHomotopy
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ModuleCasimir
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ChevalleyEilenbergExt
import MathGenome.Internal.AlgebraCore.P103.Ch10.Comparison

/-! LA-C03: comparison homotopy on the canonical CE free resolution.
The comparison theorem lifts through the formula-checked CE boundary,
using the augmented exactness and freeness proved in `CE.Ext.free_resolution`. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open CategoryTheory
open AdvancedHomologicalAlgebra.CE AdvancedHomologicalAlgebra.CE.Ext
open P103.Specs.Ch10.Comparison P103.Specs.Ch11.ExtTorDefinitions
universe u v w
namespace LieAlgebrasAndRepresentations.CentralActionHomotopy
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
  [Module.Free k g]

private abbrev ceChain :=
  chain k g (boundaryData k g).differential (boundaryData k g).augmented

/-- Central multiplication is a U-linear chain map. -/
def centralChain (C : U k g) (hC : C ∈ Subalgebra.center k (U k g)) :
    ceChain k g ⟶ ceChain k g where
  f n := ModuleCat.ofHom (centralLinear k g C hC (V k g n))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact ((ceChain k g).d i j).hom.map_smul C z

/-- The augmentation-zero chain map is compared to zero on the proved free
resolution. The comparison theorem includes the augmentation-degree lift. -/
def centralChainHomotopy (C : U k g) (hC : C ∈ Subalgebra.center k (U k g))
    (hε : Shared.Lie.augmentation k g C = 0) :
    Homotopy (centralChain k g C hC) 0 := by
  letI := trivialModule k g
  let D := boundaryData k g
  have hD := free_resolution.{u,v} k g D
  let P := resolution k g D.differential D.augmented hD.1
  have hP : P.IsProjective := by
    intro n
    change Module.Projective (U k g) (V k g n)
    let := hD.2 n
    infer_instance
  apply P103.Ch10.Comparison.chainNullHomotopy P P hP (centralChain k g C hC)
  apply LinearMap.ext
  intro z
  change V k g 0 at z
  change augmentation k g (C • z) = 0
  rw [D.augmented.2.2, hε, zero_mul]

/-- The components of the comparison homotopy in ordinary chain notation. -/
def chainHomotopyComponent (C : U k g) (hC : C ∈ Subalgebra.center k (U k g))
    (hε : Shared.Lie.augmentation k g C = 0) (n : ℕ) :
    V k g n →ₗ[U k g] V k g (n+1) :=
  ((centralChainHomotopy k g C hC hε).hom n (n+1)).hom

theorem chainHomotopyComponent_contraction (C : U k g)
    (hC : C ∈ Subalgebra.center k (U k g))
    (hε : Shared.Lie.augmentation k g C = 0) :
    ChainContraction k g C (chainHomotopyComponent k g C hC hε) := by
  let H := centralChainHomotopy k g C hC hε
  constructor
  · intro z
    have he := H.comm 0
    rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex] at he
    simp only [zero_add, HomologicalComplex.zero_f, add_zero] at he
    have hz := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom he) z
    exact hz.symm
  · intro n z
    have he := H.comm (n+1)
    rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at he
    simp only [HomologicalComplex.zero_f, add_zero] at he
    have hz := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom he) z
    simp only [ceChain, chain, ChainComplex.of_d] at hz
    exact (add_comm _ _).trans hz.symm

/-- Applying Hom gives H(F)=F ∘ h, with no signs. -/
theorem induced_contraction (C : U k g)
    (h : ∀ n, V k g n →ₗ[U k g] V k g (n+1))
    (hh : ChainContraction k g C h)
    (N : Type w) [AddCommGroup N] [Module (U k g) N] :
    InducedContraction k g C h N := by
  constructor
  · intro F z
    change F ((boundaryData k g).differential 0 (h 0 z)) = C • F z
    rw [hh.1, F.map_smul]
  · intro n F z
    let d := (boundaryData k g).differential
    change F (h n (d n z)) + F (d (n+1) (h (n+1) z)) = _
    rw [← map_add, add_comm (h n (d n z)) (d (n+1) (h (n+1) z)), hh.2, F.map_smul]

/-- Precomposition by central multiplication equals coefficient multiplication. -/
theorem homPreMap_centralChain (C : U k g)
    (hC : C ∈ Subalgebra.center k (U k g))
    (N : Type w) [AddCommGroup N] [Module (U k g) N] :
    homPreMap (centralChain k g C hC) N =
      homPostMap (ceChain k g) (centralLinear k g C hC N) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro F
  apply LinearMap.ext
  intro z
  exact F.map_smul C z

/-- The genuine cochain homotopy obtained by the contravariant Hom functor. -/
def coefficientHomotopy (C : U k g)
    (hC : C ∈ Subalgebra.center k (U k g))
    (hε : Shared.Lie.augmentation k g C = 0)
    (N : Type w) [AddCommGroup N] [Module (U k g) N] :
    Homotopy (homPostMap (ceChain k g) (centralLinear k g C hC N)) 0 := by
  have H := (homFunctor (R := U k g) N).mapHomotopy
    (centralChainHomotopy k g C hC hε).op
  change Homotopy (homPreMap (centralChain k g C hC) N)
    (homPreMap (0 : ceChain k g ⟶ ceChain k g) N) at H
  have hz : homPreMap (0 : ceChain k g ⟶ ceChain k g) N = 0 := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro F
    apply LinearMap.ext
    intro z
    exact F.map_zero
  rw [hz, homPreMap_centralChain] at H
  exact H

/-- The evaluation comparison carries the nullhomotopy to pointwise
multiplication on the exterior CE cochains with their formula-checked coboundary. -/
theorem exterior_coefficient_nullhomotopy (C : U k g)
    (hC : C ∈ Subalgebra.center k (U k g))
    (hε : Shared.Lie.augmentation k g C = 0)
    (N : Type w) [AddCommGroup N] [Module k N] [Module (U k g) N]
    [IsScalarTower k (U k g) N] :
    let D := boundaryData k g
    let E := cochainData k g N D
    let K := cochain k g N E.differential E.squared
    ∃ f : K ⟶ K,
      (∀ n (F : W k g n →ₗ[k] N) z, (f.f n).hom F z = C • F z) ∧
        Nonempty (Homotopy f 0) := by
  dsimp only
  let D := boundaryData k g
  let E := cochainData k g N D
  let e := evaluationIso k g N D.differential D.augmented E
  let f := e.inv ≫ homPostMap (ceChain k g) (centralLinear k g C hC N) ≫ e.hom
  refine ⟨f, ?_, ?_⟩
  · intro n F z
    let G := (e.inv.f n).hom F
    have hG : E.evaluation n G = F :=
      LinearMap.congr_fun (congrArg (fun a => (a.f n).hom) e.inv_hom_id) F
    change E.evaluation n ((centralLinear k g C hC N).comp G) z = C • F z
    rw [E.evaluate_tmul, ← hG, E.evaluate_tmul]
    rfl
  · exact ⟨by
      simpa only [f, Category.assoc, Limits.comp_zero, Limits.zero_comp] using
        (((coefficientHomotopy k g C hC hε N).compLeft e.inv).compRight e.hom)⟩

theorem central_nullhomotopy :
    Specs.LieAlgebrasAndRepresentations.CentralActionHomotopy.central_nullhomotopy_type.{u,v,w} := by
  intro k g _ _ _ _ C hC hε
  refine ⟨chainHomotopyComponent k g C hC hε,
    chainHomotopyComponent_contraction k g C hC hε, ?_⟩
  intro N _ _
  exact ⟨induced_contraction k g C _ (chainHomotopyComponent_contraction k g C hC hε) N,
    ⟨coefficientHomotopy k g C hC hε N⟩⟩

theorem module_casimir_nullhomotopy :
    Specs.LieAlgebrasAndRepresentations.CentralActionHomotopy.module_casimir_nullhomotopy_type.{u,v,w} := by
  intro k g M _ _ _ _ _ _ _ _ _ _ _ hg hM
  obtain ⟨C, hC⟩ := ModuleCasimir.exists_module_casimir k g M hg hM
  let := coefficientModule k g M
  obtain ⟨h, hh, hi⟩ := central_nullhomotopy.{u,v,w} k g C hC.1 hC.2.1
  refine ⟨C, hC, h, hh, (hi M).1, ?_, (hi M).2⟩
  intro n F z
  exact F.map_smul C z

end LieAlgebrasAndRepresentations.CentralActionHomotopy
