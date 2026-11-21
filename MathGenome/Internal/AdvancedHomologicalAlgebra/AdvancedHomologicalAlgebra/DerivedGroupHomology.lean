import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DerivedGroupHomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCoinvariants
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.RightBarHomologyComplex
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TorBalance
import MathGenome.Internal.AlgebraCore.P103.Ch10.HomologySequence
import MathGenome.Internal.AlgebraCore.P103.Ch11.TorExactSequences
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DerivedTorComparison
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import MathGenome.Internal.AlgebraCore.P103.Ch11.FlatResolutions

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped MonoidAlgebra
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch10.HomologySequence
namespace AdvancedHomologicalAlgebra.DerivedGroupHomology
universe u v w
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

@[simp] theorem barChain_d (n : ℕ) :
    ((barChain k G).d (n+1) n).hom = RightBar.boundary k G n := rfl

/-- Exact augmented right bar resolution, packaged for the classical Tor API. -/
def barResolution : LeftResolution k[G]ᵐᵒᵖ (GroupCoinvariants.TrivialRight k G) where
  complex := barChain k G
  ε := RightBar.rightAugmentation k G
  surjective := GroupBar.Large.augmentation_surjective.{u,v,0} k G
  exact_zero := by
    ext x
    exact (GroupBar.Large.exact_zero.{u,v,0} k G x).symm
  exact_succ n := by
    ext x
    exact (GroupBar.Large.exact_succ.{u,v,0} k G n x).symm

theorem barResolution_projective : (barResolution k G).IsProjective := by
  intro n
  change Module.Projective k[G]ᵐᵒᵖ (RightBar.B k G n)
  let := RightBar.degree_free k G n
  exact Module.Projective.of_free

def barChoice : ProjectiveChoice k[G]ᵐᵒᵖ (trivial k G) :=
  ⟨barResolution k G, barResolution_projective k G⟩

theorem rightBarResolution : Specification.ResolutionType := by
  intro k G _ _
  exact ⟨barResolution k G, rfl, barResolution_projective k G, HEq.rfl⟩

/-- Comparison on arbitrary projective choices, built from the actual two-variable Tor maps. -/
def resolutionTorIso (P Q : ProjectiveChoice k[G]ᵐᵒᵖ (trivial k G))
    (M : ModuleCat.{w} k[G]) (n : ℕ) : TorWith P.val M n ≃ₗ[ℤ] TorWith Q.val M n := by
  let E := (P103.Ch11.ExtTorDefinitions.theory.{max u v,u,w} k[G]).torMaps n
  refine LinearEquiv.ofLinearMap (E.map P Q (𝟙 _) (𝟙 M))
    (E.map Q P (𝟙 _) (𝟙 M)) ?_ ?_
  · simpa only [← E.comp, Category.id_comp] using E.id Q M
  · simpa only [← E.comp, Category.id_comp] using E.id P M

/-- Tor of the trivial right module is computed by the right bar resolution. -/
def torBarIso (M : ModuleCat.{w} k[G]) (n : ℕ) :
    GroupCoinvariants.GroupHomology k G M n ≃ₗ[ℤ] barHomology k G M n :=
  resolutionTorIso k G
    ((P103.Ch11.ExtTorDefinitions.theory.{max u v,u,w} k[G]).rightResolutions (trivial k G))
    (barChoice k G) M n

lemma tensorFirstMap_id (P : ProjectiveChoice k[G]ᵐᵒᵖ (trivial k G))
    (M : ModuleCat.{w} k[G]) : tensorFirstMap (𝟙 P.val.complex) M = 𝟙 _ :=
  P103.Ch11.TorExactSequences.tensorFirstMap_id P.val.complex M

lemma torMaps_coefficient (P : ProjectiveChoice k[G]ᵐᵒᵖ (trivial k G))
    {M N : ModuleCat.{w} k[G]} (f : M ⟶ N) (n : ℕ) :
    ((P103.Ch11.ExtTorDefinitions.theory.{max u v,u,w} k[G]).torMaps n).map P P (𝟙 _) f =
      homologyMap (tensorSecondMap P.val.complex f.hom) n := by
  have h := ((P103.Ch11.ExtTorDefinitions.theory.{max u v,u,w} k[G]).torMaps n).formula
    P P (𝟙 _) f (𝟙 P.val.complex) (by ext; rfl)
  simpa only [tensorFirstMap_id, Category.id_comp] using h

lemma torBarIso_natural {M N : ModuleCat.{w} k[G]} (f : M ⟶ N) (n : ℕ) z :
    torBarIso k G N n ((homologyFunctor k G n).map f z) =
      barHomologyMap k G f n (torBarIso k G M n z) := by
  let E := (P103.Ch11.ExtTorDefinitions.theory.{max u v,u,w} k[G]).torMaps n
  let P := (P103.Ch11.ExtTorDefinitions.theory.{max u v,u,w} k[G]).rightResolutions (trivial k G)
  let Q := barChoice k G
  have h := E.comp P P Q (𝟙 _) (𝟙 _) f (𝟙 N)
  have h' := E.comp P Q Q (𝟙 _) (𝟙 _) (𝟙 M) f
  simp only [Category.id_comp, Category.comp_id] at h h'
  have he : (E.map P Q (𝟙 _) (𝟙 N)).comp (E.map P P (𝟙 _) f) =
      (E.map Q Q (𝟙 _) f).comp (E.map P Q (𝟙 _) (𝟙 M)) := h.symm.trans h'
  rw [show barHomologyMap k G f n = E.map Q Q (𝟙 _) f from
    (torMaps_coefficient k G Q f n).symm]
  exact LinearMap.congr_fun he z

/-- The augmented comparison from the chosen right resolution to the bar resolution. -/
def barComparisonLift : (canonicalResolution k G).val.complex ⟶ barChain k G :=
  P103.Ch10.Comparison.chainMap (canonicalResolution k G).val (barChoice k G).val
    (canonicalResolution k G).property LinearMap.id

lemma barComparisonLift_lifts :
    ChainLift (canonicalResolution k G).val (barChoice k G).val LinearMap.id
      (barComparisonLift k G) :=
  P103.Ch10.Comparison.chainMap_lifts _ _ _ _

lemma torBarIso_eq_homologyMap (M : ModuleCat.{w} k[G]) (n : ℕ) :
    (torBarIso k G M n).toLinearMap =
      homologyMap (tensorFirstMap (barComparisonLift k G) M) n := by
  let E := (P103.Ch11.ExtTorDefinitions.theory.{max u v,u,w} k[G]).torMaps n
  change E.map (canonicalResolution k G) (barChoice k G) (𝟙 _) (𝟙 M) = _
  simpa only [ModuleCat.hom_id, P103.Ch11.TorExactSequences.tensorSecondMap_id,
    Category.comp_id] using
    E.formula (canonicalResolution k G) (barChoice k G) (𝟙 _) (𝟙 M)
      (barComparisonLift k G) (barComparisonLift_lifts k G)

/-- A comparison of the two augmented resolutions induces the prescribed map. -/
theorem torBarCoordinates : BarCoordinates.{u,v,w} k G (torBarIso k G) := by
  refine ⟨barChoice k G, rfl, HEq.rfl, barComparisonLift k G, barComparisonLift_lifts k G, ?_⟩
  intro M n
  simpa only [eqToHom_refl, Category.comp_id] using torBarIso_eq_homologyMap k G M n

theorem barComparison : Specification.BarComparisonType := by
  intro k G _ _
  exact ⟨torBarIso k G, torBarCoordinates k G, torBarIso_natural k G⟩

/-- The right augmentation induces the same degree-zero map on both resolutions. -/
lemma torBarAugmentation_zero (M : ModuleCat.{w} k[G]) (z : GroupCoinvariants.GroupHomology k G M 0) :
    P103.Ch11.ExtTorDefinitions.torZero (barResolution k G) M (torBarIso k G M 0 z) =
      torZero k G M z := by
  let P := (canonicalResolution k G).val
  let Q := barResolution k G
  have h := P103.Ch11.ExtTorDefinitions.tor_zero_natural k[G]
    (trivial k G) (trivial k G) P Q M M LinearMap.id LinearMap.id
    (barComparisonLift k G) (barComparisonLift_lifts k G)
    (P103.Ch11.ExtTorDefinitions.torZero P M)
    (P103.Ch11.ExtTorDefinitions.torZero Q M)
    (P103.Ch11.ExtTorDefinitions.torZero_class P M)
    (P103.Ch11.ExtTorDefinitions.torZero_class Q M) z
  have hid : tensorMap (LinearMap.id : trivial k G →ₗ[k[G]ᵐᵒᵖ] trivial k G)
      (LinearMap.id : M →ₗ[k[G]] M) = LinearMap.id := by
    apply tensor_hom_ext
    intro a m
    rfl
  have hc := LinearMap.congr_fun (torBarIso_eq_homologyMap k G M 0) z
  change torBarIso k G M 0 z = homologyMap (tensorFirstMap (barComparisonLift k G) M) 0 z at hc
  rw [hc]
  change P103.Ch11.ExtTorDefinitions.torZero Q M _ = P103.Ch11.ExtTorDefinitions.torZero P M z
  simp only [P103.Ch11.TorExactSequences.tensorSecondMap_id, Category.comp_id,
    hid, LinearMap.id_apply] at h
  exact h

/-- Degree zero with its canonical tensor augmentation followed by the inverse
of [m] ↦ 1 tensor m. -/
def zeroIso (M : ModuleCat.{w} k[G]) :
    GroupCoinvariants.GroupHomology k G M 0 ≃+ GroupCoinvariants.Coinvariants k G M :=
  (P103.Ch11.ExtTorDefinitions.torZero
    ((P103.Ch11.ExtTorDefinitions.theory.{max u v,u,w} k[G]).rightResolutions (trivial k G)).val M).trans
      (GroupCoinvariants.coinvariantTensorIso M).symm.toAddEquiv

lemma zeroIso_natural {M N : ModuleCat.{w} k[G]} (f : M ⟶ N) z :
    zeroIso k G N ((homologyFunctor k G 0).map f z) =
      GroupCoinvariants.coinvariantsMap k G f (zeroIso k G M z) := by
  let P := (P103.Ch11.ExtTorDefinitions.theory.{max u v,u,w} k[G]).rightResolutions (trivial k G)
  have h := P103.Ch11.ExtTorDefinitions.tor_zero_natural k[G]
    (trivial k G) (trivial k G) P.val P.val M N LinearMap.id f.hom
    (𝟙 P.val.complex) (by ext; rfl)
    (P103.Ch11.ExtTorDefinitions.torZero P.val M)
    (P103.Ch11.ExtTorDefinitions.torZero P.val N)
    (P103.Ch11.ExtTorDefinitions.torZero_class P.val M)
    (P103.Ch11.ExtTorDefinitions.torZero_class P.val N) z
  simp only [tensorFirstMap_id, Category.id_comp] at h
  apply (GroupCoinvariants.coinvariantTensorIso N).injective
  rw [GroupCoinvariants.coinvariantTensorIso_natural]
  change (GroupCoinvariants.coinvariantTensorIso N)
      ((GroupCoinvariants.coinvariantTensorIso N).symm
        (P103.Ch11.ExtTorDefinitions.torZero P.val N ((homologyFunctor k G 0).map f z))) =
    P103.BalancedTensor.map LinearMap.id f.hom
      ((GroupCoinvariants.coinvariantTensorIso M)
        ((GroupCoinvariants.coinvariantTensorIso M).symm
          (P103.Ch11.ExtTorDefinitions.torZero P.val M z)))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  change P103.Ch11.ExtTorDefinitions.torZero P.val N
    (((P103.Ch11.ExtTorDefinitions.theory.{max u v,u,w} k[G]).torMaps 0).map P P (𝟙 _) f z) = _
  rw [torMaps_coefficient k G P f 0, ← P103.Ch11.ExtTorDefinitions.tensorMap_eq]
  exact h

lemma zeroCoordinates : CoinvariantCoordinates.{u,v,w} k G (fun M z => zeroIso k G M z) := by
  intro M a m
  change (GroupCoinvariants.coinvariantTensorIso M).symm
    (torZero k G M ((torZero k G M).symm (P103.BalancedTensor.tmul k[G] a m))) = _
  rw [AddEquiv.apply_symm_apply, GroupCoinvariants.coinvariantTensorIso_symm_tmul]

theorem degreeZero : Specification.ZeroType := by
  intro k G _ _
  exact ⟨zeroIso k G, zeroCoordinates k G, zeroIso_natural k G⟩

/-- Tensoring a coefficient short exact sequence with a projective right
resolution is exact in every degree. -/
lemma resolution_degreewise_exact (P : ProjectiveChoice k[G]ᵐᵒᵖ (trivial k G))
    (S : ShortComplex (ModuleCat.{w} k[G])) (hS : S.ShortExact) :
    DegreewiseExact (tensorSecondMap P.val.complex S.f.hom)
      (tensorSecondMap P.val.complex S.g.hom) := by
  intro n
  have he : Function.Exact S.f.hom S.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  refine ⟨P103.Ch11.TorBalance.right_projective_tensor_injective (P.property n) S.f.hom
    hS.moduleCat_injective_f, ?_⟩
  exact P103.HomTensorExactness.tensorSecond_rightExact S.f.hom S.g.hom he
    hS.moduleCat_surjective_g
    (tensorMap (LinearMap.id : P.val.complex.X n →ₗ[k[G]ᵐᵒᵖ] _) S.f.hom).toAddMonoidHom
    (tensorMap LinearMap.id S.g.hom).toAddMonoidHom (fun _ _ => rfl) (fun _ _ => rfl)

lemma coefficient_degreewise_exact (S : ShortComplex (ModuleCat.{w} k[G]))
    (hS : S.ShortExact) : DegreewiseExact (chainMap k G S.f) (chainMap k G S.g) :=
  resolution_degreewise_exact k G (barChoice k G) S hS

lemma tor_degreewise_exact (S : ShortComplex (ModuleCat.{w} k[G])) (hS : S.ShortExact) :
    DegreewiseExact (torChainMap k G S.f) (torChainMap k G S.g) :=
  resolution_degreewise_exact k G (canonicalResolution k G) S hS

/-- The positive, lift-and-boundary connecting map on the actual bar homology. -/
def barBoundary (S : ShortComplex (ModuleCat.{w} k[G])) (hS : S.ShortExact) (n : ℕ) :
    barHomology k G S.X₃ (n+1) →ₗ[ℤ] barHomology k G S.X₁ n :=
  Classical.choose (P103.Ch10.HomologySequence.sequence
    (chainMap k G S.f) (chainMap k G S.g) (coefficient_degreewise_exact k G S hS)
    (n+1) n (by rfl))

lemma barBoundary_spec (S : ShortComplex (ModuleCat.{w} k[G])) (hS : S.ShortExact) (n : ℕ) :
    P103.Specs.Ch10.HomologySequence.Connecting
      (chainMap k G S.f) (chainMap k G S.g) (n+1) n (barBoundary k G S hS n) ∧
    P103.Specs.Ch10.HomologySequence.SequenceExact
      (chainMap k G S.f) (chainMap k G S.g) (n+1) n (barBoundary k G S hS n) :=
  (Classical.choose_spec (P103.Ch10.HomologySequence.sequence
    (chainMap k G S.f) (chainMap k G S.g) (coefficient_degreewise_exact k G S hS)
    (n+1) n (by rfl))).1

lemma chainMap_comp {L M N : ModuleCat.{w} k[G]} (f : L ⟶ M) (g : M ⟶ N) :
    chainMap k G (f ≫ g) = chainMap k G f ≫ chainMap k G g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  rfl

lemma barBoundary_natural (S T : ShortComplex (ModuleCat.{w} k[G]))
    (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T) (n : ℕ) :
    (barHomologyMap k G f.τ₁ n).comp (barBoundary k G S hS n) =
      (barBoundary k G T hT n).comp (barHomologyMap k G f.τ₃ (n+1)) := by
  have hi : chainMap k G S.f ≫ chainMap k G f.τ₂ =
      chainMap k G f.τ₁ ≫ chainMap k G T.f := by
    rw [← chainMap_comp, ← chainMap_comp, f.comm₁₂]
  have hp : chainMap k G S.g ≫ chainMap k G f.τ₃ =
      chainMap k G f.τ₂ ≫ chainMap k G T.g := by
    rw [← chainMap_comp, ← chainMap_comp, f.comm₂₃]
  exact (P103.Ch10.HomologySequence.naturality
    (chainMap k G S.f) (chainMap k G S.g) (chainMap k G T.f) (chainMap k G T.g)
    (chainMap k G f.τ₁) (chainMap k G f.τ₂) (chainMap k G f.τ₃) hi hp
    (coefficient_degreewise_exact k G S hS) (coefficient_degreewise_exact k G T hT)
    (n+1) n (by rfl) (barBoundary k G S hS n) (barBoundary k G T hT n)
    (barBoundary_spec k G S hS n).1 (barBoundary_spec k G T hT n).1).2.2.1

theorem barCoefficientSequence : Specification.BarSequenceType := by
  intro k G _ _
  exact ⟨coefficient_degreewise_exact k G, barBoundary k G,
    barBoundary_spec k G, barBoundary_natural k G⟩

lemma tensor_differential (M : ModuleCat.{w} k[G]) (n : ℕ)
    (z : RightBar.TensorChains k G M (n+1)) :
    ((chains k G M).d (n+1) n).hom z = RightBar.tensorBoundary k G M n z := by
  induction z using P103.BalancedTensor.induction_on with
  | h0 => exact (map_zero ((chains k G M).d (n+1) n).hom).trans ((map_zero (RightBar.tensorBoundary k G M n)).symm)
  | ht b m => rfl
  | ha z w hz hw => simp only [map_add, hz, hw]

theorem explicitModel : Specification.ExplicitModelType :=
  ⟨RightBar.barModel, tensor_differential⟩

/-- The positive connecting map on the tensor complex of the chosen right resolution. -/
def coefficientBoundary (S : ShortComplex (ModuleCat.{w} k[G])) (hS : S.ShortExact) (n : ℕ) :
    GroupCoinvariants.GroupHomology k G S.X₃ (n+1) →ₗ[ℤ]
      GroupCoinvariants.GroupHomology k G S.X₁ n :=
  Classical.choose (P103.Ch10.HomologySequence.sequence (torChainMap k G S.f)
    (torChainMap k G S.g) (tor_degreewise_exact k G S hS) (n+1) n rfl)

lemma coefficientBoundary_spec (S : ShortComplex (ModuleCat.{w} k[G]))
    (hS : S.ShortExact) (n : ℕ) :
    Connecting (torChainMap k G S.f) (torChainMap k G S.g) (n+1) n
      (coefficientBoundary k G S hS n) ∧
    SequenceExact (torChainMap k G S.f) (torChainMap k G S.g) (n+1) n
      (coefficientBoundary k G S hS n) :=
  (Classical.choose_spec (P103.Ch10.HomologySequence.sequence (torChainMap k G S.f)
    (torChainMap k G S.g) (tor_degreewise_exact k G S hS) (n+1) n rfl)).1

lemma coefficientBoundary_tor_connecting (S : ShortComplex (ModuleCat.{w} k[G]))
    (hS : S.ShortExact) (n : ℕ) :
    Connecting (torChainMap k G S.f) (torChainMap k G S.g) (n+1) n
      (coefficientBoundary k G S hS n) :=
  (coefficientBoundary_spec k G S hS n).1

lemma barComparisonLift_natural {M N : ModuleCat.{w} k[G]} (f : M ⟶ N) :
    torChainMap k G f ≫ tensorFirstMap (barComparisonLift k G) N =
      tensorFirstMap (barComparisonLift k G) M ≫ chainMap k G f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  rfl

@[simp] lemma torBarIso_boundary (S : ShortComplex (ModuleCat.{w} k[G]))
    (hS : S.ShortExact) (n : ℕ) z :
    torBarIso k G S.X₁ n (coefficientBoundary k G S hS n z) =
      barBoundary k G S hS n (torBarIso k G S.X₃ (n+1) z) := by
  have h := (P103.Ch10.HomologySequence.naturality
    (torChainMap k G S.f) (torChainMap k G S.g) (chainMap k G S.f) (chainMap k G S.g)
    (tensorFirstMap (barComparisonLift k G) S.X₁) (tensorFirstMap (barComparisonLift k G) S.X₂)
    (tensorFirstMap (barComparisonLift k G) S.X₃)
    (barComparisonLift_natural k G S.f) (barComparisonLift_natural k G S.g)
    (tor_degreewise_exact k G S hS) (coefficient_degreewise_exact k G S hS)
    (n+1) n rfl (coefficientBoundary k G S hS n) (barBoundary k G S hS n)
    (coefficientBoundary_tor_connecting k G S hS n) (barBoundary_spec k G S hS n).1).2.2.1
  rw [← torBarIso_eq_homologyMap, ← torBarIso_eq_homologyMap] at h
  exact LinearMap.congr_fun h z

lemma homologyFunctor_map_hom {M N : ModuleCat.{w} k[G]} (f : M ⟶ N) (n : ℕ) :
    ((homologyFunctor k G n).map f).hom = homologyMap (torChainMap k G f) n :=
  torMaps_coefficient k G (canonicalResolution k G) f n

lemma coefficientBoundary_exact (S : ShortComplex (ModuleCat.{w} k[G]))
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact ((homologyFunctor k G (n+1)).map S.f)
      ((homologyFunctor k G (n+1)).map S.g) ∧
    Function.Exact ((homologyFunctor k G (n+1)).map S.g) (coefficientBoundary k G S hS n) ∧
    Function.Exact (coefficientBoundary k G S hS n) ((homologyFunctor k G n).map S.f) := by
  change Function.Exact (((homologyFunctor k G (n+1)).map S.f).hom)
      (((homologyFunctor k G (n+1)).map S.g).hom) ∧
    Function.Exact (((homologyFunctor k G (n+1)).map S.g).hom) (coefficientBoundary k G S hS n) ∧
    Function.Exact (coefficientBoundary k G S hS n) (((homologyFunctor k G n).map S.f).hom)
  simp only [homologyFunctor_map_hom]
  exact (coefficientBoundary_spec k G S hS n).2

lemma coefficientBoundary_natural (S T : ShortComplex (ModuleCat.{w} k[G]))
    (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T) (n : ℕ) :
    ((homologyFunctor k G n).map f.τ₁).hom.comp (coefficientBoundary k G S hS n) =
      (coefficientBoundary k G T hT n).comp ((homologyFunctor k G (n+1)).map f.τ₃).hom := by
  apply LinearMap.ext
  intro z
  apply (torBarIso k G T.X₁ n).injective
  change torBarIso k G T.X₁ n ((homologyFunctor k G n).map f.τ₁
    (coefficientBoundary k G S hS n z)) =
      torBarIso k G T.X₁ n (coefficientBoundary k G T hT n
        ((homologyFunctor k G (n+1)).map f.τ₃ z))
  rw [torBarIso_natural, torBarIso_boundary, torBarIso_boundary, torBarIso_natural]
  exact LinearMap.congr_fun (barBoundary_natural k G S T hS hT f n) _

lemma coefficientBoundary_connecting (S : ShortComplex (ModuleCat.{w} k[G]))
    (hS : S.ShortExact) (n : ℕ) :
    P103.Specs.Ch10.HomologySequence.Connecting
      (chainMap k G S.f) (chainMap k G S.g) (n+1) n
      ((torBarIso k G S.X₁ n).toLinearMap.comp ((coefficientBoundary k G S hS n).comp
        (torBarIso k G S.X₃ (n+1)).symm.toLinearMap)) := by
  have he : (torBarIso k G S.X₁ n).toLinearMap.comp ((coefficientBoundary k G S hS n).comp
      (torBarIso k G S.X₃ (n+1)).symm.toLinearMap) = barBoundary k G S hS n := by
    ext z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, torBarIso_boundary,
      LinearEquiv.apply_symm_apply]
  rw [he]
  exact (barBoundary_spec k G S hS n).1

theorem coefficientSequence : Specification.CoefficientSequenceType := by
  intro k G _ _
  refine ⟨torBarIso k G, coefficientBoundary k G, torBarCoordinates k G, torBarIso_natural k G, ?_,
    coefficientBoundary_natural k G, ?_⟩
  · intro S hS n
    exact ⟨tor_degreewise_exact k G S hS, coefficientBoundary_tor_connecting k G S hS n,
      coefficientBoundary_connecting k G S hS n, coefficientBoundary_exact k G S hS n⟩
  · intro S hS
    exact GroupCoinvariants.coinvariants_rightExact S.f S.g
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
      hS.moduleCat_surjective_g

/-- The canonical coinvariant/tensor identification as an isomorphism of
functors in the left coefficient variable. -/
def coinvariantTensorFunctorIso : coinvariantGroups k G ≅ tensorCoefficients k G :=
  NatIso.ofComponents
    (fun M => ((ULift.moduleEquiv : ULift.{u} (GroupCoinvariants.Coinvariants k G M) ≃ₗ[k]
      GroupCoinvariants.Coinvariants k G M).toAddEquiv.trans
        (GroupCoinvariants.coinvariantTensorIso M).toAddEquiv).toIntLinearEquiv.toModuleIso)
    (by
      intro M N f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      have h := GroupCoinvariants.coinvariantTensorIso_natural f (show ULift.{u} _ from z).down
      rw [← P103.Ch11.ExtTorDefinitions.tensorMap_eq] at h
      exact h)

theorem tensorFunctorComparison : Specification.TensorFunctorType := by
  intro k G _ _
  refine ⟨coinvariantTensorFunctorIso k G, ?_⟩
  intro M a m
  exact GroupCoinvariants.coinvariantTensorIso_symm_tmul M a m

lemma tensorIso_natural {M N : ModuleCat.{w} k[G]} (f : M ⟶ N) (n : ℕ)
    (z : RightBar.TensorChains k G M n) :
    RightBar.tensorIso k G N n (((chainMap k G f).f n).hom z) =
      directSumMap k G f n (RightBar.tensorIso k G M n z) := by
  obtain ⟨x, rfl⟩ := (RightBar.tensorIso k G M n).symm.surjective z
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single g m =>
    rw [RightBar.tensorIso_symm_single]
    change RightBar.tensorIso k G N n
      (P103.BalancedTensor.tmul k[G]
        ((RightBar.untwist k G _).symm (GroupBar.Large.single.{u,v,0} k G (RightBar.barTuple G g) 1))
        (f.hom (RestrictScalars.addEquiv k k[G] M m))) = _
    rw [show f.hom (RestrictScalars.addEquiv k k[G] M m) =
      RestrictScalars.addEquiv k k[G] N (coefficientLinearMap k G f m) from rfl]
    rw [RightBar.tensorIso_symbol, ← RightBar.tensorIso_symm_single,
      LinearEquiv.apply_symm_apply]
    simp [directSumMap, Finsupp.mapRange.linearMap]

theorem naturalExplicitModel : Specification.NaturalExplicitType := by
  intro k G _ _
  refine ⟨RightBar.tensorIso k G, RightBar.tensorIso_symbol k G, tensorIso_natural k G, ?_⟩
  intro M n g m
  rw [tensor_differential, ← RightBar.chainBoundary_tensorIso, LinearEquiv.apply_symm_apply]
  exact RightBar.chainBoundary_single k G M n g m

section Scalars

open scoped ModuleCat.Algebra

local instance coefficientRepresentationLinear :
    (Rep.ofModuleMonoidAlgebra (k := k) (G := G) :
      ModuleCat.{w} k[G] ⥤ Rep.{w} k G).Linear k where
  map_smul _ _ := by
    ext x
    rfl

instance coinvariantsLinear : (GroupCoinvariants.coinvariantsFunctor k G :
    ModuleCat.{w} k[G] ⥤ ModuleCat.{w} k).Linear k := by
  unfold GroupCoinvariants.coinvariantsFunctor
  infer_instance

/-- The zeroth comparison also preserves the central k-action on Tor. -/
def zeroLinearIso (M : ModuleCat.{w} k[G]) :
    (kHomologyFunctor k G 0).obj M ≅
      (GroupCoinvariants.coinvariantsFunctor k G ⋙ ModuleCat.uliftFunctor.{max u v,w} k).obj M := by
  letI := torModule k G M 0
  let e : GroupCoinvariants.GroupHomology k G M 0 ≃ₗ[k] GroupCoinvariants.Coinvariants k G M :=
    { zeroIso k G M with map_smul' := ?_ }
  · exact (e.trans ULift.moduleEquiv.symm).toModuleIso
  intro r z
  have h := zeroIso_natural k G (scalarCoefficientMap k G M r) z
  change zeroIso k G M (r • z) =
    ((GroupCoinvariants.coinvariantsFunctor k G).map (r • 𝟙 M)) (zeroIso k G M z) at h
  have hs : (GroupCoinvariants.coinvariantsFunctor k G).map (r • 𝟙 M) =
      r • 𝟙 ((GroupCoinvariants.coinvariantsFunctor k G).obj M) := by
    rw [Functor.map_smul, (GroupCoinvariants.coinvariantsFunctor k G).map_id M]
  exact h.trans (ConcreteCategory.congr_hom hs
    (show (GroupCoinvariants.coinvariantsFunctor k G).obj M from zeroIso k G M z))

/-- The scalar-linear degree-zero identification on the original coefficients. -/
def zeroNatIso : kHomologyFunctor.{u,v,w} k G 0 ≅
    GroupCoinvariants.coinvariantsFunctor k G ⋙ ModuleCat.uliftFunctor.{max u v,w} k :=
  NatIso.ofComponents (fun M => zeroLinearIso k G M) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change ULift.up (zeroIso k G N ((homologyFunctor k G 0).map f z)) =
      ULift.up (GroupCoinvariants.coinvariantsMap k G f (zeroIso k G M z))
    exact congrArg ULift.up (zeroIso_natural k G f z))

theorem degreeZeroLinear : Specification.ZeroLinearType := by
  intro k G _ _
  exact ⟨zeroNatIso k G, zeroCoordinates k G⟩

end Scalars

end AdvancedHomologicalAlgebra.DerivedGroupHomology


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
open CategoryTheory
open scoped MonoidAlgebra ModuleCat.Algebra
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.TorBalance
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open AdvancedHomologicalAlgebra.DerivedTorComparison
namespace AdvancedHomologicalAlgebra.DerivedGroupHomology
universe u v w x y
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

/-- The underlying abelian groups of ambient coinvariants. -/
abbrev ambientCoinvariantGroups :
    ModuleCat.{max u v w} k[G] ⥤ ModuleCat.{max u v w} ℤ :=
  Specification.ambientCoinvariants.{u,v,w} k G ⋙ ModuleCat.restrictScalars (Int.castRingHom k)

/-- The original coinvariant–tensor identification, on the ambient coefficient category. -/
def ambientCoinvariantTensorFunctorIso :
    ambientCoinvariantGroups.{u,v,w} k G ≅ tensorCoefficients.{u,v,max u v w} k G :=
  NatIso.ofComponents
    (fun M => (GroupCoinvariants.coinvariantTensorIso M).toAddEquiv.toIntLinearEquiv.toModuleIso)
    (by
      intro M N f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      have h := GroupCoinvariants.coinvariantTensorIso_natural f z
      rw [← P103.Ch11.ExtTorDefinitions.tensorMap_eq] at h
      exact h)

abbrev coefficientTensorComplex (K : ChainComplex (ModuleCat.{max u v w} k[G]) ℕ) :=
  leftOrdinaryTensorComplex (GroupCoinvariants.TrivialRight k G) K

/-- The two quasi-isomorphic augmentations of the same tensor total complex. -/
def barTensorAugmentations {M : ModuleCat.{max u v w} k[G]} (Q : LeftResolution k[G] M)
    (hQ : Q.IsProjective) :
    { α : Augmentations (barResolution k G) Q //
      QuasiIsomorphism α.left ∧ QuasiIsomorphism α.right } :=
  let h := TorBalance.balance k[G] (GroupCoinvariants.TrivialRight k G) M
    (barResolution k G) Q (barResolution_projective k G) hQ
  ⟨h.choose, h.choose_spec⟩

/-- The comparison comes from the two augmentations, with the coefficient
variable resolved by an arbitrary ordinary projective resolution. -/
def resolutionBalanceIso {M : ModuleCat.{max u v w} k[G]} (Q : LeftResolution k[G] M)
    (hQ : Q.IsProjective) (n : ℕ) :
    barHomology k G M n ≃ₗ[ℤ] Homology (coefficientTensorComplex.{u,v,w} k G Q.complex) n :=
  let α := barTensorAugmentations.{u,v,w} k G Q hQ
  balanceEquiv α.val α.property.1 α.property.2 n

private lemma leftTensorFirstMap_id
    (K : ChainComplex (ModuleCat.{max u v w} k[G]) ℕ) :
    leftTensorFirstMap
      (LinearMap.id : GroupCoinvariants.TrivialRight k G →ₗ[k[G]ᵐᵒᵖ] _)
      K = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  rfl

/-- Naturality for every map of augmented coefficient resolutions. -/
lemma resolutionBalanceIso_naturality {M N : ModuleCat.{max u v w} k[G]}
    {P : LeftResolution k[G] M} {Q : LeftResolution k[G] N}
    (hP : P.IsProjective) (hQ : Q.IsProjective) {f : M ⟶ N}
    (l : P.complex ⟶ Q.complex) (hl : ChainLift P Q f.hom l) (n : ℕ) :
    (resolutionBalanceIso.{u,v,w} k G Q hQ n).toLinearMap.comp (barHomologyMap k G f n) =
      (homologyMap (((tensorCoefficients k G).mapHomologicalComplex (.down ℕ)).map l) n).comp
        (resolutionBalanceIso.{u,v,w} k G P hP n).toLinearMap := by
  let α := barTensorAugmentations.{u,v,w} k G P hP
  let β := barTensorAugmentations.{u,v,w} k G Q hQ
  have h := TorBalance.balance_naturality k[G]
    (GroupCoinvariants.TrivialRight k G) (GroupCoinvariants.TrivialRight k G)
    M N (barResolution k G) (barResolution k G) P Q LinearMap.id f.hom
    (𝟙 (barResolution k G).complex) l (P103.Ch10.Comparison.chainLift_id (barResolution k G)) hl
    α.val β.val α.property.1 α.property.2 β.property.1 β.property.2 n
  have hr : tensorFirstMap (𝟙 (barResolution k G).complex) M = 𝟙 _ :=
    tensorFirstMap_id k G (barChoice k G) M
  rw [hr, Category.id_comp, leftTensorMap, leftTensorFirstMap_id, Category.id_comp] at h
  exact h

/-- Coinvariants and tensor with the trivial right module agree termwise. -/
def coinvariantTensorComplexIso {ι : Type*} (c : ComplexShape ι) :
    (ambientCoinvariantGroups.{u,v,w} k G).mapHomologicalComplex c ≅
      (tensorCoefficients k G).mapHomologicalComplex c :=
  NatIso.mapHomologicalComplex (ambientCoinvariantTensorFunctorIso.{u,v,w} k G) c

/-- H⁻ⁿ of the underlying coinvariant cochain complex is the ordinary
quotient homology of the tensor of the coefficient resolution. -/
def coinvariantResolutionHomologyIso {M : ModuleCat.{max u v w} k[G]}
    (Q : LeftResolution k[G] M) (n : ℕ) :
    (((ambientCoinvariantGroups.{u,v,w} k G).mapHomologicalComplex (.up ℤ)).obj
      (cochainResolution Q)).homology (-(n : ℤ)) ≅
      ModuleCat.of ℤ (Homology (coefficientTensorComplex.{u,v,w} k G Q.complex) n) :=
  let K := ((ambientCoinvariantGroups.{u,v,w} k G).mapHomologicalComplex (.down ℕ)).obj Q.complex
  (HomologicalComplex.homologyFunctor _ (.up ℤ) (-(n : ℤ))).mapIso
        (mapExtendIso (ambientCoinvariantGroups.{u,v,w} k G) Q.complex ComplexShape.embeddingDownNat) ≪≫
    K.extendHomologyIso ComplexShape.embeddingDownNat rfl ≪≫
    (HomologicalComplex.homologyFunctor _ (.down ℕ) n).mapIso
        ((coinvariantTensorComplexIso.{u,v,w} k G (.down ℕ)).app Q.complex) ≪≫
    quotientHomologyIso (coefficientTensorComplex.{u,v,w} k G Q.complex) n

@[reassoc]
lemma coinvariantResolutionHomologyIso_naturality
    {M N : ModuleCat.{max u v w} k[G]} {P : LeftResolution k[G] M} {Q : LeftResolution k[G] N}
    (l : P.complex ⟶ Q.complex) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((ambientCoinvariantGroups.{u,v,w} k G).mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.extendMap l ComplexShape.embeddingDownNat)) (-(n : ℤ)) ≫
      (coinvariantResolutionHomologyIso.{u,v,w} k G Q n).hom =
    (coinvariantResolutionHomologyIso.{u,v,w} k G P n).hom ≫
      ModuleCat.ofHom (homologyMap (((tensorCoefficients k G).mapHomologicalComplex (.down ℕ)).map l) n) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} ℤ) (.up ℤ) (-(n : ℤ))
  let H' := HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} ℤ) (.down ℕ) n
  have h := congrArg H.map
    (mapExtendIso_naturality (ambientCoinvariantGroups.{u,v,w} k G) ComplexShape.embeddingDownNat l)
  have h' :
      HomologicalComplex.homologyMap
          (((ambientCoinvariantGroups.{u,v,w} k G).mapHomologicalComplex (.down ℕ)).map l) n ≫
        H'.map ((coinvariantTensorComplexIso.{u,v,w} k G (.down ℕ)).app Q.complex).hom =
      H'.map ((coinvariantTensorComplexIso.{u,v,w} k G (.down ℕ)).app P.complex).hom ≫
        HomologicalComplex.homologyMap
          (((tensorCoefficients k G).mapHomologicalComplex (.down ℕ)).map l) n := by
    have hm := congrArg H'.map
      ((coinvariantTensorComplexIso.{u,v,w} k G (.down ℕ)).hom.naturality l)
    simp only [Functor.map_comp] at hm
    exact hm
  have hassoc := congrArg
    (fun f => f ≫ (quotientHomologyIso (coefficientTensorComplex.{u,v,w} k G Q.complex) n).hom) h'
  simp only [Functor.map_comp] at h
  simp only [Category.assoc] at hassoc
  dsimp only [coinvariantResolutionHomologyIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
  erw [h]
  simp only [Category.assoc]
  have hn := HomologicalComplex.extendHomologyIso_hom_naturality_assoc
    (((ambientCoinvariantGroups.{u,v,w} k G).mapHomologicalComplex (.down ℕ)).map l)
    ComplexShape.embeddingDownNat (j := n) (hj' := rfl)
    (H'.map ((coinvariantTensorComplexIso.{u,v,w} k G (.down ℕ)).app Q.complex).hom ≫
      (quotientHomologyIso (coefficientTensorComplex.{u,v,w} k G Q.complex) n).hom)
  erw [hn]
  have hq := quotientHomologyIso_naturality
    (((tensorCoefficients k G).mapHomologicalComplex (.down ℕ)).map l) n
  erw [hassoc, hq]

/-- After computation on any projective coefficient resolution, the
coinvariant cochain homology agrees with the bar homology. -/
def coinvariantBarHomologyIso {M : ModuleCat.{max u v w} k[G]}
    (Q : LeftResolution k[G] M) (hQ : Q.IsProjective) (n : ℕ) :
    (((ambientCoinvariantGroups.{u,v,w} k G).mapHomologicalComplex (.up ℤ)).obj
      (cochainResolution Q)).homology (-(n : ℤ)) ≅
      ModuleCat.of ℤ (barHomology k G M n) :=
  coinvariantResolutionHomologyIso.{u,v,w} k G Q n ≪≫
    (resolutionBalanceIso.{u,v,w} k G Q hQ n).symm.toModuleIso

@[reassoc]
lemma coinvariantBarHomologyIso_naturality
    {M N : ModuleCat.{max u v w} k[G]} {P : LeftResolution k[G] M} {Q : LeftResolution k[G] N}
    (hP : P.IsProjective) (hQ : Q.IsProjective) {f : M ⟶ N}
    (l : P.complex ⟶ Q.complex) (hl : ChainLift P Q f.hom l) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((ambientCoinvariantGroups.{u,v,w} k G).mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.extendMap l ComplexShape.embeddingDownNat)) (-(n : ℤ)) ≫
      (coinvariantBarHomologyIso.{u,v,w} k G Q hQ n).hom =
    (coinvariantBarHomologyIso.{u,v,w} k G P hP n).hom ≫
      ModuleCat.ofHom (barHomologyMap k G f n) := by
  have h := resolutionBalanceIso_naturality k G hP hQ l hl n
  dsimp only [coinvariantBarHomologyIso, Iso.trans_hom]
  rw [← Category.assoc, coinvariantResolutionHomologyIso_naturality, Category.assoc,
    Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply (resolutionBalanceIso.{u,v,w} k G Q hQ n).injective
  change (resolutionBalanceIso.{u,v,w} k G Q hQ n)
      ((resolutionBalanceIso.{u,v,w} k G Q hQ n).symm
        (homologyMap (((tensorCoefficients k G).mapHomologicalComplex (.down ℕ)).map l) n z)) =
    (resolutionBalanceIso.{u,v,w} k G Q hQ n)
      (barHomologyMap k G f n ((resolutionBalanceIso.{u,v,w} k G P hP n).symm z))
  rw [LinearEquiv.apply_symm_apply]
  have hz := LinearMap.congr_fun h ((resolutionBalanceIso.{u,v,w} k G P hP n).symm z)
  change resolutionBalanceIso.{u,v,w} k G Q hQ n
      (barHomologyMap k G f n ((resolutionBalanceIso.{u,v,w} k G P hP n).symm z)) =
    homologyMap (((tensorCoefficients k G).mapHomologicalComplex (.down ℕ)).map l) n
      (resolutionBalanceIso.{u,v,w} k G P hP n ((resolutionBalanceIso.{u,v,w} k G P hP n).symm z)) at hz
  rw [LinearEquiv.apply_symm_apply] at hz
  exact hz.symm

lemma homologicalComplex_homologyMap_scalarId {C ι : Type*}
    [Category* C] [Abelian C] [CategoryTheory.Linear k C]
    {c : ComplexShape ι} (K : HomologicalComplex C c) (i : ι) (r : k) :
    HomologicalComplex.homologyMap (r • 𝟙 K) i = r • 𝟙 (K.homology i) := by
  change ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor C c i).map (r • 𝟙 K)) = _
  have h : (HomologicalComplex.shortComplexFunctor C c i).map (r • 𝟙 K) =
      r • (HomologicalComplex.shortComplexFunctor C c i).map (𝟙 K) := rfl
  change _ = r • 𝟙 ((HomologicalComplex.shortComplexFunctor C c i).obj K).homology
  rw [h, ShortComplex.homologyMap_smul]
  exact congrArg (r • ·) (HomologicalComplex.homologyMap_id K i)

section HomologyRestriction
variable {C E I : Type*} [Category* C] [Abelian C] [Category* E] [Abelian E]
  (F : C ⥤ E) [F.Additive] [F.PreservesHomology] {c : ComplexShape I}

/-- Homology in the target of an exact additive functor is the image of homology. -/
def restrictHomologyIso (K : HomologicalComplex C c) (i : I) :
    F.obj (K.homology i) ≅ ((F.mapHomologicalComplex c).obj K).homology i :=
  ((K.sc i).mapHomologyIso F).symm

@[reassoc]
lemma restrictHomologyIso_natural {K L : HomologicalComplex C c} (f : K ⟶ L) (i : I) :
    F.map (HomologicalComplex.homologyMap f i) ≫ (restrictHomologyIso F L i).hom =
      (restrictHomologyIso F K i).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex c).map f) i :=
  ShortComplex.mapHomologyIso_inv_naturality ((HomologicalComplex.shortComplexFunctor C c i).map f) F
end HomologyRestriction

section DerivedValues
variable [HasDerivedCategory.{x} (ModuleCat.{max u v w} k[G])] [HasDerivedCategory.{y} (ModuleCat.{max u v w} k)]
  [(minus (ModuleCat.{max u v w} k[G])).IsTriangulated] [(minus (ModuleCat.{max u v w} k)).IsTriangulated]
  (D : ExactLeftData.{(max u v w)+1,max u v w,(max u v w)+1,max u v w,x,y}
    (Specification.ambientCoinvariants.{u,v,w} k G))

/-- Compute the genuine derived coinvariants using any coefficient projective resolution. -/
def derivedResolutionIso {M : (ModuleCat.{max u v w} k[G])} (P : LeftResolution k[G] M) (hP : P.IsProjective) (n : ℕ) :
    (leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).obj M ≅ (((GroupCoinvariants.coinvariantsFunctor k G).mapHomologicalComplex (.up ℤ)).obj (cochainResolution P)).homology (-(n : ℤ)) :=
  cochainComputationIso (Specification.ambientCoinvariants.{u,v,w} k G) D M (cochainResolution P) (cochainAugmentation P)
    (cochainAugmentation_quasiIso P) (cochainResolution_projective P hP) n

lemma derivedResolutionIso_natural {M N : (ModuleCat.{max u v w} k[G])} {P : LeftResolution k[G] M}
    {Q : LeftResolution k[G] N} (hP : P.IsProjective) (hQ : Q.IsProjective) (f : M ⟶ N)
    (l : P.complex ⟶ Q.complex) (hl : ChainLift P Q f.hom l) (n : ℕ) :
    (leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).map f ≫ (derivedResolutionIso.{u,v,w,x,y} k G D Q hQ n).hom =
      (derivedResolutionIso.{u,v,w,x,y} k G D P hP n).hom ≫ HomologicalComplex.homologyMap
        (((GroupCoinvariants.coinvariantsFunctor k G).mapHomologicalComplex (.up ℤ)).map (HomologicalComplex.extendMap l ComplexShape.embeddingDownNat))
        (-(n : ℤ)) :=
  cochainComputationIso_naturality (Specification.ambientCoinvariants.{u,v,w} k G) D (p := cochainAugmentation P) (hp := cochainAugmentation_quasiIso P)
    (hK := cochainResolution_projective P hP) (cochainAugmentation Q) (cochainAugmentation_quasiIso Q)
    (cochainResolution_projective Q hQ) _ f
    (cochainAugmentation_naturality Q f l hl) n

/-- The actual k-linear derived value, restricted to abelian groups, is the
homology of the same coinvariant cochain complex with scalars restricted. -/
def derivedResolutionGroupsIso {M : (ModuleCat.{max u v w} k[G])}
    (P : LeftResolution k[G] M) (hP : P.IsProjective) (n : ℕ) :
    (ModuleCat.restrictScalars (Int.castRingHom k)).obj ((leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).obj M) ≅
      (((ambientCoinvariantGroups.{u,v,w} k G).mapHomologicalComplex (.up ℤ)).obj (cochainResolution P)).homology (-(n : ℤ)) :=
  (ModuleCat.restrictScalars (Int.castRingHom k)).mapIso (derivedResolutionIso.{u,v,w,x,y} k G D P hP n) ≪≫
    restrictHomologyIso (ModuleCat.restrictScalars (Int.castRingHom k)) (((GroupCoinvariants.coinvariantsFunctor k G).mapHomologicalComplex (.up ℤ)).obj (cochainResolution P)) (-(n : ℤ))

@[reassoc]
lemma derivedResolutionGroupsIso_natural {M N : (ModuleCat.{max u v w} k[G])} {P : LeftResolution k[G] M}
    {Q : LeftResolution k[G] N} (hP : P.IsProjective) (hQ : Q.IsProjective) (f : M ⟶ N)
    (l : P.complex ⟶ Q.complex) (hl : ChainLift P Q f.hom l) (n : ℕ) :
    (ModuleCat.restrictScalars (Int.castRingHom k)).map ((leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).map f) ≫ (derivedResolutionGroupsIso.{u,v,w,x,y} k G D Q hQ n).hom =
      (derivedResolutionGroupsIso.{u,v,w,x,y} k G D P hP n).hom ≫ HomologicalComplex.homologyMap
        (((ambientCoinvariantGroups.{u,v,w} k G).mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.extendMap l ComplexShape.embeddingDownNat)) (-(n : ℤ)) := by
  have h := congrArg (ModuleCat.restrictScalars (Int.castRingHom k)).map (derivedResolutionIso_natural.{u,v,w,x,y} k G D hP hQ f l hl n)
  simp only [Functor.map_comp] at h
  dsimp only [derivedResolutionGroupsIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, h, Category.assoc]
  erw [restrictHomologyIso_natural]
  rw [Category.assoc]
  rfl

lemma leftValue_scalarCoefficientMap (M : (ModuleCat.{max u v w} k[G])) (P : LeftResolution k[G] M)
    (hP : P.IsProjective) (n : ℕ) (r : k) :
    (leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).map (scalarCoefficientMap k G M r) = r • 𝟙 ((leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).obj M) := by
  let K := cochainResolution P
  let p := cochainAugmentation P
  let l : K ⟶ K := r • 𝟙 K
  let f := scalarCoefficientMap k G M r
  have hl : l ≫ p = p ≫ (CochainComplex.singleFunctor (ModuleCat.{max u v w} k[G]) 0).map f := by
    have h : (CochainComplex.singleFunctor (ModuleCat.{max u v w} k[G]) 0).map f =
        r • 𝟙 ((CochainComplex.singleFunctor (ModuleCat.{max u v w} k[G]) 0).obj M) := by
      change (CochainComplex.singleFunctor (ModuleCat.{max u v w} k[G]) 0).map (r • 𝟙 M) = _
      simp
    rw [h]
    simp [l]
  have h := cochainComputationIso_naturality (Specification.ambientCoinvariants.{u,v,w} k G) D (p := p) (hp := cochainAugmentation_quasiIso P)
    (hK := cochainResolution_projective P hP) p (cochainAugmentation_quasiIso P)
    (cochainResolution_projective P hP) l f hl n
  let Eₙ := derivedResolutionIso.{u,v,w,x,y} k G D P hP n
  change (leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).map f ≫ Eₙ.hom = Eₙ.hom ≫
    HomologicalComplex.homologyMap (((GroupCoinvariants.coinvariantsFunctor k G).mapHomologicalComplex (.up ℤ)).map (r • 𝟙 K)) (-(n : ℤ)) at h
  apply (cancel_mono Eₙ.hom).mp
  have hm := ((GroupCoinvariants.coinvariantsFunctor k G).mapHomologicalComplex (.up ℤ)).map_id K
  rw [h, Functor.map_smul, hm, homologicalComplex_homologyMap_scalarId]
  simp
  exact Category.comp_id (r • Eₙ.hom)


end DerivedValues

section DerivedBar
variable [HasDerivedCategory.{x} (ModuleCat.{max u v w} k[G])] [HasDerivedCategory.{y} (ModuleCat.{max u v w} k)]
  [(minus (ModuleCat.{max u v w} k[G])).IsTriangulated] [(minus (ModuleCat.{max u v w} k)).IsTriangulated]
  (D : ExactLeftData.{(max u v w)+1,max u v w,(max u v w)+1,max u v w,x,y}
    (Specification.ambientCoinvariants.{u,v,w} k G))

/-- Compute derived coinvariants via any projective coefficient resolution,
then compare with the bar homology by the two tensor total augmentations. -/
def derivedBarGroupsIsoOnResolution {M : ModuleCat.{max u v w} k[G]}
    (Q : LeftResolution k[G] M) (hQ : Q.IsProjective) (n : ℕ) :
    (ModuleCat.restrictScalars (Int.castRingHom k)).obj
      ((leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).obj M) ≅
      ModuleCat.of ℤ (barHomology k G M n) :=
  derivedResolutionGroupsIso.{u,v,w,x,y} k G D Q hQ n ≪≫ coinvariantBarHomologyIso.{u,v,w} k G Q hQ n

lemma derivedBarGroupsIsoOnResolution_natural {M N : ModuleCat.{max u v w} k[G]}
    {P : LeftResolution k[G] M} {Q : LeftResolution k[G] N}
    (hP : P.IsProjective) (hQ : Q.IsProjective) (f : M ⟶ N)
    (l : P.complex ⟶ Q.complex) (hl : ChainLift P Q f.hom l) (n : ℕ) :
    (ModuleCat.restrictScalars (Int.castRingHom k)).map
        ((leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).map f) ≫
        (derivedBarGroupsIsoOnResolution.{u,v,w,x,y} k G D Q hQ n).hom =
      (derivedBarGroupsIsoOnResolution.{u,v,w,x,y} k G D P hP n).hom ≫
        ModuleCat.ofHom (barHomologyMap k G f n) := by
  dsimp only [derivedBarGroupsIsoOnResolution, Iso.trans_hom]
  rw [← Category.assoc, derivedResolutionGroupsIso_natural.{u,v,w,x,y} k G D hP hQ f l hl n,
    Category.assoc, coinvariantBarHomologyIso_naturality.{u,v,w} k G hP hQ l hl n, Category.assoc]

private abbrev coefficientResolutionChoice (M : ModuleCat.{max u v w} k[G]) : ProjectiveChoice k[G] M :=
  P103.Ch11.ExtTorDefinitions.resolutionFamily k[G] M

/-- Derived coinvariants compared with the bar model, in all degrees. -/
def derivedBarGroupsIso (M : ModuleCat.{max u v w} k[G]) (n : ℕ) :
    (ModuleCat.restrictScalars (Int.castRingHom k)).obj
      ((leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).obj M) ≅
      ModuleCat.of ℤ (barHomology k G M n) :=
  derivedBarGroupsIsoOnResolution.{u,v,w,x,y} k G D (coefficientResolutionChoice.{u,v,w} k G M).val
    (coefficientResolutionChoice.{u,v,w} k G M).property n

lemma derivedBarGroupsIso_natural {M N : ModuleCat.{max u v w} k[G]} (f : M ⟶ N) (n : ℕ) :
    (ModuleCat.restrictScalars (Int.castRingHom k)).map
        ((leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).map f) ≫
        (derivedBarGroupsIso.{u,v,w,x,y} k G D N n).hom =
      (derivedBarGroupsIso.{u,v,w,x,y} k G D M n).hom ≫ ModuleCat.ofHom (barHomologyMap k G f n) := by
  let P := coefficientResolutionChoice.{u,v,w} k G M
  let Q := coefficientResolutionChoice.{u,v,w} k G N
  obtain ⟨l, hl⟩ := P103.Ch10.Comparison.chain_exists k[G] M N P.val Q.val P.property f.hom
  exact derivedBarGroupsIsoOnResolution_natural.{u,v,w,x,y} k G D P.property Q.property f l hl n

/-- On any other projective coefficient resolution, the normalized comparison
computes the same isomorphism. -/
lemma derivedBarGroupsIso_eq {M : ModuleCat.{max u v w} k[G]} (Q : LeftResolution k[G] M)
    (hQ : Q.IsProjective) (n : ℕ) :
    derivedBarGroupsIso.{u,v,w,x,y} k G D M n = derivedBarGroupsIsoOnResolution.{u,v,w,x,y} k G D Q hQ n := by
  let P := coefficientResolutionChoice.{u,v,w} k G M
  obtain ⟨l, hl⟩ := P103.Ch10.Comparison.chain_exists k[G] M M P.val Q P.property
    (ModuleCat.Hom.hom (𝟙 M))
  have h := derivedBarGroupsIsoOnResolution_natural.{u,v,w,x,y} k G D P.property hQ (𝟙 M) l hl n
  have hm : ModuleCat.ofHom (barHomologyMap k G (𝟙 M) n) = 𝟙 _ := by
    have hh := congrArg ModuleCat.ofHom (torMaps_coefficient k G (barChoice k G) (𝟙 M) n)
    rw [((P103.Ch11.ExtTorDefinitions.theory.{max u v,u,max u v w} k[G]).torMaps n).id] at hh
    exact hh.symm
  apply Iso.ext
  have hId := ((leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n) ⋙
    ModuleCat.restrictScalars (Int.castRingHom k)).map_id M
  change (ModuleCat.restrictScalars (Int.castRingHom k)).map
    ((leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).map (𝟙 M)) = 𝟙 _ at hId
  rw [hId, Category.id_comp, hm, Category.comp_id] at h
  exact h.symm

end DerivedBar

section DerivedTor
variable [HasDerivedCategory.{x} (ModuleCat.{max u v w} k[G])] [HasDerivedCategory.{y} (ModuleCat.{max u v w} k)]
  [(minus (ModuleCat.{max u v w} k[G])).IsTriangulated] [(minus (ModuleCat.{max u v w} k)).IsTriangulated]
  (D : ExactLeftData.{(max u v w)+1,max u v w,(max u v w)+1,max u v w,x,y}
    (Specification.ambientCoinvariants.{u,v,w} k G))

/-- The two derived comparisons converge to the canonical Tor object. -/
def derivedTorGroupsIso (M : ModuleCat.{max u v w} k[G]) (n : ℕ) :
    (ModuleCat.restrictScalars (Int.castRingHom k)).obj ((leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).obj M) ≅
      (homologyFunctor k G n).obj M :=
  derivedBarGroupsIso.{u,v,w,x,y} k G D M n ≪≫ (torBarIso k G M n).symm.toModuleIso

lemma derivedTorGroupsIso_natural {M N : ModuleCat.{max u v w} k[G]} (f : M ⟶ N) (n : ℕ)
    (z : (leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).obj M) :
    (derivedTorGroupsIso.{u,v,w,x,y} k G D N n).hom ((leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).map f z) =
      (homologyFunctor k G n).map f ((derivedTorGroupsIso.{u,v,w,x,y} k G D M n).hom z) := by
  have h := ConcreteCategory.congr_hom (derivedBarGroupsIso_natural.{u,v,w,x,y} k G D f n)
    (show (ModuleCat.restrictScalars (Int.castRingHom k)).obj ((leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).obj M) from z)
  apply (torBarIso k G N n).injective
  change torBarIso k G N n ((torBarIso k G N n).symm
      ((derivedBarGroupsIso.{u,v,w,x,y} k G D N n).hom ((leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).map f z))) =
    torBarIso k G N n ((homologyFunctor k G n).map f
      ((torBarIso k G M n).symm ((derivedBarGroupsIso.{u,v,w,x,y} k G D M n).hom z)))
  rw [LinearEquiv.apply_symm_apply, torBarIso_natural, LinearEquiv.apply_symm_apply]
  exact h

/-- The comparison is k-linear for the canonical scalar action on Tor. -/
def derivedTorLinearIso (M : ModuleCat.{max u v w} k[G]) (n : ℕ) :
    (leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).obj M ≅ (kHomologyFunctor k G n).obj M := by
  let e := derivedTorGroupsIso.{u,v,w,x,y} k G D M n
  let P := coefficientResolutionChoice.{u,v,w} k G M
  let f : (leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).obj M →ₗ[k] (kHomologyFunctor k G n).obj M :=
    { toFun := fun z => e.hom z
      map_add' := map_add e.hom.hom
      map_smul' := fun r z => by
        have h := derivedTorGroupsIso_natural.{u,v,w,x,y} k G D (scalarCoefficientMap k G M r) n z
        have hr := ConcreteCategory.congr_hom
          (leftValue_scalarCoefficientMap.{u,v,w,x,y} k G D M P.val P.property n r) z
        change (leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).map (scalarCoefficientMap k G M r) z = r • z at hr
        change e.hom (r • z) = (homologyFunctor k G n).map (scalarCoefficientMap k G M r) (e.hom z)
        exact (congrArg (fun t : (leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).obj M => e.hom t) hr).symm.trans h }
  exact (LinearEquiv.ofBijective f e.toLinearEquiv.bijective).toModuleIso

/-- In each degree, an isomorphism of the genuine k-module-valued functors. -/
def derivedTorIso (n : ℕ) : leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n ≅ kHomologyFunctor k G n :=
  NatIso.ofComponents (fun M => derivedTorLinearIso.{u,v,w,x,y} k G D M n) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact derivedTorGroupsIso_natural.{u,v,w,x,y} k G D f n z)

@[simp]
lemma torBarIso_derivedTorIso (M : ModuleCat.{max u v w} k[G]) (n : ℕ)
    (z : (leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n).obj M) :
    torBarIso k G M n ((derivedTorIso.{u,v,w,x,y} k G D n).hom.app M z) =
      (derivedBarGroupsIso.{u,v,w,x,y} k G D M n).hom z :=
  (torBarIso k G M n).apply_symm_apply _

end DerivedTor

end AdvancedHomologicalAlgebra.DerivedGroupHomology
end


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 240000
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.TorBalance
namespace AdvancedHomologicalAlgebra.DerivedGroupHomology

section TotalSplitting
universe u v w

private instance : (HomologicalComplex₂.totalFunctor (ModuleCat.{v} ℤ)
    (.down ℤ) (.down ℤ) (.down ℤ)).PreservesZeroMorphisms where
  map_zero K L := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply HomologicalComplex₂.total.hom_ext
    intro p q h
    change K.ιTotal _ p q n h ≫ (HomologicalComplex₂.total.map (0 : K ⟶ L) _).f n =
      K.ιTotal _ p q n h ≫ 0
    rw [HomologicalComplex₂.ιTotal_map]
    simp

/-- Degreewise maps between total terms, induced by maps on their summands. -/
private def totalTermMap (K L : HomologicalComplex₂ (ModuleCat.{v} ℤ) (.down ℤ) (.down ℤ)) (n : ℤ)
    (f : ∀ p q, (K.X p).X q ⟶ (L.X p).X q) :
    (K.total (.down ℤ)).X n ⟶ (L.total (.down ℤ)).X n :=
  K.totalDesc (fun p q h => f p q ≫ L.ιTotal (.down ℤ) p q n h)

@[reassoc (attr := simp)]
private lemma ι_totalTermMap (K L : HomologicalComplex₂ (ModuleCat.{v} ℤ) (.down ℤ) (.down ℤ)) (n p q : ℤ)
    (h : p + q = n) (f : ∀ p q, (K.X p).X q ⟶ (L.X p).X q) :
    K.ιTotal (.down ℤ) p q n h ≫ totalTermMap K L n f =
      f p q ≫ L.ιTotal (.down ℤ) p q n h :=
  K.ι_totalDesc _ p q h

/-- Splittings on a diagonal give a splitting of its coproduct. -/
private def totalSplitting (S : ShortComplex (HomologicalComplex₂ (ModuleCat.{v} ℤ) (.down ℤ) (.down ℤ)))
    (σ : ∀ p q, ((S.map (HomologicalComplex.eval _ _ p)).map
      (HomologicalComplex.eval _ _ q)).Splitting) (n : ℤ) :
    ((S.map (HomologicalComplex₂.totalFunctor _ (.down ℤ) (.down ℤ) (.down ℤ))).map (HomologicalComplex.eval _ _ n)).Splitting where
  r := totalTermMap S.X₂ S.X₁ n (fun p q => (σ p q).r)
  s := totalTermMap S.X₃ S.X₂ n (fun p q => (σ p q).s)
  f_r := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q h
    change _ ≫ (HomologicalComplex₂.total.map S.f (.down ℤ)).f n ≫ _ =
      _ ≫ 𝟙 ((S.X₁.total (.down ℤ)).X n)
    rw [HomologicalComplex₂.ιTotal_map_assoc, ι_totalTermMap, ← Category.assoc, Category.comp_id]
    have hf := (σ p q).f_r
    change (S.f.f p).f q ≫ (σ p q).r = 𝟙 ((S.X₁.X p).X q) at hf
    rw [hf, Category.id_comp]
  s_g := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q h
    change _ ≫ totalTermMap _ _ _ _ ≫ (HomologicalComplex₂.total.map S.g (.down ℤ)).f n =
      _ ≫ 𝟙 ((S.X₃.total (.down ℤ)).X n)
    rw [ι_totalTermMap_assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc, Category.comp_id]
    have hg := (σ p q).s_g
    change (σ p q).s ≫ (S.g.f p).f q = 𝟙 ((S.X₃.X p).X q) at hg
    rw [hg, Category.id_comp]
  id := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q h
    change _ ≫ (totalTermMap _ _ _ _ ≫ (HomologicalComplex₂.total.map S.f (.down ℤ)).f n +
      (HomologicalComplex₂.total.map S.g (.down ℤ)).f n ≫ totalTermMap _ _ _ _) =
      _ ≫ 𝟙 ((S.X₂.total (.down ℤ)).X n)
    rw [Preadditive.comp_add, ι_totalTermMap_assoc, HomologicalComplex₂.ιTotal_map,
      HomologicalComplex₂.ιTotal_map_assoc, ι_totalTermMap, ← Category.assoc,
      ← Category.assoc, ← Preadditive.add_comp, Category.comp_id]
    have hi := (σ p q).id
    change ((σ p q).r ≫ (S.f.f p).f q : (S.X₂.X p).X q ⟶ (S.X₂.X p).X q) +
      ((S.g.f p).f q ≫ (σ p q).s : (S.X₂.X p).X q ⟶ (S.X₂.X p).X q) =
      𝟙 ((S.X₂.X p).X q) at hi
    rw [hi, Category.id_comp]
end TotalSplitting

section TensorTotal
universe u v w
variable {R : Type u} [Ring R]

/-- Form the tensor bicomplex with the first factor fixed. -/
private def fixedTensorBicomplex (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) :
    ChainComplex (ModuleCat.{w} R) ℤ ⥤
      HomologicalComplex₂ (ModuleCat.{max v w} ℤ) (.down ℤ) (.down ℤ) where
  obj D := tensorBicomplex C D
  map g := tensorBicomplexMap (𝟙 C) g
  map_id D := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply HomologicalComplex.Hom.ext
    funext q
    exact (leftTensorFunctor (C.X p)).map_id (D.X q)
  map_comp g h := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply HomologicalComplex.Hom.ext
    funext q
    exact (leftTensorFunctor (C.X p)).map_comp (g.f q) (h.f q)

private instance (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) :
    (fixedTensorBicomplex.{u,v,w} C).Additive where
  map_add := by
    intro D D' f g
    apply HomologicalComplex.Hom.ext
    funext p
    apply HomologicalComplex.Hom.ext
    funext q
    exact (leftTensorFunctor (C.X p)).map_add

/-- A degreewise split coefficient sequence has degreewise split tensor totals. -/
lemma tensorTotal_degreewise_exact (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (S : ShortComplex (ChainComplex (ModuleCat.{w} R) ℕ))
    (σ : ∀ q, (S.map (HomologicalComplex.eval _ _ q)).Splitting) :
    P103.Specs.Ch10.HomologySequence.DegreewiseExact
      (ordinaryTotalMap (𝟙 C) S.f) (ordinaryTotalMap (𝟙 C) S.g) := by
  let Z := S.map (nonnegativeChainEmbedding.extendFunctor (ModuleCat R))
  let C' := extendNonnegativeChain C
  let T := Z.map (fixedTensorBicomplex C')
  let e := nonnegativeChainEmbedding
  have σ' (p q : ℤ) :
      ((T.map (HomologicalComplex.eval _ _ p)).map (HomologicalComplex.eval _ _ q)).Splitting :=
    (e.splittingExtend σ q).map (leftTensorFunctor (C'.X p))
  intro n
  let h := (totalSplitting T σ' (n : ℤ)).shortExact
  have hf : HomologicalComplex.extendMap (𝟙 C) e = 𝟙 C' :=
    (e.extendFunctor _).map_id C
  change Function.Injective ((tensorTotalMap (HomologicalComplex.extendMap (𝟙 C) e)
      (HomologicalComplex.extendMap S.f e)).f (n : ℤ)).hom ∧
    Function.Exact ((tensorTotalMap (HomologicalComplex.extendMap (𝟙 C) e)
      (HomologicalComplex.extendMap S.f e)).f (n : ℤ)).hom
      ((tensorTotalMap (HomologicalComplex.extendMap (𝟙 C) e)
      (HomologicalComplex.extendMap S.g e)).f (n : ℤ)).hom ∧
    Function.Surjective ((tensorTotalMap (HomologicalComplex.extendMap (𝟙 C) e)
      (HomologicalComplex.extendMap S.g e)).f (n : ℤ)).hom
  rw [hf]
  exact ⟨h.moduleCat_injective_f,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h.exact,
    h.moduleCat_surjective_g⟩
end TensorTotal
end AdvancedHomologicalAlgebra.DerivedGroupHomology
end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 480000
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.TorBalance P103.Specs.Ch10.HomologySequence
open AdvancedHomologicalAlgebra.DerivedTorComparison
namespace AdvancedHomologicalAlgebra.DerivedGroupHomology

section BalanceBoundary
universe u v w
variable {R : Type u} [Ring R] {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
  (P : LeftResolution Rᵐᵒᵖ A)
  (S : ShortComplex (ModuleCat.{max u w} R))
  (L : LeftResolution R S.X₁) (N : LeftResolution R S.X₃)
  (H : P103.Specs.Ch10.Horseshoe.ProjectiveData S.f.hom S.g.hom L N)

private lemma tensorFirstMap_id' (D : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (B : Type*) [AddCommGroup B] [Module R B] :
    tensorFirstMap (𝟙 D) B = 𝟙 _ :=
  ((tensorFunctor B).mapHomologicalComplex (.down ℕ)).map_id D

private lemma leftTensorFirstMap_id' {D : ChainComplex (ModuleCat.{w} R) ℕ} :
    leftTensorFirstMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) D = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact (leftTensorFunctor A).map_id (D.X n)

/-- The positive connecting maps agree under the two augmentation maps of the
same tensor-total horseshoe. -/
lemma balance_boundary
    (α₁ : Augmentations P L) (α₂ : Augmentations P H.middle) (α₃ : Augmentations P N)
    (h₁L : QuasiIsomorphism α₁.left) (h₁R : QuasiIsomorphism α₁.right)
    (h₃L : QuasiIsomorphism α₃.left) (h₃R : QuasiIsomorphism α₃.right)
    (hS : DegreewiseExact (tensorSecondMap P.complex S.f.hom) (tensorSecondMap P.complex S.g.hom))
    (n : ℕ)
    (δL : TorWith P S.X₃ (n+1) →ₗ[ℤ] TorWith P S.X₁ n)
    (δR : Homology (leftOrdinaryTensorComplex A N.complex) (n+1) →ₗ[ℤ]
      Homology (leftOrdinaryTensorComplex A L.complex) n)
    (hL : Connecting (tensorSecondMap P.complex S.f.hom) (tensorSecondMap P.complex S.g.hom) (n+1) n δL)
    (hR : Connecting (((leftTensorFunctor A).mapHomologicalComplex (.down ℕ)).map H.inclusion)
        (((leftTensorFunctor A).mapHomologicalComplex (.down ℕ)).map H.projection) (n+1) n δR)
    (z : TorWith P S.X₃ (n+1)) :
    balanceEquiv α₁ h₁L h₁R n (δL z) = δR (balanceEquiv α₃ h₃L h₃R (n+1) z) := by
  let g₁ := ordinaryTotalMap (𝟙 P.complex) H.inclusion
  let g₂ := ordinaryTotalMap (𝟙 P.complex) H.projection
  have ht : DegreewiseExact g₁ g₂ := tensorTotal_degreewise_exact P.complex
    (horseshoeChain S L N H) (horseshoeChainSplitting S L N H)
  have hr : DegreewiseExact (((leftTensorFunctor A).mapHomologicalComplex (.down ℕ)).map H.inclusion)
      (((leftTensorFunctor A).mapHomologicalComplex (.down ℕ)).map H.projection) := by
    intro m
    let h := ((horseshoeChainSplitting S L N H m).map (leftTensorFunctor A)).shortExact
    exact ⟨h.moduleCat_injective_f,
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h.exact,
      h.moduleCat_surjective_g⟩
  have hI : ChainLift P P (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) (𝟙 P.complex) := by
    dsimp [ChainLift]
  have e₁ := P103.Ch11.TorBalance.augmentation_natural R A A S.X₁ S.X₂ P P L H.middle
    LinearMap.id S.f.hom (𝟙 P.complex) H.inclusion hI H.augmentation_inclusion α₁ α₂
  have e₂ := P103.Ch11.TorBalance.augmentation_natural R A A S.X₂ S.X₃ P P H.middle N
    LinearMap.id S.g.hom (𝟙 P.complex) H.projection hI H.augmentation_projection α₂ α₃
  simp only [tensorFirstMap_id', leftTensorMap, leftTensorFirstMap_id', Category.id_comp] at e₁ e₂
  obtain ⟨δ, hδ, _⟩ := P103.Ch10.HomologySequence.sequence g₁ g₂ ht (n+1) n (by simp)
  have hf := (P103.Ch10.HomologySequence.naturality g₁ g₂ _ _ α₁.left α₂.left α₃.left
    e₁.1 e₂.1 ht hS (n+1) n (by simp) δ δL hδ.1 hL).2.2.1
  have hg := (P103.Ch10.HomologySequence.naturality g₁ g₂ _ _ α₁.right α₂.right α₃.right
    e₁.2 e₂.2 ht hr (n+1) n (by simp) δ δR hδ.1 hR).2.2.1
  obtain ⟨t, rfl⟩ := (h₃L (n+1)).2 z
  have hf' := DFunLike.congr_fun hf t
  have hg' := DFunLike.congr_fun hg t
  change homologyMap α₁.left n (δ t) = δL (homologyMap α₃.left (n+1) t) at hf'
  change homologyMap α₁.right n (δ t) = δR (homologyMap α₃.right (n+1) t) at hg'
  rw [← hf']
  have norm (B : ModuleCat.{max u w} R) (Q : LeftResolution R B)
      (a : Augmentations P Q) (l : QuasiIsomorphism a.left) (r : QuasiIsomorphism a.right)
      (m : ℕ) (x : Homology (ordinaryTotal P.complex Q.complex) m) :
      balanceEquiv a l r m (homologyMap a.left m x) = homologyMap a.right m x := by
    change (LinearEquiv.ofBijective (homologyMap a.right m) (r m))
      ((LinearEquiv.ofBijective (homologyMap a.left m) (l m)).symm
      ((LinearEquiv.ofBijective (homologyMap a.left m) (l m)) x)) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  rw [norm S.X₁ L α₁ h₁L h₁R, norm S.X₃ N α₃ h₃L h₃R, hg']
end BalanceBoundary
end AdvancedHomologicalAlgebra.DerivedGroupHomology
end
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option quotPrecheck false
open CategoryTheory
open scoped MonoidAlgebra
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch10.HomologySequence
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open AdvancedHomologicalAlgebra.DerivedTorComparison
namespace AdvancedHomologicalAlgebra.DerivedGroupHomology
universe u v w
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

section ResolutionBoundary
variable (S : ShortComplex (ModuleCat.{max u v w} k[G]))
    (P : LeftResolution k[G] S.X₁) (Q : LeftResolution k[G] S.X₃)
    (H : P103.Specs.Ch10.Horseshoe.ProjectiveData S.f.hom S.g.hom P Q)

set_option hygiene false in
local notation "F₁" => (ambientCoinvariantGroups.{u,v,w} k G).mapHomologicalComplex (.up ℤ)
local notation "T₀" => (tensorCoefficients k G).mapHomologicalComplex (.down ℕ)
local notation "e" => ComplexShape.embeddingDownNat
local notation "Ext" => (e).extendFunctor (ModuleCat ℤ)
local notation "C₀" => horseshoeChain S P Q H
local notation "C₁" => horseshoeCochain S P Q H

lemma adjacent_negative_degrees (n : ℕ) : (.up ℤ : ComplexShape ℤ).Rel
    (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) := by
  change -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ)
  omega

/-- Image of the coefficient horseshoe under coinvariants, on underlying groups. -/
private def coinvariantHorseshoeTensorIso :
    ((C₁).map F₁) ≅ ((C₀).map T₀).map Ext :=
  mapExtendShortComplexIso (ambientCoinvariantGroups.{u,v,w} k G) C₀ e ≪≫
    (Ext).mapShortComplex.mapIso ((C₀).mapNatIso (coinvariantTensorComplexIso.{u,v,w} k G (.down ℕ)))

private lemma coinvariantResolutionHomologyIso_factor
    {M : ModuleCat.{max u v w} k[G]} (V : LeftResolution k[G] M) (n : ℕ) :
    (coinvariantResolutionHomologyIso.{u,v,w} k G V n).hom =
      HomologicalComplex.homologyMap ((mapExtendIso (ambientCoinvariantGroups.{u,v,w} k G) V.complex e).hom ≫
        (Ext).map ((coinvariantTensorComplexIso.{u,v,w} k G (.down ℕ)).hom.app V.complex)) (-(n : ℤ)) ≫
      (extendedQuotientHomologyIso ((T₀).obj V.complex) n e rfl).hom := by
  dsimp only [coinvariantResolutionHomologyIso, Iso.trans_hom, Functor.mapIso_hom,
    extendedQuotientHomologyIso]
  rw [HomologicalComplex.homologyMap_comp]
  simp only [Category.assoc]
  congr 1
  exact (HomologicalComplex.extendHomologyIso_hom_naturality_assoc
    ((coinvariantTensorComplexIso.{u,v,w} k G (.down ℕ)).hom.app V.complex) e
    (show (e).f n = -(n : ℤ) from rfl)
    (quotientHomologyIso (coefficientTensorComplex.{u,v,w} k G V.complex) n).hom).symm

/-- Connecting morphism on the ordinary tensor coefficient resolutions, transported
from the coefficient coinvariant cochain complex. -/
def coinvariantResolutionBoundary (n : ℕ) :
    ModuleCat.of ℤ (Homology (coefficientTensorComplex.{u,v,w} k G Q.complex) (n+1)) ⟶
      ModuleCat.of ℤ (Homology (coefficientTensorComplex.{u,v,w} k G P.complex) n) :=
  (coinvariantResolutionHomologyIso.{u,v,w} k G Q (n+1)).inv ≫
    (horseshoeImage_shortExact S P Q H (ambientCoinvariantGroups.{u,v,w} k G)).δ
      (-((n+1 : ℕ) : ℤ)) (-(n : ℤ)) (adjacent_negative_degrees n) ≫
    (coinvariantResolutionHomologyIso.{u,v,w} k G P n).hom

/-- The connecting morphism of the coinvariant horseshoe uses positive
lift-and-boundary in the ordinary tensor computation. -/
lemma coinvariantResolutionBoundary_connecting (n : ℕ) :
    Connecting ((T₀).map H.inclusion) ((T₀).map H.projection) (n+1) n
      (coinvariantResolutionBoundary.{u,v,w} k G S P Q H n).hom := by
  let α := coinvariantHorseshoeTensorIso.{u,v,w} k G S P Q H
  let hC := horseshoeImage_shortExact S P Q H (ambientCoinvariantGroups.{u,v,w} k G)
  let hT := ShortComplex.shortExact_of_iso α hC
  let i : ℤ := -((n+1 : ℕ) : ℤ)
  let j : ℤ := -(n : ℤ)
  let h : (ComplexShape.up ℤ).Rel i j := adjacent_negative_degrees n
  let U₁ := extendedQuotientHomologyIso ((T₀).obj P.complex) n e (show (e).f n = j from rfl)
  let U₃ := extendedQuotientHomologyIso ((T₀).obj Q.complex) (n+1) e
    (show (e).f (n+1) = i from rfl)
  have h₁ : (coinvariantResolutionHomologyIso.{u,v,w} k G P n).hom =
      HomologicalComplex.homologyMap α.hom.τ₁ j ≫ U₁.hom :=
    coinvariantResolutionHomologyIso_factor.{u,v,w} k G P n
  have h₃ : (coinvariantResolutionHomologyIso.{u,v,w} k G Q (n+1)).hom =
      HomologicalComplex.homologyMap α.hom.τ₃ i ≫ U₃.hom :=
    coinvariantResolutionHomologyIso_factor.{u,v,w} k G Q (n+1)
  have hd := HomologicalComplex.HomologySequence.δ_naturality α.hom hC hT i j h
  have hδ : coinvariantResolutionBoundary.{u,v,w} k G S P Q H n =
      U₃.inv ≫ hT.δ i j h ≫ U₁.hom := by
    rw [← cancel_epi (coinvariantResolutionHomologyIso.{u,v,w} k G Q (n+1)).hom]
    dsimp only [coinvariantResolutionBoundary]
    rw [Iso.hom_inv_id_assoc, h₁, ← Category.assoc (hC.δ i j h), hd]
    rw [h₃]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hδ]
  exact extendedBoundaryConnecting ((C₀).map T₀) e hT (n+1) n (by rfl)

/-- The positive connecting map for the coefficient coinvariant cochains is
carried by the normalized comparison to the bar lift-and-boundary map. -/
lemma coinvariantBarHomologyIso_boundary (n : ℕ) (hS : S.ShortExact)
    (hP : P.IsProjective) (hQ : Q.IsProjective) :
    (horseshoeImage_shortExact S P Q H (ambientCoinvariantGroups.{u,v,w} k G)).δ
      (-((n+1 : ℕ) : ℤ)) (-(n : ℤ)) (adjacent_negative_degrees n) ≫
      (coinvariantBarHomologyIso.{u,v,w} k G P hP n).hom =
    (coinvariantBarHomologyIso.{u,v,w} k G Q hQ (n+1)).hom ≫
      ModuleCat.ofHom (barBoundary k G S hS n) := by
  let α₁ := barTensorAugmentations.{u,v,w} k G P hP
  let α₂ := barTensorAugmentations.{u,v,w} k G H.middle H.projective
  let α₃ := barTensorAugmentations.{u,v,w} k G Q hQ
  have hb (z : barHomology k G S.X₃ (n+1)) :
      resolutionBalanceIso.{u,v,w} k G P hP n (barBoundary k G S hS n z) =
        coinvariantResolutionBoundary.{u,v,w} k G S P Q H n (resolutionBalanceIso.{u,v,w} k G Q hQ (n+1) z) :=
    balance_boundary.{max u v,u,max u v w} (barResolution k G) S P Q H α₁.val α₂.val α₃.val
      α₁.property.1 α₁.property.2 α₃.property.1 α₃.property.2
      (coefficient_degreewise_exact k G S hS) n (barBoundary k G S hS n)
      (coinvariantResolutionBoundary.{u,v,w} k G S P Q H n).hom
      (barBoundary_spec k G S hS n).1 (coinvariantResolutionBoundary_connecting.{u,v,w} k G S P Q H n) z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let E₁ := coinvariantResolutionHomologyIso.{u,v,w} k G P n
  let E₃ := coinvariantResolutionHomologyIso.{u,v,w} k G Q (n+1)
  let b₁ := resolutionBalanceIso.{u,v,w} k G P hP n
  let b₃ := resolutionBalanceIso.{u,v,w} k G Q hQ (n+1)
  let hC := horseshoeImage_shortExact S P Q H (ambientCoinvariantGroups.{u,v,w} k G)
  let δ := hC.δ (-((n+1 : ℕ) : ℤ)) (-(n : ℤ)) (adjacent_negative_degrees n)
  change b₁.symm (E₁.hom (δ z)) = barBoundary k G S hS n (b₃.symm (E₃.hom z))
  apply b₁.injective
  rw [LinearEquiv.apply_symm_apply]
  rw [hb]
  change E₁.hom (δ z) =
    E₁.hom (δ (E₃.inv (b₃ (b₃.symm (E₃.hom z)))))
  rw [LinearEquiv.apply_symm_apply, CategoryTheory.Iso.hom_inv_id_apply]

end ResolutionBoundary
end AdvancedHomologicalAlgebra.DerivedGroupHomology
end
section
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open AdvancedHomologicalAlgebra.DerivedTorComparison

namespace AdvancedHomologicalAlgebra.DerivedGroupHomology
universe u v w x y
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

section RestrictBoundary
variable {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
variable {ι : Type*} {c : ComplexShape ι}
local notation "U" => ModuleCat.restrictScalars f
local notation "Uₕ" => CategoryTheory.Functor.mapHomologicalComplex (ModuleCat.restrictScalars f) c

lemma restrictShortExact (T : ShortComplex (HomologicalComplex (ModuleCat S) c))
    (hT : T.ShortExact) : (T.map Uₕ).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  exact ((HomologicalComplex.shortExact_iff_degreewise_shortExact T).1 hT i).map_of_exact U

lemma restrictHomologyIso_π (K : HomologicalComplex (ModuleCat S) c) (i : ι) :
    (U).map (K.homologyπ i) ≫ (restrictHomologyIso U K i).hom =
      ((K.sc i).mapCyclesIso U).inv ≫ ((Uₕ).obj K).homologyπ i := by
  let V := K.sc i
  let h := ShortComplex.LeftHomologyData.canonical V
  have hH : h.homologyIso = Iso.refl V.homology := by
    apply Iso.ext
    rw [← cancel_epi V.homologyπ, h.homologyπ_comp_homologyIso_hom]
    have hC : h.cyclesIso.hom = 𝟙 V.cycles := by
      rw [← cancel_mono V.iCycles, Category.id_comp]
      exact h.cyclesIso_hom_comp_i
    simp only [hC, Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  have hC : (h.map U).cyclesIso = V.mapCyclesIso U := by
    apply Iso.ext
    rw [← cancel_mono ((U).map V.iCycles), ShortComplex.mapCyclesIso_hom_iCycles]
    exact (h.map U).cyclesIso_hom_comp_i
  change (U).map V.homologyπ ≫ (V.mapHomologyIso U).inv =
    (V.mapCyclesIso U).inv ≫ (V.map U).homologyπ
  rw [h.mapHomologyIso_eq U, hH, ← hC]
  change (U).map V.homologyπ ≫ (U).map (𝟙 V.homology) ≫ (h.map U).homologyIso.inv =
    (h.map U).cyclesIso.inv ≫ (V.map U).homologyπ
  calc
    (U).map V.homologyπ ≫ (U).map (𝟙 V.homology) ≫ (h.map U).homologyIso.inv =
        (U).map V.homologyπ ≫ 𝟙 ((U).obj V.homology) ≫ (h.map U).homologyIso.inv :=
      congrArg (fun g : (U).obj V.homology ⟶ (U).obj V.homology =>
        (U).map V.homologyπ ≫ g ≫ (h.map U).homologyIso.inv) ((U).map_id V.homology)
    _ = (U).map V.homologyπ ≫ (h.map U).homologyIso.inv :=
      congrArg (fun g : (U).obj V.homology ⟶ (V.map U).homology =>
        (U).map V.homologyπ ≫ g) (Category.id_comp (h.map U).homologyIso.inv)
    _ = _ := (h.map U).π_comp_homologyIso_inv

lemma restrictCyclesIso_cyclesMk (K : HomologicalComplex (ModuleCat S) c)
    (i j : ι) (hij : c.next i = j) (x : K.X i) (hx : K.d i j x = 0) :
    ((K.sc i).mapCyclesIso U).hom (((Uₕ).obj K).cyclesMk x j hij hx) =
      K.cyclesMk x j hij hx := by
  apply (ModuleCat.mono_iff_injective (K.iCycles i)).1 inferInstance
  have h := ConcreteCategory.congr_hom (ShortComplex.mapCyclesIso_hom_iCycles (K.sc i) U)
    (((Uₕ).obj K).cyclesMk x j hij hx)
  change K.iCycles i (((K.sc i).mapCyclesIso U).hom
    (((Uₕ).obj K).cyclesMk x j hij hx)) = ((Uₕ).obj K).iCycles i (((Uₕ).obj K).cyclesMk x j hij hx) at h
  exact h.trans ((((Uₕ).obj K).i_cyclesMk x j hij hx).trans (K.i_cyclesMk x j hij hx).symm)

lemma restrictHomologyIso_cyclesMk (K : HomologicalComplex (ModuleCat S) c)
    (i j : ι) (hij : c.next i = j) (x : K.X i) (hx : K.d i j x = 0) :
    (restrictHomologyIso U K i).hom (K.homologyπ i (K.cyclesMk x j hij hx)) =
      ((Uₕ).obj K).homologyπ i (((Uₕ).obj K).cyclesMk x j hij hx) := by
  have h := ConcreteCategory.congr_hom (restrictHomologyIso_π f K i) (K.cyclesMk x j hij hx)
  change (restrictHomologyIso U K i).hom (K.homologyπ i (K.cyclesMk x j hij hx)) =
    ((Uₕ).obj K).homologyπ i (((K.sc i).mapCyclesIso U).inv (K.cyclesMk x j hij hx)) at h
  rw [h, ← restrictCyclesIso_cyclesMk f K i j hij x hx, Iso.hom_inv_id_apply]

lemma restrictHomologyIso_boundary (T : ShortComplex (HomologicalComplex (ModuleCat S) c))
    (hT : T.ShortExact) (i j : ι) (hij : c.Rel i j) :
    (U).map (hT.δ i j hij) ≫ (restrictHomologyIso U T.X₁ j).hom =
      (restrictHomologyIso U T.X₃ i).hom ≫ (restrictShortExact f T hT).δ i j hij := by
  have := hT.epi_g
  have hi := c.next_eq' hij
  apply ModuleCat.hom_ext
  ext z
  obtain ⟨v, rfl⟩ := (ModuleCat.epi_iff_surjective (T.X₃.homologyπ i)).1 inferInstance z
  let x₃ := T.X₃.iCycles i v
  have hx₃ : T.X₃.d i j x₃ = 0 := by
    rw [← hi]
    exact ConcreteCategory.congr_hom (T.X₃.iCycles_d i (c.next i)) v
  obtain ⟨x₂, hx₂⟩ := (ModuleCat.epi_iff_surjective (T.g.f i)).1 inferInstance x₃
  have hz : T.g.f j (T.X₂.d i j x₂) = 0 := by
    rw [← ModuleCat.comp_apply, ← T.g.comm i j, ModuleCat.comp_apply, hx₂, hx₃]
  have hTj := (HomologicalComplex.shortExact_iff_degreewise_shortExact T).1 hT j
  obtain ⟨x₁, hx₁⟩ := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hTj.exact _ |>.1 hz
  have hv : v = T.X₃.cyclesMk x₃ j hi hx₃ := by
    apply (ModuleCat.mono_iff_injective (T.X₃.iCycles i)).1 inferInstance
    exact (T.X₃.i_cyclesMk x₃ j hi hx₃).symm
  rw [hv]
  change (restrictHomologyIso U T.X₁ j).hom ((hT.δ i j hij) (T.X₃.homologyπ i (T.X₃.cyclesMk x₃ j hi hx₃))) =
    (restrictShortExact f T hT).δ i j hij ((restrictHomologyIso U T.X₃ i).hom
      (T.X₃.homologyπ i (T.X₃.cyclesMk x₃ j hi hx₃)))
  have h₁ := hT.δ_apply i j hij x₃ hx₃ x₂ hx₂ x₁ hx₁ _ rfl
  have h₂ := (restrictShortExact f T hT).δ_apply i j hij x₃ hx₃ x₂ hx₂ x₁ hx₁ _ rfl
  erw [h₁, restrictHomologyIso_cyclesMk, restrictHomologyIso_cyclesMk]
  exact h₂.symm

end RestrictBoundary

section DerivedValues
variable [HasDerivedCategory.{x} (ModuleCat.{max u v w} k[G])] [HasDerivedCategory.{y} (ModuleCat.{max u v w} k)]
  [(minus (ModuleCat.{max u v w} k[G])).IsTriangulated] [(minus (ModuleCat.{max u v w} k)).IsTriangulated]
  (D : ExactLeftData.{(max u v w)+1,max u v w,(max u v w)+1,max u v w,x,y}
    (Specification.ambientCoinvariants.{u,v,w} k G))

/-- Restriction of scalars carries the genuine derived connecting map to the
connecting map on the coinvariants of the coefficient horseshoe. -/
lemma derivedResolutionGroupsIso_boundary (S : ShortComplex (ModuleCat.{max u v w} k[G])) (hS : S.ShortExact)
    (P : LeftResolution k[G] S.X₁) (Q : LeftResolution k[G] S.X₃)
    (HP : P.IsProjective) (HQ : Q.IsProjective)
    (H : P103.Specs.Ch10.Horseshoe.ProjectiveData S.f.hom S.g.hom P Q)
    (n : ℕ) :
    (ModuleCat.restrictScalars (Int.castRingHom k)).map (leftBoundary (Specification.ambientCoinvariants.{u,v,w} k G) D hS n) ≫ (derivedResolutionGroupsIso.{u,v,w,x,y} k G D P HP n).hom =
      (derivedResolutionGroupsIso.{u,v,w,x,y} k G D Q HQ (n+1)).hom ≫
        (horseshoeImage_shortExact S P Q H (ambientCoinvariantGroups.{u,v,w} k G)).δ
          (-((n+1 : ℕ) : ℤ)) (-(n : ℤ))
          (by change -((n+1 : ℕ) : ℤ) + 1 = -(n : ℤ); omega) := by
  let C := horseshoeCochain S P Q H
  let a := horseshoeAugmentation S P Q H
  letI : C.X₁.IsStrictlyLE 0 := by
    change (cochainResolution P).IsStrictlyLE 0
    infer_instance
  letI : C.X₂.IsStrictlyLE 0 := by
    change (cochainResolution H.middle).IsStrictlyLE 0
    infer_instance
  letI : C.X₃.IsStrictlyLE 0 := by
    change (cochainResolution Q).IsStrictlyLE 0
    infer_instance
  letI : QuasiIso a.τ₁ := cochainAugmentation_quasiIso P
  letI : QuasiIso a.τ₂ := cochainAugmentation_quasiIso H.middle
  letI : QuasiIso a.τ₃ := cochainAugmentation_quasiIso Q
  let T := C.map ((GroupCoinvariants.coinvariantsFunctor k G).mapHomologicalComplex (.up ℤ))
  let hT : T.ShortExact := horseshoeImage_shortExact S P Q H (GroupCoinvariants.coinvariantsFunctor k G)
  let i : ℤ := -((n+1 : ℕ) : ℤ)
  let j : ℤ := -(n : ℤ)
  have hij : (ComplexShape.up ℤ).Rel i j := by
    change -((n+1 : ℕ) : ℤ) + 1 = -(n : ℤ)
    omega
  have hbC := cochainComputationIso_boundary (Specification.ambientCoinvariants.{u,v,w} k G) D C (horseshoeCochainSplitting S P Q H)
    hS a (cochainResolution_projective P HP)
    (cochainResolution_projective H.middle H.projective) (cochainResolution_projective Q HQ)
    (horseshoeCochain_shortExact S P Q H) hT n
  change leftBoundary (Specification.ambientCoinvariants.{u,v,w} k G) D hS n ≫ (derivedResolutionIso.{u,v,w,x,y} k G D P HP n).hom =
    (derivedResolutionIso.{u,v,w,x,y} k G D Q HQ (n+1)).hom ≫ hT.δ i j hij at hbC
  have hb := congrArg (ModuleCat.restrictScalars (Int.castRingHom k)).map hbC
  simp only [Functor.map_comp] at hb
  have hr := restrictHomologyIso_boundary (Int.castRingHom k) T hT i j hij
  change (ModuleCat.restrictScalars (Int.castRingHom k)).map (hT.δ i j hij) ≫
      (restrictHomologyIso (ModuleCat.restrictScalars (Int.castRingHom k)) (((GroupCoinvariants.coinvariantsFunctor k G).mapHomologicalComplex (.up ℤ)).obj (cochainResolution P)) j).hom =
    (restrictHomologyIso (ModuleCat.restrictScalars (Int.castRingHom k)) (((GroupCoinvariants.coinvariantsFunctor k G).mapHomologicalComplex (.up ℤ)).obj (cochainResolution Q)) i).hom ≫
      (horseshoeImage_shortExact S P Q H (ambientCoinvariantGroups.{u,v,w} k G)).δ i j hij at hr
  dsimp only [derivedResolutionGroupsIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hb, Category.assoc, hr, Category.assoc]

end DerivedValues

section DerivedBarBoundary
variable [HasDerivedCategory.{x} (ModuleCat.{max u v w} k[G])] [HasDerivedCategory.{y} (ModuleCat.{max u v w} k)]
  [(minus (ModuleCat.{max u v w} k[G])).IsTriangulated] [(minus (ModuleCat.{max u v w} k)).IsTriangulated]
  (D : ExactLeftData.{(max u v w)+1,max u v w,(max u v w)+1,max u v w,x,y}
    (Specification.ambientCoinvariants.{u,v,w} k G))

/-- The comparison with the bar model carries the connecting morphism of
actual derived coinvariants to the positive lift-and-boundary map. -/
lemma derivedBarGroupsIso_boundary (S : ShortComplex (ModuleCat.{max u v w} k[G]))
    (hS : S.ShortExact) (n : ℕ) :
    (ModuleCat.restrictScalars (Int.castRingHom k)).map
      (leftBoundary (Specification.ambientCoinvariants.{u,v,w} k G) D hS n) ≫
        (derivedBarGroupsIso.{u,v,w,x,y} k G D S.X₁ n).hom =
      (derivedBarGroupsIso.{u,v,w,x,y} k G D S.X₃ (n+1)).hom ≫
        ModuleCat.ofHom (barBoundary k G S hS n) := by
  let P := coefficientResolutionChoice.{u,v,w} k G S.X₁
  let Q := coefficientResolutionChoice.{u,v,w} k G S.X₃
  obtain ⟨H⟩ := P103.Ch10.Horseshoe.projective_horseshoe k[G] S.X₁ S.X₂ S.X₃
    S.f.hom S.g.hom hS.moduleCat_injective_f
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
    hS.moduleCat_surjective_g P.val Q.val P.property Q.property
  rw [derivedBarGroupsIso_eq.{u,v,w,x,y} k G D P.val P.property n,
    derivedBarGroupsIso_eq.{u,v,w,x,y} k G D Q.val Q.property (n+1)]
  dsimp only [derivedBarGroupsIsoOnResolution, Iso.trans_hom]
  rw [← Category.assoc, derivedResolutionGroupsIso_boundary.{u,v,w,x,y} k G D S hS P.val Q.val
    P.property Q.property H n, Category.assoc,
    coinvariantBarHomologyIso_boundary.{u,v,w} k G S P.val Q.val H n hS P.property Q.property,
    Category.assoc]

end DerivedBarBoundary

section Comparison
variable [HasDerivedCategory.{x} (ModuleCat.{max u v w} k[G])] [HasDerivedCategory.{y} (ModuleCat.{max u v w} k)]
  [(minus (ModuleCat.{max u v w} k[G])).IsTriangulated] [(minus (ModuleCat.{max u v w} k)).IsTriangulated]
  (D : ExactLeftData.{(max u v w)+1,max u v w,(max u v w)+1,max u v w,x,y}
    (Specification.ambientCoinvariants.{u,v,w} k G))

/-- The boundary transported from the genuine derived functor is the boundary
of the original Tor coefficient sequence. -/
lemma transportedDerivedBoundary_agrees (S : ShortComplex (ModuleCat.{max u v w} k[G]))
    (hS : S.ShortExact) (n : ℕ) (z : GroupCoinvariants.GroupHomology k G S.X₃ (n+1)) :
    ((derivedTorIso.{u,v,w,x,y} k G D (n+1)).inv.app S.X₃ ≫
      leftBoundary (Specification.ambientCoinvariants.{u,v,w} k G) D hS n ≫
      (derivedTorIso.{u,v,w,x,y} k G D n).hom.app S.X₁) z =
      coefficientBoundary k G S hS n z := by
  let e := (derivedTorIso.{u,v,w,x,y} k G D (n+1)).app S.X₃
  obtain ⟨w, rfl⟩ := e.toLinearEquiv.surjective z
  have h := ConcreteCategory.congr_hom (derivedBarGroupsIso_boundary.{u,v,w,x,y} k G D S hS n)
    (show (ModuleCat.restrictScalars (Int.castRingHom k)).obj
      ((leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D (n+1)).obj S.X₃) from w)
  apply (torBarIso k G S.X₁ n).injective
  rw [torBarIso_boundary]
  have hw : e.inv (e.hom w) = w := e.hom_inv_id_apply w
  change torBarIso k G S.X₁ n ((derivedTorIso.{u,v,w,x,y} k G D n).hom.app S.X₁
      (leftBoundary (Specification.ambientCoinvariants.{u,v,w} k G) D hS n (e.inv (e.hom w)))) =
    barBoundary k G S hS n (torBarIso k G S.X₃ (n+1) (e.hom w))
  rw [hw, torBarIso_derivedTorIso]
  change _ = barBoundary k G S hS n
    (torBarIso k G S.X₃ (n+1) ((derivedTorIso.{u,v,w,x,y} k G D (n+1)).hom.app S.X₃ w))
  rw [torBarIso_derivedTorIso]
  exact h


lemma derivedTorIso_connecting (S : ShortComplex (ModuleCat.{max u v w} k[G]))
    (hS : S.ShortExact) (n : ℕ) :
    P103.Specs.Ch10.HomologySequence.Connecting (torChainMap k G S.f)
      (torChainMap k G S.g) (n+1) n
      (((derivedTorIso.{u,v,w,x,y} k G D (n+1)).inv.app S.X₃ ≫
        leftBoundary (Specification.ambientCoinvariants.{u,v,w} k G) D hS n ≫
        (derivedTorIso.{u,v,w,x,y} k G D n).hom.app S.X₁).hom.toAddMonoidHom.toIntLinearMap) := by
  have h :
      (((derivedTorIso.{u,v,w,x,y} k G D (n+1)).inv.app S.X₃ ≫
        leftBoundary (Specification.ambientCoinvariants.{u,v,w} k G) D hS n ≫
        (derivedTorIso.{u,v,w,x,y} k G D n).hom.app S.X₁).hom.toAddMonoidHom.toIntLinearMap) =
      coefficientBoundary k G S hS n := by
    apply LinearMap.ext
    intro z
    exact transportedDerivedBoundary_agrees.{u,v,w,x,y} k G D S hS n z
  rw [h]
  exact coefficientBoundary_tor_connecting k G S hS n

end Comparison

end AdvancedHomologicalAlgebra.DerivedGroupHomology
end


section DegreeZeroNormalization
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000
set_option quotPrecheck false
set_option hygiene false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidAlgebra ModuleCat.Algebra
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open P103.Ch11.FlatResolutions (leftZeroTensor leftZeroTensor_class)
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open AdvancedHomologicalAlgebra.DerivedTorComparison
open private cochainComputationIso_counit mapExtendTerm_XIso from
  MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DerivedTorComparison

namespace AdvancedHomologicalAlgebra.DerivedGroupHomology
universe u v w x y
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

local notation "A" => ModuleCat.{max u v w} k[G]
local notation "B" => ModuleCat.{max u v w} k
local notation "Z" => ModuleCat.{max u v w} ℤ
local notation "F" => Specification.ambientCoinvariants.{u,v,w} k G
local notation "U" => (ModuleCat.restrictScalars (Int.castRingHom k) : B ⥤ Z)
local notation "V" => ambientCoinvariantGroups.{u,v,w} k G
local notation "T" => tensorCoefficients.{u,v,max u v w} k G
local notation "e" => ComplexShape.embeddingDownNat
local notation "c" => ComplexShape.down ℕ
local notation "c'" => ComplexShape.up ℤ

private lemma cochainAugmentation_f_zero {M : A} (Q : LeftResolution k[G] M) :
    (cochainAugmentation Q).f 0 ≫ (singleObjXSelf c' 0 M).hom =
      (Q.complex.extendXIso e (show (e).f 0 = 0 from rfl)).hom ≫ ModuleCat.ofHom Q.ε := by
  simp only [cochainAugmentation, HomologicalComplex.comp_f,
    HomologicalComplex.extendSingleIso_hom_f, HomologicalComplex.extendMap_f _ _
      (show (e).f 0 = 0 from rfl), Category.assoc, Iso.inv_hom_id_assoc,
    ChainComplex.single₀ObjXSelf, Iso.refl_hom, Category.id_comp, Iso.inv_hom_id,
    Category.comp_id, augmentation, ChainComplex.toSingle₀Equiv_symm_apply_f_zero]

private def mappedCoinvariantAugmentation {M : A} (Q : LeftResolution k[G] M) :
    ((F).mapHomologicalComplex c').obj (cochainResolution Q) ⟶
      (CochainComplex.singleFunctor B 0).obj ((F).obj M) :=
  ((F).mapHomologicalComplex c').map (cochainAugmentation Q) ≫
    ((F).mapCochainComplexSingleFunctor 0).hom.app M

private lemma mappedCoinvariantAugmentation_f_zero {M : A} (Q : LeftResolution k[G] M) :
    (mappedCoinvariantAugmentation.{u,v,w} k G Q).f 0 ≫
        (singleObjXSelf c' 0 ((F).obj M)).hom =
      (F).map (Q.complex.extendXIso e (show (e).f 0 = 0 from rfl)).hom ≫
        (F).map (ModuleCat.ofHom Q.ε) := by
  rw [mappedCoinvariantAugmentation, HomologicalComplex.comp_f]
  change (F).map ((cochainAugmentation Q).f 0) ≫
    ((singleMapHomologicalComplex F c' 0).hom.app M).f 0 ≫
      (singleObjXSelf c' 0 ((F).obj M)).hom = _
  rw [singleMapHomologicalComplex_hom_app_self, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, ← (F).map_comp, ← (F).map_comp, cochainAugmentation_f_zero.{u,v,w} k G Q]

private lemma coefficientTensorZero_projection {M : A} (Q : LeftResolution k[G] M) :
    let K := coefficientTensorComplex.{u,v,w} k G Q.complex
    K.homologyπ 0 ≫ (quotientHomologyIso K 0).hom ≫
      (leftZeroTensor (GroupCoinvariants.TrivialRight k G) Q).toModuleIso.hom =
    K.iCycles 0 ≫ (T).map (ModuleCat.ofHom Q.ε) := by
  intro K
  rw [quotientHomologyIso_projection_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change leftZeroTensor (GroupCoinvariants.TrivialRight k G) Q
    (homologyClass _ 0 ((K.sc 0).moduleCatCyclesIso.hom z)) =
    tensorMap LinearMap.id Q.ε (K.iCycles 0 z)
  rw [leftZeroTensor_class]
  congr 1

private lemma coefficientTensorZero_balance {M : A} (P : LeftResolution k[G]ᵐᵒᵖ
    (GroupCoinvariants.TrivialRight k G)) (Q : LeftResolution k[G] M)
    (α : Augmentations P Q) (hL : QuasiIsomorphism α.left)
    (hR : QuasiIsomorphism α.right) (z : TorWith P M 0) :
    leftZeroTensor (GroupCoinvariants.TrivialRight k G) Q (balanceEquiv α hL hR 0 z) =
      P103.Ch11.ExtTorDefinitions.torZero P M z := by
  obtain ⟨q, rfl⟩ := (hL 0).surjective z
  have hn := P103.Ch11.FlatResolutions.leftZero_normalization P Q α q
  have hl := P103.Ch11.FlatResolutions.leftZero_augmentation P Q (homologyMap α.right 0 q)
  have hb : balanceEquiv α hL hR 0 (homologyMap α.left 0 q) =
      homologyMap α.right 0 q := by
    change
      (LinearEquiv.ofBijective _ (hR 0))
        ((LinearEquiv.ofBijective _ (hL 0)).symm ((LinearEquiv.ofBijective _ (hL 0)) q)) =
          homologyMap α.right 0 q
    rw [LinearEquiv.symm_apply_apply]
    rfl
  rw [hb, ← hl, hn]

private lemma homologyProjection_extend_map
    {C : Type*} [Category* C] [Abelian C]
    (L : CochainComplex C ℤ) (J TQ : ChainComplex C ℕ)
    (f : L ⟶ J.extend e) (g : J ⟶ TQ) {X : C}
    (p : TQ.homology 0 ⟶ X) (a : TQ.X 0 ⟶ X)
    (hp : TQ.homologyπ 0 ≫ p = TQ.iCycles 0 ≫ a) :
    L.homologyπ 0 ≫ HomologicalComplex.homologyMap f 0 ≫
      (J.extendHomologyIso e (show (e).f 0 = 0 from rfl)).hom ≫
        HomologicalComplex.homologyMap g 0 ≫ p =
      L.iCycles 0 ≫ f.f 0 ≫
        (J.extendXIso e (show (e).f 0 = 0 from rfl)).hom ≫ g.f 0 ≫ a := by
  rw [homologyπ_naturality_assoc, homologyπ_extendHomologyIso_hom_assoc,
    homologyπ_naturality_assoc, hp, cyclesMap_i_assoc, extendCyclesIso_hom_iCycles_assoc,
    cyclesMap_i_assoc]

private lemma homologyProjection_stalk
    {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (X : C) (q : K ⟶ (single C c' 0).obj X) :
    K.homologyπ 0 ≫ HomologicalComplex.homologyMap q 0 ≫
      (singleObjHomologySelfIso c' 0 X).hom =
    K.iCycles 0 ≫ q.f 0 ≫ (singleObjXSelf c' 0 X).hom := by
  rw [homologyπ_naturality_assoc, homologyπ_singleObjHomologySelfIso_hom,
    singleObjCyclesSelfIso_hom, cyclesMap_i_assoc]

private lemma coinvariantResolutionZero_projection {M : A} (Q : LeftResolution k[G] M) :
    let K := ((F).mapHomologicalComplex c').obj (cochainResolution Q)
    (restrictHomologyIso U K 0).hom ≫
      (coinvariantResolutionHomologyIso.{u,v,w} k G Q 0).hom ≫
      (leftZeroTensor (GroupCoinvariants.TrivialRight k G) Q).toModuleIso.hom =
    (U).map (HomologicalComplex.homologyMap (mappedCoinvariantAugmentation.{u,v,w} k G Q) 0 ≫
      (singleObjHomologySelfIso c' 0 ((F).obj M)).hom) ≫
      (ambientCoinvariantTensorFunctorIso.{u,v,w} k G).hom.app M := by
  intro K
  let L := ((U).mapHomologicalComplex c').obj K
  let J := ((V).mapHomologicalComplex c).obj Q.complex
  let TQ := coefficientTensorComplex.{u,v,w} k G Q.complex
  let h : (e).f 0 = 0 := rfl
  let f : L ⟶ J.extend e := (mapExtendIso V Q.complex e).hom
  let g : J ⟶ TQ := ((coinvariantTensorComplexIso.{u,v,w} k G c).app Q.complex).hom
  let η := (ambientCoinvariantTensorFunctorIso.{u,v,w} k G).hom
  let q := mappedCoinvariantAugmentation.{u,v,w} k G Q
  have hg : g.f 0 = η.app (Q.complex.X 0) := rfl
  have hf : f.f 0 ≫ (J.extendXIso e h).hom =
      (V).map (Q.complex.extendXIso e h).hom :=
    mapExtendTerm_XIso V Q.complex ((e).r_eq_some h)
  have hzero : L.homologyπ 0 ≫ (coinvariantResolutionHomologyIso.{u,v,w} k G Q 0).hom ≫
      (leftZeroTensor (GroupCoinvariants.TrivialRight k G) Q).toModuleIso.hom =
      L.iCycles 0 ≫ f.f 0 ≫ (J.extendXIso e h).hom ≫ g.f 0 ≫
        (T).map (ModuleCat.ofHom Q.ε) := by
    change L.homologyπ 0 ≫ HomologicalComplex.homologyMap f 0 ≫
        (J.extendHomologyIso e h).hom ≫ HomologicalComplex.homologyMap g 0 ≫
        (quotientHomologyIso TQ 0).hom ≫
        (leftZeroTensor (GroupCoinvariants.TrivialRight k G) Q).toModuleIso.hom = _
    exact homologyProjection_extend_map L J TQ f g _ _
      (coefficientTensorZero_projection.{u,v,w} k G Q)
  have hAug := homologyProjection_stalk K ((F).obj M) q
  have hCycle :
      ((K.sc 0).mapCyclesIso U).inv ≫ L.iCycles 0 = (U).map (K.iCycles 0) := by
    apply (cancel_epi ((K.sc 0).mapCyclesIso U).hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact (ShortComplex.mapCyclesIso_hom_iCycles (K.sc 0) U).symm
  apply (cancel_epi ((U).map (K.homologyπ 0))).mp
  rw [← Category.assoc ((U).map (K.homologyπ 0)), restrictHomologyIso_π,
    Category.assoc, hzero, ← Category.assoc ((K.sc 0).mapCyclesIso U).inv, hCycle]
  rw [← (U).map_comp_assoc, hAug, CategoryTheory.Functor.map_comp, Category.assoc,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc (f.f 0), hf, hg, ← η.naturality]
  rw [← (U).map_comp_assoc, mappedCoinvariantAugmentation_f_zero.{u,v,w} k G Q]
  change (V).map (Q.complex.extendXIso e h).hom ≫
      (V).map (ModuleCat.ofHom Q.ε) ≫ η.app M =
    (U).map ((F).map (Q.complex.extendXIso e h).hom ≫ (F).map (ModuleCat.ofHom Q.ε)) ≫
      η.app M
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

variable [HasDerivedCategory.{x} A] [HasDerivedCategory.{y} B]
  [(minus A).IsTriangulated] [(minus B).IsTriangulated]
  (D : ExactLeftData.{(max u v w)+1,max u v w,(max u v w)+1,max u v w,x,y} F)

private lemma derivedTorIso_counit_eq {M : A} (z : (leftValue F D 0).obj M) :
    GroupCoinvariants.coinvariantTensorIso M (Specification.counitZero.{u,v,w,x,y} k G D M z) =
      torZero k G M ((derivedTorIso.{u,v,w,x,y} k G D 0).hom.app M z) := by
  let Q := (coefficientResolutionChoice.{u,v,w} k G M).val
  let hQ := (coefficientResolutionChoice.{u,v,w} k G M).property
  let K := cochainResolution Q
  let p := cochainAugmentation Q
  let q := mappedCoinvariantAugmentation.{u,v,w} k G Q
  let eD := derivedResolutionIso.{u,v,w,x,y} k G D Q hQ 0
  let eG := derivedResolutionGroupsIso.{u,v,w,x,y} k G D Q hQ 0
  let eQ := coinvariantResolutionHomologyIso.{u,v,w} k G Q 0
  let eB := resolutionBalanceIso.{u,v,w} k G Q hQ 0
  let γ := leftZeroTensor (GroupCoinvariants.TrivialRight k G) Q
  let α := barTensorAugmentations.{u,v,w} k G Q hQ
  have hc : Specification.counitZero.{u,v,w,x,y} k G D M =
      eD.hom ≫ HomologicalComplex.homologyMap q 0 ≫
        (singleObjHomologySelfIso c' 0 ((F).obj M)).hom :=
    cochainComputationIso_counit F D M K p (cochainAugmentation_quasiIso Q)
      (cochainResolution_projective Q hQ)
  have hv := ConcreteCategory.congr_hom (coinvariantResolutionZero_projection.{u,v,w} k G Q)
    (show (U).obj ((((F).mapHomologicalComplex c').obj K).homology 0) from eD.hom z)
  change γ (eQ.hom (eG.hom z)) =
    GroupCoinvariants.coinvariantTensorIso M
      ((HomologicalComplex.homologyMap q 0 ≫
        (singleObjHomologySelfIso c' 0 ((F).obj M)).hom) (eD.hom z)) at hv
  have hb :
      eB (torBarIso k G M 0 ((derivedTorIso.{u,v,w,x,y} k G D 0).hom.app M z)) =
        eQ.hom (eG.hom z) := by
    rw [torBarIso_derivedTorIso]
    change eB (eB.symm _) = _
    exact eB.apply_symm_apply _
  rw [hc]
  change GroupCoinvariants.coinvariantTensorIso M
      ((HomologicalComplex.homologyMap q 0 ≫
        (singleObjHomologySelfIso c' 0 ((F).obj M)).hom) (eD.hom z)) = _
  rw [← hv, ← hb]
  change γ (balanceEquiv α.val α.property.1 α.property.2 0
      (torBarIso k G M 0 ((derivedTorIso.{u,v,w,x,y} k G D 0).hom.app M z))) = _
  rw [coefficientTensorZero_balance.{u,v,w} k G (barResolution k G) Q α.val
    α.property.1 α.property.2, torBarAugmentation_zero k G]

/-- The balanced comparison identifies the derived counit with the original
right-resolution augmentation and the scalar-valued coinvariant formula. -/
lemma derivedTorIso_zero_counit (M : A) (a : GroupCoinvariants.TrivialRight k G) (m : M) :
    Specification.counitZero.{u,v,w,x,y} k G D M ((derivedTorIso.{u,v,w,x,y} k G D 0).inv.app M
      ((torZero k G M).symm (P103.BalancedTensor.tmul k[G] a m))) =
      GroupCoinvariants.trivialScalar k G a • GroupCoinvariants.quotientMap k G M
        ((RestrictScalars.addEquiv k k[G] M).symm m) := by
  let z := (torZero k G M).symm (P103.BalancedTensor.tmul k[G] a m)
  apply (GroupCoinvariants.coinvariantTensorIso M).injective
  rw [derivedTorIso_counit_eq.{u,v,w,x,y} k G D]
  change torZero k G M ((derivedTorIso.{u,v,w,x,y} k G D 0).hom.app M
      ((derivedTorIso.{u,v,w,x,y} k G D 0).inv.app M z)) = _
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id_app, ModuleCat.id_apply]
  change _ = GroupCoinvariants.coinvariantTensorIso M
    ((GroupCoinvariants.coinvariantTensorIso M).symm (P103.BalancedTensor.tmul k[G] a m))
  rw [LinearEquiv.apply_symm_apply]
  exact AddEquiv.apply_symm_apply _ _

end AdvancedHomologicalAlgebra.DerivedGroupHomology
end
end DegreeZeroNormalization



section
open CategoryTheory
open scoped MonoidAlgebra
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open P103.Specs.Ch10.HomologySequence
namespace AdvancedHomologicalAlgebra.DerivedGroupHomology
universe u v w x y
variable (k : Type u) (G : Type v) [CommRing k] [Group G]
  [HasDerivedCategory.{x} (ModuleCat.{max u v w} k[G])]
  [HasDerivedCategory.{y} (ModuleCat.{max u v w} k)]
  [(minus (ModuleCat.{max u v w} k[G])).IsTriangulated]
  [(minus (ModuleCat.{max u v w} k)).IsTriangulated]
  (D : ExactLeftData.{(max u v w)+1,max u v w,(max u v w)+1,max u v w,x,y}
    (Specification.ambientCoinvariants.{u,v,w} k G))

/-- The ambient comparison identifies the actual stalk counit and the
positive coefficient connectors on the canonical Tor complex. -/
theorem ambientDerivedComparison :
    ∃ E : ∀ n : ℕ, leftValue (Specification.ambientCoinvariants.{u,v,w} k G) D n ≅
        kHomologyFunctor.{u,v,max u v w} k G n,
      (∀ (M : ModuleCat.{max u v w} k[G])
        (a : GroupCoinvariants.TrivialRight k G) (m : M),
        Specification.counitZero k G D M ((E 0).inv.app M
          ((torZero k G M).symm (P103.BalancedTensor.tmul k[G] a m))) =
            GroupCoinvariants.trivialScalar k G a • GroupCoinvariants.quotientMap k G M
              ((RestrictScalars.addEquiv k k[G] M).symm m)) ∧
      (∀ (S : ShortComplex (ModuleCat.{max u v w} k[G])) (hS : S.ShortExact) (n : ℕ),
        Connecting (torChainMap k G S.f) (torChainMap k G S.g) (n+1) n
          (((E (n+1)).inv.app S.X₃ ≫
            leftBoundary (Specification.ambientCoinvariants.{u,v,w} k G) D hS n ≫
            (E n).hom.app S.X₁).hom.toAddMonoidHom.toIntLinearMap)) := by
  refine ⟨derivedTorIso.{u,v,w,x,y} k G D, ?_, derivedTorIso_connecting.{u,v,w,x,y} k G D⟩
  intro M a m
  exact derivedTorIso_zero_counit.{u,v,w,x,y} k G D M a m

end AdvancedHomologicalAlgebra.DerivedGroupHomology
end


section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped MonoidAlgebra
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
namespace AdvancedHomologicalAlgebra.DerivedGroupHomology
universe u v w x y
variable (k : Type u) (G : Type v) [CommRing k] [Group G]
section CarrierComparison

open CategoryTheory.Functor
open scoped ModuleCat.Algebra
open Specification
open P103.Specs.Ch10.HomologySequence
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

set_option maxHeartbeats 1200000
set_option maxRecDepth 1800

/-- Invert the coefficient lift on each term of the fixed Tor complex. -/
private def lowerTorChainMap (M : ModuleCat.{w} k[G]) :
    tensorComplex (canonicalResolution k G).val.complex ((liftCoefficients.{u,v,w} k G).obj M) ⟶
      tensorComplex (canonicalResolution k G).val.complex M where
  f n := ModuleCat.ofHom (tensorMap LinearMap.id
    (ULift.moduleEquiv.toLinearMap : (liftCoefficients.{u,v,w} k G).obj M →ₗ[k[G]] M))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl

private lemma liftTorChainMap_lowerTorChainMap (M : ModuleCat.{w} k[G]) :
    liftTorChainMap k G M ≫ lowerTorChainMap k G M = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext j
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  rfl

private lemma lowerTorChainMap_liftTorChainMap (M : ModuleCat.{w} k[G]) :
    lowerTorChainMap k G M ≫ liftTorChainMap k G M = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext j
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  rfl

private lemma liftTorChainMap_natural {M N : ModuleCat.{w} k[G]} (f : M ⟶ N) :
    torChainMap k G f ≫ liftTorChainMap k G N =
      liftTorChainMap k G M ≫ torChainMap k G ((liftCoefficients.{u,v,w} k G).map f) := by
  apply HomologicalComplex.Hom.ext
  funext j
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  rfl

private def liftTorHomologyEquiv (M : ModuleCat.{w} k[G]) (n : ℕ) :
    GroupCoinvariants.GroupHomology k G M n ≃ₗ[ℤ]
      GroupCoinvariants.GroupHomology k G ((liftCoefficients.{u,v,w} k G).obj M) n :=
  LinearEquiv.ofLinearMap (homologyMap (liftTorChainMap k G M) n)
    (homologyMap (lowerTorChainMap k G M) n)
    (by rw [← P103.Ch10.Complexes.homologyMap_comp, lowerTorChainMap_liftTorChainMap,
      P103.Ch10.Complexes.homologyMap_id])
    (by rw [← P103.Ch10.Complexes.homologyMap_comp, liftTorChainMap_lowerTorChainMap,
      P103.Ch10.Complexes.homologyMap_id])

private lemma liftTorHomology_natural {M N : ModuleCat.{w} k[G]} (f : M ⟶ N)
    (n : ℕ) (z : GroupCoinvariants.GroupHomology k G M n) :
    homologyMap (liftTorChainMap k G N) n ((homologyFunctor k G n).map f z) =
      (homologyFunctor k G n).map ((liftCoefficients.{u,v,w} k G).map f)
        (homologyMap (liftTorChainMap k G M) n z) := by
  change (homologyMap (liftTorChainMap k G N) n).comp ((homologyFunctor k G n).map f).hom z =
    ((homologyFunctor k G n).map ((liftCoefficients.{u,v,w} k G).map f)).hom.comp
      (homologyMap (liftTorChainMap k G M) n) z
  rw [homologyFunctor_map_hom, homologyFunctor_map_hom, ← P103.Ch10.Complexes.homologyMap_comp,
    liftTorChainMap_natural, P103.Ch10.Complexes.homologyMap_comp]
  rfl

attribute [local instance] torModule

private def liftTorLinearEquiv (M : ModuleCat.{w} k[G]) (n : ℕ) :
    GroupCoinvariants.GroupHomology k G M n ≃ₗ[k]
      GroupCoinvariants.GroupHomology k G ((liftCoefficients.{u,v,w} k G).obj M) n where
  toAddEquiv := (liftTorHomologyEquiv k G M n).toAddEquiv
  map_smul' r z := by
    have h : (liftCoefficients.{u,v,w} k G).map (scalarCoefficientMap k G M r) =
        scalarCoefficientMap k G ((liftCoefficients.{u,v,w} k G).obj M) r := by
      ext x
      rfl
    change homologyMap (liftTorChainMap k G M) n
      ((homologyFunctor k G n).map (scalarCoefficientMap k G M r) z) =
        (homologyFunctor k G n).map (scalarCoefficientMap k G ((liftCoefficients.{u,v,w} k G).obj M) r)
          (homologyMap (liftTorChainMap k G M) n z)
    rw [← h]
    exact liftTorHomology_natural k G (scalarCoefficientMap k G M r) n z

/-- The original and lifted Tor functors agree via the class map of the coefficient lift. -/
private def liftTorIso (n : ℕ) : kHomologyFunctor.{u,v,w} k G n ≅
    liftCoefficients.{u,v,w} k G ⋙ kHomologyFunctor.{u,v,max u v w} k G n :=
  NatIso.ofComponents (fun M => (liftTorLinearEquiv k G M n).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact liftTorHomology_natural k G f n)


section DerivedTransport

variable [HasDerivedCategory.{x} (ModuleCat.{max u v w} k[G])]
  [HasDerivedCategory.{y} (ModuleCat.{max u v w} k)]
  [(minus (ModuleCat.{max u v w} k[G])).IsTriangulated]
  [(minus (ModuleCat.{max u v w} k)).IsTriangulated]
variable (D : ExactLeftData.{(max u v w)+1,max u v w,(max u v w)+1,max u v w,x,y}
  (ambientCoinvariants.{u,v,w} k G))

private abbrev AmbientDerivedIso :=
  ∀ n : ℕ, leftValue (ambientCoinvariants.{u,v,w} k G) D n ≅
    kHomologyFunctor.{u,v,max u v w} k G n

private def restrictDerivedIso (E : AmbientDerivedIso.{u,v,w,x,y} k G D) :
    OriginalDerivedCoordinates k G D :=
  fun n => isoWhiskerLeft (liftCoefficients.{u,v,w} k G) (E n) ≪≫ (liftTorIso k G n).symm

private lemma restrictDerivedIso_lift (E : AmbientDerivedIso.{u,v,w,x,y} k G D)
    (M : ModuleCat.{w} k[G]) (n : ℕ) (z : (leftValue (ambientCoinvariants.{u,v,w} k G) D n).obj
      ((liftCoefficients.{u,v,w} k G).obj M)) :
    (E n).hom.app ((liftCoefficients.{u,v,w} k G).obj M) z =
      homologyMap (liftTorChainMap k G M) n ((restrictDerivedIso k G D E n).hom.app M z) := by
  change (E n).hom.app ((liftCoefficients.{u,v,w} k G).obj M) z =
    (liftTorIso k G n).hom.app M ((liftTorIso k G n).inv.app M
      ((E n).hom.app ((liftCoefficients.{u,v,w} k G).obj M) z))
  exact ((liftTorIso k G n).app M).inv_hom_id_apply _ |>.symm

private lemma restrictDerivedBoundary_lift (E : AmbientDerivedIso.{u,v,w,x,y} k G D)
    (S : ShortComplex (ModuleCat.{w} k[G])) (hS : S.ShortExact) (n : ℕ)
    (z : GroupCoinvariants.GroupHomology k G S.X₃ (n+1)) :
    homologyMap (liftTorChainMap k G S.X₁) n
      (transportedDerivedBoundary k G D (restrictDerivedIso k G D E) S hS n z) =
      ((E (n+1)).inv.app ((liftCoefficients.{u,v,w} k G).obj S.X₃) ≫
        leftBoundary (ambientCoinvariants.{u,v,w} k G) D (hS.map_of_exact (liftCoefficients.{u,v,w} k G)) n ≫
        (E n).hom.app ((liftCoefficients.{u,v,w} k G).obj S.X₁))
          (homologyMap (liftTorChainMap k G S.X₃) (n+1) z) := by
  change homologyMap (liftTorChainMap k G S.X₁) n
    ((restrictDerivedIso k G D E n).hom.app S.X₁
      (leftBoundary (ambientCoinvariants.{u,v,w} k G) D (hS.map_of_exact (liftCoefficients.{u,v,w} k G)) n
        ((E (n+1)).inv.app ((liftCoefficients.{u,v,w} k G).obj S.X₃)
          (homologyMap (liftTorChainMap k G S.X₃) (n+1) z)))) = _
  rw [← restrictDerivedIso_lift]
  rfl

/-- Transport the ambient representative formula along the coefficient lift. -/
private lemma restrictDerivedBoundary_connecting (E : AmbientDerivedIso.{u,v,w,x,y} k G D)
    (S : ShortComplex (ModuleCat.{w} k[G])) (hS : S.ShortExact) (n : ℕ)
    (h : Connecting (torChainMap k G ((liftCoefficients.{u,v,w} k G).map S.f))
      (torChainMap k G ((liftCoefficients.{u,v,w} k G).map S.g)) (n+1) n
      (((E (n+1)).inv.app ((liftCoefficients.{u,v,w} k G).obj S.X₃) ≫
        leftBoundary (ambientCoinvariants.{u,v,w} k G) D (hS.map_of_exact (liftCoefficients.{u,v,w} k G)) n ≫
        (E n).hom.app ((liftCoefficients.{u,v,w} k G).obj S.X₁)).hom.toAddMonoidHom.toIntLinearMap)) :
    Connecting (torChainMap k G S.f) (torChainMap k G S.g) (n+1) n
      (transportedDerivedBoundary k G D (restrictDerivedIso k G D E) S hS n).hom.toAddMonoidHom.toIntLinearMap := by
  intro z b a hb ha
  let α := liftTorChainMap k G S.X₁
  let β := liftTorChainMap k G S.X₂
  let γ := liftTorChainMap k G S.X₃
  have square₁ := liftTorChainMap_natural k G S.f
  have square₂ := liftTorChainMap_natural k G S.g
  apply (liftTorHomologyEquiv k G S.X₁ n).injective
  change homologyMap α n
    (transportedDerivedBoundary k G D (restrictDerivedIso k G D E) S hS n
      (homologyClass _ _ z)) = homologyClass _ n (cyclesMap α n a)
  rw [restrictDerivedBoundary_lift]
  exact h (cyclesMap γ (n+1) z) ((β.f (n+1)).hom b) (cyclesMap α n a)
    (by
      have H := congrArg (fun f => (f.f (n+1)).hom b) square₂
      change (γ.f (n+1)).hom (((torChainMap k G S.g).f (n+1)).hom b) = _ at H
      rw [hb] at H
      exact H.symm)
    (by
      have H := congrArg (fun f => (f.f n).hom a.val) square₁
      change (β.f n).hom (((torChainMap k G S.f).f n).hom a.val) = _ at H
      rw [ha, ← P103.Ch10.HomologySequence.comm_apply β (n+1) n b] at H
      exact H.symm)

private theorem comparisonOfAmbient
    (E : AmbientDerivedIso.{u,v,w,x,y} k G D)
    (h0 : ∀ (M : ModuleCat.{max u v w} k[G])
      (a : GroupCoinvariants.TrivialRight k G) (m : M),
      counitZero k G D M ((E 0).inv.app M
        ((torZero k G M).symm (P103.BalancedTensor.tmul k[G] a m))) =
          GroupCoinvariants.trivialScalar k G a • GroupCoinvariants.quotientMap k G M
            ((RestrictScalars.addEquiv k k[G] M).symm m))
    (hConn : ∀ (S : ShortComplex (ModuleCat.{max u v w} k[G])) (hS : S.ShortExact) (n : ℕ),
      Connecting (torChainMap k G S.f) (torChainMap k G S.g) (n+1) n
        (((E (n+1)).inv.app S.X₃ ≫ leftBoundary (ambientCoinvariants.{u,v,w} k G) D hS n ≫
          (E n).hom.app S.X₁).hom.toAddMonoidHom.toIntLinearMap))
    (hSeq : Specification.CoefficientSequenceType.{u,v,w}) :
    DerivedComparisonStatement k G D := by
  obtain ⟨b, δ, hb, hbNaturality, hδ, _, _⟩ := hSeq k G
  refine ⟨restrictDerivedIso k G D E, b, ⟨E, h0, hConn, restrictDerivedIso_lift k G D E⟩,
    hb, hbNaturality, ?_⟩
  intro S hS n
  have h := restrictDerivedBoundary_connecting k G D E S hS n
    (hConn (S.map (liftCoefficients.{u,v,w} k G)) (hS.map_of_exact (liftCoefficients.{u,v,w} k G)) n)
  refine ⟨h, ?_⟩
  obtain ⟨hex, hδCanon, hδBar, _⟩ := hδ S hS n
  have heq := P103.Ch10.HomologySequence.connecting_unique
    (torChainMap k G S.f) (torChainMap k G S.g) hex (show
      (ComplexShape.down ℕ).Rel (n+1) n from rfl) (δ S hS n) hδCanon _ h
  rw [heq]
  exact hδBar

end DerivedTransport

theorem coefficientDerivedComparison : Specification.DerivedComparisonType.{u,v,w,x,y} := by
  intro k G _ _ _ _ hA hE
  let := hA
  let := hE
  intro D
  obtain ⟨E, h0, hConn⟩ := ambientDerivedComparison.{u,v,w,x,y} k G D
  exact comparisonOfAmbient.{u,v,w,x,y} k G D E h0 hConn coefficientSequence

theorem coefficientDerivedValues : Specification.DerivedValuesType.{u,v,w,x,y} := by
  intro k G _ _ _ _ hA hE
  let := hA
  let := hE
  intro D
  obtain ⟨e, _, h, _⟩ := coefficientDerivedComparison k G hA hE D
  exact ⟨e, h⟩

theorem coefficientDerivedExists : Specification.DerivedCoinvariantsType.{u,v,w} := by
  intro k G _ _
  let := HasDerivedCategory.standard (ModuleCat.{max u v w} k[G])
  let := HasDerivedCategory.standard (ModuleCat.{max u v w} k)
  obtain ⟨hA, hE, ⟨D⟩⟩ := AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor.existence
    (ModuleCat.{max u v w} k[G]) (ModuleCat.{max u v w} k) (ambientCoinvariants.{u,v,w} k G)
  exact ⟨hA, hE, D, coefficientDerivedComparison k G hA hE D⟩

end CarrierComparison

end AdvancedHomologicalAlgebra.DerivedGroupHomology
end
