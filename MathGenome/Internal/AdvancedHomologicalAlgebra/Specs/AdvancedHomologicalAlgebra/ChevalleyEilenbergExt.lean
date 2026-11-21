import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ChevalleyEilenbergComplex
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ExtShiftedHom
import Mathlib.Algebra.Module.RingHom

/-! HA-A07, source lines 3219–3274. All rings, including zero rings, and
free Lie modules of unrestricted rank. Ext is P103's actual resolution Hom
quotient. The comparison is evaluation, with unsigned precomposition. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions

namespace AdvancedHomologicalAlgebra.CE.Ext
open scoped TensorProduct
universe u v w
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

/-- The trivial U-module structure is restriction along the actual augmentation. -/
abbrev trivialModule : Module (U k g) k :=
  Module.compHom k (Shared.Lie.augmentation k g).toRingHom

/-- Exactness of the actual augmented boundary, rather than an assumed
resolution certificate in the main theorem. -/
def AugmentedExact (d : BoundaryFamily k g) : Prop :=
  Function.Surjective (augmentation k g) ∧
  LinearMap.range ((d 0).restrictScalars k) = LinearMap.ker (augmentation k g) ∧
  ∀ n, LinearMap.range (d (n+1)) = LinearMap.ker (d n)

/-- The natural-number chain complex on the original tensor products. -/
abbrev chain (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d) :
    ChainComplex (ModuleCat.{max u v} (U k g)) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of (U k g) (V k g n))
    (fun n => ModuleCat.ofHom (d n)) (fun n => by
      apply ModuleCat.hom_ext
      exact hc.1 n)

attribute [local instance] trivialModule

/-- The genuine U-linear augmentation, with the above trivial action. -/
def augmentationLinear (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d) :
    V k g 0 →ₗ[U k g] k where
  toFun := augmentation k g
  map_add' := map_add _
  map_smul' a z := hc.2.2 a z

/-- Packaging actual exactness produces the ordinary P103 resolution. -/
def resolution (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d)
    (he : AugmentedExact k g d) : LeftResolution (U k g) k where
  complex := chain k g d hc
  ε := augmentationLinear k g d hc
  surjective := he.1
  exact_zero := by
    ext z
    change (∃ y, ((chain k g d hc).d 1 0).hom y = z) ↔ augmentation k g z = 0
    simp only [chain, ChainComplex.of_d, ModuleCat.hom_ofHom]
    exact SetLike.ext_iff.mp he.2.1 z
  exact_succ n := by
    change LinearMap.range ((chain k g d hc).d ((n+1)+1) (n+1)).hom =
      LinearMap.ker ((chain k g d hc).d (n+1) n).hom
    simpa only [chain, ChainComplex.of_d, ModuleCat.hom_ofHom] using he.2.2 n

variable (M : Type w) [AddCommGroup M] [Module k M]

/-- The printed CE cochain complex, for any actual square-zero coboundary. -/
abbrev cochain (δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M))
    (hs : ∀ n, (δ (n+1)).comp (δ n) = 0) :
    CochainComplex (ModuleCat.{max u v w} ℤ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℤ (W k g n →ₗ[k] M))
    (fun n => ModuleCat.ofHom (δ n).toAddMonoidHom.toIntLinearMap) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      change δ (n+1) (δ n f) = 0
      exact LinearMap.congr_fun (hs n) f)

/-- A pointwise map between cochain complexes whose carriers may be in
different universes. The differential equation identifies the images of
boundaries, and the representative equation fixes the map on the quotient. -/
def InducesCohomologyMap.{s, t} {K : CochainComplex (ModuleCat.{s} ℤ) ℕ}
    {L : CochainComplex (ModuleCat.{t} ℤ) ℕ}
    (f : ∀ n, K.X n →ₗ[ℤ] L.X n)
    (H : ∀ n, Homology K n →ₗ[ℤ] Homology L n) : Prop :=
  (∀ i j, (L.d i j).hom.comp (f i) = (f j).comp (K.d i j).hom) ∧
    ∀ n (z : cycles K n), ∃ y : cycles L n,
      y.val = f n z.val ∧ H n (homologyClass K n z) = homologyClass L n y

end AdvancedHomologicalAlgebra.CE.Ext

namespace Specs.AdvancedHomologicalAlgebra.CE.Ext
open _root_.AdvancedHomologicalAlgebra.CE _root_.AdvancedHomologicalAlgebra.CE.Ext
open scoped TensorProduct
universe u v w w'

def freeResolutionExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    [Module.Free k g] (D : BoundaryData k g),
    AugmentedExact k g D.differential ∧ ∀ n, Module.Free (U k g) (V k g n)

/-- The all-degree evaluation comparison with P103's Ext quotient, on the
free resolution supplied by the first target. The canonical map on
cohomology is fixed by the isomorphism of cochain complexes. -/
def cohomologyExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    [Module.Free k g] (D : BoundaryData k g) (he : AugmentedExact k g D.differential)
    (M : Type w) [AddCommGroup M] [Module k M] [Module (U k g) M]
    [IsScalarTower k (U k g) M] (C : CochainData k g M D.differential),
    let K := cochain k g M C.differential C.squared
    ∃ e : homComplex (chain k g D.differential D.augmented) M ≅ K,
      (∀ n (F : V k g n →ₗ[U k g] M), (e.hom.f n).hom F = C.evaluation n F) ∧
      ∀ n, ∃ q : Homology K n ≃+
        @ExtWith _ _ _ _ (trivialModule k g) (resolution k g D.differential D.augmented he) M _ _ n,
        ∀ z : cycles K n,
          q (homologyClass K n z) = homologyClass _ n (cyclesMap e.inv n z)

/-- Naturality of the comparison on actual quotient cohomology. Arbitrary
choices satisfying evaluation are allowed; hence the comparison is canonical. -/
def naturalityExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d)
    (M : Type w) [AddCommGroup M] [Module k M] [Module (U k g) M]
    [IsScalarTower k (U k g) M]
    (N : Type w) [AddCommGroup N] [Module k N] [Module (U k g) N]
    [IsScalarTower k (U k g) N]
    (δM : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M))
    (sM : ∀ n, (δM (n+1)).comp (δM n) = 0)
    (δN : ∀ n, (W k g n →ₗ[k] N) →ₗ[k] (W k g (n+1) →ₗ[k] N))
    (sN : ∀ n, (δN (n+1)).comp (δN n) = 0)
    (eM : homComplex (chain k g d hc) M ≅ cochain k g M δM sM)
    (eN : homComplex (chain k g d hc) N ≅ cochain k g N δN sN),
    (∀ n (F : V k g n →ₗ[U k g] M) z, (eM.hom.f n).hom F z = F ((1 : U k g) ⊗ₜ[k] z)) →
    (∀ n (F : V k g n →ₗ[U k g] N) z, (eN.hom.f n).hom F z = F ((1 : U k g) ⊗ₜ[k] z)) →
    ∀ h : M →ₗ[U k g] N,
    ∃ f : cochain k g M δM sM ⟶ cochain k g N δN sN,
      (∀ n z, (f.f n).hom z = (h.restrictScalars k).comp z) ∧
      ∀ n, (homologyMap eN.inv n).comp (homologyMap f n) =
        (homologyMap (homPostMap (chain k g d hc) h) n).comp (homologyMap eM.inv n)

/-- The same naturality square for independently sized original coefficients,
with both arrows induced by postcomposition on the original quotients. -/
def heterogeneousNaturalityExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (D : BoundaryData k g)
    (M : Type w) [AddCommGroup M] [Module k M] [Module (U k g) M]
    [IsScalarTower k (U k g) M]
    (N : Type w') [AddCommGroup N] [Module k N] [Module (U k g) N]
    [IsScalarTower k (U k g) N]
    (CM : CochainData k g M D.differential) (CN : CochainData k g N D.differential),
    let P := chain k g D.differential D.augmented
    let K := cochain k g M CM.differential CM.squared
    let L := cochain k g N CN.differential CN.squared
    ∀ (eM : homComplex P M ≅ K) (eN : homComplex P N ≅ L),
    (∀ n (F : V k g n →ₗ[U k g] M), (eM.hom.f n).hom F = CM.evaluation n F) →
    (∀ n (F : V k g n →ₗ[U k g] N), (eN.hom.f n).hom F = CN.evaluation n F) →
    ∀ h : M →ₗ[U k g] N,
    ∃ (a : ∀ n, Homology K n →ₗ[ℤ] Homology L n)
      (b : ∀ n, Homology (homComplex P M) n →ₗ[ℤ] Homology (homComplex P N) n),
      InducesCohomologyMap (K := K) (L := L)
        (fun _ => (P103.HomTensorExactness.post (h.restrictScalars k)).toIntLinearMap) a ∧
      InducesCohomologyMap (K := homComplex P M) (L := homComplex P N)
        (fun _ => (P103.HomTensorExactness.post h).toIntLinearMap) b ∧
      ∀ n, (homologyMap eN.inv n).comp (a n) = (b n).comp (homologyMap eM.inv n)

end Specs.AdvancedHomologicalAlgebra.CE.Ext

namespace Specs.AdvancedHomologicalAlgebra.CE.Ext
open _root_.AdvancedHomologicalAlgebra.CE _root_.AdvancedHomologicalAlgebra.CE.Ext
open scoped TensorProduct
universe u v w

/-- The evaluation computation agrees with every ordinary projective
resolution of the trivial module, on every augmented comparison lift.
This connects the concrete CE quotient to P103's general Ext model and
includes independence of the resolution and of the lift. -/
def resolutionComparisonExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    [Module.Free k g] (d : BoundaryFamily k g), HasBoundaryFormula k g d →
    ∀ (hc : IsAugmentedComplex k g d) (he : AugmentedExact k g d)
      (M : Type w) [AddCommGroup M] [Module k M] [Module (U k g) M]
      [IsScalarTower k (U k g) M]
      (δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M))
      (s : ∀ n, (δ (n+1)).comp (δ n) = 0)
      (e : homComplex (chain k g d hc) M ≅ cochain k g M δ s),
    (∀ n (F : V k g n →ₗ[U k g] M) z, (e.hom.f n).hom F z = F ((1 : U k g) ⊗ₜ[k] z)) →
    letI := trivialModule k g
    ∀ (Q : LeftResolution (U k g) k), Q.IsProjective → ∀ n,
      ∃ q : Homology (cochain k g M δ s) n ≃+ ExtWith Q M n,
        ∀ (f : Q.complex ⟶ chain k g d hc),
          ChainLift Q (resolution k g d hc he) LinearMap.id f →
          ∀ z : cycles (cochain k g M δ s) n,
            q (homologyClass _ n z) = homologyMap (homPreMap f M) n
              (homologyClass _ n (cyclesMap e.inv n z))

end Specs.AdvancedHomologicalAlgebra.CE.Ext
