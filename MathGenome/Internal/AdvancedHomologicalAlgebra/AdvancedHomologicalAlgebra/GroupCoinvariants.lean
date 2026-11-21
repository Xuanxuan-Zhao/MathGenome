import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupCoinvariants
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Limits

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped MonoidAlgebra
namespace AdvancedHomologicalAlgebra.GroupCoinvariants
open P103.BalancedTensor
universe u v w
variable {k : Type u} {G : Type v} [CommRing k] [Group G]

@[simp] theorem augmentation_single (g : G) (a : k) :
    augmentation k G (MonoidAlgebra.single g a) = a := by
  simp [augmentation, MonoidAlgebra.liftNCRingHom_single]

@[simp] theorem augmentation_algebraMap (a : k) :
    augmentation k G (algebraMap k k[G] a) = a := by
  change augmentation k G (MonoidAlgebra.single 1 a) = a
  simp

@[simp] theorem trivial_op_smul (r : k[G]) (a : TrivialRight k G) :
    trivialScalar k G (MulOpposite.op r • a) =
      augmentation k G r * trivialScalar k G a := rfl

omit [Group G] in
@[simp] theorem trivial_k_smul (r : k) (a : TrivialRight k G) :
    trivialScalar k G (r • a) = r * trivialScalar k G a := rfl

abbrev underlyingEquiv (M : ModuleCat.{w} k[G]) := RestrictScalars.addEquiv k k[G] M

@[simp] theorem coefficient_apply (M : ModuleCat.{w} k[G]) (g : G)
    (m : RestrictScalars k k[G] M) :
    underlyingEquiv M (coefficientRepresentation k G M g m) =
      MonoidAlgebra.single g (1 : k) • underlyingEquiv M m := by
  rfl

@[simp] theorem quotient_single_smul (M : ModuleCat.{w} k[G]) (g : G) (a : k) (m : M) :
    quotientMap k G M ((underlyingEquiv M).symm (MonoidAlgebra.single g a • m)) =
      a • quotientMap k G M ((underlyingEquiv M).symm m) := by
  have h : (underlyingEquiv M).symm (MonoidAlgebra.single g a • m) =
      a • coefficientRepresentation k G M g ((underlyingEquiv M).symm m) := by
    change MonoidAlgebra.single g a • m =
      algebraMap k k[G] a • (MonoidAlgebra.single g (1 : k) • m)
    rw [smul_smul]
    congr 1
    simp
  rw [h, map_smul, Representation.Coinvariants.mk_self_apply]

/-- The augmentation describes the action of every group-algebra element on
coinvariants. This is proved by finite-support induction, without commutativity of G. -/
theorem quotient_smul (M : ModuleCat.{w} k[G]) (r : k[G]) (m : M) :
    quotientMap k G M ((underlyingEquiv M).symm (r • m)) =
      augmentation k G r • quotientMap k G M ((underlyingEquiv M).symm m) := by
  induction r using MonoidAlgebra.induction_on with
  | of g => simp [MonoidAlgebra.of_apply, quotient_single_smul]
  | add r s hr hs => simp [add_smul, hr, hs]
  | smul a r hr =>
    rw [RestrictScalars.addEquiv_symm_map_smul_smul, map_smul, hr]
    simp only [Algebra.smul_def, map_mul, augmentation_algebraMap, mul_smul]

/-- The balanced inverse pairing `(a,m) ↦ a[m]`. -/
def coinvariantPairing (M : ModuleCat.{w} k[G]) :
    Pairing k[G] (A := TrivialRight k G) (B := M) (Coinvariants k G M) :=
  Pairing.ofFun
    (fun a m => trivialScalar k G a • quotientMap k G M ((underlyingEquiv M).symm m))
    (by intros; exact add_smul _ _ _)
    (by intros; simp [smul_add])
    (by
      intro r a m
      rw [quotient_smul]
      simp only [trivial_op_smul, smul_smul]
      rw [mul_comm])

def tensorToCoinvariants (M : ModuleCat.{w} k[G]) :
    TrivialTensor k G M →ₗ[k] Coinvariants k G M where
  __ := lift (coinvariantPairing M)
  map_smul' s z := lift_leftScale (coinvariantPairing M)
    (fun s a b => by
      change (s * trivialScalar k G a) • quotientMap k G M ((underlyingEquiv M).symm b) =
        s • (trivialScalar k G a • quotientMap k G M ((underlyingEquiv M).symm b))
      exact mul_smul _ _ _) s z

@[simp] theorem tensorToCoinvariants_tmul (M : ModuleCat.{w} k[G])
    (a : TrivialRight k G) (m : M) :
    tensorToCoinvariants M (tmul k[G] a m) =
      trivialScalar k G a • quotientMap k G M ((underlyingEquiv M).symm m) := rfl

/-- `m ↦ 1 ⊗ m`, with linearity proved from the actual balance relation. -/
def tensorUnit (M : ModuleCat.{w} k[G]) :
    RestrictScalars k k[G] M →ₗ[k] TrivialTensor k G M where
  toFun m := tmul k[G] (1 : TrivialRight k G) (underlyingEquiv M m)
  map_add' x y := tmul_add _ _ _
  map_smul' a m := by
    change tmul k[G] (1 : TrivialRight k G) (algebraMap k k[G] a • underlyingEquiv M m) =
      leftScale a (tmul k[G] (1 : TrivialRight k G) (underlyingEquiv M m))
    rw [leftScale_tmul, ← balance]
    congr 1
    change augmentation k G (algebraMap k k[G] a) * 1 = a * 1
    simp

def coinvariantsToTensor (M : ModuleCat.{w} k[G]) :
    Coinvariants k G M →ₗ[k] TrivialTensor k G M :=
  Representation.Coinvariants.lift _ (tensorUnit M) (fun g => by
    ext m
    change tmul k[G] (1 : TrivialRight k G) (MonoidAlgebra.single g (1 : k) • underlyingEquiv M m) =
      tmul k[G] (1 : TrivialRight k G) (underlyingEquiv M m)
    rw [← balance]
    congr 1
    change augmentation k G (MonoidAlgebra.single g (1 : k)) * 1 = 1
    simp)

@[simp] theorem coinvariantsToTensor_mk (M : ModuleCat.{w} k[G])
    (m : RestrictScalars k k[G] M) :
    coinvariantsToTensor M (quotientMap k G M m) =
      tmul k[G] (1 : TrivialRight k G) (underlyingEquiv M m) := rfl

/-- The source isomorphism, oriented `[m] ↦ 1 ⊗ m`. -/
def coinvariantTensorIso (M : ModuleCat.{w} k[G]) :
    Coinvariants k G M ≃ₗ[k] TrivialTensor k G M :=
  LinearEquiv.ofLinearMap (coinvariantsToTensor M) (tensorToCoinvariants M)
    (by
      apply LinearMap.ext
      intro z
      induction z using P103.BalancedTensor.induction_on with
      | h0 => simp
      | ht a m =>
        change coinvariantsToTensor M
          (trivialScalar k G a • quotientMap k G M ((underlyingEquiv M).symm m)) = _
        rw [map_smul, coinvariantsToTensor_mk]
        change leftScale (trivialScalar k G a) (tmul k[G] (1 : TrivialRight k G) m) = _
        rw [leftScale_tmul]
        congr 1
        change (trivialScalar k G a) * 1 = trivialScalar k G a
        exact mul_one _
      | ha x y hx hy => simp_all)
    (by
      apply Representation.Coinvariants.hom_ext
      ext m
      change trivialScalar k G (1 : TrivialRight k G) • quotientMap k G M m = _
      exact one_smul _ _)

@[simp] theorem coinvariantTensorIso_mk (M : ModuleCat.{w} k[G])
    (m : RestrictScalars k k[G] M) :
    coinvariantTensorIso M (quotientMap k G M m) =
      tmul k[G] (1 : TrivialRight k G) (underlyingEquiv M m) := rfl

@[simp] theorem coinvariantTensorIso_symm_tmul (M : ModuleCat.{w} k[G])
    (a : TrivialRight k G) (m : M) :
    (coinvariantTensorIso M).symm (tmul k[G] a m) =
      trivialScalar k G a • quotientMap k G M ((underlyingEquiv M).symm m) := rfl

/-- The comparison commutes with every homomorphism of coefficient modules. -/
theorem coinvariantTensorIso_natural {M N : ModuleCat.{w} k[G]} (f : M ⟶ N)
    (z : Coinvariants k G M) :
    coinvariantTensorIso N (coinvariantsMap k G f z) =
      P103.BalancedTensor.map LinearMap.id f.hom (coinvariantTensorIso M z) := by
  induction z using Representation.Coinvariants.induction_on with
  | h m => rfl

/-- Right exactness is a consequence of the coinvariant/trivial-representation
adjunction and the equivalence between representations and group-algebra modules. -/
instance coinvariants_preservesFiniteColimits :
    Limits.PreservesFiniteColimits ((coinvariantsFunctor k G : ModuleCat.{w} k[G] ⥤ ModuleCat k)) := by
  unfold coinvariantsFunctor
  infer_instance

instance coinvariants_additive :
    (coinvariantsFunctor k G : ModuleCat.{w} k[G] ⥤ ModuleCat k).Additive := by
  constructor
  intro M N f g
  apply ModuleCat.hom_ext
  apply Representation.Coinvariants.hom_ext
  ext m
  change quotientMap k G N ((underlyingEquiv N).symm (f.hom (underlyingEquiv M m) +
      g.hom (underlyingEquiv M m))) = _
  simp only [map_add]
  rfl

/-- Images and kernels remain equal after passing to coinvariants, and the
last map remains onto. Injectivity of the first map is not assumed. -/
theorem coinvariants_rightExact {L M N : ModuleCat.{w} k[G]}
    (f : L ⟶ M) (g : M ⟶ N) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    Function.Exact (coinvariantsMap k G f) (coinvariantsMap k G g) ∧
      Function.Surjective (coinvariantsMap k G g) := by
  let S : ShortComplex (ModuleCat.{w} k[G]) := ShortComplex.mk f g (by
    ext x
    exact hfg.apply_apply_eq_zero x)
  have hS : S.Exact :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 hfg
  have he : Epi S.g := (ModuleCat.epi_iff_surjective g).2 hg
  have hF : ∀ (T : ShortComplex (ModuleCat.{w} k[G])), T.Exact ∧ Epi T.g →
      (T.map (coinvariantsFunctor k G)).Exact ∧
        Epi ((coinvariantsFunctor k G).map T.g) :=
    ((Functor.preservesFiniteColimits_tfae (coinvariantsFunctor k G)).out 4 2).mp
      (inferInstance : Limits.PreservesFiniteColimits (coinvariantsFunctor k G))
  have h := hF S ⟨hS, he⟩
  exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h.1,
    (ModuleCat.epi_iff_surjective _).1 h.2⟩

/-- Public coinvariant object for an arbitrary left group-algebra module. -/
def coinvariants : Specification.coinvariantsType.{u,v,w} :=
  Specification.coinvariantsValue

/-- Public coefficient group homology, indexed by all natural numbers. -/
def groupHomology : Specification.groupHomologyType.{u,v,w} :=
  Specification.groupHomologyValue

theorem tensorComparison : Specification.tensorComparisonType.{u,v,w} := by
  intro k G _ _
  exact ⟨fun M => coinvariantTensorIso M,
    fun M m => coinvariantTensorIso_mk M m,
    fun M a m => coinvariantTensorIso_symm_tmul M a m,
    fun f z => coinvariantTensorIso_natural f z⟩

theorem rightExact : Specification.rightExactType.{u,v,w} := by
  intro k G _ _ L M N f g hfg hg
  exact coinvariants_rightExact f g hfg hg

end AdvancedHomologicalAlgebra.GroupCoinvariants
