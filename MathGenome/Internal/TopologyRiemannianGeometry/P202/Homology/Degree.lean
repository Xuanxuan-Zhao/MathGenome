import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.Degree
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.SpheresDisks
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.PrismHomotopy
import Mathlib.Algebra.Homology.Additive

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace P202.Degree
open P202Specs.SingularChains P202Specs.SpheresDisks P202Specs.Degree

def degree : degree_type := degree_value

/-- The upstream computation concerns the actual augmented singular homology. -/
def sphereCoordinate (n : ℕ) : sphereGroup n ≃ₗ[ℤ] ℤ :=
  Classical.choice ((P202.SpheresDisks.sphereHomology ℤ ℤ n n).1 rfl)

lemma scalar_exists (n : ℕ) (f : sphere n ⟶ sphere n) :
    ∃ d : ℤ, ∀ x : sphereGroup n, induced n f x = d • x := by
  let e := sphereCoordinate n
  refine ⟨e (induced n f (e.symm 1)), fun x => e.injective ?_⟩
  have hx : x = e x • e.symm 1 := by
    apply e.injective
    simp
  conv_lhs => rw [hx]
  simp [mul_comm]

lemma action (n : ℕ) (f : sphere n ⟶ sphere n) (x : sphereGroup n) :
    induced n f x = P202Specs.Degree.degree n f • x := by
  unfold P202Specs.Degree.degree
  rw [dite_eq_left (scalar_exists n f)]
  exact (scalar_exists n f).choose_spec x

lemma scalar_unique (n : ℕ) (f : sphere n ⟶ sphere n) (d : ℤ)
    (h : ∀ x : sphereGroup n, induced n f x = d • x) :
    d = P202Specs.Degree.degree n f := by
  let e := sphereCoordinate n
  have hh := congrArg e ((h (e.symm 1)).symm.trans (action n f (e.symm 1)))
  simpa using hh

theorem degreeAction : degreeAction_type := by
  intro n f
  exact ⟨action n f, fun d h => scalar_unique n f d h⟩

theorem generatorIndependent : generatorIndependent_type := by
  intro n f e
  rw [action]
  simp

theorem homotopyInvariant : homotopyInvariant_type := by
  intro n f g H
  apply (scalar_unique n g _ ?_)
  intro x
  change (reducedHomologyFunctor ℤ ℤ (n : ℤ)).map g x = _
  rw [← (P202.PrismHomotopy.homology ℤ ℤ H (n : ℤ)).2]
  exact action n f x

theorem identity : identity_type := by
  intro n
  symm
  apply scalar_unique
  intro x
  change (reducedHomologyFunctor ℤ ℤ (n : ℤ)).map (𝟙 (sphere n)) x = (1 : ℤ) • x
  rw [(reducedHomologyFunctor ℤ ℤ (n : ℤ)).map_id]
  simp only [ModuleCat.id_apply, one_smul]

theorem composition : composition_type := by
  intro n f g
  symm
  apply scalar_unique
  intro x
  simp only [induced, Functor.map_comp, ModuleCat.comp_apply]
  change induced n g (induced n f x) = _
  rw [action, action, smul_smul]

lemma constant_induced (n : ℕ) (p : sphere n) : induced n (constantMap n p) = 0 := by
  let X := P202Specs.SingularDegreeZero.point.{0}
  let a : sphere n ⟶ X := TopCat.ofHom (ContinuousMap.const _ PUnit.unit)
  let b : X ⟶ sphere n := TopCat.ofHom (ContinuousMap.const _ p)
  have h : constantMap n p = a ≫ b := rfl
  change (reducedHomologyFunctor ℤ ℤ (n : ℤ)).map _ = _
  rw [h, Functor.map_comp]
  have hz := (P202.SpheresDisks.contractible ℤ ℤ).1 (n : ℤ)
  rw [hz.eq_of_src ((reducedHomologyFunctor ℤ ℤ (n : ℤ)).map b) 0, comp_zero]

theorem constant : constant_type := by
  intro n p
  symm
  apply scalar_unique
  intro x
  rw [constant_induced]
  simp

lemma homologyMap_eq_of_component_eq {K L : ChainComplex (ModuleCat ℤ) ℤ}
    (f g : K ⟶ L) (i : ℤ) (h : f.f i = g.f i) :
    homologyMap f i = homologyMap g i := by
  rw [← cancel_epi (K.homologyπ i), homologyπ_naturality, homologyπ_naturality]
  have hc : cyclesMap f i = cyclesMap g i := by
    rw [← cancel_mono (L.iCycles i), cyclesMap_i, cyclesMap_i, h]
  rw [hc]

lemma zero_simplex_natural {X Y : TopCat} (f : X ⟶ Y) (s : Simplex X 0) :
    TopCat.toSSetObj₀Equiv ((TopCat.toSSet.map f).app _ s) =
      f (TopCat.toSSetObj₀Equiv s) := rfl

lemma reduced_degree_natural {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    (reducedNonnegativeIso ℤ ℤ X n).inv ≫ ((reducedFunctor ℤ ℤ).map f).f (n : ℤ) =
      (chainMap ℤ ℤ f).f n ≫ (reducedNonnegativeIso ℤ ℤ Y n).inv := by
  change (reducedNonnegativeIso ℤ ℤ X n).inv ≫
    (HomologicalComplex.extendMap (augmentedShiftedMap ℤ ℤ f) (degreeEmbedding (-1))).f (n : ℤ) = _
  rw [HomologicalComplex.extendMap_f _ _
    (show (degreeEmbedding (-1)).f (n+1) = (n : ℤ) by dsimp [degreeEmbedding]; omega)]
  simp [reducedNonnegativeIso, augmentedShiftedMap]

lemma chainMap_sum_zero_degree (f g h k : sphere 0 ⟶ sphere 0)
    (H : ∀ x : sphere 0, (f x = h x ∧ g x = k x) ∨ (f x = k x ∧ g x = h x)) :
    (chainMap ℤ ℤ f).f 0 + (chainMap ℤ ℤ g).f 0 =
      (chainMap ℤ ℤ h).f 0 + (chainMap ℤ ℤ k).f 0 := by
  apply ModuleCat.hom_ext
  change Finsupp.lmapDomain ℤ ℤ ((TopCat.toSSet.map f).app _) +
    Finsupp.lmapDomain ℤ ℤ ((TopCat.toSSet.map g).app _) =
    Finsupp.lmapDomain ℤ ℤ ((TopCat.toSSet.map h).app _) +
    Finsupp.lmapDomain ℤ ℤ ((TopCat.toSSet.map k).app _)
  apply Finsupp.lhom_ext
  intro s m
  simp only [LinearMap.add_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rcases H (TopCat.toSSetObj₀Equiv s) with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · have e1 : (TopCat.toSSet.map f).app _ s = (TopCat.toSSet.map h).app _ s :=
      TopCat.toSSetObj₀Equiv.injective h1
    have e2 : (TopCat.toSSet.map g).app _ s = (TopCat.toSSet.map k).app _ s :=
      TopCat.toSSetObj₀Equiv.injective h2
    rw [e1,e2]
  · have e1 : (TopCat.toSSet.map f).app _ s = (TopCat.toSSet.map k).app _ s :=
      TopCat.toSSetObj₀Equiv.injective h1
    have e2 : (TopCat.toSSet.map g).app _ s = (TopCat.toSSet.map h).app _ s :=
      TopCat.toSSetObj₀Equiv.injective h2
    rw [e1,e2,add_comm]

def pole (b : Fin 2) : sphere 0 := P202.SpheresDisks.zeroSphereMap ⟨b⟩
lemma interchange_pole_zero : interchange (pole 0) = pole 1 := by
  apply Subtype.ext
  ext i
  fin_cases i
  simp [interchange, pole, P202.SpheresDisks.zeroSphereMap, EuclideanSpace.single]
lemma interchange_pole_one : interchange (pole 1) = pole 0 := by
  apply Subtype.ext
  ext i
  fin_cases i
  simp [interchange, pole, P202.SpheresDisks.zeroSphereMap, EuclideanSpace.single]
lemma pole_exhaustive (x : sphere 0) : x = pole 0 ∨ x = pole 1 := by
  obtain ⟨⟨b⟩, rfl⟩ := P202.SpheresDisks.zeroSphereHomeomorph.surjective x
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl


/-- On zero-chains, interchange + identity is the sum of the two constants. -/
lemma interchange_chain_sum :
    (chainMap ℤ ℤ interchange).f 0 + (chainMap ℤ ℤ (𝟙 (sphere 0))).f 0 =
      (chainMap ℤ ℤ (constantMap 0 (pole 0))).f 0 +
      (chainMap ℤ ℤ (constantMap 0 (pole 1))).f 0 := by
  apply chainMap_sum_zero_degree
  intro x
  rcases pole_exhaustive x with rfl | rfl
  · exact Or.inr ⟨interchange_pole_zero, rfl⟩
  · exact Or.inl ⟨interchange_pole_one, rfl⟩

/-- Homology in degree zero depends only on the map on zero-cycles. -/
lemma interchange_induced : induced 0 interchange = -(𝟙 (sphereGroup 0)) := by
  let F := reducedFunctor ℤ ℤ
  have hd : (F.map interchange + F.map (𝟙 (sphere 0))).f 0 =
      (F.map (constantMap 0 (pole 0)) + F.map (constantMap 0 (pole 1))).f 0 := by
    dsimp only [F]
    simp only [HomologicalComplex.add_f_apply]
    rw [← cancel_epi (reducedNonnegativeIso ℤ ℤ (sphere 0) 0).inv]
    simp only [Preadditive.comp_add]
    erw [reduced_degree_natural interchange 0,
      reduced_degree_natural (𝟙 (sphere 0)) 0,
      reduced_degree_natural (constantMap 0 (pole 0)) 0,
      reduced_degree_natural (constantMap 0 (pole 1)) 0]
    rw [← Preadditive.add_comp, ← Preadditive.add_comp, interchange_chain_sum]
  have hm := homologyMap_eq_of_component_eq _ _ 0 hd
  simp only [homologyMap_add] at hm
  change induced 0 interchange + induced 0 (𝟙 (sphere 0)) =
    induced 0 (constantMap 0 (pole 0)) + induced 0 (constantMap 0 (pole 1)) at hm
  rw [constant_induced, constant_induced, add_zero] at hm
  have hid : induced 0 (𝟙 (sphere 0)) = 𝟙 (sphereGroup 0) :=
    (reducedHomologyFunctor ℤ ℤ 0).map_id _
  rw [hid] at hm
  exact add_eq_zero_iff_eq_neg.mp hm

theorem interchangeDegree : interchange_type := by
  change P202Specs.Degree.degree 0 interchange = -1
  symm
  apply scalar_unique
  intro x
  rw [interchange_induced]
  simp

theorem zeroSphere : zeroSphere_type :=
  ⟨identity 0, interchangeDegree, constant 0⟩

end P202.Degree
