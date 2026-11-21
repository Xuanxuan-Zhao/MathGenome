import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.SimplicialChains

/-!
Independent statements of paper.tex, Theorem `thm:p202-simplicial-comparison`
(lines 1452–1527), with the coefficient conventions at lines 1430–1438.
All chain objects below are the upstream finite-support objects. Realizations
have the upstream weak topology. No finiteness or dimension assumption occurs.

`ComparisonData` records only the already specified affine chain maps, without
assuming they induce isomorphisms. The theorem types assert those isomorphisms.
Naturality includes absolute and relative groups and permits vertex collapse.
The last statement compares the canonical order with every other linear order,
using the sign of the sorting permutation on the actual chain generators.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory HomologicalComplex
open P202.Cellular
universe u v w
namespace P202Specs.SimplicialComparison
attribute [local instance] P202Specs.OrientedSimplicialAlgebra.vertexOrder

variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

/-- The original canonical affine maps, including the actual quotients for pairs. -/
structure SimplicialComparisonData {V : Type w} (K : AbstractSimplicialComplex V)
    (B : P202Specs.RelativeParametrizations.Simplicial.Subcomplex K) where
  absolute : P202Specs.OrientedSimplicialAlgebra.complex R A (K := K) ⟶ P202Specs.SingularChains.complex R A (TopCat.of K.Realization)
  absolute_formula : ∀ n, (absolute.f n).hom = P202Specs.RelativeParametrizations.Simplicial.affineLinear K R A n
  relative : P202Specs.RelativeParametrizations.Simplicial.relativeComplex R A K B ⟶
    P202Specs.RelativeParametrizations.singularRelativeComplex R A (TopCat.of K.Realization) (B.carrier K)
  relative_formula : ∀ n x,
    (relative.f n).hom (((P202Specs.RelativeParametrizations.Simplicial.selection R A K B).module n).mkQ x) =
      ((P202Specs.RelativeParametrizations.singularSelection R A (TopCat.of K.Realization) (B.carrier K)).module n).mkQ
        (P202Specs.RelativeParametrizations.Simplicial.affineLinear K R A n x)

structure DeltaComparisonData (D : DeltaComplex.{w}) (B : P202Specs.RelativeParametrizations.DeltaSubcomplex D) where
  absolute : P202Specs.RelativeParametrizations.deltaComplex R A D ⟶ P202Specs.SingularChains.complex R A (TopCat.of D.Realization)
  absolute_formula : ∀ n, (absolute.f n).hom = P202Specs.RelativeParametrizations.deltaParametrizationLinear R A D n
  relative : P202Specs.RelativeParametrizations.deltaRelativeComplex R A D B ⟶
    P202Specs.RelativeParametrizations.singularRelativeComplex R A (TopCat.of D.Realization) B.carrier
  relative_formula : ∀ n x,
    (relative.f n).hom (((P202Specs.RelativeParametrizations.deltaSelection R A D B).module n).mkQ x) =
      ((P202Specs.RelativeParametrizations.singularSelection R A (TopCat.of D.Realization) B.carrier).module n).mkQ
        (P202Specs.RelativeParametrizations.deltaParametrizationLinear R A D n x)

/-- Every nonnegative degree, for every subcomplex (including the empty one). -/
def simplicialComparison_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    {V : Type w} (K : AbstractSimplicialComplex V) (B : P202Specs.RelativeParametrizations.Simplicial.Subcomplex K),
    ∃ F : SimplicialComparisonData R A K B,
      (∀ q : ℕ, IsIso (homologyMap F.absolute q)) ∧
      (∀ q : ℕ, IsIso (homologyMap F.relative q))

/-- Specified ordered Δ-parametrizations; repeated face labels are retained. -/
def deltaComparison_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    (D : DeltaComplex.{w}) (B : P202Specs.RelativeParametrizations.DeltaSubcomplex D),
    ∃ F : DeltaComparisonData R A D B,
      (∀ q : ℕ, IsIso (homologyMap F.absolute q)) ∧
      (∀ q : ℕ, IsIso (homologyMap F.relative q))

/-- Naturality of both canonical comparison maps for arbitrary simplicial maps
of pairs. The realized map is required to be the barycentric vertex map.
Existence of all maps is a conclusion, not an extra hypothesis. -/
def simplicialNaturality_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    {V W : Type w} (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (B : P202Specs.RelativeParametrizations.Simplicial.Subcomplex K) (E : P202Specs.RelativeParametrizations.Simplicial.Subcomplex L) (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    (_hf : ∀ s ∈ B.complex.simplices, s.image f.vertices ∈ E.complex.simplices),
    ∃ g : TopCat.of K.Realization ⟶ TopCat.of L.Realization,
      (∀ x, (g x).val = x.val.map f.vertices) ∧
      ∃ (T : P202Specs.OrientedSimplicialAlgebra.complex R A (K := K) ⟶ P202Specs.OrientedSimplicialAlgebra.complex R A (K := L))
        (Trel : P202Specs.RelativeParametrizations.Simplicial.relativeComplex R A K B ⟶ P202Specs.RelativeParametrizations.Simplicial.relativeComplex R A L E)
        (grel : P202Specs.RelativeParametrizations.singularRelativeComplex R A (TopCat.of K.Realization) (B.carrier K) ⟶
          P202Specs.RelativeParametrizations.singularRelativeComplex R A (TopCat.of L.Realization) (E.carrier L)),
        (∀ n, (T.f n).hom = P202Specs.OrientedSimplicialAlgebra.pushforward R A f n) ∧
        (∀ n x, (Trel.f n).hom (((P202Specs.RelativeParametrizations.Simplicial.selection R A K B).module n).mkQ x) =
          ((P202Specs.RelativeParametrizations.Simplicial.selection R A L E).module n).mkQ (P202Specs.OrientedSimplicialAlgebra.pushforward R A f n x)) ∧
        (∀ n x, (grel.f n).hom
            (((P202Specs.RelativeParametrizations.singularSelection R A (TopCat.of K.Realization) (B.carrier K)).module n).mkQ x) =
          ((P202Specs.RelativeParametrizations.singularSelection R A (TopCat.of L.Realization) (E.carrier L)).module n).mkQ
            ((P202Specs.SingularChains.chainMap R A g).f n x)) ∧
        ∀ (F : SimplicialComparisonData R A K B) (G : SimplicialComparisonData R A L E)
          (q : ℕ),
          homologyMap T q ≫ homologyMap G.absolute q =
            homologyMap F.absolute q ≫ homologyMap (P202Specs.SingularChains.chainMap R A g) q ∧
          homologyMap Trel q ≫ homologyMap G.relative q =
            homologyMap F.relative q ≫ homologyMap grel q

/-- Naturality for Δ-complex maps preserving the ordered parametrizations,
including maps of all subcomplex pairs. -/
def deltaNaturality_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    {D E : DeltaComplex.{w}} (B : P202Specs.RelativeParametrizations.DeltaSubcomplex D) (H : P202Specs.RelativeParametrizations.DeltaSubcomplex E)
    (f : P202Specs.RelativeParametrizations.DeltaMap D E)
    (_hf : ∀ n s, s ∈ B.selected n → f.simplex n s ∈ H.selected n),
    ∃ g : TopCat.of D.Realization ⟶ TopCat.of E.Realization,
      (∀ n s t, g (D.simplexChart n s t) = E.simplexChart n (f.simplex n s) t) ∧
      ∃ (T : P202Specs.RelativeParametrizations.deltaComplex R A D ⟶ P202Specs.RelativeParametrizations.deltaComplex R A E)
        (Trel : P202Specs.RelativeParametrizations.deltaRelativeComplex R A D B ⟶ P202Specs.RelativeParametrizations.deltaRelativeComplex R A E H)
        (grel : P202Specs.RelativeParametrizations.singularRelativeComplex R A (TopCat.of D.Realization) B.carrier ⟶
          P202Specs.RelativeParametrizations.singularRelativeComplex R A (TopCat.of E.Realization) H.carrier),
        (∀ n, (T.f n).hom = P202Specs.RelativeParametrizations.deltaPushforward R A f n) ∧
        (∀ n x, (Trel.f n).hom (((P202Specs.RelativeParametrizations.deltaSelection R A D B).module n).mkQ x) =
          ((P202Specs.RelativeParametrizations.deltaSelection R A E H).module n).mkQ (P202Specs.RelativeParametrizations.deltaPushforward R A f n x)) ∧
        (∀ n x, (grel.f n).hom
            (((P202Specs.RelativeParametrizations.singularSelection R A (TopCat.of D.Realization) B.carrier).module n).mkQ x) =
          ((P202Specs.RelativeParametrizations.singularSelection R A (TopCat.of E.Realization) H.carrier).module n).mkQ
            ((P202Specs.SingularChains.chainMap R A g).f n x)) ∧
        ∀ (F : DeltaComparisonData R A D B) (G : DeltaComparisonData R A E H) (q : ℕ),
          homologyMap T q ≫ homologyMap G.absolute q =
            homologyMap F.absolute q ≫ homologyMap (P202Specs.SingularChains.chainMap R A g) q ∧
          homologyMap Trel q ≫ homologyMap G.relative q =
            homologyMap F.relative q ≫ homologyMap grel q

/-! An arbitrary second vertex order, on the same geometric complex. We reuse
ordered Δ-chains to avoid replacing the accepted canonical oriented model. -/

/-- Increasing tuples in any specified linear order, with all their ordered faces. -/
def orderedDelta {V : Type w} (K : AbstractSimplicialComplex V) (o : LinearOrder V) :
    DeltaComplex.{w} := by
  letI := o
  exact {
    Simplex := fun n => {s : Fin (n+1) ↪o V // Finset.univ.image s ∈ K.simplices}
    face := fun a s => ⟨a.trans s.1, K.face s.2
      (by intro x hx
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_image.mpr ⟨a i, Finset.mem_univ _, rfl⟩)
      (Finset.image_nonempty.mpr Finset.univ_nonempty)⟩
    face_id := by intros; rfl
    face_comp := by intros; rfl }

def orderedSubcomplex {V : Type w} (K : AbstractSimplicialComplex V)
    (B : P202Specs.RelativeParametrizations.Simplicial.Subcomplex K) (o : LinearOrder V) : P202Specs.RelativeParametrizations.DeltaSubcomplex (orderedDelta K o) where
  selected n := {s | Finset.univ.image s.1 ∈ B.complex.simplices}
  face_closed a s hs := B.complex.face hs
    (by intro x hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_image.mpr ⟨a i, Finset.mem_univ _, rfl⟩)
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- Affine chart of a tuple increasing in the second order, into the SAME
weak realization as the canonical chart. -/
def orderedParametrization {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) (s : (orderedDelta K o).Simplex n) :
    C(StandardSimplex n, K.Realization) := by
  classical
  let r : Fin (n+1) → (Finset.univ.image s.1 : Finset V) :=
    fun i => ⟨s.1 i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  exact ⟨K.simplexChart ⟨_, s.2⟩ ∘ Convexity.StdSimplex.map r,
    (continuous_iSup_rng (i := (⟨_, s.2⟩ : K.Simplex)) continuous_coinduced_rng).comp
      (Convexity.StdSimplex.continuous_map ℝ r)⟩

def orderedAffineLinear {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) : P202Specs.RelativeParametrizations.DeltaChains A (orderedDelta K o) n →ₗ[R]
    P202Specs.SingularChains.Chains A (TopCat.of K.Realization) n :=
  Finsupp.lmapDomain A R fun s =>
    (P202Specs.SingularChains.simplexEquiv _ n).symm (orderedParametrization K o n s)

/-- Sorting permutation with respect to the second order. -/
def sortingPermutation {V : Type w} (o : LinearOrder V) {n : ℕ} (s : Fin (n+1) → V) :
    Equiv.Perm (Fin (n+1)) := by
  letI := o
  exact Tuple.sort s

def reorderedSimplex {V : Type w} {K : AbstractSimplicialComplex V}
    (o : LinearOrder V) {n : ℕ} (s : P202Specs.OrientedSimplicialAlgebra.Simplex K n) :
    (orderedDelta K o).Simplex n := by
  letI := o
  exact ⟨OrderEmbedding.ofStrictMono (s.1 ∘ Tuple.sort s.1)
    ((Tuple.monotone_sort s.1).strictMono_of_injective
      (s.1.injective.comp (Tuple.sort s.1).injective)), by
    convert s.2 using 1
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => ⟨Tuple.sort s.1 i, hi⟩,
      fun ⟨i, hi⟩ => ⟨(Tuple.sort s.1).symm i, by simpa using hi⟩⟩⟩

/-- Transport of orientation inserts the sign before the reordered affine map. -/
def orderTransitionLinear {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) : P202Specs.OrientedSimplicialAlgebra.Chains K A n →ₗ[R]
    P202Specs.RelativeParametrizations.DeltaChains A (orderedDelta K o) n := by
  classical
  exact Finsupp.lsum R fun s => {
    toFun := fun a => (Equiv.Perm.sign (sortingPermutation o s.1) : ℤ) •
      Finsupp.single (reorderedSimplex o s) a
    map_add' := by intros; simp [Finsupp.single_add, smul_add]
    map_smul' := by intro r a; simp [smul_comm r] }

/-- All choices of vertex order give the same absolute and relative homology
comparison after the specified orientation transport. The second-order affine
maps, the signed transport chain maps, their isomorphisms, and the homology
identities are all conclusions. -/
def orderIndependence_type : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    {V : Type w} (K : AbstractSimplicialComplex V) (B : P202Specs.RelativeParametrizations.Simplicial.Subcomplex K) (o : LinearOrder V),
    ∃ (G : P202Specs.RelativeParametrizations.deltaComplex R A (orderedDelta K o) ⟶ P202Specs.SingularChains.complex R A (TopCat.of K.Realization))
      (Grel : P202Specs.RelativeParametrizations.deltaRelativeComplex R A (orderedDelta K o) (orderedSubcomplex K B o) ⟶
        P202Specs.RelativeParametrizations.singularRelativeComplex R A (TopCat.of K.Realization) (B.carrier K))
      (T : P202Specs.OrientedSimplicialAlgebra.complex R A (K := K) ⟶ P202Specs.RelativeParametrizations.deltaComplex R A (orderedDelta K o))
      (Trel : P202Specs.RelativeParametrizations.Simplicial.relativeComplex R A K B ⟶
        P202Specs.RelativeParametrizations.deltaRelativeComplex R A (orderedDelta K o) (orderedSubcomplex K B o)),
      (∀ n, (G.f n).hom = orderedAffineLinear R A K o n) ∧
      (∀ n x, (Grel.f n).hom
          (((P202Specs.RelativeParametrizations.deltaSelection R A (orderedDelta K o) (orderedSubcomplex K B o)).module n).mkQ x) =
        ((P202Specs.RelativeParametrizations.singularSelection R A (TopCat.of K.Realization) (B.carrier K)).module n).mkQ
          (orderedAffineLinear R A K o n x)) ∧
      (∀ n, (T.f n).hom = orderTransitionLinear R A K o n) ∧
      (∀ n x, (Trel.f n).hom (((P202Specs.RelativeParametrizations.Simplicial.selection R A K B).module n).mkQ x) =
        ((P202Specs.RelativeParametrizations.deltaSelection R A (orderedDelta K o) (orderedSubcomplex K B o)).module n).mkQ
          (orderTransitionLinear R A K o n x)) ∧
      (∀ q : ℕ, IsIso (homologyMap G q) ∧ IsIso (homologyMap Grel q) ∧
        IsIso (homologyMap T q) ∧ IsIso (homologyMap Trel q)) ∧
      ∀ (F : SimplicialComparisonData R A K B) (q : ℕ),
        homologyMap T q ≫ homologyMap G q = homologyMap F.absolute q ∧
        homologyMap Trel q ≫ homologyMap Grel q = homologyMap F.relative q

end P202Specs.SimplicialComparison
