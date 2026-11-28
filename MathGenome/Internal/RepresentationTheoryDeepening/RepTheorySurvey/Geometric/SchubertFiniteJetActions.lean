import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SchubertFiniteJetActions
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SchubertIntersectionConstructibility
import Batteries.Tactic.OpenPrivate
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section

open Topology
open scoped MatrixGroups

namespace RepTheorySurvey.Geometric.SchubertFiniteJetActions

open LatticeModelSpecs BoundedLatticeSpecs RankTwoSchubertStrataSpecs
open SchubertIntersectionConstructibilitySpecs RankTwoSchubertStrata
open SchubertFiniteJetActionsSpecs

open private pair_window_end from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RankTwoSchubertStrata
open private boundedSubspace_injective schubertStageHomeomorph schubertStageHomeomorph_apply
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SchubertIntersectionConstructibility

private abbrev Jet (k : ℕ) := GLJets 2 (k + 1) (Nat.succ_pos k)

private abbrev reduction (k : ℕ) : GL (Fin 2) O →* Jet k :=
  reduceGL 2 (k + 1) (Nat.succ_pos k)

private abbrev truncation {k l : ℕ} (h : k ≤ l) : Jet l →* Jet k :=
  Matrix.GeneralLinearGroup.map (truncateJet (Nat.succ_le_succ h))

private theorem reduction_surjective (k : ℕ) : Function.Surjective (reduction k) :=
  reduceGL_surjective 2 (k + 1) (Nat.succ_pos k)

private theorem truncation_reduction {k l : ℕ} (h : k ≤ l) (g : GL (Fin 2) O) :
    truncation h (reduction l g) = reduction k g := by
  apply Units.ext
  ext i j
  rfl

private theorem truncation_surjective {k l : ℕ} (h : k ≤ l) :
    Function.Surjective (truncation h) := by
  intro g
  obtain ⟨u, rfl⟩ := reduction_surjective k g
  exact ⟨reduction l u, truncation_reduction h u⟩

private theorem coeff_truncate {m n : ℕ} (h : m ≤ n) (z : JetRing n) (i : Fin m) :
    jetCoefficients m (truncateJet h z) i = jetCoefficients n z (Fin.castLE h i) := by
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective z
  change jetCoefficients m (jetReduction m u) i =
    jetCoefficients n (jetReduction n u) (Fin.castLE h i)
  rw [jetCoefficients_reduce, jetCoefficients_reduce]
  rfl

private def restrictCoefficients {m n : ℕ} (h : m ≤ n) :
    JetMatrixCoefficients 2 n →ₗ[ℂ] JetMatrixCoefficients 2 m where
  toFun A i j d := A i j (Fin.castLE h d)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem restrictCoefficients_surjective {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (restrictCoefficients h) := by
  intro A
  refine ⟨fun i j d ↦ if hd : d.val < m then A i j ⟨d.val, hd⟩ else 0, ?_⟩
  ext i j d
  change (if hd : d.val < m then A i j ⟨d.val, hd⟩ else 0) = A i j d
  rw [dite_eq_left d.isLt]

private theorem truncation_isOpenMap
    (hOpen : ∀ k : ℕ, IsOpenEmbedding (fun g : Jet k ↦ jetMatrixCoefficients g.val))
    {k l : ℕ} (h : k ≤ l) : IsOpenMap (truncation h) := by
  let π := restrictCoefficients (Nat.succ_le_succ h)
  have hπ : IsOpenMap π :=
    LinearMap.isOpenMap_of_finiteDimensional π (restrictCoefficients_surjective _)
  apply (hOpen k).isOpenMap_iff.mpr
  have he : (fun g : Jet k ↦ jetMatrixCoefficients g.val) ∘ truncation h =
      π ∘ (fun g : Jet l ↦ jetMatrixCoefficients g.val) := by
    funext g i j d
    exact coeff_truncate _ (g.val i j) d
  rw [he]
  exact hπ.comp (hOpen l).isOpenMap

private theorem loop_preserves_orbit (ab : DominantPair) (g : GL (Fin 2) O)
    {L : GL2Lattice} (hL : L ∈ gl2Orbit ab) :
    positiveGLMap 2 g • L ∈ gl2Orbit ab :=
  smul_mem_gl2Orbit ab ⟨positiveGLMap 2 g, ⟨g, rfl⟩⟩ hL

private theorem loop_preserves_closure (ab : DominantPair) (g : GL (Fin 2) O)
    {L : GL2Lattice} (hL : L ∈ closureLattices ab) :
    positiveGLMap 2 g • L ∈ closureLattices ab :=
  smul_mem_closureLattices ab ⟨positiveGLMap 2 g, ⟨g, rfl⟩⟩ hL

private theorem in_minimal_window {ab : DominantPair} {L : GL2Lattice}
    (hL : L ∈ closureLattices ab) :
    (scalarLattice 2 (ab.val.2 + (difference ab : ℤ))).val ≤ L.val ∧
      L.val ≤ (scalarLattice 2 ab.val.2).val := by
  obtain ⟨cd, hcd, horbit⟩ := hL
  obtain ⟨_, ha, hb⟩ := (below_iff cd ab).mp hcd
  obtain ⟨hLower, hUpper⟩ := orbit_endpoints horbit
  rw [pair_window_end]
  exact ⟨(hLower _).mpr ha, (hUpper _).mpr hb⟩

private theorem loop_smul_eq_of_reduction {ab : DominantPair} {k : ℕ}
    (hk : difference ab - 1 ≤ k) {g g' : GL (Fin 2) O}
    (hg : reduction k g = reduction k g') {L : GL2Lattice} (hL : L ∈ closureLattices ab) :
    positiveGLMap 2 g • L = positiveGLMap 2 g' • L := by
  obtain ⟨A, _, hAction, _, _⟩ := (schubertJetActions ab ab.val.2 (difference ab) (k + 1)
    (Nat.succ_pos k) (by omega) le_rfl (by rw [pair_window_end])).2
  have he := (hAction g L hL).symm.trans
    ((congrArg (fun u ↦ (A.smul u ⟨_, ⟨L, hL, rfl⟩⟩).val) hg).trans (hAction g' L hL))
  let wid := fun (u : GL (Fin 2) O) ↦
    (⟨positiveGLMap 2 u • L, in_minimal_window (loop_preserves_closure ab u hL)⟩ :
      WindowLattice 2 ab.val.2 (difference ab))
  have hi : wid g = wid g' :=
    (BoundedLattices.windowStageComparison 2 ab.val.2 (difference ab)).1.injective he
  exact congrArg Subtype.val hi

private def translateLattice {ab : DominantPair} {N : ℕ} (g : GL (Fin 2) O)
    (L : schubertLatticeSet ab N) : schubertLatticeSet ab N := by
  refine ⟨⟨positiveGLMap 2 g • L.val.val, ?_⟩, loop_preserves_closure ab g L.property⟩
  let B : WindowLattice 2 (-(N : ℤ)) (2 * N) := ⟨L.val.val, by
    simpa only [boundedExponent] using L.val.property⟩
  simpa only [boundedExponent] using
    BoundedLattices.windowPositiveStable 2 (-(N : ℤ)) (2 * N) g B

@[instance_reducible] private def loopAction {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N) :
    MulAction (GL (Fin 2) O) (SchubertSpace ab N hN) where
  smul g p := E.symm (translateLattice g (E p))
  one_smul p := by
    change E.symm (translateLattice 1 (E p)) = p
    apply E.injective
    rw [E.apply_symm_apply]
    apply Subtype.ext
    apply Subtype.ext
    change positiveGLMap 2 1 • (E p).val.val = (E p).val.val
    rw [map_one, one_smul]
  mul_smul g u p := by
    change E.symm (translateLattice (g * u) (E p)) =
      E.symm (translateLattice g (E (E.symm (translateLattice u (E p)))))
    rw [E.apply_symm_apply]
    apply congrArg E.symm
    apply Subtype.ext
    apply Subtype.ext
    change positiveGLMap 2 (g * u) • (E p).val.val =
      positiveGLMap 2 g • (positiveGLMap 2 u • (E p).val.val)
    rw [map_mul, mul_smul]

private theorem loopAction_lattice {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N) (g : GL (Fin 2) O)
    (p : SchubertSpace ab N hN) :
    (E ((loopAction E).smul g p)).val.val = positiveGLMap 2 g • (E p).val.val := by
  change (E (E.symm (translateLattice g (E p)))).val.val = _
  rw [E.apply_symm_apply]
  rfl

private theorem loopAction_preservesOrbit {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    (hE : ∀ p, schubertPointSubspace p = boundedSubspace (E p).val)
    (g : GL (Fin 2) O) (p : SchubertSpace ab N hN) (i : OrbitIndex ab) :
    (loopAction E).smul g p ∈ orbitPoints ab N hN i ↔ p ∈ orbitPoints ab N hN i := by
  have hMem (q : SchubertSpace ab N hN) :
      q ∈ orbitPoints ab N hN i ↔ (E q).val.val ∈ gl2Orbit (orbitLabel ab i) := by
    constructor
    · rintro ⟨L, hL, hsub⟩
      have he := boundedSubspace_injective N (hsub.symm.trans (hE q))
      exact he ▸ hL
    · intro hq
      exact ⟨(E q).val, hq, hE q⟩
  rw [hMem, hMem, loopAction_lattice]
  constructor
  · intro hp
    simpa only [inv_smul_smul, map_inv] using loop_preserves_orbit (orbitLabel ab i) g⁻¹ hp
  · exact loop_preserves_orbit (orbitLabel ab i) g

private theorem loopAction_subspace {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    (hE : ∀ p, schubertPointSubspace p = boundedSubspace (E p).val)
    (g : GL (Fin 2) O) (p : SchubertSpace ab N hN) (L : BoundedLattice 2 N)
    (hL : schubertPointSubspace p = boundedSubspace L) :
    schubertPointSubspace ((loopAction E).smul g p) =
      latticeSubspace (-(N : ℤ)) (2 * N) (positiveGLMap 2 g • L.val) := by
  have he := boundedSubspace_injective N ((hE p).symm.trans hL)
  rw [hE, boundedSubspace, loopAction_lattice, he]

private theorem descendAction {G H X : Type} [Monoid G] [Monoid H]
    (f : G →* H) (hf : Function.Surjective f) (A : MulAction G X)
    (h : ∀ g u, f g = f u → ∀ x, A.smul g x = A.smul u x) :
    ∃ B : MulAction H X, ∀ g x, B.smul (f g) x = A.smul g x := by
  let s := hf.hasRightInverse.choose
  have hs : Function.RightInverse s f := hf.hasRightInverse.choose_spec
  have hsmul (g : G) (x : X) : A.smul (s (f g)) x = A.smul g x :=
    h (s (f g)) g (hs (f g)) x
  refine ⟨{ smul := fun g x ↦ A.smul (s g) x
            one_smul := fun x ↦ (h (s 1) 1 ((hs 1).trans (map_one f).symm) x).trans (A.one_smul x)
            mul_smul := fun g u x ↦ ?_ }, hsmul⟩
  have he : f (s (g * u)) = f (s g * s u) := by rw [hs, map_mul, hs, hs]
  exact (h _ _ he x).trans (A.mul_smul _ _ _)

private theorem jetAction_exists {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N) (k : ℕ)
    (hk : difference ab - 1 ≤ k) :
    ∃ A : MulAction (Jet k) (SchubertSpace ab N hN),
      ∀ g p, A.smul (reduction k g) p = (loopAction E).smul g p := by
  apply descendAction (reduction k) (reduction_surjective k) (loopAction E)
  intro g u he p
  apply E.injective
  apply Subtype.ext
  apply Subtype.ext
  rw [loopAction_lattice, loopAction_lattice]
  exact loop_smul_eq_of_reduction hk he (E p).property

private theorem fullWindowAction {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    (hE : ∀ p, schubertPointSubspace p = boundedSubspace (E p).val)
    {k : ℕ} (hw : 2 * N ≤ k + 1) (A : MulAction (Jet k) (SchubertSpace ab N hN))
    (hA : ∀ g p, A.smul (reduction k g) p = (loopAction E).smul g p) :
    Continuous (fun x : Jet k × SchubertSpace ab N hN ↦ A.smul x.1 x.2) ∧
      ∀ g p, schubertPointSubspace (A.smul g p) =
        (schubertPointSubspace p).map (windowJetLinear (-(N : ℤ)) hw g.val) := by
  have hb : -(N : ℤ) ≤ ab.val.2 := by simpa [pairCoweight] using (hN 1).1
  have ha : ab.val.1 ≤ (-(N : ℤ)) + ((2 * N : ℕ) : ℤ) := by
    rw [boundedExponent]
    simpa [pairCoweight] using (hN 0).2
  obtain ⟨B, hMap, hReduce, hCont, _⟩ := (schubertJetActions ab (-(N : ℤ)) (2 * N) (k + 1)
    (Nat.succ_pos k) hw hb ha).2
  let H := E.trans (schubertStageHomeomorph ab N hN boundedSchubertComparison)
  have hH (p : SchubertSpace ab N hN) :
      (H p).val = windowStagePoint (-(N : ℤ)) (2 * N) (E p).val.val :=
    schubertStageHomeomorph_apply ab N hN boundedSchubertComparison (E p)
  have hSub (p : SchubertSpace ab N hN) :
      windowStageSubspace (H p).val = schubertPointSubspace p := by
    rw [hE p, hH p]
    exact (BoundedLattices.boundedStageComparison 2 N).2 (E p).val
  have hCompat (g : Jet k) (p : SchubertSpace ab N hN) : H (A.smul g p) = B.smul g (H p) := by
    obtain ⟨u, rfl⟩ := reduction_surjective k g
    apply Subtype.ext
    have hp : H p =
        ⟨windowStagePoint (-(N : ℤ)) (2 * N) (E p).val.val, ⟨_, (E p).property, rfl⟩⟩ :=
      Subtype.ext (hH p)
    rw [hH, hA, loopAction_lattice, hp, hReduce u (E p).val.val (E p).property]
  constructor
  · have he : (fun x : Jet k × SchubertSpace ab N hN ↦ A.smul x.1 x.2) =
        fun x ↦ H.symm (B.smul x.1 (H x.2)) := by
      funext x
      rw [← hCompat, H.symm_apply_apply]
    rw [he]
    exact H.symm.continuous.comp (hCont.comp (continuous_fst.prodMk
      (H.continuous.comp continuous_snd)))
  · intro g p
    rw [← hSub (A.smul g p), ← hSub p, hCompat]
    exact hMap g (H p)

private theorem continuous_of_truncation {k l : ℕ} {X : Type} [TopologicalSpace X]
    {h : k ≤ l} (hOpen : IsOpenMap (truncation h)) (hCont : Continuous (truncation h))
    {a : Jet k × X → X} {b : Jet l × X → X} (hb : Continuous b)
    (hAct : ∀ (g : Jet l) (p : X), a (truncation h g, p) = b (g, p)) : Continuous a := by
  let f := Prod.map (truncation h) (id : X → X)
  have hf : IsQuotientMap f := (hOpen.prodMap IsOpenMap.id).isQuotientMap
    (hCont.prodMap continuous_id) ((truncation_surjective h).prodMap Function.surjective_id)
  have he : a ∘ f = b := funext fun x ↦ hAct x.1 x.2
  exact hf.continuous_iff.mpr (he.symm ▸ hb)

theorem schubertFiniteJetActions : SchubertFiniteJetActions := by
  intro hOpen hContinuous ab N hN
  obtain ⟨E, hE, _⟩ := schubertStratification ab N hN
  choose ρ hρ using jetAction_exists E
  have hTransition ⦃k l : ℕ⦄ (h : k ≤ l) (hk : difference ab - 1 ≤ k)
      (g : Jet l) (p : SchubertSpace ab N hN) :
      (ρ k hk).smul (truncation h g) p = (ρ l (hk.trans h)).smul g p := by
    obtain ⟨u, rfl⟩ := reduction_surjective l g
    rw [truncation_reduction, hρ, hρ]
  refine ⟨ρ, ?_, hTransition, ?_, ?_, ?_⟩
  · intro k hk
    let l := max k (2 * N)
    have h : k ≤ l := le_max_left _ _
    have hw : 2 * N ≤ l + 1 := Nat.le_succ_of_le (le_max_right _ _)
    exact continuous_of_truncation (truncation_isOpenMap hOpen h) (hContinuous h)
      (fullWindowAction E hE hw (ρ l (hk.trans h)) (hρ l (hk.trans h))).1 (hTransition h hk)
  · intro k hk g p i
    obtain ⟨u, rfl⟩ := reduction_surjective k g
    rw [hρ]
    exact loopAction_preservesOrbit E hE u p i
  · intro k hk g p L hL
    rw [hρ]
    exact loopAction_subspace E hE g p L hL
  · intro k hk hw
    exact (fullWindowAction E hE hw (ρ k hk) (hρ k hk)).2

end RepTheorySurvey.Geometric.SchubertFiniteJetActions
