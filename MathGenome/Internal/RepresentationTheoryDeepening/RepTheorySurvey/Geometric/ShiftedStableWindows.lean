import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ShiftedStableWindows
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RankTwoSchubertStrata
import Batteries.Tactic.OpenPrivate

namespace RepTheorySurvey.Geometric.ShiftedStableWindows

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups (Points SchemeOver)
open LatticeModelSpecs BoundedLatticeSpecs ShiftedStableWindowsSpecs

noncomputable section

set_option autoImplicit false

open private windowRepresentative windowRepresentative_coeff mem_windowSubspace_iff
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SchubertAnalyticFlagTransport

private theorem translate_shiftedInclusion (a b : ℤ) (x : Fin 2 → O) :
    diagonalEquiv (fun _ : Fin 2 ↦ a) (shiftedInclusion 2 b x) =
      shiftedInclusion 2 (b + a) x := by
  funext i
  change monomial a * (monomial b * inclusion (x i)) = monomial (b + a) * inclusion (x i)
  rw [monomial_add, mul_left_comm, mul_assoc]

private theorem translate_scalar (a b : ℤ) :
    translate a (scalarLattice 2 b) = scalarLattice 2 (b + a) := by
  let f := ((diagonalEquiv (fun _ : Fin 2 ↦ a)).restrictScalars O).toLinearMap
  have h : f.comp (shiftedInclusion 2 b) = shiftedInclusion 2 (b + a) :=
    LinearMap.ext (translate_shiftedInclusion a b)
  apply Subtype.ext
  change ((scalarLattice 2 b).val.map f) = (scalarLattice 2 (b + a)).val
  rw [scalarLattice_val 2 b, scalarLattice_val 2 (b + a), ← LinearMap.range_comp, h]

private theorem translate_mono (a : ℤ) {L S : GL2Lattice} (h : L.val ≤ S.val) :
    (translate a L).val ≤ (translate a S).val :=
  Submodule.map_mono h

private def translateWindow (a : ℤ) {b : ℤ} {m : ℕ} (L : WindowLattice 2 b m) :
    WindowLattice 2 (b + a) m := by
  refine ⟨translate a L.val, ?_, ?_⟩
  · have h := translate_mono a L.property.1
    rwa [translate_scalar, add_right_comm b] at h
  · have h := translate_mono a L.property.2
    rwa [translate_scalar] at h

private theorem translate_mem_shifted (a b : ℤ) (x : Fin 2 → O) (L : GL2Lattice) :
    shiftedInclusion 2 (b + a) x ∈ (translate a L).val ↔ shiftedInclusion 2 b x ∈ L.val := by
  let e := diagonalEquiv (fun _ : Fin 2 ↦ a)
  change shiftedInclusion 2 (b + a) x ∈ L.val.map (e.restrictScalars O).toLinearMap ↔ _
  rw [← translate_shiftedInclusion a b x]
  constructor
  · rintro ⟨y, hy, he⟩
    exact (e.injective he) ▸ hy
  · intro hx
    exact ⟨_, hx, rfl⟩

private theorem shiftWindow_representative (a b : ℤ) (m : ℕ) (x : Fin 2 → O) :
    shiftWindow a b m (windowRepresentative b m x) = windowRepresentative (b + a) m x := by
  apply (windowCoordinates 2 (b + a) m).injective
  simp only [shiftWindow, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  funext ij
  obtain ⟨i, j⟩ := ij
  exact (windowRepresentative_coeff x i j).trans (windowRepresentative_coeff x i j).symm

private theorem shiftWindow_operator (a b : ℤ) (m : ℕ) (z : Window 2 b m) :
    shiftWindow a b m (windowOperator 2 b m z) =
      windowOperator 2 (b + a) m (shiftWindow a b m z) := by
  let e := windowJets 2 b m ≪≫ₗ (windowJets 2 (b + a) m).symm
  have he (v : Window 2 b m) : shiftWindow a b m v = e v := by
    apply (windowCoordinates 2 (b + a) m).injective
    simp only [shiftWindow, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    unfold windowCoordinates
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      LinearEquiv.apply_symm_apply]
  change shiftWindow a b m (t • z) = t • shiftWindow a b m z
  rw [he, he, map_smul]

private theorem shiftWindow_subspace (a b : ℤ) (m : ℕ) (L : GL2Lattice) :
    latticeSubspace (b + a) m (translate a L) =
      (latticeSubspace b m L).map (shiftWindow a b m).toLinearMap := by
  ext z
  rw [mem_windowSubspace_iff, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨windowRepresentative b m x, (mem_windowSubspace_iff L _).mpr ⟨x, ?_, rfl⟩,
      shiftWindow_representative a b m x⟩
    exact (translate_mem_shifted a b x L).mp hx
  · rintro ⟨y, hy, hyz⟩
    obtain ⟨x, hx, rfl⟩ := (mem_windowSubspace_iff L y).mp hy
    exact ⟨x, (translate_mem_shifted a b x L).mpr hx,
      (shiftWindow_representative a b m x).symm.trans hyz⟩

open private stableSchemePlane from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.BoundedLattices
open private reducedClosure_dense_points from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RankTwoSchubertStrata

private theorem isIso_of_closedImmersion_of_dense_points {X Y : SchemeOver ℂ}
    (i : X ⟶ Y) (hi : IsClosedImmersion i.left) (hred : IsReduced Y.left)
    (hdense : Dense (Set.range (pointLocation : Points Y complexAlgebra → Y.left)))
    (hsurj : Function.Surjective (fun q : Points X complexAlgebra ↦ q ≫ i)) : IsIso i := by
  have hsub : Set.range (pointLocation : Points Y complexAlgebra → Y.left) ⊆ Set.range i.left := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨p, rfl⟩ := hsurj q
    exact ⟨pointLocation p, (pointLocation_comp p i).symm⟩
  have hrange := closure_minimal hsub hi.isClosedEmbedding.isClosed_range
  rw [hdense.closure_eq] at hrange
  have : Surjective i.left := ⟨fun y ↦ hrange (Set.mem_univ y)⟩
  have : IsIso ((Over.forget _).map i) := isIso_of_isClosedImmersion_of_surjective i.left
  exact isIso_of_reflects_iso i (Over.forget _)

section StableScheme

variable {U W ι κ : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private theorem map_stable (E : U ≃ₗ[ℂ] W) {T : U →ₗ[ℂ] U} {S : W →ₗ[ℂ] W}
    (hE : ∀ x, E (T x) = S (E x)) {P : Submodule ℂ U} (hP : P.map T ≤ P) :
    (P.map E.toLinearMap).map S ≤ P.map E.toLinearMap := by
  rw [Submodule.map_le_iff_le_comap]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  exact Submodule.mem_map.mpr ⟨T x, hP (Submodule.mem_map_of_mem hx), hE x⟩

omit [Fintype κ] [DecidableEq κ] in
private theorem stableSchemePoint_of_subspace (b : Module.Basis ι ℂ U) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ U) (T : U →ₗ[ℂ] U)
    (P : Submodule ℂ U) (hP : P.map T ≤ P) (hPdim : Module.finrank ℂ P = d) :
    ∃ p : Points (stableScheme b hd T) complexAlgebra, stableSchemePlane b hd T p = P := by
  let q := subspacePoint b hd P hPdim
  have hq : grassmannianSubspace b hd q = P := subspacePoint_subspace b hd P hPdim
  have hstable : StablePlane b hd T q := by
    unfold StablePlane
    rwa [hq]
  let cmp := LatticeModels.stableSchemePoints b hd T
  refine ⟨cmp.symm ⟨q, hstable⟩, ?_⟩
  have hp := congrArg Subtype.val (cmp.apply_symm_apply ⟨q, hstable⟩)
  exact (congrArg (grassmannianSubspace b hd) hp).trans hq

private theorem stableScheme_map_surjective (E : U ≃ₗ[ℂ] W)
    (bu : Module.Basis ι ℂ U) (bw : Module.Basis κ ℂ W)
    {d d' : ℕ} (hu : d ≤ Module.finrank ℂ U) (hw : d' ≤ Module.finrank ℂ W)
    (hdim : d' = d) (T : U →ₗ[ℂ] U) (S : W →ₗ[ℂ] W) (hE : ∀ x, E (T x) = S (E x))
    (i : stableScheme bu hu T ⟶ stableScheme bw hw S)
    (hi : ∀ q : Points (stableScheme bu hu T) complexAlgebra,
      stableSchemePlane bw hw S (q ≫ i) = (stableSchemePlane bu hu T q).map E.toLinearMap) :
    Function.Surjective (fun q : Points (stableScheme bu hu T) complexAlgebra ↦ q ≫ i) := by
  intro q
  let Q := stableSchemePlane bw hw S q
  have hQ : Q.map S ≤ Q := (LatticeModels.stableSchemePoints bw hw S q).property
  have hQdim : Module.finrank ℂ Q = d' := grassmannianSubspace_finrank bw hw _
  have hEinv (y : W) : E.symm (S y) = T (E.symm y) := by
    apply E.injective
    rw [LinearEquiv.apply_symm_apply, hE, LinearEquiv.apply_symm_apply]
  let P := Q.map E.symm.toLinearMap
  have hP : P.map T ≤ P := map_stable E.symm hEinv hQ
  have hPdim : Module.finrank ℂ P = d := (E.symm.finrank_map_eq Q).trans (hQdim.trans hdim)
  obtain ⟨p, hp⟩ := stableSchemePoint_of_subspace bu hu T P hP hPdim
  have hback : P.map E.toLinearMap = Q := (Submodule.map_symm_eq_iff E).mp rfl
  have hpq : stableSchemePlane bw hw S (p ≫ i) = Q := by
    rw [hi, hp, hback]
  let cmp := LatticeModels.stableSchemePoints bw hw S
  refine ⟨p, cmp.injective (Subtype.ext ?_)⟩
  exact grassmannianSubspace_injective bw hw hpq

private theorem stableSchemeIso (E : U ≃ₗ[ℂ] W)
    (bu : Module.Basis ι ℂ U) (bw : Module.Basis κ ℂ W)
    {d : ℕ} (hu : d ≤ Module.finrank ℂ U)
    (T : U →ₗ[ℂ] U) (S : W →ₗ[ℂ] W) (hE : ∀ x, E (T x) = S (E x)) :
    ∃ (d' : ℕ) (hw : d' ≤ Module.finrank ℂ W), d' = d ∧
      ∃ e : stableScheme bu hu T ≅ stableScheme bw hw S,
        ∀ q : Points (stableScheme bu hu T) complexAlgebra,
          stableSchemePlane bw hw S (q ≫ e.hom) =
            (stableSchemePlane bu hu T q).map E.toLinearMap := by
  let : Module.Finite ℂ U := Module.Finite.of_basis bu
  let : Module.Finite ℂ W := Module.Finite.of_basis bw
  let Z := Fin 0 → ℂ
  let : Subsingleton Z := ⟨fun _ _ ↦ funext fun i ↦ Fin.elim0 i⟩
  let : Unique (Z × Z) := ⟨⟨0⟩, fun _ ↦ Subsingleton.elim _ _⟩
  let split : W ≃ₗ[ℂ] U × (Z × Z) := E.symm ≪≫ₗ LinearEquiv.prodUnique.symm
  have hmem (P : Submodule ℂ U) (w : W) :
      w ∈ P.map E.toLinearMap ↔ (split w).1 ∈ P ∧ (split w).2.2 = 0 := by
    rw [Submodule.mem_map_equiv]
    exact ⟨fun h ↦ ⟨h, Subsingleton.elim _ _⟩, And.left⟩
  have hzero : Module.finrank ℂ Z = 0 := Module.finrank_zero_of_subsingleton
  have hdim : d + Module.finrank ℂ Z = d := by rw [hzero, Nat.add_zero]
  obtain ⟨j, hj, hformula⟩ := GrassmannianIncidenceSchemes.grassmannianIncidence split bu bw hu
  let hw' := GrassmannianIncidenceSpecs.incidenceDimension_le split hu
  have hjmap (p : GrassmannianPoints bu hu) :
      grassmannianSubspace bw hw' (p ≫ j) = (grassmannianSubspace bu hu p).map E.toLinearMap :=
    Submodule.ext fun w ↦ (hformula p w).trans (hmem _ w).symm
  have hstable (p : GrassmannianPoints bu hu) (hp : StablePlane bu hu T p) :
      StablePlane bw hw' S (p ≫ j) := by
    unfold StablePlane
    rw [hjmap]
    exact map_stable E hE hp
  obtain ⟨i, hi, _, hipoint⟩ :=
    GrassmannianIncidenceSchemes.stableGrassmannianIncidence split bu bw hu j T S hj hformula hstable
  have hip (p : Points (stableScheme bu hu T) complexAlgebra) :
      stableSchemePlane bw hw' S (p ≫ i) = (stableSchemePlane bu hu T p).map E.toLinearMap :=
    Submodule.ext fun w ↦ (hipoint p w).trans (hmem _ w).symm
  let Y := (grassmannianCharts bw hw').scheme
  let stable : Set (Points Y complexAlgebra) := {p | StablePlane bw hw' S p}
  have hiIso := isIso_of_closedImmersion_of_dense_points i hi
    (LatticeModels.reducedClosure_reduced Y stable) (reducedClosure_dense_points stable)
    (stableScheme_map_surjective E bu bw hu hw' hdim T S hE i hip)
  exact ⟨_, hw', hdim, asIso i, hip⟩

end StableScheme

section WindowSchemes

attribute [local irreducible] windowBasis windowOperator shiftWindow latticeSubspace translate

set_option maxHeartbeats 600000 in
private theorem shiftWindow_scheme (a b : ℤ) (m : ℕ) (d : WindowDimension 2 b m) :
    ∃ d' : WindowDimension 2 (b + a) m, d'.val = d.val ∧
      ∃ e : windowStableScheme 2 b m d ≅ windowStableScheme 2 (b + a) m d',
        ∀ q : Points (windowStableScheme 2 b m d) complexAlgebra,
          windowSchemeSubspace (q ≫ e.hom) =
            (windowSchemeSubspace q).map (shiftWindow a b m).toLinearMap := by
  obtain ⟨n, hn, hdim, e, he⟩ := stableSchemeIso
    (U := Window 2 b m) (W := Window 2 (b + a) m)
    (ι := Fin 2 × Fin m) (κ := Fin 2 × Fin m) (d := d.val) (shiftWindow a b m)
    (windowBasis 2 b m) (windowBasis 2 (b + a) m) (windowDimension_le d)
    (windowOperator 2 b m) (windowOperator 2 (b + a) m) (shiftWindow_operator a b m)
  let d' : WindowDimension 2 (b + a) m := ⟨n, Nat.lt_succ_of_le hn⟩
  exact ⟨d', hdim, e, he⟩

private theorem shiftWindow_into_symmetric (a b : ℤ) (m : ℕ)
    {d : WindowDimension 2 b m} {d' : WindowDimension 2 (b + a) m}
    (hd' : d'.val = d.val)
    (e : windowStableScheme 2 b m d ≅ windowStableScheme 2 (b + a) m d')
    (he : ∀ q : Points (windowStableScheme 2 b m d) complexAlgebra,
      windowSchemeSubspace (q ≫ e.hom) =
        (windowSchemeSubspace q).map (shiftWindow a b m).toLinearMap)
    (M : ℕ) (hlo : -(M : ℤ) ≤ b + a) (hhi : b + a + (m : ℤ) ≤ (M : ℤ)) :
    ∃ (d'' : WindowDimension 2 (-(M : ℤ)) (2 * M))
      (k : windowStableScheme 2 b m d ⟶ windowStableScheme 2 (-(M : ℤ)) (2 * M) d''),
      (d''.val : ℤ) = (d.val : ℤ) + 2 * ((M : ℤ) - (b + a + (m : ℤ))) ∧
      IsClosedImmersion k.left ∧
      ∀ (q : Points (windowStableScheme 2 b m d) complexAlgebra) (L : WindowLattice 2 b m),
        windowSchemeSubspace q = latticeSubspace b m L.val →
          windowSchemeSubspace (q ≫ k) = latticeSubspace (-(M : ℤ)) (2 * M) (translate a L.val) := by
  obtain ⟨d'', hdim, j, hj, hpoint⟩ := BoundedLattices.windowInclusions
    2 (b + a) (-(M : ℤ)) m (2 * M) hlo (by rwa [boundedExponent]) d'
  have hdim' := congrArg (fun n : ℕ ↦ (n : ℤ)) hdim
  rw [boundedExponent, hd'] at hdim'
  push_cast at hdim'
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr hhi)] at hdim'
  refine ⟨d'', e.hom ≫ j, hdim', ?_, ?_⟩
  · have : IsIso e.hom.left := Functor.map_isIso (Over.forget _) e.hom
    change IsClosedImmersion (e.hom.left ≫ j.left)
    infer_instance
  · intro q L hq
    let L' := translateWindow a L
    have hq' : windowSchemeSubspace (q ≫ e.hom) = latticeSubspace (b + a) m L'.val :=
      (he q).trans ((congrArg (fun P ↦ P.map (shiftWindow a b m).toLinearMap) hq).trans
        (shiftWindow_subspace a b m L.val).symm)
    rw [← Category.assoc]
    exact hpoint L' (q ≫ e.hom) hq'

theorem windowTranslation : WindowTranslation := by
  intro a b m
  refine ⟨fun L ↦ ⟨(translateWindow a L).property, shiftWindow_subspace a b m L.val⟩,
    shiftWindow_operator a b m, fun d ↦ ?_⟩
  obtain ⟨d', hd', e, he⟩ := shiftWindow_scheme a b m d
  exact ⟨d', hd', e, he, shiftWindow_into_symmetric a b m hd' e he⟩

end WindowSchemes

end

end RepTheorySurvey.Geometric.ShiftedStableWindows
