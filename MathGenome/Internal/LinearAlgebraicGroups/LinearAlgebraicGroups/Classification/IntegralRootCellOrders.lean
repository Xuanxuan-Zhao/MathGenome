import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralRootCellOrders
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralLattices
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.MatrixOpenCell
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Polynomial.Eval.Degree

open scoped Matrix

universe u

namespace LinearAlgebraicGroups.Classification.IntegralRootCellOrders

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralLattices (Index Positive Negative orderedMatrix triangularEntries
  ClosedRootImage TorusCoordinatesGenerate)
open Specs.OrderedRootProducts (Enumerates)
open Specs.IntegralRootCellOrders
open Specs.MatrixOpenCell

noncomputable section

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
/-- Comparing polynomial coefficients over the universal torus separates the
weight shift of every nonzero coefficient. -/
theorem coefficients_supported_on_root_shifts {D : BasedRootDatum.{u}} {n : ℕ}
    {w : Index.{u} n → D.X}
    {p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ)}
    (h : ScalarAction w p) (a : D.I) (m : ℕ) (i j : Index.{u} n)
    (hij : w i ≠ w j + m • D.datum.root a) : (p a i j).coeff m = 0 := by
  classical
  let M := Multiplicative D.X
  let A := MonoidAlgebra ℤ M
  let t : M →* (Polynomial A)ˣ :=
    (Units.map Polynomial.C.toMonoidHom).comp (MonoidAlgebra.of ℤ M).toHomUnits
  let χ : M := Multiplicative.ofAdd (D.datum.root a)
  let wi : M := Multiplicative.ofAdd (w i)
  let wj : M := Multiplicative.ofAdd (w j)
  let s (b : M) : A := MonoidAlgebra.single b 1
  have ht (b : M) : (t b : Polynomial A) = Polynomial.C (s b) := rfl
  let f := p a i j
  let F := f.map (Int.castRingHom A)
  have heval (x : Polynomial A) :
      f.eval₂ (Int.castRingHom (Polynomial A)) x = F.comp x := by
    change f.eval₂ (Int.castRingHom (Polynomial A)) x =
      (f.map (Int.castRingHom A)).eval₂ Polynomial.C x
    rw [Polynomial.eval₂_map,
      show Polynomial.C.comp (Int.castRingHom A) = Int.castRingHom (Polynomial A)
        from Subsingleton.elim _ _]
  have he := congrArg (fun B : Matrix (Index.{u} n) (Index.{u} n) (Polynomial A) =>
    B i j) (h a (Polynomial A) t Polynomial.X)
  simp only [torusMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal] at he
  change (t wi : Polynomial A) * f.eval₂ _ Polynomial.X =
    f.eval₂ _ ((t χ : Polynomial A) * Polynomial.X) * (t wj : Polynomial A) at he
  simp only [ht, heval, Polynomial.comp_X] at he
  have hc := congrArg (fun q : Polynomial A => q.coeff m) he
  change (Polynomial.C (s wi) * F).coeff m =
    (F.comp (Polynomial.C (s χ) * Polynomial.X) * Polynomial.C (s wj)).coeff m at hc
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.comp_C_mul_X_coeff,
    Polynomial.coeff_map] at hc
  let z := f.coeff m
  change MonoidAlgebra.single wi (1 : ℤ) * MonoidAlgebra.single (1 : M) z =
    MonoidAlgebra.single (1 : M) z * MonoidAlgebra.single χ (1 : ℤ) ^ m *
      MonoidAlgebra.single wj 1 at hc
  simp only [MonoidAlgebra.single_pow, MonoidAlgebra.single_mul_single, one_mul, mul_one,
    one_pow] at hc
  have hne : χ ^ m * wj ≠ wi := by
    intro heq
    apply hij
    have hh := congrArg Multiplicative.toAdd heq
    change m • D.datum.root a + w j = w i at hh
    simpa only [add_comm] using hh.symm
  have hz := congrArg (fun g : A => g.coeff wi) hc
  change (Finsupp.single wi z) wi = (Finsupp.single (χ ^ m * wj) z) wi at hz
  simpa only [Finsupp.single_apply, ite_eq_left rfl, ite_eq_right hne, ite_true] using hz

theorem orderedRootCells : OrderedRootCells.{u} := by
  intro D n w height p hw hpositive hnegative hzero htorus hunit negative positive hn hp
  have hshift := coefficients_supported_on_root_shifts htorus
  have htneg := IntegralLattices.orderedMatrix_unitriangular negative
    (fun a => D.datum.root a.val) w height hw false hnegative (fun a => p a.val)
    (fun a => hzero a.val) (fun a => hshift a.val)
  have htpos := IntegralLattices.orderedMatrix_unitriangular positive
    (fun a => D.datum.root a.val) w height hw true hpositive (fun a => p a.val)
    (fun a => hzero a.val) (fun a => hshift a.val)
  refine ⟨⟨htneg, ?_⟩, ⟨htpos, ?_⟩⟩
  · exact IntegralLattices.orderedMatrix_inverse_coordinates false negative hn
      ((Function.Embedding.subtype _).trans D.datum.root) w (-height)
      (fun a => by
        change 0 < -(height (D.datum.root a.val))
        exact neg_pos.mpr (hnegative a))
      (fun a => p a.val)
      (fun a => hzero a.val) (fun a => hshift a.val) htneg (fun a => hunit a.val)
  · exact IntegralLattices.orderedMatrix_inverse_coordinates true positive hp
      ((Function.Embedding.subtype _).trans D.datum.root) w height hpositive (fun a => p a.val)
      (fun a => hzero a.val) (fun a => hshift a.val) htpos (fun a => hunit a.val)

private def characterUnit {D : BasedRootDatum.{u}} (μ : D.X) :
    (IntegralCellCoordinates D)ˣ where
  val := MvPolynomial.C (AddMonoidAlgebra.single μ 1)
  inv := MvPolynomial.C (AddMonoidAlgebra.single (-μ) 1)
  val_inv := by rw [← map_mul]; simp [← AddMonoidAlgebra.one_def]
  inv_val := by rw [← map_mul]; simp [← AddMonoidAlgebra.one_def]

private theorem substitutedCoordinate_mem {D : BasedRootDatum.{u}} {n : ℕ}
    {σ : Type u} (label : σ → D.I) (upper : Bool)
    (P : Matrix (Index.{u} n) (Index.{u} n) (MvPolynomial σ ℤ))
    (hP : IsOrderedRootChart upper P) (S : Subalgebra ℤ (IntegralCellCoordinates D))
    (hentries : ∀ i j, cellParameterMap label (P i j) ∈ S) (a : σ) :
    MvPolynomial.X (label a) ∈ S := by
  let t : MvPolynomial σ ℤ →ₐ[ℤ] IntegralCellCoordinates D :=
    { toRingHom := cellParameterMap label
      commutes' z := RingHom.congr_fun (Subsingleton.elim
        ((cellParameterMap label).comp (algebraMap ℤ (MvPolynomial σ ℤ)))
        (algebraMap ℤ (IntegralCellCoordinates D))) z }
  let e := MvPolynomial.aeval (R := ℤ) (fun ij : triangularEntries n upper => P ij.val.1 ij.val.2)
  have hle : (t.comp e).range ≤ S := by
    have he : t.comp e = MvPolynomial.aeval (R := ℤ) (fun ij => t (P ij.val.1 ij.val.2)) := by
      apply MvPolynomial.algHom_ext
      intro ij
      simp [e]
    rw [he, ← Algebra.adjoin_range_eq_range_aeval]
    apply Algebra.adjoin_le
    rintro _ ⟨ij, rfl⟩
    exact hentries _ _
  obtain ⟨q, hq⟩ := hP.2 a
  apply hle
  refine ⟨q, ?_⟩
  change t (e q) = MvPolynomial.X (label a)
  rw [show e q = MvPolynomial.X a from hq]
  exact MvPolynomial.eval₂Hom_X' _ _ a

private def markedFactors {D : BasedRootDatum.{u}} {n : ℕ}
    (negative : List (Negative D)) (positive : List (Positive D))
    (w : Index.{u} n → D.X)
    (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hn : IsOrderedRootChart false (orderedMatrix negative (fun a => p a.val)))
    (hp : IsOrderedRootChart true (orderedMatrix positive (fun a => p a.val))) :
    Factors (IntegralCellCoordinates D) n where
  lower := rootMatrixOverCell Subtype.val negative p
  diagonal i := characterUnit (w (ULift.up i))
  upper := rootMatrixOverCell Subtype.val positive p
  lower_zero i j hij := by
    change cellParameterMap Subtype.val
      (orderedMatrix negative (fun a => p a.val) (ULift.up i) (ULift.up j)) = 0
    rw [hn.1 _ _ (show ¬ (ULift.up j : Index.{u} n) < ULift.up i from not_lt_of_gt hij),
      Matrix.one_apply_ne (fun e => hij.ne (congrArg ULift.down e)), map_zero]
  lower_one i := by
    change cellParameterMap Subtype.val
      (orderedMatrix negative (fun a => p a.val) (ULift.up i) (ULift.up i)) = 1
    rw [hn.1 _ _ (lt_irrefl _), Matrix.one_apply_eq, map_one]
  upper_zero i j hij := by
    change cellParameterMap Subtype.val
      (orderedMatrix positive (fun a => p a.val) (ULift.up i) (ULift.up j)) = 0
    rw [hp.1 _ _ (show ¬ (ULift.up i : Index.{u} n) < ULift.up j from not_lt_of_gt hij),
      Matrix.one_apply_ne (fun e => hij.ne (congrArg ULift.down e.symm)), map_zero]
  upper_one i := by
    change cellParameterMap Subtype.val
      (orderedMatrix positive (fun a => p a.val) (ULift.up i) (ULift.up i)) = 1
    rw [hp.1 _ _ (lt_irrefl _), Matrix.one_apply_eq, map_one]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
private theorem surjective_of_factor_map {D : BasedRootDatum.{u}} {n : ℕ}
    {E : Type u} [CommRing E]
    (negative : List (Negative D)) (positive : List (Positive D))
    (w : Index.{u} n → D.X)
    (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hw : TorusCoordinatesGenerate w)
    (hn : IsOrderedRootChart false (orderedMatrix negative (fun a => p a.val)))
    (hp : IsOrderedRootChart true (orderedMatrix positive (fun a => p a.val)))
    (φ : E →+* IntegralCellCoordinates D) (f : Factors E n)
    (hφ : f.map φ = markedFactors negative positive w p hn hp) : Function.Surjective φ := by
  classical
  let C := IntegralCellCoordinates D
  let F := markedFactors negative positive w p hn hp
  let ψ : E →ₐ[ℤ] C :=
    { toRingHom := φ
      commutes' z := RingHom.congr_fun (Subsingleton.elim
        (φ.comp (algebraMap ℤ E)) (algebraMap ℤ C)) z }
  let S : Subalgebra ℤ C := ψ.range
  have hl (i j : Fin n) : F.lower i j ∈ S :=
    ⟨f.lower i j, congrArg (fun m : Factors C n => m.lower i j) hφ⟩
  have hu (i j : Fin n) : F.upper i j ∈ S :=
    ⟨f.upper i j, congrArg (fun m : Factors C n => m.upper i j) hφ⟩
  have hd (i : Fin n) : (F.diagonal i : C) ∈ S :=
    ⟨f.diagonal i, congrArg (fun m : Factors C n => (m.diagonal i : C)) hφ⟩
  have hdi (i : Fin n) : ((F.diagonal i)⁻¹ : Cˣ).val ∈ S := by
    refine ⟨((f.diagonal i)⁻¹).val, ?_⟩
    have h := congrArg (fun m : Factors C n => m.diagonal i) hφ
    change Units.map φ.toMonoidHom (f.diagonal i) = F.diagonal i at h
    rw [← h, ← map_inv]
    rfl
  let c : AddMonoidAlgebra ℤ D.X →ₐ[ℤ] C := IsScalarTower.toAlgHom ℤ _ _
  have hcoeff (v : AddMonoidAlgebra ℤ D.X) : MvPolynomial.C v ∈ S := by
    have htop : (⊤ : Subalgebra ℤ (AddMonoidAlgebra ℤ D.X)) ≤ S.comap c := by
      rw [← hw]
      apply Algebra.adjoin_le
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact hd i.down
      · exact hdi i.down
    exact htop (Algebra.mem_top (x := v))
  have hX (a : D.I) : (MvPolynomial.X a : C) ∈ S := by
    by_cases ha : D.base.IsPos a
    · exact substitutedCoordinate_mem Subtype.val true (orderedMatrix positive (fun a => p a.val))
        hp S (fun i j => hu i.down j.down) (⟨a, ha⟩ : Positive D)
    · exact substitutedCoordinate_mem Subtype.val false (orderedMatrix negative (fun a => p a.val))
        hn S (fun i j => hl i.down j.down) (⟨a, ha⟩ : Negative D)
  intro v
  suffices v ∈ S from this
  induction v using MvPolynomial.induction_on with
  | C a => exact hcoeff a
  | add a b ha hb => exact S.add_mem ha hb
  | mul_X v a hv => exact S.mul_mem hv (hX a)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
theorem integralCell_surjective : SurjectiveCellCoordinates.{u} := by
  intro D n negative positive w p hw hn hp
  let C := IntegralCellCoordinates D
  let Z := ULift.{u} ℤ
  let : Algebra Z C := ((Int.castRingHom C).comp ULift.ringEquiv.toRingHom).toAlgebra
  let F := markedFactors negative positive w p hn hp
  obtain ⟨_, _, f, _, _, hf⟩ := LinearAlgebraicGroups.MatrixOpenCell.regularOpenCell Z n
  obtain ⟨φ, hφ⟩ := (hf C).1.2 F
  refine ⟨φ.toRingHom, surjective_of_factor_map negative positive w p hw hn hp φ.toRingHom f hφ, ?_⟩
  change φ.toRingHom.mapMatrix (cellMatrix Z n) = F.product
  exact ((hf C).2.1 φ).symm.trans (congrArg (fun x : Factors C n => x.product) hφ)

set_option backward.isDefEq.respectTransparency false in
private theorem localization_of_compatible_maps
    {A C B K : Type u} [CommRing A] [CommRing C] [CommRing B] [CommRing K]
    (r : A) (generic : A →+* B) (φ : Localization.Away r →+* C)
    (restrict : B →+* K) (extend : C →+* K)
    (hφ : Function.Surjective φ) (hr : Function.Injective restrict)
    (he : Function.Injective extend)
    (hcompat : restrict.comp generic = extend.comp (φ.comp (algebraMap _ _))) :
    ∃ f : (A ⧸ RingHom.ker generic) →+* C,
      f.comp (Ideal.Quotient.mk (RingHom.ker generic)) = φ.comp (algebraMap _ _) ∧
      letI := f.toAlgebra
      IsLocalization.Away (Ideal.Quotient.mk (RingHom.ker generic) r) C := by
  let j : A →+* Localization.Away r := algebraMap _ _
  let g := φ.comp j
  let I := RingHom.ker generic
  have hker : I = RingHom.ker g := by
    rw [show I = RingHom.ker (restrict.comp generic) from
      (RingHom.ker_comp_of_injective generic hr).symm, hcompat,
      RingHom.ker_comp_of_injective _ he]
  let f := Ideal.Quotient.lift I g (fun x hx => RingHom.mem_ker.mp (hker ▸ hx))
  let q := Ideal.Quotient.mk I
  have hf (x : A) : f (q x) = φ (j x) := rfl
  refine ⟨f, RingHom.ext hf, ?_⟩
  let : Algebra (A ⧸ I) (C) := f.toAlgebra
  change IsLocalization (Submonoid.powers (q r)) (C)
  rw [isLocalization_iff]
  have hu : IsUnit (f (q r)) := (IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away r) r).map φ
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, rfl⟩
    change IsUnit (f ((q r) ^ m))
    rw [map_pow]
    exact hu.pow m
  · intro y
    obtain ⟨z, rfl⟩ := hφ y
    obtain ⟨m, x, hx⟩ := IsLocalization.Away.surj r z
    refine ⟨⟨q x, ⟨(q r) ^ m, ⟨m, rfl⟩⟩⟩, ?_⟩
    change φ z * f ((q r) ^ m) = f (q x)
    simpa only [map_pow, hf, map_mul] using congrArg φ hx
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    change g a = g b at hxy
    have hab : a - b ∈ I := by
      rw [hker, RingHom.mem_ker, map_sub, sub_eq_zero]
      exact hxy
    have hab' : q a = q b := Ideal.Quotient.eq.mpr hab
    exact ⟨1, by rw [hab']⟩

/-- Use the same schematic closure for every order compatible with its generic chart. -/
theorem localizedClosureCoordinates : LocalizedClosureCoordinates.{u} := by
  intro D n B K _ _ generic φ restrict extend hφ hr he hcompat
  exact localization_of_compatible_maps (minorProduct (ULift.{u} ℤ) n)
    generic φ restrict extend hφ hr he hcompat

private theorem evaluate_orderedMatrix {n : ℕ} {σ R : Type u} [CommRing R]
    (l : List σ) (p : σ → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (x : σ → R) :
    (MvPolynomial.eval₂Hom (Int.castRingHom R) x).mapMatrix (orderedMatrix l p) =
      (l.map (fun a => evaluateRootMatrix (p a) (x a))).prod := by
  let g := MvPolynomial.eval₂Hom (Int.castRingHom R) x
  change g.mapMatrix ((l.map fun a =>
    (Polynomial.aeval (MvPolynomial.X a)).toRingHom.mapMatrix (p a)).prod) = _
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  ext i j
  change g ((p a i j).eval₂ (algebraMap ℤ _) (MvPolynomial.X a)) = (p a i j).eval₂ _ (x a)
  rw [Polynomial.hom_eval₂,
    show g.comp (algebraMap ℤ _) = Int.castRingHom R from Subsingleton.elim _ _]
  rw [show g (MvPolynomial.X a) = x a from MvPolynomial.eval₂Hom_X' _ _ _]

private theorem evaluateRootMatrix_zero {n : ℕ} {R : Type u} [CommRing R]
    (p : Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hzero : ∀ i j, (p i j).coeff 0 = (1 : Matrix _ _ ℤ) i j) :
    evaluateRootMatrix p (0 : R) = 1 := by
  ext i j
  change (p i j).eval₂ (Int.castRingHom R) 0 = (1 : Matrix _ _ R) i j
  rw [Polynomial.eval₂_at_zero, hzero i j]
  exact congrFun (congrFun (map_one (Int.castRingHom R).mapMatrix) i) j

private theorem evaluate_single_root {n : ℕ} {σ R : Type u} [CommRing R] [DecidableEq σ]
    (l : List σ) (p : σ → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hzero : ∀ a i j, (p a i j).coeff 0 = (1 : Matrix _ _ ℤ) i j)
    (a : σ) (r : R) (hl : l.Nodup) (ha : a ∈ l) :
    (l.map (fun b => evaluateRootMatrix (p b) ((Pi.single a r : σ → R) b))).prod =
      evaluateRootMatrix (p a) r := by
  have hone (b : σ) (hb : b ≠ a) : evaluateRootMatrix (p b) ((Pi.single a r : σ → R) b) = 1 := by
    rw [Pi.single_eq_of_ne hb, evaluateRootMatrix_zero _ (hzero b)]
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rw [List.map_cons, List.prod_cons]
    obtain ⟨hnmem, hn⟩ := List.nodup_cons.mp hl
    rcases eq_or_ne b a with rfl | hb
    · rw [Pi.single_eq_same, List.prod_eq_one, mul_one]
      intro M hM
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hM
      exact hone c (fun h => hnmem (h ▸ hc))
    · rw [hone b hb, one_mul]
      exact ih hn ((List.mem_cons.mp ha).resolve_left hb.symm)

/-- The subgroup from a single order contains each root factor individually.
Consequently a product in another order is represented in the first order. -/
private theorem evaluate_in_reference_order {n : ℕ} {σ R : Type u} [CommRing R]
    (upper : Bool) (l l' : List σ)
    (p : σ → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hl : Enumerates l Set.univ)
    (hzero : ∀ a i j, (p a i j).coeff 0 = (1 : Matrix _ _ ℤ) i j)
    (hc : ClosedRootImage upper (orderedMatrix l p)) (x : σ → R) :
    ∃ y : σ → R, (MvPolynomial.eval₂Hom (Int.castRingHom R) y).mapMatrix (orderedMatrix l p) =
      (MvPolynomial.eval₂Hom (Int.castRingHom R) x).mapMatrix (orderedMatrix l' p) := by
  classical
  obtain ⟨f, hf, H, hH⟩ := hc.2.2 R
  let g (a : σ) := f (Pi.single a (x a))
  have hset (U : Matrix.GeneralLinearGroup (Index.{u} n) R) : U ∈ Set.range f ↔ U ∈ H :=
    Set.ext_iff.mp hH U
  have hprod : (l'.map g).prod ∈ H := by
    apply H.list_prod_mem
    intro U hU
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hU
    exact (hset _).mp ⟨Pi.single a (x a), rfl⟩
  obtain ⟨y, hy⟩ := (hset _).mpr hprod
  refine ⟨y, ?_⟩
  rw [← hf, hy, evaluate_orderedMatrix]
  change Units.coeHom (Matrix (Index.{u} n) (Index.{u} n) R) ((l'.map g).prod) = _
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  change (f (Pi.single a (x a))).val = _
  rw [hf, evaluate_orderedMatrix]
  exact evaluate_single_root l p hzero a (x a) hl.1 ((hl.2 a).mpr (Set.mem_univ a))

set_option backward.isDefEq.respectTransparency false in
private theorem substitute_marked_order {D : BasedRootDatum.{u}} {n : ℕ}
    (negative negative' : List (Negative D)) (positive positive' : List (Positive D))
    (w : Index.{u} n → D.X)
    (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hn : Enumerates negative Set.univ) (hp : Enumerates positive Set.univ)
    (hzero : ∀ a i j, (p a i j).coeff 0 = (1 : Matrix _ _ ℤ) i j)
    (hnegative : ClosedRootImage false (orderedMatrix negative (fun a => p a.val)))
    (hpositive : ClosedRootImage true (orderedMatrix positive (fun a => p a.val))) :
    ∃ e : IntegralCellCoordinates D →ₐ[AddMonoidAlgebra ℤ D.X] IntegralCellCoordinates D,
      e.toRingHom.mapMatrix (markedCellMatrix negative positive w p) =
        markedCellMatrix negative' positive' w p := by
  classical
  let C := IntegralCellCoordinates D
  obtain ⟨yn, hyn⟩ := evaluate_in_reference_order false negative negative' (fun a => p a.val)
    hn (fun a => hzero a.val) hnegative (fun a => (MvPolynomial.X a.val : C))
  obtain ⟨yp, hyp⟩ := evaluate_in_reference_order true positive positive' (fun a => p a.val)
    hp (fun a => hzero a.val) hpositive (fun a => (MvPolynomial.X a.val : C))
  let y (a : D.I) : C := if h : D.base.IsPos a then yp ⟨a, h⟩ else yn ⟨a, h⟩
  let e : C →ₐ[AddMonoidAlgebra ℤ D.X] C := MvPolynomial.aeval y
  have heN (a : Negative D) : e (MvPolynomial.X a.val) = yn a :=
    (MvPolynomial.aeval_X y a.val).trans (dite_eq_right a.property)
  have heP (a : Positive D) : e (MvPolynomial.X a.val) = yp a :=
    (MvPolynomial.aeval_X y a.val).trans (dite_eq_left a.property)
  refine ⟨e, ?_⟩
  have he {σ : Type u} (label : σ → D.I) (l : List σ) (y : σ → C)
      (hy : ∀ a, e (MvPolynomial.X (label a)) = y a) :
      e.toRingHom.mapMatrix (rootMatrixOverCell label l p) =
        ((MvPolynomial.eval₂Hom (Int.castRingHom C) y).mapMatrix
          (orderedMatrix l (p ∘ label))).submatrix ULift.up ULift.up := by
    have hcomp : e.toRingHom.comp (cellParameterMap label) =
        MvPolynomial.eval₂Hom (Int.castRingHom C) y := by
      apply MvPolynomial.ringHom_ext
      · exact RingHom.congr_fun (Subsingleton.elim
          ((e.toRingHom.comp (cellParameterMap label)).comp MvPolynomial.C)
          ((MvPolynomial.eval₂Hom (Int.castRingHom C) y).comp MvPolynomial.C))
      · intro a
        change e ((cellParameterMap label) (MvPolynomial.X a)) = _
        rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
        exact hy a
    apply Matrix.ext
    intro i j
    exact RingHom.congr_fun hcomp _
  have hN : e.toRingHom.mapMatrix (rootMatrixOverCell Subtype.val negative p) =
      rootMatrixOverCell Subtype.val negative' p :=
    (he Subtype.val negative yn heN).trans
      (congrArg (fun M : Matrix (Index.{u} n) (Index.{u} n) C => M.submatrix ULift.up ULift.up) hyn)
  have hP : e.toRingHom.mapMatrix (rootMatrixOverCell Subtype.val positive p) =
      rootMatrixOverCell Subtype.val positive' p :=
    (he Subtype.val positive yp heP).trans
      (congrArg (fun M : Matrix (Index.{u} n) (Index.{u} n) C => M.submatrix ULift.up ULift.up) hyp)
  unfold markedCellMatrix
  rw [map_mul, map_mul, hN, hP]
  congr 2
  rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  exact MvPolynomial.aeval_C _ _

private theorem matrixGroupCoordinates_hom_ext {n : ℕ} {R : Type u} [CommRing R]
    {f g : MatrixGroupCoordinates (ULift.{u} ℤ) n →+* R}
    (h : f.mapMatrix (glMatrix (ULift.{u} ℤ) n) = g.mapMatrix (glMatrix (ULift.{u} ℤ) n)) :
    f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (genericMatrix (ULift.{u} ℤ) n).det)
  apply MvPolynomial.ringHom_ext
  · intro r
    let Z := ULift.{u} ℤ
    let A := MvPolynomial (Index.{u} n × Index.{u} n) Z
    let a := (algebraMap A (MatrixGroupCoordinates Z n)).comp (MvPolynomial.C : Z →+* A)
    exact RingHom.congr_fun (Subsingleton.elim
      ((f.comp a).comp ULift.ringEquiv.symm.toRingHom)
      ((g.comp a).comp ULift.ringEquiv.symm.toRingHom)) r.down
  · rintro ⟨⟨i⟩, ⟨j⟩⟩
    exact congrFun (congrFun h i) j

private theorem cellCoordinates_hom_ext {n : ℕ} {R : Type u} [CommRing R]
    {f g : CellCoordinates (ULift.{u} ℤ) n →+* R}
    (h : f.mapMatrix (cellMatrix (ULift.{u} ℤ) n) = g.mapMatrix (cellMatrix (ULift.{u} ℤ) n)) :
    f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (minorProduct (ULift.{u} ℤ) n))
  exact matrixGroupCoordinates_hom_ext h

private theorem leftInverse_of_markedCell {n : ℕ} {R : Type u} [CommRing R]
    (φ : CellCoordinates (ULift.{u} ℤ) n →+* R) (hφ : Function.Surjective φ)
    (e e' : R →+* R) (A B : Matrix (Fin n) (Fin n) R)
    (hA : φ.mapMatrix (cellMatrix (ULift.{u} ℤ) n) = A)
    (he : e.mapMatrix A = B) (he' : e'.mapMatrix B = A) : Function.LeftInverse e' e := by
  have h : e'.comp (e.comp φ) = φ := by
    apply cellCoordinates_hom_ext
    change e'.mapMatrix (e.mapMatrix (φ.mapMatrix (cellMatrix (ULift.{u} ℤ) n))) = _
    rw [hA, he, he']
  intro a
  obtain ⟨b, rfl⟩ := hφ a
  exact RingHom.congr_fun h b

set_option backward.isDefEq.respectTransparency false in
/-- After comparing one order with the generic representation, transport the
chart through the integral changes of root coordinates for every other order. -/
theorem reorderedClosureCoordinates : ReorderedClosureCoordinates.{u} := by
  intro D A Q _ _ z e h ω V n b w height p hweight hw hpos hneg hgen hcoeff hunit
  have hzero := (IntegralLattices.integralRootPolynomials_support V b w hweight p hcoeff).1
  have hclosed (negative : List (Negative D)) (positive : List (Positive D))
      (hn : Enumerates negative Set.univ) (hp : Enumerates positive Set.univ) :=
    IntegralLattices.closedRootImages_of_unit_coefficients V b w hweight height hw hpos hneg
      p hcoeff negative positive hn hp (fun a => hunit a)
  intro B K _ _ generic restrict extend negative positive hn hp hr he hmatch
  obtain ⟨hnClosed, hpClosed⟩ := hclosed negative positive hn hp
  obtain ⟨φ, hφ, hφmatrix⟩ := integralCell_surjective negative positive w p hgen
    ⟨hnClosed.1, hnClosed.2.1⟩ ⟨hpClosed.1, hpClosed.2.1⟩
  refine ⟨φ, hφ, hφmatrix, ?_⟩
  intro negative' positive' hn' hp'
  obtain ⟨hnClosed', hpClosed'⟩ := hclosed negative' positive' hn' hp'
  obtain ⟨toOther, htoOther⟩ := substitute_marked_order negative negative' positive positive'
    w p hn hp hzero hnClosed hpClosed
  obtain ⟨toFirst, htoFirst⟩ := substitute_marked_order negative' negative positive' positive
    w p hn' hp' hzero hnClosed' hpClosed'
  obtain ⟨φ', hφ', hφmatrix'⟩ := integralCell_surjective negative' positive' w p hgen
    ⟨hnClosed'.1, hnClosed'.2.1⟩ ⟨hpClosed'.1, hpClosed'.2.1⟩
  have hleft := leftInverse_of_markedCell φ hφ toOther.toRingHom toFirst.toRingHom _ _
    hφmatrix htoOther htoFirst
  have hright := leftInverse_of_markedCell φ' hφ' toFirst.toRingHom toOther.toRingHom _ _
    hφmatrix' htoFirst htoOther
  let changeOrder := AlgEquiv.ofBijective toOther ⟨hleft.injective, hright.surjective⟩
  let ψ := changeOrder.toRingHom.comp φ
  have hψ : Function.Surjective ψ := changeOrder.surjective.comp hφ
  have hψmatrix : ψ.mapMatrix (cellMatrix (ULift.{u} ℤ) n) =
      markedCellMatrix negative' positive' w p :=
    (congrArg changeOrder.toRingHom.mapMatrix hφmatrix).trans htoOther
  refine ⟨changeOrder, hψ, hψmatrix, ?_⟩
  let extend' := extend.comp changeOrder.symm.toRingHom
  apply localizedClosureCoordinates generic ψ restrict extend' hψ hr (he.comp changeOrder.symm.injective)
  apply matrixGroupCoordinates_hom_ext
  apply Matrix.ext
  intro i j
  change restrict (generic (glMatrix (ULift.{u} ℤ) n i j)) =
    extend (changeOrder.symm (changeOrder (φ (cellMatrix (ULift.{u} ℤ) n i j))))
  rw [changeOrder.symm_apply_apply, hmatch i j]
  exact congrArg extend (congrFun (congrFun hφmatrix i) j).symm

end

end LinearAlgebraicGroups.Classification.IntegralRootCellOrders
