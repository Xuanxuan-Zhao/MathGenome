import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Conditioning.Neumann

/-! Independent statement of paper.tex, W11. All operator norms are the norms on
continuous linear maps induced by the given vector norms. The equation equivalence
asserts existence and uniqueness with the explicit inverse-image solution. -/
namespace NumAnalysis206.Conditioning.Specs

def perturbedLinearSystems : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (A : X ≃L[𝕜] Y) (D : X →L[𝕜] Y),
    ‖A.symm.toContinuousLinearMap‖ * ‖D‖ < 1 →
    ∃ B : X ≃L[𝕜] Y,
      B.toContinuousLinearMap = A.toContinuousLinearMap + D ∧
      ∀ (b db : Y) (x : X), A x = b →
        let xt := B.symm (b + db)
        (∀ z : X, (A.toContinuousLinearMap + D) z = b + db ↔ z = xt) ∧
        ‖xt - x‖ ≤
          (‖A.symm.toContinuousLinearMap‖ /
            (1 - ‖A.symm.toContinuousLinearMap‖ * ‖D‖)) * (‖db‖ + ‖D‖ * ‖x‖) ∧
        (b ≠ 0 →
          let a := ‖D‖ / ‖A.toContinuousLinearMap‖
          let c := ‖db‖ / ‖b‖
          let κ := ‖A.toContinuousLinearMap‖ * ‖A.symm.toContinuousLinearMap‖
          ‖xt - x‖ / ‖x‖ ≤ κ * (a + c) / (1 - κ * a))

end NumAnalysis206.Conditioning.Specs
