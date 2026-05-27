import Mathlib.Data.ZMod.Basic
import SumcheckProtocol.Src.CMvPolynomial

abbrev fieldSize {𝔽} [Fintype 𝔽] : ℕ :=
  Fintype.card 𝔽

/-- The sumcheck soundness error bound: n * maxIndDegree(p) / |𝔽|. -/
noncomputable def soundnessError
  {𝔽 : Type _} {n : ℕ} [CommSemiring 𝔽] [Fintype 𝔽]
  (p : CPoly.CMvPolynomial n 𝔽) : ℚ :=
  (n : ℚ) * (maxIndDegree p : ℚ) / (fieldSize (𝔽 := 𝔽) : ℚ)
