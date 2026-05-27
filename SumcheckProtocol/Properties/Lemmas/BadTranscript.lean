import CompPoly.Multivariate.CMvPolynomial

import SumcheckProtocol.Properties.Events.BadTranscript

lemma badTranscript_implies_lastBadRound
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n)))
  (r : Fin n → 𝔽) :
  BadTranscriptEvent st.domain st.polynomial (proverTranscript st P r) →
  LastBadRound st P r := by
  classical
  intro hBad
  let t : Transcript 𝔽 n := proverTranscript st P r

  -- the set of "bad" rounds (where the prover deviates from the honest round poly)
  let bad : Finset (Fin n) :=
    Finset.univ.filter (fun i => t.roundPolys i ≠ honestRoundPoly st.domain st.polynomial r i)

  have bad_nonempty : bad.Nonempty := by
    rcases hBad with ⟨i0, hi0⟩
    refine ⟨i0, ?_⟩
    simpa [bad, BadRound, t] using hi0

  -- choose the last bad round
  let i : Fin n := Finset.max' bad bad_nonempty

  have hi_neq :
      t.roundPolys i ≠ honestRoundPoly st.domain st.polynomial r i := by
    have hi_mem : i ∈ bad := Finset.max'_mem bad bad_nonempty
    simpa [bad] using hi_mem

  refine ⟨i, ?_, ?_⟩
  · -- the witness round is bad
    simpa [t] using hi_neq
  · intro j hij
    -- show every round after i is good, else contradict maximality of i
    by_contra hneq
    have hneq' : t.roundPolys j ≠ honestRoundPoly st.domain st.polynomial r j := by
      simpa [t] using hneq
    have hj_mem : j ∈ bad := by
      simp [bad, hneq']

    have hj_le : j ≤ i := by
      have hle : j ≤ Finset.max' bad bad_nonempty :=
        Finset.le_max' bad j hj_mem
      simpa [i] using hle

    exact (not_le_of_gt hij) hj_le
