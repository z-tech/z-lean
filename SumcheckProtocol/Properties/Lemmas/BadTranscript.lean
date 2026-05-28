import CompPoly.Multivariate.CMvPolynomial

import SumcheckProtocol.Properties.Events.BadTranscript

/-- K-parameterized: a bad partial-run transcript has a last bad round. -/
lemma badTranscript_implies_lastBadRound_k
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (k : Fin (n + 1))
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) k))
  (r : Fin k.val → 𝔽) :
  BadTranscriptEvent k st.domain st.polynomial (proverTranscript k st P r) →
  LastBadRound k st P r := by
  classical
  intro hBad
  let t : Transcript 𝔽 k.val := proverTranscript k st P r
  let bad : Finset (Fin k.val) :=
    Finset.univ.filter (fun i => t.roundPolys i ≠ honestRoundPolyAtK k st.domain st.polynomial r i)
  have bad_nonempty : bad.Nonempty := by
    rcases hBad with ⟨i0, hi0⟩
    refine ⟨i0, ?_⟩
    simpa [bad, BadRound, t] using hi0
  let i : Fin k.val := Finset.max' bad bad_nonempty
  have hi_neq :
      t.roundPolys i ≠ honestRoundPolyAtK k st.domain st.polynomial r i := by
    have hi_mem : i ∈ bad := Finset.max'_mem bad bad_nonempty
    simpa [bad] using hi_mem
  refine ⟨i, ?_, ?_⟩
  · simpa [t] using hi_neq
  · intro j hij
    by_contra hneq
    have hneq' : t.roundPolys j ≠ honestRoundPolyAtK k st.domain st.polynomial r j := by
      simpa [t] using hneq
    have hj_mem : j ∈ bad := by simp [bad, hneq']
    have hj_le : j ≤ i := by
      have hle : j ≤ Finset.max' bad bad_nonempty := Finset.le_max' bad j hj_mem
      simpa [i] using hle
    exact (not_le_of_gt hij) hj_le

lemma badTranscript_implies_lastBadRound
  {𝔽 : Type _} {n : ℕ}
  [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
  (st : SumcheckProtocolStatement 𝔽 n)
  (P : Prover (sumcheckProtocol (𝔽 := 𝔽) (n := n) ⟨n, Nat.lt_succ_self n⟩))
  (r : Fin n → 𝔽) :
  BadTranscriptEvent ⟨n, Nat.lt_succ_self n⟩ st.domain st.polynomial
    (proverTranscript ⟨n, Nat.lt_succ_self n⟩ st P r) →
  LastBadRound ⟨n, Nat.lt_succ_self n⟩ st P r := by
  classical
  intro hBad
  let t : Transcript 𝔽 n := proverTranscript ⟨n, Nat.lt_succ_self n⟩ st P r

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
