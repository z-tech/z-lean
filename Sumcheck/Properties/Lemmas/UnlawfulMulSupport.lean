import CompPoly.Multivariate.Unlawful
import CompPoly.Multivariate.Lawful
import CompPoly.Data.ExtTreeMap.ExtTreeMap

namespace Sumcheck

open CPoly
open Std

namespace CPoly.Unlawful

lemma getElem?_fromUnlawful {n : ℕ} {R : Type _} [Zero R] [BEq R] [LawfulBEq R]
    (u : CPoly.Unlawful n R) (m : CPoly.CMvMonomial n) :
  (CPoly.Lawful.fromUnlawful (n := n) (R := R) u).1[m]?
    = Option.filter (fun c => c != 0) u[m]? := by
  unfold CPoly.Lawful.fromUnlawful
  -- Now LHS is `(Std.ExtTreeMap.filter (fun _ c => c != 0) u)[m]?`
  -- The library lemma has RHS `Option.filter ((fun _ c => c != 0) m) u[m]?`,
  -- so we align the goal with a `change` and then `exact` it.
  change (Std.ExtTreeMap.filter (fun (_ : CPoly.CMvMonomial n) (c : R) => c != 0) u)[m]?
      = Option.filter ((fun (_ : CPoly.CMvMonomial n) (c : R) => c != 0) m) u[m]?
  exact (Std.ExtTreeMap.getElem?_filter_with_getKey
    (f := fun (_ : CPoly.CMvMonomial n) (c : R) => c != 0)
    (k := m) (m := u))

lemma mem_fromUnlawful_imp_exists_coeff {n : ℕ} {R : Type _} [Zero R] [BEq R] [LawfulBEq R]
    (u : CPoly.Unlawful n R) (m : CPoly.CMvMonomial n) :
  m ∈ (CPoly.Lawful.fromUnlawful (n := n) (R := R) u)
    → ∃ v : R, v ≠ 0 ∧ u[m]? = some v := by
  intro hm
  classical
  rcases (CPoly.Lawful.mem_iff
      (p := CPoly.Lawful.fromUnlawful (n := n) (R := R) u) (x := m)).1 hm with
    ⟨v, hv0, hv_some⟩
  -- rewrite hv_some using getElem?_fromUnlawful
  have hv_filter :
      Option.filter (fun c => c != 0) u[m]? = some v := by
    -- IMPORTANT: plain rewrite, no `simpa` that can collapse to True
    exact (by
      -- hv_some : (fromUnlawful u).1[m]? = some v
      -- rewrite LHS
      simpa [getElem?_fromUnlawful (n := n) (R := R) u m] using hv_some)

  -- now destruct u[m]? and read off the witness
  cases h : u[m]? with
  | none =>
      -- filter none = none, contradiction
      simp [h] at hv_filter
  | some w =>
      -- First rewrite hv_filter so it talks about (some w)
      have hv_filter' : Option.filter (fun c => c != 0) (some w) = some v := by
        -- IMPORTANT: plain rewrite, no simp lemmas about filter_eq_some
        exact (by simpa [h] using hv_filter)

      -- Now do a controlled case split on (w != 0)
      by_cases hne : (w != 0) = true
      · -- unfold Option.filter, and rewrite using hne
        have hw_eq : some w = some v := by
          -- unfold Option.filter *as a definition*, so it becomes an if-then-else
          -- then rewrite with hne
          -- This avoids simp rewriting into ∧
          simpa [Option.filter, hne] using hv_filter'
        have hwv : w = v := by
          exact Option.some.inj hw_eq
        refine ⟨v, hv0, ?_⟩
        -- u[m]? = some v (rewrite h using hwv)
        simp [hwv]
      · -- if w != 0 is false, filter returns none, contradiction
        have : Option.filter (fun c => c != 0) (some w) = none := by
          simp [Option.filter, hne]
        -- contradict hv_filter'
        cases hv_filter' ▸ this

end CPoly.Unlawful

end Sumcheck
