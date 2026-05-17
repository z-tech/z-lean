/-
# Code restriction to a support set

For a linear code `c ⊆ Fⁿ` and a coordinate set `T ⊆ [n]`, the
*restriction* `c|T` is the image of `c` under projecting onto the `T`
coordinates. BCGM25's MCA framework is phrased in terms of restricted
codes: `u|T ∈ c|T` means "there is a codeword agreeing with `u` on `T`".

We use a predicate form rather than a separate submodule: this is
lighter and keeps the ambient type uniform (`Fin n → F`) across calls.
The two forms are equivalent for our purposes.
-/

import LinearCodes.Algebraic.Code


namespace LinearCodes

variable {F : Type*} [Field F] {n : ℕ}

/-- A vector `u` lies in the restriction of code `c` to support `T` iff
some codeword of `c` agrees with `u` on every coordinate of `T`. -/
def InRestrictedCode (c : Submodule F (Fin n → F)) (T : Finset (Fin n))
    (u : Fin n → F) : Prop :=
  ∃ v ∈ c, ∀ i ∈ T, v i = u i

/-! ### Basic identities -/

/-- A codeword of `c` lies in `c|T` for any support `T`. -/
theorem inRestrictedCode_of_mem (c : Submodule F (Fin n → F))
    (T : Finset (Fin n)) {u : Fin n → F} (hu : u ∈ c) :
    InRestrictedCode c T u :=
  ⟨u, hu, fun _ _ => rfl⟩

/-- The zero vector lies in `c|T` for any code `c` (since `0 ∈ c`). -/
theorem inRestrictedCode_zero (c : Submodule F (Fin n → F))
    (T : Finset (Fin n)) :
    InRestrictedCode c T 0 :=
  ⟨0, c.zero_mem, fun _ _ => rfl⟩

/-- Restriction to the full coordinate set is the same as full membership. -/
theorem inRestrictedCode_univ_iff (c : Submodule F (Fin n → F))
    {u : Fin n → F} :
    InRestrictedCode c Finset.univ u ↔ u ∈ c := by
  constructor
  · rintro ⟨v, hv, hagree⟩
    have hvu : v = u := funext fun i => hagree i (Finset.mem_univ i)
    rwa [hvu] at hv
  · intro hu
    exact ⟨u, hu, fun i _ => rfl⟩

/-- Restriction to the empty set is trivial — every vector belongs. -/
theorem inRestrictedCode_empty (c : Submodule F (Fin n → F))
    (u : Fin n → F) :
    InRestrictedCode c ∅ u :=
  ⟨0, c.zero_mem, fun i hi => by simp at hi⟩

/-- Restriction is monotone: if `u ∈ c|T'` and `T ⊆ T'`, then `u ∈ c|T`. -/
theorem inRestrictedCode_mono {c : Submodule F (Fin n → F)}
    {T T' : Finset (Fin n)} (h : T ⊆ T') {u : Fin n → F}
    (hu : InRestrictedCode c T' u) :
    InRestrictedCode c T u := by
  obtain ⟨v, hv, hagree⟩ := hu
  exact ⟨v, hv, fun i hi => hagree i (h hi)⟩

/-- Closure under vector addition: if `u₁, u₂ ∈ c|T` then `u₁ + u₂ ∈ c|T`. -/
theorem inRestrictedCode_add {c : Submodule F (Fin n → F)}
    {T : Finset (Fin n)} {u₁ u₂ : Fin n → F}
    (h₁ : InRestrictedCode c T u₁) (h₂ : InRestrictedCode c T u₂) :
    InRestrictedCode c T (u₁ + u₂) := by
  obtain ⟨v₁, hv₁, h₁'⟩ := h₁
  obtain ⟨v₂, hv₂, h₂'⟩ := h₂
  refine ⟨v₁ + v₂, c.add_mem hv₁ hv₂, fun i hi => ?_⟩
  simp [Pi.add_apply, h₁' i hi, h₂' i hi]

/-- Closure under scalar multiplication. -/
theorem inRestrictedCode_smul {c : Submodule F (Fin n → F)}
    {T : Finset (Fin n)} {u : Fin n → F} (α : F)
    (hu : InRestrictedCode c T u) :
    InRestrictedCode c T (α • u) := by
  obtain ⟨v, hv, hagree⟩ := hu
  refine ⟨α • v, c.smul_mem α hv, fun i hi => ?_⟩
  simp [Pi.smul_apply, hagree i hi]

/-- Unfold-form: explicit existential characterisation. -/
theorem inRestrictedCode_iff (c : Submodule F (Fin n → F))
    (T : Finset (Fin n)) (u : Fin n → F) :
    InRestrictedCode c T u ↔ ∃ v ∈ c, ∀ i ∈ T, v i = u i := Iff.rfl

/-! ### More closure properties -/

/-- Closure under negation. -/
theorem inRestrictedCode_neg {c : Submodule F (Fin n → F)}
    {T : Finset (Fin n)} {u : Fin n → F}
    (hu : InRestrictedCode c T u) :
    InRestrictedCode c T (-u) := by
  obtain ⟨v, hv, hagree⟩ := hu
  refine ⟨-v, c.neg_mem hv, fun i hi => ?_⟩
  simp [Pi.neg_apply, hagree i hi]

/-- Closure under subtraction. -/
theorem inRestrictedCode_sub {c : Submodule F (Fin n → F)}
    {T : Finset (Fin n)} {u₁ u₂ : Fin n → F}
    (h₁ : InRestrictedCode c T u₁) (h₂ : InRestrictedCode c T u₂) :
    InRestrictedCode c T (u₁ - u₂) := by
  obtain ⟨v₁, hv₁, h₁'⟩ := h₁
  obtain ⟨v₂, hv₂, h₂'⟩ := h₂
  refine ⟨v₁ - v₂, c.sub_mem hv₁ hv₂, fun i hi => ?_⟩
  simp [Pi.sub_apply, h₁' i hi, h₂' i hi]

/-- Restriction to a singleton support: `u ∈ c|{i}` iff some codeword
agrees with `u` at coordinate `i`. -/
theorem inRestrictedCode_singleton (c : Submodule F (Fin n → F))
    (i : Fin n) (u : Fin n → F) :
    InRestrictedCode c {i} u ↔ ∃ v ∈ c, v i = u i := by
  unfold InRestrictedCode
  constructor
  · rintro ⟨v, hv, hagree⟩
    exact ⟨v, hv, hagree i (Finset.mem_singleton.mpr rfl)⟩
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, fun j hj => ?_⟩
    rw [Finset.mem_singleton] at hj
    rw [hj]; exact h

end LinearCodes
