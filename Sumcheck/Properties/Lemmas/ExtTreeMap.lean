import CompPoly.Data.ExtTreeMap.ExtTreeMap
import Mathlib.Tactic.Set

lemma Std.ExtTreeMap.foldl_empty
  {α : Type u} {β : Type v} {cmp : α → α → Ordering} {δ : Type w}
  [Std.TransCmp cmp]
  (f : δ → α → β → δ) (init : δ) :
  Std.ExtTreeMap.foldl (cmp := cmp) f init (∅ : Std.ExtTreeMap α β cmp) = init := by
  classical
  have hnil : ((∅ : Std.ExtTreeMap α β cmp).toList) = [] := by
    exact (Std.ExtTreeMap.toList_eq_nil_iff (t := (∅ : Std.ExtTreeMap α β cmp))).2 rfl
  simp [Std.ExtTreeMap.foldl_eq_foldl_toList, hnil]

lemma Std.ExtTreeMap.foldl_insert_empty
  {α : Type u} {β : Type v} {cmp : α → α → Ordering} {δ : Type w}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  [DecidableEq α] [DecidableEq β]
  (f : δ → α → β → δ) (init : δ) (k : α) (v : β) :
  Std.ExtTreeMap.foldl (cmp := cmp) f init
      ((∅ : Std.ExtTreeMap α β cmp).insert k v)
    =
  f init k v := by
  classical
  set t : Std.ExtTreeMap α β cmp := (∅ : Std.ExtTreeMap α β cmp).insert k v

  have hknot : k ∉ (∅ : Std.ExtTreeMap α β cmp) := by simp
  have hsize : t.size = 1 := by
    -- size_insert + size_empty
    simpa [t, hknot] using
      (Std.ExtTreeMap.size_insert
        (t := (∅ : Std.ExtTreeMap α β cmp)) (k := k) (v := v))

  have hlen : t.toList.length = 1 := by
    simp [Std.ExtTreeMap.length_toList, hsize]

  rcases (List.length_eq_one_iff.mp hlen) with ⟨a, ha⟩

  have hget : t[k]? = some v := by
    simp [t]

  have hmem : (k, v) ∈ t.toList := by
    exact (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some (t := t) (k := k) (v := v)).2 hget

  have haKV : a = (k, v) := by
    -- from membership in a singleton list
    have : (k, v) ∈ [a] := by simpa [ha] using hmem
    simpa using (List.mem_singleton.1 this).symm

  -- foldl over a singleton list
  simp [Std.ExtTreeMap.foldl_eq_foldl_toList, t, ha, haKV]

@[simp] lemma Std_ExtTreeMap_foldl_empty
  {α β σ : Type _} {cmp : α → α → Ordering} [Std.TransCmp cmp]
  (f : σ → α → β → σ) (init : σ) :
  Std.ExtTreeMap.foldl (cmp := cmp) f init (∅ : Std.ExtTreeMap α β cmp) = init := by
  simpa using (Std.ExtTreeMap.foldl_empty (cmp := cmp) (f := f) (init := init))
