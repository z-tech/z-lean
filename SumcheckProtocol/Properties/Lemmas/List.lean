import Mathlib.Data.List.Basic
import Mathlib.Algebra.Group.Defs

lemma List.foldl_mul_pull_out
  {α β : Type _} [Monoid α]
  (h : β → α) :
  ∀ (a : α) (l : List β),
    List.foldl (fun acc x => acc * h x) a l
      =
    a * List.foldl (fun acc x => acc * h x) 1 l
  | a, [] =>
      by
        -- LHS = a, RHS = a * 1
        simp
  | a, x :: xs =>
      by
        -- recursive instances (IMPORTANT: pass h := h)
        have ih_a :
            List.foldl (fun acc t => acc * h t) (a * h x) xs
              =
            (a * h x) * List.foldl (fun acc t => acc * h t) 1 xs :=
          (List.foldl_mul_pull_out (h := h) (a := a * h x) (l := xs))

        have ih_hx :
            List.foldl (fun acc t => acc * h t) (h x) xs
              =
            (h x) * List.foldl (fun acc t => acc * h t) 1 xs :=
          (List.foldl_mul_pull_out (h := h) (a := h x) (l := xs))

        -- main calc
        calc
          List.foldl (fun acc t => acc * h t) a (x :: xs)
              = List.foldl (fun acc t => acc * h t) (a * h x) xs := rfl
          _ = (a * h x) * List.foldl (fun acc t => acc * h t) 1 xs := ih_a
          _ = a * (h x * List.foldl (fun acc t => acc * h t) 1 xs) := by
                -- reassociate: (a*h x)*rest = a*(h x*rest)
                simp [mul_assoc]
          _ = a * List.foldl (fun acc t => acc * h t) (h x) xs := by
                -- use ih_hx backwards inside `a * _`
                simpa using congrArg (fun z => a * z) ih_hx.symm
          _ = a * List.foldl (fun acc t => acc * h t) (1 * h x) xs := by
                simp
          _ = a * List.foldl (fun acc t => acc * h t) 1 (x :: xs) := rfl
