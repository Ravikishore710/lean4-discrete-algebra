import DiscreteAlgebra.CardinalityBounds

namespace DiscreteAlgebra

/-- Sum of a finite list of natural numbers. -/
def listSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + listSum xs

/-- Cartesian product of two finite lists. -/
def cartProd {α β : Type} : List α → List β → List (α × β)
  | [], _ => []
  | a :: as, ys => ys.map (fun b => (a, b)) ++ cartProd as ys

private theorem exists_of_mem_map {α β : Type} {f : α → β} {y : β} {l : List α}
    (h : y ∈ l.map f) : ∃ x, x ∈ l ∧ f x = y := by
  induction l with
  | nil => simp at h
  | cons a xs ih =>
    simp only [List.map_cons, List.mem_cons] at h
    cases h with
    | inl hya => exact ⟨a, by simp, hya.symm⟩
    | inr hys =>
      cases ih hys with
      | intro x hx => exact ⟨x, by simp [hx.1], hx.2⟩

private theorem listSum_map_zero {α : Type} (l : List α) :
    listSum (l.map fun _ => 0) = 0 := by
  induction l with
  | nil => rfl
  | cons _ xs ih => simp [listSum, ih]

private theorem listSum_filter_cons {α β : Type} (R : α → β → Bool)
    (a : α) (as : List α) (ys : List β) :
    listSum (ys.map fun b => ((a :: as).filter fun x => R x b).length) =
    (ys.filter fun b => R a b).length +
    listSum (ys.map fun b => (as.filter fun x => R x b).length) := by
  induction ys with
  | nil => simp [listSum]
  | cons b bs ih =>
    cases h : R a b <;> simp [List.filter, listSum, h] <;> omega

private theorem listSum_map_const {α : Type} (l : List α) (f : α → Nat) (k : Nat)
    (h : ∀ x, x ∈ l → f x = k) : listSum (l.map f) = l.length * k := by
  induction l with
  | nil => simp [listSum]
  | cons a xs ih =>
    have ha : f a = k := h a (by simp)
    have hxs : listSum (xs.map f) = xs.length * k := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, listSum, List.length_cons, ha, hxs]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- Injective maps preserve the duplicate-free property on finite lists. -/
theorem nodup_map_of_injective {α β : Type} {f : α → β} {l : List α}
    (hinj : ∀ x y : α, f x = f y → x = y) (hnd : NoDup l) : NoDup (l.map f) := by
  induction l with
  | nil => exact NoDup.nil
  | cons a xs ih =>
    cases hnd with
    | cons hnotmem hnd_xs =>
      apply NoDup.cons
      · intro hmem
        cases exists_of_mem_map hmem with
        | intro x hx =>
          have hxa : x = a := hinj x a hx.2
          rw [hxa] at hx
          exact hnotmem hx.1
      · exact ih hnd_xs

/-- Injective cardinality bound: if an injection maps a duplicate-free list `l₁` into `l₂`,
then `l₁.length ≤ l₂.length`. -/
theorem card_le_of_inj_on_list {α β : Type} [DecidableEq β] {f : α → β}
    {l₁ : List α} {l₂ : List β}
    (hinj : ∀ x y : α, f x = f y → x = y)
    (hnd : NoDup l₁)
    (hmap : ∀ x, x ∈ l₁ → f x ∈ l₂) :
    l₁.length ≤ l₂.length := by
  have hnd_map : NoDup (l₁.map f) := nodup_map_of_injective hinj hnd
  have hsub : ∀ y, y ∈ l₁.map f → y ∈ l₂ := by
    intro y hy
    cases exists_of_mem_map hy with
    | intro x hx =>
      rw [← hx.2]
      exact hmap x hx.1
  have hle := nodup_length_le_of_subset hnd_map hsub
  simp only [List.length_map] at hle
  exact hle

/-- Finite Bijection Principle: duplicate-free finite lists in bijection have equal cardinality. -/
theorem card_eq_of_bij_on_list {α β : Type} [DecidableEq α] [DecidableEq β]
    {f : α → β} {g : β → α} {l₁ : List α} {l₂ : List β}
    (hleft : ∀ x : α, g (f x) = x)
    (hright : ∀ y : β, f (g y) = y)
    (hnd₁ : NoDup l₁) (hnd₂ : NoDup l₂)
    (hf : ∀ x, x ∈ l₁ → f x ∈ l₂)
    (hg : ∀ y, y ∈ l₂ → g y ∈ l₁) :
    l₁.length = l₂.length := by
  have hfinj : ∀ x y : α, f x = f y → x = y := by
    intro x y hxy
    calc x = g (f x) := (hleft x).symm
      _ = g (f y) := by rw [hxy]
      _ = y := hleft y
  have hginj : ∀ x y : β, g x = g y → x = y := by
    intro x y hxy
    calc x = f (g x) := (hright x).symm
      _ = f (g y) := by rw [hxy]
      _ = y := hright y
  have hle1 : l₁.length ≤ l₂.length := card_le_of_inj_on_list hfinj hnd₁ hf
  have hle2 : l₂.length ≤ l₁.length := card_le_of_inj_on_list hginj hnd₂ hg
  omega

/-- General finite double-counting theorem: summing row degrees of a binary relation equals
summing its column degrees. -/
theorem double_counting {α β : Type} (R : α → β → Bool) (xs : List α) (ys : List β) :
    listSum (xs.map fun a => (ys.filter fun b => R a b).length) =
    listSum (ys.map fun b => (xs.filter fun a => R a b).length) := by
  induction xs with
  | nil =>
    simp only [List.map_nil, listSum, List.filter, List.length_nil]
    exact (listSum_map_zero ys).symm
  | cons a as ih =>
    simp only [List.map_cons, listSum]
    rw [ih, listSum_filter_cons]

/-- Regular bipartite double-counting identity: if every element of `xs` has degree `r` and
every element of `ys` has degree `c`, then `|xs| * r = |ys| * c`. -/
theorem double_counting_regular {α β : Type} (R : α → β → Bool) (xs : List α) (ys : List β)
    (r c : Nat)
    (hrow : ∀ a, a ∈ xs → (ys.filter fun b => R a b).length = r)
    (hcol : ∀ b, b ∈ ys → (xs.filter fun a => R a b).length = c) :
    xs.length * r = ys.length * c := by
  have hdc := double_counting R xs ys
  rw [listSum_map_const xs _ r hrow, listSum_map_const ys _ c hcol] at hdc
  exact hdc

/-- Product rule for finite cardinality: `|xs × ys| = |xs| * |ys|`. -/
theorem length_cartProd {α β : Type} (xs : List α) (ys : List β) :
    (cartProd xs ys).length = xs.length * ys.length := by
  induction xs with
  | nil => simp [cartProd]
  | cons a as ih =>
    simp only [cartProd, List.length_append, List.length_map, List.length_cons, ih]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

end DiscreteAlgebra
