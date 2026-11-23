namespace DiscreteAlgebra

/-- Inductive duplicate-free predicate on finite lists. -/
inductive NoDup {α : Type} : List α → Prop where
  | nil : NoDup []
  | cons {a : α} {xs : List α} : a ∉ xs → NoDup xs → NoDup (a :: xs)

/-- Removes the first occurrence of `x` from a list, if present. -/
def eraseFirst {α : Type} [DecidableEq α] (x : α) : List α → List α
  | [] => []
  | a :: xs => if a = x then xs else a :: eraseFirst x xs

/-- Counts the multiplicity of `x` in a finite list. -/
def count {α : Type} [DecidableEq α] (x : α) : List α → Nat
  | [] => 0
  | a :: xs => if a = x then count x xs + 1 else count x xs

private theorem mem_eraseFirst_of_ne {α : Type} [DecidableEq α] {x y : α} {l : List α}
    (hne : y ≠ x) (hmem : y ∈ l) : y ∈ eraseFirst x l := by
  induction l with
  | nil => simp at hmem
  | cons a xs ih =>
    simp only [eraseFirst]
    split
    · next hax =>
      simp only [List.mem_cons] at hmem
      cases hmem with
      | inl hya => exact False.elim (hne (hya.trans hax))
      | inr hys => exact hys
    · next hax =>
      simp only [List.mem_cons] at hmem ⊢
      cases hmem with
      | inl hya => exact Or.inl hya
      | inr hys => exact Or.inr (ih hys)

private theorem length_eraseFirst_of_mem {α : Type} [DecidableEq α] {x : α} {l : List α}
    (hmem : x ∈ l) : (eraseFirst x l).length + 1 = l.length := by
  induction l with
  | nil => simp at hmem
  | cons a xs ih =>
    simp only [eraseFirst]
    split
    · rfl
    · next hax =>
      simp only [List.mem_cons] at hmem
      cases hmem with
      | inl hxa => exact False.elim (hax hxa.symm)
      | inr hxs =>
        have hlen := ih hxs
        simp only [List.length_cons]
        omega

private theorem one_le_count_of_mem {α : Type} [DecidableEq α] {x : α} {l : List α}
    (hmem : x ∈ l) : 1 ≤ count x l := by
  induction l with
  | nil => simp at hmem
  | cons a xs ih =>
    simp only [count]
    split
    · omega
    · next hax =>
      simp only [List.mem_cons] at hmem
      cases hmem with
      | inl hxa => exact False.elim (hax hxa.symm)
      | inr hxs => exact ih hxs

private theorem exists_two_le_count_of_not_nodup {α : Type} [DecidableEq α] {l : List α}
    (hnot : ¬ NoDup l) : ∃ x, 2 ≤ count x l := by
  induction l with
  | nil => exact False.elim (hnot NoDup.nil)
  | cons a xs ih =>
    cases hc : count a xs with
    | zero =>
      have hnotmem : a ∉ xs := by
        intro hmem
        have hpos := one_le_count_of_mem hmem
        omega
      have hnot_xs : ¬ NoDup xs := by
        intro hnd_xs
        exact hnot (NoDup.cons hnotmem hnd_xs)
      cases ih hnot_xs with
      | intro x hx =>
        refine ⟨x, ?_⟩
        simp only [count]
        split <;> omega
    | succ c =>
      refine ⟨a, ?_⟩
      simp only [count]
      split
      · omega
      · next hneq => exact False.elim (hneq rfl)

/-- Filtering a finite list never increases its cardinality. -/
theorem length_filter_le {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a xs ih =>
    cases h : p a <;> simp [List.filter, h] <;> omega

/-- Partition cardinality identity: filtered elements and their complement sum to the list length. -/
theorem length_filter_add_not {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => simp
  | cons a xs ih =>
    cases h : p a <;> simp [List.filter, h] <;> omega

/-- Cardinality monotonicity: a duplicate-free list contained in `l₂` has length at most `l₂.length`. -/
theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] {l₁ l₂ : List α}
    (hnd : NoDup l₁) (hsub : ∀ x, x ∈ l₁ → x ∈ l₂) : l₁.length ≤ l₂.length := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a xs ih =>
    cases hnd with
    | cons hnotmem hnd_xs =>
      have ha : a ∈ l₂ := hsub a (by simp)
      have hsub' : ∀ y, y ∈ xs → y ∈ eraseFirst a l₂ := by
        intro y hy
        have hne : y ≠ a := by
          intro heq
          rw [heq] at hy
          exact hnotmem hy
        have hmem2 : y ∈ l₂ := hsub y (by simp [hy])
        exact mem_eraseFirst_of_ne hne hmem2
      have hle : xs.length ≤ (eraseFirst a l₂).length := ih hnd_xs hsub'
      have hlen : (eraseFirst a l₂).length + 1 = l₂.length := length_eraseFirst_of_mem ha
      simp only [List.length_cons]
      omega

/-- Finite Pigeonhole Principle: if every element of `l₁` occurs in `l₂` and
`l₂.length < l₁.length`, then some element appears at least twice in `l₁`. -/
theorem pigeonhole_exists_dup {α : Type} [DecidableEq α] {l₁ l₂ : List α}
    (hlt : l₂.length < l₁.length) (hsub : ∀ x, x ∈ l₁ → x ∈ l₂) :
    ∃ x, 2 ≤ count x l₁ := by
  apply exists_two_le_count_of_not_nodup
  intro hnd
  have hle := nodup_length_le_of_subset hnd hsub
  omega

end DiscreteAlgebra
