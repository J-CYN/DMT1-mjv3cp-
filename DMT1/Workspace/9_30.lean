theorem hungry (H M S: Prop) : (H ∧ M) → (H → M → S) → S :=
  (
    fun (hm : H ∧ M) =>
      fun(hms: H → M → S)=>
        (
          hms hm.left hm.right
        )
  )

theorem xyz (C M B: Prop) : (C ∨ M) → (C → B) → (M → B) → B :=
  fun(corm cb mb) =>
    match corm with
    | Or.inl c => cb c
    | Or.inr m => mb m

#check Or

/-
inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b
-/

theorem orComm (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) :=
  Iff.intro
  -- forward
  (
    fun porq =>
    (
      Or.inl
    )
  )
  -- backward
  (
    fun porq =>
    (
      Or.inr
    )
  )
