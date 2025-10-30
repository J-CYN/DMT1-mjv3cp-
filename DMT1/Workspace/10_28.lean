#check And

namespace cs2120

structure And (a b: Prop) : Prop where
  intro ::
  left : a
  right : b

inductive Sum (α : Type u) (β : Type v) where
  | inl (val : α) : Sum α β
  | inr (val : β) : Sum α β

end cs2120


#check Prod

def pr : Prod Nat Bool := Prod.mk 2 true

def pr1: Prod Nat Bool := Prod.mk 5 false
def pr2: Nat × Bool := (4, true)
def pr3 := ("Hello", true)
def pr4 := ("Hello", "Bye")
#check pr4

def swap {α β : Type} : (α × β) → (β × α) :=
(
  fun(ab: α × β) =>
  (
    Prod.mk ab.snd ab.fst
  )
)

example {P Q : Prop} : P ∧ Q → Q ∧ P :=
  fun (h) =>
  (
    And.intro h.right h.left
  )

#eval (swap pr3)

def v1 : Nat ⊕ String := Sum.inr "Hello"
def v2 : Nat ⊕  String := Sum.inl 5

def bar {α β : Type} : α ⊕ β → β ⊕ α :=
(
  fun nbpr =>
  (
    match nbpr with
    | Sum.inl a => Sum.inr a
    | Sum.inr b => Sum.inl b
  )
)

def porq_comm {P Q: Prop} : P ∨ Q → Q ∨ P :=
fun h =>
(
  match h with
  | Or.inl p => Or.inr p
  | Or.inr q => Or.inl q
)
#check Or

#check Sum

#check Eq
#check Eq 3 5
#check Eq 1 "true"
#check Eq true false

#check Eq.refl
#check Eq.subst
