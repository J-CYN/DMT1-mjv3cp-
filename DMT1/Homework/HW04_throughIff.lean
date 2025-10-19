/- @@@
To prepare for this homework (1) be sure you
have read and understood the class materials
through 05_or.lean, corresponding to the "Or"
section in the online notes. (2) Refer to the
inference rules cheat sheet linked at the bottom
of the web site.
@@@ -/


/- @@@
#1. Suppose P and Q are any propositions.

#1.A: State and prove the conjecture that,
*and* implies *equivalence*. In other words,
if for any propositions, X and Y, X ∧ Y is
true, then it must be that X ↔ Y is as well.
Call your theorem andImpEquiv.
@@@ -/

--Left and right don't work without it for some strange reason


-- ANSWER
/-
This didn't work for some reason, so I wrote it another way as well

-- ANSWER (Formal proof in Lean)


theorem andImpEquiv (P Q: Prop) : (P ∧ Q) → P ↔ Q :=
  fun (pq: P ∧ Q) =>
    let PipQ := fun(p : P) => pq.right
    let QipP := fun(q : Q) => pq.left
    Iff.intro PipQ QipP
-/

theorem andImpEquiv (P Q : Prop) (pq : P ∧ Q) : P ↔ Q :=
  Iff.intro (fun p => pq.right) (fun q => pq.left)

/- @@@
#2: Give the proof for #1 in English. To do this,
just explain clearly what assumptions you make or
use at each step and what inference rules you use
to make progress at each step. We get you started:

-- ANSWER

So the defined theorem proposes that when given a proof of P ∧ Q which is pq,
in which P and Q are propositions, by applying a function in which we
provide a proof of P and know a proof of pq(a proof of P ∧ Q) then we
can create a proof that Q is true, and the same for a proof of pq and Q to create a proof of P.
So using the functions that make this process possible we can use Iff.intro and these two functions to prove that if one is true,
the other is also true assuming our provided proofs.

-- PARTIAL ANSWER, YOU COMPLETE IT


Proof: To prove this *implication* we'll use the
introduction rule for →. So *assume* the premise
is true. What remains to be proved is that, in
this context,  the conclusion must be true as well.
So assume P ∧ Q is true.

What now remains to be proved is an equivalence,
namely _____. To prove an equivalence we need to
prove both ... and ... To prove ...
@@@ -/


/- @@@
#3: Use axiom declarations to represent this world.

- X is a proposition
- Y is a propostion
- X ∧ Y is true

Once you've done that, in a #check command, apply
the general theorem we just proved to prove that X
is equivalent to Y.

Use this example to help you see that once you've
proved a theorem (as in #1 above) you can use it by
applying it to prove any special case, here with X
and Y in place of the formal parameters in the
statement of the theorem itself.
@@@ -/

-- Answer

axiom X: Prop
axiom Y: Prop
axiom xy: X ∧ Y
#check andImpEquiv X Y xy

/- @@@
#4: Something About False

Recall from class discussion that the proposition,
in Lean, called False, has no proofs at all. That
is what makes it false. Assuming that there is one
assumes something that's impossibile. The crucial
conclusion to draw is *not* that the impossible is
suddenly possible, but that the *assumption* itself
must be wrong. Therefore, if at any point in trying
to prove something we can derive a proof of False,
that means we're in a situation that can't actually
happen. So we really don't have to finish the proof!

For example, suppose  K is some unknown proposition.
When we say that (False → K) is true, we are *not*
saying that *K* is true; we're saying that once you
assume or can derive a proof of False, you know you
are in a case that can never happen, so you can just
"bail out" and not worry about constructing a proof
of K, no matter what proposition it is. The keyword
*nomatch* in Lean applied to any proof of false does
exactly bail one of of an impossible case.

Here's a formal proof of it. We assume K is any
proposition, then we prove False → K. To prove
this implication, we assume we're given f, a proof
of false. In any other situation, for *exFalsoK*
to be defined, we'd *have to* return some value of
type K. Here we don't even know what that type is.
And yet the function is well-defined, and as such
*proves* the implication, *False → K*. The trick
of course, is that as soon as we have a proof of
false in (or derivable given) our context, then we
can *bail out* and Lean will accept the definition.
Lean's *nomatch* contruct will bail you out as long
as it's applied to a proof of false, which is the
evidence Lean needs to know it's ok to accept the
definition.
@@@ -/

-- ANSWER
def exFalsoK (K : Prop) : False → K :=
  False.elim


def exFalsoK' (K : Prop) : False → K :=
  fun f => nomatch f

/- @@@
Why is it safe to accept tihs definition? What do we
know that's special about *exFalsoK* that makes it ok?

ANSWER:
It is safe to accept this definition because we've gotten to a point that should
be impossible in reasoning. The very things we assume as our parameters make sure
that there is no valid way to get to this point. A proof of false is impossible
so if we have one, something wrong has occurred and we are no longer in
as valid nor possible context we basically just "bail out" and say it's true as
this context is once again, not possible and therefore doesn't really matter.
@@@ -/


/- @@@
#5 In Lean, state and prove the proposition that is
P and Q are aribtrary propositions, then False *and*
P implies Q.
@@@-/

-- ANSWER
def False_P_IMP_Q (P Q: Prop) : P ∧ False → Q :=
  fun(P_False) => nomatch P_False.right

/- @@@
Write a short paragraph stating the proposition to be
proved and the proof of it -- in English.
@@@ -/

-- ANSWER
/-We are trying to prove that False and P implies Q
We assumed P and Q are arbitrary Props
And we are trying to prove that when given a Proposition of P and False
that we can derive a proof of Q from it. Since a proof of P ∧ False would require
a proof of that would require both a proof of P and a proof of False, it is impossible to
get to this stage of a proof. It is almost impossible. So we can break the and apart and grab the proof of False
from the P ∧ False proposition and use nomatch on it to get out of the proof.
-/

/- @@@
#6 State and prove the proposition that False → False.
Give both formal and English (natural language) proofs.
@@@ -/

def False_False : False → False :=
  fun(Input_False) => nomatch Input_False

-- ANSWER

/-
If given a proof of False, we can return a proof of False. In reality this is just
an identity property, so lean can prove this rather easily. As a function that just
takes it's proof of False input and applies no match to it to quickly by pass the proof.
-/
