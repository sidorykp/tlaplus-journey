
# A Redundant Algorithm: [MoneyTransferPendingExplicit](src/moneyTransfer/MoneyTransferPendingExplicit.tla)

MoneyTransfer is hard to prove. Almost all theorems that require to prove how AmountPendingTotal changes (or does not change) in a given step require extra effort. And theorem init_AmountPendingTotal_initPrecond is the hardest from them all.

It is much easier to prove a redundant algorithm: MoneyTransferPendingExplicit, which:

1. has one more variable: "pendingTrans"
1. the "pendingTrans" is set explicitly, it is redundant, and it **duplicates** the dynamically calculated "transPending" set
1. "pendingTrans" can be derived from the original MoneyTransfer algorithm
1. its IndInv has all MoneyTransfer's IndInv constraints including "Imbalance = 0", and it has additional constraints making it inductively invariant.

The redundant algorithm uses the following expression
>AmountPendingTotal == MapThenSumSet(pendingTransAmount, pendingTrans)

"pendingTrans" changes **explicitly** during the "debit" and "credit" steps, making proofs of how AmountPendingTotal changes (or does not change) in algorithm steps very easy, like in the following fragment of the proof:
> PROVE AmountPendingTotal' = AmountPendingTotal - amount[self]
BY DEF credit, AmountPendingTotal

The MoneyTransferPendingExplicit [proof](src/moneyTransfer/MoneyTransferPendingExplicit_proofs.tla) concludes with the analogous theorem as in the MoneyTransfer proof:
>THEOREM IndInvPreservedE == Spec => []IndInv

The main difference compared to MoneyTransfer is that a **different expression for AmountPendingTotal** is used in MoneyTransferPendingExplicit.

# Equivalence Between MoneyTransfer and MoneyTransferPendingExplicit
The MoneyTransfer becomes **identical** to MoneyTransferPendingExplicit when pendingTrans is **derived** by using the following expression:
> pendingTransDerived == {<<t, amount[t]>>: t \in {t \in Transfer: AmountIsPending(t)}}

Proving that it indeed becomes identical allows to act on a **higher level**, above the individual algorithm level.

The derivation of pendingTrans in MoneyTransferPendingExplicit is done by using the following substitution:
>E == INSTANCE MoneyTransferPendingExplicit WITH pendingTrans <- pendingTransDerived

The specification of the "E" algorithm is **E!Spec** and it is the Spec of **MoneyTransferPendingExplicit** with pendingTrans substituted with this:
>{<<t, amount[t]>>: t \in {t \in Transfer: AmountIsPending(t)}}

It is [proved](src/moneyTransfer/MoneyTransferEquivalence.tla) that Spec and E!Spec are identical:
>THEOREM specEquivalence == E!Spec <=> Spec

# Common use of equivalence between two algorithms

Proving equivalence between two algorithms is an **advanced topic** but the need to prove such equivalence is **common**.

This is because algorithm implementations usually contain **more variables** than (abstract) algorithms contain. You could add e.g. timestamps to each state transition in the algorithm implementation, and it would mean more variables.

It should be **proved** that adding more variables maintains invariants that are meant to be invariants in the implementation **intact**.

If we do not prove the above fact then we risk that our precious invariants are violated.

# Utilization of the equivalence between two algorithms
Our assumption about MoneyTransfer and MoneyTransferPendingExplicit is that they both produce the same value for AmountPendingTotal.
They use **different variables** to calculate AmountPendingTotal though:
>MapThenSumSet(transAmount, transPending)\
> in MoneyTransfer
>
vs
> MapThenSumSet(pendingTransAmount, pendingTrans)\
> in MoneyTransferPendingExplicit

"transPending" is implicit and is derived from existing variables. "pendingTrans" is a variable and is set explicitly.

It is proved that AmountPendingTotal is indeed the same under Spec:
>THEOREM Spec => [](E!AmountPendingTotal = AmountPendingTotal)

A **direct proof** of the above theorem by using E!AmountPendingTotal and AmountPendingTotal definitions **failed** so far.

But the **indirect proof succeeds**. The crucial part of the indirect proof is this:
> Spec => [](E!Imbalance = 0 /\ Imbalance = 0)

and the **specEquivalence** theorem is used to prove this crucial part.

Utilizing equivalence between algorithms is an advanced topic because it requires:
1. proving two different algorithms individually
1. proving equivalence between two algorithms
1. proving the property that we are interested in based on the proved equivalence
