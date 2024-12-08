# tlaplus-journey
TLA+ algorithms with TLAPS proofs

# [MoneyTransfer](src/moneyTransfer/MoneyTransfer.tla)
A simple (but not trivial) algorithm modeling money transfer between accounts.

What makes the algorithm non-trivial:
1. It is **fault-tolerant**.
1. It models any number of accounts and money transfers.
1. It is [fully proved](src/moneyTransfer/MoneyTransfer_proofs.tla) using the TLA+ Proof System (TLAPS).
1. The main invariant that is proved is a **global invariant**: the global amount of money present in the model.
1. It requires atomic operations on individual entities only (neither distributed transactions nor multi-row transactions are required)

# MoneyTransfer Proof

The inductive invariant **IndInv** is defined in the MoneyTransfer module. The main goal of the proof is to prove that IndInv is:
1. true in the initial state Init
1. maintained in all state transitions: init, debit, crash, credit

The following theorem confirms the two above properties of the MoneyTransfer algorithm:
>THEOREM IndInvPreserved == Spec => []IndInv

IndInv contains condition **"Imbalance = 0"**, which means that total amount of money modeled by the algorithm does not change when the algorithm is being executed. Imbalance is defined as follows:

> Imbalance == CreditTotal - DebitTotal + AmountPendingTotal

Proving that "Imbalance = 0" is always true is the **ultimate goal** of the proof.

## The component making the proof hard
**AmountPendingTotal** is the component making the proof hard:

>AmountPendingTotal == MapThenSumSet(transAmount, transPending)

**MapThenSumSet** resolves to a **recursive function**. It maps items from the "transPending" set and sums up mapped values. But it does not make proofs hard alone. It is the way that "transPending" is defined combined with the recursive function that makes the proof hard:
>transPending == {t \in Transfer: AmountIsPending(t)}

"transPending" is a subset of the Transfer set, and it changes **implicitly** during some steps: "debit" and "credit".

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

# The price we pay for having two equivalent algorithms
One fragment of the **specEquivalence** proof was particularly hard during developing the two MoneyTransfer algorithms:
>ASSUME NEW self \in Transfer, init(self)
PROVE E!init(self)

The workaround was to use one **redundant** condition:
>init:\
>&nbsp;&nbsp;&nbsp;&nbsp;if(initPrecond(self)) {

The above redundant condition is **completely unnecessary** in each of the two MoneyTransfer algorithms when treated separately.

The sole purpose of this redundant condition is to make the specEquivalence proof possible.

# Pre-Requisites
The project is being developed using:
- [TLA+ Toolbox v1.7.4](https://github.com/tlaplus/tlaplus/releases/tag/v1.7.4)
- [TLA+ Proof manager (tlapm)](https://github.com/tlaplus/tlapm)
- [TLA+ Community Modules](https://github.com/tlaplus/CommunityModules)

tlapm needs to be **built from sources**. The [latest available](https://github.com/tlaplus/tlapm/commit/ffb8846ff3c49d53ee6eeedfc4c8c4c409306ae3) sources of tlapm are used. The reason to build tlapm from sources is that its released versions use outdated [Isabelle](https://isabelle.in.tum.de) versions. And outdated Isabelle fails to prove some of the theorems. Using released versions of tlapm is possible but some theorems will not be proved.

The [latest tagged version](https://github.com/tlaplus/CommunityModules/releases/tag/202409181925) of Community Modules is used. The Community Modules source code is just checked out and the sources are used directly.

# Running the specification

## Running via IntelliJ

You can run the [MoneyTransfer](src/moneyTransfer/MoneyTransfer.tla) specification with IntelliJ, and it requires the TLA+ plug-in.

You have to specify the location of tlapm modules and Community Modules to run the specification:
> -DTLA-Library=/usr/local/lib/tlaps:`<Community Modules source parent directory>`/CommunityModules/modules