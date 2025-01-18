# tlaplus-journey
TLA+ algorithms with TLAPS proofs

# [MoneyTransferReference](src/moneyTransfer/MoneyTransferReference.tla)
A simple (but not trivial) algorithm modeling money transfer between accounts.

What makes the algorithm non-trivial:
1. It is **fault-tolerant**.
1. It models any number of accounts and money transfers.
1. It is [fully proved](src/moneyTransfer/MoneyTransferReference_proofs.tla) using the TLA+ Proof System (TLAPS).
1. The main invariant that is proved is a **global invariant**: the global amount of money present in the model.
1. It requires atomic operations on individual entities only (neither distributed transactions nor multi-row transactions are required)

# [MoneyTransferReference Proof](src/moneyTransfer/MoneyTransferReference_proofs.tla)

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

# Pre-Requisites
The project is being developed using:
- [TLA+ Toolbox v1.7.4](https://github.com/tlaplus/tlaplus/releases/tag/v1.7.4)
- [TLA+ Proof manager (tlapm)](https://github.com/tlaplus/tlapm)
- [TLA+ Community Modules](https://github.com/tlaplus/CommunityModules)

tlapm version [1.6.0-pre](https://github.com/tlaplus/tlapm/releases/tag/1.6.0-pre) is used to work with the project's code. Using older versions of tlapm is possible but some theorems will not be proved then.

The [latest tagged version](https://github.com/tlaplus/CommunityModules/releases/tag/202409181925) of Community Modules is used. The Community Modules source code is just checked out and the sources are used directly.

# Running the specification

## Running via IntelliJ

You can run the [MoneyTransferReference](src/moneyTransfer/MoneyTransferReference.tla) specification with IntelliJ, and it requires the TLA+ plug-in.

You have to specify the location of tlapm modules and Community Modules to run the specification:
> -DTLA-Library=/usr/local/lib/tlaps:`<Community Modules source parent directory>`/CommunityModules/modules