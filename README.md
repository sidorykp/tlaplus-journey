# tlaplus-journey
TLA+ algorithms with TLAPS proofs

# [MoneyTransfer](src/moneyTransfer/MoneyTransfer.tla)
A simple (but not trivial) algorithm modeling money transfer between accounts.

What makes the algorithm non-trivial:
1. It is **fault-tolerant**.
1. It models any number of accounts and money transfers.
1. It is **fully proved** using the TLA+ Proof System (TLAPS).
1. The main invariant that is proved is a **global invariant**: the global amount of money present in the model.
1. It requires atomic operations on individual entities only (neither distributed transactions nor multi-row transaction are required)

# MoneyTransfer Proof

The inductive invariant IndInv is defined in the MoneyTransfer module. The main goal of the proof is to prove that IndInv is:
1. true in the initial state Init
1. maintained in all state transitions: init, debit, crash, credit

IndInv contains condition **"Imbalance = 0"**, which means that total amount of money modeled by the algorithm does not change when the algorithm is being executed.

Proving that "Imbalance = 0" is always true is the **ultimate goal** of the proof.

## Proof by proving a derived algorithm first

IndInv cannot be proved directly at this moment with TLAPS. And it was proved anyway by:
1. Creating an [equivalent algorithm](src/moneyTransfer/MoneyTransferPendingExplicit.tla) that has some state duplication:
   1. has one more variable: "pendingTrans"
   2. its "credits" and "debits" records (variables) have one more attribute: "amount"
   3. "pendingTrans" and "amount" can be derived from the original algorithm
   4. its IndInv has all IndInv constraints including "Imbalance = 0", and has additional constraints
1. [Proving](src/moneyTransfer/MoneyTransferPendingExplicit_proofs.tla) IndInv of the equivalent algorithm:
>THEOREM IndInvPreserved == Spec => []IndInv
3. [Proving](src/moneyTransfer/MoneyTransferEquivalence.tla) that the equivalent algorithm is identical to the original algorithm when additional state is derived from the original algorithm:
>E == INSTANCE MoneyTransferPendingExplicit 
> 
>WITH pendingTrans <- pendingTransE, credits <- creditsDerived, debits <- debitsDerived

The proof contains evidence that the equivalent algorithm implements identical specification when additional state is derived:
>THEOREM specEquivalence == E!Spec <=> SpecE

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