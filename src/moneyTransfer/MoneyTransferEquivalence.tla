----MODULE MoneyTransferEquivalence----
EXTENDS MoneyTransfer, TLAPS, FiniteSetsExt_theorems, FiniteSetTheorems

VARIABLE pendingTransE

pendingTransDerived == {<<t, amount[t]>>: t \in {t \in Transfer: AmountIsPending(t)}}

varsE == <<credits, debits, amount, accounts, pc, pendingTransE>>

InitE == Init /\ pendingTransE = pendingTransDerived

initE(self) == init(self) /\ pendingTransE' = pendingTransDerived'

debitE(self) == debit(self) /\ pendingTransE' = pendingTransDerived'

crashE(self) == crash(self) /\ pendingTransE' = pendingTransDerived'

creditE(self) == credit(self) /\ pendingTransE' = pendingTransDerived'

transE(self) == initE(self) \/ debitE(self) \/ crashE(self) \/ creditE(self)

TerminatingE == /\ \A self \in ProcSet: pc[self] = "Done"
                /\ UNCHANGED varsE

NextE == (\E self \in Transfer: transE(self))
         \/ TerminatingE

SpecE == InitE /\ [][NextE]_varsE

IndInvE == IndInv /\ pendingTransE = pendingTransDerived

IndSpecE == IndInvE /\ [][NextE]_varsE

E == INSTANCE MoneyTransferPendingExplicit WITH pendingTrans <- pendingTransDerived

ASSUME EquivalentSymbolsAssumption ==
    /\ EmptyAccounts = E!EmptyAccounts

THEOREM InitEquivalence == E!Init <=> InitE
BY EquivalentSymbolsAssumption DEF E!Init, InitE, Init, pendingTransDerived,
    pcLabels, E!ProcSet, ProcSet,
    AmountIsPending, creditPrecond, isTransKnown, isTransKnownToItem

THEOREM initEquivalence == ASSUME NEW self \in Transfer, E!init(self)
PROVE initE(self)
BY DEF E!init, initE, pendingTransDerived,
    pcLabels, E!ProcSet, ProcSet,
    AmountIsPending, creditPrecond

THEOREM initEquivalenceRev == ASSUME NEW self \in Transfer, initE(self)
PROVE E!init(self)
BY DEF E!init, initE, init, pendingTransDerived,
    pcLabels, E!ProcSet, ProcSet,
    AmountIsPending

THEOREM debitEquivalence == ASSUME NEW self \in Transfer, E!debit(self)
PROVE debitE(self)
BY DEF E!debit, debitE, pendingTransDerived,
    pcLabels, E!ProcSet, ProcSet, E!debitPrecond,
    AmountIsPending, creditPrecond, isTransKnown, isTransKnownToItem

THEOREM debitEquivalenceRev == ASSUME NEW self \in Transfer, debitE(self)
PROVE E!debit(self)
BY DEF E!debit, debitE, debit, pendingTransDerived,
    pcLabels, E!ProcSet, ProcSet, E!debitPrecond, AmountIsPending
    
THEOREM crashEquivalence == ASSUME NEW self \in Transfer, E!crash(self)
PROVE crashE(self)
BY DEF E!crash, crashE, pendingTransDerived,
    pcLabels, E!ProcSet, ProcSet,
    AmountIsPending, creditPrecond
    
THEOREM crashEquivalenceRev == ASSUME NEW self \in Transfer, crashE(self)
PROVE E!crash(self)
BY DEF E!crash, crashE, crash, pendingTransDerived,
    pcLabels, E!ProcSet, ProcSet,
    AmountIsPending, creditPrecond

THEOREM creditEquivalence == ASSUME NEW self \in Transfer, E!credit(self)
PROVE creditE(self)
<1>1 credit(self) BY DEF E!credit, creditE
<1>2 pendingTransE' = pendingTransDerived'
    <2>1 CASE E!creditPrecond(self)
        <3> QED BY <2>1 DEF E!credit, pendingTransDerived,
            pcLabels, E!ProcSet, ProcSet
    <2>2 CASE ~E!creditPrecond(self)
        <3>1 UNCHANGED <<credits, pendingTransE>> BY <2>2 DEF E!credit
        <3>2 UNCHANGED <<debits, amount, accounts>> BY <2>2 DEF E!credit
        <3>3 pc' = [pc EXCEPT ![self] = "Done"] BY <2>2 DEF E!credit
        <3> QED BY <2>2, <3>1, <3>2, <3>3 DEF pendingTransDerived,
            pcLabels, E!ProcSet, ProcSet,
            AmountIsPending, creditPrecond, isTransKnown, isTransKnownToItem
    <2> QED BY <2>1, <2>2
<1> QED BY <1>1, <1>2 DEF creditE

THEOREM creditEquivalenceRev == ASSUME NEW self \in Transfer, creditE(self)
PROVE E!credit(self)
BY DEF E!credit, creditE, credit, pendingTransDerived,
    pcLabels, E!ProcSet, ProcSet, E!creditPrecond, AmountIsPending
    
THEOREM transEquivalence == ASSUME NEW self \in Transfer, E!trans(self)
PROVE transE(self)
<1>1 CASE E!init(self) BY <1>1, initEquivalence DEF E!trans, transE
<1>2 CASE E!debit(self) BY <1>2, debitEquivalence DEF E!trans, transE
<1>3 CASE E!crash(self) BY <1>3, crashEquivalence DEF E!trans, transE
<1>4 CASE E!credit(self) BY <1>4, creditEquivalence DEF E!trans, transE
<1> QED BY <1>1, <1>2, <1>3, <1>4
    DEF E!trans

THEOREM transEquivalenceRev == ASSUME NEW self \in Transfer, transE(self)
PROVE E!trans(self)
<1>1 CASE initE(self) BY <1>1, initEquivalenceRev DEF E!trans, transE
<1>2 CASE debitE(self) BY <1>2, debitEquivalenceRev DEF E!trans, transE
<1>3 CASE crashE(self) BY <1>3, crashEquivalenceRev DEF E!trans, transE
<1>4 CASE creditE(self) BY <1>4, creditEquivalenceRev DEF E!trans, transE
<1> QED BY <1>1, <1>2, <1>3, <1>4
    DEF transE

THEOREM unchangedEquivalence == UNCHANGED E!vars <=> UNCHANGED varsE
BY DEF E!vars, vars, varsE

THEOREM terminatingEquivalence == E!Terminating <=> TerminatingE
BY unchangedEquivalence DEF E!Terminating, TerminatingE,
    E!ProcSet, ProcSet
    
THEOREM nextEquivalence == E!Next <=> NextE
BY transEquivalence, transEquivalenceRev, terminatingEquivalence
    DEF E!Next, NextE

THEOREM specEquivalence == E!Spec <=> SpecE
BY PTL, nextEquivalence, InitEquivalence, unchangedEquivalence
    DEF E!Spec, SpecE,
    E!vars, vars, varsE


PendingTransInv == pendingTransE = pendingTransDerived

THEOREM pendingTransInit == ASSUME InitE PROVE PendingTransInv
BY DEF PendingTransInv, InitE

THEOREM pendingTransTrans == ASSUME NEW self \in Transfer, transE(self),
PendingTransInv
PROVE PendingTransInv'
BY DEF PendingTransInv, transE, initE, debitE, crashE, creditE

THEOREM pendingTransUnchanged == PendingTransInv /\ UNCHANGED varsE => PendingTransInv'
<1> SUFFICES ASSUME PendingTransInv, UNCHANGED varsE PROVE PendingTransInv' OBVIOUS
<1> QED BY DEF PendingTransInv, varsE,
    pendingTransDerived, AmountIsPending, creditPrecond,
    isTransKnown, isTransKnownToItem

THEOREM pendingTransNext == PendingTransInv /\ NextE => PendingTransInv'
<1> SUFFICES ASSUME PendingTransInv, NextE
    PROVE PendingTransInv'
    OBVIOUS
<1> USE DEF PendingTransInv, NextE, TerminatingE
<1>1 CASE ~TerminatingE
    <2> QED BY <1>1, pendingTransTrans
<1>2 CASE TerminatingE
    <2>1 UNCHANGED varsE BY <1>2 DEF TerminatingE
    <2> QED BY <1>2, <2>1, pendingTransUnchanged
<1> QED BY <1>1, <1>2

THEOREM PendingTransInvPreserved == SpecE => []PendingTransInv
<1>1 PendingTransInv /\ UNCHANGED varsE => PendingTransInv'
    BY pendingTransUnchanged
<1> QED BY PTL, pendingTransInit, pendingTransNext, <1>1 DEF SpecE


CONSTANTS NTransfer

ASSUME NTransferAssumption == NTransfer \in NNat

ASSUME TransferAssumption == Transfer = 1..NTransfer

\* proved in MoneyTransferPendingExplicit_proofs
THEOREM IndInvPreservedE == E!Spec => []E!IndInv OMITTED

\* proved in MoneyTransferPendingExplicit_proofs
LEMMA AmountPendingTotalInNat == ASSUME NTransferAssumption, E!IndInv
PROVE E!AmountPendingTotal \in Nat OMITTED

\* proved in MoneyTransfer_proofs: begin
THEOREM initProperty == ASSUME Init PROVE IndInv

THEOREM init_IndInv == ASSUME IndInv, NEW self \in Transfer, init(self)
PROVE IndInv'

THEOREM crash_IndInv == ASSUME IndInv, NEW self \in Transfer, crash(self)
PROVE IndInv'

THEOREM debit_IndInv == ASSUME IndInv, NEW self \in Transfer, debit(self)
PROVE IndInv'

THEOREM credit_IndInv == ASSUME IndInv, NEW self \in Transfer, credit(self)
PROVE IndInv'

THEOREM unchangedVarsProperty == IndInv /\ UNCHANGED vars => IndInv'
\* proved in MoneyTransfer_proofs: end

THEOREM initEProperty == ASSUME InitE PROVE IndInv
BY initProperty DEF InitE

THEOREM nextNonTerminatingE == ASSUME IndInv, NextE, ~TerminatingE
PROVE IndInv'
<1> SUFFICES ASSUME IndInv, NEW self \in Transfer, transE(self)
    PROVE IndInv'
    BY DEF NextE, transE
<1>1 CASE initE(self) BY <1>1, init_IndInv DEF initE
<1>2 CASE debitE(self) BY <1>2, debit_IndInv DEF debitE
<1>3 CASE crashE(self) BY <1>3, crash_IndInv DEF crashE
<1>4 CASE creditE(self) BY <1>4, credit_IndInv DEF creditE
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF transE

THEOREM unchangedVarsPropertyE == IndInv /\ UNCHANGED varsE => IndInv'
<1> SUFFICES ASSUME IndInv, UNCHANGED varsE
    PROVE IndInv'
    OBVIOUS
<1> QED BY unchangedVarsProperty DEF varsE, vars

THEOREM nextTerminatingE == ASSUME IndInv, NextE, TerminatingE
PROVE IndInv'
<1> SUFFICES ASSUME IndInv, TerminatingE
    PROVE IndInv'
    BY DEF NextE, TerminatingE
<1>1 UNCHANGED varsE BY DEF TerminatingE
<1> QED BY <1>1, unchangedVarsPropertyE

THEOREM nextPropertyE == IndInv /\ NextE => IndInv'
<1> SUFFICES ASSUME IndInv, NextE
    PROVE IndInv'
    OBVIOUS
<1> USE DEF IndInv, NextE, TerminatingE
<1>1 CASE ~TerminatingE
    <2> QED BY <1>1, nextNonTerminatingE
<1>2 CASE TerminatingE
    <2> QED BY <1>2, nextTerminatingE    
<1> QED BY <1>1, <1>2

THEOREM IndInvPreservedEE == SpecE => [](IndInv /\ E!IndInv)
<1>1 IndInv /\ UNCHANGED varsE => IndInv'
    BY unchangedVarsPropertyE
<1>2 SpecE => []E!IndInv BY IndInvPreservedE, specEquivalence
<1>3 SpecE => []IndInv BY PTL, initEProperty, nextPropertyE, <1>1 DEF SpecE
<1> QED BY <1>2, <1>3


THEOREM DebitTotalEquivalence == E!DebitTotal = DebitTotal
BY DEF E!DebitTotal, DebitTotal,
    E!MapThenSumSetE, E!MapThenFoldSetE, MapThenSumSet, MapThenFoldSet,
    E!opAmount, opAmount

THEOREM CreditTotalEquivalence == E!CreditTotal = CreditTotal
BY DEF E!CreditTotal, CreditTotal,
    E!MapThenSumSetE, E!MapThenFoldSetE, MapThenSumSet, MapThenFoldSet,
    E!opAmount, opAmount
    
LEMMA transPendingAmountNat == ASSUME IndInv
PROVE \A am \in transPending: transAmount(am) \in Nat
BY DEF AmountIsPending, isTransKnown, transAmount, transPending, IndInv, TypeOK

LEMMA transSetIsFinite == ASSUME NTransferAssumption
PROVE IsFiniteSet(Transfer)
<1>1 Transfer \in SUBSET (Nat) BY TransferAssumption
<1>2 \A t \in Transfer: t <= NTransfer BY TransferAssumption
<1> QED BY <1>1, <1>2, FS_BoundedSetOfNaturals DEF NNat

LEMMA transPendingIsFinite == IsFiniteSet(transPending)
BY transSetIsFinite, FS_Subset, NTransferAssumption DEF transPending

LEMMA pendingTransAmountInNat == ASSUME E!TypeOK, NEW self \in E!TN
PROVE E!pendingTransAmount(self) \in Nat
BY DEF E!TypeOK, E!pendingTransAmount, E!TN

THEOREM imbalanceByComponents == ASSUME
    pendingTransE = pendingTransDerived,
    E!DebitTotal = DebitTotal,
    IndInv, E!IndInv,
    E!CreditTotal = CreditTotal,
    E!Imbalance = 0,
    Imbalance = 0
PROVE E!AmountPendingTotal = AmountPendingTotal
<1>1 (E!CreditTotal - E!DebitTotal) + E!AmountPendingTotal
    = (CreditTotal - DebitTotal) + AmountPendingTotal BY DEF E!Imbalance, Imbalance
<1>2 DebitTotal \in Nat
    <2>1 \A d \in debits: opAmount(d) \in Nat BY DEF opAmount, IndInv, TypeOK
    <2> QED BY <2>1, MapThenSumSetType DEF DebitTotal, IndInv, TypeOK
<1>3 E!AmountPendingTotal \in Nat BY AmountPendingTotalInNat, NTransferAssumption
<1>4 CreditTotal \in Nat
    <2>1 \A c \in credits: opAmount(c) \in Nat BY DEF opAmount, IndInv, TypeOK
    <2> QED BY <2>1, MapThenSumSetType DEF CreditTotal, IndInv, TypeOK
<1>5 AmountPendingTotal \in Nat BY transPendingAmountNat, transPendingIsFinite, MapThenSumSetType DEF AmountPendingTotal
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5
    
THEOREM SpecE => E!AmountPendingTotal = AmountPendingTotal
<1> SUFFICES ASSUME SpecE PROVE E!AmountPendingTotal = AmountPendingTotal
    OBVIOUS
<1>1 Imbalance = 0 BY PTL, IndInvPreservedEE DEF IndInv
<1>2 E!Imbalance = 0 BY PTL, IndInvPreservedE, specEquivalence DEF E!IndInv
<1>3 IndInv BY PTL, IndInvPreservedEE
<1>4 pendingTransE = pendingTransDerived BY PTL, PendingTransInvPreserved DEF PendingTransInv
<1>5 E!IndInv BY PTL, IndInvPreservedE, specEquivalence
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, DebitTotalEquivalence, CreditTotalEquivalence, imbalanceByComponents

THEOREM SpecE => [](E!AmountPendingTotal = AmountPendingTotal)
<1>1 SpecE => [](E!Imbalance = 0 /\ Imbalance = 0) BY PTL, IndInvPreservedE, IndInvPreservedEE,
    specEquivalence DEF E!IndInv, IndInv
<1>2 SpecE => []IndInv BY IndInvPreservedEE
<1>3 SpecE => [](pendingTransE = pendingTransDerived) BY PendingTransInvPreserved DEF PendingTransInv
<1>4 SpecE => []E!IndInv BY IndInvPreservedE, specEquivalence
<1> QED BY PTL, <1>1, <1>2, <1>3, <1>4,
    DebitTotalEquivalence, CreditTotalEquivalence, imbalanceByComponents


THEOREM E!IndInv /\ UNCHANGED E!vars => E!IndInv'
<1> SUFFICES ASSUME E!IndInv, UNCHANGED E!vars
    PROVE E!IndInv'
    OBVIOUS
<1> USE DEF E!vars
<1>1 E!TypeOK' = E!TypeOK BY DEF E!TypeOK, E!pcLabels,
    E!TransPendingEquivalence, E!TransInPendingTrans, E!AmountIsPending, E!creditPrecond,
    E!PendingTransDerived, E!PendingTransUniqueness
<1>2 (/\ \A t \in Transfer:
        \/ accounts[t] = E!EmptyAccounts
        \/ E!DifferentAccounts(t) /\ E!NonEmptyAccounts(t))' =
      /\ \A t \in Transfer:
        \/ accounts[t] = E!EmptyAccounts
        \/ E!DifferentAccounts(t) /\ E!NonEmptyAccounts(t)
    BY DEF E!DifferentAccounts, E!NonEmptyAccounts
<1>3 (/\ \A t \in Transfer: pc[t] = "init" => E!initPrecond(t))' =
    /\ \A t \in Transfer: pc[t] = "init" => E!initPrecond(t)
    BY DEF E!initPrecond
<1>4 (/\ \A t \in Transfer:
        pc[t] \notin {"init"} <=> E!NonEmptyAccounts(t))' =
      /\ \A t \in Transfer:
        pc[t] \notin {"init"} <=> E!NonEmptyAccounts(t)
    BY DEF E!NonEmptyAccounts
<1>5 E!CreditTotal' = E!CreditTotal BY DEF E!CreditTotal
<1>6 E!DebitTotal' = E!DebitTotal BY DEF E!DebitTotal
<1>7 E!AmountPendingTotal' = E!AmountPendingTotal BY DEF E!AmountPendingTotal

<1>8 (E!Imbalance = 0)' = (E!Imbalance = 0) BY <1>5, <1>6, <1>7 DEF E!Imbalance

<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>8 DEF E!IndInv


====