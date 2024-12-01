----MODULE MoneyTransferEquivalence----
EXTENDS MoneyTransfer, TLAPS

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

E == INSTANCE MoneyTransferPendingExplicit WITH pendingTrans <- pendingTransE

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
BY DEF E!init, initE, pendingTransDerived,
    pcLabels, E!ProcSet, ProcSet,
    AmountIsPending, creditPrecond

THEOREM debitEquivalence == ASSUME NEW self \in Transfer, E!debit(self)
PROVE debitE(self)
BY DEF E!debit, debitE, pendingTransDerived,
    pcLabels, E!ProcSet, ProcSet, E!debitPrecond,
    AmountIsPending, creditPrecond, isTransKnown, isTransKnownToItem

THEOREM debitEquivalenceRev == ASSUME NEW self \in Transfer, debitE(self)
PROVE E!debit(self)
BY DEF E!debit, debitE, pendingTransDerived,
    pcLabels, E!ProcSet, ProcSet, E!debitPrecond,
    AmountIsPending, creditPrecond, isTransKnown, isTransKnownToItem
    
THEOREM crashEquivalence == ASSUME NEW self \in Transfer, E!crash(self)
PROVE crashE(self)
BY DEF E!crash, crashE, pendingTransDerived,
    pcLabels, E!ProcSet, ProcSet,
    AmountIsPending, creditPrecond
    
THEOREM crashEquivalenceRev == ASSUME NEW self \in Transfer, crashE(self)
PROVE E!crash(self)
BY DEF E!crash, crashE, pendingTransDerived,
    pcLabels, E!ProcSet, ProcSet,
    AmountIsPending, creditPrecond, isTransKnown, isTransKnownToItem

THEOREM creditEquivalence == ASSUME NEW self \in Transfer, E!credit(self)
PROVE creditE(self)
<1>1 credit(self) BY DEF E!credit, creditE
<1>2 pendingTransE' = pendingTransDerived'
    <2>1 CASE E!creditPrecond(self)
        <3> QED BY <2>1 DEF E!credit, pendingTransDerived,
            pcLabels, E!ProcSet, ProcSet
    <2>2 CASE ~E!creditPrecond(self)
        <3>1 UNCHANGED <<credits, pendingTransE>> BY <2>2 DEF E!credit
        <3> QED BY <2>2, <3>1 DEF E!credit, pendingTransDerived,
            pcLabels, E!ProcSet, ProcSet,
            AmountIsPending, creditPrecond, isTransKnown, isTransKnownToItem
    <2> QED BY <2>1, <2>2
<1> QED BY <1>1, <1>2 DEF creditE

THEOREM creditEquivalenceRev == ASSUME NEW self \in Transfer, creditE(self)
PROVE E!credit(self)
BY DEF E!credit, creditE, credit, pendingTransDerived,
    pcLabels, E!ProcSet, ProcSet
    
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


\* proved in MoneyTransferPendingExplicit_proofs
THEOREM IndInvPreservedE == E!Spec => []E!IndInv OMITTED

\* proved in MoneyTransfer_proofs
THEOREM IndInvPreserved == Spec => []IndInv

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


THEOREM initEProperty == ASSUME InitE PROVE IndInv
BY initProperty DEF InitE

THEOREM initE_IndInv == ASSUME IndInv, NEW self \in Transfer, initE(self)
PROVE IndInv'
BY init_IndInv DEF initE

THEOREM crashE_IndInv == ASSUME IndInv, NEW self \in Transfer, crashE(self)
PROVE IndInv'
BY crash_IndInv DEF crashE

THEOREM debitE_IndInv == ASSUME IndInv, NEW self \in Transfer, debitE(self)
PROVE IndInv'
BY debit_IndInv DEF debitE

THEOREM creditE_IndInv == ASSUME IndInv, NEW self \in Transfer, creditE(self)
PROVE IndInv'
BY credit_IndInv DEF creditE

THEOREM nextNonTerminatingE == ASSUME IndInv, NextE, ~TerminatingE
PROVE IndInv'
<1> SUFFICES ASSUME IndInv, NEW self \in Transfer, transE(self)
    PROVE IndInv'
    BY DEF NextE, transE
<1>1 CASE initE(self) BY <1>1, initE_IndInv
<1>2 CASE debitE(self) BY <1>2, debitE_IndInv
<1>3 CASE crashE(self) BY <1>3, crashE_IndInv
<1>4 CASE creditE(self) BY <1>4, creditE_IndInv
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

THEOREM IndInvPreservedEE == SpecE => []IndInv
<1>1 IndInv /\ UNCHANGED varsE => IndInv'
    BY unchangedVarsPropertyE
<1> QED BY PTL, initEProperty, nextPropertyE, <1>1 DEF SpecE


THEOREM DebitTotalEquivalence == E!DebitTotal = DebitTotal
BY DEF E!DebitTotal, DebitTotal,
    E!MapThenSumSetE, E!MapThenFoldSetE, MapThenSumSet, MapThenFoldSet,
    E!opAmount, opAmount

THEOREM CreditTotalEquivalence == E!CreditTotal = CreditTotal
BY DEF E!CreditTotal, CreditTotal,
    E!MapThenSumSetE, E!MapThenFoldSetE, MapThenSumSet, MapThenFoldSet,
    E!opAmount, opAmount

THEOREM imbalanceByComponents == ASSUME E!DebitTotal = DebitTotal,
    E!CreditTotal = CreditTotal,
    E!Imbalance = Imbalance
PROVE E!AmountPendingTotal = AmountPendingTotal
<1>1 E!CreditTotal - E!DebitTotal = CreditTotal - DebitTotal OBVIOUS
<1>2 (E!CreditTotal - E!DebitTotal) + E!AmountPendingTotal
    = (CreditTotal - DebitTotal) + AmountPendingTotal BY DEF E!Imbalance, Imbalance
<1>10 E!CreditTotal \in Nat OMITTED
<1>11 E!DebitTotal \in Nat OMITTED
<1>12 E!AmountPendingTotal \in Nat OMITTED
<1>20 CreditTotal \in Nat OMITTED
<1>21 DebitTotal \in Nat OMITTED
<1>22 AmountPendingTotal \in Nat OMITTED
<1> QED BY <1>2,
    <1>10, <1>11, <1>12, <1>20, <1>21, <1>22
    
THEOREM SpecE => E!AmountPendingTotal = AmountPendingTotal
<1> SUFFICES ASSUME SpecE PROVE E!AmountPendingTotal = AmountPendingTotal
    OBVIOUS
<1>1 Imbalance = 0 BY PTL, IndInvPreservedEE DEF IndInv
<1>2 E!Imbalance = 0 BY PTL, IndInvPreservedE, specEquivalence DEF E!IndInv
<1>3 E!Imbalance = Imbalance BY <1>1, <1>2
<1> QED BY <1>3, DebitTotalEquivalence, CreditTotalEquivalence, imbalanceByComponents
    DEF E!Imbalance, Imbalance


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