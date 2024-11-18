----MODULE MoneyTransferEquivalence----
EXTENDS MoneyTransfer

VARIABLE pendingTransE

pendingTransDerived == {<<t, amount[t]>>: t \in {t \in Transfer: AmountIsPending(t)}}

varsE == <<vars, pendingTransE>>

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

THEOREM E!Spec <=> SpecE

THEOREM E!Init <=> InitE
BY EquivalentSymbolsAssumption DEF E!Init, InitE, Init, pendingTransDerived,
    pcLabels, E!ProcSet, ProcSet,
    AmountIsPending, creditPrecond, isTransKnown, isTransKnownToItem


THEOREM unchangedVarsProperty == E!IndInv /\ UNCHANGED E!vars => E!IndInv'
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