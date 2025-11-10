---- MODULE MoneyTransferReference_proofs ----
EXTENDS MoneyTransferReference, MoneyTransfer_proofsCommon, TLAPS

THEOREM InitProperty == ASSUME Init PROVE IndInv
<1> USE DEF Init, IndInv, StateConstraints, TypeOK
<1>1 TypeOK
    <2>1 accounts \in [Transfer -> EAccounts] BY DEF EmptyAccounts, EAccounts, EAccount
    <2>2 pcLabels BY DEF ProcSet, pcLabels
    <2> QED BY <2>1, <2>2
<1>2 MoneyConstant
    BY DEF MoneyConstant, moneyConstantForTrans, debitAmount, pendingAmount, creditAmount
<1>3 TransfersIndivisible
    BY DEF TransfersIndivisible, transferIndivisible, AmountIsPending,
        creditPrecond, isTransKnown, EmptyAccounts, EAccounts, EAccount
<1>4 \A t \in Transfer: accounts[t] = EmptyAccounts \/ DifferentAccounts(t)
    BY DEF EmptyAccounts, DifferentAccounts
<1>5 \A t \in Transfer: pc[t] \in {"choose_accounts", "choose_amount"} => debitPrecond(t)
    BY DEF debitPrecond, isTransKnown, EmptyAccounts, EAccounts, EAccount
<1>6 \A t \in Transfer: pc[t] \notin {"choose_accounts"} => NonEmptyAccounts(t)
    <2>1 \A t \in Transfer: pc[t] \in {"choose_accounts"} BY DEF ProcSet
    <2> QED BY <2>1 DEF NonEmptyAccounts, EmptyAccounts
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6

LEMMA stateConstraints == ASSUME IndInv, NEW self \in Transfer,
    \/ choose_accounts(self)
    \/ choose_amount(self)
    \/ debit(self)
    \/ retryDebit(self)
    \/ credit(self)
    \/ retryCredit(self)
PROVE StateConstraints'
<1> USE DEF IndInv, StateConstraints, TypeOK,
    choose_accounts, choose_amount, debit, retryDebit, credit, retryCredit
<1>1 \A t \in Transfer: (accounts[t] = EmptyAccounts \/ DifferentAccounts(t))'
    BY DEF DifferentAccounts, EmptyAccounts, EAccounts, EAccount
<1>2 \A t \in Transfer: (pc[t] \in {"choose_accounts", "choose_amount"} => debitPrecond(t))'
    BY DEF pcLabels, debitPrecond, isTransKnown, EmptyAccounts, EAccounts, EAccount
<1>3 \A t \in Transfer: (pc[t] \notin {"choose_accounts"} => NonEmptyAccounts(t))'
    <2> USE DEF pcLabels, NonEmptyAccounts
    <2>1 (pc[self] \notin {"choose_accounts"} => NonEmptyAccounts(self))'
        <3>1 (accounts[self].from)' # Empty BY EmptyAssumption, AccountAssumption
        <3>2 (accounts[self].to)' # Empty BY EmptyAssumption, AccountAssumption
        <3>3 NonEmptyAccounts(self)'
            BY <3>1, <3>2
        <3> QED BY <3>3
    <2> QED BY <2>1
<1> QED BY <1>1, <1>2, <1>3

LEMMA otherTransfers_moneyConstantForTrans == ASSUME IndInv, NEW self \in Transfer,
    NEW t \in Transfer \ {self},
    \/ choose_accounts(self)
    \/ choose_amount(self)
    \/ retryDebit(self)
    \/ retryCredit(self)
PROVE moneyConstantForTrans(t)' = moneyConstantForTrans(t)
<1> USE DEF choose_accounts, choose_amount, retryDebit, retryCredit, IndInv, StateConstraints, TypeOK,
     debitAmount, pendingAmount, creditAmount, moneyConstantForTrans
<1>1 pc[t]' = pc[t] BY DEF pcLabels
<1>2 creditPrecond(t)' = creditPrecond(t) BY DEF creditPrecond
<1>3 pendingAmount(t)' = pendingAmount(t)
    BY <1>1, <1>2 DEF AmountIsPending
<1> QED BY <1>3

THEOREM choose_accounts_IndInv == ASSUME IndInv, NEW self \in Transfer, choose_accounts(self)
PROVE IndInv'
<1> USE DEF choose_accounts, IndInv, StateConstraints, TypeOK
<1>1 TypeOK'
    <2>1 accounts' \in [Transfer -> EAccounts] BY DEF EmptyAccounts, EAccounts, EAccount
    <2>2 pcLabels' BY DEF pcLabels
    <2> QED BY <2>1, <2>2
<1>2 MoneyConstant'
    <2> USE DEF MoneyConstant, debitAmount, pendingAmount, creditAmount, moneyConstantForTrans
    <2>1 moneyConstantForTrans(self)'
        <3>1 ~(self \in debits[accounts[self].from])' BY DEF debitPrecond, isTransKnown
        <3>2 debitAmount(self)' = 0 BY <3>1
        <3>3 ~(self \in credits[accounts[self].to])' BY DEF debitPrecond, isTransKnown
        <3>4 creditAmount(self)' = 0 BY <3>3
        <3>5 ~(AmountIsPending(self))' BY DEF AmountIsPending, creditPrecond, debitPrecond, isTransKnown
        <3>6 pendingAmount(self)' = 0 BY <3>5
        <3> QED BY <3>2, <3>3, <3>6
    <2>2 ASSUME NEW t \in Transfer \ {self} PROVE moneyConstantForTrans(t)' = moneyConstantForTrans(t)
        BY otherTransfers_moneyConstantForTrans
    <2> QED BY <2>1, <2>2
<1>3 StateConstraints' BY stateConstraints
<1> QED BY <1>1, <1>2, <1>3

THEOREM choose_amount_IndInv == ASSUME IndInv, NEW self \in Transfer, choose_amount(self)
PROVE IndInv'
<1> USE DEF choose_amount, IndInv, StateConstraints, TypeOK
<1>1 TypeOK' BY DEF pcLabels
<1>2 MoneyConstant'
    <2> USE DEF MoneyConstant, debitAmount, pendingAmount, creditAmount, moneyConstantForTrans
    <2>1 moneyConstantForTrans(self)'
        <3>1 accounts[self].from \in Account BY DEF NonEmptyAccounts, EmptyAccounts, EAccounts, EAccount
        <3>2 ~(self \in debits[accounts[self].from])' BY <3>1 DEF debitPrecond, isTransKnown
        <3>3 debitAmount(self)' = 0 BY <3>2
        <3>4 accounts[self].to \in Account BY DEF NonEmptyAccounts, EmptyAccounts, EAccounts, EAccount
        <3>5 ~(self \in credits[accounts[self].to])' BY <3>4 DEF debitPrecond, isTransKnown
        <3>6 creditAmount(self)' = 0 BY <3>5
        <3>7 ~(AmountIsPending(self))' BY <3>1 DEF AmountIsPending, creditPrecond, debitPrecond, isTransKnown
        <3>8 pendingAmount(self)' = 0 BY <3>7
        <3> QED BY <3>3, <3>5, <3>8
    <2>2 ASSUME NEW t \in Transfer \ {self} PROVE moneyConstantForTrans(t)' = moneyConstantForTrans(t)
        BY otherTransfers_moneyConstantForTrans
    <2> QED BY <2>1, <2>2
<1>3 StateConstraints' BY stateConstraints
<1> QED BY <1>1, <1>2, <1>3

THEOREM debit_IndInv == ASSUME IndInv, NEW self \in Transfer, debit(self)
PROVE IndInv'
<1> USE DEF debit, IndInv, StateConstraints, TypeOK
<1> DEFINE accountFrom == accounts[self].from
<1> DEFINE accountTo == accounts[self].to
<1>1 TypeOK' BY DEF pcLabels
<1>2 MoneyConstant'
    <2> USE DEF MoneyConstant, debitAmount, pendingAmount, creditAmount, moneyConstantForTrans
    <2>1 moneyConstantForTrans(self)'
        <3>1 CASE ~debitPrecond(self) \/ debits' = debits
            <4> QED BY <3>1 DEF AmountIsPending, creditPrecond, pcLabels
        <3>2 CASE debitPrecond(self) /\ debits' # debits
            <4>1 (debitAmount(self) = amount[self])'
                <5>1 (self \in debits[accountFrom])' BY <3>2
                <5> QED BY <5>1
            <4>2 accountTo \in Account BY DEF NonEmptyAccounts, EmptyAccounts, EAccounts, EAccount
            <4>3 (creditAmount(self) = 0)'
                <5>1 ~(self \in credits[accountTo])' BY <3>2, <4>2 DEF debitPrecond, isTransKnown
                <5> QED BY <5>1
            <4>4 (pendingAmount(self) = amount[self])'
                <5>1 ~(self \in debits[accountTo]) BY <3>2, <4>2 DEF debitPrecond, isTransKnown
                <5>2 accountTo # accountFrom BY DEF NonEmptyAccounts, DifferentAccounts, EmptyAccounts
                <5>3 debits[accountTo]' = debits[accountTo] BY <3>2, <4>2, <5>2 DEF EmptyAccounts, EAccounts, EAccount
                <5>4 ~(self \in debits[accountTo])' BY <5>1, <5>3
                <5> QED BY <3>2, <5>4 DEF
                    AmountIsPending, creditPrecond, debitPrecond, isTransKnown, pcLabels
            <4> QED BY <4>1, <4>3, <4>4
        <3> QED BY <3>1, <3>2
    <2>2 ASSUME NEW t \in Transfer \ {self} PROVE moneyConstantForTrans(t)' = moneyConstantForTrans(t)
        <3>1 (t \in debits[accountFrom])' <=> t \in debits[accountFrom] BY <2>2
        <3>2 debitAmount(t)' = debitAmount(t) BY <3>1 DEF EmptyAccounts, EAccounts, EAccount
        <3>3 creditAmount(t)' = creditAmount(t) BY <3>2
        <3>4 pendingAmount(t)' = pendingAmount(t) BY <3>2 DEF
            AmountIsPending, EmptyAccounts, EAccounts, EAccount, creditPrecond, isTransKnown, pcLabels
        <3> QED BY <3>2, <3>3, <3>4
    <2> QED BY <2>1, <2>2
<1>3 StateConstraints' BY stateConstraints
<1> QED BY <1>1, <1>2, <1>3

THEOREM credit_IndInv == ASSUME IndInv, NEW self \in Transfer, credit(self)
PROVE IndInv'
<1> USE DEF credit, IndInv, StateConstraints, TypeOK
<1> DEFINE accountFrom == accounts[self].from
<1> DEFINE accountTo == accounts[self].to
<1>1 TypeOK' BY DEF pcLabels
<1>2 MoneyConstant'
    <2> USE DEF MoneyConstant, debitAmount, pendingAmount, creditAmount, moneyConstantForTrans
    <2>1 moneyConstantForTrans(self)'
        <3>1 CASE ~creditPrecond(self) \/ credits' = credits
            <4> QED BY <3>1 DEF AmountIsPending, creditPrecond, pcLabels
        <3>2 CASE creditPrecond(self) /\ credits' # credits
            <4>1 (creditAmount(self) = amount[self])'
                <5>1 (self \in credits[accountTo])' BY <3>2
                <5> QED BY <5>1
            <4>2 (debitAmount(self) = amount[self])'
                <5>1 (self \in debits[accountFrom])' BY <3>2 DEF creditPrecond, isTransKnown
                <5> QED BY <5>1
            <4>3 (pendingAmount(self) = 0)' BY <3>2 DEF NonEmptyAccounts,
                AmountIsPending, creditPrecond, isTransKnown, EmptyAccounts, EAccounts, EAccount
            <4> QED BY <4>1, <4>2, <4>3
        <3> QED BY <3>1, <3>2
    <2>2 ASSUME NEW t \in Transfer \ {self} PROVE moneyConstantForTrans(t)' = moneyConstantForTrans(t)
        <3>1 (t \in credits[accountTo])' <=> t \in credits[accountTo] BY <2>2
        <3>2 creditAmount(t)' = creditAmount(t) BY <3>1 DEF
            EmptyAccounts, EAccounts, EAccount
        <3>3 debitAmount(t)' = debitAmount(t) BY <2>2
        <3>4 pendingAmount(t)' = pendingAmount(t) BY <2>2 DEF
            AmountIsPending, EmptyAccounts, EAccounts, EAccount, creditPrecond, isTransKnown, pcLabels
        <3> QED BY <3>2, <3>3, <3>4
    <2> QED BY <2>1, <2>2
<1>3 StateConstraints' BY stateConstraints
<1> QED BY <1>1, <1>2, <1>3

THEOREM retryDebitCredit_IndInv == ASSUME IndInv, NEW self \in Transfer,
    \/ retryDebit(self)
    \/ retryCredit(self)
PROVE IndInv'
<1> USE DEF retryDebit, retryCredit, IndInv, StateConstraints, TypeOK
<1>1 TypeOK'
    <2>1 accounts' \in [Transfer -> EAccounts] BY DEF EmptyAccounts, EAccounts, EAccount
    <2>2 pcLabels' BY DEF pcLabels
    <2> QED BY <2>1, <2>2
<1>2 MoneyConstant'
    <2> USE DEF MoneyConstant, debitAmount, pendingAmount, creditAmount, moneyConstantForTrans
    <2>1 moneyConstantForTrans(self)'
        <3>1 AmountIsPending(self)' = AmountIsPending(self) BY DEF AmountIsPending, creditPrecond,
            isTransKnown, pcLabels
        <3>2 pendingAmount(self)' = pendingAmount(self) BY <3>1
        <3> QED BY <3>2
    <2>2 ASSUME NEW t \in Transfer \ {self} PROVE moneyConstantForTrans(t)' = moneyConstantForTrans(t)
        BY otherTransfers_moneyConstantForTrans
    <2> QED BY <2>1, <2>2
<1>3 StateConstraints' BY stateConstraints
<1> QED BY <1>1, <1>2, <1>3

THEOREM nextNonTerminating == ASSUME IndInv, NEW self \in Transfer, trans(self), ~Terminating
PROVE IndInv'
<1>1 CASE choose_accounts(self) BY <1>1, choose_accounts_IndInv
<1>2 CASE choose_amount(self) BY <1>2, choose_amount_IndInv
<1>3 CASE debit(self) BY <1>3, debit_IndInv
<1>4 CASE retryDebit(self) BY <1>4, retryDebitCredit_IndInv
<1>5 CASE credit(self) BY <1>5, credit_IndInv
<1>6 CASE retryCredit(self) BY <1>6, retryDebitCredit_IndInv
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF trans

THEOREM unchangedVarsProperty == ASSUME IndInv, UNCHANGED vars PROVE IndInv'
<1> USE DEF vars
<1>1 TypeOK' = TypeOK BY DEF TypeOK, pcLabels
<1>2 StateConstraints' = StateConstraints
    <2>1 (/\ \A t \in Transfer:
            \/ accounts[t] = EmptyAccounts
            \/ DifferentAccounts(t))' =
          /\ \A t \in Transfer:
            \/ accounts[t] = EmptyAccounts
            \/ DifferentAccounts(t)
        BY DEF DifferentAccounts, NonEmptyAccounts
    <2>2 (/\ \A t \in Transfer: pc[t] \in {"choose_accounts", "choose_amount"} => debitPrecond(t))' =
          /\ \A t \in Transfer: pc[t] \in {"choose_accounts", "choose_amount"} => debitPrecond(t)
        BY DEF debitPrecond
    <2>3 (/\ \A t \in Transfer:
            pc[t] \notin {"choose_accounts"} => NonEmptyAccounts(t))' =
          /\ \A t \in Transfer:
            pc[t] \notin {"choose_accounts"} => NonEmptyAccounts(t)
        BY DEF NonEmptyAccounts
    <2> QED BY <2>1, <2>2, <2>3 DEF StateConstraints
<1>3 MoneyConstant' = MoneyConstant
    BY DEF MoneyConstant, moneyConstantForTrans, debitAmount, pendingAmount, creditAmount,
        AmountIsPending, creditPrecond
<1> QED BY <1>1, <1>2, <1>3 DEF IndInv

THEOREM NextProperty == IndInv /\ Next => IndInv'
<1> USE DEF IndInv, Next, Terminating
<1>1 CASE ~Terminating
    <2> QED BY <1>1, nextNonTerminating
<1>2 CASE Terminating
    <2> QED BY <1>2, unchangedVarsProperty 
<1> QED BY <1>1, <1>2

THEOREM IndInvPreserved == Spec => []IndInv
<1>1 IndInv /\ UNCHANGED vars => IndInv'
    BY unchangedVarsProperty
<1> QED BY PTL, InitProperty, NextProperty, <1>1 DEF Spec

THEOREM ImplicationProperty == IndInv => Inv
BY DEF IndInv, Inv

THEOREM InvPreserved == Spec => []Inv
BY PTL, IndInvPreserved, ImplicationProperty
    
====