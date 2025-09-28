---- MODULE MoneyTransferReferenceLocal_proofs ----
EXTENDS MoneyTransferReference, MoneyTransfer_proofsCommon, TLAPS

THEOREM initProperty == ASSUME Init PROVE IndInv
<1> USE DEF Init, IndInv, StateConstraints, TypeOK
<1>1 TypeOK
    <2>1 accounts \in [Transfer -> EAccounts] BY DEF EmptyAccounts, EAccounts, EAccount
    <2>2 pcLabels BY DEF ProcSet, pcLabels
    <2> QED BY <2>1, <2>2
<1>2 MoneyConstant
    BY DEF MoneyConstant, moneyConstantForTrans, debitAmount, pendingAmount, creditAmount
<1>3 \A t \in Transfer: accounts[t] = EmptyAccounts \/ DifferentAccounts(t)
    BY DEF EmptyAccounts, DifferentAccounts
<1>4 \A t \in Transfer: pc[t] \in {"choose_accounts", "choose_amount"} => debitPrecond(t)
    BY DEF debitPrecond, isTransKnown
<1>5 \A t \in Transfer: pc[t] \notin {"choose_accounts"} => NonEmptyAccounts(t)
    <2>1 \A t \in Transfer: pc[t] \in {"choose_accounts"} BY DEF ProcSet
    <2> QED BY <2>1 DEF NonEmptyAccounts, EmptyAccounts
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5

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
    BY DEF pcLabels, debitPrecond, isTransKnown
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
<1>1 NonEmptyAccounts(t)' = NonEmptyAccounts(t)
    BY DEF NonEmptyAccounts
<1>2 debitAmount(t)' = debitAmount(t) BY <1>1
<1>3 creditAmount(t)' = creditAmount(t) BY <1>1
<1>4 pc[t]' = pc[t] BY DEF pcLabels
<1>5 creditPrecond(t)' = creditPrecond(t) BY DEF creditPrecond
<1>6 pendingAmount(t)' = pendingAmount(t)
    BY <1>1, <1>4, <1>5 DEF AmountIsPending
<1> QED BY <1>2, <1>3, <1>6

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
        <3>7 ~(AmountIsPending(self))' BY <3>1, <3>4 DEF AmountIsPending, creditPrecond, debitPrecond, isTransKnown
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
            <4>1 (self \in debits[accountFrom])' BY <3>2
            <4>2 (debitAmount(self) = amount[self])' BY <4>1 DEF NonEmptyAccounts
            <4>3 accountTo \in Account BY DEF NonEmptyAccounts, EmptyAccounts, EAccounts, EAccount
            <4>4 ~(self \in credits[accountTo])' BY <3>2, <4>3 DEF debitPrecond, isTransKnown
            <4>5 (creditAmount(self) = 0)' BY <4>4
            <4>6 ~(self \in debits[accountTo]) BY <3>2, <4>3 DEF debitPrecond, isTransKnown
            <4>7 accountTo # accountFrom BY DEF NonEmptyAccounts, DifferentAccounts, EmptyAccounts
            <4>8 debits[accountTo]' = debits[accountTo] BY <3>2, <4>3, <4>7
            <4>9 ~(self \in debits[accountTo])' BY <4>6, <4>8
            <4>10 (pendingAmount(self) = amount[self])' BY <3>2, <4>4, <4>9 DEF NonEmptyAccounts,
                AmountIsPending, creditPrecond, debitPrecond, isTransKnown, pcLabels
            <4> QED BY <4>2, <4>5, <4>10
        <3> QED BY <3>1, <3>2
    <2>2 ASSUME NEW t \in Transfer \ {self} PROVE moneyConstantForTrans(t)' = moneyConstantForTrans(t)
        <3>1 (t \in debits[accountFrom])' <=> t \in debits[accountFrom] BY <2>2
        <3>2 debitAmount(t)' = debitAmount(t) BY <3>1 DEF NonEmptyAccounts,
            EmptyAccounts, EAccounts, EAccount
        <3>3 creditAmount(t)' = creditAmount(t) BY <3>2 DEF NonEmptyAccounts
        <3>4 pendingAmount(t)' = pendingAmount(t) BY <3>2 DEF NonEmptyAccounts,
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
                <5> QED BY <5>1 DEF NonEmptyAccounts
            <4>2 (debitAmount(self) = amount[self])'
                <5>1 (self \in debits[accountFrom])' BY <3>2 DEF creditPrecond, isTransKnown
                <5> QED BY <5>1 DEF NonEmptyAccounts
            <4>3 (pendingAmount(self) = 0)' BY <3>2 DEF NonEmptyAccounts,
                AmountIsPending, creditPrecond, isTransKnown
            <4> QED BY <4>1, <4>2, <4>3
        <3> QED BY <3>1, <3>2
    <2>2 ASSUME NEW t \in Transfer \ {self} PROVE moneyConstantForTrans(t)' = moneyConstantForTrans(t)
        <3>1 (t \in credits[accountTo])' <=> t \in credits[accountTo] BY <2>2
        <3>2 creditAmount(t)' = creditAmount(t) BY <3>1 DEF NonEmptyAccounts,
            EmptyAccounts, EAccounts, EAccount
        <3>3 debitAmount(t)' = debitAmount(t) BY <2>2 DEF NonEmptyAccounts
        <3>4 pendingAmount(t)' = pendingAmount(t) BY <2>2 DEF NonEmptyAccounts,
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
        <3>1 debitAmount(self)' = debitAmount(self) BY DEF NonEmptyAccounts
        <3>2 creditAmount(self)' = creditAmount(self) BY DEF NonEmptyAccounts
        <3>3 (AmountIsPending(self))' = AmountIsPending(self) BY DEF AmountIsPending, creditPrecond, debitPrecond,
            isTransKnown, pcLabels
        <3>4 pendingAmount(self)' = pendingAmount(self) BY <3>3 DEF NonEmptyAccounts
        <3> QED BY <3>1, <3>2, <3>4
    <2>2 ASSUME NEW t \in Transfer \ {self} PROVE moneyConstantForTrans(t)' = moneyConstantForTrans(t)
        BY otherTransfers_moneyConstantForTrans
    <2> QED BY <2>1, <2>2
<1>3 StateConstraints' BY stateConstraints
<1> QED BY <1>1, <1>2, <1>3

====