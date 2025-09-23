---- MODULE MoneyTransferReferenceLocal_proofs ----
EXTENDS MoneyTransferReference, MoneyTransfer_proofsCommon, TLAPS

THEOREM initProperty == ASSUME Init PROVE IndInv
<1> USE DEF Init, IndInv, TypeOK
<1>1 TypeOK
    <2>1 accounts \in [Transfer -> EAccounts] BY DEF EmptyAccounts, EAccounts, EAccount
    <2>2 pcLabels BY DEF ProcSet, pcLabels
    <2> QED BY <2>1, <2>2
<1>2 MoneyConstant
    <2> QED BY DEF MoneyConstant, moneyConstantForTrans, debitAmount, pendingAmount, creditAmount
<1>3 \A t \in Transfer: accounts[t] = EmptyAccounts \/ DifferentAccounts(t)
    <2> QED BY DEF EmptyAccounts, DifferentAccounts
<1>4 \A t \in Transfer: pc[t] \in {"choose_accounts", "choose_amount"} => debitPrecond(t)
    <2> QED BY DEF debitPrecond, isTransKnown
<1>5 \A t \in Transfer: pc[t] \notin {"choose_accounts"} => NonEmptyAccounts(t)
    <2>1 \A t \in Transfer: pc[t] \in {"choose_accounts"} BY DEF ProcSet
    <2> QED BY <2>1 DEF NonEmptyAccounts, EmptyAccounts
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5


THEOREM choose_accounts_IndInv == ASSUME IndInv, NEW self \in Transfer, choose_accounts(self)
PROVE IndInv'
<1> USE DEF choose_accounts, IndInv, TypeOK
<1>1 TypeOK'
    <2>1 accounts' \in [Transfer -> EAccounts] BY DEF EmptyAccounts, EAccounts, EAccount
    <2>2 pcLabels' BY DEF ProcSet, pcLabels
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
    <2>2 \A t \in Transfer \ {self}: moneyConstantForTrans(t)' = moneyConstantForTrans(t)
        <3>1 \A t \in Transfer \ {self}: NonEmptyAccounts(t)' = NonEmptyAccounts(t)
            BY DEF NonEmptyAccounts
        <3>2 \A t \in Transfer \ {self}: debitAmount(t)' = debitAmount(t) BY <3>1
        <3>3 \A t \in Transfer \ {self}: creditAmount(t)' = creditAmount(t) BY <3>1
        <3>4 \A t \in Transfer \ {self}: pc[t]' = pc[t] BY DEF pcLabels
        <3>5 \A t \in Transfer \ {self}: creditPrecond(t)' = creditPrecond(t) BY DEF creditPrecond
        <3>6 \A t \in Transfer \ {self}: pendingAmount(t)' = pendingAmount(t)
            BY <3>1, <3>4, <3>5 DEF AmountIsPending
        <3> QED BY <3>2, <3>3, <3>6
    <2> QED BY <2>1, <2>2
<1>3 \A t \in Transfer: (accounts[t] = EmptyAccounts \/ DifferentAccounts(t))'
    BY DEF DifferentAccounts, EmptyAccounts, EAccounts, EAccount
<1>4 \A t \in Transfer: (pc[t] \in {"choose_accounts", "choose_amount"} => debitPrecond(t))'
    BY DEF pcLabels, debitPrecond, isTransKnown
<1>5 \A t \in Transfer: (pc[t] \notin {"choose_accounts"} => NonEmptyAccounts(t))'
    <2> USE DEF pcLabels, NonEmptyAccounts
    <2>1 (pc[self] \notin {"choose_accounts"} => NonEmptyAccounts(self))'
        <3>1 (accounts[self].from)' # Empty BY EmptyAssumption, AccountAssumption
        <3>2 (accounts[self].to)' # Empty BY EmptyAssumption, AccountAssumption
        <3>3 NonEmptyAccounts(self)'
            BY <3>1, <3>2
        <3> QED BY <3>3
    <2> QED BY <2>1
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5

====