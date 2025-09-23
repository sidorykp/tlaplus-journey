---- MODULE MoneyTransferReferenceLocal_proofs ----
EXTENDS MoneyTransferReference, MoneyTransfer_proofsCommon, TLAPS

THEOREM initProperty == ASSUME Init PROVE IndInv
<1> USE DEF Init, IndInv, TypeOK
<1>1 TypeOK
    <2>1 accounts \in [Transfer -> EAccounts] BY DEF EmptyAccounts, EAccounts, EAccount
    <2>2 pcLabels BY DEF ProcSet, pcLabels
    <2> QED BY <2>1, <2>2
<1>2 MoneyConstant
    <2> QED BY DEF MoneyConstant, debitAmount, pendingAmount, creditAmount
<1>3 \A t \in Transfer: accounts[t] = EmptyAccounts \/ DifferentAccounts(t)
    <2> QED BY DEF EmptyAccounts, DifferentAccounts
<1>4 \A t \in Transfer: pc[t] \in {"choose_accounts", "choose_amount"} => debitPrecond(t)
    <2> QED BY DEF debitPrecond, isTransKnown
<1>5 \A t \in Transfer: pc[t] \notin {"choose_accounts"} => NonEmptyAccounts(t)
    <2>1 \A t \in Transfer: pc[t] \in {"choose_accounts"} BY DEF ProcSet
    <2> QED BY <2>1 DEF NonEmptyAccounts, EmptyAccounts
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5

====