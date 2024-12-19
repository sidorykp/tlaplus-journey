---- MODULE MoneyTransferSmall_proofs ----
EXTENDS MoneyTransferSmall, TLAPS

ASSUME AvailAssumption == Avail \in Nat \ {0}

ASSUME EmptyAssumption == Empty \notin Account

THEOREM ImplicationProperty == IndInv => MoneyTotalPreserved
BY DEF MoneyTotalPreserved, IndInv

THEOREM InitProperty == ASSUME Init
PROVE IndInv
<1> USE DEF Init, IndInv, TypeOK, Account, Transfer
<1>1 TypeOK
    <2>1 pcLabels BY DEF pcLabels, ProcSet
    <2>2 bal \in [Account -> Int] BY AvailAssumption
    <2>3 accounts \in [Transfer -> EAccounts] BY EmptyAssumption
        DEF EmptyAccounts, EAccounts, EAccount
    <2> QED BY <2>1, <2>2, <2>3
<1>2 MoneyTotalPreserved
    <2>1 bal[a1] + bal[a2] + bal[a3] = 3 * Avail BY AvailAssumption
    <2>2 \A t \in Transfer: amountPending(t) = 0 BY DEF amountPending, pcLabels
    <2>3 \A a \in Account: bal[a] \in Int BY AvailAssumption
    <2>4 bal[a1] + bal[a2] + bal[a3] \in Int BY <2>3
    <2> QED BY <2>1, <2>2, <2>3 DEF MoneyTotalPreserved, MoneyTotal
<1>3 \A t \in Transfer: pc[t] \notin {"choose_accounts"} <=> NonEmptyAccounts(t)
    BY EmptyAssumption DEF pcLabels, ProcSet, NonEmptyAccounts, EmptyAccounts
<1> QED BY <1>2, <1>1, <1>3


THEOREM choose_accounts_IndInv == ASSUME IndInv, \E self \in Transfer: choose_accounts(self)
PROVE IndInv'
<1> USE DEF Init, IndInv, TypeOK, Account, Transfer, choose_accounts
<1>1 TypeOK'
    <2>1 pcLabels' BY DEF pcLabels, ProcSet
    <2>2 bal' \in [Account -> Int] BY AvailAssumption
    <2>3 accounts' \in [Transfer -> EAccounts] BY EmptyAssumption
        DEF EmptyAccounts, EAccounts, EAccount
    <2> QED BY <2>1, <2>2, <2>3
<1>2 MoneyTotalPreserved'
    <2>1 \A a \in Account: bal[a]' = bal[a] OBVIOUS
    <2>2 \A t \in Transfer: amountPending(t)' = amountPending(t) BY DEF amountPending, pcLabels
    <2> QED BY <2>1, <2>2 DEF MoneyTotalPreserved, MoneyTotal
<1>3 \A t \in Transfer: (pc[t] \notin {"choose_accounts"})' <=> NonEmptyAccounts(t)'
    BY EmptyAssumption DEF NonEmptyAccounts, pcLabels
<1> QED BY <1>1, <1>2, <1>3


THEOREM choose_amount_IndInv == ASSUME IndInv, \E self \in Transfer: choose_amount(self)
PROVE IndInv'
<1> USE DEF Init, IndInv, TypeOK, Account, Transfer, choose_amount
<1>1 TypeOK'
    <2>1 pcLabels' BY DEF pcLabels, ProcSet
    <2>2 bal' \in [Account -> Int] BY AvailAssumption
    <2>3 accounts' \in [Transfer -> EAccounts] BY EmptyAssumption
        DEF EmptyAccounts, EAccounts, EAccount
    <2> QED BY <2>1, <2>2, <2>3
<1>2 MoneyTotalPreserved'
    <2>1 \A a \in Account: bal[a]' = bal[a] OBVIOUS
    <2>2 \A t \in Transfer: amountPending(t)' = amountPending(t) BY DEF amountPending, pcLabels
    <2> QED BY <2>1, <2>2 DEF MoneyTotalPreserved, MoneyTotal
<1>3 \A t \in Transfer: (pc[t] \notin {"choose_accounts"})' <=> NonEmptyAccounts(t)'
    BY EmptyAssumption DEF NonEmptyAccounts, pcLabels
<1> QED BY <1>1, <1>2, <1>3

====
