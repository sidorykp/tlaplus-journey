---- MODULE MoneyTransferSmall_proofs ----
EXTENDS MoneyTransferSmall, TLAPS

ASSUME AvailAssumption == Avail \in Nat \ {0}

ASSUME EmptyAssumption == Empty \notin Account

ASSUME AccountsUniqueAssumption ==
    /\ a1 # a2
    /\ a1 # a3
    /\ a2 # a3
    
ASSUME TransfersUniqueAssumption == t1 # t2

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
    <2>1 pcLabels' BY DEF pcLabels
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


THEOREM choose_amount_IndInv == ASSUME IndInv, NEW self \in Transfer, choose_amount(self)
PROVE IndInv'
<1> USE DEF Init, IndInv, TypeOK, Account, Transfer, choose_amount
<1>1 TypeOK'
    <2>1 pcLabels' BY DEF pcLabels
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


THEOREM debit_IndInv == ASSUME IndInv, NEW self \in Transfer, debit(self)
PROVE IndInv'
<1> USE DEF Init, IndInv, TypeOK, Account, Transfer, debit
<1>1 TypeOK'
    <2>1 pcLabels' BY DEF pcLabels
    <2>2 bal' \in [Account -> Int] BY AvailAssumption
    <2>3 accounts' \in [Transfer -> EAccounts] BY EmptyAssumption
        DEF EmptyAccounts, EAccounts, EAccount
    <2> QED BY <2>1, <2>2, <2>3
<1> DEFINE a == accounts[self].from
<1>2 MoneyTotalPreserved'
    <2>1 a \in Account BY DEF EAccounts, EAccount, NonEmptyAccounts
    <2>2 bal[a]' = bal[a] - amount[self] BY <2>1
    <2>3 amountPending(self) = 0 BY DEF amountPending, pcLabels
    <2>4 amountPending(self)' = amount[self] BY DEF amountPending, pcLabels
    <2>5 (bal[a] + amountPending(self))' = bal[a] + amountPending(self) BY <2>1, <2>3, <2>4
    <2>10 bal[a1] + bal[a2] + bal[a3] + amountPending(self) \in Int BY DEF amountPending
    <2>11 (bal[a1] + bal[a2] + bal[a3] + amountPending(self))' \in Int BY DEF amountPending
    <2>12 bal[a] \in Int BY <2>1
    <2>13 bal[a]' \in Int BY <2>12, <2>2
    <2>7 (bal[a1] + bal[a2] + bal[a3] + amountPending(self))'
        = bal[a1] + bal[a2] + bal[a3] + amountPending(self)
        BY AccountsUniqueAssumption, <2>5, <2>10, <2>11, <2>12, <2>13 DEF amountPending
    <2>8 \A t \in Transfer \ {self}: amountPending(t)' = amountPending(t)
        BY DEF amountPending, pcLabels
    <2> QED BY AccountsUniqueAssumption, <2>7, <2>8, TransfersUniqueAssumption
        DEF MoneyTotalPreserved, MoneyTotal, amountPending
<1>3 \A t \in Transfer: (pc[t] \notin {"choose_accounts"})' <=> NonEmptyAccounts(t)'
    BY EmptyAssumption DEF NonEmptyAccounts, pcLabels
<1> QED BY <1>1, <1>2, <1>3

====
