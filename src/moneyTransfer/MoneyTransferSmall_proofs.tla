---- MODULE MoneyTransferSmall_proofs ----
EXTENDS MoneyTransferSmall, TLAPS

ASSUME AvailAssumption == Avail \in Nat \ {0}

ASSUME EmptyAssumption == Empty \notin Account

ASSUME AccountsUniqueAssumption ==
    /\ a1 # a2
    /\ a1 # a3
    /\ a2 # a3
    
ASSUME TransfersUniqueAssumption == t1 # t2


LEMMA AccountCardinality == Cardinality(Account) = 3
<1>1 Cardinality({a1}) = 1 BY FS_Singleton
<1>2 IsFiniteSet({a1}) BY FS_Singleton
<1>3 a2 \notin {a1} BY AccountsUniqueAssumption
<1>4 Cardinality({a1} \cup {a2}) = 2 BY <1>1, <1>3, <1>2, FS_AddElement
<1>5 IsFiniteSet({a1} \cup {a2}) BY <1>1, <1>3, <1>2, FS_AddElement
<1>6 a3 \notin {a1, a2} BY AccountsUniqueAssumption
<1>7 Cardinality({a1, a2} \cup {a3}) = 3 BY <1>4, <1>5, <1>6, FS_AddElement
<1> QED BY <1>7 DEF Account


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
    <2> QED BY <2>1, <2>2, <2>3, AccountCardinality DEF MoneyTotalPreserved, MoneyTotal
<1>3 \A t \in Transfer: pc[t] \notin {"choose_accounts"} <=> NonEmptyAccounts(t)
    BY EmptyAssumption DEF pcLabels, ProcSet, NonEmptyAccounts, EmptyAccounts
<1> QED BY <1>1, <1>2, <1>3


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
    <2>6 bal[a1] + bal[a2] + bal[a3] + amountPending(self) \in Int BY DEF amountPending
    <2>7 (bal[a1] + bal[a2] + bal[a3] + amountPending(self))' \in Int BY DEF amountPending
    <2>8 bal[a] \in Int BY <2>1
    <2>9 bal[a]' \in Int BY <2>8, <2>2
    <2>10 (bal[a1] + bal[a2] + bal[a3] + amountPending(self))'
        = bal[a1] + bal[a2] + bal[a3] + amountPending(self)
        BY AccountsUniqueAssumption, <2>5, <2>6, <2>7, <2>8, <2>9 DEF amountPending
    <2>11 \A t \in Transfer \ {self}: amountPending(t)' = amountPending(t)
        BY DEF amountPending, pcLabels
    <2> QED BY AccountsUniqueAssumption, <2>10, <2>11, TransfersUniqueAssumption
        DEF MoneyTotalPreserved, MoneyTotal, amountPending
<1>3 \A t \in Transfer: (pc[t] \notin {"choose_accounts"})' <=> NonEmptyAccounts(t)'
    BY EmptyAssumption DEF NonEmptyAccounts, pcLabels
<1> QED BY <1>1, <1>2, <1>3


THEOREM credit_IndInv == ASSUME IndInv, NEW self \in Transfer, credit(self)
PROVE IndInv'
<1> USE DEF Init, IndInv, TypeOK, Account, Transfer, credit
<1>1 TypeOK'
    <2>1 pcLabels' BY DEF pcLabels
    <2>2 bal' \in [Account -> Int] BY AvailAssumption
    <2>3 accounts' \in [Transfer -> EAccounts] BY EmptyAssumption
        DEF EmptyAccounts, EAccounts, EAccount
    <2> QED BY <2>1, <2>2, <2>3
<1> DEFINE a == accounts[self].to
<1>2 MoneyTotalPreserved'
    <2>1 a \in Account BY DEF EAccounts, EAccount, NonEmptyAccounts
    <2>2 bal[a]' = bal[a] + amount[self] BY <2>1
    <2>3 amountPending(self)' = 0 BY DEF amountPending, pcLabels
    <2>4 amountPending(self) = amount[self] BY DEF amountPending, pcLabels
    <2>5 (bal[a] + amountPending(self))' = bal[a] + amountPending(self) BY <2>1, <2>3, <2>4
    <2>6 bal[a1] + bal[a2] + bal[a3] + amountPending(self) \in Int BY DEF amountPending
    <2>7 (bal[a1] + bal[a2] + bal[a3] + amountPending(self))' \in Int BY DEF amountPending
    <2>8 bal[a] \in Int BY <2>1
    <2>9 bal[a]' \in Int BY <2>8, <2>2
    <2>10 (bal[a1] + bal[a2] + bal[a3] + amountPending(self))'
        = bal[a1] + bal[a2] + bal[a3] + amountPending(self)
        BY AccountsUniqueAssumption, <2>5, <2>6, <2>7, <2>8, <2>9 DEF amountPending
    <2>11 \A t \in Transfer \ {self}: amountPending(t)' = amountPending(t)
        BY DEF amountPending, pcLabels
    <2> QED BY AccountsUniqueAssumption, <2>10, <2>11, TransfersUniqueAssumption
        DEF MoneyTotalPreserved, MoneyTotal, amountPending
<1>3 \A t \in Transfer: (pc[t] \notin {"choose_accounts"})' <=> NonEmptyAccounts(t)'
    BY EmptyAssumption DEF NonEmptyAccounts, pcLabels
<1> QED BY <1>1, <1>2, <1>3


THEOREM NextNonTerminating == ASSUME IndInv, Next, ~Terminating
PROVE IndInv'
<1> SUFFICES ASSUME IndInv, NEW self \in Transfer, trans(self)
    PROVE IndInv'
    BY DEF Next, trans
<1>1 CASE choose_accounts(self) BY <1>1, choose_accounts_IndInv
<1>2 CASE choose_amount(self) BY <1>2, choose_amount_IndInv
<1>3 CASE debit(self) BY <1>3, debit_IndInv
<1>4 CASE credit(self) BY <1>4, credit_IndInv
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF trans


THEOREM unchangedVarsProperty == IndInv /\ UNCHANGED vars => IndInv'
<1> SUFFICES ASSUME IndInv, UNCHANGED vars
    PROVE IndInv'
    OBVIOUS
<1> USE DEF vars
<1>1 TypeOK' = TypeOK BY DEF TypeOK, pcLabels
<1>2 MoneyTotalPreserved' BY DEF MoneyTotalPreserved, MoneyTotal, amountPending,
    IndInv, TypeOK
<1>3 \A t \in Transfer: pc[t]' \notin {"choose_accounts"} <=> NonEmptyAccounts(t)'
    BY DEF IndInv, TypeOK, NonEmptyAccounts
<1> QED BY <1>1, <1>2, <1>3 DEF IndInv


THEOREM NextProperty == IndInv /\ Next => IndInv'
<1> SUFFICES ASSUME IndInv, Next
    PROVE IndInv'
    OBVIOUS
<1> USE DEF IndInv, Next, Terminating
<1>1 CASE ~Terminating
    <2> QED BY <1>1, NextNonTerminating
<1>2 CASE Terminating
    <2> QED BY <1>2, unchangedVarsProperty 
<1> QED BY <1>1, <1>2


THEOREM IndInvPreserved == Spec => []IndInv
<1>1 IndInv /\ UNCHANGED vars => IndInv'
    BY unchangedVarsProperty
<1> QED BY PTL, InitProperty, NextProperty, <1>1 DEF Spec


THEOREM Correctenss == Spec => []MoneyTotalPreserved
BY PTL, IndInvPreserved, ImplicationProperty DEF Spec

====
