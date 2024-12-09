---- MODULE MoneyTransferPendingExplicit_proofs ----
EXTENDS MoneyTransferPendingExplicit, FiniteSetsExt_theorems, FiniteSetTheorems, TLAPS

CONSTANTS NAccount, NTransfer

ASSUME AccountAssumption == Account = 1..NAccount

ASSUME TransferAssumption == Transfer = 1..NTransfer

ASSUME NTransferAssumption == NTransfer \in NNat

ASSUME NAccountAssumption == NAccount \in NNat

ASSUME NAvailAssumption == NAvail \in NNat

ASSUME EmptyAssumption == Empty = 0

LEMMA pendingTransAmountInNat == ASSUME TypeOK, NEW self \in TN
PROVE pendingTransAmount(self) \in Nat
BY DEF TypeOK, pendingTransAmount, TN

LEMMA transSetIsFinite == ASSUME NTransferAssumption
PROVE IsFiniteSet(Transfer)
<1>1 Transfer \in SUBSET (Nat) BY TransferAssumption
<1>2 \A t \in Transfer: t <= NTransfer BY TransferAssumption
<1> QED BY <1>1, <1>2, FS_BoundedSetOfNaturals DEF NNat

LEMMA AmountPendingTotalInNat == ASSUME NTransferAssumption, IndInv
PROVE AmountPendingTotal \in Nat
<1>1 IsFiniteSet(Transfer) BY transSetIsFinite, NTransferAssumption
<1>2 IsFiniteSet({t \in Transfer : AmountIsPending(t)}) BY <1>1, FS_Subset
<1>3 IsFiniteSet(pendingTrans) BY <1>2, FS_Image DEF IndInv, TypeOK
<1>4 \A pt \in pendingTrans: pt \in TN BY DEF TN, IndInv, TypeOK
<1>5 \A pt \in pendingTrans: pendingTransAmount(pt) \in Nat BY <1>4, pendingTransAmountInNat
    DEF IndInv
<1> QED BY <1>3, <1>5, MapThenSumSetType DEF AmountPendingTotal


LEMMA init_Imbalance == ASSUME Init
PROVE Imbalance = 0
<1> USE DEF Init
<1>1 CreditTotal = 0 BY MapThenSumSetEmpty DEF CreditTotal, MapThenSumSetE, MapThenFoldSetE
<1>2 DebitTotal = 0 BY MapThenSumSetEmpty DEF DebitTotal, MapThenSumSetE, MapThenFoldSetE
<1>3 AmountPendingTotal = 0
    BY MapThenSumSetEmpty DEF AmountPendingTotal, AmountIsPending, creditPrecond, isTransKnown
<1> QED BY <1>1, <1>2, <1>3 DEF Imbalance


THEOREM initProperty == ASSUME Init PROVE IndInv
<1> USE DEF Init, IndInv, TypeOK
<1>1 IsFiniteSet(credits) BY FS_EmptySet
<1>2 IsFiniteSet(debits) BY FS_EmptySet
<1>3 IsFiniteSet(pendingTrans) BY FS_EmptySet
<1>4 accounts \in [Transfer -> EAccounts] BY DEF EAccount, EmptyAccounts, EAccounts
<1>5 pcLabels BY DEF pcLabels, ProcSet
<1>6 \A t \in Transfer: pc[t] = "init" => initPrecond(t)
    BY DEF initPrecond, isTransKnown, isTransKnownToItem
<1>7 \A t \in Transfer:
        pc[t] \notin {"init"} <=> NonEmptyAccounts(t)
    BY DEF ProcSet, NonEmptyAccounts, EmptyAccounts
<1>8 TransPendingEquivalence BY DEF TransPendingEquivalence, AmountIsPending, creditPrecond,
    isTransKnown, isTransKnownToItem, TransInPendingTrans
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, init_Imbalance
    DEF PendingTransDerived, PendingTransUniqueness


THEOREM crash_AmountPendingTotal == ASSUME IndInv, NEW self \in Transfer, crash(self)
PROVE AmountPendingTotal' = AmountPendingTotal
BY DEF crash, AmountPendingTotal


THEOREM crash_IndInv == ASSUME IndInv, NEW self \in Transfer, crash(self)
PROVE IndInv'
<1> USE DEF IndInv, TypeOK
<1>1 credits' \in SUBSET (AT \X Nat) BY DEF crash
<1>2 IsFiniteSet(credits)' BY DEF crash
<1>3 debits' \in SUBSET (AT \X Nat) BY DEF crash
<1>4 IsFiniteSet(debits)' BY DEF crash
<1>5 pendingTrans' \in SUBSET TN BY DEF crash
<1>6 IsFiniteSet(pendingTrans)' BY DEF crash
<1>7 amount' \in [Transfer -> Nat] BY DEF crash
<1>8 accounts' \in [Transfer -> EAccounts] BY DEF crash

<1>9 pc'[self] \in {"credit", "debit"} BY DEF crash, pcLabels
<1>10 pcLabels' BY <1>9 DEF crash, pcLabels

<1>11 Imbalance' = Imbalance BY crash_AmountPendingTotal
    DEF crash, Imbalance, creditPrecond, CreditTotal, DebitTotal
<1>12 Imbalance' = 0 BY <1>11

<1>13 \A t \in Transfer:
    (\/ accounts[t] = EmptyAccounts
     \/ DifferentAccounts(t) /\ NonEmptyAccounts(t))'
    BY DEF crash, EmptyAccounts, DifferentAccounts, NonEmptyAccounts

<1>14 \A t \in Transfer: pc[t] \notin {"init"} <=> NonEmptyAccounts(t)
    BY DEF IndInv
<1>15 \A t \in Transfer: NonEmptyAccounts(t)' = NonEmptyAccounts(t)
    BY DEF crash, NonEmptyAccounts
<1>16 NonEmptyAccounts(self)' = NonEmptyAccounts(self)
    BY <1>15
<1>17 pc[self] \notin {"init"} <=> NonEmptyAccounts(self)
    BY <1>14
<1>18 pc[self] \notin {"init"} BY DEF crash
<1>19 pc'[self] \notin {"init"} BY <1>9
<1>20 pc'[self] \notin {"init"} <=> NonEmptyAccounts(self)'
    BY <1>16, <1>17, <1>18, <1>19

<1>21 pc'[self] = "init" => initPrecond(self)' BY <1>9
<1>22 \A t \in Transfer: pc'[t] = "init" => initPrecond(t)'
    BY <1>21 DEF crash, pcLabels

<1>23 \A t \in Transfer \ {self}: pc'[t] \notin {"init"} <=> pc[t] \notin {"init"}
    BY DEF crash, pcLabels
<1>24 \A t \in Transfer \ {self}: pc'[t] \notin {"init"} <=> NonEmptyAccounts(t)'
    BY <1>14, <1>15, <1>23

<1>25 \A t \in Transfer: pc'[t] \notin {"init"} <=> NonEmptyAccounts(t)'
    BY <1>20, <1>24

<1>26 TransPendingEquivalence' BY DEF crash, TransPendingEquivalence, TransInPendingTrans,
    pcLabels, AmountIsPending, creditPrecond, isTransKnown, isTransKnownToItem

<1>27 PendingTransDerived' BY DEF crash, PendingTransDerived

<1>28 PendingTransUniqueness' BY DEF crash, PendingTransUniqueness

<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>10, <1>12, <1>13, <1>22, <1>25, <1>26, <1>27, <1>28


THEOREM init_AmountPendingTotal == ASSUME IndInv, NEW self \in Transfer, init(self)
PROVE AmountPendingTotal' = AmountPendingTotal
BY DEF init, AmountPendingTotal


THEOREM init_IndInv == ASSUME IndInv, NEW self \in Transfer, init(self)
PROVE IndInv'
<1> DEFINE am == amount'[self]
<1> DEFINE selfAccounts == accounts'[self]
<1> DEFINE account1 == selfAccounts.from
<1> DEFINE account2 == selfAccounts.to
<1> USE DEF IndInv, TypeOK
<1>1 credits' \in SUBSET (AT \X Nat) BY DEF init
<1>2 IsFiniteSet(credits)' BY DEF init
<1>3 debits' \in SUBSET (AT \X Nat) BY DEF init
<1>4 IsFiniteSet(debits)' BY DEF init
<1>5 pendingTrans' \in SUBSET TN BY DEF init
<1>6 IsFiniteSet(pendingTrans)' BY DEF init

<1>7 am \in Nat BY DEF init, NNat
<1>8 amount' \in [Transfer -> Nat] BY <1>7 DEF init

<1>9 selfAccounts \in EAccounts BY DEF init, EAccounts, EAccount
<1>10 accounts' \in [Transfer -> EAccounts] BY <1>9 DEF init

<1>11 pcLabels' BY DEF init, ProcSet, pcLabels

<1>12 Imbalance' = Imbalance BY init_AmountPendingTotal DEF init, Imbalance, creditPrecond, CreditTotal, DebitTotal
<1>13 Imbalance' = 0 BY <1>12

<1>14 Empty \notin Account BY EmptyAssumption, AccountAssumption
<1>15 account1 # Empty BY <1>14 DEF init
<1>16 account2 # Empty BY <1>14 DEF init
<1>17 account1 # account2 BY DEF init
<1>18 (\/ accounts[self] = EmptyAccounts
       \/ DifferentAccounts(self) /\ NonEmptyAccounts(self))'
    BY <1>15, <1>16, <1>17 DEF DifferentAccounts, NonEmptyAccounts
<1>19 \A t \in Transfer:
    (\/ accounts[t] = EmptyAccounts
     \/ DifferentAccounts(t) /\ NonEmptyAccounts(t))'
    BY <1>18 DEF init, EmptyAccounts, DifferentAccounts, NonEmptyAccounts

<1>20 initPrecond(self)' BY DEF init, initPrecond, isTransKnown, isTransKnownToItem
<1>21 pc'[self] = "init" => initPrecond(self)' BY <1>20 DEF ProcSet
<1>22 \A t \in Transfer: pc'[t] = "init" => initPrecond(t)' BY <1>21 DEF init, pcLabels

<1>23 NonEmptyAccounts(self)' BY <1>15, <1>16 DEF NonEmptyAccounts
<1>24 pc'[self] \notin {"init"} <=> NonEmptyAccounts(self)' BY <1>23 DEF init, ProcSet, pcLabels

<1>25 \A t \in Transfer \ {self}: pc'[t] \notin {"init"} <=> pc[t] \notin {"init"}
    BY DEF init, pcLabels
<1>26 \A t \in Transfer \ {self}: NonEmptyAccounts(t)' = NonEmptyAccounts(t)
    BY DEF init, NonEmptyAccounts
<1>27 \A t \in Transfer \ {self}: pc'[t] \notin {"init"} <=> NonEmptyAccounts(t)'
    BY <1>25, <1>26 DEF IndInv

<1>28 \A t \in Transfer: pc'[t] \notin {"init"} <=> NonEmptyAccounts(t)'
    BY <1>24, <1>27 DEF init, ProcSet, pcLabels

<1>29 ~AmountIsPending(self) BY DEF init, AmountIsPending, creditPrecond, initPrecond
<1>30 ~AmountIsPending(self)' BY DEF init, AmountIsPending, creditPrecond, initPrecond
<1>31 TransInPendingTrans(self)' = TransInPendingTrans(self)
    <2>1 CASE initPrecond(self)
        <3> QED BY <2>1 DEF init, TransInPendingTrans, PendingTransUniqueness
    <2>2 CASE ~initPrecond(self)
        <3> QED BY <2>2 DEF init, TransInPendingTrans
    <2> QED BY <2>1, <2>2
<1>32 (AmountIsPending(self) <=> TransInPendingTrans(self)) ' = (AmountIsPending(self) <=> TransInPendingTrans(self))
    BY <1>29, <1>30, <1>31
<1>33 \A t \in Transfer \ {self}: (AmountIsPending(t) <=> TransInPendingTrans(t))' = (AmountIsPending(t) <=> TransInPendingTrans(t))
    <2>1 CASE initPrecond(self)
        <3>1 pendingTrans' = pendingTrans BY DEF init
        <3> QED BY <2>1, <3>1 DEF init, AmountIsPending, TransInPendingTrans,
            creditPrecond, isTransKnown, isTransKnownToItem
    <2>2 CASE ~initPrecond(self)
        <3> QED BY <2>2 DEF init, AmountIsPending, TransInPendingTrans
    <2> QED BY <2>1, <2>2
<1>34 TransPendingEquivalence'  = TransPendingEquivalence BY <1>32, <1>33 DEF TransPendingEquivalence

<1>35 PendingTransDerived' BY DEF init, PendingTransDerived

<1>36 PendingTransUniqueness' BY DEF init, PendingTransUniqueness

<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>8, <1>10, <1>11, <1>13, <1>19, <1>22, <1>28, <1>34, <1>35, <1>36


LEMMA debit_DebitTotal_debitPrecond_success == ASSUME IndInv, NEW self \in Transfer, debit(self),
debitPrecond(self), ~(UNCHANGED <<debits, pendingTrans>>)
PROVE DebitTotal' = DebitTotal + amount[self]
<1> DEFINE a == accounts[self].from
<1> DEFINE nadd == <<[a |-> a, t |-> self], amount[self]>>
<1> USE DEF IndInv, TypeOK, debitPrecond
<1>1 nadd \notin debits BY DEF isTransKnown, isTransKnownToItem, AT
<1>2 debits' = debits \cup {nadd} BY DEF debit
<1>3 \A nb \in debits: opAmount(nb) \in Nat BY DEF opAmount
<1>4 opAmount(nadd) \in Nat BY DEF opAmount
<1>5 MapThenSumSet(opAmount, debits') =
    MapThenSumSet(opAmount, debits) + opAmount(nadd)
    BY <1>1, <1>2, <1>3, <1>4, MapThenSumSetAddElem
<1>6 DebitTotal' = DebitTotal + opAmount(nadd)
    BY <1>5 DEF DebitTotal, MapThenSumSetE, MapThenFoldSetE, MapThenSumSet, MapThenFoldSet
<1> QED BY <1>6 DEF opAmount

LEMMA debit_DebitTotal_notDebitPrecond_or_crash == ASSUME IndInv, NEW self \in Transfer, debit(self),
~debitPrecond(self) \/ UNCHANGED <<debits, pendingTrans>>
PROVE DebitTotal' = DebitTotal
BY DEF debit, DebitTotal


LEMMA debit_AmountPendingTotal_debitPrecond_success == ASSUME IndInv, NEW self \in Transfer, debit(self),
debitPrecond(self), ~(UNCHANGED <<debits, pendingTrans>>)
PROVE AmountPendingTotal' = AmountPendingTotal + amount[self]
<1> DEFINE nadd == <<self, amount[self]>>
<1>1 pendingTrans' = pendingTrans \cup {nadd}
    BY DEF debit
<1> USE DEF IndInv, TypeOK
<1>2 nadd \notin pendingTrans BY DEF TransPendingEquivalence, TransInPendingTrans,
    AmountIsPending, isTransKnown, isTransKnownToItem, debitPrecond, creditPrecond, AT
<1>3 \A pt \in pendingTrans: pendingTransAmount(pt) \in Nat BY pendingTransAmountInNat
<1>4 pendingTransAmount(nadd) \in Nat BY DEF debit, pendingTransAmount
<1>5 MapThenSumSet(pendingTransAmount, pendingTrans') =
    MapThenSumSet(pendingTransAmount, pendingTrans) + pendingTransAmount(nadd)
    BY <1>1, <1>2, <1>3, <1>4, MapThenSumSetAddElem
<1>6 AmountPendingTotal' = AmountPendingTotal + pendingTransAmount(nadd)
    BY <1>5 DEF AmountPendingTotal
<1> QED BY <1>6 DEF pendingTransAmount

LEMMA debit_AmountPendingTotal_notDebitPrecond_or_crash == ASSUME IndInv, NEW self \in Transfer, debit(self),
~debitPrecond(self) \/ UNCHANGED <<debits, pendingTrans>>
PROVE AmountPendingTotal' = AmountPendingTotal
BY DEF debit, AmountPendingTotal


LEMMA debit_Imbalance == ASSUME IndInv, NEW self \in Transfer, debit(self)
PROVE Imbalance' = Imbalance
<1>1 credits' = credits BY DEF debit
<1>2 CreditTotal' = CreditTotal
    BY <1>1 DEF CreditTotal
<1>3 CASE debitPrecond(self) /\ ~(UNCHANGED <<debits, pendingTrans>>)
    <2> QED BY <1>3, <1>2, debit_DebitTotal_debitPrecond_success,
        debit_AmountPendingTotal_debitPrecond_success DEF debit, Imbalance
<1>4 CASE ~debitPrecond(self) \/ UNCHANGED <<debits, pendingTrans>>
    <2> QED BY <1>4, <1>2, debit_DebitTotal_notDebitPrecond_or_crash,
        debit_AmountPendingTotal_notDebitPrecond_or_crash
        DEF debit, Imbalance
<1> QED BY <1>3, <1>4


THEOREM debit_IndInv_common == ASSUME IndInv, NEW self \in Transfer, debit(self)
PROVE (
    /\ credits \in SUBSET (AT \X Nat)
    /\ IsFiniteSet(credits)
    /\ CommonIndInv)'
<1> USE DEF CommonIndInv
<1>1 credits' \in SUBSET (AT \X Nat) BY DEF debit, IndInv, TypeOK
<1>2 IsFiniteSet(credits)' BY DEF debit, IndInv, TypeOK
<1>3 amount' \in [Transfer -> Nat] BY DEF debit, IndInv, TypeOK
<1>4 accounts' \in [Transfer -> EAccounts] BY DEF debit, IndInv, TypeOK
<1>5 pc' = [pc EXCEPT ![self] = "crash"] BY DEF debit
<1>6 pc'[self] = "crash" BY <1>5 DEF pcLabels, IndInv, TypeOK
<1>7 pcLabels' BY <1>6 DEF debit, pcLabels, ProcSet
<1>8 \A t \in Transfer:
    \/ accounts'[t] = EmptyAccounts
    \/ DifferentAccounts(t)' /\ NonEmptyAccounts(t)'
    BY DEF debit, EmptyAccounts, DifferentAccounts, NonEmptyAccounts, IndInv, TypeOK

<1>9 pc'[self] = "init" => initPrecond(self)' BY <1>6
<1>10 \A t \in Transfer \ {self}: pc[t]' = pc[t]
    BY <1>5 DEF pcLabels, IndInv, TypeOK
<1>11 \A t \in Transfer: pc'[t] = "init" => initPrecond(t)'
    BY <1>9, <1>10 DEF IndInv

<1>12 \A t \in Transfer: pc[t] \notin {"init"} <=> NonEmptyAccounts(t)
    BY DEF IndInv
<1>13 \A t \in Transfer: NonEmptyAccounts(t)' = NonEmptyAccounts(t)
    BY DEF debit, NonEmptyAccounts
<1>14 NonEmptyAccounts(self)' = NonEmptyAccounts(self)
    BY <1>13
<1>15 pc[self] \notin {"init"} <=> NonEmptyAccounts(self)
    BY <1>12
<1>16 pc[self] \notin {"init"} BY DEF debit
<1>17 pc'[self] \notin {"init"} BY <1>6
<1>18 pc'[self] \notin {"init"} <=> NonEmptyAccounts(self)'
    BY <1>14, <1>15, <1>16, <1>17

<1>19 \A t \in Transfer \ {self}: pc'[t] \notin {"init"} <=> pc[t] \notin {"init"}
    BY <1>10
<1>20 \A t \in Transfer \ {self}: pc'[t] \notin {"init"} <=> NonEmptyAccounts(t)'
    BY <1>12, <1>13, <1>19

<1>21 \A t \in Transfer: pc'[t] \notin {"init"} <=> NonEmptyAccounts(t)'
    BY <1>18, <1>20

<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>7, <1>8, <1>11, <1>21, debit_Imbalance DEF IndInv


THEOREM debit_IndInv == ASSUME IndInv, NEW self \in Transfer, debit(self)
PROVE IndInv'
<1> DEFINE a == accounts[self].from
<1> DEFINE nadd == <<[a |-> a, t |-> self], amount[self]>>
<1> DEFINE ptAdd == <<self, amount[self]>>
<1> USE DEF IndInv, TypeOK, CommonIndInv
<1>1 CASE debitPrecond(self) /\ ~(UNCHANGED <<debits, pendingTrans>>)
    <2>1 debits' = debits \cup {nadd} BY <1>1 DEF debit
    <2>2 a \in EAccount BY DEF EAccounts
    <2>3 a # Empty BY DEF debit, NonEmptyAccounts
    <2>4 a \in Account BY <2>2, <2>3 DEF EAccount
    <2>5 nadd \in AT \X Nat BY <2>4 DEF AT
    <2>6 debits' \in SUBSET (AT \X Nat)
        BY <2>1, <2>5
    <2>7 IsFiniteSet(debits)' BY <1>1, FS_AddElement DEF debit
    <2>8 pendingTrans' = pendingTrans \cup {ptAdd} BY <1>1 DEF debit
    <2>9 ptAdd \in TN BY DEF TN
    <2>10 pendingTrans' \in SUBSET TN BY <2>8, <2>9
    <2>11 IsFiniteSet(pendingTrans)' BY <1>1, FS_AddElement DEF debit
    
    <2>12 credits' = credits BY DEF debit
    
    <2>13 (AmountIsPending(self) <=> TransInPendingTrans(self))'
        <3>1 ~AmountIsPending(self) BY <1>1 DEF debit, AmountIsPending, creditPrecond, debitPrecond
        <3>2 AmountIsPending(self)' BY <1>1 DEF debit, AmountIsPending, creditPrecond,
            isTransKnown, isTransKnownToItem
        <3>3 ~TransInPendingTrans(self) BY <1>1, <3>1, TransPendingEquivalence DEF debit
        <3>4 TransInPendingTrans(self)' BY <1>1, <2>8 DEF debit, TransInPendingTrans
        <3> QED BY <3>1, <3>2, <3>3, <3>4
    <2>14 \A t \in Transfer \ {self}: TransInPendingTrans(t) = TransInPendingTrans(t)'
        BY <1>1, <2>1, <2>8, <2>12
        DEF TransInPendingTrans, debit
    <2>16 \A t \in Transfer \ {self}: AmountIsPending(t) = AmountIsPending(t)'
        BY <1>1, <2>1, <2>8, <2>12
        DEF debit, AmountIsPending, pcLabels, creditPrecond, isTransKnown, isTransKnownToItem
    <2>17 TransPendingEquivalence' = TransPendingEquivalence
        BY <2>13, <2>14, <2>16 DEF TransPendingEquivalence

    <2>18 \E d \in debits': d[1].t = ptAdd[1] /\ d[2] = ptAdd[2] BY <1>1, <2>1
    <2> HIDE DEF IndInv, TypeOK, CommonIndInv
    <2>19 \A pt \in pendingTrans' \ {ptAdd}: \E d \in debits': d[1].t = pt[1] /\ d[2] = pt[2]
        BY <1>1, <2>1, <2>8 DEF debit, IndInv, TypeOK, PendingTransDerived
    <2>20 \A pt \in pendingTrans': \E d \in debits': d[1].t = pt[1] /\ d[2] = pt[2]
        BY <1>1, <2>18, <2>19
    <2>21 PendingTransDerived' BY <2>20 DEF debit, PendingTransDerived
    
    <2>22 PendingTransUniqueness' = PendingTransUniqueness
        <3>1 pendingTrans' = {ptAdd} BY <1>1, <2>8 DEF debit
        <3> QED BY <1>1, <3>1 DEF debit, PendingTransUniqueness

    <2> QED BY <2>6, <2>7, <2>10, <2>11, <2>17, <2>21, <2>22, debit_IndInv_common, debit_Imbalance DEF IndInv, TypeOK, CommonIndInv
<1>2 CASE ~debitPrecond(self) \/ UNCHANGED <<debits, pendingTrans>>
    <2>1 debits' \in SUBSET (AT \X Nat) BY <1>2 DEF debit
    <2>2 IsFiniteSet(debits)' BY <1>2 DEF debit
    <2>3 pendingTrans' \in SUBSET TN BY <1>2 DEF debit
    <2>4 IsFiniteSet(pendingTrans)' BY <1>2 DEF debit
    <2>5 TransPendingEquivalence' BY <1>2 DEF debit, TransPendingEquivalence, TransInPendingTrans,
        pcLabels, AmountIsPending, creditPrecond, isTransKnown, isTransKnownToItem
    <2>6 PendingTransDerived'  BY <1>2 DEF debit, PendingTransDerived
    <2>7 PendingTransUniqueness' BY <1>2 DEF debit, PendingTransUniqueness
    <2> QED BY <1>1, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, debit_IndInv_common, debit_Imbalance
<1> QED BY <1>1, <1>2


LEMMA credit_AmountPendingTotal_creditPrecond == ASSUME IndInv, NEW self \in Transfer, credit(self),
creditPrecond(self)
PROVE AmountPendingTotal' = AmountPendingTotal - amount[self]
BY DEF credit, AmountPendingTotal


\* practically a copy of init_AmountPendingTotal
LEMMA credit_AmountPendingTotal_notCreditPrecond == ASSUME IndInv, NEW self \in Transfer, credit(self),
~creditPrecond(self)
PROVE AmountPendingTotal' = AmountPendingTotal
BY DEF credit, AmountPendingTotal


\* practically a copy of debit_DebitTotal
LEMMA credit_CreditTotal == ASSUME IndInv, NEW self \in Transfer, credit(self),
creditPrecond(self)
PROVE CreditTotal' = CreditTotal + amount[self]
<1> DEFINE a == accounts[self].to
<1> DEFINE nadd == <<[a |-> a, t |-> self], amount[self]>>
<1> USE DEF IndInv, TypeOK, creditPrecond
<1>1 nadd \notin credits BY DEF isTransKnown, isTransKnownToItem, AT
<1>2 credits' = credits \cup {nadd} BY DEF credit
<1>3 \A nb \in credits: opAmount(nb) \in Nat BY DEF opAmount
<1>4 opAmount(nadd) \in Nat BY DEF opAmount
<1>5 MapThenSumSet(opAmount, credits') =
    MapThenSumSet(opAmount, credits) + opAmount(nadd)
    BY <1>1, <1>2, <1>3, <1>4, MapThenSumSetAddElem
<1>6 CreditTotal' = CreditTotal + opAmount(nadd)
    BY <1>5 DEF CreditTotal, MapThenSumSetE, MapThenFoldSetE, MapThenSumSet, MapThenFoldSet
<1> QED BY <1>6 DEF opAmount


LEMMA credit_Imbalance == ASSUME IndInv, NEW self \in Transfer, credit(self)
PROVE Imbalance' = Imbalance
<1>1 debits' = debits BY DEF credit
<1>2 DebitTotal' = DebitTotal
    BY <1>1 DEF DebitTotal
<1>3 CASE creditPrecond(self)
    <2>1 CreditTotal' = CreditTotal + amount[self] BY <1>3, credit_CreditTotal
    <2>2 AmountPendingTotal' = AmountPendingTotal - amount[self] BY <1>3, credit_AmountPendingTotal_creditPrecond
    <2>3 amount[self] \in Nat BY DEF IndInv, TypeOK
    <2>4 \A c \in credits: opAmount(c) \in Nat BY DEF opAmount, IndInv, TypeOK
    <2>5 CreditTotal \in Nat BY <2>4, MapThenSumSetType DEF CreditTotal, IndInv, TypeOK,
        MapThenSumSetE, MapThenFoldSetE, MapThenSumSet, MapThenFoldSet
    <2>6 IsFiniteSet(pendingTrans) BY DEF IndInv, TypeOK
    <2>7 \A pt \in pendingTrans: pendingTransAmount(pt) \in Nat BY pendingTransAmountInNat, <1>3 DEF credit, IndInv
    <2>8 AmountPendingTotal \in Nat BY <2>6, <2>7, MapThenSumSetType DEF AmountPendingTotal
    <2>9 CreditTotal' + AmountPendingTotal' = CreditTotal + AmountPendingTotal BY <2>1, <2>2, <2>3, <2>5, <2>8
    <2>10 (CreditTotal' + AmountPendingTotal') - DebitTotal' = (CreditTotal + AmountPendingTotal) - DebitTotal BY <1>2, <2>9
    <2> QED BY <2>8, <2>10, <1>2 DEF Imbalance, credit
<1>4 CASE ~creditPrecond(self)
    <2>1 AmountPendingTotal' = AmountPendingTotal BY <1>4, credit_AmountPendingTotal_notCreditPrecond
    <2> QED BY <1>2, <2>1 DEF credit, Imbalance
<1> QED BY <1>3, <1>4


THEOREM credit_IndInv_common == ASSUME IndInv, NEW self \in Transfer, credit(self)
PROVE (
    /\ debits \in SUBSET (AT \X Nat)
    /\ IsFiniteSet(debits)
    /\ pendingTrans \in SUBSET TN
    /\ IsFiniteSet(pendingTrans)
    /\ CommonIndInv
    /\ TransPendingEquivalence
    /\ PendingTransDerived
    /\ PendingTransUniqueness)'
<1> USE DEF CommonIndInv
<1>1 debits' \in SUBSET (AT \X Nat) BY DEF credit, IndInv, TypeOK
<1>2 IsFiniteSet(debits)' BY DEF credit
<1>3 amount' \in [Transfer -> Nat] BY DEF credit, IndInv, TypeOK
<1>4 accounts' \in [Transfer -> EAccounts] BY DEF credit
<1>5 pc[self]' = "Done" BY DEF credit
<1>6 pcLabels' BY <1>5 DEF credit, pcLabels, ProcSet
<1>7 \A t \in Transfer:
    \/ accounts'[t] = EmptyAccounts
    \/ DifferentAccounts(t)' /\ NonEmptyAccounts(t)'
    BY DEF credit, EmptyAccounts, DifferentAccounts, NonEmptyAccounts, IndInv, TypeOK

<1>8 pc' = [pc EXCEPT ![self] = "Done"] BY DEF credit
<1>9 pc'[self] = "init" => initPrecond(self)' BY <1>5
<1>10 \A t \in Transfer \ {self}: pc[t]' = pc[t]
    BY <1>8 DEF pcLabels, IndInv, TypeOK
<1>11 \A t \in Transfer: pc'[t] = "init" => initPrecond(t)'
    BY <1>9, <1>10 DEF IndInv

<1>12 \A t \in Transfer: pc[t] \notin {"init"} <=> NonEmptyAccounts(t)
    BY DEF IndInv
<1>13 \A t \in Transfer: NonEmptyAccounts(t)' = NonEmptyAccounts(t)
    BY DEF credit, NonEmptyAccounts
<1>14 NonEmptyAccounts(self)' = NonEmptyAccounts(self)
    BY <1>13
<1>15 pc[self] \notin {"init"} <=> NonEmptyAccounts(self)
    BY <1>12
<1>16 pc[self] \notin {"init"} BY DEF credit
<1>17 pc'[self] \notin {"init"} BY <1>5
<1>18 pc'[self] \notin {"init"} <=> NonEmptyAccounts(self)'
    BY <1>14, <1>15, <1>16, <1>17

<1>19 \A t \in Transfer \ {self}: pc'[t] \notin {"init"} <=> pc[t] \notin {"init"}
    BY <1>10
<1>20 \A t \in Transfer \ {self}: pc'[t] \notin {"init"} <=> NonEmptyAccounts(t)'
    BY <1>12, <1>13, <1>19

<1>21 \A t \in Transfer: pc'[t] \notin {"init"} <=> NonEmptyAccounts(t)'
    BY <1>18, <1>20

<1>22 debits' = debits BY DEF credit
<1>23 pendingTrans' \in SUBSET TN  BY DEF credit, IndInv, TypeOK
<1>24 IsFiniteSet(pendingTrans)' BY DEF credit
<1> HIDE DEF IndInv, TypeOK, CommonIndInv
<1>25 AmountIsPending(self)' <=> TransInPendingTrans(self)' /\ PendingTransUniqueness'
    <2>1 CASE ~creditPrecond(self)
        <3>1 credits' = credits BY <2>1 DEF credit
        <3>2 pendingTrans' = pendingTrans BY <2>1 DEF credit
        <3> QED BY <3>1, <3>2 DEF TransInPendingTrans, credit, AmountIsPending
     <2>2 CASE creditPrecond(self)
        <3> DEFINE a == accounts[self].to
        <3> DEFINE nadd == <<[a |-> a, t |-> self], amount[self]>>
        <3> DEFINE ptAdd == <<self, amount[self]>>
        <3>1 credits' = credits \cup {nadd} BY <2>2 DEF credit
        <3>2 pendingTrans' = pendingTrans \ {ptAdd} BY <2>2 DEF credit
        <3> QED BY <2>2, <3>1, <3>2
            DEF TransInPendingTrans, credit, AmountIsPending
     <2> QED BY <2>1, <2>2

<1>26 TransPendingEquivalence'
    BY <1>25 DEF credit, TransPendingEquivalence, TransInPendingTrans

<1>27 PendingTransDerived' BY <1>20, <1>25 DEF credit, PendingTransDerived

<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>6, <1>7, <1>11, <1>21, <1>23, <1>24, <1>26, <1>27, credit_Imbalance
    DEF IndInv, TypeOK, CommonIndInv


THEOREM credit_IndInv == ASSUME IndInv, NEW self \in Transfer, credit(self)
PROVE IndInv'
<1> DEFINE a == accounts[self].to
<1> DEFINE nadd == <<[a |-> a, t |-> self], amount[self]>>
<1> USE DEF IndInv, TypeOK, CommonIndInv
<1>1 CASE creditPrecond(self)
    <2>3 credits' = credits \cup {nadd} BY <1>1 DEF credit
    <2>4 a \in EAccount BY DEF EAccounts
    <2>5 a # Empty BY DEF credit, NonEmptyAccounts
    <2>6 a \in Account BY <2>4, <2>5 DEF EAccount
    <2>7 nadd \in AT \X Nat BY <2>6 DEF AT
    <2>8 credits' \in SUBSET (AT \X Nat)
        BY <2>3, <2>7
    <2>9 IsFiniteSet(credits)' BY <1>1, FS_AddElement DEF credit
    <2> QED BY <2>8, <2>9, <1>1, credit_IndInv_common, credit_Imbalance
        DEF IndInv, TypeOK, CommonIndInv
<1>2 CASE ~creditPrecond(self)
    <2>3 credits' \in SUBSET (AT \X Nat) BY <1>2 DEF credit
    <2>4 IsFiniteSet(credits)' BY <1>2 DEF credit
    <2> QED BY <2>3, <2>4, <1>1, credit_IndInv_common, credit_Imbalance
<1> QED BY <1>1, <1>2


THEOREM nextNonTerminating == ASSUME IndInv, Next, ~Terminating
PROVE IndInv'
<1> SUFFICES ASSUME IndInv, NEW self \in Transfer, trans(self)
    PROVE IndInv'
    BY DEF Next, trans
<1>1 CASE init(self) BY <1>1, init_IndInv
<1>2 CASE debit(self) BY <1>2, debit_IndInv
<1>3 CASE crash(self) BY <1>3, crash_IndInv
<1>4 CASE credit(self) BY <1>4, credit_IndInv
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF trans


THEOREM unchangedVarsProperty == IndInv /\ UNCHANGED vars => IndInv'
<1> SUFFICES ASSUME IndInv, UNCHANGED vars
    PROVE IndInv'
    OBVIOUS
<1> USE DEF vars
<1>1 TypeOK' = TypeOK BY DEF TypeOK, pcLabels,
    TransPendingEquivalence, TransInPendingTrans, AmountIsPending, creditPrecond,
    PendingTransDerived, PendingTransUniqueness
<1>2 (/\ \A t \in Transfer:
        \/ accounts[t] = EmptyAccounts
        \/ DifferentAccounts(t) /\ NonEmptyAccounts(t))' =
      /\ \A t \in Transfer:
        \/ accounts[t] = EmptyAccounts
        \/ DifferentAccounts(t) /\ NonEmptyAccounts(t)
    BY DEF DifferentAccounts, NonEmptyAccounts
<1>3 (/\ \A t \in Transfer: pc[t] = "init" => initPrecond(t))' =
    /\ \A t \in Transfer: pc[t] = "init" => initPrecond(t)
    BY DEF initPrecond
<1>4 (/\ \A t \in Transfer:
        pc[t] \notin {"init"} <=> NonEmptyAccounts(t))' =
      /\ \A t \in Transfer:
        pc[t] \notin {"init"} <=> NonEmptyAccounts(t)
    BY DEF NonEmptyAccounts
<1>5 CreditTotal' = CreditTotal BY DEF CreditTotal
<1>6 DebitTotal' = DebitTotal BY DEF DebitTotal
<1>7 AmountPendingTotal' = AmountPendingTotal BY DEF AmountPendingTotal

<1>8 (Imbalance = 0)' = (Imbalance = 0) BY <1>5, <1>6, <1>7 DEF Imbalance

<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>8 DEF IndInv


THEOREM nextTerminating == ASSUME IndInv, Next, Terminating
PROVE IndInv'
<1> SUFFICES ASSUME IndInv, Terminating
    PROVE IndInv'
    BY DEF Next, Terminating
<1>1 UNCHANGED vars BY DEF Terminating
<1> QED BY <1>1, unchangedVarsProperty


THEOREM nextProperty == IndInv /\ Next => IndInv'
<1> SUFFICES ASSUME IndInv, Next
    PROVE IndInv'
    OBVIOUS
<1> USE DEF IndInv, Next, Terminating
<1>1 CASE ~Terminating
    <2> QED BY <1>1, nextNonTerminating
<1>2 CASE Terminating
    <2> QED BY <1>2, nextTerminating    
<1> QED BY <1>1, <1>2


THEOREM IndInvPreservedE == Spec => []IndInv
<1>1 IndInv /\ UNCHANGED vars => IndInv'
    BY unchangedVarsProperty
<1> QED BY PTL, initProperty, nextProperty, <1>1 DEF Spec

====
