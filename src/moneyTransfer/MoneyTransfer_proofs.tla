---- MODULE MoneyTransfer_proofs ----
EXTENDS MoneyTransfer, FiniteSetsExt_theorems, FiniteSetTheorems

ASSUME NTransferAssumption == NTransfer \in NNat

ASSUME NAccountAssumption == NAccount \in NNat

ASSUME NAvailAssumption == NAvail \in NNat

ASSUME EmptyAssumption == Empty = 0

LEMMA transAmountInNat == ASSUME TypeOK, NEW self \in Transfer
PROVE transAmount(self) \in Nat
BY DEF TypeOK, transAmount


LEMMA transSetIsFinite == ASSUME NTransferAssumption
PROVE IsFiniteSet(Transfer)
<1>1 Transfer \in SUBSET (Nat) BY DEF Transfer
<1>2 \A t \in Transfer: t <= NTransfer BY DEF Transfer
<1> QED BY <1>1, <1>2, FS_BoundedSetOfNaturals DEF NNat


LEMMA init_Imbalance == ASSUME Init
PROVE Imbalance = 0
<1> USE DEF Init, Account, Transfer
<1>1 CreditTotal = 0 BY MapThenSumSetEmpty DEF CreditTotal
<1>2 DebitTotal = 0 BY MapThenSumSetEmpty DEF DebitTotal
<1>3 AmountPendingTotal = 0
    BY MapThenSumSetEmpty DEF AmountPendingTotal, AmountIsPending, transPending, creditPrecond, isTransKnown
<1> QED BY <1>1, <1>2, <1>3 DEF Imbalance


THEOREM ASSUME Init
PROVE IndInv
<1> USE DEF Init, IndInv, TypeOK
<1>1 IsFiniteSet(credits) BY FS_EmptySet
<1>2 IsFiniteSet(debits) BY FS_EmptySet
<1>3 accounts \in [Transfer -> EAccounts] BY DEF EAccount, EmptyAccounts, EAccounts
<1>4 pcLabels BY DEF pcLabels, ProcSet
<1>5 \A t \in Transfer: pc[t] = "init" => initPrecond(t)
    BY DEF initPrecond, isTransKnown, isTransKnownToItem
<1>6 \A t \in Transfer:
        pc[t] \notin {"init"} <=> NonEmptyAccounts(t)
    BY DEF ProcSet, NonEmptyAccounts, EmptyAccounts
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, init_Imbalance


LEMMA debit_DebitTotal == ASSUME IndInv, NEW self \in Transfer, debit(self),
debitPrecond(self)
PROVE DebitTotal' = DebitTotal + transAmount(self)
<1> DEFINE a == accounts[self].from
<1> DEFINE nadd == <<[a |-> a, t |-> self], transAmount(self)>>
<1> USE DEF IndInv, TypeOK, debitPrecond
<1>1 nadd \notin debits BY DEF isTransKnown, isTransKnownToItem, AT
<1>2 debits' = debits \cup {nadd} BY DEF debit
<1>3 \A nb \in debits: opAmount(nb) \in Nat BY DEF opAmount
<1>4 opAmount(nadd) \in Nat BY transAmountInNat DEF opAmount
<1>5 MapThenSumSet(opAmount, debits') =
    MapThenSumSet(opAmount, debits) + opAmount(nadd)
    BY <1>1, <1>2, <1>3, <1>4, MapThenSumSetAddElem
<1>6 DebitTotal' = DebitTotal + opAmount(nadd)
    BY <1>5 DEF DebitTotal
<1> QED BY <1>6 DEF opAmount


LEMMA transPendingIsFinite == IsFiniteSet(transPending)
BY transSetIsFinite, FS_Subset, NTransferAssumption DEF transPending

LEMMA transPendingAmountNat == ASSUME IndInv
PROVE \A am \in transPending: transAmount(am) \in Nat
BY DEF AmountIsPending, isTransKnown, transAmount, transPending, IndInv, TypeOK


LEMMA debit_AmountPendingTotal == ASSUME IndInv, NEW self \in Transfer, debit(self),
debitPrecond(self)
PROVE AmountPendingTotal' = AmountPendingTotal + transAmount(self)
<1>1 transPending' = transPending \cup {self}
    BY DEF transPending, debit, AmountIsPending, isTransKnown, debitPrecond, isTransKnownToItem,
    AT, creditPrecond, transAmount, EAccounts, pcLabels
<1> USE DEF IndInv, TypeOK
<1>2 self \notin transPending
    BY DEF transPending, AmountIsPending, isTransKnown, isTransKnownToItem, debitPrecond, creditPrecond, AT
<1>3 transAmount(self) \in Nat BY transAmountInNat
<1>4 IsFiniteSet(transPending) BY transPendingIsFinite
<1>5 \A t \in transPending: transAmount(t) \in Nat BY transPendingAmountNat
<1> HIDE DEF IndInv, TypeOK
<1>6 MapThenSumSet(transAmount, transPending') =
    MapThenSumSet(transAmount, transPending) + transAmount(self)
    BY <1>1, <1>2, <1>3, <1>4, <1>5, MapThenSumSetAddElem
<1>7 AmountPendingTotal' = MapThenSumSet(transAmount, transPending)' BY DEF AmountPendingTotal
<1>8 AmountPendingTotal' = MapThenSumSet(transAmount, transPending')
    BY DEF debit, transPending, AmountIsPending
<1>9 MapThenSumSet(transAmount, transPending') = MapThenSumSet(transAmount, transPending)'
    BY <1>7, <1>8
<1> QED BY <1>6, <1>9 DEF AmountPendingTotal


LEMMA debit_Imbalance == ASSUME IndInv, NEW self \in Transfer, debit(self)
PROVE Imbalance' = Imbalance
<1>1 CASE debitPrecond(self)
    <2> QED BY debit_DebitTotal, debit_AmountPendingTotal
        DEF debit, Imbalance, debitPrecond, isTransKnown, isTransKnownToItem, CreditTotal, pcLabels
<1>2 CASE ~debitPrecond(self)
    <2> QED BY DEF debit, Imbalance, debitPrecond, CreditTotal, pcLabels
<1> QED BY <1>1, <1>2


THEOREM debit_IndInv_common == ASSUME IndInv, NEW self \in Transfer, debit(self)
PROVE (
    /\ credits \in SUBSET (AT \X Nat)
    /\ IsFiniteSet(credits)
    /\ amount \in [Transfer -> Nat]
    /\ accounts \in [Transfer -> EAccounts]
    /\ pcLabels
    /\ Imbalance = 0
    /\ \A t \in Transfer:
        \/ accounts[t] = EmptyAccounts
        \/ DifferentAccounts(t) /\ NonEmptyAccounts(t)
    /\ \A t \in Transfer: pc[t] = "init" => initPrecond(t)
    /\ \A t \in Transfer:
        pc[t] \notin {"init"} <=> NonEmptyAccounts(t))'
<1>1 credits' \in SUBSET (AT \X Nat) BY DEF debit
<1>2 IsFiniteSet(credits)' BY DEF debit
<1>3 amount' \in [Transfer -> Nat] BY DEF debit, IndInv
<1>4 accounts' \in [Transfer -> EAccounts] BY DEF debit
<1>5 pcLabels' BY DEF debit, pcLabels, ProcSet
<1>6 \A t \in Transfer:
    \/ accounts'[t] = EmptyAccounts
    \/ DifferentAccounts(t)' /\ NonEmptyAccounts(t)'
    BY DEF debit, EmptyAccounts, DifferentAccounts, NonEmptyAccounts

<1>7 pc' = [pc EXCEPT ![self] = "crash"] BY DEF debit
<1>8 pc'[self] = "crash" BY <1>7 DEF pcLabels, IndInv, TypeOK
<1>9 pc'[self] = "init" => initPrecond(self)' BY <1>8
<1>10 \A t \in Transfer \ {self}: pc[t]' = pc[t]
    BY <1>7 DEF pcLabels, IndInv, TypeOK
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
<1>17 pc'[self] \notin {"init"} BY <1>8
<1>18 pc'[self] \notin {"init"} <=> NonEmptyAccounts(self)'
    BY <1>14, <1>15, <1>16, <1>17

<1>19 \A t \in Transfer \ {self}: pc'[t] \notin {"init"} <=> pc[t] \notin {"init"}
    BY <1>10
<1>20 \A t \in Transfer \ {self}: pc'[t] \notin {"init"} <=> NonEmptyAccounts(t)'
    BY <1>12, <1>13, <1>19

<1>21 \A t \in Transfer: pc'[t] \notin {"init"} <=> NonEmptyAccounts(t)'
    BY <1>18, <1>20

<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>11, <1>21, debit_Imbalance DEF IndInv


THEOREM debit_IndInv == ASSUME IndInv, NEW self \in Transfer, debit(self)
PROVE IndInv'
<1> DEFINE a == accounts[self].from
<1> DEFINE nadd == <<[a |-> a, t |-> self], transAmount(self)>>
<1> USE DEF IndInv, TypeOK
<1>1 CASE debitPrecond(self)
    <2>3 debits' = debits \cup {nadd} BY <1>1 DEF debit
    <2>4 a \in EAccount BY DEF EAccounts
    <2>5 a # Empty BY DEF debit, NonEmptyAccounts
    <2>6 a \in Account BY <2>4, <2>5 DEF EAccount
    <2>7 nadd \in AT \X Nat BY <2>6, transAmountInNat DEF AT
    <2>8 debits' \in SUBSET (AT \X Nat)
        BY <2>3, <2>7
    <2>9 IsFiniteSet(debits)' BY <1>1, FS_AddElement DEF debit
    <2> QED BY <2>8, <2>9, <1>1, debit_IndInv_common, debit_Imbalance
<1>2 CASE ~debitPrecond(self)
    <2>3 debits' \in SUBSET (AT \X Nat) BY <1>2 DEF debit
    <2>4 IsFiniteSet(debits)' BY <1>2 DEF debit
    <2> QED BY <2>3, <2>4, <1>1, debit_IndInv_common, debit_Imbalance
<1> QED BY <1>1, <1>2


LEMMA credit_AmountPendingTotal == ASSUME IndInv, NEW self \in Transfer, credit(self),
creditPrecond(self)
PROVE AmountPendingTotal' = AmountPendingTotal - transAmount(self)
<1> USE DEF IndInv, TypeOK
<1>1 self \in transPending
    BY DEF credit, transPending, AmountIsPending
<1>2 transPending' = transPending \ {self}
    BY DEF transPending, credit, AmountIsPending, isTransKnown, creditPrecond, isTransKnownToItem,
    AT, transAmount, EAccounts, pcLabels
<1>3 transAmount(self) \in Nat BY transAmountInNat
<1>4 IsFiniteSet(transPending) BY transPendingIsFinite
<1>5 \A t \in transPending: transAmount(t) \in Nat BY transPendingAmountNat
<1> HIDE DEF IndInv, TypeOK
<1>6 MapThenSumSet(transAmount, transPending) =
    MapThenSumSet(transAmount, transPending') + transAmount(self)
    BY <1>1, <1>2, <1>3, <1>4, <1>5, MapThenSumSetRemElem
    
<1>7 AmountPendingTotal' = MapThenSumSet(transAmount, transPending)' BY DEF AmountPendingTotal
<1>8 AmountPendingTotal' = MapThenSumSet(transAmount, transPending')
    BY DEF credit, transPending, AmountIsPending
<1>9 MapThenSumSet(transAmount, transPending') = MapThenSumSet(transAmount, transPending)'
    BY <1>7, <1>8
    
<1>10 MapThenSumSet(transAmount, transPending) \in Nat
    BY <1>4, <1>5, MapThenSumSetType
    
<1>11 IsFiniteSet(transPending') BY <1>2, <1>4, FS_RemoveElement
<1>12 \A t \in transPending': transAmount(t) \in Nat
    BY <1>2, <1>5
<1>13 MapThenSumSet(transAmount, transPending') \in Nat
    BY <1>11, <1>12, MapThenSumSetType

<1>14 MapThenSumSet(transAmount, transPending') = MapThenSumSet(transAmount, transPending) - transAmount(self)
    BY <1>6, <1>10, <1>3, <1>13
<1> QED BY <1>14, <1>9 DEF AmountPendingTotal


LEMMA credit_CreditTotal == ASSUME IndInv, NEW self \in Transfer, credit(self),
creditPrecond(self)
PROVE CreditTotal' = CreditTotal + transAmount(self)
<1> DEFINE a == accounts[self].to
<1> DEFINE nadd == <<[a |-> a, t |-> self], transAmount(self)>>
<1> USE DEF IndInv, TypeOK, creditPrecond
<1>1 nadd \notin credits BY DEF isTransKnown, isTransKnownToItem, AT
<1>2 credits' = credits \cup {nadd} BY DEF credit
<1>3 \A nb \in credits: opAmount(nb) \in Nat BY DEF opAmount
<1>4 opAmount(nadd) \in Nat BY transAmountInNat DEF opAmount
<1>5 MapThenSumSet(opAmount, credits') =
    MapThenSumSet(opAmount, credits) + opAmount(nadd)
    BY <1>1, <1>2, <1>3, <1>4, MapThenSumSetAddElem
<1>6 CreditTotal' = CreditTotal + opAmount(nadd)
    BY <1>5 DEF CreditTotal
<1> QED BY <1>6 DEF opAmount


LEMMA credit_Imbalance == ASSUME IndInv, NEW self \in Transfer, credit(self)
PROVE Imbalance' = Imbalance
<1>1 CASE creditPrecond(self)
    <2> QED BY credit_CreditTotal, credit_AmountPendingTotal
        DEF credit, Imbalance, creditPrecond, isTransKnown, isTransKnownToItem, CreditTotal, pcLabels
<1>2 CASE ~creditPrecond(self)
    <2> QED BY DEF credit, Imbalance, creditPrecond, CreditTotal, pcLabels
<1> QED BY <1>1, <1>2


THEOREM nextNonTerminating == ASSUME IndInv, Next, ~Terminating
PROVE IndInv'
<1> SUFFICES ASSUME IndInv, NEW self \in Transfer, trans(self)
    PROVE IndInv'
    BY DEF Next, trans
<1>1 CASE init(self)
    <2> QED OMITTED
<1>2 CASE debit(self) BY debit_IndInv DEF debit
<1>3 CASE crash(self)
    <2> QED OMITTED
<1>4 CASE credit(self)
    <2> QED OMITTED
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF trans


THEOREM nextTerminating == ASSUME IndInv, Next, Terminating
PROVE IndInv'
<1> QED OMITTED


THEOREM ASSUME IndInv, Next
PROVE IndInv'
<1> USE DEF IndInv, Next, Terminating
<1>1 CASE ~Terminating
    <2> QED BY <1>1, nextNonTerminating
<1>2 CASE Terminating
    <2> QED BY <1>2, nextTerminating    
<1> QED BY <1>1, <1>2
====
