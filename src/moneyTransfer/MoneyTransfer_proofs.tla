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
<1>1 \A a \in Account, t \in Transfer: Cardinality({c \in credits: isTransKnownToItem(t, a, c)}) \in 0..1
    BY FS_EmptySet
<1>2 \A a \in Account, t \in Transfer: Cardinality({d \in debits: isTransKnownToItem(t, a, d)}) \in 0..1
    BY FS_EmptySet
<1>3 IsFiniteSet(credits) BY FS_EmptySet
<1>4 IsFiniteSet(debits) BY FS_EmptySet
<1>5 accounts \in [Transfer -> EAccounts] BY DEF EAccount, EmptyAccounts, EAccounts
<1>6 pc \in [Transfer -> {"Done","init","debit","credit", "crash"}] BY DEF ProcSet
<1>7 \A t \in Transfer: pc[t] = "init" => initPrecond(t)
    BY DEF initPrecond, isTransKnown, isTransKnownToItem
<1>8 \A t \in Transfer:
        pc[t] \notin {"init"} <=> NonEmptyAccounts(t)
    BY DEF ProcSet, NonEmptyAccounts, EmptyAccounts
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, init_Imbalance


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


LEMMA debit_AmountPendingTotal == ASSUME IndInv, NEW self \in Transfer, debit(self),
debitPrecond(self)
PROVE AmountPendingTotal' = AmountPendingTotal + transAmount(self)
<1>1 transPending' = transPending \cup {self}
    BY DEF transPending, debit, AmountIsPending, isTransKnown, debitPrecond, isTransKnownToItem,
    AT, creditPrecond, transAmount, EAccounts
<1> USE DEF IndInv, TypeOK
<1>2 self \notin transPending
    BY DEF transPending, AmountIsPending, isTransKnown, isTransKnownToItem, debitPrecond, creditPrecond, AT
<1>3 transAmount(self) \in Nat BY transAmountInNat
<1>4 IsFiniteSet(transPending) BY transSetIsFinite, FS_Subset, NTransferAssumption DEF transPending
<1>5 \A am \in transPending: transAmount(am) \in Nat
    BY DEF AmountIsPending, isTransKnown, transAmount, transPending
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
        DEF debit, Imbalance, debitPrecond, isTransKnown, isTransKnownToItem, CreditTotal
<1>2 CASE ~debitPrecond(self)
    <2> QED BY DEF debit, Imbalance, debitPrecond, CreditTotal
<1> QED BY <1>1, <1>2


LEMMA debit_debitIsFinite == ASSUME IndInv, NEW self \in Transfer, debit(self)
PROVE IsFiniteSet(debits)'
<1> USE DEF IndInv, TypeOK
<1>1 CASE debitPrecond(self) BY FS_AddElement DEF debit
<1>2 CASE ~debitPrecond(self)
    <2>1 IsFiniteSet(debits) OBVIOUS
    <2> QED BY <1>2, <2>1 DEF debit
<1> QED BY <1>1, <1>2


THEOREM nextNonTerminating == ASSUME IndInv, Next, ~Terminating
PROVE IndInv'
<1> SUFFICES ASSUME IndInv, NEW self \in Transfer, trans(self)
    PROVE IndInv'
    BY DEF Next, trans
<1>1 CASE init(self)
    <2> QED OMITTED
<1>2 CASE debit(self)
    <2> QED OMITTED
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
