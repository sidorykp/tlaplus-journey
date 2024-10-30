---- MODULE MoneyTransfer_proofs ----
EXTENDS MoneyTransfer, FiniteSetsExt_theorems, FiniteSetTheorems


LEMMA transAmountNat == ASSUME TypeOK, NEW self \in Transfer
PROVE transAmount(self) \in Nat
BY DEF TypeOK, transAmount


LEMMA transSetIsFinite == ASSUME NTransferAssumption
PROVE IsFiniteSet(Transfer)
<1>1 Transfer \in SUBSET (Nat) BY DEF Transfer
<1>2 \A t \in Transfer: t <= NTransfer BY DEF Transfer
<1> QED BY <1>1, <1>2, FS_BoundedSetOfNaturals DEF NNat


LEMMA init_Imbalance == ASSUME Init, NAccountAssumption
PROVE Imbalance = 0
<1> USE DEF Init, Account, Transfer
<1>1 CreditTotal = 0 BY MapThenSumSetEmpty DEF CreditTotal
<1>2 DebitTotal = 0 BY MapThenSumSetEmpty DEF DebitTotal
<1>3 AmountPendingTotal = 0
    BY MapThenSumSetEmpty DEF AmountPendingTotal, AmountIsPending, transPending, creditPrecond
<1> QED BY <1>1, <1>2, <1>3 DEF Imbalance


LEMMA debit_DebitTotal == ASSUME IndInv, NEW self \in Transfer, debit(self),
debitPrecond(self)
PROVE DebitTotal' = DebitTotal + transAmount(self)
<1> DEFINE a == accounts[self][1]
<1> DEFINE nadd == <<a, self, transAmount(self)>>
<1> USE DEF IndInv, TypeOK, debitPrecond
<1>1 nadd \notin debits BY DEF isTransKnown, isTransKnownToItem
<1>2 debits' = debits \cup {nadd} BY DEF debit
<1>3 \A nb \in debits: opAmount(nb) \in Nat BY DEF opAmount
<1>4 opAmount(nadd) \in Nat BY transAmountNat DEF opAmount
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
    BY DEF transPending, debit, AmountIsPending, isTransKnown
<1> USE DEF IndInv, TypeOK
<1>2 self \notin transPending
    BY DEF transPending, AmountIsPending, isTransKnown, isTransKnownToItem, debitPrecond, creditPrecond
<1>3 transAmount(self) \in Nat BY transAmountNat
<1>4 IsFiniteSet(transPending) BY transSetIsFinite, FS_Subset DEF transPending
<1>5 \A am \in transPending: transAmount(am) \in Nat
    BY DEF AmountIsPending, isTransKnown, transAmount, transPending
<1> HIDE DEF IndInv, TypeOK
<1>6 MapThenSumSet(transAmount, transPending') =
    MapThenSumSet(transAmount, transPending) + transAmount(self)
    BY <1>1, <1>2, <1>3, <1>4, <1>5, MapThenSumSetAddElem
<1>7 AmountPendingTotal' = MapThenSumSet(transAmount, transPending)' BY DEF AmountPendingTotal
<1>8 AmountPendingTotal' = MapThenSumSet(transAmount, transPending') BY DEF debit, transPending, AmountIsPending
<1>9 MapThenSumSet(transAmount, transPending') = MapThenSumSet(transAmount, transPending)'
    BY <1>7, <1>8
<1> QED BY <1>6, <1>9 DEF AmountPendingTotal


LEMMA debit_CreditTotal == ASSUME IndInv, NEW self \in Transfer, debit(self)
PROVE CreditTotal' = CreditTotal
PROOF BY DEF IndInv, debit


LEMMA debit_Imbalance == ASSUME IndInv, NEW self \in Transfer, debit(self)
PROVE Imbalance' = Imbalance
<1>1 CASE debitPrecond(self)
    <2> QED BY debit_DebitTotal, debit_CreditTotal, debit_AmountPendingTotal DEF debit, Imbalance
<1>2 CASE ~debitPrecond(self)
    <2> QED BY DEF debit, Imbalance
<1> QED BY <1>1, <1>2


LEMMA ASSUME IndInv, NEW self \in Transfer, debit(self),
NEW a, a = accounts[self][1],
debitPrecond(self)
PROVE Cardinality({d \in debits': isTransKnownToItem(self, a, d)}) \in 0..1
<1> USE DEF IndInv, TypeOK
<1> DEFINE nadd == <<a, self, transAmount(self)>>
<1> DEFINE selfDebit == {d \in debits: isTransKnownToItem(self, a, d)}
<1> DEFINE selfDebitNext == {d \in debits': isTransKnownToItem(self, a, d)}
<1>1 selfDebit = {} BY DEF isTransKnown, isTransKnownToItem, debitPrecond
<1>2 selfDebitNext = {nadd} BY <1>1 DEF debit, debitPrecond, isTransKnown, isTransKnownToItem
<1>3 Cardinality(selfDebit) = 0 BY <1>1, FS_EmptySet
<1>4 Cardinality(selfDebitNext) = 1 BY <1>2, FS_Singleton
<1> QED BY <1>3, <1>4


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
