---- MODULE MoneyTransfer_proofs ----
EXTENDS MoneyTransfer, MoneyTransferCommon, MoneyTransfer_proofsCommon,
FiniteSetsExt_theorems_ext, FiniteSetTheorems, TLAPS

LEMMA transPendingIsFinite == IsFiniteSet(transPending)
BY transSetIsFinite, FS_Subset, NTransferAssumption DEF transPending

LEMMA transAmountInNat == ASSUME TypeOK, NEW self \in Transfer
PROVE transAmount(self) \in Nat
BY DEF TypeOK, transAmount

LEMMA AmountPendingTotalInNat == ASSUME IndInv
PROVE AmountPendingTotal \in Nat
<1>1 IsFiniteSet(Transfer) BY transSetIsFinite
<1>2 IsFiniteSet({t \in Transfer : AmountIsPending(t)}) BY <1>1, FS_Subset
<1>3 IsFiniteSet(transPending) BY transPendingIsFinite
<1>4 \A t \in transPending: transAmount(t) \in Nat BY DEF transPending, transAmount, IndInv, TypeOK
<1> QED BY <1>3, <1>4, MapThenSumSetType DEF AmountPendingTotal

LEMMA transPendingAmountNat == ASSUME IndInv
PROVE \A am \in transPending: transAmount(am) \in Nat
BY DEF AmountIsPending, isTransKnown, transAmount, transPending, IndInv, TypeOK


LEMMA init_Imbalance == ASSUME Init
PROVE Imbalance = 0
<1> USE DEF Init
<1>1 CreditTotal = 0 BY MapThenSumSetEmpty DEF CreditTotal
<1>2 DebitTotal = 0 BY MapThenSumSetEmpty DEF DebitTotal
<1>3 AmountPendingTotal = 0
    BY MapThenSumSetEmpty DEF AmountPendingTotal, AmountIsPending, transPending, creditPrecond, isTransKnown
<1> QED BY <1>1, <1>2, <1>3 DEF Imbalance


THEOREM initProperty == ASSUME Init PROVE IndInv
<1> USE DEF Init, IndInv, TypeOK
<1>1 IsFiniteSet(credits) BY FS_EmptySet
<1>2 IsFiniteSet(debits) BY FS_EmptySet
<1>3 accounts \in [Transfer -> EAccounts] BY DEF EAccount, EmptyAccounts, EAccounts
<1>4 pcLabels BY DEF pcLabels, ProcSet
<1>5 \A t \in Transfer: pc[t] = "init" => initPrecond(t)
    BY DEF initPrecond, isTransKnown
<1>6 \A t \in Transfer:
        pc[t] \notin {"init"} <=> NonEmptyAccounts(t)
    BY DEF ProcSet, NonEmptyAccounts, EmptyAccounts
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, init_Imbalance


THEOREM retryDebit_AmountPendingTotal == ASSUME IndInv, NEW self \in Transfer, retryDebit(self)
PROVE AmountPendingTotal' = AmountPendingTotal
<1> USE DEF retryDebit, IndInv, TypeOK
<1>1 transPending' = transPending
    <2>1 self \in transPending BY DEF transPending, AmountIsPending, creditPrecond,
        debitPrecond, isTransKnown, pcLabels
    <2>2 self \in transPending' BY <2>1 DEF transPending, AmountIsPending, creditPrecond,
    isTransKnown, pcLabels
    <2> QED BY <2>1, <2>2 DEF pcLabels,
            transPending, AmountIsPending, creditPrecond
<1>2 \A t \in Transfer: transAmount(t)' = transAmount(t) BY DEF transAmount,
    creditPrecond, debitPrecond
<1> QED BY <1>1, <1>2 DEF transPending, transAmount, AmountIsPending, creditPrecond,
    isTransKnown, MapThenSumSet, MapThenFoldSet, AmountPendingTotal


THEOREM retryDebit_IndInv == ASSUME IndInv, NEW self \in Transfer, retryDebit(self)
PROVE IndInv'
<1> USE DEF IndInv, TypeOK, retryDebit
<1>1 pcLabels' BY DEF pcLabels
<1>2 Imbalance' = Imbalance BY retryDebit_AmountPendingTotal
    DEF Imbalance, creditPrecond, CreditTotal, DebitTotal
<1>3 Imbalance' = 0 BY <1>2
<1>4 \A t \in Transfer:
    (\/ accounts[t] = EmptyAccounts
     \/ DifferentAccounts(t) /\ NonEmptyAccounts(t))'
    BY DEF EmptyAccounts, DifferentAccounts, NonEmptyAccounts
<1>5 \A t \in Transfer: NonEmptyAccounts(t)' = NonEmptyAccounts(t)
    BY DEF NonEmptyAccounts
<1>6 \A t \in Transfer: pc'[t] = "init" => initPrecond(t)'
    BY DEF pcLabels
<1>7 \A t \in Transfer \ {self}: pc'[t] \notin {"init"} <=> pc[t] \notin {"init"}
    BY DEF pcLabels
<1>8 \A t \in Transfer: pc'[t] \notin {"init"} <=> NonEmptyAccounts(t)'
    BY <1>5, <1>7 DEF pcLabels
<1> QED BY <1>1, <1>3, <1>4, <1>6, <1>8

\* a copy of retryDebit_IndInv
THEOREM retryCredit_AmountPendingTotal == ASSUME IndInv, NEW self \in Transfer, retryCredit(self)
PROVE AmountPendingTotal' = AmountPendingTotal
<1> USE DEF retryCredit, IndInv, TypeOK
<1>1 transPending' = transPending
    <2>1 CASE creditPrecond(self)
        <3>1 self \in transPending BY <2>1 DEF transPending, AmountIsPending, creditPrecond,
            debitPrecond, isTransKnown, pcLabels
        <3>2 self \in transPending' BY <3>1 DEF transPending, AmountIsPending, creditPrecond,
        isTransKnown, pcLabels
        <3> QED BY <3>1, <3>2 DEF pcLabels,
                transPending, AmountIsPending, creditPrecond
    <2>2 CASE ~creditPrecond(self)
        <3>1 ~self \in transPending BY <2>2 DEF transPending, AmountIsPending, creditPrecond
        <3>2 ~(self \in transPending)' BY <2>2 DEF transPending, AmountIsPending, creditPrecond
        <3> QED BY <3>1, <3>2 DEF pcLabels,
                transPending, AmountIsPending, creditPrecond
    <2> QED BY <2>1, <2>2
<1>2 \A t \in Transfer: transAmount(t)' = transAmount(t) BY DEF transAmount,
    creditPrecond, debitPrecond
<1> QED BY <1>1, <1>2 DEF transPending, transAmount, AmountIsPending, creditPrecond,
    isTransKnown, MapThenSumSet, MapThenFoldSet, AmountPendingTotal

THEOREM retryCredit_IndInv == ASSUME IndInv, NEW self \in Transfer, retryCredit(self)
PROVE IndInv'
<1> USE DEF IndInv, TypeOK, retryCredit
<1>1 pcLabels' BY DEF pcLabels
<1>2 Imbalance' = Imbalance BY retryCredit_AmountPendingTotal
    DEF Imbalance, creditPrecond, CreditTotal, DebitTotal
<1>3 Imbalance' = 0 BY <1>2
<1>4 \A t \in Transfer:
    (\/ accounts[t] = EmptyAccounts
     \/ DifferentAccounts(t) /\ NonEmptyAccounts(t))'
    BY DEF EmptyAccounts, DifferentAccounts, NonEmptyAccounts
<1>5 \A t \in Transfer: NonEmptyAccounts(t)' = NonEmptyAccounts(t)
    BY DEF NonEmptyAccounts
<1>6 \A t \in Transfer: pc'[t] = "init" => initPrecond(t)'
    BY DEF pcLabels
<1>7 \A t \in Transfer \ {self}: pc'[t] \notin {"init"} <=> pc[t] \notin {"init"}
    BY DEF pcLabels
<1>8 \A t \in Transfer: pc'[t] \notin {"init"} <=> NonEmptyAccounts(t)'
    BY <1>5, <1>7 DEF pcLabels
<1> QED BY <1>1, <1>3, <1>4, <1>6, <1>8


THEOREM init_AmountPendingTotal == ASSUME IndInv, NEW self \in Transfer, init(self)
PROVE AmountPendingTotal' = AmountPendingTotal
<1>1 self \notin transPending BY DEF transPending, AmountIsPending, init
<1>2 ~AmountIsPending(self)' BY DEF AmountIsPending, creditPrecond, initPrecond, init, IndInv, TypeOK
<1>3 self \notin transPending' BY <1>2 DEF transPending
<1>4 transPending' = transPending BY <1>1, <1>3 DEF pcLabels,
    transPending, AmountIsPending, creditPrecond, isTransKnown, init, IndInv, TypeOK
<1>5 \A t \in transPending: transAmount(t)' = transAmount(t) BY
    DEF transPending, transAmount, AmountIsPending, init, IndInv, TypeOK
<1>6 \A t \in transPending: transAmount(t) \in Nat BY DEF init, IndInv, TypeOK,
    transAmount, transPending
<1>7 \A t \in transPending: transAmount(t)' \in Nat BY DEF init, IndInv, TypeOK, NNat,
    transAmount, transPending
<1>8 IsFiniteSet(transPending) BY transSetIsFinite, FS_Subset DEF transPending
<1>9 (CHOOSE iter :
          iter
          = [s \in SUBSET transPending |->
               IF s = {}
                 THEN 0
                 ELSE transAmount(CHOOSE x \in s : TRUE)
                      + iter[s \ {CHOOSE x \in s : TRUE}]])[transPending]
    = (CHOOSE iter :
          iter
          = [s \in SUBSET transPending |->
               IF s = {}
                 THEN 0
                 ELSE transAmount(CHOOSE x \in s : TRUE)'
                      + iter[s \ {CHOOSE x \in s : TRUE}]])[transPending]
    BY <1>5, <1>6, <1>7, <1>8, MapThenSumSetEqual DEF init, MapThenSumSet, MapThenFoldSet
<1>10 MapThenSumSet(transAmount, transPending)' = MapThenSumSet(transAmount, transPending)
    BY <1>4, <1>9 DEF MapThenSumSet, MapThenFoldSet, transAmount
<1> QED BY <1>10 DEF AmountPendingTotal


THEOREM init_IndInv == ASSUME IndInv, NEW self \in Transfer, init(self)
PROVE IndInv'
<1> USE DEF IndInv, TypeOK, init
<1>1 amount' \in [Transfer -> Nat] BY DEF NNat
<1>2 accounts'[self] \in EAccounts BY DEF EAccounts, EAccount
<1>3 accounts' \in [Transfer -> EAccounts] BY <1>2 DEF init
<1>4 pcLabels' BY DEF pcLabels
<1>5 Imbalance' = Imbalance BY init_AmountPendingTotal
    DEF Imbalance, creditPrecond, CreditTotal, DebitTotal
<1>6 Imbalance' = 0 BY <1>5
<1>7 Empty \notin Account BY EmptyAssumption, AccountAssumption
<1>8 (\/ accounts[self] = EmptyAccounts
      \/ DifferentAccounts(self) /\ NonEmptyAccounts(self))'
    BY <1>7 DEF DifferentAccounts, NonEmptyAccounts
<1>9 \A t \in Transfer:
    (\/ accounts[t] = EmptyAccounts
     \/ DifferentAccounts(t) /\ NonEmptyAccounts(t))'
    BY <1>8 DEF EmptyAccounts, DifferentAccounts, NonEmptyAccounts
<1>10 pc'[self] = "init" => initPrecond(self)' BY DEF initPrecond, isTransKnown
<1>11 \A t \in Transfer: pc'[t] = "init" => initPrecond(t)' BY <1>10 DEF pcLabels
<1>12 pc'[self] \notin {"init"} <=> NonEmptyAccounts(self)' BY <1>7 DEF NonEmptyAccounts, pcLabels
<1>13 \A t \in Transfer: pc'[t] \notin {"init"} <=> NonEmptyAccounts(t)'
    BY <1>12 DEF pcLabels, NonEmptyAccounts
<1> QED BY <1>1, <1>3, <1>4, <1>6, <1>9, <1>11, <1>13


LEMMA debit_DebitTotal_debitPrecond_success == ASSUME IndInv, NEW self \in Transfer, debit(self),
debitPrecond(self), ~(UNCHANGED debits)
PROVE DebitTotal' = DebitTotal + amount[self]
<1> DEFINE a == accounts[self].from
<1> DEFINE nadd == <<[a |-> a, t |-> self], amount[self]>>
<1> USE DEF IndInv, TypeOK, debitPrecond
<1>1 nadd \notin debits BY DEF isTransKnown, AT
<1>2 debits' = debits \cup {nadd} BY DEF debit
<1>3 \A nb \in debits: opAmount(nb) \in Nat BY DEF opAmount
<1>4 opAmount(nadd) \in Nat BY transAmountInNat DEF opAmount
<1>5 MapThenSumSet(opAmount, debits') =
    MapThenSumSet(opAmount, debits) + opAmount(nadd)
    BY <1>1, <1>2, <1>3, <1>4, MapThenSumSetAddElem
<1>6 DebitTotal' = DebitTotal + opAmount(nadd)
    BY <1>5 DEF DebitTotal
<1> QED BY <1>6 DEF opAmount


LEMMA debit_DebitTotal_notDebitPrecond_or_retryDebit == ASSUME IndInv, NEW self \in Transfer, debit(self),
~debitPrecond(self) \/ UNCHANGED debits
PROVE DebitTotal' = DebitTotal
BY DEF debit, DebitTotal


LEMMA debit_AmountPendingTotal_debitPrecond == ASSUME IndInv, NEW self \in Transfer, debit(self),
debitPrecond(self), ~(UNCHANGED debits)
PROVE AmountPendingTotal' = AmountPendingTotal + amount[self]
<1>1 transPending' = transPending \cup {self}
    BY DEF transPending, debit, AmountIsPending, isTransKnown, creditPrecond
<1> USE DEF IndInv, TypeOK
<1>2 self \notin transPending
    BY DEF transPending, AmountIsPending, isTransKnown, debitPrecond, creditPrecond, AT
<1>3 transAmount(self) = amount[self] BY DEF transAmount
<1>4 transAmount(self) \in Nat BY transAmountInNat
<1>5 IsFiniteSet(transPending) BY transPendingIsFinite
<1>6 \A t \in transPending: transAmount(t) \in Nat BY transPendingAmountNat
<1> HIDE DEF IndInv, TypeOK
<1>7 MapThenSumSet(transAmount, transPending') =
    MapThenSumSet(transAmount, transPending) + transAmount(self)
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, MapThenSumSetAddElem
<1>8 AmountPendingTotal' = MapThenSumSet(transAmount, transPending)' BY DEF AmountPendingTotal
<1>9 AmountPendingTotal' = MapThenSumSet(transAmount, transPending')
    BY <1>1 DEF debit, transPending, AmountIsPending, debitPrecond
<1>10 MapThenSumSet(transAmount, transPending') = MapThenSumSet(transAmount, transPending)'
    BY <1>8, <1>9
<1> QED BY <1>7, <1>10, <1>3 DEF AmountPendingTotal


LEMMA debit_AmountPendingTotal_notDebitPrecond_or_retryDebit == ASSUME IndInv, NEW self \in Transfer, debit(self),
~debitPrecond(self) \/ UNCHANGED debits
PROVE AmountPendingTotal' = AmountPendingTotal
<1>1 self \notin transPending
    BY DEF debit, transPending, AmountIsPending, creditPrecond, isTransKnown
<1>2 self \notin transPending'
    BY <1>1 DEF debit, transPending, AmountIsPending, debitPrecond, creditPrecond, IndInv, TypeOK, pcLabels,
        isTransKnown
<1>3 transPending' = transPending BY <1>1, <1>2 DEF debit
<1>4 MapThenSumSet(transAmount, transPending') = MapThenSumSet(transAmount, transPending) 
    BY <1>3 DEF debit, transAmount
<1>5 \A t \in transPending: accounts[t] = accounts[t]' BY <1>3 DEF debit, pcLabels,
    transPending, AmountIsPending, creditPrecond, isTransKnown
<1>6 (CHOOSE iter :
          iter
          = [s \in SUBSET transPending |->
               IF s = {}
                 THEN 0
                 ELSE amount[CHOOSE x \in s : TRUE]
                      + iter[s \ {CHOOSE x \in s : TRUE}]])[transPending]
    = (CHOOSE iter :
          iter
          = [s \in SUBSET transPending |->
               IF s = {}
                 THEN 0
                 ELSE amount[CHOOSE x \in s : TRUE]'
                      + iter[s \ {CHOOSE x \in s : TRUE}]])[transPending]
    BY <1>5 DEF debit, pcLabels, transPending, AmountIsPending, creditPrecond,
    isTransKnown
<1>7 MapThenSumSet(transAmount, transPending)' = MapThenSumSet(transAmount, transPending)
    BY <1>4, <1>6, <1>3 DEF debit, transAmount, MapThenSumSet, MapThenFoldSet
<1> QED BY <1>7 DEF AmountPendingTotal


LEMMA debit_Imbalance == ASSUME IndInv, NEW self \in Transfer, debit(self)
PROVE Imbalance' = Imbalance
<1>1 credits' = credits BY DEF debit
<1>2 CreditTotal' = CreditTotal
    BY <1>1 DEF CreditTotal
<1>3 CASE debitPrecond(self) /\ ~(UNCHANGED debits)
    <2>1 DebitTotal' = DebitTotal + amount[self] BY <1>3, debit_DebitTotal_debitPrecond_success
    <2>2 AmountPendingTotal' = AmountPendingTotal + amount[self] BY <1>3,
        debit_AmountPendingTotal_debitPrecond
    <2>3 AmountPendingTotal \in Nat BY AmountPendingTotalInNat, NTransferAssumption
    <2> QED BY <1>2, <2>1, <2>2, <2>3 DEF Imbalance, debit
<1>4 CASE ~debitPrecond(self) \/ UNCHANGED debits
    <2> QED BY <1>4, <1>2, debit_DebitTotal_notDebitPrecond_or_retryDebit,
        debit_AmountPendingTotal_notDebitPrecond_or_retryDebit DEF debit, Imbalance
<1> QED BY <1>3, <1>4


THEOREM debit_IndInv_common == ASSUME IndInv, NEW self \in Transfer, debit(self)
PROVE (
    /\ credits \in SUBSET (AT \X Nat)
    /\ IsFiniteSet(credits)
    /\ CommonIndInv)'
<1> USE DEF IndInv, TypeOK, CommonIndInv, debit
<1>1 pcLabels' BY DEF pcLabels
<1>2 \A t \in Transfer:
    \/ accounts'[t] = EmptyAccounts
    \/ DifferentAccounts(t)' /\ NonEmptyAccounts(t)'
    BY DEF EmptyAccounts, DifferentAccounts, NonEmptyAccounts
<1>3 \A t \in Transfer \ {self}: pc[t]' = pc[t]
    BY DEF pcLabels
<1>4 \A t \in Transfer: pc'[t] = "init" => initPrecond(t)'
    BY <1>3 DEF pcLabels
<1>5 \A t \in Transfer: NonEmptyAccounts(t)' = NonEmptyAccounts(t)
    BY DEF NonEmptyAccounts
<1>6 pc'[self] \notin {"init"} BY DEF pcLabels
<1>7 \A t \in Transfer \ {self}: pc'[t] \notin {"init"} <=> NonEmptyAccounts(t)'
    BY <1>5, <1>3
<1>8 \A t \in Transfer: pc'[t] \notin {"init"} <=> NonEmptyAccounts(t)'
    BY <1>5, <1>6, <1>7
<1> QED BY <1>1, <1>2, <1>4, <1>8, debit_Imbalance


THEOREM debit_IndInv == ASSUME IndInv, NEW self \in Transfer, debit(self)
PROVE IndInv'
<1> DEFINE a == accounts[self].from
<1> DEFINE nadd == <<[a |-> a, t |-> self], amount[self]>>
<1> USE DEF IndInv, TypeOK, CommonIndInv
<1>1 CASE debitPrecond(self) /\ ~(UNCHANGED debits)
    <2>1 debits' = debits \cup {nadd} BY <1>1 DEF debit
    <2>2 a \in EAccount BY DEF EAccounts
    <2>3 a # Empty BY DEF debit, NonEmptyAccounts
    <2>4 a \in Account BY <2>2, <2>3 DEF EAccount
    <2>5 nadd \in AT \X Nat BY <2>4, transAmountInNat DEF AT
    <2>6 debits' \in SUBSET (AT \X Nat)
        BY <2>1, <2>5
    <2>7 IsFiniteSet(debits)' BY <1>1, FS_AddElement DEF debit
    <2> QED BY <2>6, <2>7, <1>1, debit_IndInv_common, debit_Imbalance
<1>2 CASE ~debitPrecond(self) \/ UNCHANGED debits
    <2>1 debits' \in SUBSET (AT \X Nat) BY <1>2 DEF debit
    <2>2 IsFiniteSet(debits)' BY <1>2 DEF debit
    <2> QED BY <2>1, <2>2, <1>1, debit_IndInv_common, debit_Imbalance
<1> QED BY <1>1, <1>2


LEMMA credit_AmountPendingTotal_creditPrecond == ASSUME IndInv, NEW self \in Transfer, credit(self),
creditPrecond(self)
PROVE AmountPendingTotal' = AmountPendingTotal - amount[self]
<1>1 self \in transPending
    BY DEF credit, transPending, AmountIsPending
<1>2 ~AmountIsPending(self) BY DEF credit, creditPrecond, AmountIsPending,
    isTransKnown, creditPrecond
<1> USE DEF IndInv, TypeOK
<1>3 transPending' = transPending \ {self}
    BY <1>1, <1>2 DEF transPending
<1>4 transAmount(self) \in Nat BY transAmountInNat
<1>5 IsFiniteSet(transPending) BY transPendingIsFinite
<1>6 \A t \in transPending: transAmount(t) \in Nat BY transPendingAmountNat
<1> HIDE DEF IndInv, TypeOK
<1>7 MapThenSumSet(transAmount, transPending) =
    MapThenSumSet(transAmount, transPending') + transAmount(self)
    BY <1>1, <1>3, <1>4, <1>5, <1>6,  MapThenSumSetRemElem
    
<1>8 AmountPendingTotal' = MapThenSumSet(transAmount, transPending)' BY DEF AmountPendingTotal
<1>9 AmountPendingTotal' = MapThenSumSet(transAmount, transPending')
    BY DEF credit, transPending, AmountIsPending, isTransKnown, creditPrecond
<1>10 MapThenSumSet(transAmount, transPending') = MapThenSumSet(transAmount, transPending)'
    BY <1>8, <1>9
    
<1>11 MapThenSumSet(transAmount, transPending) \in Nat
    BY <1>5, <1>6, MapThenSumSetType
    
<1>12 IsFiniteSet(transPending') BY <1>3, <1>5, FS_RemoveElement
<1>13 \A t \in transPending': transAmount(t) \in Nat
    BY <1>3, <1>6
<1>14 MapThenSumSet(transAmount, transPending') \in Nat
    BY <1>12, <1>13, MapThenSumSetType

<1>15 MapThenSumSet(transAmount, transPending') = MapThenSumSet(transAmount, transPending) - transAmount(self)
    BY <1>7, <1>11, <1>4, <1>14
<1> QED BY <1>15, <1>10 DEF AmountPendingTotal, transAmount


\* practically a copy of init_AmountPendingTotal
THEOREM credit_AmountPendingTotal_notCreditPrecond == ASSUME IndInv, NEW self \in Transfer, credit(self),
~creditPrecond(self) \/ UNCHANGED credits
PROVE AmountPendingTotal' = AmountPendingTotal
<1>1 self \notin transPending BY DEF credit, pcLabels, transPending, AmountIsPending
<1>2 ~AmountIsPending(self)' BY <1>1 DEF credit, pcLabels, transPending
<1>3 self \notin transPending' BY <1>2 DEF transPending
<1>4 transPending' = transPending BY <1>1, <1>3 DEF credit, pcLabels, IndInv, TypeOK,
    transPending, AmountIsPending, creditPrecond, isTransKnown
<1>5 \A t \in transPending: transAmount(t)' = transAmount(t) BY DEF credit, transAmount, IndInv, TypeOK,
    creditPrecond, isTransKnown
<1>6 MapThenSumSet(transAmount, transPending') = MapThenSumSet(transAmount, transPending) BY <1>4, <1>5
<1>7 AmountPendingTotal' = MapThenSumSet(transAmount, transPending') BY <1>4, <1>5 DEF credit,
    transPending, transAmount, AmountIsPending, creditPrecond,
    isTransKnown, MapThenSumSet, MapThenFoldSet, AmountPendingTotal
<1> QED BY <1>6, <1>7 DEF AmountPendingTotal


\* practically a copy of debit_DebitTotal_debitPrecond
LEMMA credit_CreditTotal == ASSUME IndInv, NEW self \in Transfer, credit(self),
creditPrecond(self) /\ ~(UNCHANGED credits)
PROVE CreditTotal' = CreditTotal + amount[self]
<1> DEFINE a == accounts[self].to
<1> DEFINE nadd == <<[a |-> a, t |-> self], amount[self]>>
<1> USE DEF IndInv, TypeOK
<1>1 nadd \notin credits BY DEF isTransKnown, creditPrecond, AT
<1>2 credits' = credits \cup {nadd} BY DEF credit, AT
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
<1>1 debits' = debits BY DEF credit
<1>2 DebitTotal' = DebitTotal
    BY <1>1 DEF DebitTotal
<1>3 CASE creditPrecond(self) /\ ~(UNCHANGED credits)
    <2>1 CreditTotal' = CreditTotal + amount[self] BY <1>3, credit_CreditTotal
    <2>2 AmountPendingTotal' = AmountPendingTotal - amount[self] BY <1>3, credit_AmountPendingTotal_creditPrecond
    <2>3 amount[self] \in Nat BY DEF IndInv, TypeOK
    <2>4 \A c \in credits: opAmount(c) \in Nat BY DEF opAmount, IndInv, TypeOK
    <2>5 CreditTotal \in Nat BY <2>4, MapThenSumSetType DEF CreditTotal, IndInv, TypeOK
    <2>6 AmountPendingTotal \in Nat BY transPendingAmountNat, transPendingIsFinite, MapThenSumSetType DEF AmountPendingTotal
    <2>7 CreditTotal' + AmountPendingTotal' = CreditTotal + AmountPendingTotal BY <2>1, <2>2, <2>3, <2>5, <2>6
    <2>8 (CreditTotal' + AmountPendingTotal') - DebitTotal' = (CreditTotal + AmountPendingTotal) - DebitTotal BY <1>2, <2>7
    <2> QED BY <2>8, <1>2 DEF Imbalance, credit
<1>4 CASE ~creditPrecond(self) \/ UNCHANGED credits
    <2>1 AmountPendingTotal' = AmountPendingTotal BY <1>4, credit_AmountPendingTotal_notCreditPrecond
    <2>2 CreditTotal' = CreditTotal BY <2>1 DEF credit, CreditTotal
    <2> QED BY <1>2, <2>1, <2>2 DEF Imbalance
<1> QED BY <1>3, <1>4


\* practically a copy of debit_IndInv_common
THEOREM credit_IndInv_common == ASSUME IndInv, NEW self \in Transfer, credit(self)
PROVE (
    /\ debits \in SUBSET (AT \X Nat)
    /\ IsFiniteSet(debits)
    /\ CommonIndInv)'
<1> USE DEF IndInv, TypeOK, CommonIndInv, credit
<1>1 pcLabels' BY DEF pcLabels
<1>2 \A t \in Transfer:
    \/ accounts'[t] = EmptyAccounts
    \/ DifferentAccounts(t)' /\ NonEmptyAccounts(t)'
    BY DEF EmptyAccounts, DifferentAccounts, NonEmptyAccounts
<1>3 pc'[self] = "init" => initPrecond(self)' BY DEF pcLabels
<1>4 \A t \in Transfer: pc'[t] = "init" => initPrecond(t)'
    BY <1>3 DEF pcLabels
<1>5 \A t \in Transfer: NonEmptyAccounts(t)' = NonEmptyAccounts(t)
    BY DEF NonEmptyAccounts
<1>6 pc'[self] \notin {"init"} BY DEF pcLabels
<1>7 pc'[self] \notin {"init"} <=> NonEmptyAccounts(self)'
    BY <1>5, <1>6
<1>8 \A t \in Transfer \ {self}: pc'[t] \notin {"init"} <=> NonEmptyAccounts(t)'
    BY <1>5 DEF pcLabels
<1>9 \A t \in Transfer: pc'[t] \notin {"init"} <=> NonEmptyAccounts(t)'
    BY <1>7, <1>8
<1> QED BY <1>1, <1>2, <1>4, <1>9, credit_Imbalance


\* practically a copy of debit_IndInv
THEOREM credit_IndInv == ASSUME IndInv, NEW self \in Transfer, credit(self)
PROVE IndInv'
<1> DEFINE a == accounts[self].to
<1> DEFINE nadd == <<[a |-> a, t |-> self], amount[self]>>
<1> USE DEF IndInv, TypeOK, CommonIndInv
<1>1 CASE creditPrecond(self) /\ ~(UNCHANGED credits)
    <2>3 credits' = credits \cup {nadd} BY <1>1 DEF credit
    <2>4 a \in EAccount BY DEF EAccounts
    <2>5 a # Empty BY DEF credit, NonEmptyAccounts
    <2>6 a \in Account BY <2>4, <2>5 DEF EAccount
    <2>7 nadd \in AT \X Nat BY <2>6, transAmountInNat DEF AT
    <2>8 credits' \in SUBSET (AT \X Nat)
        BY <2>3, <2>7
    <2>9 IsFiniteSet(credits)' BY <1>1, FS_AddElement DEF credit
    <2> QED BY <2>8, <2>9, <1>1, credit_IndInv_common, credit_Imbalance
<1>2 CASE ~creditPrecond(self) \/ UNCHANGED credits
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
<1>3 CASE retryDebit(self) BY <1>3, retryDebit_IndInv
<1>4 CASE credit(self) BY <1>4, credit_IndInv
<1>5 CASE retryCredit(self) BY <1>5, retryCredit_IndInv
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF trans


THEOREM unchangedVarsProperty == IndInv /\ UNCHANGED vars => IndInv'
<1> SUFFICES ASSUME IndInv, UNCHANGED vars
    PROVE IndInv'
    OBVIOUS
<1> USE DEF vars
<1>1 TypeOK' = TypeOK BY DEF TypeOK, pcLabels
<1>2 (/\ \A t \in Transfer:
        \/ accounts[t] = EmptyAccounts
        \/ DifferentAccounts(t) /\ NonEmptyAccounts(t))' =
      /\ \A t \in Transfer:
        \/ accounts[t] = EmptyAccounts
        \/ DifferentAccounts(t) /\ NonEmptyAccounts(t)
    BY DEF DifferentAccounts, NonEmptyAccounts
<1>3 (/\ \A t \in Transfer: pc[t] = "init" => initPrecond(t))' = /\ \A t \in Transfer: pc[t] = "init" => initPrecond(t)
    BY DEF initPrecond
<1>4 (/\ \A t \in Transfer:
        pc[t] \notin {"init"} <=> NonEmptyAccounts(t))' =
      /\ \A t \in Transfer:
        pc[t] \notin {"init"} <=> NonEmptyAccounts(t)
    BY DEF NonEmptyAccounts
<1>5 CreditTotal' = CreditTotal BY DEF CreditTotal
<1>6 DebitTotal' = DebitTotal BY DEF DebitTotal
<1>7 \A t \in Transfer: transAmount(t)' = transAmount(t) BY DEF transAmount, creditPrecond, debitPrecond
<1>8 transPending' = transPending BY DEF transPending, AmountIsPending,
    creditPrecond, isTransKnown
<1>9 MapThenSumSet(transAmount, transPending) = MapThenSumSet(transAmount, transPending') BY <1>7, <1>8
<1>10 AmountPendingTotal' = MapThenSumSet(transAmount, transPending)' BY DEF AmountPendingTotal
<1>11 AmountPendingTotal' = MapThenSumSet(transAmount, transPending') BY DEF AmountPendingTotal,
    transAmount, transPending, AmountIsPending, creditPrecond, isTransKnown,
    MapThenSumSet, MapThenFoldSet
<1>12 AmountPendingTotal' = AmountPendingTotal BY <1>9, <1>10, <1>11 DEF AmountPendingTotal

<1>13 (Imbalance = 0)' = (Imbalance = 0) BY <1>5, <1>6, <1>12 DEF Imbalance
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>13 DEF IndInv


THEOREM nextProperty == IndInv /\ Next => IndInv'
<1> SUFFICES ASSUME IndInv, Next
    PROVE IndInv'
    OBVIOUS
<1> USE DEF IndInv, Next, Terminating
<1>1 CASE ~Terminating
    <2> QED BY <1>1, nextNonTerminating
<1>2 CASE Terminating
    <2> QED BY <1>2, unchangedVarsProperty 
<1> QED BY <1>1, <1>2


THEOREM IndInvPreserved == Spec => []IndInv
<1>1 IndInv /\ UNCHANGED vars => IndInv'
    BY unchangedVarsProperty
<1> QED BY PTL, initProperty, nextProperty, <1>1 DEF Spec

====
