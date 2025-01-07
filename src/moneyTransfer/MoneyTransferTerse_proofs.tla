---- MODULE MoneyTransferTerse_proofs ----
EXTENDS MoneyTransferTerse, MoneyTransfer_proofsCommon, FiniteSetsExt_theorems_ext, FiniteSetTheorems, TLAPS

LEMMA transAmountInNat == ASSUME TypeOK, NEW self \in Transfer
PROVE transAmount(self) \in Nat
BY DEF TypeOK, transAmount

LEMMA transPendingIsFinite ==
IsFiniteSet(transPending) BY transSetIsFinite, FS_Subset DEF transPending

LEMMA transPendingAmountNat == ASSUME IndInv
PROVE \A am \in transPending: transAmount(am) \in Nat
BY DEF AmountIsPending, transAmount, transPending, IndInv, TypeOK

LEMMA AmountPendingTotalInNat == ASSUME IndInv
PROVE AmountPendingTotal \in Nat
<1>1 IsFiniteSet(Transfer) BY transSetIsFinite
<1>2 IsFiniteSet({t \in Transfer : AmountIsPending(t)}) BY <1>1, FS_Subset
<1>3 IsFiniteSet(transPending) BY transPendingIsFinite
<1>4 \A t \in transPending: transAmount(t) \in Nat BY transPendingAmountNat
<1> QED BY <1>3, <1>4, MapThenSumSetType DEF AmountPendingTotal

LEMMA init_Imbalance == ASSUME Init
PROVE Imbalance = 0
<1> USE DEF Init
<1>1 CreditTotal = 0 BY MapThenSumSetEmpty DEF CreditTotal
<1>2 DebitTotal = 0 BY MapThenSumSetEmpty DEF DebitTotal
<1>3 AmountPendingTotal = 0
    BY MapThenSumSetEmpty DEF AmountPendingTotal, AmountIsPending, transPending,
    creditPrecond, isTransKnown
<1> QED BY <1>1, <1>2, <1>3 DEF Imbalance


THEOREM initProperty == ASSUME Init PROVE IndInv
<1> USE DEF Init, IndInv, TypeOK
<1>1 IsFiniteSet(credits) BY FS_EmptySet
<1>2 IsFiniteSet(debits) BY FS_EmptySet
<1>3 accounts \in [Transfer -> EAccounts] BY DEF EAccounts, EAccount, EmptyAccounts
<1>4 pcLabels BY DEF pcLabels, ProcSet
<1>5 \A t \in Transfer: pc[t] \in {"choose_accounts", "choose_amount"} => debitPrecond(t)
    BY DEF debitPrecond, isTransKnown
<1>6 \A t \in Transfer:
        pc[t] \notin {"choose_accounts"} <=> NonEmptyAccounts(t)
    BY DEF NonEmptyAccounts, EmptyAccounts, ProcSet
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, init_Imbalance


THEOREM choose_accounts_AmountPendingTotal == ASSUME IndInv, NEW self \in Transfer, choose_accounts(self)
PROVE AmountPendingTotal' = AmountPendingTotal
<1>1 self \notin transPending BY DEF transPending, AmountIsPending, choose_accounts
<1>2 ~AmountIsPending(self)' BY DEF AmountIsPending, creditPrecond, debitPrecond, choose_accounts, IndInv, TypeOK
<1>3 self \notin transPending' BY <1>2 DEF transPending
<1>4 transPending' = transPending BY <1>1, <1>3 DEF pcLabels,
    transPending, AmountIsPending, creditPrecond, isTransKnown, choose_accounts, IndInv, TypeOK
<1>5 \A t \in transPending: amount[t]' = amount[t] BY
    DEF transPending, AmountIsPending, choose_accounts, IndInv, TypeOK
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
    BY <1>5 DEF choose_accounts
<1>7 MapThenSumSet(transAmount, transPending)' = MapThenSumSet(transAmount, transPending)
    BY <1>4, <1>6 DEF MapThenSumSet, MapThenFoldSet, transAmount
<1> QED BY <1>7 DEF AmountPendingTotal


THEOREM choose_accounts_IndInv == ASSUME IndInv, NEW self \in Transfer, choose_accounts(self)
PROVE IndInv'
<1> USE DEF choose_accounts, IndInv, TypeOK
<1>1 accounts' \in [Transfer -> EAccounts] BY DEF EAccounts, EAccount, EmptyAccounts
<1>2 pcLabels' BY DEF pcLabels
<1>3 NonEmptyAccounts(self)'
    <2>1 accounts[self]'.from \in Account OBVIOUS
    <2>2 accounts[self]'.to \in Account OBVIOUS
    <2>3 accounts[self]'.from # Empty BY <2>1, EmptyAssumption, NAccountAssumption, AccountAssumption DEF NNat
    <2>4 accounts[self]'.to # Empty BY <2>2, EmptyAssumption, NAccountAssumption, AccountAssumption DEF NNat
    <2> QED BY <2>3, <2>4 DEF NonEmptyAccounts
<1>4 \A t \in Transfer:
        \/ accounts[t]' = EmptyAccounts
        \/ (DifferentAccounts(t) /\ NonEmptyAccounts(t))'
    BY <1>1, <1>3 DEF DifferentAccounts, NonEmptyAccounts
<1>5 \A t \in Transfer: pc[t]' \in {"choose_accounts", "choose_amount"} => debitPrecond(t)'
    BY DEF pcLabels, debitPrecond, isTransKnown
<1>6 \A t \in Transfer: (pc[t] \notin {"choose_accounts"})' <=> NonEmptyAccounts(t)'
    BY <1>3 DEF pcLabels, NonEmptyAccounts
<1>7 TypeOK' BY <1>1, <1>2
<1>8 Imbalance' = 0
    <2>1 AmountPendingTotal' = AmountPendingTotal BY choose_accounts_AmountPendingTotal
    <2>2 DebitTotal' = DebitTotal BY DEF DebitTotal, opAmount, MapThenSumSet, MapThenFoldSet
    <2>3 CreditTotal' = CreditTotal BY DEF CreditTotal, opAmount, MapThenSumSet, MapThenFoldSet
    <2>4 Imbalance' = Imbalance BY <2>1, <2>2, <2>3 DEF Imbalance
    <2> QED BY <2>4
<1> QED BY <1>7, <1>4, <1>5, <1>6, <1>8


THEOREM choose_amount_AmountPendingTotal == ASSUME IndInv, NEW self \in Transfer, choose_amount(self)
PROVE AmountPendingTotal' = AmountPendingTotal
<1>1 self \notin transPending BY DEF transPending, AmountIsPending, choose_amount
<1>2 ~AmountIsPending(self)' BY DEF AmountIsPending, creditPrecond, debitPrecond, choose_amount, IndInv, TypeOK,
    pcLabels, isTransKnown, AT
<1>3 self \notin transPending' BY <1>2 DEF transPending
<1>4 transPending' = transPending BY <1>1, <1>3 DEF pcLabels,
    transPending, AmountIsPending, creditPrecond, isTransKnown, choose_amount, IndInv, TypeOK
<1>5 \A t \in transPending: transAmount(t)' = transAmount(t) BY
    DEF transPending, transAmount, AmountIsPending, choose_amount, IndInv, TypeOK
<1>6 \A t \in transPending: transAmount(t) \in Nat BY DEF choose_amount, IndInv, TypeOK,
    transAmount, transPending
<1>7 \A t \in transPending: transAmount(t)' \in Nat BY DEF choose_amount, IndInv, TypeOK, NNat,
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
    BY <1>5, <1>6, <1>7, <1>8, MapThenSumSetEqual DEF choose_amount, MapThenSumSet, MapThenFoldSet
<1>10 MapThenSumSet(transAmount, transPending)' = MapThenSumSet(transAmount, transPending)
    BY <1>4, <1>9 DEF MapThenSumSet, MapThenFoldSet, transAmount
<1> QED BY <1>10 DEF AmountPendingTotal


THEOREM choose_amount_IndInv == ASSUME IndInv, NEW self \in Transfer, choose_amount(self)
PROVE IndInv'
<1> USE DEF choose_amount, IndInv, TypeOK
<1>1 accounts' \in [Transfer -> EAccounts] BY DEF EAccounts, EAccount, EmptyAccounts
<1>2 pcLabels' BY DEF pcLabels
<1>3 amount' \in [Transfer -> Nat] BY DEF NNat
<1>4 \A t \in Transfer:
        \/ accounts[t]' = EmptyAccounts
        \/ (DifferentAccounts(t) /\ NonEmptyAccounts(t))'
    BY DEF DifferentAccounts, NonEmptyAccounts
<1>5 \A t \in Transfer: pc[t]' \in {"choose_accounts", "choose_amount"} => debitPrecond(t)'
    BY DEF pcLabels, debitPrecond, isTransKnown
<1>6 \A t \in Transfer: (pc[t] \notin {"choose_accounts"})' <=> NonEmptyAccounts(t)'
    BY DEF pcLabels, NonEmptyAccounts
<1>7 TypeOK' BY <1>1, <1>2, <1>3
<1>8 Imbalance' = 0
    <2>1 AmountPendingTotal' = AmountPendingTotal BY choose_amount_AmountPendingTotal
    <2>2 DebitTotal' = DebitTotal
        <3>1 ~\E a \in Account: isTransKnown(self, a, debits) BY DEF debitPrecond
        <3>2 debits' = debits OBVIOUS
        <3>3 \A d \in debits: opAmount(d)' = opAmount(d) BY <3>1 DEF opAmount, isTransKnown, AT
        <3>4 \A d \in debits: opAmount(d) \in Nat BY DEF opAmount, AT
        <3>5 \A d \in debits: opAmount(d)' \in Nat BY DEF opAmount, AT, NNat
        <3>6 IsFiniteSet(debits) OBVIOUS
        <3>7 (CHOOSE iter :
                  iter
                  = [s \in SUBSET debits |->
                       IF s = {}
                         THEN 0
                         ELSE opAmount(CHOOSE x \in s : TRUE)
                              + iter[s \ {CHOOSE x \in s : TRUE}]])[debits]
            = (CHOOSE iter :
                  iter
                  = [s \in SUBSET debits |->
                       IF s = {}
                         THEN 0
                         ELSE opAmount(CHOOSE x \in s : TRUE)'
                              + iter[s \ {CHOOSE x \in s : TRUE}]])[debits]
            BY <3>3, <3>4, <3>5, <3>6, MapThenSumSetEqual DEF choose_amount, MapThenSumSet, MapThenFoldSet
        <3>8 MapThenSumSet(opAmount, debits)' = MapThenSumSet(opAmount, debits)
            BY <3>2, <3>7 DEF MapThenSumSet, MapThenFoldSet, opAmount
        <3> QED BY <3>8 DEF DebitTotal
    <2>3 CreditTotal' = CreditTotal
        <3>1 ~\E a \in Account: isTransKnown(self, a, credits) BY DEF debitPrecond
        <3>2 credits' = credits OBVIOUS
        <3>3 \A c \in credits: opAmount(c)' = opAmount(c) BY <3>1 DEF opAmount, isTransKnown, AT
        <3>4 \A c \in credits: opAmount(c) \in Nat BY DEF opAmount, AT
        <3>5 \A c \in credits: opAmount(c)' \in Nat BY DEF opAmount, AT, NNat
        <3>6 IsFiniteSet(credits) OBVIOUS
        <3>7 (CHOOSE iter :
                  iter
                  = [s \in SUBSET credits |->
                       IF s = {}
                         THEN 0
                         ELSE opAmount(CHOOSE x \in s : TRUE)
                              + iter[s \ {CHOOSE x \in s : TRUE}]])[credits]
            = (CHOOSE iter :
                  iter
                  = [s \in SUBSET credits |->
                       IF s = {}
                         THEN 0
                         ELSE opAmount(CHOOSE x \in s : TRUE)'
                              + iter[s \ {CHOOSE x \in s : TRUE}]])[credits]
            BY <3>3, <3>4, <3>5, <3>6, MapThenSumSetEqual DEF choose_amount, MapThenSumSet, MapThenFoldSet
        <3>8 MapThenSumSet(opAmount, credits)' = MapThenSumSet(opAmount, credits)
            BY <3>2, <3>7 DEF MapThenSumSet, MapThenFoldSet, opAmount
        <3> QED BY <3>8 DEF CreditTotal
    <2>4 Imbalance' = Imbalance BY <2>1, <2>2, <2>3 DEF Imbalance
    <2> QED BY <2>4
<1> QED BY <1>7, <1>4, <1>5, <1>6, <1>8


LEMMA debit_DebitTotal_debitPrecond_success == ASSUME IndInv, NEW self \in Transfer, debit(self),
debitPrecond(self), ~(UNCHANGED debits)
PROVE DebitTotal' = DebitTotal + amount[self]
<1> USE DEF debit, IndInv, TypeOK
<1> DEFINE selfAccount == accounts[self].from
<1> DEFINE nadd == [a |-> selfAccount, t |-> self]
<1> DEFINE otherDebits == debits \ {nadd}
<1>1 nadd \notin debits BY DEF isTransKnown, AT
<1>2 MapThenSumSet(opAmount, debits)' = MapThenSumSet(opAmount, otherDebits) + opAmount(nadd)'
    <2>1 \A at \in otherDebits: opAmount(at) \in Nat BY DEF opAmount, AT
    <2>2 MapThenSumSet(opAmount, otherDebits)' = MapThenSumSet(opAmount, otherDebits)
        <3>1 \A at \in otherDebits: opAmount(at)' \in Nat BY DEF opAmount, AT
        <3> QED BY <2>1, <3>1, MapThenSumSetEqual DEF MapThenSumSet, MapThenFoldSet, opAmount
    <2>3 MapThenSumSet(opAmount, debits)' = MapThenSumSet(opAmount, otherDebits)' + opAmount(nadd)'
        <3>1 MapThenSumSet(opAmount, otherDebits \cup {nadd})' = (MapThenSumSet(opAmount, otherDebits) + opAmount(nadd))'
            <4>1 IsFiniteSet(otherDebits) BY FS_Subset
            <4>2 opAmount(nadd) \in Nat BY transAmountInNat DEF opAmount
            <4>3 MapThenSumSet(opAmount, otherDebits \cup {nadd}) = MapThenSumSet(opAmount, otherDebits) + opAmount(nadd)
                BY <4>1, <2>1, <4>2, <1>1, MapThenSumSetAddElem
            <4> QED BY <4>3 DEF MapThenSumSet, MapThenFoldSet, opAmount
        <3> QED BY <3>1
    <2> QED BY <2>2, <2>3
<1>3 MapThenSumSet(opAmount, debits)' = MapThenSumSet(opAmount, debits) + amount[self]
    <2>1 MapThenSumSet(opAmount, otherDebits) = MapThenSumSet(opAmount, debits)
        <3>1 otherDebits = debits BY <1>1
        <3> QED BY <3>1
    <2> QED BY <1>2, <2>1 DEF opAmount
<1> QED BY <1>3 DEF DebitTotal


LEMMA debit_AmountPendingTotal_debitPrecond == ASSUME IndInv, NEW self \in Transfer, debit(self),
debitPrecond(self), ~(UNCHANGED debits)
PROVE
    /\ AmountPendingTotal' = AmountPendingTotal + amount[self]
    /\ AmountPendingTotal' \in Nat
<1> USE DEF debit, IndInv, TypeOK
<1> DEFINE selfAccount == accounts[self].from
<1> DEFINE nadd == [a |-> selfAccount, t |-> self]
<1>1 accounts[self].from \in Account BY DEF NonEmptyAccounts, EAccounts, EAccount
<1>2 ~creditPrecond(self) BY <1>1 DEF creditPrecond, debitPrecond, isTransKnown
<1>3 creditPrecond(self)'
    <2>1 accounts[self].to \in Account BY DEF NonEmptyAccounts, EAccounts, EAccount
    <2>2 ~\E a \in Account: isTransKnown(self, a, credits') BY DEF debitPrecond
    <2>3 ~isTransKnown(self, accounts[self].to, debits) BY <2>1 DEF debitPrecond,
        isTransKnown
    <2>4 ~isTransKnown(self, accounts[self].to, {nadd})
        <3>1 NonEmptyAccounts(self) BY <1>1, <2>1
        <3>2 accounts[self] # EmptyAccounts BY <3>1 DEF EmptyAccounts, NonEmptyAccounts
        <3>3 accounts[self].from # accounts[self].to BY <3>2 DEF DifferentAccounts
        <3> QED BY <3>3 DEF debitPrecond, isTransKnown
    <2>5 ~isTransKnown(self, accounts[self].to, debits') BY <2>3, <2>4 DEF isTransKnown
    <2>6 isTransKnown(self, accounts[self].from, debits') BY <1>1 DEF debitPrecond, isTransKnown
    <2> QED BY <2>2, <2>5, <2>6 DEF creditPrecond
<1>4 transPending' = transPending \cup {self} BY <1>2, <1>3 DEF transPending, AmountIsPending,
    creditPrecond, isTransKnown, pcLabels
<1>5 IsFiniteSet(transPending) BY transPendingIsFinite
<1>6 \A t \in transPending: transAmount(t) \in Nat BY transPendingAmountNat
<1>7 transAmount(self) \in Nat BY DEF transAmount
<1>8 MapThenSumSet(transAmount, transPending') = MapThenSumSet(transAmount, transPending) + transAmount(self)
    <2>1 self \notin transPending BY <1>2 DEF transPending, AmountIsPending
    <2> QED BY <1>4, <2>1, <1>5, <1>6, <1>7, MapThenSumSetAddElem
<1>9 AmountPendingTotal' \in Nat
    <2>1 IsFiniteSet(transPending') BY <1>4, <1>5, FS_AddElement
    <2>2 \A t \in transPending': transAmount(t) \in Nat BY <1>4, <1>6, <1>7
    <2>3 MapThenSumSet(transAmount, transPending') \in Nat BY <2>1, <2>2, MapThenSumSetType
    <2> QED BY <2>3 DEF AmountPendingTotal, transAmount, MapThenSumSet, MapThenFoldSet
<1> QED BY <1>8, <1>9 DEF AmountPendingTotal, transAmount, MapThenSumSet, MapThenFoldSet


LEMMA CreditTotalInNat == ASSUME IndInv
PROVE CreditTotal \in Nat
<1> USE DEF IndInv, TypeOK
<1>2 \A c \in credits: opAmount(c) \in Nat BY DEF opAmount, AT
<1> QED BY <1>2, MapThenSumSetType DEF CreditTotal

LEMMA DebitTotalInNat == ASSUME IndInv
PROVE DebitTotal \in Nat
<1> USE DEF IndInv, TypeOK
<1>2 \A d \in debits: opAmount(d) \in Nat BY DEF opAmount, AT
<1> QED BY <1>2, MapThenSumSetType DEF DebitTotal


LEMMA debit_AmountPendingDebitTotal_debitPrecond == ASSUME IndInv, NEW self \in Transfer, debit(self),
debitPrecond(self), ~(UNCHANGED debits)
PROVE AmountPendingTotal' - DebitTotal' = AmountPendingTotal - DebitTotal
    /\ AmountPendingTotal' \in Nat
    /\ DebitTotal' \in Nat
<1> USE DEF debit, IndInv, TypeOK
<1>1 DebitTotal' = DebitTotal + amount[self]
    BY debit_DebitTotal_debitPrecond_success
<1>2 DebitTotal \in Nat BY DebitTotalInNat
<1>3 DebitTotal' \in Nat BY <1>2, <1>1
<1>4 AmountPendingTotal \in Nat BY AmountPendingTotalInNat
<1> QED BY <1>2, <1>4, <1>1, <1>3, debit_AmountPendingTotal_debitPrecond


LEMMA debit_AmountPendingTotal_notDebitPrecond_or_retryDebit == ASSUME IndInv, NEW self \in Transfer, debit(self),
~debitPrecond(self) \/ UNCHANGED debits
PROVE AmountPendingTotal' = AmountPendingTotal
<1> USE DEF debit, IndInv, TypeOK
<1>1 transPending' = transPending BY DEF transPending, AmountIsPending, creditPrecond, isTransKnown, pcLabels
<1>2 MapThenSumSet(transAmount, transPending') = MapThenSumSet(transAmount, transPending) 
    BY <1>1 DEF transAmount
<1>3 MapThenSumSet(transAmount, transPending') = MapThenSumSet(transAmount, transPending) BY <1>1, <1>2
<1>4 AmountPendingTotal' = MapThenSumSet(transAmount, transPending') BY <1>1, <1>2 DEF
    transPending, transAmount, AmountIsPending, creditPrecond,
    isTransKnown, MapThenSumSet, MapThenFoldSet, AmountPendingTotal
<1> QED BY <1>3, <1>4 DEF AmountPendingTotal


THEOREM debit_IndInv == ASSUME IndInv, NEW self \in Transfer, debit(self)
PROVE IndInv'
<1> DEFINE selfAccount == accounts[self].from
<1> DEFINE nadd == [a |-> selfAccount, t |-> self]
<1> USE DEF debit, IndInv, TypeOK
<1>1 TypeOK'
    <2>1 pcLabels' BY DEF pcLabels
    <2>2 /\ debits' \in SUBSET AT
         /\ IsFiniteSet(debits')
         <3>1 CASE debitPrecond(self) /\ ~(UNCHANGED debits) 
            <4>1 debits' = debits \cup {nadd} BY <3>1
            <4>2 selfAccount \in Account BY DEF NonEmptyAccounts, EAccounts, EAccount
            <4>3 nadd \in AT BY <4>2 DEF AT
            <4>4 IsFiniteSet(debits') BY <4>1, FS_AddElement
            <4>5 debits' \in SUBSET AT BY <4>1, <4>3
            <4> QED BY <4>4, <4>5
         <3>2 CASE ~debitPrecond(self) \/ UNCHANGED debits
            <4>1 debits' = debits BY <3>2
            <4> QED BY <4>1
         <3> QED BY <3>1, <3>2
    <2> QED BY <2>1, <2>2
<1>2 (Imbalance = 0)' = (Imbalance = 0)
    <2>1 CreditTotal' = CreditTotal BY DEF CreditTotal, opAmount, MapThenSumSet, MapThenFoldSet
    <2>3 CreditTotal \in Nat BY CreditTotalInNat
    <2>4 DebitTotal \in Nat BY DebitTotalInNat
    <2>5 AmountPendingTotal \in Nat BY AmountPendingTotalInNat
    <2>2 AmountPendingTotal' - DebitTotal' = AmountPendingTotal - DebitTotal
         /\ AmountPendingTotal' \in Nat
         /\ DebitTotal' \in Nat
        <3>1 CASE debitPrecond(self) /\ ~(UNCHANGED debits)
            BY <3>1, debit_AmountPendingDebitTotal_debitPrecond
        <3>2 CASE ~debitPrecond(self) \/ UNCHANGED debits
            <4>1 DebitTotal' = DebitTotal BY <3>2 DEF DebitTotal, opAmount, MapThenSumSet, MapThenFoldSet
            <4>2 AmountPendingTotal' = AmountPendingTotal BY <3>2, debit_AmountPendingTotal_notDebitPrecond_or_retryDebit
            <4> QED BY <4>1, <4>2, AmountPendingTotalInNat, DebitTotalInNat
        <3> QED BY <3>1, <3>2
    <2>6 (CreditTotal - DebitTotal + AmountPendingTotal)' = CreditTotal - DebitTotal + AmountPendingTotal
        BY <2>1, <2>2, <2>3, <2>4, <2>5
    <2>7 CreditTotal - DebitTotal + AmountPendingTotal = 0 BY DEF Imbalance
    <2>8 (CreditTotal - DebitTotal + AmountPendingTotal)' = 0 BY <2>3, <2>4, <2>5, <2>6, <2>7
    <2> QED BY <2>6 DEF Imbalance
<1>3 \A t \in Transfer:
        \/ accounts[t]' = EmptyAccounts
        \/ (DifferentAccounts(t) /\ NonEmptyAccounts(t))'
    BY DEF DifferentAccounts, NonEmptyAccounts
<1>4 \A t \in Transfer: pc[t]' \in {"choose_accounts", "choose_amount"} => debitPrecond(t)'
    BY DEF pcLabels, debitPrecond, isTransKnown
<1>5 (pc[self] \notin {"choose_accounts"})' <=> NonEmptyAccounts(self)'
    <2>1 pc[self]' \notin {"choose_accounts"} BY DEF pcLabels
    <2>2 NonEmptyAccounts(self)' BY EmptyAssumption, NAccountAssumption, AccountAssumption
        DEF NonEmptyAccounts
    <2> QED BY <2>1, <2>2
<1>6 \A t \in Transfer \ {self}: (pc[t] \notin {"choose_accounts"})' <=> NonEmptyAccounts(t)'
    BY DEF pcLabels, NonEmptyAccounts
<1>7 \A t \in Transfer: (pc[t] \notin {"choose_accounts"})' <=> NonEmptyAccounts(t)'
    BY <1>5, <1>6
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>7, <1>3


LEMMA credit_CreditTotal_creditPrecond_success == ASSUME IndInv, NEW self \in Transfer, credit(self),
creditPrecond(self), ~(UNCHANGED credits)
PROVE CreditTotal' = CreditTotal + amount[self]
<1> USE DEF credit, IndInv, TypeOK
<1> DEFINE selfAccount == accounts[self].to
<1> DEFINE nadd == [a |-> selfAccount, t |-> self]
<1> DEFINE otherCredits == credits \ {nadd}
<1>1 nadd \notin credits BY DEF isTransKnown, AT
<1>2 MapThenSumSet(opAmount, credits)' = MapThenSumSet(opAmount, otherCredits) + opAmount(nadd)'
    <2>1 \A at \in otherCredits: opAmount(at) \in Nat BY DEF opAmount, AT
    <2>2 MapThenSumSet(opAmount, otherCredits)' = MapThenSumSet(opAmount, otherCredits)
        <3>1 \A at \in otherCredits: opAmount(at)' \in Nat BY DEF opAmount, AT
        <3> QED BY <2>1, <3>1, MapThenSumSetEqual DEF MapThenSumSet, MapThenFoldSet, opAmount
    <2>3 MapThenSumSet(opAmount, credits)' = MapThenSumSet(opAmount, otherCredits)' + opAmount(nadd)'
        <3>1 MapThenSumSet(opAmount, otherCredits \cup {nadd})' = (MapThenSumSet(opAmount, otherCredits) + opAmount(nadd))'
            <4>1 IsFiniteSet(otherCredits) BY FS_Subset
            <4>2 opAmount(nadd) \in Nat BY transAmountInNat DEF opAmount
            <4>3 MapThenSumSet(opAmount, otherCredits \cup {nadd}) = MapThenSumSet(opAmount, otherCredits) + opAmount(nadd)
                BY <4>1, <2>1, <4>2, <1>1, MapThenSumSetAddElem
            <4> QED BY <4>3 DEF MapThenSumSet, MapThenFoldSet, opAmount
        <3> QED BY <3>1
    <2> QED BY <2>2, <2>3
<1>3 MapThenSumSet(opAmount, credits)' = MapThenSumSet(opAmount, credits) + amount[self]
    <2>1 MapThenSumSet(opAmount, otherCredits) = MapThenSumSet(opAmount, credits)
        <3>1 otherCredits = credits BY <1>1
        <3> QED BY <3>1
    <2> QED BY <1>2, <2>1 DEF opAmount
<1> QED BY <1>3 DEF CreditTotal


LEMMA credit_AmountPendingTotal_creditPrecond == ASSUME IndInv, NEW self \in Transfer, credit(self),
creditPrecond(self), ~(UNCHANGED credits)
PROVE
    /\ AmountPendingTotal = AmountPendingTotal' + amount[self]
    /\ AmountPendingTotal' \in Nat
<1> USE DEF credit, IndInv, TypeOK
<1>1 accounts[self].to \in Account BY DEF NonEmptyAccounts, EAccounts, EAccount
<1>2 ~creditPrecond(self)' BY <1>1 DEF creditPrecond, isTransKnown
<1>3 transPending' = transPending \ {self} BY <1>2 DEF transPending, AmountIsPending,
    creditPrecond, isTransKnown, pcLabels
<1>4 IsFiniteSet(transPending) BY transPendingIsFinite
<1>5 \A t \in transPending: transAmount(t) \in Nat BY transPendingAmountNat
<1>6 transAmount(self) \in Nat BY DEF transAmount
<1>7 MapThenSumSet(transAmount, transPending) = MapThenSumSet(transAmount, transPending') + transAmount(self)
    <2>1 self \in transPending BY DEF transPending, AmountIsPending
    <2> QED BY <1>3, <2>1, <1>4, <1>5, <1>6, MapThenSumSetRemElem
<1>8 AmountPendingTotal' \in Nat
    <2>1 IsFiniteSet(transPending') BY <1>3, <1>4, FS_RemoveElement
    <2>2 \A t \in transPending': transAmount(t) \in Nat BY <1>3, <1>5, <1>6
    <2>3 MapThenSumSet(transAmount, transPending') \in Nat BY <2>1, <2>2, MapThenSumSetType
    <2> QED BY <2>3 DEF AmountPendingTotal, transAmount, MapThenSumSet, MapThenFoldSet
<1> QED BY <1>7, <1>8 DEF AmountPendingTotal, transAmount, MapThenSumSet, MapThenFoldSet


LEMMA credit_AmountPendingCreditTotal_creditPrecond == ASSUME IndInv, NEW self \in Transfer, credit(self),
creditPrecond(self), ~(UNCHANGED credits)
PROVE AmountPendingTotal' + CreditTotal' = AmountPendingTotal + CreditTotal
    /\ AmountPendingTotal' \in Nat
    /\ CreditTotal' \in Nat
<1> USE DEF credit, IndInv, TypeOK
<1>1 CreditTotal' = CreditTotal + amount[self]
    BY credit_CreditTotal_creditPrecond_success
<1>2 CreditTotal \in Nat BY CreditTotalInNat
<1>3 CreditTotal' \in Nat BY <1>2, <1>1
<1>4 AmountPendingTotal \in Nat BY AmountPendingTotalInNat
<1> QED BY <1>2, <1>4, <1>1, <1>3, credit_AmountPendingTotal_creditPrecond


THEOREM credit_AmountPendingTotal_notCreditPrecond_or_retryCredit == ASSUME IndInv, NEW self \in Transfer, credit(self),
~creditPrecond(self) \/ UNCHANGED credits
PROVE AmountPendingTotal' = AmountPendingTotal
<1> USE DEF credit, IndInv, TypeOK
<1>1 transPending' = transPending BY DEF transPending, AmountIsPending, creditPrecond, isTransKnown, pcLabels
<1>2 \A t \in transPending: transAmount(t)' = transAmount(t) BY DEF transAmount,
    creditPrecond, isTransKnown
<1>3 MapThenSumSet(transAmount, transPending') = MapThenSumSet(transAmount, transPending) BY <1>1, <1>2
<1>4 AmountPendingTotal' = MapThenSumSet(transAmount, transPending') BY <1>1, <1>2 DEF
    transPending, transAmount, AmountIsPending, creditPrecond,
    isTransKnown, MapThenSumSet, MapThenFoldSet, AmountPendingTotal
<1> QED BY <1>3, <1>4 DEF AmountPendingTotal


THEOREM credit_IndInv == ASSUME IndInv, NEW self \in Transfer, credit(self)
PROVE IndInv'
<1> DEFINE selfAccount == accounts[self].to
<1> DEFINE nadd == [a |-> selfAccount, t |-> self]
<1> USE DEF credit, IndInv, TypeOK
<1>1 TypeOK'
    <2>1 pcLabels' BY DEF pcLabels
    <2>2 /\ credits' \in SUBSET AT
         /\ IsFiniteSet(credits')
         <3>1 CASE creditPrecond(self) /\ ~(UNCHANGED credits) 
            <4>1 credits' = credits \cup {nadd} BY <3>1
            <4>2 selfAccount \in Account BY DEF NonEmptyAccounts, EAccounts, EAccount
            <4>3 nadd \in AT BY <4>2 DEF AT
            <4>4 IsFiniteSet(credits') BY <4>1, FS_AddElement
            <4>5 credits' \in SUBSET AT BY <4>1, <4>3
            <4> QED BY <4>4, <4>5
         <3>2 CASE ~creditPrecond(self) \/ UNCHANGED credits
            <4>1 credits' = credits BY <3>2
            <4> QED BY <4>1
         <3> QED BY <3>1, <3>2
    <2> QED BY <2>1, <2>2
<1>2 (Imbalance = 0)' = (Imbalance = 0)
    <2>1 DebitTotal' = DebitTotal BY DEF DebitTotal, opAmount, MapThenSumSet, MapThenFoldSet
    <2>3 DebitTotal \in Nat BY DebitTotalInNat
    <2>4 CreditTotal \in Nat BY CreditTotalInNat
    <2>5 AmountPendingTotal \in Nat BY AmountPendingTotalInNat
    <2>2 AmountPendingTotal' + CreditTotal' = AmountPendingTotal + CreditTotal
         /\ AmountPendingTotal' \in Nat
         /\ CreditTotal' \in Nat
        <3>1 CASE creditPrecond(self) /\ ~(UNCHANGED credits)
            BY <3>1, credit_AmountPendingCreditTotal_creditPrecond
        <3>2 CASE ~creditPrecond(self) \/ UNCHANGED credits
            <4>1 CreditTotal' = CreditTotal BY <3>2 DEF CreditTotal, opAmount, MapThenSumSet, MapThenFoldSet
            <4>2 AmountPendingTotal' = AmountPendingTotal BY <3>2, credit_AmountPendingTotal_notCreditPrecond_or_retryCredit
            <4> QED BY <4>1, <4>2, AmountPendingTotalInNat, CreditTotalInNat
        <3> QED BY <3>1, <3>2
    <2>6 (CreditTotal - DebitTotal + AmountPendingTotal)' = CreditTotal - DebitTotal + AmountPendingTotal
        <3>1 (CreditTotal + AmountPendingTotal)' = CreditTotal + AmountPendingTotal
            BY <2>2, <2>4, <2>5
        <3>2 (CreditTotal + AmountPendingTotal)' - DebitTotal' = CreditTotal + AmountPendingTotal - DebitTotal
            BY <3>1, <2>1, <2>3, <2>4, <2>5
        <3>3 (CreditTotal + AmountPendingTotal - DebitTotal)' = CreditTotal + AmountPendingTotal - DebitTotal
            BY <2>2, <3>2, <2>1, <2>3, <2>4, <2>5
        <3> QED BY <3>3, <2>2, <2>1, <2>3, <2>4, <2>5
    <2>7 CreditTotal - DebitTotal + AmountPendingTotal = 0 BY DEF Imbalance
    <2>8 (CreditTotal - DebitTotal + AmountPendingTotal)' = 0 BY <2>3, <2>4, <2>5, <2>6, <2>7
    <2> QED BY <2>6 DEF Imbalance
<1>3 \A t \in Transfer:
        \/ accounts[t]' = EmptyAccounts
        \/ (DifferentAccounts(t) /\ NonEmptyAccounts(t))'
    BY DEF DifferentAccounts, NonEmptyAccounts
<1>4 \A t \in Transfer: pc[t]' \in {"choose_accounts", "choose_amount"} => debitPrecond(t)'
    BY DEF pcLabels, debitPrecond, isTransKnown
<1>5 (pc[self] \notin {"choose_accounts"})' <=> NonEmptyAccounts(self)'
    <2>1 pc[self]' \notin {"choose_accounts"} BY DEF pcLabels
    <2>2 NonEmptyAccounts(self)' BY EmptyAssumption, NAccountAssumption, AccountAssumption
        DEF NonEmptyAccounts
    <2> QED BY <2>1, <2>2
<1>6 \A t \in Transfer \ {self}: (pc[t] \notin {"choose_accounts"})' <=> NonEmptyAccounts(t)'
    BY DEF pcLabels, NonEmptyAccounts
<1>7 \A t \in Transfer: (pc[t] \notin {"choose_accounts"})' <=> NonEmptyAccounts(t)'
    BY <1>5, <1>6
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>7, <1>3

    
THEOREM retryDebit_AmountPendingTotal == ASSUME IndInv, NEW self \in Transfer, retryDebit(self)
PROVE AmountPendingTotal' = AmountPendingTotal
<1> USE DEF retryDebit, IndInv, TypeOK
<1>1 transPending' = transPending
    <2>1 CASE ~debitPrecond(self)
        <3> QED BY <2>1 DEF transPending, AmountIsPending, creditPrecond, isTransKnown, pcLabels
    <2>2 CASE debitPrecond(self)
        <3>1 self \notin transPending BY <2>2 DEF transPending, AmountIsPending, creditPrecond,
            debitPrecond, isTransKnown, pcLabels, AT
        <3> QED BY <3>1 DEF pcLabels, transPending, AmountIsPending, creditPrecond
    <2> QED BY <2>1, <2>2
<1>2 \A t \in Transfer: transAmount(t)' = transAmount(t) BY DEF transAmount,
    creditPrecond, debitPrecond
<1> QED BY <1>1, <1>2 DEF transPending, transAmount, AmountIsPending, creditPrecond,
    isTransKnown, MapThenSumSet, MapThenFoldSet, AmountPendingTotal

THEOREM retryDebit_IndInv == ASSUME IndInv, NEW self \in Transfer, retryDebit(self)
PROVE IndInv'
<1> USE DEF retryDebit, IndInv, TypeOK
<1>1 accounts' \in [Transfer -> EAccounts] BY DEF EAccounts, EAccount, EmptyAccounts
<1>2 pcLabels' BY DEF pcLabels
<1>3 Imbalance' = 0
    <2>1 AmountPendingTotal' = AmountPendingTotal BY retryDebit_AmountPendingTotal
    <2>2 DebitTotal' = DebitTotal BY DEF DebitTotal, opAmount, MapThenSumSet, MapThenFoldSet
    <2>3 CreditTotal' = CreditTotal BY DEF CreditTotal, opAmount, MapThenSumSet, MapThenFoldSet
    <2>4 Imbalance' = Imbalance BY <2>1, <2>2, <2>3 DEF Imbalance
    <2> QED BY <2>4
<1>4 \A t \in Transfer:
        \/ accounts[t]' = EmptyAccounts
        \/ (DifferentAccounts(t) /\ NonEmptyAccounts(t))'
    BY DEF DifferentAccounts, NonEmptyAccounts
<1>5 \A t \in Transfer: pc[t]' \in {"choose_accounts", "choose_amount"} => debitPrecond(t)'
    BY DEF pcLabels, debitPrecond, isTransKnown
<1>6 \A t \in Transfer: (pc[t] \notin {"choose_accounts"})' <=> NonEmptyAccounts(t)'
    BY DEF pcLabels, NonEmptyAccounts
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6


THEOREM retryCredit_AmountPendingTotal == ASSUME IndInv, NEW self \in Transfer, retryCredit(self)
PROVE AmountPendingTotal' = AmountPendingTotal
<1> USE DEF retryCredit, IndInv, TypeOK
<1>1 transPending' = transPending
    <2>1 CASE ~creditPrecond(self)
        <3> QED BY <2>1 DEF transPending, AmountIsPending, creditPrecond, isTransKnown, pcLabels
    <2>2 CASE creditPrecond(self)
        <3>1 self \in transPending BY <2>2 DEF transPending, AmountIsPending, creditPrecond,
            debitPrecond, isTransKnown, pcLabels, AT
        <3> QED BY <3>1 DEF pcLabels, transPending, AmountIsPending, creditPrecond
    <2> QED BY <2>1, <2>2
<1>2 \A t \in Transfer: transAmount(t)' = transAmount(t) BY DEF transAmount,
    creditPrecond, debitPrecond
<1> QED BY <1>1, <1>2 DEF transPending, transAmount, AmountIsPending, creditPrecond,
    isTransKnown, MapThenSumSet, MapThenFoldSet, AmountPendingTotal

THEOREM retryCredit_IndInv == ASSUME IndInv, NEW self \in Transfer, retryCredit(self)
PROVE IndInv'
<1> USE DEF retryCredit, IndInv, TypeOK
<1>1 accounts' \in [Transfer -> EAccounts] BY DEF EAccounts, EAccount, EmptyAccounts
<1>2 pcLabels' BY DEF pcLabels
<1>3 Imbalance' = 0
    <2>1 AmountPendingTotal' = AmountPendingTotal BY retryCredit_AmountPendingTotal
    <2>2 DebitTotal' = DebitTotal BY DEF DebitTotal, opAmount, MapThenSumSet, MapThenFoldSet
    <2>3 CreditTotal' = CreditTotal BY DEF CreditTotal, opAmount, MapThenSumSet, MapThenFoldSet
    <2>4 Imbalance' = Imbalance BY <2>1, <2>2, <2>3 DEF Imbalance
    <2> QED BY <2>4
<1>4 \A t \in Transfer:
        \/ accounts[t]' = EmptyAccounts
        \/ (DifferentAccounts(t) /\ NonEmptyAccounts(t))'
    BY DEF DifferentAccounts, NonEmptyAccounts
<1>5 \A t \in Transfer: pc[t]' \in {"choose_accounts", "choose_amount"} => debitPrecond(t)'
    BY DEF pcLabels, debitPrecond, isTransKnown
<1>6 \A t \in Transfer: (pc[t] \notin {"choose_accounts"})' <=> NonEmptyAccounts(t)'
    BY DEF pcLabels, NonEmptyAccounts
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6


THEOREM nextNonTerminating == ASSUME IndInv, Next, ~Terminating
PROVE IndInv'
<1> SUFFICES ASSUME IndInv, NEW self \in Transfer, trans(self)
    PROVE IndInv'
    BY DEF Next, trans
<1>1 CASE choose_accounts(self) BY <1>1, choose_accounts_IndInv
<1>2 CASE choose_amount(self) BY <1>2, choose_amount_IndInv
<1>3 CASE debit(self) BY <1>3, debit_IndInv
<1>4 CASE retryDebit(self) BY <1>4, retryDebit_IndInv
<1>5 CASE credit(self) BY <1>5, credit_IndInv
<1>6 CASE retryCredit(self) BY <1>6, retryCredit_IndInv
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF trans


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
<1>3 (/\ \A t \in Transfer: pc[t] \in {"choose_accounts", "choose_amount"} => debitPrecond(t))' =
      /\ \A t \in Transfer: pc[t] \in {"choose_accounts", "choose_amount"} => debitPrecond(t)
    BY DEF debitPrecond
<1>4 (/\ \A t \in Transfer:
        pc[t] \notin {"choose_accounts"} <=> NonEmptyAccounts(t))' =
      /\ \A t \in Transfer:
        pc[t] \notin {"choose_accounts"} <=> NonEmptyAccounts(t)
    BY DEF NonEmptyAccounts
<1>5 CreditTotal' = CreditTotal BY DEF CreditTotal, opAmount, MapThenSumSet, MapThenFoldSet
<1>6 DebitTotal' = DebitTotal BY DEF DebitTotal, opAmount, MapThenSumSet, MapThenFoldSet
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

====
