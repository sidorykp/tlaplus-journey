---- MODULE MoneyTransferTerse_proofs ----
EXTENDS MoneyTransferTerse, MoneyTransfer_proofsCommon, FiniteSetsExt_theorems_ext, FiniteSetTheorems, TLAPS

LEMMA transAmountInNat == ASSUME TypeOK, NEW self \in Transfer
PROVE transAmount(self) \in Nat
BY DEF TypeOK, transAmount


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
PROVE IndInv
<1> USE DEF choose_accounts, IndInv, TypeOK
<1>1 accounts' \in [Transfer -> EAccounts] BY DEF EAccounts, EAccount, EmptyAccounts
<1>2 pcLabels' BY DEF pcLabels
<1>3 \A t \in Transfer: pc[t]' \in {"choose_accounts", "choose_amount"} => debitPrecond(t)'
    BY DEF pcLabels, debitPrecond, isTransKnown
<1>4 \A t \in Transfer \ {self}: (pc[t] \notin {"choose_accounts"}) <=> NonEmptyAccounts(t)'
    BY DEF pcLabels, NonEmptyAccounts
<1> QED BY <1>1, <1>2, <1>3, <1>4, choose_accounts_AmountPendingTotal


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
PROVE IndInv
<1> USE DEF choose_amount, IndInv, TypeOK
<1>1 accounts' \in [Transfer -> EAccounts] BY DEF EAccounts, EAccount, EmptyAccounts
<1>2 pcLabels' BY DEF pcLabels
<1>3 \A t \in Transfer: pc[t]' \in {"choose_accounts", "choose_amount"} => debitPrecond(t)'
    BY DEF pcLabels, debitPrecond, isTransKnown
<1>4 \A t \in Transfer \ {self}: (pc[t] \notin {"choose_accounts"}) <=> NonEmptyAccounts(t)'
    BY DEF pcLabels, NonEmptyAccounts
<1> QED BY <1>1, <1>2, <1>3, <1>4, choose_amount_AmountPendingTotal


LEMMA debit_DebitTotal_debitPrecond_success == ASSUME IndInv, NEW self \in Transfer, debit(self),
debitPrecond(self), ~(UNCHANGED debits)
PROVE DebitTotal' = DebitTotal + amount[self]
<1> USE DEF debit, IndInv, TypeOK
<1> DEFINE selfAccount == accounts[self].from
<1> DEFINE nadd == [a |-> selfAccount, t |-> self]
<1> DEFINE otherDebits == debits \ {nadd}
<1>1 nadd \notin debits BY DEF isTransKnown, AT
<1>2 \A at \in otherDebits: opAmount(at) \in Nat BY DEF opAmount, AT
<1>3 MapThenSumSet(opAmount, debits)' = MapThenSumSet(opAmount, otherDebits) + opAmount(nadd)'
    <2>1 MapThenSumSet(opAmount, otherDebits)' = MapThenSumSet(opAmount, otherDebits)
        <3>1 \A at \in otherDebits: opAmount(at)' \in Nat BY DEF opAmount, AT
        <3> QED BY <1>2, <3>1, MapThenSumSetEqual DEF MapThenSumSet, MapThenFoldSet, opAmount
    <2>2 MapThenSumSet(opAmount, debits)' = MapThenSumSet(opAmount, otherDebits)' + opAmount(nadd)'
        <3>1 MapThenSumSet(opAmount, otherDebits \cup {nadd})' = (MapThenSumSet(opAmount, otherDebits) + opAmount(nadd))'
            <4>1 IsFiniteSet(otherDebits) BY FS_Subset
            <4>2 opAmount(nadd) \in Nat BY transAmountInNat DEF opAmount
            <4>3 MapThenSumSet(opAmount, otherDebits \cup {nadd}) = MapThenSumSet(opAmount, otherDebits) + opAmount(nadd)
                BY <4>1, <1>2, <4>2, <1>1, MapThenSumSetAddElem
            <4> QED BY <4>3 DEF MapThenSumSet, MapThenFoldSet, opAmount
        <3> QED BY <3>1
    <2> QED BY <2>1, <2>2
<1>4 MapThenSumSet(opAmount, debits)' = MapThenSumSet(opAmount, debits) + amount[self]
    <2>1 MapThenSumSet(opAmount, otherDebits) = MapThenSumSet(opAmount, debits)
        <3>1 otherDebits = debits BY <1>1
        <3> QED BY <3>1
    <2> QED BY <1>3, <2>1 DEF opAmount
<1> QED BY <1>4 DEF DebitTotal

====
