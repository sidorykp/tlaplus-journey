---- MODULE MoneyTransferNaive_proofs ----
EXTENDS MoneyTransferNaive, MoneyTransfer_proofsCommon,
FiniteSetsExt_theorems_ext, FiniteSetTheorems, TLAPS

THEOREM ImplicationProperty == IndInv => MoneyTotalPreserved
BY DEF MoneyTotalPreserved, IndInv

LEMMA transPendingIsFinite ==
IsFiniteSet(transPending) BY transSetIsFinite, FS_Subset DEF transPending

THEOREM InitProperty == ASSUME Init
PROVE IndInv
<1> USE DEF Init, IndInv, TypeOK
<1>1 TypeOK
    <2>1 pcLabels BY DEF pcLabels, ProcSet
    <2>2 accounts \in [Transfer -> EAccounts] BY EmptyAssumption
        DEF EmptyAccounts, EAccounts, EAccount
    <2> QED BY <2>1, <2>2
<1>2 MoneyTotalPreserved
    <2>1 \A a \in Account: creditBal(a) = 0 BY DEF creditBal
    <2>2 \A a \in Account: debitBal(a) = 0 BY DEF debitBal
    <2>3 IsFiniteSet(Account) BY accountSetIsFinite
    <2>4 CreditTotal = 0 BY <2>1, <2>3, MapThenSumSetZeros DEF CreditTotal
    <2>5 DebitTotal = 0 BY <2>2, <2>3, MapThenSumSetZeros DEF DebitTotal
    <2>6 \A t \in transPending: transAmount(t) = 0 BY DEF transPending, transAmount,
        pcLabels, AmountIsPending
    <2>7 IsFiniteSet(transPending) BY transPendingIsFinite
    <2>8 AmountPendingTotal = 0 BY <2>6, <2>7, MapThenSumSetZeros
        DEF AmountPendingTotal, transAmount
    <2> QED BY <2>4, <2>5, <2>8 DEF MoneyTotalPreserved, Imbalance
<1>3 \A t \in Transfer: pc[t] \notin {"choose_accounts"} <=> NonEmptyAccounts(t)
    BY EmptyAssumption DEF pcLabels, ProcSet, NonEmptyAccounts, EmptyAccounts
<1> QED BY <1>1, <1>2, <1>3


THEOREM choose_accounts_AmountPendingTotal == ASSUME IndInv, NEW self \in Transfer, choose_accounts(self)
PROVE AmountPendingTotal' = AmountPendingTotal
<1>1 self \notin transPending BY DEF transPending, AmountIsPending, choose_accounts
<1>2 ~AmountIsPending(self)' BY DEF AmountIsPending, pcLabels, choose_accounts, IndInv, TypeOK
<1>3 self \notin transPending' BY <1>2 DEF transPending
<1>4 transPending' = transPending BY <1>1, <1>3 DEF pcLabels,
    transPending, AmountIsPending, choose_accounts, IndInv, TypeOK
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
<1>1 TypeOK'
    <2>1 pcLabels' BY DEF pcLabels
    <2>2 accounts' \in [Transfer -> EAccounts] BY EmptyAssumption
        DEF EmptyAccounts, EAccounts, EAccount
    <2> QED BY <2>1, <2>2
<1>2 MoneyTotalPreserved' = MoneyTotalPreserved
    <2>1 CreditTotal' = CreditTotal BY DEF CreditTotal, creditBal, MapThenSumSet, MapThenFoldSet
    <2>2 DebitTotal' = DebitTotal BY DEF DebitTotal, debitBal, MapThenSumSet, MapThenFoldSet
    <2> QED BY <2>1, <2>2, choose_accounts_AmountPendingTotal DEF MoneyTotalPreserved, Imbalance
<1>3 (pc[self] \notin {"choose_accounts"})' <=> NonEmptyAccounts(self)'
    <2>1 pc[self]' \notin {"choose_accounts"} BY DEF pcLabels
    <2>2 NonEmptyAccounts(self)' BY EmptyAssumption, NAccountAssumption, AccountAssumption
        DEF NonEmptyAccounts
    <2> QED BY <2>1, <2>2
<1>4 \A t \in Transfer \ {self}: (pc[t] \notin {"choose_accounts"})' <=> NonEmptyAccounts(t)'
    BY DEF pcLabels, NonEmptyAccounts
<1> QED BY <1>1, <1>2, <1>3, <1>4


THEOREM choose_amount_AmountPendingTotal == ASSUME IndInv, NEW self \in Transfer, choose_amount(self)
PROVE AmountPendingTotal' = AmountPendingTotal
<1>1 self \notin transPending BY DEF transPending, AmountIsPending, choose_amount
<1>2 ~AmountIsPending(self)' BY DEF AmountIsPending, choose_amount, IndInv, TypeOK,
    pcLabels
<1>3 self \notin transPending' BY <1>2 DEF transPending
<1>4 transPending' = transPending BY <1>1, <1>3 DEF pcLabels,
    transPending, AmountIsPending, choose_amount, IndInv, TypeOK
<1>5 \A t \in transPending: transAmount(t)' = transAmount(t) BY
    DEF transPending, AmountIsPending, choose_amount, IndInv, TypeOK, transAmount
<1>6 \A t \in transPending: transAmount(t) \in Nat BY DEF choose_amount, IndInv, TypeOK,
    transAmount, transPending
<1>7 \A t \in transPending: transAmount(t)' \in Nat BY DEF choose_amount, IndInv, TypeOK, NNat,
    transAmount, transPending
<1>8 IsFiniteSet(transPending) BY transPendingIsFinite
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
    BY <1>4, <1>9 DEF MapThenSumSet, MapThenFoldSet
<1> QED BY <1>10 DEF AmountPendingTotal

====
