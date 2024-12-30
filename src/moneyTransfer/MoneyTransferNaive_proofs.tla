---- MODULE MoneyTransferNaive_proofs ----
EXTENDS MoneyTransferNaive, MoneyTransfer_proofsCommon,
FiniteSetsExt_theorems, FiniteSetTheorems, TLAPS

THEOREM ImplicationProperty == IndInv => MoneyTotalPreserved
BY DEF MoneyTotalPreserved, IndInv

THEOREM InitProperty == ASSUME Init
PROVE IndInv
<1> USE DEF Init, IndInv, TypeOK
<1>1 TypeOK
    <2>1 pcLabels BY DEF pcLabels, ProcSet
    <2>2 accounts \in [Transfer -> EAccounts] BY EmptyAssumption
        DEF EmptyAccounts, EAccounts, EAccount
    <2> QED BY <2>1, <2>2
<1>2 MoneyTotalPreserved
    <2>1 \A a \in Account: accBal(a) = 0 BY DEF accBal
    <2>2 \A t \in transPending: transAmount(t) = 0 BY DEF transPending, transAmount,
        pcLabels, AmountIsPending
    <2>3 IsFiniteSet(Transfer) BY transSetIsFinite
    <2>4 IsFiniteSet(transPending) BY <2>3, FS_Subset
        DEF transPending, NNat
    <2>5 AmountPendingTotal = 0 BY <2>2, <2>4, MapThenSumSetZeros
        DEF AmountPendingTotal, transAmount
    <2>6 IsFiniteSet(Account) BY accountSetIsFinite
    <2>7 BalanceTotal = 0 BY <2>1, <2>6, MapThenSumSetZeros DEF BalanceTotal
    <2> QED BY <2>5, <2>7 DEF MoneyTotalPreserved, Imbalance
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


THEOREM recur_sum == ASSUME NEW S \in SUBSET Transfer, NEW op1(_), NEW op2(_),
\A s \in S: op1(s) = op2(s),
\A s \in S: op1(s) \in Nat,
\A s \in S: op2(s) \in Nat
PROVE 
    (CHOOSE iter :
          iter
          = [s \in SUBSET S |->
               IF s = {}
                 THEN 0
                 ELSE op1(CHOOSE x \in s : TRUE)
                      + iter[s \ {CHOOSE x \in s : TRUE}]])[S]
    = (CHOOSE iter :
          iter
          = [s \in SUBSET S |->
               IF s = {}
                 THEN 0
                 ELSE op2(CHOOSE x \in s : TRUE)
                      + iter[s \ {CHOOSE x \in s : TRUE}]])[S]
<1> DEFINE opDiff(s) == op1(s) - op2(s)
<1>1 IsFiniteSet(S) BY transSetIsFinite, FS_Subset
<1>2 (CHOOSE iter :
          iter
          = [s \in SUBSET S |->
               IF s = {}
                 THEN 0
                 ELSE op1(CHOOSE x \in s : TRUE)
                      + iter[s \ {CHOOSE x \in s : TRUE}]])[S] = MapThenSumSet(op1, S)
    BY DEF MapThenSumSet, MapThenFoldSet
<1>3 (CHOOSE iter :
          iter
          = [s \in SUBSET S |->
               IF s = {}
                 THEN 0
                 ELSE op2(CHOOSE x \in s : TRUE)
                      + iter[s \ {CHOOSE x \in s : TRUE}]])[S] = MapThenSumSet(op2, S)
    BY DEF MapThenSumSet, MapThenFoldSet
<1>4 MapThenSumSet(op1, S) \in Nat BY <1>1, MapThenSumSetType
<1>5 MapThenSumSet(op2, S) \in Nat BY <1>1, MapThenSumSetType
<1>6 \A s \in S: opDiff(s) = 0 OBVIOUS
<1>7 MapThenSumSet(opDiff, S) = 0 BY <1>1, <1>6, MapThenSumSetZeros
<1>8 \A s \in S: opDiff(s) \in Nat BY <1>6
<1>9 MapThenSumSet(op1, S) = MapThenSumSet(op2, S) BY <1>1, <1>4, <1>5, <1>7, <1>8
    DEF MapThenSumSet, MapThenFoldSet
<1> QED BY <1>9 DEF MapThenSumSet, MapThenFoldSet


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
<1>8 transPending \in SUBSET Transfer BY DEF transPending
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
    BY <1>5, <1>6, <1>7, <1>8, recur_sum DEF choose_amount, transPending, AmountIsPending,
    pcLabels, IndInv, TypeOK, NNat
<1>10 MapThenSumSet(transAmount, transPending)' = MapThenSumSet(transAmount, transPending)
    BY <1>4, <1>9 DEF MapThenSumSet, MapThenFoldSet, transAmount
<1> QED BY <1>10 DEF AmountPendingTotal

====
