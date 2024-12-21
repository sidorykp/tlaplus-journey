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
    <2>2 bal \in [Account -> Int] BY AvailAssumption DEF NNat
    <2>3 accounts \in [Transfer -> EAccounts] BY EmptyAssumption
        DEF EmptyAccounts, EAccounts, EAccount
    <2> QED BY <2>1, <2>2, <2>3
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

====
