g---- MODULE MoneyTransferNaive_proofs ----
EXTENDS MoneyTransferNaive, MoneyTransfer_proofsCommon,
FiniteSetsExt_theorems_ext, FiniteSetTheorems, TLAPS

THEOREM ImplicationProperty == IndInv => MoneyTotalPreserved
BY DEF MoneyTotalPreserved, IndInv

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

LEMMA transAmountInNat == ASSUME TypeOK, NEW self \in Transfer
PROVE transAmount(self) \in Nat
BY DEF TypeOK, transAmount


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


THEOREM choose_amount_IndInv == ASSUME IndInv, NEW self \in Transfer, choose_amount(self)
PROVE IndInv'
<1> USE DEF choose_amount, IndInv, TypeOK
<1>1 TypeOK'
    <2>1 pcLabels' BY DEF pcLabels
    <2>2 accounts' \in [Transfer -> EAccounts] BY EmptyAssumption
        DEF EmptyAccounts, EAccounts, EAccount
    <2> QED BY <2>1, <2>2
<1>2 MoneyTotalPreserved' = MoneyTotalPreserved
    <2>1 CreditTotal' = CreditTotal BY DEF CreditTotal, creditBal, MapThenSumSet, MapThenFoldSet
    <2>2 DebitTotal' = DebitTotal BY DEF DebitTotal, debitBal, MapThenSumSet, MapThenFoldSet
    <2> QED BY <2>1, <2>2, choose_amount_AmountPendingTotal DEF MoneyTotalPreserved, Imbalance
<1>3 (pc[self] \notin {"choose_accounts"})' <=> NonEmptyAccounts(self)'
    <2>1 pc[self]' \notin {"choose_accounts"} BY DEF pcLabels
    <2>2 NonEmptyAccounts(self)' BY EmptyAssumption, NAccountAssumption, AccountAssumption
        DEF NonEmptyAccounts
    <2> QED BY <2>1, <2>2
<1>4 \A t \in Transfer \ {self}: (pc[t] \notin {"choose_accounts"})' <=> NonEmptyAccounts(t)'
    BY DEF pcLabels, NonEmptyAccounts
<1> QED BY <1>1, <1>2, <1>3, <1>4


LEMMA CreditTotalInNat == ASSUME IndInv
PROVE CreditTotal \in Nat
<1> USE DEF IndInv, TypeOK
<1>1 IsFiniteSet(Account) BY accountSetIsFinite
<1>2 \A a \in Account: creditBal(a) \in Nat BY DEF creditBal
<1> QED BY <1>1, <1>2, MapThenSumSetType DEF CreditTotal

LEMMA DebitTotalInNat == ASSUME IndInv
PROVE DebitTotal \in Nat
<1> USE DEF IndInv, TypeOK
<1>1 IsFiniteSet(Account) BY accountSetIsFinite
<1>2 \A a \in Account: debitBal(a) \in Nat BY DEF debitBal
<1> QED BY <1>1, <1>2, MapThenSumSetType DEF DebitTotal


THEOREM debitTotalProperty == ASSUME IndInv, NEW self \in Transfer, debit(self)
PROVE DebitTotal' = DebitTotal + amount[self]
<1> USE DEF debit, IndInv, TypeOK
<1> DEFINE selfAccount == accounts[self].from
<1> DEFINE otherAccounts == Account \ {selfAccount}
<1>1 selfAccount \in Account BY DEF NonEmptyAccounts, EAccounts, EAccount
<1>2 debits[selfAccount]' = debits[selfAccount] + amount[self] BY <1>1
<1>3 debitBal(selfAccount) \in Nat BY <1>1 DEF debitBal
<1>4 debitBal(selfAccount)' \in Nat BY <1>1, <1>2 DEF debitBal
<1>5 \A a \in otherAccounts: debitBal(a)' = debitBal(a) BY DEF debitBal
<1>6 \A a \in otherAccounts: debitBal(a) \in Nat BY DEF debitBal
<1>7 \A a \in otherAccounts: debitBal(a)' \in Nat BY DEF debitBal
<1>8 debitBal(selfAccount)' - debitBal(selfAccount) = amount[self] BY <1>1, <1>2, <1>3, <1>4 DEF debitBal
<1>9 IsFiniteSet(otherAccounts) BY accountSetIsFinite, FS_Subset
<1>10 selfAccount \notin otherAccounts OBVIOUS
<1>11 Account = otherAccounts \cup {selfAccount} BY <1>1
<1>12 MapThenSumSet(debitBal, otherAccounts)' = MapThenSumSet(debitBal, otherAccounts)
    BY <1>5, <1>6, <1>7, <1>9, MapThenSumSetEqual DEF MapThenSumSet, MapThenFoldSet, debitBal
<1>13 MapThenSumSet(debitBal, Account)' = MapThenSumSet(debitBal, otherAccounts)' + debitBal(selfAccount)'
    <2>1 MapThenSumSet(debitBal, otherAccounts \cup {selfAccount})' = (MapThenSumSet(debitBal, otherAccounts) + debitBal(selfAccount))'
        BY MapThenSumSetAddElem, <1>7, <1>9, <1>10, <1>4 DEF MapThenSumSet, MapThenFoldSet, debitBal
    <2> QED BY <2>1, <1>11
<1>14 MapThenSumSet(debitBal, otherAccounts)' \in Nat
    <2>1 MapThenSumSet(debitBal, otherAccounts) \in Nat BY <1>6, <1>9, MapThenSumSetType
    <2> QED BY <2>1, <1>12
<1>15 MapThenSumSet(debitBal, Account) \in Nat BY accountSetIsFinite, MapThenSumSetType DEF debitBal
<1>16 MapThenSumSet(debitBal, Account)' \in Nat
    <2>1  MapThenSumSet(debitBal, otherAccounts)' + debitBal(selfAccount)' \in Nat BY <1>14, <1>4, <1>1 DEF debitBal
    <2> QED BY <2>1, <1>13
<1>17 MapThenSumSet(debitBal, Account) = MapThenSumSet(debitBal, otherAccounts)' + debitBal(selfAccount)
    <2>1 MapThenSumSet(debitBal, Account) = MapThenSumSet(debitBal, otherAccounts) + debitBal(selfAccount)
        <3>1 MapThenSumSet(debitBal, otherAccounts \cup {selfAccount}) = MapThenSumSet(debitBal, otherAccounts) + debitBal(selfAccount)
            BY MapThenSumSetAddElem, <1>6, <1>9, <1>10, <1>3
        <3> QED BY <3>1, <1>11
    <2> QED BY <2>1, <1>12
<1>18 MapThenSumSet(debitBal, Account)' = MapThenSumSet(debitBal, Account) + amount[self]
    <2>1 MapThenSumSet(debitBal, Account)' = MapThenSumSet(debitBal, Account) + debitBal(selfAccount)' - debitBal(selfAccount)
        <3>1 MapThenSumSet(debitBal, Account) - debitBal(selfAccount) + debitBal(selfAccount)' =
            MapThenSumSet(debitBal, Account) + debitBal(selfAccount)' - debitBal(selfAccount)
            <4>1 - debitBal(selfAccount) + debitBal(selfAccount)' = debitBal(selfAccount)' - debitBal(selfAccount)
                BY <1>1, <1>2, <1>3, <1>4 DEF debitBal
            <4> QED BY <4>1, <1>15, <1>3, <1>4
        <3>2 MapThenSumSet(debitBal, Account)' = MapThenSumSet(debitBal, Account) - debitBal(selfAccount) + debitBal(selfAccount)'
            <4>1 MapThenSumSet(debitBal, Account)' - debitBal(selfAccount)' + debitBal(selfAccount)' =
                 MapThenSumSet(debitBal, Account) - debitBal(selfAccount) + debitBal(selfAccount)'
                <5>1 MapThenSumSet(debitBal, Account)' - debitBal(selfAccount)' = MapThenSumSet(debitBal, Account) - debitBal(selfAccount)
                    <6>1 MapThenSumSet(debitBal, Account)' - debitBal(selfAccount)' = MapThenSumSet(debitBal, otherAccounts)'
                        BY <1>13, <1>16, <1>4, <1>14 DEF debitBal
                    <6>2 MapThenSumSet(debitBal, Account) - debitBal(selfAccount) = MapThenSumSet(debitBal, otherAccounts)'
                        BY <1>17, <1>15, <1>3, <1>14 DEF debitBal
                    <6> QED BY <6>1, <6>2
                <5> QED BY <5>1, <1>16, <1>15, <1>3, <1>4
            <4> QED BY <4>1, <1>16, <1>15, <1>3, <1>4 DEF debitBal
        <3> QED BY <3>2, <3>1, <1>16, <1>15, <1>3, <1>4
    <2> QED BY <2>1, <1>8, <1>16, <1>15, <1>3, <1>4
<1> QED BY <1>18 DEF DebitTotal


THEOREM debit_IndInv == ASSUME IndInv, NEW self \in Transfer, debit(self)
PROVE IndInv'
<1> USE DEF debit, IndInv, TypeOK
<1>1 TypeOK'
    <2>1 pcLabels' BY DEF pcLabels
    <2>2 accounts' \in [Transfer -> EAccounts] BY EmptyAssumption
        DEF EmptyAccounts, EAccounts, EAccount
    <2> QED BY <2>1, <2>2
<1>2 MoneyTotalPreserved' = MoneyTotalPreserved
    <2>1 CreditTotal' = CreditTotal BY DEF CreditTotal, creditBal, MapThenSumSet, MapThenFoldSet
    <2>3 CreditTotal \in Nat BY CreditTotalInNat
    <2>4 DebitTotal \in Nat BY DebitTotalInNat
    <2>5 AmountPendingTotal \in Nat BY AmountPendingTotalInNat
    <2>2 AmountPendingTotal' - DebitTotal' = AmountPendingTotal - DebitTotal
         /\ AmountPendingTotal' \in Nat
         /\ DebitTotal' \in Nat
        <3>1 DebitTotal' = DebitTotal + amount[self]
            BY debitTotalProperty
        <3>2 AmountPendingTotal' = AmountPendingTotal + amount[self]
             /\ AmountPendingTotal' \in Nat
            <4>1 transPending' = transPending \cup {self} BY DEF transPending, AmountIsPending, pcLabels
            <4>2 self \notin transPending BY DEF transPending, AmountIsPending
            <4>3 IsFiniteSet(transPending) BY transPendingIsFinite
            <4>4 \A t \in transPending: transAmount(t) \in Nat BY transPendingAmountNat
            <4>5 transAmount(self) \in Nat BY DEF transAmount
            <4>6 MapThenSumSet(transAmount, transPending') = MapThenSumSet(transAmount, transPending) + transAmount(self)
                BY <4>1, <4>2, <4>3, <4>4, <4>5, MapThenSumSetAddElem
            <4>7 IsFiniteSet(transPending') BY <4>1, <4>3, FS_AddElement
            <4>8 \A t \in transPending': transAmount(t) \in Nat BY <4>1, <4>4, <4>5
            <4>9 MapThenSumSet(transAmount, transPending') \in Nat BY <4>7, <4>8, MapThenSumSetType
            <4>10 AmountPendingTotal' \in Nat BY <4>9 DEF AmountPendingTotal, transAmount, MapThenSumSet, MapThenFoldSet
            <4> QED BY <4>6, <4>10 DEF AmountPendingTotal, transAmount, MapThenSumSet, MapThenFoldSet
        <3>4 DebitTotal' \in Nat BY <2>4, <3>1
        <3> QED BY <2>4, <2>5, <3>1, <3>2, <3>4
    <2>6 (CreditTotal - DebitTotal + AmountPendingTotal)' = CreditTotal - DebitTotal + AmountPendingTotal
        BY <2>1, <2>2, <2>3, <2>4, <2>5
    <2>7 CreditTotal - DebitTotal + AmountPendingTotal = 0 BY DEF MoneyTotalPreserved, Imbalance
    <2>8 (CreditTotal  - DebitTotal + AmountPendingTotal)' = 0 BY <2>3, <2>4, <2>5, <2>6, <2>7
    <2> QED BY <2>6 DEF MoneyTotalPreserved, Imbalance
<1>3 (pc[self] \notin {"choose_accounts"})' <=> NonEmptyAccounts(self)'
    <2>1 pc[self]' \notin {"choose_accounts"} BY DEF pcLabels
    <2>2 NonEmptyAccounts(self)' BY EmptyAssumption, NAccountAssumption, AccountAssumption
        DEF NonEmptyAccounts
    <2> QED BY <2>1, <2>2
<1>4 \A t \in Transfer \ {self}: (pc[t] \notin {"choose_accounts"})' <=> NonEmptyAccounts(t)'
    BY DEF pcLabels, NonEmptyAccounts
<1> QED BY <1>1, <1>2, <1>3, <1>4


THEOREM creditTotalProperty == ASSUME IndInv, NEW self \in Transfer, credit(self)
PROVE CreditTotal' = CreditTotal + amount[self]
<1> USE DEF credit, IndInv, TypeOK
<1> DEFINE selfAccount == accounts[self].to
<1> DEFINE otherAccounts == Account \ {selfAccount}
<1>1 selfAccount \in Account BY DEF NonEmptyAccounts, EAccounts, EAccount
<1>2 credits[selfAccount]' = credits[selfAccount] + amount[self] BY <1>1
<1>3 creditBal(selfAccount) \in Nat BY <1>1 DEF creditBal
<1>4 creditBal(selfAccount)' \in Nat BY <1>1, <1>2 DEF creditBal
<1>5 \A a \in otherAccounts: creditBal(a)' = creditBal(a) BY DEF creditBal
<1>6 \A a \in otherAccounts: creditBal(a) \in Nat BY DEF creditBal
<1>7 \A a \in otherAccounts: creditBal(a)' \in Nat BY DEF creditBal
<1>8 creditBal(selfAccount)' - creditBal(selfAccount) = amount[self] BY <1>1, <1>2, <1>3, <1>4 DEF creditBal
<1>9 IsFiniteSet(otherAccounts) BY accountSetIsFinite, FS_Subset
<1>10 selfAccount \notin otherAccounts OBVIOUS
<1>11 Account = otherAccounts \cup {selfAccount} BY <1>1
<1>12 MapThenSumSet(creditBal, otherAccounts)' = MapThenSumSet(creditBal, otherAccounts)
    BY <1>5, <1>6, <1>7, <1>9, MapThenSumSetEqual DEF MapThenSumSet, MapThenFoldSet, creditBal
<1>13 MapThenSumSet(creditBal, Account)' = MapThenSumSet(creditBal, otherAccounts)' + creditBal(selfAccount)'
    <2>1 MapThenSumSet(creditBal, otherAccounts \cup {selfAccount})' = (MapThenSumSet(creditBal, otherAccounts) + creditBal(selfAccount))'
        BY MapThenSumSetAddElem, <1>7, <1>9, <1>10, <1>4 DEF MapThenSumSet, MapThenFoldSet, creditBal
    <2> QED BY <2>1, <1>11
<1>14 MapThenSumSet(creditBal, otherAccounts)' \in Nat
    <2>1 MapThenSumSet(creditBal, otherAccounts) \in Nat BY <1>6, <1>9, MapThenSumSetType
    <2> QED BY <2>1, <1>12
<1>15 MapThenSumSet(creditBal, Account) \in Nat BY accountSetIsFinite, MapThenSumSetType DEF creditBal
<1>16 MapThenSumSet(creditBal, Account)' \in Nat
    <2>1  MapThenSumSet(creditBal, otherAccounts)' + creditBal(selfAccount)' \in Nat BY <1>14, <1>4, <1>1 DEF creditBal
    <2> QED BY <2>1, <1>13
<1>17 MapThenSumSet(creditBal, Account) = MapThenSumSet(creditBal, otherAccounts)' + creditBal(selfAccount)
    <2>1 MapThenSumSet(creditBal, Account) = MapThenSumSet(creditBal, otherAccounts) + creditBal(selfAccount)
        <3>1 MapThenSumSet(creditBal, otherAccounts \cup {selfAccount}) = MapThenSumSet(creditBal, otherAccounts) + creditBal(selfAccount)
            BY MapThenSumSetAddElem, <1>6, <1>9, <1>10, <1>3
        <3> QED BY <3>1, <1>11
    <2> QED BY <2>1, <1>12
<1>18 MapThenSumSet(creditBal, Account)' = MapThenSumSet(creditBal, Account) + amount[self]
    <2>1 MapThenSumSet(creditBal, Account)' = MapThenSumSet(creditBal, Account) + creditBal(selfAccount)' - creditBal(selfAccount)
        <3>1 MapThenSumSet(creditBal, Account) - creditBal(selfAccount) + creditBal(selfAccount)' =
            MapThenSumSet(creditBal, Account) + creditBal(selfAccount)' - creditBal(selfAccount)
            <4>1 - creditBal(selfAccount) + creditBal(selfAccount)' = creditBal(selfAccount)' - creditBal(selfAccount)
                BY <1>1, <1>2, <1>3, <1>4 DEF creditBal
            <4> QED BY <4>1, <1>15, <1>3, <1>4
        <3>2 MapThenSumSet(creditBal, Account)' = MapThenSumSet(creditBal, Account) - creditBal(selfAccount) + creditBal(selfAccount)'
            <4>1 MapThenSumSet(creditBal, Account)' - creditBal(selfAccount)' + creditBal(selfAccount)' =
                 MapThenSumSet(creditBal, Account) - creditBal(selfAccount) + creditBal(selfAccount)'
                <5>1 MapThenSumSet(creditBal, Account)' - creditBal(selfAccount)' = MapThenSumSet(creditBal, Account) - creditBal(selfAccount)
                    <6>1 MapThenSumSet(creditBal, Account)' - creditBal(selfAccount)' = MapThenSumSet(creditBal, otherAccounts)'
                        BY <1>13, <1>16, <1>4, <1>14 DEF creditBal
                    <6>2 MapThenSumSet(creditBal, Account) - creditBal(selfAccount) = MapThenSumSet(creditBal, otherAccounts)'
                        BY <1>17, <1>15, <1>3, <1>14 DEF creditBal
                    <6> QED BY <6>1, <6>2
                <5> QED BY <5>1, <1>16, <1>15, <1>3, <1>4
            <4> QED BY <4>1, <1>16, <1>15, <1>3, <1>4 DEF creditBal
        <3> QED BY <3>2, <3>1, <1>16, <1>15, <1>3, <1>4
    <2> QED BY <2>1, <1>8, <1>16, <1>15, <1>3, <1>4
<1> QED BY <1>18 DEF CreditTotal


THEOREM credit_IndInv == ASSUME IndInv, NEW self \in Transfer, credit(self)
PROVE IndInv'
<1> USE DEF credit, IndInv, TypeOK
<1> DEFINE selfAccount == accounts[self].to
<1>1 TypeOK'
    <2>1 pcLabels' BY DEF pcLabels
    <2>2 accounts' \in [Transfer -> EAccounts] BY EmptyAssumption
        DEF EmptyAccounts, EAccounts, EAccount
    <2> QED BY <2>1, <2>2
<1>2 MoneyTotalPreserved' = MoneyTotalPreserved
    <2>1 DebitTotal' = DebitTotal BY DEF DebitTotal, debitBal, MapThenSumSet, MapThenFoldSet
    <2>3 CreditTotal \in Nat BY CreditTotalInNat
    <2>4 DebitTotal \in Nat BY DebitTotalInNat
    <2>5 AmountPendingTotal \in Nat BY AmountPendingTotalInNat
    <2>2 /\ AmountPendingTotal' + CreditTotal' = AmountPendingTotal + CreditTotal
         /\ AmountPendingTotal' \in Nat
         /\ CreditTotal' \in Nat
        <3>1 CreditTotal' = CreditTotal + amount[self] BY creditTotalProperty
        <3>2 /\ AmountPendingTotal = AmountPendingTotal' + amount[self]
             /\ AmountPendingTotal' \in Nat
            <4>1 transPending' = transPending \ {self} BY DEF transPending, AmountIsPending, pcLabels
            <4>2 self \in transPending BY DEF transPending, AmountIsPending
            <4>3 IsFiniteSet(transPending) BY transPendingIsFinite
            <4>4 \A t \in transPending: transAmount(t) \in Nat BY transPendingAmountNat
            <4>5 transAmount(self) \in Nat BY DEF transAmount
            <4>6 MapThenSumSet(transAmount, transPending) = MapThenSumSet(transAmount, transPending') + transAmount(self)
                BY <4>1, <4>2, <4>3, <4>4, <4>5, MapThenSumSetRemElem
            <4>7 IsFiniteSet(transPending') BY <4>1, <4>3, FS_RemoveElement
            <4>8 \A t \in transPending': transAmount(t) \in Nat BY <4>1, <4>4
            <4>9 MapThenSumSet(transAmount, transPending') \in Nat BY <4>7, <4>8, MapThenSumSetType
            <4>10 AmountPendingTotal' \in Nat BY <4>9 DEF AmountPendingTotal, transAmount, MapThenSumSet, MapThenFoldSet
            <4> QED BY <4>6, <4>10 DEF AmountPendingTotal, transAmount, MapThenSumSet, MapThenFoldSet
        <3>3 AmountPendingTotal' + CreditTotal' + amount[self] = AmountPendingTotal + CreditTotal + amount[self]
            BY <3>1, <3>2, <2>3, <2>5
        <3>4 CreditTotal' \in Nat BY <2>3, <3>1
        <3> QED BY <2>3, <2>5, <3>2, <3>3, <3>4
    <2>6 (CreditTotal - DebitTotal + AmountPendingTotal)' = CreditTotal - DebitTotal + AmountPendingTotal
        BY <2>1, <2>2, <2>3, <2>4, <2>5
    <2>7 CreditTotal - DebitTotal + AmountPendingTotal = 0 BY DEF MoneyTotalPreserved, Imbalance
    <2>8 (CreditTotal - DebitTotal + AmountPendingTotal)' = 0 BY <2>3, <2>4, <2>5, <2>6, <2>7
    <2> QED BY <2>6 DEF MoneyTotalPreserved, Imbalance
<1>3 (pc[self] \notin {"choose_accounts"})' <=> NonEmptyAccounts(self)'
    <2>1 pc[self]' \notin {"choose_accounts"} BY DEF pcLabels
    <2>2 NonEmptyAccounts(self)' BY EmptyAssumption, NAccountAssumption, AccountAssumption
        DEF NonEmptyAccounts
    <2> QED BY <2>1, <2>2
<1>4 \A t \in Transfer \ {self}: (pc[t] \notin {"choose_accounts"})' <=> NonEmptyAccounts(t)'
    BY DEF pcLabels, NonEmptyAccounts
<1> QED BY <1>1, <1>2, <1>3, <1>4

====
