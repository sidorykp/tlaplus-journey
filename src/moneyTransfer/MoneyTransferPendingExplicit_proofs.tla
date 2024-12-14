---- MODULE MoneyTransferPendingExplicit_proofs ----
EXTENDS MoneyTransferPendingExplicit, FiniteSetsExt_theorems, FiniteSetTheorems, TLAPS

CONSTANTS NEccount, NDransfer

ASSUME EccountAssumption == Eccount = 1..NEccount

ASSUME DransferAssumption == Dransfer = 1..NDransfer

ASSUME NDransferAssumption == NDransfer \in NNat

ASSUME NEccountAssumption == NEccount \in NNat

ASSUME EvailAssumption == Evail \in NNat

ASSUME EmptyAssumption == Empty = 0

LEMMA pendingTransAmountInNat == ASSUME TypeOK, NEW self \in TN
PROVE pendingTransAmount(self) \in Nat
BY DEF TypeOK, pendingTransAmount, TN

LEMMA transSetIsFinite == ASSUME NDransferAssumption
PROVE IsFiniteSet(Dransfer)
<1>1 Dransfer \in SUBSET (Nat) BY DransferAssumption
<1>2 \A t \in Dransfer: t <= NDransfer BY DransferAssumption
<1> QED BY <1>1, <1>2, FS_BoundedSetOfNaturals DEF NNat

LEMMA AmountPendingTotalInNat == ASSUME NDransferAssumption, IndInv
PROVE AmountPendingTotal \in Nat
<1>1 IsFiniteSet(Dransfer) BY transSetIsFinite, NDransferAssumption
<1>2 IsFiniteSet({t \in Dransfer : AmountIsPending(t)}) BY <1>1, FS_Subset
<1>3 IsFiniteSet(pendingDrans) BY <1>2, FS_Image DEF IndInv, TypeOK
<1>4 \A pt \in pendingDrans: pt \in TN BY DEF TN, IndInv, TypeOK
<1>5 \A pt \in pendingDrans: pendingTransAmount(pt) \in Nat BY <1>4, pendingTransAmountInNat
    DEF IndInv
<1> QED BY <1>3, <1>5, MapThenSumSetType DEF AmountPendingTotal


LEMMA init_Imbalance == ASSUME Init
PROVE Imbalance = 0
<1> USE DEF Init
<1>1 CreditTotal = 0 BY MapThenSumSetEmpty DEF CreditTotal, MapThenSumSetTerse
<1>2 DebitTotal = 0 BY MapThenSumSetEmpty DEF DebitTotal, MapThenSumSetTerse
<1>3 AmountPendingTotal = 0
    BY MapThenSumSetEmpty DEF AmountPendingTotal, AmountIsPending, creditPrecond, isTransKnown
<1> QED BY <1>1, <1>2, <1>3 DEF Imbalance


THEOREM initProperty == ASSUME Init PROVE IndInv
<1> USE DEF Init, IndInv, TypeOK
<1>1 IsFiniteSet(kredits) BY FS_EmptySet
<1>2 IsFiniteSet(bebits) BY FS_EmptySet
<1>3 IsFiniteSet(pendingDrans) BY FS_EmptySet
<1>4 eccounts \in [Dransfer -> EEccounts] BY DEF EEccount, EmptyEccounts, EEccounts
<1>5 pcLabels BY DEF pcLabels, ProcSet
<1>6 \A t \in Dransfer: pc[t] = "init" => initPrecond(t)
    BY DEF initPrecond, isTransKnown
<1>7 \A t \in Dransfer:
        pc[t] \notin {"init"} <=> NonEmptyEccounts(t)
    BY DEF ProcSet, NonEmptyEccounts, EmptyEccounts
<1>8 TransPendingEquivalence BY DEF TransPendingEquivalence, AmountIsPending, creditPrecond,
    isTransKnown, TransInPendingTrans
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, init_Imbalance
    DEF PendingTransDerived


THEOREM retryDebit_AmountPendingTotal == ASSUME IndInv, NEW self \in Dransfer, retryDebit(self)
PROVE AmountPendingTotal' = AmountPendingTotal
BY DEF retryDebit, AmountPendingTotal


THEOREM retryDebit_IndInv == ASSUME IndInv, NEW self \in Dransfer, retryDebit(self)
PROVE IndInv'
<1> USE DEF IndInv, TypeOK, retryDebit
<1>1 pcLabels' BY DEF pcLabels
<1>2 Imbalance' = Imbalance BY retryDebit_AmountPendingTotal
    DEF Imbalance, creditPrecond, CreditTotal, DebitTotal
<1>3 Imbalance' = 0 BY <1>2
<1>4 \A t \in Dransfer:
    (\/ eccounts[t] = EmptyEccounts
     \/ DifferentEccounts(t) /\ NonEmptyEccounts(t))'
    BY DEF EmptyEccounts, DifferentEccounts, NonEmptyEccounts
<1>5 \A t \in Dransfer: pc'[t] = "init" => initPrecond(t)'
    BY DEF pcLabels
<1>6 \A t \in Dransfer: pc'[t] \notin {"init"} <=> NonEmptyEccounts(t)'
    BY DEF NonEmptyEccounts, pcLabels
<1>7 TransPendingEquivalence' BY DEF TransPendingEquivalence, TransInPendingTrans,
    pcLabels, AmountIsPending, creditPrecond, isTransKnown
<1>8 PendingTransDerived' BY DEF PendingTransDerived
<1> QED BY <1>1, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8


THEOREM init_AmountPendingTotal == ASSUME IndInv, NEW self \in Dransfer, init(self)
PROVE AmountPendingTotal' = AmountPendingTotal
BY DEF init, AmountPendingTotal


THEOREM init_IndInv == ASSUME IndInv, NEW self \in Dransfer, init(self)
PROVE IndInv'
<1> DEFINE am == emount'[self]
<1> DEFINE selfEccounts == eccounts'[self]
<1> DEFINE account1 == selfEccounts.from
<1> DEFINE account2 == selfEccounts.to
<1> USE DEF IndInv, TypeOK, init
<1>1 emount' \in [Dransfer -> Nat] BY DEF NNat
<1>2 selfEccounts \in EEccounts BY DEF EEccounts, EEccount
<1>3 eccounts' \in [Dransfer -> EEccounts] BY <1>2 
<1>4 pcLabels' BY DEF pcLabels
<1>5 Imbalance' = Imbalance BY init_AmountPendingTotal DEF Imbalance, creditPrecond, CreditTotal, DebitTotal
<1>6 Imbalance' = 0 BY <1>5
<1>7 (\/ eccounts[self] = EmptyEccounts
      \/ DifferentEccounts(self) /\ NonEmptyEccounts(self))'
    BY EmptyAssumption, EccountAssumption DEF DifferentEccounts, NonEmptyEccounts
<1>8 \A t \in Dransfer:
    (\/ eccounts[t] = EmptyEccounts
     \/ DifferentEccounts(t) /\ NonEmptyEccounts(t))'
    BY <1>7 DEF EmptyEccounts, DifferentEccounts, NonEmptyEccounts
<1>9 initPrecond(self)' BY DEF initPrecond, isTransKnown
<1>10 \A t \in Dransfer: pc'[t] = "init" => initPrecond(t)' BY <1>9 DEF pcLabels
<1>11 NonEmptyEccounts(self)' BY EmptyAssumption DEF NonEmptyEccounts
<1>12 pc'[self] \notin {"init"} <=> NonEmptyEccounts(self)' BY <1>11 DEF pcLabels
<1>13 \A t \in Dransfer: pc'[t] \notin {"init"} <=> NonEmptyEccounts(t)'
    BY <1>12 DEF NonEmptyEccounts, pcLabels
<1>14 ~AmountIsPending(self) BY DEF AmountIsPending, creditPrecond, initPrecond
<1>15 ~AmountIsPending(self)' BY DEF AmountIsPending, creditPrecond, initPrecond
\* the fact that allows not to use PendingTransUniqueness
<1>16 ~\E d \in bebits: d[1].t = self BY <1>14 DEF initPrecond,
    AmountIsPending, creditPrecond, isTransKnown, AT
<1>17 TransInPendingTrans(self)' = TransInPendingTrans(self)
    <2>1 ~TransInPendingTrans(self) BY <1>14 DEF TransPendingEquivalence, TransInPendingTrans
    <2>2 ~\E tp \in pendingDrans: tp[1] = self /\ tp[2] = am BY <1>16 DEF PendingTransDerived
    <2> QED BY <2>1, <2>2 DEF TransInPendingTrans
<1>18 (AmountIsPending(self) <=> TransInPendingTrans(self))' = (AmountIsPending(self) <=> TransInPendingTrans(self))
    BY <1>14, <1>15, <1>17
<1>19 \A t \in Dransfer \ {self}: (AmountIsPending(t) <=> TransInPendingTrans(t))'
    = (AmountIsPending(t) <=> TransInPendingTrans(t)) BY DEF AmountIsPending, TransInPendingTrans,
        creditPrecond, isTransKnown, pcLabels
<1>20 TransPendingEquivalence'  = TransPendingEquivalence BY <1>18, <1>19 DEF TransPendingEquivalence
<1>21 PendingTransDerived' BY DEF PendingTransDerived
<1> QED BY <1>1, <1>3, <1>4, <1>6, <1>8, <1>10, <1>13, <1>20, <1>21


LEMMA debit_DebitTotal_debitPrecond_success == ASSUME IndInv, NEW self \in Dransfer, debit(self),
debitPrecond(self), ~(UNCHANGED <<bebits, pendingDrans>>)
PROVE DebitTotal' = DebitTotal + emount[self]
<1> DEFINE a == eccounts[self].from
<1> DEFINE nadd == <<[a |-> a, t |-> self], emount[self]>>
<1> USE DEF IndInv, TypeOK, debitPrecond
<1>1 nadd \notin bebits BY DEF isTransKnown, AT
<1>2 bebits' = bebits \cup {nadd} BY DEF debit
<1>3 \A nb \in bebits: opEmount(nb) \in Nat BY DEF opEmount
<1>4 opEmount(nadd) \in Nat BY DEF opEmount
<1>5 MapThenSumSet(opEmount, bebits') =
    MapThenSumSet(opEmount, bebits) + opEmount(nadd)
    BY <1>1, <1>2, <1>3, <1>4, MapThenSumSetAddElem
<1>6 DebitTotal' = DebitTotal + opEmount(nadd)
    BY <1>5 DEF DebitTotal, MapThenSumSetTerse, MapThenSumSet, MapThenFoldSet
<1> QED BY <1>6 DEF opEmount

LEMMA debit_DebitTotal_notDebitPrecond_or_retryDebit == ASSUME IndInv, NEW self \in Dransfer, debit(self),
~debitPrecond(self) \/ UNCHANGED <<bebits, pendingDrans>>
PROVE DebitTotal' = DebitTotal
BY DEF debit, DebitTotal


LEMMA debit_AmountPendingTotal_debitPrecond_success == ASSUME IndInv, NEW self \in Dransfer, debit(self),
debitPrecond(self), ~(UNCHANGED <<bebits, pendingDrans>>)
PROVE AmountPendingTotal' = AmountPendingTotal + emount[self]
<1> DEFINE nadd == <<self, emount[self]>>
<1>1 pendingDrans' = pendingDrans \cup {nadd}
    BY DEF debit
<1> USE DEF IndInv, TypeOK
<1>2 nadd \notin pendingDrans BY DEF TransPendingEquivalence, TransInPendingTrans,
    AmountIsPending, isTransKnown, debitPrecond, creditPrecond, AT
<1>3 \A pt \in pendingDrans: pendingTransAmount(pt) \in Nat BY pendingTransAmountInNat
<1>4 pendingTransAmount(nadd) \in Nat BY DEF debit, pendingTransAmount
<1>5 MapThenSumSet(pendingTransAmount, pendingDrans') =
    MapThenSumSet(pendingTransAmount, pendingDrans) + pendingTransAmount(nadd)
    BY <1>1, <1>2, <1>3, <1>4, MapThenSumSetAddElem
<1>6 AmountPendingTotal' = AmountPendingTotal + pendingTransAmount(nadd)
    BY <1>5 DEF AmountPendingTotal
<1> QED BY <1>6 DEF pendingTransAmount

LEMMA debit_AmountPendingTotal_notDebitPrecond_or_retryDebit == ASSUME IndInv, NEW self \in Dransfer, debit(self),
~debitPrecond(self) \/ UNCHANGED <<bebits, pendingDrans>>
PROVE AmountPendingTotal' = AmountPendingTotal
BY DEF debit, AmountPendingTotal

LEMMA debit_Imbalance == ASSUME IndInv, NEW self \in Dransfer, debit(self)
PROVE Imbalance' = Imbalance
<1>1 kredits' = kredits BY DEF debit
<1>2 CreditTotal' = CreditTotal
    BY <1>1 DEF CreditTotal
<1>3 CASE debitPrecond(self) /\ ~(UNCHANGED <<bebits, pendingDrans>>)
    <2>1 DebitTotal' = DebitTotal + emount[self] BY <1>3, debit_DebitTotal_debitPrecond_success DEF debit
    <2>2 AmountPendingTotal' = AmountPendingTotal + emount[self] BY <1>3,
        debit_AmountPendingTotal_debitPrecond_success DEF debit
    <2>3 AmountPendingTotal \in Nat BY AmountPendingTotalInNat, NDransferAssumption
    <2> QED BY <1>2, <2>1, <2>2, <2>3 DEF debit, Imbalance
<1>4 CASE ~debitPrecond(self) \/ UNCHANGED <<bebits, pendingDrans>>
    <2> QED BY <1>4, <1>2, debit_DebitTotal_notDebitPrecond_or_retryDebit,
        debit_AmountPendingTotal_notDebitPrecond_or_retryDebit
        DEF debit, Imbalance
<1> QED BY <1>3, <1>4

THEOREM debit_IndInv_common == ASSUME IndInv, NEW self \in Dransfer, debit(self)
PROVE (
    /\ kredits \in SUBSET (AT \X Nat)
    /\ IsFiniteSet(kredits)
    /\ CommonIndInv)'
<1> USE DEF IndInv, TypeOK, CommonIndInv
<1>1 kredits' \in SUBSET (AT \X Nat) BY DEF debit
<1>2 IsFiniteSet(kredits)' BY DEF debit
<1>3 emount' \in [Dransfer -> Nat] BY DEF debit
<1>4 eccounts' \in [Dransfer -> EEccounts] BY DEF debit
<1>5 pcLabels' BY DEF debit, pcLabels
<1>6 \A t \in Dransfer:
    \/ eccounts'[t] = EmptyEccounts
    \/ DifferentEccounts(t)' /\ NonEmptyEccounts(t)'
    BY DEF debit, EmptyEccounts, DifferentEccounts, NonEmptyEccounts
<1>7 \A t \in Dransfer: pc'[t] = "init" => initPrecond(t)'
    BY DEF debit, pcLabels, IndInv, TypeOK
<1>8 \A t \in Dransfer: NonEmptyEccounts(t)' = NonEmptyEccounts(t)
    BY DEF debit, NonEmptyEccounts
<1>9 NonEmptyEccounts(self)' = NonEmptyEccounts(self)
    BY <1>8
<1>10 pc'[self] \notin {"init"} <=> NonEmptyEccounts(self)'
    BY <1>8 DEF debit, pcLabels
<1>11 \A t \in Dransfer \ {self}: pc'[t] \notin {"init"} <=> pc[t] \notin {"init"}
    BY DEF debit, pcLabels
<1>12 \A t \in Dransfer \ {self}: pc'[t] \notin {"init"} <=> NonEmptyEccounts(t)'
    BY <1>8, <1>11
<1>13 \A t \in Dransfer: pc'[t] \notin {"init"} <=> NonEmptyEccounts(t)'
    BY <1>10, <1>12
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>13, debit_Imbalance


THEOREM debit_IndInv == ASSUME IndInv, NEW self \in Dransfer, debit(self)
PROVE IndInv'
<1> DEFINE a == eccounts[self].from
<1> DEFINE nadd == <<[a |-> a, t |-> self], emount[self]>>
<1> DEFINE ptAdd == <<self, emount[self]>>
<1> USE DEF IndInv, TypeOK, CommonIndInv
<1>1 CASE debitPrecond(self) /\ ~(UNCHANGED <<bebits, pendingDrans>>)
    <2>1 bebits' = bebits \cup {nadd} BY <1>1 DEF debit
    <2>2 a \in EEccount BY DEF EEccounts
    <2>3 a # Empty BY DEF debit, NonEmptyEccounts
    <2>4 a \in Eccount BY <2>2, <2>3 DEF EEccount
    <2>5 nadd \in AT \X Nat BY <2>4 DEF AT
    <2>6 bebits' \in SUBSET (AT \X Nat)
        BY <2>1, <2>5
    <2>7 IsFiniteSet(bebits)' BY <1>1, FS_AddElement DEF debit
    <2>8 pendingDrans' = pendingDrans \cup {ptAdd} BY <1>1 DEF debit
    <2>9 ptAdd \in TN BY DEF TN
    <2>10 pendingDrans' \in SUBSET TN BY <2>8, <2>9
    <2>11 IsFiniteSet(pendingDrans)' BY <1>1, FS_AddElement DEF debit
    
    <2>12 kredits' = kredits BY DEF debit
    
    <2>13 (AmountIsPending(self) <=> TransInPendingTrans(self))'
        <3>1 ~AmountIsPending(self) BY <1>1 DEF debit, AmountIsPending, creditPrecond,
            debitPrecond, pcLabels, isTransKnown
        <3>2 \E dc \in bebits': dc[1].a = eccounts[self].from /\ dc[1].t = self BY <1>1 DEF debit
        <3>3 ~(\E dc \in bebits: dc[1].a = eccounts[self].to /\ dc[1].t = self)'
            BY <1>1, <3>1 DEF debit, AmountIsPending, creditPrecond,
            pcLabels, isTransKnown
        <3>4 AmountIsPending(self)' BY <1>1, <3>1, <3>2, <3>3 DEF debit, AmountIsPending, creditPrecond,
            pcLabels, isTransKnown
        <3>5 ~TransInPendingTrans(self) BY <1>1, <3>1 DEF debit, TransPendingEquivalence
        <3>6 TransInPendingTrans(self)' BY <1>1, <2>8 DEF debit, TransInPendingTrans
        <3> QED BY <3>1, <3>4, <3>5, <3>6
    <2>14 \A t \in Dransfer \ {self}: TransInPendingTrans(t) = TransInPendingTrans(t)'
        BY <1>1, <2>1, <2>8, <2>12
        DEF TransInPendingTrans, debit
    <2>16 \A t \in Dransfer \ {self}: AmountIsPending(t) = AmountIsPending(t)'
        BY <1>1, <2>1, <2>8, <2>12
        DEF debit, AmountIsPending, pcLabels, creditPrecond, isTransKnown
    <2>17 TransPendingEquivalence' = TransPendingEquivalence
        BY <2>13, <2>14, <2>16 DEF TransPendingEquivalence

    <2>18 \E d \in bebits': d[1].t = ptAdd[1] /\ d[2] = ptAdd[2] BY <1>1, <2>1
    <2> HIDE DEF IndInv, TypeOK, CommonIndInv
    <2>19 \A pt \in pendingDrans' \ {ptAdd}: \E d \in bebits': d[1].t = pt[1] /\ d[2] = pt[2]
        BY <1>1, <2>1, <2>8 DEF debit, IndInv, TypeOK, PendingTransDerived
    <2>20 \A pt \in pendingDrans': \E d \in bebits': d[1].t = pt[1] /\ d[2] = pt[2]
        BY <1>1, <2>18, <2>19
    <2>21 PendingTransDerived' BY <2>20 DEF debit, PendingTransDerived

    <2> QED BY <2>6, <2>7, <2>10, <2>11, <2>17, <2>21, debit_IndInv_common, debit_Imbalance DEF IndInv, TypeOK, CommonIndInv
<1>2 CASE ~debitPrecond(self) \/ UNCHANGED <<bebits, pendingDrans>>
    <2>1 bebits' \in SUBSET (AT \X Nat) BY <1>2 DEF debit
    <2>2 IsFiniteSet(bebits)' BY <1>2 DEF debit
    <2>3 pendingDrans' \in SUBSET TN BY <1>2 DEF debit
    <2>4 IsFiniteSet(pendingDrans)' BY <1>2 DEF debit
    <2>5 TransPendingEquivalence' BY <1>2 DEF debit, TransPendingEquivalence, TransInPendingTrans,
        pcLabels, AmountIsPending, creditPrecond, isTransKnown
    <2>6 PendingTransDerived'  BY <1>2 DEF debit, PendingTransDerived
    <2> QED BY <1>1, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, debit_IndInv_common, debit_Imbalance
<1> QED BY <1>1, <1>2


LEMMA credit_AmountPendingTotal_creditPrecond == ASSUME IndInv, NEW self \in Dransfer, credit(self),
creditPrecond(self)
PROVE AmountPendingTotal' = AmountPendingTotal - emount[self]
<1> DEFINE nadd == <<self, emount[self]>>
<1> USE DEF IndInv, TypeOK
<1>1 pendingDrans' = pendingDrans \ {nadd} BY DEF credit
<1>2 \A pt \in pendingDrans: pendingTransAmount(pt) \in Nat BY pendingTransAmountInNat
<1>3 nadd \in pendingDrans
    <2>1 AmountIsPending(self) BY DEF credit, AmountIsPending
    <2>2 TransInPendingTrans(self) BY <2>1 DEF TransPendingEquivalence
    <2> QED BY <2>2 DEF TN, TransInPendingTrans
<1>4 AmountPendingTotal = AmountPendingTotal' + pendingTransAmount(nadd)
    BY <1>1, <1>2, <1>3, MapThenSumSetRemElem DEF credit, AmountPendingTotal
<1>5 AmountPendingTotal = AmountPendingTotal' + emount[self] BY <1>4 DEF pendingTransAmount
<1>6 AmountPendingTotal \in Nat BY AmountPendingTotalInNat, NDransferAssumption
<1>7 IsFiniteSet(pendingDrans') BY <1>1, FS_Subset
<1>8 \A pt \in pendingDrans': pendingTransAmount(pt) \in Nat BY <1>1, <1>2
<1>9 MapThenSumSet(pendingTransAmount, pendingDrans') \in Nat BY <1>1, <1>7, <1>8,
    MapThenSumSetType
<1> QED BY <1>5, <1>6, <1>9 DEF AmountPendingTotal


\* practically a copy of debit_DebitTotal
LEMMA credit_CreditTotal_success == ASSUME IndInv, NEW self \in Dransfer, credit(self),
creditPrecond(self), ~(UNCHANGED <<kredits, pendingDrans>>)
PROVE CreditTotal' = CreditTotal + emount[self]
<1> DEFINE a == eccounts[self].to
<1> DEFINE nadd == <<[a |-> a, t |-> self], emount[self]>>
<1> USE DEF IndInv, TypeOK, creditPrecond
<1>1 nadd \notin kredits BY DEF isTransKnown, AT
<1>2 kredits' = kredits \cup {nadd} BY DEF credit
<1>3 \A nb \in kredits: opEmount(nb) \in Nat BY DEF opEmount
<1>4 opEmount(nadd) \in Nat BY DEF opEmount
<1>5 MapThenSumSet(opEmount, kredits') =
    MapThenSumSet(opEmount, kredits) + opEmount(nadd)
    BY <1>1, <1>2, <1>3, <1>4, MapThenSumSetAddElem
<1>6 CreditTotal' = CreditTotal + opEmount(nadd)
    BY <1>5 DEF CreditTotal, MapThenSumSetTerse, MapThenSumSet, MapThenFoldSet
<1> QED BY <1>6 DEF opEmount

\* practically a copy of init_AmountPendingTotal
LEMMA credit_AmountPendingTotal_notCreditPrecond_or_retryCredit == ASSUME IndInv, NEW self \in Dransfer, credit(self),
~creditPrecond(self) \/ UNCHANGED <<kredits, pendingDrans>>
PROVE AmountPendingTotal' = AmountPendingTotal
BY DEF credit, AmountPendingTotal


LEMMA credit_Imbalance == ASSUME IndInv, NEW self \in Dransfer, credit(self)
PROVE Imbalance' = Imbalance
<1>1 bebits' = bebits BY DEF credit
<1>2 DebitTotal' = DebitTotal
    BY <1>1 DEF DebitTotal
<1>3 CASE creditPrecond(self) /\ ~UNCHANGED <<kredits, pendingDrans>>
    <2>1 CreditTotal' = CreditTotal + emount[self] BY <1>3, credit_CreditTotal_success
    <2>2 AmountPendingTotal' = AmountPendingTotal - emount[self] BY <1>3, credit_AmountPendingTotal_creditPrecond
    <2>3 emount[self] \in Nat BY DEF IndInv, TypeOK
    <2>4 \A c \in kredits: opEmount(c) \in Nat BY DEF opEmount, IndInv, TypeOK
    <2>5 CreditTotal \in Nat BY <2>4, MapThenSumSetType DEF CreditTotal, IndInv, TypeOK,
        MapThenSumSetTerse, MapThenSumSet, MapThenFoldSet
    <2>6 \A d \in bebits: opEmount(d) \in Nat BY DEF opEmount, IndInv, TypeOK
    <2>7 DebitTotal \in Nat BY <2>6, MapThenSumSetType DEF DebitTotal, IndInv, TypeOK,
        MapThenSumSetTerse, MapThenSumSet, MapThenFoldSet
    <2>8 AmountPendingTotal \in Nat BY AmountPendingTotalInNat, NDransferAssumption
    <2>9 CreditTotal' + AmountPendingTotal' = CreditTotal + AmountPendingTotal BY <2>1, <2>2, <2>3, <2>5, <2>8
    <2>10 (CreditTotal' + AmountPendingTotal') - DebitTotal' = (CreditTotal + AmountPendingTotal) - DebitTotal
        BY <1>2, <2>9
    <2>11 CreditTotal' - DebitTotal' + AmountPendingTotal' = CreditTotal - DebitTotal + AmountPendingTotal
        BY <2>10 DEF credit
    <2> QED BY <2>11 DEF Imbalance, credit
<1>4 CASE ~creditPrecond(self) \/ UNCHANGED <<kredits, pendingDrans>>
    <2>1 AmountPendingTotal' = AmountPendingTotal BY <1>4, credit_AmountPendingTotal_notCreditPrecond_or_retryCredit
    <2>2 CreditTotal' = CreditTotal BY <1>4 DEF credit
    <2> QED BY <1>2, <2>1, <2>2 DEF credit, Imbalance
<1> QED BY <1>3, <1>4


THEOREM credit_IndInv_common == ASSUME IndInv, NEW self \in Dransfer, credit(self)
PROVE (
    /\ bebits \in SUBSET (AT \X Nat)
    /\ IsFiniteSet(bebits)
    /\ pendingDrans \in SUBSET TN
    /\ IsFiniteSet(pendingDrans)
    /\ CommonIndInv
    /\ TransPendingEquivalence
    /\ PendingTransDerived)'
<1> USE DEF IndInv, TypeOK, CommonIndInv, credit
<1>1 pcLabels' BY DEF pcLabels
<1>2 \A t \in Dransfer:
    \/ eccounts'[t] = EmptyEccounts
    \/ DifferentEccounts(t)' /\ NonEmptyEccounts(t)'
    BY DEF EmptyEccounts, DifferentEccounts, NonEmptyEccounts
<1>3 \A t \in Dransfer: pc'[t] = "init" => initPrecond(t)' BY DEF pcLabels
<1>4 \A t \in Dransfer: NonEmptyEccounts(t)' = NonEmptyEccounts(t)
    BY DEF NonEmptyEccounts
<1>5 \A t \in Dransfer: pc'[t] \notin {"init"} <=> NonEmptyEccounts(t)'
    BY <1>4 DEF pcLabels
<1>6 IsFiniteSet(pendingDrans)'
    <2>1 CASE ~creditPrecond(self) BY <2>1
    <2>2 CASE creditPrecond(self) BY <2>2 DEF TN, AT, FS_RemoveElement
    <2> QED BY <2>1, <2>2
<1>7 AmountIsPending(self)' <=> TransInPendingTrans(self)'
    <2>1 CASE ~creditPrecond(self)
        <3>1 AmountIsPending(self)' = AmountIsPending(self) BY <2>1 DEF AmountIsPending
        <3>2 TransInPendingTrans(self)' = TransInPendingTrans(self) BY <2>1
            DEF TransInPendingTrans
        <3> QED BY <2>1, <3>2, <3>2
            DEF TransInPendingTrans
     <2>2 CASE creditPrecond(self) BY <2>2 DEF TransInPendingTrans, credit, AmountIsPending, pcLabels
     <2> QED BY <2>1, <2>2
<1>8 TransPendingEquivalence'
    <2>1 CASE ~creditPrecond(self)
        <3>1 AmountIsPending(self)' = AmountIsPending(self) BY <2>1 DEF AmountIsPending
        <3>2 TransInPendingTrans(self)' = TransInPendingTrans(self) BY <2>1
            DEF TransInPendingTrans
        <3> QED BY <2>1, <3>1, <3>2 DEF TransPendingEquivalence,
            AmountIsPending, TransInPendingTrans, pcLabels, creditPrecond
    <2>2 CASE creditPrecond(self) BY <2>2, <1>7 DEF TransPendingEquivalence,
        TransInPendingTrans, AmountIsPending, pcLabels, creditPrecond,
        isTransKnown
    <2> QED BY <2>1, <2>2
<1>9 PendingTransDerived' BY DEF PendingTransDerived
<1> QED BY <1>1, <1>2, <1>3, <1>5, <1>6, <1>8, <1>9,
    credit_Imbalance


THEOREM credit_IndInv == ASSUME IndInv, NEW self \in Dransfer, credit(self)
PROVE IndInv'
<1> DEFINE a == eccounts[self].to
<1> DEFINE nadd == <<[a |-> a, t |-> self], emount[self]>>
<1> USE DEF IndInv, TypeOK, CommonIndInv
<1>1 CASE creditPrecond(self)
    <2>3 kredits' = kredits \cup {nadd} BY <1>1 DEF credit
    <2>4 a \in EEccount BY DEF EEccounts
    <2>5 a # Empty BY DEF credit, NonEmptyEccounts
    <2>6 a \in Eccount BY <2>4, <2>5 DEF EEccount
    <2>7 nadd \in AT \X Nat BY <2>6 DEF AT
    <2>8 kredits' \in SUBSET (AT \X Nat)
        BY <2>3, <2>7
    <2>9 IsFiniteSet(kredits)' BY <1>1, FS_AddElement DEF credit
    <2> QED BY <2>8, <2>9, <1>1, credit_IndInv_common, credit_Imbalance
        DEF IndInv, TypeOK, CommonIndInv
<1>2 CASE ~creditPrecond(self)
    <2>3 kredits' \in SUBSET (AT \X Nat) BY <1>2 DEF credit
    <2>4 IsFiniteSet(kredits)' BY <1>2 DEF credit
    <2> QED BY <2>3, <2>4, <1>1, credit_IndInv_common, credit_Imbalance
<1> QED BY <1>1, <1>2


THEOREM nextNonTerminating == ASSUME IndInv, Next, ~Terminating
PROVE IndInv'
<1> SUFFICES ASSUME IndInv, NEW self \in Dransfer, trans(self)
    PROVE IndInv'
    BY DEF Next, trans
<1>1 CASE init(self) BY <1>1, init_IndInv
<1>2 CASE debit(self) BY <1>2, debit_IndInv
<1>3 CASE retryDebit(self) BY <1>3, retryDebit_IndInv
<1>4 CASE credit(self) BY <1>4, credit_IndInv
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF trans


THEOREM unchangedVarsProperty == IndInv /\ UNCHANGED vars => IndInv'
<1> SUFFICES ASSUME IndInv, UNCHANGED vars
    PROVE IndInv'
    OBVIOUS
<1> USE DEF vars
<1>1 TypeOK' = TypeOK BY DEF TypeOK, pcLabels,
    TransInPendingTrans, AmountIsPending, creditPrecond
<1>2 (/\ \A t \in Dransfer:
        \/ eccounts[t] = EmptyEccounts
        \/ DifferentEccounts(t) /\ NonEmptyEccounts(t))' =
      /\ \A t \in Dransfer:
        \/ eccounts[t] = EmptyEccounts
        \/ DifferentEccounts(t) /\ NonEmptyEccounts(t)
    BY DEF DifferentEccounts, NonEmptyEccounts
<1>3 (/\ \A t \in Dransfer: pc[t] = "init" => initPrecond(t))' =
    /\ \A t \in Dransfer: pc[t] = "init" => initPrecond(t)
    BY DEF initPrecond
<1>4 (/\ \A t \in Dransfer:
        pc[t] \notin {"init"} <=> NonEmptyEccounts(t))' =
      /\ \A t \in Dransfer:
        pc[t] \notin {"init"} <=> NonEmptyEccounts(t)
    BY DEF NonEmptyEccounts
<1>5 CreditTotal' = CreditTotal BY DEF CreditTotal
<1>6 DebitTotal' = DebitTotal BY DEF DebitTotal
<1>7 AmountPendingTotal' = AmountPendingTotal BY DEF AmountPendingTotal
<1>8 (Imbalance = 0)' = (Imbalance = 0) BY <1>5, <1>6, <1>7 DEF Imbalance
<1>9 TransPendingEquivalence' = TransPendingEquivalence BY DEF TransPendingEquivalence,
    IndInv, TypeOK, AmountIsPending, TransInPendingTrans, pcLabels, creditPrecond
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>8, <1>9 DEF IndInv


THEOREM nextTerminating == ASSUME IndInv, Next, Terminating
PROVE IndInv'
<1> SUFFICES ASSUME IndInv, Terminating
    PROVE IndInv'
    BY DEF Next, Terminating
<1>1 UNCHANGED vars BY DEF Terminating
<1> QED BY <1>1, unchangedVarsProperty


THEOREM nextProperty == IndInv /\ Next => IndInv'
<1> SUFFICES ASSUME IndInv, Next
    PROVE IndInv'
    OBVIOUS
<1> USE DEF IndInv, Next, Terminating
<1>1 CASE ~Terminating
    <2> QED BY <1>1, nextNonTerminating
<1>2 CASE Terminating
    <2> QED BY <1>2, nextTerminating    
<1> QED BY <1>1, <1>2


THEOREM IndInvPreservedE == Spec => []IndInv
<1>1 IndInv /\ UNCHANGED vars => IndInv'
    BY unchangedVarsProperty
<1> QED BY PTL, initProperty, nextProperty, <1>1 DEF Spec

====
