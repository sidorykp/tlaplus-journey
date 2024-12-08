----MODULE MoneyTransferEquivalence----
EXTENDS MoneyTransfer, TLAPS, FiniteSetsExt_theorems, FiniteSetTheorems

pendingTransDerived == {<<t, amount[t]>>: t \in {t \in Transfer: AmountIsPending(t)}}

E == INSTANCE MoneyTransferPendingExplicit WITH pendingTrans <- pendingTransDerived

ASSUME EquivalentSymbolsAssumption ==
    /\ E!EmptyAccounts = EmptyAccounts

THEOREM InitEquivalence == E!Init <=> Init
BY EquivalentSymbolsAssumption DEF E!Init, Init, pendingTransDerived,
    E!ProcSet, ProcSet,
    AmountIsPending, creditPrecond, isTransKnown, isTransKnownToItem

THEOREM initEquivalence == ASSUME NEW self \in Transfer, E!init(self)
PROVE init(self)
<1>1 CASE initPrecond(self)
    <2> QED BY <1>1 DEF E!init, init, pendingTransDerived,
    E!initPrecond, initPrecond,
    E!isTransKnown, E!isTransKnownToItem,
    isTransKnown, isTransKnownToItem,
    AmountIsPending, creditPrecond
<1>2 CASE ~initPrecond(self)
    <2> QED BY <1>2 DEF E!init, init, pendingTransDerived,
    E!initPrecond, initPrecond,
    E!isTransKnown, E!isTransKnownToItem,
    isTransKnown, isTransKnownToItem,
    AmountIsPending, creditPrecond
<1> QED BY <1>1, <1>2

THEOREM initEquivalenceRev == ASSUME NEW self \in Transfer, init(self)
PROVE E!init(self)
<1>1 CASE initPrecond(self)
    <2>1 ~AmountIsPending(self) BY <1>1 DEF init, AmountIsPending, creditPrecond,
        isTransKnown, isTransKnownToItem, initPrecond
    <2>2 UNCHANGED {<<t, amount[t]>>: t \in {t \in Transfer : AmountIsPending(t)}}
        BY <1>1, <2>1 DEF init, AmountIsPending, creditPrecond,
        isTransKnown, isTransKnownToItem, initPrecond
    <2> QED BY <2>2
        DEF pendingTransDerived,
        E!init, init,
        E!initPrecond, initPrecond,
        E!isTransKnown, E!isTransKnownToItem,
        isTransKnown, isTransKnownToItem,
        AmountIsPending, creditPrecond
<1>2 CASE ~initPrecond(self)
    <2>1 ~AmountIsPending(self) BY <1>2 DEF init, AmountIsPending, creditPrecond,
        isTransKnown, isTransKnownToItem, initPrecond
    <2>2 UNCHANGED {<<t, amount[t]>>: t \in {t \in Transfer : AmountIsPending(t)}}
        BY <1>2, <2>1 DEF init, AmountIsPending, creditPrecond,
        isTransKnown, isTransKnownToItem, initPrecond
    <2> QED BY <2>2
        DEF pendingTransDerived,
        E!init, init,
        E!initPrecond, initPrecond,
        E!isTransKnown, E!isTransKnownToItem,
        isTransKnown, isTransKnownToItem,
        AmountIsPending, creditPrecond
<1> QED BY <1>1, <1>2


THEOREM debitEquivalence == ASSUME NEW self \in Transfer, E!debit(self)
PROVE debit(self)
BY DEF E!debit, debit, pendingTransDerived,
    AmountIsPending, debitPrecond, isTransKnown, isTransKnownToItem,
    E!debitPrecond

THEOREM debitEquivalenceRev == ASSUME NEW self \in Transfer, debit(self)
PROVE E!debit(self)
BY DEF E!debit, debit, pendingTransDerived,
    AmountIsPending, debitPrecond, isTransKnown, isTransKnownToItem,
    E!debitPrecond
    
THEOREM crashEquivalence == ASSUME NEW self \in Transfer, E!crash(self)
PROVE crash(self)
<1>1 CASE E!debitPrecond(self)
    <2>1 debitPrecond(self) BY <1>1 DEF
        E!crash, crash,
        E!debitPrecond, debitPrecond,
        E!isTransKnown, isTransKnown,
        E!isTransKnownToItem, isTransKnownToItem
    <2> QED BY <1>1, <2>1 DEF E!crash, crash
<1>2 CASE ~E!debitPrecond(self)
    <2>1 ~debitPrecond(self) BY <1>2 DEF
        E!crash, crash,
        E!debitPrecond, debitPrecond,
        E!isTransKnown, isTransKnown,
        E!isTransKnownToItem, isTransKnownToItem
    <2> QED BY <1>2, <2>1 DEF E!crash, crash
<1> QED BY <1>1, <1>2
    
THEOREM crashEquivalenceRev == ASSUME NEW self \in Transfer, crash(self)
PROVE E!crash(self)
BY DEF E!crash, crash, pendingTransDerived,
    AmountIsPending, creditPrecond, isTransKnown, isTransKnownToItem

THEOREM creditEquivalence == ASSUME NEW self \in Transfer, E!credit(self)
PROVE credit(self)
BY DEF E!credit, credit, pendingTransDerived,
    E!creditPrecond

THEOREM creditEquivalenceRev == ASSUME NEW self \in Transfer, credit(self)
PROVE E!credit(self)
BY DEF E!credit, credit
    
THEOREM transEquivalence == ASSUME NEW self \in Transfer, E!trans(self)
PROVE trans(self)
<1>1 CASE E!init(self) BY <1>1, initEquivalence DEF E!trans, trans
<1>2 CASE E!debit(self) BY <1>2, debitEquivalence DEF E!trans, trans
<1>3 CASE E!crash(self) BY <1>3, crashEquivalence DEF E!trans, trans
<1>4 CASE E!credit(self) BY <1>4, creditEquivalence DEF E!trans, trans
<1> QED BY <1>1, <1>2, <1>3, <1>4
    DEF E!trans

THEOREM transEquivalenceRev == ASSUME NEW self \in Transfer, trans(self)
PROVE E!trans(self)
<1>1 CASE init(self) BY <1>1, initEquivalenceRev DEF E!trans, trans
<1>2 CASE debit(self) BY <1>2, debitEquivalenceRev DEF E!trans, trans
<1>3 CASE crash(self) BY <1>3, crashEquivalenceRev DEF E!trans, trans
<1>4 CASE credit(self) BY <1>4, creditEquivalenceRev DEF E!trans, trans
<1> QED BY <1>1, <1>2, <1>3, <1>4
    DEF trans

THEOREM unchangedEquivalence == UNCHANGED E!vars <=> UNCHANGED vars
BY DEF E!vars, vars, pendingTransDerived, AmountIsPending,
    creditPrecond, isTransKnown, isTransKnownToItem

THEOREM terminatingEquivalence == E!Terminating <=> Terminating
BY unchangedEquivalence DEF E!Terminating, Terminating,
    E!ProcSet, ProcSet
    
THEOREM nextEquivalence == E!Next <=> Next
BY transEquivalence, transEquivalenceRev, terminatingEquivalence
    DEF E!Next, Next

THEOREM specEquivalence == E!Spec <=> Spec
BY PTL, nextEquivalence, InitEquivalence, unchangedEquivalence
    DEF E!Spec, Spec,
    E!vars, vars

CONSTANTS NTransfer

ASSUME NTransferAssumption == NTransfer \in NNat

ASSUME TransferAssumption == Transfer = 1..NTransfer

\* proved in MoneyTransferPendingExplicit_proofs
THEOREM IndInvPreservedE == E!Spec => []E!IndInv OMITTED

\* proved in MoneyTransferPendingExplicit_proofs
LEMMA AmountPendingTotalInNat == ASSUME NTransferAssumption, E!IndInv
PROVE E!AmountPendingTotal \in Nat OMITTED

\* proved in MoneyTransfer_proofs
THEOREM IndInvPreserved == Spec => []IndInv

THEOREM DebitTotalEquivalence == E!DebitTotal = DebitTotal
BY DEF E!DebitTotal, DebitTotal,
    E!MapThenSumSetE, E!MapThenFoldSetE, MapThenSumSet, MapThenFoldSet,
    E!opAmount, opAmount

THEOREM CreditTotalEquivalence == E!CreditTotal = CreditTotal
BY DEF E!CreditTotal, CreditTotal,
    E!MapThenSumSetE, E!MapThenFoldSetE, MapThenSumSet, MapThenFoldSet,
    E!opAmount, opAmount
    
LEMMA transPendingAmountNat == ASSUME IndInv
PROVE \A am \in transPending: transAmount(am) \in Nat
BY DEF AmountIsPending, isTransKnown, transAmount, transPending, IndInv, TypeOK

LEMMA transSetIsFinite == ASSUME NTransferAssumption
PROVE IsFiniteSet(Transfer)
<1>1 Transfer \in SUBSET (Nat) BY TransferAssumption
<1>2 \A t \in Transfer: t <= NTransfer BY TransferAssumption
<1> QED BY <1>1, <1>2, FS_BoundedSetOfNaturals DEF NNat

LEMMA transPendingIsFinite == IsFiniteSet(transPending)
BY transSetIsFinite, FS_Subset, NTransferAssumption DEF transPending

LEMMA pendingTransAmountInNat == ASSUME E!TypeOK, NEW self \in E!TN
PROVE E!pendingTransAmount(self) \in Nat
BY DEF E!TypeOK, E!pendingTransAmount, E!TN

THEOREM imbalanceByComponents == ASSUME
    E!DebitTotal = DebitTotal,
    IndInv, E!IndInv,
    E!CreditTotal = CreditTotal,
    E!Imbalance = 0,
    Imbalance = 0
PROVE E!AmountPendingTotal = AmountPendingTotal
<1>1 (E!CreditTotal - E!DebitTotal) + E!AmountPendingTotal
    = (CreditTotal - DebitTotal) + AmountPendingTotal BY DEF E!Imbalance, Imbalance
<1>2 DebitTotal \in Nat
    <2>1 \A d \in debits: opAmount(d) \in Nat BY DEF opAmount, IndInv, TypeOK
    <2> QED BY <2>1, MapThenSumSetType DEF DebitTotal, IndInv, TypeOK
<1>3 E!AmountPendingTotal \in Nat BY AmountPendingTotalInNat, NTransferAssumption
<1>4 CreditTotal \in Nat
    <2>1 \A c \in credits: opAmount(c) \in Nat BY DEF opAmount, IndInv, TypeOK
    <2> QED BY <2>1, MapThenSumSetType DEF CreditTotal, IndInv, TypeOK
<1>5 AmountPendingTotal \in Nat BY transPendingAmountNat, transPendingIsFinite, MapThenSumSetType DEF AmountPendingTotal
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5
    
THEOREM Spec => E!AmountPendingTotal = AmountPendingTotal
<1> SUFFICES ASSUME Spec PROVE E!AmountPendingTotal = AmountPendingTotal
    OBVIOUS
<1>1 Imbalance = 0 BY PTL, IndInvPreserved DEF IndInv
<1>2 E!Imbalance = 0 BY PTL, IndInvPreservedE, specEquivalence DEF E!IndInv
<1>3 IndInv BY PTL, IndInvPreserved
<1>4 E!IndInv BY PTL, IndInvPreservedE, specEquivalence
<1> QED BY <1>1, <1>2, <1>3, <1>4, DebitTotalEquivalence, CreditTotalEquivalence, imbalanceByComponents

THEOREM Spec => [](E!AmountPendingTotal = AmountPendingTotal)
<1>1 Spec => [](E!Imbalance = 0 /\ Imbalance = 0) BY PTL,
    IndInvPreserved, IndInvPreservedE,
    specEquivalence DEF E!IndInv, IndInv
<1>2 Spec => []IndInv BY IndInvPreserved
<1>3 Spec => []E!IndInv BY IndInvPreservedE, specEquivalence
<1> QED BY PTL, <1>1, <1>2, <1>3,
    DebitTotalEquivalence, CreditTotalEquivalence, imbalanceByComponents

====