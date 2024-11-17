----MODULE MoneyTransferEquivalence----
EXTENDS MoneyTransfer, TLAPS

pendingTransE == {<<t, amount[t]>>: t \in {t \in Transfer: AmountIsPending(t)}}

E == INSTANCE MoneyTransferPendingExplicit WITH pendingTrans <- pendingTransE


ASSUME EquivalentSymbolsAssumption ==
    /\ EmptyAccounts = E!EmptyAccounts
    /\ NNat = E!NNat

THEOREM InitEquivalence == ASSUME Init
PROVE E!Init
<1>1 pendingTransE = {} BY DEF Init, pendingTransE,
    AmountIsPending, creditPrecond, isTransKnown, isTransKnownToItem
<1> QED BY EquivalentSymbolsAssumption, <1>1 DEF Init, E!Init,
    ProcSet, E!ProcSet
    
THEOREM InitEquivalenceAdj == ASSUME E!Init
PROVE Init
<1>1 pendingTransE = {} BY DEF E!Init, pendingTransE,
    AmountIsPending, creditPrecond, isTransKnown, isTransKnownToItem
<1> QED BY EquivalentSymbolsAssumption, <1>1 DEF Init, E!Init,
    ProcSet, E!ProcSet

THEOREM initEquivalence == ASSUME NEW self \in Transfer, init(self), IndInv
PROVE E!init(self)
<1>1 UNCHANGED pendingTransE BY EquivalentSymbolsAssumption DEF init, pendingTransE,
    AmountIsPending, creditPrecond, isTransKnown, isTransKnownToItem
<1>2 \A a \in Account:
    /\ accountCreditsSum(a) = E!accountCreditsSum(a)
    /\ accountDebitsSum(a) = E!accountDebitsSum(a)
    BY DEF accountDebitsCerdits, E!accountDebitsCerdits,
    accountCreditsSum, E!accountCreditsSum,
    accountDebitsSum, E!accountDebitsSum,
    MapThenSumSet, MapThenFoldSet, E!MapThenSumSetE,
    opAmount, E!opAmount
<1> QED BY EquivalentSymbolsAssumption, <1>1, <1>2 DEF init, E!init,
    amountAvail, E!amountAvail
    
THEOREM initEquivalenceAdj == ASSUME NEW self \in Transfer, E!init(self), IndInv
PROVE init(self)
<1>1 UNCHANGED pendingTransE BY EquivalentSymbolsAssumption DEF E!init, pendingTransE,
    AmountIsPending, creditPrecond, isTransKnown, isTransKnownToItem
<1>2 \A a \in Account:
    /\ accountCreditsSum(a) = E!accountCreditsSum(a)
    /\ accountDebitsSum(a) = E!accountDebitsSum(a)
    BY DEF accountDebitsCerdits, E!accountDebitsCerdits,
    accountCreditsSum, E!accountCreditsSum,
    accountDebitsSum, E!accountDebitsSum,
    MapThenSumSet, MapThenFoldSet, E!MapThenSumSetE,
    opAmount, E!opAmount
<1> QED BY EquivalentSymbolsAssumption, <1>1, <1>2 DEF init, E!init,
    amountAvail, E!amountAvail

THEOREM debitEquivalence == ASSUME NEW self \in Transfer, debit(self), IndInv
PROVE E!debit(self)
BY DEF debit, E!debit

THEOREM debitEquivalenceAdj == ASSUME NEW self \in Transfer, E!debit(self), IndInv
PROVE debit(self)
BY DEF debit, E!debit

THEOREM crashEquivalence == ASSUME NEW self \in Transfer, crash(self), IndInv
PROVE E!crash(self)
BY DEF crash, E!crash, pendingTransE

THEOREM crashEquivalenceAdj == ASSUME NEW self \in Transfer, E!crash(self), IndInv
PROVE crash(self)
<1> QED BY DEF crash, E!crash, AmountIsPending

THEOREM creditEquivalence == ASSUME NEW self \in Transfer, credit(self), IndInv
PROVE E!credit(self)
BY DEF credit, E!credit, pendingTransE

THEOREM creditEquivalenceAdj == ASSUME NEW self \in Transfer, E!credit(self), IndInv
PROVE credit(self)
BY DEF credit, E!credit, AmountIsPending

THEOREM transEquivalence == ASSUME NEW self \in Transfer, trans(self), IndInv
PROVE E!trans(self)
BY initEquivalence, debitEquivalence, creditEquivalence, crashEquivalence
DEF trans, E!trans

THEOREM transEquivalenceAdj == ASSUME NEW self \in Transfer, E!trans(self), IndInv
PROVE trans(self)
BY initEquivalenceAdj, debitEquivalenceAdj, creditEquivalenceAdj, crashEquivalenceAdj
DEF trans, E!trans

THEOREM nextEquivalenceNonTerminating == ASSUME Next, ~Terminating, IndInv
PROVE E!Next
BY transEquivalence DEF Next, E!Next

THEOREM nextEquivalenceNonTerminatingAdj == ASSUME E!Next, ~E!Terminating, IndInv
PROVE Next
BY transEquivalenceAdj DEF Next, E!Next

THEOREM unchangedVarsEquivalence == ASSUME UNCHANGED vars, IndInv
PROVE UNCHANGED E!vars
BY EquivalentSymbolsAssumption DEF vars, E!vars, pendingTransE,
    AmountIsPending, creditPrecond, isTransKnown, isTransKnownToItem

THEOREM unchangedVarsEquivalenceAdj == ASSUME UNCHANGED E!vars, IndInv
PROVE UNCHANGED vars
BY EquivalentSymbolsAssumption DEF vars, E!vars, pendingTransE,
    AmountIsPending, creditPrecond, isTransKnown, isTransKnownToItem

THEOREM terminatingEquivalence == ASSUME Terminating, IndInv
PROVE E!Terminating
BY unchangedVarsEquivalence
DEF Terminating, E!Terminating,
    ProcSet, E!ProcSet

THEOREM terminatingEquivalenceAdj == ASSUME E!Terminating, IndInv
PROVE Terminating
BY unchangedVarsEquivalenceAdj
DEF Terminating, E!Terminating,
    ProcSet, E!ProcSet

THEOREM nextEquivalenceTerminating == ASSUME Next, Terminating, IndInv
PROVE E!Next
<1>1 UNCHANGED vars BY DEF Terminating
<1>2 UNCHANGED E!vars BY <1>1, unchangedVarsEquivalence
<1>3 E!Terminating BY <1>2 DEF Terminating, E!Terminating, ProcSet, E!ProcSet
<1> QED BY <1>3 DEF Next, E!Next
    
THEOREM nextEquivalenceTerminatingAdj == ASSUME E!Next, E!Terminating, IndInv
PROVE Next
<1>1 UNCHANGED E!vars BY DEF E!Terminating
<1>2 UNCHANGED vars BY <1>1, unchangedVarsEquivalenceAdj
<1>3 Terminating BY <1>2 DEF Terminating, E!Terminating, ProcSet, E!ProcSet
<1> QED BY <1>3 DEF Next, E!Next

THEOREM nextEquivalence == ASSUME Next, IndInv
PROVE E!Next
<1>1 CASE Terminating BY <1>1, nextEquivalenceTerminating
<1>2 CASE ~Terminating BY <1>1, nextEquivalenceNonTerminating
<1> QED BY <1>1, <1>2

THEOREM nextEquivalenceAdj == ASSUME E!Next, IndInv
PROVE Next
<1>1 CASE E!Terminating BY <1>1, nextEquivalenceTerminatingAdj
<1>2 CASE ~E!Terminating BY <1>1, nextEquivalenceNonTerminatingAdj
<1> QED BY <1>1, <1>2

THEOREM InitEquivalenceTotal == Init <=> E!Init
BY InitEquivalence, InitEquivalenceAdj

THEOREM nextEquivalenceTotal == ASSUME IndInv PROVE
Next <=> E!Next
BY nextEquivalence, nextEquivalenceAdj

THEOREM unchangedVarsEquivalenceTotal == ASSUME IndInv
PROVE UNCHANGED vars <=> UNCHANGED E!vars
BY unchangedVarsEquivalence, unchangedVarsEquivalenceAdj

THEOREM terminatingEquivalenceTotal == ASSUME IndInv
PROVE Terminating <=> E!Terminating
BY terminatingEquivalence, terminatingEquivalenceAdj

THEOREM ASSUME IndInv, vars = E!vars, Next /\ E!Next
PROVE vars' = E!vars'
BY nextEquivalenceTotal DEF Next, E!Next, vars, E!vars

SpecE == Init /\ [][Next]_E!vars

InitCombined == Init /\ E!Init

NextCombined == Next /\ E!Next

SpecCombined == InitCombined /\ [][NextCombined]_vars

IndSpecCombined == /\ IndInv /\ [][NextCombined]_vars

====