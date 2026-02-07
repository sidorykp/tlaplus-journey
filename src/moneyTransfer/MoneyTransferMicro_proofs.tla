---- MODULE MoneyTransferMicro_proofs ----
EXTENDS MoneyTransferMicro, TLAPS

ASSUME AvailAssumption == Avail \in Nat \ {0}

MoneyTotalPreserved == MoneyTotal = 2 * Avail

THEOREM ImplicationProperty == IndInv => MoneyTotalPreserved
BY DEF MoneyTotalPreserved, IndInv

THEOREM InitProperty == ASSUME Init
PROVE IndInv
BY AvailAssumption DEF Init, IndInv, TypeOK, pcLabels, MoneyTotal, amountPending


THEOREM NextProperty == ASSUME IndInv, Next
PROVE IndInv'
BY DEF vars, choose_amount, debit, credit, Terminating,
    IndInv, TypeOK, MoneyTotal, amountPending, pcLabels, Next
    
THEOREM UnchangedVarsProperty == ASSUME IndInv, UNCHANGED vars
PROVE IndInv'
BY DEF vars, IndInv, TypeOK, pcLabels, MoneyTotal, amountPending

THEOREM IndInvPreserved == Spec => []IndInv
<1>1 IndInv /\ UNCHANGED vars => IndInv'
    BY UnchangedVarsProperty
<1> QED BY <1>1, PTL, InitProperty, NextProperty DEF Spec

THEOREM Correctenss == Spec => []MoneyTotalPreserved
BY PTL, IndInvPreserved, ImplicationProperty DEF Spec

====
