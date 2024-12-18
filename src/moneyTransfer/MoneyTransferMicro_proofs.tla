---- MODULE MoneyTransferMicro_proofs ----
EXTENDS MoneyTransferMicro, TLAPS

ASSUME AvailAssumption == Avail \in Nat \ {0}

THEOREM initProperty == ASSUME Init
PROVE IndInv
BY AvailAssumption DEF Init, IndInv, TypeOK, pcLabels, MoneyTotal, amountPending


THEOREM nextProperty == ASSUME IndInv, Next
PROVE IndInv'
BY DEF vars, choose_amount, debit, credit, Terminating,
    IndInv, TypeOK, MoneyTotal, amountPending, pcLabels, Next
    
THEOREM unchangedVarsProperty == ASSUME IndInv, UNCHANGED vars
PROVE IndInv'
BY DEF vars, IndInv, TypeOK, pcLabels, MoneyTotal, amountPending


THEOREM indInvPreserved == Spec => []IndInv
<1>1 IndInv /\ UNCHANGED vars => IndInv'
    BY unchangedVarsProperty
<1> QED BY <1>1, PTL, initProperty, nextProperty DEF Spec


====
