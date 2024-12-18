---- MODULE MoneyTransferMicro_proofs ----
EXTENDS MoneyTransferMicro

ASSUME AvailAssumption == Avail \in Nat \ {0}

THEOREM initProperty == ASSUME Init
PROVE IndInv
BY AvailAssumption DEF Init, IndInv, TypeOK, pcLabels, MoneyTotal, amountPending


THEOREM nextProperty == ASSUME IndInv, Next
PROVE IndInv'
BY DEF vars, choose_amount, debit, credit, Terminating,
    IndInv, TypeOK, MoneyTotal, amountPending, pcLabels, Next
====
