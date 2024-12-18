---- MODULE MoneyTransferMicro ----
EXTENDS Integers

CONSTANTS Avail

(***************************************************************************
--algorithm MoneyTransferMicro {
    variables
       bal1 = Avail,
       bal2 = Avail,
       amount = 0;
    
    {
        choose_amount:
            with (am \in 1..Avail)
                amount := am;
        
        debit:
            bal1 := bal1 - amount;
        
        credit:
            bal2 := bal2 + amount;
    }
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "84aed434" /\ chksum(tla) = "6a903974")
VARIABLES bal1, bal2, amount, pc

vars == << bal1, bal2, amount, pc >>

Init == (* Global variables *)
        /\ bal1 = Avail
        /\ bal2 = Avail
        /\ amount = 0
        /\ pc = "choose_amount"

choose_amount == /\ pc = "choose_amount"
                 /\ \E am \in 1..Avail:
                      amount' = am
                 /\ pc' = "debit"
                 /\ UNCHANGED << bal1, bal2 >>

debit == /\ pc = "debit"
         /\ bal1' = bal1 - amount
         /\ pc' = "credit"
         /\ UNCHANGED << bal2, amount >>

credit == /\ pc = "credit"
          /\ bal2' = bal2 + amount
          /\ pc' = "Done"
          /\ UNCHANGED << bal1, amount >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == choose_amount \/ debit \/ credit
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

amountPending == IF pc = "credit" THEN amount ELSE 0

MoneyTotal == bal1 + bal2 + amountPending

pcLabels == pc \in {"choose_amount", "debit", "credit", "Done"}

TypeOK ==
    /\ pcLabels
    /\ bal1 \in Int
    /\ bal2 \in Int
    /\ amount \in Nat

IndInv ==
    /\ TypeOK
    /\ MoneyTotal = 2 * Avail

IndSpec == IndInv /\ [][Next]_vars

IntSmall == -2..2

StateConstraint ==
    /\ bal1 \in IntSmall
    /\ bal2 \in IntSmall

====
