---- MODULE MoneyTransferSmall ----
EXTENDS Integers, FiniteSets, FiniteSetTheorems

CONSTANTS Avail, Empty, a1, a2, a3, t1, t2

Account == {a1, a2, a3}

Transfer == {t1, t2}

EAccount == Account \cup {Empty}

EmptyAccounts == [from |-> Empty, to |-> Empty]

(***************************************************************************
--algorithm MoneyTransferSmall {
    variables
        bal = [a \in Account |-> Avail],
        amount = [t \in Transfer |-> 0],
        accounts = [t \in Transfer |-> EmptyAccounts]

    process (trans \in Transfer)
    {
        choose_accounts:
            with (account1 \in Account; account2 \in Account \ {account1})
                accounts[self] := [from |-> account1, to |-> account2];
    
        choose_amount:
            with (am \in 1..bal[accounts[self].from])
                amount[self] := am;

        debit:
            with (a = accounts[self].from)
                bal[a] := bal[a] - amount[self];

        credit:
            with (a = accounts[self].to)
                bal[a] := bal[a] + amount[self];
    }
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "c2320f8b" /\ chksum(tla) = "f3c3f715")
VARIABLES bal, amount, accounts, pc

vars == << bal, amount, accounts, pc >>

ProcSet == (Transfer)

Init == (* Global variables *)
        /\ bal = [a \in Account |-> Avail]
        /\ amount = [t \in Transfer |-> 0]
        /\ accounts = [t \in Transfer |-> EmptyAccounts]
        /\ pc = [self \in ProcSet |-> "choose_accounts"]

choose_accounts(self) == /\ pc[self] = "choose_accounts"
                         /\ \E account1 \in Account:
                              \E account2 \in Account \ {account1}:
                                accounts' = [accounts EXCEPT ![self] = [from |-> account1, to |-> account2]]
                         /\ pc' = [pc EXCEPT ![self] = "choose_amount"]
                         /\ UNCHANGED << bal, amount >>

choose_amount(self) == /\ pc[self] = "choose_amount"
                       /\ \E am \in 1..bal[accounts[self].from]:
                            amount' = [amount EXCEPT ![self] = am]
                       /\ pc' = [pc EXCEPT ![self] = "debit"]
                       /\ UNCHANGED << bal, accounts >>

debit(self) == /\ pc[self] = "debit"
               /\ LET a == accounts[self].from IN
                    bal' = [bal EXCEPT ![a] = bal[a] - amount[self]]
               /\ pc' = [pc EXCEPT ![self] = "credit"]
               /\ UNCHANGED << amount, accounts >>

credit(self) == /\ pc[self] = "credit"
                /\ LET a == accounts[self].to IN
                     bal' = [bal EXCEPT ![a] = bal[a] + amount[self]]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << amount, accounts >>

trans(self) == choose_accounts(self) \/ choose_amount(self) \/ debit(self)
                  \/ credit(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Transfer: trans(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

amountPending(t) == IF pc[t] = "credit" THEN amount[t] ELSE 0

MoneyTotal == bal[a1] + bal[a2] + bal[a3] + amountPending(t1) + amountPending(t2)

MoneyTotalPreserved == MoneyTotal = Avail * Cardinality(Account)

pcLabels == pc \in [Transfer -> {"choose_accounts", "choose_amount", "debit", "credit", "Done"}]

EAccounts == [from: EAccount, to: EAccount]

NonEmptyAccounts(t) ==
    /\ accounts[t].from # Empty
    /\ accounts[t].to # Empty
    
DifferentAccounts(t) == accounts[t].from # accounts[t].to

TypeOK ==
    /\ pcLabels
    /\ bal \in [Account -> Int]
    /\ amount \in [Transfer -> Nat]
    /\ accounts \in [Transfer -> EAccounts]

Inv ==
    /\ TypeOK
    /\ MoneyTotalPreserved

IndInv ==
    /\ TypeOK
    /\ MoneyTotalPreserved
    /\ \A t \in Transfer:
        pc[t] \notin {"choose_accounts"} <=> NonEmptyAccounts(t)

IndSpec == IndInv /\ [][Next]_vars

IndInt == -3..3
IndNat == 0..2
IntSmall == -1..1

StateConstraint ==
    /\ bal \in [Account -> IntSmall]


====
