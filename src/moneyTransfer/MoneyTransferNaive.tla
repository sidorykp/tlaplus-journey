---- MODULE MoneyTransferNaive ----
EXTENDS Integers, FiniteSets, FiniteSetsExt

CONSTANTS Avail, Empty, Account, Transfer

EAccount == Account \cup {Empty}

EmptyAccounts == [from |-> Empty, to |-> Empty]

(***************************************************************************
--algorithm MoneyTransferNaive {
    variables
        bal = [a \in Account |-> Avail],
        amount = [t \in Transfer |-> 0],
        accounts = [t \in Transfer |-> EmptyAccounts]

    define {
        accBal(a) == bal[a]
    }

    process (trans \in Transfer)
    {
        choose_accounts:
            with (account1 \in Account; account2 \in Account \ {account1})
                accounts[self] := [from |-> account1, to |-> account2];

        choose_amount:
            with (am \in 1..Avail)
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
\* BEGIN TRANSLATION (chksum(pcal) = "5887baf3" /\ chksum(tla) = "4a0181c0")
VARIABLES bal, amount, accounts, pc

(* define statement *)
accBal(a) == bal[a]


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
                       /\ \E am \in 1..Avail:
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

AmountPendingTotal == MapThenSumSet(amountPending, Transfer)

BalanceTotal == MapThenSumSet(accBal, Account)

MoneyTotal == BalanceTotal + AmountPendingTotal

MoneyTotalPreserved == MoneyTotal = Avail * Cardinality(Account)

Inv ==
    /\ MoneyTotalPreserved


====
