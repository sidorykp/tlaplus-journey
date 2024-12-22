---- MODULE MoneyTransferNaive ----
EXTENDS MoneyTransferCommon, Integers, FiniteSets, FiniteSetsExt

EmptyAccounts == [from |-> Empty, to |-> Empty]

(***************************************************************************
--algorithm MoneyTransferNaive {
    variables
        bal = [a \in Account |-> 0],
        amount = [t \in Transfer |-> 0],
        accounts = [t \in Transfer |-> EmptyAccounts]

    define {
        transAmount(t) == amount[t]
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
    }
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "c1888640" /\ chksum(tla) = "6fa7a018")
VARIABLES bal, amount, accounts, pc

(* define statement *)
transAmount(t) == amount[t]


vars == << bal, amount, accounts, pc >>

ProcSet == (Transfer)

Init == (* Global variables *)
        /\ bal = [a \in Account |-> 0]
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
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << amount, accounts >>

trans(self) == choose_accounts(self) \/ choose_amount(self) \/ debit(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Transfer: trans(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

AmountIsPending(t) == pc[t] = "credit"

transPending == {t \in Transfer: AmountIsPending(t)}

AmountPendingTotal == MapThenSumSet(transAmount, transPending)

Imbalance == AmountPendingTotal

MoneyTotalPreserved == Imbalance = 0

pcLabels == pc \in [Transfer -> {"choose_accounts", "choose_amount", "debit", "Done"}]

EAccounts == [from: EAccount, to: EAccount]

NonEmptyAccounts(t) ==
    /\ accounts[t].from # Empty
    /\ accounts[t].to # Empty

TypeOK ==
    /\ pcLabels
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
    /\ TRUE


====
