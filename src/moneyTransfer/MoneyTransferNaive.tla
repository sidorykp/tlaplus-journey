---- MODULE MoneyTransferNaive ----
EXTENDS MoneyTransferCommon, Naturals, FiniteSets, FiniteSetsExt

EmptyAccounts == [from |-> Empty, to |-> Empty]

(***************************************************************************
--algorithm MoneyTransferNaive {
    variables
        debits = [a \in Account |-> 0],
        credits = [a \in Account |-> 0],
        amount = [t \in Transfer |-> 0],
        accounts = [t \in Transfer |-> EmptyAccounts]

    define {
        creditBal(a) == credits[a]
        
        debitBal(a) == debits[a]
        
        amountAvail(a) == Avail + creditBal(a) - debitBal(a)

        transAmount(t) == amount[t]
    }

    process (trans \in Transfer)
    {
        choose_accounts:
            with (account1 \in Account; account2 \in Account \ {account1})
                accounts[self] := [from |-> account1, to |-> account2];

        choose_amount:
            with (am \in 1..amountAvail(accounts[self].from))
                amount[self] := am;

        debit:
            with (a = accounts[self].from)
                debits[a] := debits[a] + amount[self];

        credit:
            with (a = accounts[self].to)
                credits[a] := credits[a] + amount[self];
    }
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "3b2ff5ff" /\ chksum(tla) = "75c5026")
VARIABLES debits, credits, amount, accounts, pc

(* define statement *)
creditBal(a) == credits[a]

debitBal(a) == debits[a]

amountAvail(a) == Avail + creditBal(a) - debitBal(a)

transAmount(t) == amount[t]


vars == << debits, credits, amount, accounts, pc >>

ProcSet == (Transfer)

Init == (* Global variables *)
        /\ debits = [a \in Account |-> 0]
        /\ credits = [a \in Account |-> 0]
        /\ amount = [t \in Transfer |-> 0]
        /\ accounts = [t \in Transfer |-> EmptyAccounts]
        /\ pc = [self \in ProcSet |-> "choose_accounts"]

choose_accounts(self) == /\ pc[self] = "choose_accounts"
                         /\ \E account1 \in Account:
                              \E account2 \in Account \ {account1}:
                                accounts' = [accounts EXCEPT ![self] = [from |-> account1, to |-> account2]]
                         /\ pc' = [pc EXCEPT ![self] = "choose_amount"]
                         /\ UNCHANGED << debits, credits, amount >>

choose_amount(self) == /\ pc[self] = "choose_amount"
                       /\ \E am \in 1..amountAvail(accounts[self].from):
                            amount' = [amount EXCEPT ![self] = am]
                       /\ pc' = [pc EXCEPT ![self] = "debit"]
                       /\ UNCHANGED << debits, credits, accounts >>

debit(self) == /\ pc[self] = "debit"
               /\ LET a == accounts[self].from IN
                    debits' = [debits EXCEPT ![a] = debits[a] + amount[self]]
               /\ pc' = [pc EXCEPT ![self] = "credit"]
               /\ UNCHANGED << credits, amount, accounts >>

credit(self) == /\ pc[self] = "credit"
                /\ LET a == accounts[self].to IN
                     credits' = [credits EXCEPT ![a] = credits[a] + amount[self]]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << debits, amount, accounts >>

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

AmountIsPending(t) == pc[t] = "credit"

transPending == {t \in Transfer: AmountIsPending(t)}

AmountPendingTotal == MapThenSumSet(transAmount, transPending)

CreditTotal == MapThenSumSet(creditBal, Account)

DebitTotal == MapThenSumSet(debitBal, Account)

Imbalance == CreditTotal - DebitTotal + AmountPendingTotal

MoneyTotalPreserved == Imbalance = 0

pcLabels == pc \in [Transfer -> {"choose_accounts", "choose_amount", "debit", "credit", "Done"}]

EAccounts == [from: EAccount, to: EAccount]

NonEmptyAccounts(t) ==
    /\ accounts[t].from # Empty
    /\ accounts[t].to # Empty

TypeOK ==
    /\ pcLabels
    /\ debits \in [Account -> Nat]
    /\ credits \in [Account -> Nat]
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

IndNat == 0..2
NatSmall == 0..1

StateConstraint ==
    /\ debits \in [Account -> NatSmall]
    /\ credits \in [Account -> NatSmall]
    /\ amount \in [Transfer -> NatSmall]


====
