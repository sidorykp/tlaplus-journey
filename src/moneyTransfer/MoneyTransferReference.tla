---- MODULE MoneyTransferReference ----
EXTENDS MoneyTransferCommon, FiniteSets, FiniteSetsExt

EmptyAccounts == [from |-> Empty, to |-> Empty]

(***************************************************************************
--algorithm MoneyTransferReference {
    variables
       credits = [a \in Account |-> {}],
       debits = [a \in Account |-> {}],
       amount = [t \in Transfer |-> 0],
       accounts = [t \in Transfer |-> EmptyAccounts]

    define {
        transAmount(t) == amount[t]
    
        accountCredits(a) == MapThenSumSet(transAmount, credits[a])
        
        accountDebits(a) == MapThenSumSet(transAmount, debits[a])
        
        amountAvail(a) == Avail + accountCredits(a) - accountDebits(a)
        
        isTransKnown(t, a, balanceComponent) == a # Empty /\ t \in balanceComponent[a]
        
        debitPrecond(t) == ~\E a \in Account:
            \/ isTransKnown(t, a, debits)
            \/ isTransKnown(t, a, credits)
        
        creditPrecond(t) ==
            /\ ~\E a \in Account: isTransKnown(t, a, credits)
            /\ ~isTransKnown(t, accounts[t].to, debits)
            /\ isTransKnown(t, accounts[t].from, debits)
    }

    process (trans \in Transfer)    
    {
        choose_accounts:
            with (account1 \in Account; account2 \in Account \ {account1}) {
                accounts[self] := [from |-> account1, to |-> account2];
            };
            
        choose_amount:
            with (a = accounts[self].from; am \in 1..amountAvail(accounts[self].from)) {
                amount[self] := am;
            };
            
        debit:
            with (a = accounts[self].from) {
                if (debitPrecond(self)) {
                    either debits[a] := debits[a] \cup {self};
                    or skip;
                }
            };
            
        retryDebit: if (debitPrecond(self)) goto debit;

        credit:
            with (a = accounts[self].to) {
                if (creditPrecond(self)) {
                    either credits[a] := credits[a] \cup {self};
                    or skip;
                }
            };

        retryCredit: if (creditPrecond(self)) goto credit;
    }
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "d4981b31" /\ chksum(tla) = "582b48ad")
VARIABLES credits, debits, amount, accounts, pc

(* define statement *)
transAmount(t) == amount[t]

accountCredits(a) == MapThenSumSet(transAmount, credits[a])

accountDebits(a) == MapThenSumSet(transAmount, debits[a])

amountAvail(a) == Avail + accountCredits(a) - accountDebits(a)

isTransKnown(t, a, balanceComponent) == a # Empty /\ t \in balanceComponent[a]

debitPrecond(t) == ~\E a \in Account:
    \/ isTransKnown(t, a, debits)
    \/ isTransKnown(t, a, credits)

creditPrecond(t) ==
    /\ ~\E a \in Account: isTransKnown(t, a, credits)
    /\ ~isTransKnown(t, accounts[t].to, debits)
    /\ isTransKnown(t, accounts[t].from, debits)


vars == << credits, debits, amount, accounts, pc >>

ProcSet == (Transfer)

Init == (* Global variables *)
        /\ credits = [a \in Account |-> {}]
        /\ debits = [a \in Account |-> {}]
        /\ amount = [t \in Transfer |-> 0]
        /\ accounts = [t \in Transfer |-> EmptyAccounts]
        /\ pc = [self \in ProcSet |-> "choose_accounts"]

choose_accounts(self) == /\ pc[self] = "choose_accounts"
                         /\ \E account1 \in Account:
                              \E account2 \in Account \ {account1}:
                                accounts' = [accounts EXCEPT ![self] = [from |-> account1, to |-> account2]]
                         /\ pc' = [pc EXCEPT ![self] = "choose_amount"]
                         /\ UNCHANGED << credits, debits, amount >>

choose_amount(self) == /\ pc[self] = "choose_amount"
                       /\ LET a == accounts[self].from IN
                            \E am \in 1..amountAvail(accounts[self].from):
                              amount' = [amount EXCEPT ![self] = am]
                       /\ pc' = [pc EXCEPT ![self] = "debit"]
                       /\ UNCHANGED << credits, debits, accounts >>

debit(self) == /\ pc[self] = "debit"
               /\ LET a == accounts[self].from IN
                    IF debitPrecond(self)
                       THEN /\ \/ /\ debits' = [debits EXCEPT ![a] = debits[a] \cup {self}]
                               \/ /\ TRUE
                                  /\ UNCHANGED debits
                       ELSE /\ TRUE
                            /\ UNCHANGED debits
               /\ pc' = [pc EXCEPT ![self] = "retryDebit"]
               /\ UNCHANGED << credits, amount, accounts >>

retryDebit(self) == /\ pc[self] = "retryDebit"
                    /\ IF debitPrecond(self)
                          THEN /\ pc' = [pc EXCEPT ![self] = "debit"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "credit"]
                    /\ UNCHANGED << credits, debits, amount, accounts >>

credit(self) == /\ pc[self] = "credit"
                /\ LET a == accounts[self].to IN
                     IF creditPrecond(self)
                        THEN /\ \/ /\ credits' = [credits EXCEPT ![a] = credits[a] \cup {self}]
                                \/ /\ TRUE
                                   /\ UNCHANGED credits
                        ELSE /\ TRUE
                             /\ UNCHANGED credits
                /\ pc' = [pc EXCEPT ![self] = "retryCredit"]
                /\ UNCHANGED << debits, amount, accounts >>

retryCredit(self) == /\ pc[self] = "retryCredit"
                     /\ IF creditPrecond(self)
                           THEN /\ pc' = [pc EXCEPT ![self] = "credit"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << credits, debits, amount, accounts >>

trans(self) == choose_accounts(self) \/ choose_amount(self) \/ debit(self)
                  \/ retryDebit(self) \/ credit(self) \/ retryCredit(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Transfer: trans(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

AmountIsPending(t) ==
    /\ pc[t] \in {"debit", "retryDebit", "credit", "retryCredit"}
    /\ creditPrecond(t)

NonEmptyAccounts(t) ==
    /\ accounts[t].from # Empty
    /\ accounts[t].to # Empty

MoneyConstant == \A t \in Transfer: AmountIsPending(t) <=>
    /\ NonEmptyAccounts(t)
    /\ t \in debits[accounts[t].from]
    /\ ~(t \in credits[accounts[t].to])
    
DifferentAccounts(t) == accounts[t].from # accounts[t].to

EAccounts == [from: EAccount, to: EAccount]

pcLabels == pc \in [Transfer -> {"choose_accounts", "choose_amount", "debit", "retryDebit", "credit", "retryCredit", "Done"}]

TypeOK ==
    /\ credits \in [Account -> SUBSET Transfer]
    /\ debits \in [Account -> SUBSET Transfer]
    /\ amount \in [Transfer -> Nat]
    /\ accounts \in [Transfer -> EAccounts]
    /\ pcLabels

Inv ==
    /\ TypeOK
    /\ MoneyConstant

IndInv ==
    /\ TypeOK
    /\ MoneyConstant
    /\ \A t \in Transfer:
        \/ accounts[t] = EmptyAccounts
        \/ DifferentAccounts(t) /\ NonEmptyAccounts(t)
    /\ \A t \in Transfer: pc[t] \in {"choose_accounts", "choose_amount"} => debitPrecond(t)
    /\ \A t \in Transfer:
        pc[t] \notin {"choose_accounts"} <=> NonEmptyAccounts(t)

IndSpec == IndInv /\ [][Next]_vars

CommonIndInv ==
    /\ amount \in [Transfer -> Nat]
    /\ accounts \in [Transfer -> EAccounts]
    /\ pcLabels
    /\ MoneyConstant
    /\ \A t \in Transfer:
        \/ accounts[t] = EmptyAccounts
        \/ DifferentAccounts(t) /\ NonEmptyAccounts(t)
    /\ \A t \in Transfer: pc[t] \in {"choose_accounts", "choose_amount"} => debitPrecond(t)
    /\ \A t \in Transfer:
        pc[t] \notin {"choose_accounts"} <=> NonEmptyAccounts(t)

IndNat == 0..2

IndInvInteractiveStateConstraints == \A a \in Account: amountAvail(a) \in IndNat

====
