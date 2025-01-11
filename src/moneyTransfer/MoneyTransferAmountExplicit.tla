---- MODULE MoneyTransferAmountExplicit ----
EXTENDS MoneyTransferCommon, FiniteSets, FiniteSetsExt

EmptyAccounts == [from |-> Empty, to |-> Empty]

(***************************************
Transfer -> Account -> credit or debit
Transfer -> amount
***************************************)

(***************************************************************************
--algorithm MoneyTransferAmountExplicit {
    variables
       credits = {},
       debits = {},
       amount = [t \in Transfer |-> 0],
       accounts = [t \in Transfer |-> EmptyAccounts]

    define {
        opAmount(dc) == dc[2]
    
        accountCredits(a) == MapThenSumSet(LAMBDA c: IF c[1].a = a THEN opAmount(c) ELSE 0, credits)
        
        accountDebits(a) == MapThenSumSet(LAMBDA d: IF d[1].a = a THEN opAmount(d) ELSE 0, debits)
        
        amountAvail(a) == Avail + accountCredits(a) - accountDebits(a)
        
        isTransKnown(t, a, bal) == \E dc \in bal: dc[1].a = a /\ dc[1].t = t
        
        initPrecond(t) == ~\E a \in Account: isTransKnown(t, a, debits)
        
        debitPrecond(t) == ~\E a \in Account:
            \/ isTransKnown(t, a, debits)
            \/ isTransKnown(t, a, credits)
        
        creditPrecond(t) ==
            /\ ~\E a \in Account: isTransKnown(t, a, credits)
            /\ ~isTransKnown(t, accounts[t].to, debits)
            /\ isTransKnown(t, accounts[t].from, debits)
            
        transAmount(t) == amount[t]
    }

    process (trans \in Transfer)    
    {
        init:
            with (account1 \in Account; account2 \in Account \ {account1}; am \in NNat) {
                await amountAvail(account1) > 0;
                await am <= amountAvail(account1);
                accounts[self] := [from |-> account1, to |-> account2];
                amount[self] := am;
            };
            
        debit:
            with (a = accounts[self].from) {
                if (debitPrecond(self)) {
                    either debits := debits \cup {<<[a |-> a, t |-> self], amount[self]>>};
                    or skip;
                }
            };
            
        retryDebit: if (debitPrecond(self)) goto debit;

        credit:
            with (a = accounts[self].to) {
                if (creditPrecond(self)) {
                    either credits := credits \cup {<<[a |-> a, t |-> self], amount[self]>>};
                    or skip;
                }
            };
            
        retryCredit: if (creditPrecond(self)) goto credit;
    }
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "5320ce1e" /\ chksum(tla) = "3813d60f")
VARIABLES credits, debits, amount, accounts, pc

(* define statement *)
opAmount(dc) == dc[2]

accountCredits(a) == MapThenSumSet(LAMBDA c: IF c[1].a = a THEN opAmount(c) ELSE 0, credits)

accountDebits(a) == MapThenSumSet(LAMBDA d: IF d[1].a = a THEN opAmount(d) ELSE 0, debits)

amountAvail(a) == Avail + accountCredits(a) - accountDebits(a)

isTransKnown(t, a, bal) == \E dc \in bal: dc[1].a = a /\ dc[1].t = t

initPrecond(t) == ~\E a \in Account: isTransKnown(t, a, debits)

debitPrecond(t) == ~\E a \in Account:
    \/ isTransKnown(t, a, debits)
    \/ isTransKnown(t, a, credits)

creditPrecond(t) ==
    /\ ~\E a \in Account: isTransKnown(t, a, credits)
    /\ ~isTransKnown(t, accounts[t].to, debits)
    /\ isTransKnown(t, accounts[t].from, debits)

transAmount(t) == amount[t]


vars == << credits, debits, amount, accounts, pc >>

ProcSet == (Transfer)

Init == (* Global variables *)
        /\ credits = {}
        /\ debits = {}
        /\ amount = [t \in Transfer |-> 0]
        /\ accounts = [t \in Transfer |-> EmptyAccounts]
        /\ pc = [self \in ProcSet |-> "init"]

init(self) == /\ pc[self] = "init"
              /\ \E account1 \in Account:
                   \E account2 \in Account \ {account1}:
                     \E am \in NNat:
                       /\ amountAvail(account1) > 0
                       /\ am <= amountAvail(account1)
                       /\ accounts' = [accounts EXCEPT ![self] = [from |-> account1, to |-> account2]]
                       /\ amount' = [amount EXCEPT ![self] = am]
              /\ pc' = [pc EXCEPT ![self] = "debit"]
              /\ UNCHANGED << credits, debits >>

debit(self) == /\ pc[self] = "debit"
               /\ LET a == accounts[self].from IN
                    IF debitPrecond(self)
                       THEN /\ \/ /\ debits' = (debits \cup {<<[a |-> a, t |-> self], amount[self]>>})
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
                        THEN /\ \/ /\ credits' = (credits \cup {<<[a |-> a, t |-> self], amount[self]>>})
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

trans(self) == init(self) \/ debit(self) \/ retryDebit(self)
                  \/ credit(self) \/ retryCredit(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Transfer: trans(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
    
CreditTotal == MapThenSumSet(opAmount, credits)

DebitTotal == MapThenSumSet(opAmount, debits)

AmountIsPending(t) ==
    /\ pc[t] \in {"debit", "retryDebit", "credit", "retryCredit"}
    /\ creditPrecond(t)

transPending == {t \in Transfer: AmountIsPending(t)}

AmountPendingTotal == MapThenSumSet(transAmount, transPending)

Imbalance == CreditTotal - DebitTotal + AmountPendingTotal

NonEmptyAccounts(t) ==
    /\ accounts[t].from # Empty
    /\ accounts[t].to # Empty
    
DifferentAccounts(t) == accounts[t].from # accounts[t].to

EAccounts == [from: EAccount, to: EAccount]

AT == [a: Account, t: Transfer]

pcLabels == pc \in [Transfer -> {"init", "debit", "retryDebit", "credit", "retryCredit", "Done"}]

TypeOK ==
    /\ credits \in SUBSET (AT \X Nat)
    /\ IsFiniteSet(credits)
    /\ debits \in SUBSET (AT \X Nat)
    /\ IsFiniteSet(debits)
    /\ amount \in [Transfer -> Nat]
    /\ accounts \in [Transfer -> EAccounts]
    /\ pcLabels

Inv ==
    /\ TypeOK
    /\ Imbalance = 0

IndInv ==
    /\ TypeOK
    /\ Imbalance = 0
    /\ \A t \in Transfer:
        \/ accounts[t] = EmptyAccounts
        \/ DifferentAccounts(t) /\ NonEmptyAccounts(t)
    /\ \A t \in Transfer: pc[t] = "init" => initPrecond(t)
    /\ \A t \in Transfer:
        pc[t] \notin {"init"} <=> NonEmptyAccounts(t)

IndSpec == IndInv /\ [][Next]_vars

CommonIndInv ==
    /\ amount \in [Transfer -> Nat]
    /\ accounts \in [Transfer -> EAccounts]
    /\ pcLabels
    /\ Imbalance = 0
    /\ \A t \in Transfer:
        \/ accounts[t] = EmptyAccounts
        \/ DifferentAccounts(t) /\ NonEmptyAccounts(t)
    /\ \A t \in Transfer: pc[t] = "init" => initPrecond(t)
    /\ \A t \in Transfer:
        pc[t] \notin {"init"} <=> NonEmptyAccounts(t)

IndInvInteractiveStateConstraints ==
    /\ \A c \in credits: \E d \in debits: 
        /\ d[1].t = c[1].t
        /\ d[1].a # c[1].a
        /\ opAmount(d) = opAmount(c)
    /\ \A t \in Transfer:
        amount[t] = 0 <=> pc[t] = "init"

====
