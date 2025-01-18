---- MODULE MoneyTransferReplicated ----
EXTENDS MoneyTransferCommon, FiniteSets, FiniteSetsExt

CONSTANTS Eccount, Dransfer

EmptyAccounts == [from |-> Empty, to |-> Empty]

EEccount == Eccount \cup {Empty}

EmptyEccounts == [from |-> Empty, to |-> Empty]

(***************************************************************************
--algorithm MoneyTransferReplicated {
    variables
       credits = {},
       debits = {},
       amount = [t \in Transfer |-> 0],
       accounts = [t \in Transfer |-> EmptyAccounts],
       kredits = {},
       bebits = {},
       emount = [t \in Dransfer |-> 0],
       eccounts = [t \in Dransfer |-> EmptyEccounts],

    define {
        transAmount(t) == amount[t]

        opAmount(dc) == amount[dc.t]

        accountCredits(a) == MapThenSumSet(LAMBDA c: IF c.a = a THEN opAmount(c) ELSE 0, credits)

        accountDebits(a) == MapThenSumSet(LAMBDA d: IF d.a = a THEN opAmount(d) ELSE 0, debits)

        amountAvail(a) == Avail + accountCredits(a) - accountDebits(a)

        isTransKnown(t, a, bal) == \E dc \in bal: dc.a = a /\ dc.t = t

        debitPrecond(t) == ~\E a \in Account:
            \/ isTransKnown(t, a, debits)
            \/ isTransKnown(t, a, credits)

        creditPrecond(t) ==
            /\ ~\E a \in Account: isTransKnown(t, a, credits)
            /\ ~isTransKnown(t, accounts[t].to, debits)
            /\ isTransKnown(t, accounts[t].from, debits)

        dransAmount(t) == emount[t]

        opEmount(dc) == emount[dc.t]

        eccountKredits(a) == MapThenSumSet(LAMBDA c: IF c.a = a THEN opEmount(c) ELSE 0, kredits)

        eccountBebits(a) == MapThenSumSet(LAMBDA d: IF d.a = a THEN opEmount(d) ELSE 0, bebits)

        emountAvail(a) == Avail + eccountKredits(a) - eccountBebits(a)

        bebitPrecond(t) == ~\E a \in Eccount:
            \/ isTransKnown(t, a, bebits)
            \/ isTransKnown(t, a, kredits)

        kreditPrecond(t) ==
            /\ ~\E a \in Eccount: isTransKnown(t, a, kredits)
            /\ ~isTransKnown(t, eccounts[t].to, bebits)
            /\ isTransKnown(t, eccounts[t].from, bebits)
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
                    either debits := debits \cup {[a |-> a, t |-> self]};
                    or skip;
                }
            };

        retryDebit: if (debitPrecond(self)) goto debit;

        credit:
            with (a = accounts[self].to) {
                if (creditPrecond(self)) {
                    either credits := credits \cup {[a |-> a, t |-> self]};
                    or skip;
                }
            };

        retryCredit: if (creditPrecond(self)) goto credit;
    }

    process (drans \in Dransfer)
    {
        choose_eccounts:
            with (account1 \in Eccount; account2 \in Eccount \ {account1}) {
                eccounts[self] := [from |-> account1, to |-> account2];
            };

        choose_emount:
            with (a = eccounts[self].from; am \in 1..emountAvail(eccounts[self].from)) {
                emount[self] := am;
            };

        bebit:
            with (a = eccounts[self].from) {
                if (bebitPrecond(self)) {
                    either bebits := bebits \cup {[a |-> a, t |-> self]};
                    or skip;
                }
            };

        retryBebit: if (bebitPrecond(self)) goto bebit;

        kredit:
            with (a = eccounts[self].to) {
                if (kreditPrecond(self)) {
                    either kredits := kredits \cup {[a |-> a, t |-> self]};
                    or skip;
                }
            };

        retryKredit: if (kreditPrecond(self)) goto kredit;
    }
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "993a186e" /\ chksum(tla) = "95514516")
VARIABLES credits, debits, amount, accounts, kredits, bebits, emount, 
          eccounts, pc

(* define statement *)
transAmount(t) == amount[t]

opAmount(dc) == amount[dc.t]

accountCredits(a) == MapThenSumSet(LAMBDA c: IF c.a = a THEN opAmount(c) ELSE 0, credits)

accountDebits(a) == MapThenSumSet(LAMBDA d: IF d.a = a THEN opAmount(d) ELSE 0, debits)

amountAvail(a) == Avail + accountCredits(a) - accountDebits(a)

isTransKnown(t, a, bal) == \E dc \in bal: dc.a = a /\ dc.t = t

debitPrecond(t) == ~\E a \in Account:
    \/ isTransKnown(t, a, debits)
    \/ isTransKnown(t, a, credits)

creditPrecond(t) ==
    /\ ~\E a \in Account: isTransKnown(t, a, credits)
    /\ ~isTransKnown(t, accounts[t].to, debits)
    /\ isTransKnown(t, accounts[t].from, debits)

dransAmount(t) == emount[t]

opEmount(dc) == emount[dc.t]

eccountKredits(a) == MapThenSumSet(LAMBDA c: IF c.a = a THEN opEmount(c) ELSE 0, kredits)

eccountBebits(a) == MapThenSumSet(LAMBDA d: IF d.a = a THEN opEmount(d) ELSE 0, bebits)

emountAvail(a) == Avail + eccountKredits(a) - eccountBebits(a)

bebitPrecond(t) == ~\E a \in Eccount:
    \/ isTransKnown(t, a, bebits)
    \/ isTransKnown(t, a, kredits)

kreditPrecond(t) ==
    /\ ~\E a \in Eccount: isTransKnown(t, a, kredits)
    /\ ~isTransKnown(t, eccounts[t].to, bebits)
    /\ isTransKnown(t, eccounts[t].from, bebits)


vars == << credits, debits, amount, accounts, kredits, bebits, emount, 
           eccounts, pc >>

ProcSet == (Transfer) \cup (Dransfer)

Init == (* Global variables *)
        /\ credits = {}
        /\ debits = {}
        /\ amount = [t \in Transfer |-> 0]
        /\ accounts = [t \in Transfer |-> EmptyAccounts]
        /\ kredits = {}
        /\ bebits = {}
        /\ emount = [t \in Dransfer |-> 0]
        /\ eccounts = [t \in Dransfer |-> EmptyEccounts]
        /\ pc = [self \in ProcSet |-> CASE self \in Transfer -> "choose_accounts"
                                        [] self \in Dransfer -> "choose_eccounts"]

choose_accounts(self) == /\ pc[self] = "choose_accounts"
                         /\ \E account1 \in Account:
                              \E account2 \in Account \ {account1}:
                                accounts' = [accounts EXCEPT ![self] = [from |-> account1, to |-> account2]]
                         /\ pc' = [pc EXCEPT ![self] = "choose_amount"]
                         /\ UNCHANGED << credits, debits, amount, kredits, 
                                         bebits, emount, eccounts >>

choose_amount(self) == /\ pc[self] = "choose_amount"
                       /\ LET a == accounts[self].from IN
                            \E am \in 1..amountAvail(accounts[self].from):
                              amount' = [amount EXCEPT ![self] = am]
                       /\ pc' = [pc EXCEPT ![self] = "debit"]
                       /\ UNCHANGED << credits, debits, accounts, kredits, 
                                       bebits, emount, eccounts >>

debit(self) == /\ pc[self] = "debit"
               /\ LET a == accounts[self].from IN
                    IF debitPrecond(self)
                       THEN /\ \/ /\ debits' = (debits \cup {[a |-> a, t |-> self]})
                               \/ /\ TRUE
                                  /\ UNCHANGED debits
                       ELSE /\ TRUE
                            /\ UNCHANGED debits
               /\ pc' = [pc EXCEPT ![self] = "retryDebit"]
               /\ UNCHANGED << credits, amount, accounts, kredits, bebits, 
                               emount, eccounts >>

retryDebit(self) == /\ pc[self] = "retryDebit"
                    /\ IF debitPrecond(self)
                          THEN /\ pc' = [pc EXCEPT ![self] = "debit"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "credit"]
                    /\ UNCHANGED << credits, debits, amount, accounts, kredits, 
                                    bebits, emount, eccounts >>

credit(self) == /\ pc[self] = "credit"
                /\ LET a == accounts[self].to IN
                     IF creditPrecond(self)
                        THEN /\ \/ /\ credits' = (credits \cup {[a |-> a, t |-> self]})
                                \/ /\ TRUE
                                   /\ UNCHANGED credits
                        ELSE /\ TRUE
                             /\ UNCHANGED credits
                /\ pc' = [pc EXCEPT ![self] = "retryCredit"]
                /\ UNCHANGED << debits, amount, accounts, kredits, bebits, 
                                emount, eccounts >>

retryCredit(self) == /\ pc[self] = "retryCredit"
                     /\ IF creditPrecond(self)
                           THEN /\ pc' = [pc EXCEPT ![self] = "credit"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << credits, debits, amount, accounts, 
                                     kredits, bebits, emount, eccounts >>

trans(self) == choose_accounts(self) \/ choose_amount(self) \/ debit(self)
                  \/ retryDebit(self) \/ credit(self) \/ retryCredit(self)

choose_eccounts(self) == /\ pc[self] = "choose_eccounts"
                         /\ \E account1 \in Eccount:
                              \E account2 \in Eccount \ {account1}:
                                eccounts' = [eccounts EXCEPT ![self] = [from |-> account1, to |-> account2]]
                         /\ pc' = [pc EXCEPT ![self] = "choose_emount"]
                         /\ UNCHANGED << credits, debits, amount, accounts, 
                                         kredits, bebits, emount >>

choose_emount(self) == /\ pc[self] = "choose_emount"
                       /\ LET a == eccounts[self].from IN
                            \E am \in 1..emountAvail(eccounts[self].from):
                              emount' = [emount EXCEPT ![self] = am]
                       /\ pc' = [pc EXCEPT ![self] = "bebit"]
                       /\ UNCHANGED << credits, debits, amount, accounts, 
                                       kredits, bebits, eccounts >>

bebit(self) == /\ pc[self] = "bebit"
               /\ LET a == eccounts[self].from IN
                    IF bebitPrecond(self)
                       THEN /\ \/ /\ bebits' = (bebits \cup {[a |-> a, t |-> self]})
                               \/ /\ TRUE
                                  /\ UNCHANGED bebits
                       ELSE /\ TRUE
                            /\ UNCHANGED bebits
               /\ pc' = [pc EXCEPT ![self] = "retryBebit"]
               /\ UNCHANGED << credits, debits, amount, accounts, kredits, 
                               emount, eccounts >>

retryBebit(self) == /\ pc[self] = "retryBebit"
                    /\ IF bebitPrecond(self)
                          THEN /\ pc' = [pc EXCEPT ![self] = "bebit"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "kredit"]
                    /\ UNCHANGED << credits, debits, amount, accounts, kredits, 
                                    bebits, emount, eccounts >>

kredit(self) == /\ pc[self] = "kredit"
                /\ LET a == eccounts[self].to IN
                     IF kreditPrecond(self)
                        THEN /\ \/ /\ kredits' = (kredits \cup {[a |-> a, t |-> self]})
                                \/ /\ TRUE
                                   /\ UNCHANGED kredits
                        ELSE /\ TRUE
                             /\ UNCHANGED kredits
                /\ pc' = [pc EXCEPT ![self] = "retryKredit"]
                /\ UNCHANGED << credits, debits, amount, accounts, bebits, 
                                emount, eccounts >>

retryKredit(self) == /\ pc[self] = "retryKredit"
                     /\ IF kreditPrecond(self)
                           THEN /\ pc' = [pc EXCEPT ![self] = "kredit"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << credits, debits, amount, accounts, 
                                     kredits, bebits, emount, eccounts >>

drans(self) == choose_eccounts(self) \/ choose_emount(self) \/ bebit(self)
                  \/ retryBebit(self) \/ kredit(self) \/ retryKredit(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Transfer: trans(self))
           \/ (\E self \in Dransfer: drans(self))
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

NonEmptyEccounts(t) ==
    /\ eccounts[t].from # Empty
    /\ eccounts[t].to # Empty
    
DifferentAccounts(t) == accounts[t].from # accounts[t].to

DifferentEccounts(t) == eccounts[t].from # eccounts[t].to

EAccounts == [from: EAccount, to: EAccount]

EEccounts == [from: EEccount, to: EEccount]

AT == [a: Account, t: Transfer]

ED == [a: Eccount, t: Dransfer]

pcLabels == pc \in
    [Transfer \cup Dransfer ->
        {"choose_accounts", "choose_amount", "debit", "retryDebit", "credit", "retryCredit", "Done"}
        \cup
        {"choose_eccounts", "choose_emount", "bebit", "retryBebit", "kredit", "retryKredit", "Done"}]

TypeOK ==
    /\ credits \in SUBSET AT
    /\ IsFiniteSet(credits)
    /\ debits \in SUBSET AT
    /\ IsFiniteSet(debits)
    /\ amount \in [Transfer -> Nat]
    /\ accounts \in [Transfer -> EAccounts]
    /\ kredits \in SUBSET ED
    /\ IsFiniteSet(kredits)
    /\ bebits \in SUBSET ED
    /\ IsFiniteSet(bebits)
    /\ emount \in [Dransfer -> Nat]
    /\ eccounts \in [Dransfer -> EEccounts]
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
    /\ \A t \in Dransfer:
        \/ eccounts[t] = EmptyEccounts
        \/ DifferentEccounts(t) /\ NonEmptyEccounts(t)
    /\ \A t \in Transfer: pc[t] \in {"choose_accounts", "choose_amount"} => debitPrecond(t)
    /\ \A t \in Dransfer: pc[t] \in {"choose_eccounts", "choose_emount"} => bebitPrecond(t)
    /\ \A t \in Transfer:
        pc[t] \notin {"choose_accounts"} <=> NonEmptyAccounts(t)
    /\ \A t \in Dransfer:
        pc[t] \notin {"choose_eccounts"} <=> NonEmptyEccounts(t)

IndSpec == IndInv /\ [][Next]_vars

CommonIndInv ==
    /\ amount \in [Transfer -> Nat]
    /\ accounts \in [Transfer -> EAccounts]
    /\ pcLabels
    /\ Imbalance = 0
    /\ \A t \in Transfer:
        \/ accounts[t] = EmptyAccounts
        \/ DifferentAccounts(t) /\ NonEmptyAccounts(t)
    /\ \A t \in Transfer: pc[t] \in {"choose_accounts", "choose_amount"} => debitPrecond(t)
    /\ \A t \in Transfer:
        pc[t] \notin {"choose_accounts"} <=> NonEmptyAccounts(t)

IndNat == 0..2

IndInvInteractiveStateConstraints ==
    /\ \A c \in credits: \E d \in debits: 
        /\ d.t = c.t
        /\ d.a # c.a
        /\ opAmount(d) = opAmount(c)
    /\ \A t \in Transfer:
        amount[t] = 0 <=> pc[t] = "choose_amount"

====
