---- MODULE MoneyTransferReplicated ----
EXTENDS MoneyTransferCommon, FiniteSets, FiniteSetsExt,
Sequences, SequencesExt, TLC

CONSTANTS Dransfer, Eccount, account(_), eccount(_), transfer(_), dransfer(_)

EmptyAccounts == [from |-> Empty, to |-> Empty]
EmptyAccountsAmount == [from |-> Empty, to |-> Empty, am |-> 0]

EEccount == Eccount \cup {Empty}

EmptyEccounts == [from |-> Empty, to |-> Empty]
EmptyEccountsEmount == [from |-> Empty, to |-> Empty, am |-> 0]

EAccounts == [from: EAccount, to: EAccount]
EEccounts == [from: EEccount, to: EEccount]

EAccountsAmount == [from: EAccount, to: EAccount, am: Nat]
EEccountsEmount == [from: EEccount, to: EEccount, am: Nat]

AT == [a: Account, t: Transfer]
ED == [a: Eccount, t: Dransfer]

(***************************************************************************
 ***************************************************************************)

(***************************************************************************
--algorithm MoneyTransferReplicated {
    variables
       credits = {},
       debits = {},
       amount = [t \in Transfer |-> 0],
       accounts = [t \in Transfer |-> EmptyAccounts],
       kredits = {},
       bebits = {},
       eccountsEmount = [t \in Dransfer |-> EmptyEccountsEmount],

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

        dransEmount(t) == eccountsEmount[t].am

        opEmount(dc) == eccountsEmount[dc.t].am

        bebitPrecond(t) == ~\E a \in Eccount:
            \/ isTransKnown(t, a, bebits)
            \/ isTransKnown(t, a, kredits)

        kreditPrecond(t) ==
            /\ ~\E a \in Eccount: isTransKnown(t, a, kredits)
            /\ ~isTransKnown(t, eccountsEmount[t].to, bebits)
            /\ isTransKnown(t, eccountsEmount[t].from, bebits)
    }

    process (trans \in Transfer)
    {
        choose_accounts_amount:
            with (account1 \in Account; account2 \in Account \ {account1}; am \in 1..amountAvail(account1)) {
                accounts[self] := [from |-> account1, to |-> account2];
                amount[self] := am;
                eccountsEmount[dransfer(self)] := [
                    from |-> eccount(account1),
                    to |-> eccount(account2),
                    am |-> am];
            };

        debit:
            with (a = accounts[self].from) {
                if (debitPrecond(self)) {
                    debits := debits \cup {[a |-> a, t |-> self]};
                }
            };

        credit:
            with (a = accounts[self].to) {
                if (creditPrecond(self)) {
                    credits := credits \cup {[a |-> a, t |-> self]};
                }
            };
    }

    process (drans \in Dransfer)
    {
        choose_eccounts_emount:
            await eccountsEmount[self] # EmptyAccountsAmount;

        bebit:
            with (a = eccountsEmount[self].from) {
                if (bebitPrecond(self)) {
                    with (bebit = [a |-> a, t |-> self]) {
                        bebits := bebits \cup {bebit};
                    }
                }
            };


        kredit:
            with (a = eccountsEmount[self].to) {
                if (kreditPrecond(self)) {
                    with (kredit = [a |-> a, t |-> self]) {
                        kredits := kredits \cup {kredit};
                    }
                }
            };
    }
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "b93cdd5" /\ chksum(tla) = "6bade1fc")
VARIABLES credits, debits, amount, accounts, kredits, bebits, eccountsEmount, 
          pc

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

dransEmount(t) == eccountsEmount[t].am

opEmount(dc) == eccountsEmount[dc.t].am

bebitPrecond(t) == ~\E a \in Eccount:
    \/ isTransKnown(t, a, bebits)
    \/ isTransKnown(t, a, kredits)

kreditPrecond(t) ==
    /\ ~\E a \in Eccount: isTransKnown(t, a, kredits)
    /\ ~isTransKnown(t, eccountsEmount[t].to, bebits)
    /\ isTransKnown(t, eccountsEmount[t].from, bebits)


vars == << credits, debits, amount, accounts, kredits, bebits, eccountsEmount, 
           pc >>

ProcSet == (Transfer) \cup (Dransfer)

Init == (* Global variables *)
        /\ credits = {}
        /\ debits = {}
        /\ amount = [t \in Transfer |-> 0]
        /\ accounts = [t \in Transfer |-> EmptyAccounts]
        /\ kredits = {}
        /\ bebits = {}
        /\ eccountsEmount = [t \in Dransfer |-> EmptyEccountsEmount]
        /\ pc = [self \in ProcSet |-> CASE self \in Transfer -> "choose_accounts_amount"
                                        [] self \in Dransfer -> "choose_eccounts_emount"]

choose_accounts_amount(self) == /\ pc[self] = "choose_accounts_amount"
                                /\ \E account1 \in Account:
                                     \E account2 \in Account \ {account1}:
                                       \E am \in 1..amountAvail(account1):
                                         /\ accounts' = [accounts EXCEPT ![self] = [from |-> account1, to |-> account2]]
                                         /\ amount' = [amount EXCEPT ![self] = am]
                                         /\ eccountsEmount' = [eccountsEmount EXCEPT ![dransfer(self)] =                               [
                                                                                                         from |-> eccount(account1),
                                                                                                         to |-> eccount(account2),
                                                                                                         am |-> am]]
                                /\ pc' = [pc EXCEPT ![self] = "debit"]
                                /\ UNCHANGED << credits, debits, kredits, 
                                                bebits >>

debit(self) == /\ pc[self] = "debit"
               /\ LET a == accounts[self].from IN
                    IF debitPrecond(self)
                       THEN /\ debits' = (debits \cup {[a |-> a, t |-> self]})
                       ELSE /\ TRUE
                            /\ UNCHANGED debits
               /\ pc' = [pc EXCEPT ![self] = "credit"]
               /\ UNCHANGED << credits, amount, accounts, kredits, bebits, 
                               eccountsEmount >>

credit(self) == /\ pc[self] = "credit"
                /\ LET a == accounts[self].to IN
                     IF creditPrecond(self)
                        THEN /\ credits' = (credits \cup {[a |-> a, t |-> self]})
                        ELSE /\ TRUE
                             /\ UNCHANGED credits
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << debits, amount, accounts, kredits, bebits, 
                                eccountsEmount >>

trans(self) == choose_accounts_amount(self) \/ debit(self) \/ credit(self)

choose_eccounts_emount(self) == /\ pc[self] = "choose_eccounts_emount"
                                /\ eccountsEmount[self] # EmptyAccountsAmount
                                /\ pc' = [pc EXCEPT ![self] = "bebit"]
                                /\ UNCHANGED << credits, debits, amount, 
                                                accounts, kredits, bebits, 
                                                eccountsEmount >>

bebit(self) == /\ pc[self] = "bebit"
               /\ LET a == eccountsEmount[self].from IN
                    IF bebitPrecond(self)
                       THEN /\ LET bebit == [a |-> a, t |-> self] IN
                                 bebits' = (bebits \cup {bebit})
                       ELSE /\ TRUE
                            /\ UNCHANGED bebits
               /\ pc' = [pc EXCEPT ![self] = "kredit"]
               /\ UNCHANGED << credits, debits, amount, accounts, kredits, 
                               eccountsEmount >>

kredit(self) == /\ pc[self] = "kredit"
                /\ LET a == eccountsEmount[self].to IN
                     IF kreditPrecond(self)
                        THEN /\ LET kredit == [a |-> a, t |-> self] IN
                                  kredits' = (kredits \cup {kredit})
                        ELSE /\ TRUE
                             /\ UNCHANGED kredits
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << credits, debits, amount, accounts, bebits, 
                                eccountsEmount >>

drans(self) == choose_eccounts_emount(self) \/ bebit(self) \/ kredit(self)

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
KreditTotal == MapThenSumSet(opEmount, kredits)

DebitTotal == MapThenSumSet(opAmount, debits)
BebitTotal == MapThenSumSet(opEmount, bebits)

AmountIsPending(t) ==
    /\ pc[t] \in {"debit", "credit", "Done"}
    /\ creditPrecond(t)
EmountIsPending(t) ==
    /\ pc[t] \in {"bebit", "kredit", "Done"}
    /\ kreditPrecond(t)

transPending == {t \in Transfer: AmountIsPending(t)}
dransPending == {t \in Dransfer: EmountIsPending(t)}

AmountPendingTotal == MapThenSumSet(transAmount, transPending)
EmountPendingTotal == MapThenSumSet(dransEmount, dransPending)

Imbalance == CreditTotal - DebitTotal + AmountPendingTotal
Ymbalance == KreditTotal - BebitTotal + EmountPendingTotal

NonEmptyAccounts(t) ==
    /\ accounts[t].from # Empty
    /\ accounts[t].to # Empty
 
NonEmptyEccounts(t) ==
    /\ eccountsEmount[t].from # Empty
    /\ eccountsEmount[t].to # Empty
    
DifferentAccounts(t) == accounts[t].from # accounts[t].to

DifferentEccounts(t) == eccountsEmount[t].from # eccountsEmount[t].to

pcLabels == pc \in
    [Transfer \cup Dransfer ->
        {"choose_accounts_amount", "debit", "credit", "Done"}
        \cup
        {"choose_eccounts_emount", "bebit", "kredit", "Done"}]

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
    /\ eccountsEmount \in [Dransfer -> EEccountsEmount]
    /\ pcLabels

Inv ==
    /\ TypeOK
    /\ Imbalance = 0
    /\ Ymbalance = 0
    
IndInv ==
    /\ TypeOK
    /\ Imbalance = 0
    /\ Ymbalance = 0
    /\ \A t \in Transfer:
        \/ accounts[t] = EmptyAccounts
        \/ DifferentAccounts(t) /\ NonEmptyAccounts(t)
    /\ \A t \in Dransfer:
        \/ eccountsEmount[t] = EmptyEccountsEmount
        \/ DifferentEccounts(t) /\ NonEmptyEccounts(t)
    /\ \A t \in Transfer: pc[t] \in {"choose_accounts_amount"} => debitPrecond(t)
    /\ \A t \in Dransfer: pc[t] \in {"choose_eccounts_emount"} => bebitPrecond(t)
    /\ \A t \in Transfer:
        pc[t] \notin {"choose_accounts_amount"} <=> NonEmptyAccounts(t)
    /\ \A t \in Dransfer:
        pc[transfer(t)] \notin {"choose_accounts_amount"} <=> NonEmptyEccounts(t)
    /\ \A t \in Dransfer:
        pc[transfer(t)] \in {"choose_accounts_amount"} => pc[t] \in {"choose_eccounts_emount"}

IndSpec == IndInv /\ [][Next]_vars

IndNat == 0..1

IndInvInteractiveStateConstraints ==
    /\ \A c \in credits: \E d \in debits: 
        /\ d.t = c.t
        /\ d.a # c.a
        /\ opAmount(d) = opAmount(c)
    /\ \A c \in kredits: \E d \in bebits: 
        /\ d.t = c.t
        /\ d.a # c.a
        /\ opEmount(d) = opEmount(c)
    /\ \A t \in Transfer:
        amount[t] = 0 <=> pc[t] \in {"choose_accounts_amount"}
    /\ \A t \in Dransfer:
        eccountsEmount[t].am = 0 <=> pc[transfer(t)] \in {"choose_accounts_amount"}

====
