---- MODULE MoneyTransferReplicated ----
EXTENDS MoneyTransferCommon, FiniteSets, FiniteSetsExt,
Sequences, SequencesExt, TLC

CONSTANTS Dransfer, Eccount, account(_), eccount(_), transfer(_), dransfer(_)

EmptyAccounts == [from |-> Empty, to |-> Empty]

EEccount == Eccount \cup {Empty}

EmptyEccounts == [from |-> Empty, to |-> Empty]

EAccounts == [from: EAccount, to: EAccount]
EEccounts == [from: EEccount, to: EEccount]

AT == [a: Account, t: Transfer]
ED == [a: Eccount, t: Dransfer]

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
       queueAccount = [t \in Transfer |-> EmptyAccounts],
       queueAmount = [t \in Transfer |-> 0],
       kueueBebit = [t \in Dransfer |-> Empty],
       kueueKredit = [t \in Dransfer |-> Empty]

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

        dransEmount(t) == emount[t]

        opEmount(dc) == emount[dc.t]

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
                queueAccount[self] := [from |-> account1, to |-> account2];
            };

        choose_amount:
            with (a = accounts[self].from; am \in 1..amountAvail(accounts[self].from)) {
                amount[self] := am;
                queueAmount[self] := am;
            };

        debit:
            if (kueueBebit[dransfer(self)] # Empty) {
                with (message = kueueBebit[dransfer(self)]) {
                    assert message \in Eccount;
                    either {
                        debits := debits \cup {[a |-> account(message), t |-> self]};
                        kueueBebit[dransfer(self)] := Empty;
                    } or skip;
                }
            } else {
                with (a = accounts[self].from) {
                    if (debitPrecond(self)) {
                        either debits := debits \cup {[a |-> a, t |-> self]};
                        or skip;
                    }
                }
            };

        retryDebit: if (debitPrecond(self)) goto debit;

        credit:
            if (kueueKredit[dransfer(self)] # Empty) {
                with (message = kueueKredit[dransfer(self)]) {
                    assert message \in Eccount;
                    either {
                        credits := credits \cup {[a |-> account(message), t |-> self]};
                        kueueKredit[dransfer(self)] := Empty;
                    } or skip;
                }
            } else {
                with (a = accounts[self].to) {
                    if (creditPrecond(self)) {
                        either credits := credits \cup {[a |-> a, t |-> self]};
                        or skip;
                    }
                }
            };

        retryCredit: if (creditPrecond(self)) goto credit;
    }

    process (drans \in Dransfer)
    {
        choose_eccounts:
            {
                await queueAccount[transfer(self)] # EmptyAccounts;
                with (message = queueAccount[transfer(self)]) {
                    assert message \in EAccounts;
                    eccounts[self] := [from |-> eccount(message.from), to |-> eccount(message.to)];
                    queueAccount[transfer(self)] := EmptyAccounts;
                }
            };

        choose_emount:
            {
                await queueAmount[transfer(self)] # 0;
                with (message = queueAmount[transfer(self)]) {
                    assert message \in NNat;
                    emount[self] := message;
                    queueAmount[transfer(self)] := 0;
                }
            };

        bebit:
            with (a = eccounts[self].from) {
                if (bebitPrecond(self)) {
                    with (bebit = [a |-> a, t |-> self]) {
                        either {
                            bebits := bebits \cup {bebit};
                            kueueBebit[self] := a;
                        } or skip;
                    }
                }
            };

        retryBebit: if (bebitPrecond(self)) goto bebit;

        kredit:
            with (a = eccounts[self].to) {
                if (kreditPrecond(self)) {
                    with (kredit = [a |-> a, t |-> self]) {
                        either {
                            kredits := kredits \cup {kredit};
                            kueueKredit[self] := a;
                        } or skip;
                    }
                }
            };

        retryKredit: if (kreditPrecond(self)) goto kredit;
    }
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "505848fa" /\ chksum(tla) = "b9c10bcb")
VARIABLES credits, debits, amount, accounts, kredits, bebits, emount, 
          eccounts, queueAccount, queueAmount, kueueBebit, kueueKredit, pc

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

dransEmount(t) == emount[t]

opEmount(dc) == emount[dc.t]

bebitPrecond(t) == ~\E a \in Eccount:
    \/ isTransKnown(t, a, bebits)
    \/ isTransKnown(t, a, kredits)

kreditPrecond(t) ==
    /\ ~\E a \in Eccount: isTransKnown(t, a, kredits)
    /\ ~isTransKnown(t, eccounts[t].to, bebits)
    /\ isTransKnown(t, eccounts[t].from, bebits)


vars == << credits, debits, amount, accounts, kredits, bebits, emount, 
           eccounts, queueAccount, queueAmount, kueueBebit, kueueKredit, pc
        >>

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
        /\ queueAccount = [t \in Transfer |-> EmptyAccounts]
        /\ queueAmount = [t \in Transfer |-> 0]
        /\ kueueBebit = [t \in Dransfer |-> Empty]
        /\ kueueKredit = [t \in Dransfer |-> Empty]
        /\ pc = [self \in ProcSet |-> CASE self \in Transfer -> "choose_accounts"
                                        [] self \in Dransfer -> "choose_eccounts"]

choose_accounts(self) == /\ pc[self] = "choose_accounts"
                         /\ \E account1 \in Account:
                              \E account2 \in Account \ {account1}:
                                /\ accounts' = [accounts EXCEPT ![self] = [from |-> account1, to |-> account2]]
                                /\ queueAccount' = [queueAccount EXCEPT ![self] = [from |-> account1, to |-> account2]]
                         /\ pc' = [pc EXCEPT ![self] = "choose_amount"]
                         /\ UNCHANGED << credits, debits, amount, kredits, 
                                         bebits, emount, eccounts, queueAmount, 
                                         kueueBebit, kueueKredit >>

choose_amount(self) == /\ pc[self] = "choose_amount"
                       /\ LET a == accounts[self].from IN
                            \E am \in 1..amountAvail(accounts[self].from):
                              /\ amount' = [amount EXCEPT ![self] = am]
                              /\ queueAmount' = [queueAmount EXCEPT ![self] = am]
                       /\ pc' = [pc EXCEPT ![self] = "debit"]
                       /\ UNCHANGED << credits, debits, accounts, kredits, 
                                       bebits, emount, eccounts, queueAccount, 
                                       kueueBebit, kueueKredit >>

debit(self) == /\ pc[self] = "debit"
               /\ IF kueueBebit[dransfer(self)] # Empty
                     THEN /\ LET message == kueueBebit[dransfer(self)] IN
                               /\ Assert(message \in Eccount, 
                                         "Failure of assertion at line 88, column 21.")
                               /\ \/ /\ debits' = (debits \cup {[a |-> account(message), t |-> self]})
                                     /\ kueueBebit' = [kueueBebit EXCEPT ![dransfer(self)] = Empty]
                                  \/ /\ TRUE
                                     /\ UNCHANGED <<debits, kueueBebit>>
                     ELSE /\ LET a == accounts[self].from IN
                               IF debitPrecond(self)
                                  THEN /\ \/ /\ debits' = (debits \cup {[a |-> a, t |-> self]})
                                          \/ /\ TRUE
                                             /\ UNCHANGED debits
                                  ELSE /\ TRUE
                                       /\ UNCHANGED debits
                          /\ UNCHANGED kueueBebit
               /\ pc' = [pc EXCEPT ![self] = "retryDebit"]
               /\ UNCHANGED << credits, amount, accounts, kredits, bebits, 
                               emount, eccounts, queueAccount, queueAmount, 
                               kueueKredit >>

retryDebit(self) == /\ pc[self] = "retryDebit"
                    /\ IF debitPrecond(self)
                          THEN /\ pc' = [pc EXCEPT ![self] = "debit"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "credit"]
                    /\ UNCHANGED << credits, debits, amount, accounts, kredits, 
                                    bebits, emount, eccounts, queueAccount, 
                                    queueAmount, kueueBebit, kueueKredit >>

credit(self) == /\ pc[self] = "credit"
                /\ IF kueueKredit[dransfer(self)] # Empty
                      THEN /\ LET message == kueueKredit[dransfer(self)] IN
                                /\ Assert(message \in Eccount, 
                                          "Failure of assertion at line 108, column 21.")
                                /\ \/ /\ credits' = (credits \cup {[a |-> account(message), t |-> self]})
                                      /\ kueueKredit' = [kueueKredit EXCEPT ![dransfer(self)] = Empty]
                                   \/ /\ TRUE
                                      /\ UNCHANGED <<credits, kueueKredit>>
                      ELSE /\ LET a == accounts[self].to IN
                                IF creditPrecond(self)
                                   THEN /\ \/ /\ credits' = (credits \cup {[a |-> a, t |-> self]})
                                           \/ /\ TRUE
                                              /\ UNCHANGED credits
                                   ELSE /\ TRUE
                                        /\ UNCHANGED credits
                           /\ UNCHANGED kueueKredit
                /\ pc' = [pc EXCEPT ![self] = "retryCredit"]
                /\ UNCHANGED << debits, amount, accounts, kredits, bebits, 
                                emount, eccounts, queueAccount, queueAmount, 
                                kueueBebit >>

retryCredit(self) == /\ pc[self] = "retryCredit"
                     /\ IF creditPrecond(self)
                           THEN /\ pc' = [pc EXCEPT ![self] = "credit"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << credits, debits, amount, accounts, 
                                     kredits, bebits, emount, eccounts, 
                                     queueAccount, queueAmount, kueueBebit, 
                                     kueueKredit >>

trans(self) == choose_accounts(self) \/ choose_amount(self) \/ debit(self)
                  \/ retryDebit(self) \/ credit(self) \/ retryCredit(self)

choose_eccounts(self) == /\ pc[self] = "choose_eccounts"
                         /\ queueAccount[transfer(self)] # EmptyAccounts
                         /\ LET message == queueAccount[transfer(self)] IN
                              /\ Assert(message \in EAccounts, 
                                        "Failure of assertion at line 132, column 21.")
                              /\ eccounts' = [eccounts EXCEPT ![self] = [from |-> eccount(message.from), to |-> eccount(message.to)]]
                              /\ queueAccount' = [queueAccount EXCEPT ![transfer(self)] = EmptyAccounts]
                         /\ pc' = [pc EXCEPT ![self] = "choose_emount"]
                         /\ UNCHANGED << credits, debits, amount, accounts, 
                                         kredits, bebits, emount, queueAmount, 
                                         kueueBebit, kueueKredit >>

choose_emount(self) == /\ pc[self] = "choose_emount"
                       /\ queueAmount[transfer(self)] # 0
                       /\ LET message == queueAmount[transfer(self)] IN
                            /\ Assert(message \in NNat, 
                                      "Failure of assertion at line 142, column 21.")
                            /\ emount' = [emount EXCEPT ![self] = message]
                            /\ queueAmount' = [queueAmount EXCEPT ![transfer(self)] = 0]
                       /\ pc' = [pc EXCEPT ![self] = "bebit"]
                       /\ UNCHANGED << credits, debits, amount, accounts, 
                                       kredits, bebits, eccounts, queueAccount, 
                                       kueueBebit, kueueKredit >>

bebit(self) == /\ pc[self] = "bebit"
               /\ LET a == eccounts[self].from IN
                    IF bebitPrecond(self)
                       THEN /\ LET bebit == [a |-> a, t |-> self] IN
                                 \/ /\ bebits' = (bebits \cup {bebit})
                                    /\ kueueBebit' = [kueueBebit EXCEPT ![self] = a]
                                 \/ /\ TRUE
                                    /\ UNCHANGED <<bebits, kueueBebit>>
                       ELSE /\ TRUE
                            /\ UNCHANGED << bebits, kueueBebit >>
               /\ pc' = [pc EXCEPT ![self] = "retryBebit"]
               /\ UNCHANGED << credits, debits, amount, accounts, kredits, 
                               emount, eccounts, queueAccount, queueAmount, 
                               kueueKredit >>

retryBebit(self) == /\ pc[self] = "retryBebit"
                    /\ IF bebitPrecond(self)
                          THEN /\ pc' = [pc EXCEPT ![self] = "bebit"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "kredit"]
                    /\ UNCHANGED << credits, debits, amount, accounts, kredits, 
                                    bebits, emount, eccounts, queueAccount, 
                                    queueAmount, kueueBebit, kueueKredit >>

kredit(self) == /\ pc[self] = "kredit"
                /\ LET a == eccounts[self].to IN
                     IF kreditPrecond(self)
                        THEN /\ LET kredit == [a |-> a, t |-> self] IN
                                  \/ /\ kredits' = (kredits \cup {kredit})
                                     /\ kueueKredit' = [kueueKredit EXCEPT ![self] = a]
                                  \/ /\ TRUE
                                     /\ UNCHANGED <<kredits, kueueKredit>>
                        ELSE /\ TRUE
                             /\ UNCHANGED << kredits, kueueKredit >>
                /\ pc' = [pc EXCEPT ![self] = "retryKredit"]
                /\ UNCHANGED << credits, debits, amount, accounts, bebits, 
                                emount, eccounts, queueAccount, queueAmount, 
                                kueueBebit >>

retryKredit(self) == /\ pc[self] = "retryKredit"
                     /\ IF kreditPrecond(self)
                           THEN /\ pc' = [pc EXCEPT ![self] = "kredit"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << credits, debits, amount, accounts, 
                                     kredits, bebits, emount, eccounts, 
                                     queueAccount, queueAmount, kueueBebit, 
                                     kueueKredit >>

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
KreditTotal == MapThenSumSet(opEmount, kredits)

DebitTotal == MapThenSumSet(opAmount, debits)
BebitTotal == MapThenSumSet(opEmount, bebits)

AmountIsPending(t) ==
    /\ pc[t] \in {"debit", "retryDebit", "credit", "retryCredit"}
    /\ creditPrecond(t)
EmountIsPending(t) ==
    /\ pc[t] \in {"bebit", "retryBebit", "kredit", "retryKredit"}
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
    /\ eccounts[t].from # Empty
    /\ eccounts[t].to # Empty
    
DifferentAccounts(t) == accounts[t].from # accounts[t].to
DifferentEccounts(t) == eccounts[t].from # eccounts[t].to

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
    /\ queueAccount \in [Transfer -> EAccounts]
    /\ queueAmount \in [Transfer -> Nat]
    /\ kueueBebit \in [Dransfer -> EEccount]
    /\ kueueKredit \in [Dransfer -> EEccount]
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
        amount[t] = 0 <=> pc[t] \in {"choose_accounts", "choose_amount"}
    /\ \A t \in Dransfer:
        emount[t] = 0 <=> pc[t] \in {"choose_eccounts", "choose_emount"}

====
