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
IndInv violation found after 11:30 hours
Imbalance became 1 after "credit"
kueueKredit contained d1 :> e1
59869 distinct states found

Retry logic removed
IndInv violation found after 2:50 hours
Imbalance became 1 after "credit"
kueueKredit contained d1 :> e1
22825 distinct states found

Credit removed
IndInv violation found after 1:30 hours
Imbalance became 1 after "debit"
kueueBebit contained d1 :> e2
11977 distinct states found

kueueBebit condition added to debitPrecond
IndInv violation found after 1:20 hours
t1 in "choose_amount", this became false after "bebit":
~\E e \in Eccount: kueueBebit[dransfer(t1)] = e
the conclusion: d1 should not be in the "bebit" state
11306 distinct states found
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
       queueAccountAmount = [t \in Transfer |-> EmptyAccountsAmount],
       kueueBebit = [t \in Dransfer |-> Empty],
       kueueKredit = [t \in Dransfer |-> Empty]

    define {
        transAmount(t) == amount[t]

        opAmount(dc) == amount[dc.t]

        accountCredits(a) == MapThenSumSet(LAMBDA c: IF c.a = a THEN opAmount(c) ELSE 0, credits)

        accountDebits(a) == MapThenSumSet(LAMBDA d: IF d.a = a THEN opAmount(d) ELSE 0, debits)

        amountAvail(a) == Avail + accountCredits(a) - accountDebits(a)

        isTransKnown(t, a, bal) == \E dc \in bal: dc.a = a /\ dc.t = t

        debitPrecond(t) ==
            /\ ~\E a \in Account:
                \/ isTransKnown(t, a, debits)
                \/ isTransKnown(t, a, credits)
            /\ ~\E e \in Eccount:
                \/ kueueBebit[dransfer(t)] = e

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
        choose_accounts:
            with (account1 \in Account; account2 \in Account \ {account1}) {
                accounts[self] := [from |-> account1, to |-> account2];
            };

        choose_amount:
            with (a = accounts[self].from; am \in 1..amountAvail(a)) {
                amount[self] := am;
                queueAccountAmount[self] := [from |-> a, to |-> accounts[self].to, am |-> am];
            };

        debit:
            if (kueueBebit[dransfer(self)] # Empty) {
                with (message = kueueBebit[dransfer(self)]) {
                    assert message \in Eccount;
\*                    either {
                        debits := debits \cup {[a |-> account(message), t |-> self]};
                        kueueBebit[dransfer(self)] := Empty;
\*                    } or skip;
                }
            } else {
                with (a = accounts[self].from) {
                    if (debitPrecond(self)) {
\*                        either
                        debits := debits \cup {[a |-> a, t |-> self]};
\*                        or skip;
                    }
                }
            };

\*        retryDebit: if (debitPrecond(self)) goto debit;

\*        credit:
\*            if (kueueKredit[dransfer(self)] # Empty) {
\*                with (message = kueueKredit[dransfer(self)]) {
\*                    assert message \in Eccount;
\*\*                    either {
\*                        credits := credits \cup {[a |-> account(message), t |-> self]};
\*                        kueueKredit[dransfer(self)] := Empty;
\*\*                    } or skip;
\*                }
\*            } else {
\*                with (a = accounts[self].to) {
\*                    if (creditPrecond(self)) {
\*\*                        either
\*                        credits := credits \cup {[a |-> a, t |-> self]};
\*\*                        or skip;
\*                    }
\*                }
\*            };

\*        retryCredit: if (creditPrecond(self)) goto credit;
    }

    process (drans \in Dransfer)
    {
        choose_eccounts_emount:
            {
                await queueAccountAmount[transfer(self)] # EmptyAccountsAmount;
                with (message = queueAccountAmount[transfer(self)]) {
                    assert message \in EAccountsAmount;
                    eccountsEmount[self] := [
                        from |-> eccount(message.from),
                        to |-> eccount(message.to),
                        am |-> message.am];
                    queueAccountAmount[transfer(self)] := EmptyAccountsAmount;
                }
            };

        bebit:
            with (a = eccountsEmount[self].from) {
                if (bebitPrecond(self)) {
                    with (bebit = [a |-> a, t |-> self]) {
\*                        either {
                            bebits := bebits \cup {bebit};
                            kueueBebit[self] := a;
\*                        } or skip;
                    }
                }
            };

\*        retryBebit: if (bebitPrecond(self)) goto bebit;

\*        kredit:
\*            with (a = eccountsEmount[self].to) {
\*                if (kreditPrecond(self)) {
\*                    with (kredit = [a |-> a, t |-> self]) {
\*\*                        either {
\*                            kredits := kredits \cup {kredit};
\*                            kueueKredit[self] := a;
\*\*                        } or skip;
\*                    }
\*                }
\*            };

\*        retryKredit: if (kreditPrecond(self)) goto kredit;
    }
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "ec80edbe" /\ chksum(tla) = "ac46bb92")
VARIABLES credits, debits, amount, accounts, kredits, bebits, eccountsEmount, 
          queueAccountAmount, kueueBebit, kueueKredit, pc

(* define statement *)
transAmount(t) == amount[t]

opAmount(dc) == amount[dc.t]

accountCredits(a) == MapThenSumSet(LAMBDA c: IF c.a = a THEN opAmount(c) ELSE 0, credits)

accountDebits(a) == MapThenSumSet(LAMBDA d: IF d.a = a THEN opAmount(d) ELSE 0, debits)

amountAvail(a) == Avail + accountCredits(a) - accountDebits(a)

isTransKnown(t, a, bal) == \E dc \in bal: dc.a = a /\ dc.t = t

debitPrecond(t) ==
    /\ ~\E a \in Account:
        \/ isTransKnown(t, a, debits)
        \/ isTransKnown(t, a, credits)
    /\ ~\E e \in Eccount:
        \/ kueueBebit[dransfer(t)] = e

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
           queueAccountAmount, kueueBebit, kueueKredit, pc >>

ProcSet == (Transfer) \cup (Dransfer)

Init == (* Global variables *)
        /\ credits = {}
        /\ debits = {}
        /\ amount = [t \in Transfer |-> 0]
        /\ accounts = [t \in Transfer |-> EmptyAccounts]
        /\ kredits = {}
        /\ bebits = {}
        /\ eccountsEmount = [t \in Dransfer |-> EmptyEccountsEmount]
        /\ queueAccountAmount = [t \in Transfer |-> EmptyAccountsAmount]
        /\ kueueBebit = [t \in Dransfer |-> Empty]
        /\ kueueKredit = [t \in Dransfer |-> Empty]
        /\ pc = [self \in ProcSet |-> CASE self \in Transfer -> "choose_accounts"
                                        [] self \in Dransfer -> "choose_eccounts_emount"]

choose_accounts(self) == /\ pc[self] = "choose_accounts"
                         /\ \E account1 \in Account:
                              \E account2 \in Account \ {account1}:
                                accounts' = [accounts EXCEPT ![self] = [from |-> account1, to |-> account2]]
                         /\ pc' = [pc EXCEPT ![self] = "choose_amount"]
                         /\ UNCHANGED << credits, debits, amount, kredits, 
                                         bebits, eccountsEmount, 
                                         queueAccountAmount, kueueBebit, 
                                         kueueKredit >>

choose_amount(self) == /\ pc[self] = "choose_amount"
                       /\ LET a == accounts[self].from IN
                            \E am \in 1..amountAvail(a):
                              /\ amount' = [amount EXCEPT ![self] = am]
                              /\ queueAccountAmount' = [queueAccountAmount EXCEPT ![self] = [from |-> a, to |-> accounts[self].to, am |-> am]]
                       /\ pc' = [pc EXCEPT ![self] = "debit"]
                       /\ UNCHANGED << credits, debits, accounts, kredits, 
                                       bebits, eccountsEmount, kueueBebit, 
                                       kueueKredit >>

debit(self) == /\ pc[self] = "debit"
               /\ IF kueueBebit[dransfer(self)] # Empty
                     THEN /\ LET message == kueueBebit[dransfer(self)] IN
                               /\ Assert(message \in Eccount, 
                                         "Failure of assertion at line 112, column 21.")
                               /\ debits' = (debits \cup {[a |-> account(message), t |-> self]})
                               /\ kueueBebit' = [kueueBebit EXCEPT ![dransfer(self)] = Empty]
                     ELSE /\ LET a == accounts[self].from IN
                               IF debitPrecond(self)
                                  THEN /\ debits' = (debits \cup {[a |-> a, t |-> self]})
                                  ELSE /\ TRUE
                                       /\ UNCHANGED debits
                          /\ UNCHANGED kueueBebit
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << credits, amount, accounts, kredits, bebits, 
                               eccountsEmount, queueAccountAmount, kueueKredit >>

trans(self) == choose_accounts(self) \/ choose_amount(self) \/ debit(self)

choose_eccounts_emount(self) == /\ pc[self] = "choose_eccounts_emount"
                                /\ queueAccountAmount[transfer(self)] # EmptyAccountsAmount
                                /\ LET message == queueAccountAmount[transfer(self)] IN
                                     /\ Assert(message \in EAccountsAmount, 
                                               "Failure of assertion at line 158, column 21.")
                                     /\ eccountsEmount' = [eccountsEmount EXCEPT ![self] =                     [
                                                                                           from |-> eccount(message.from),
                                                                                           to |-> eccount(message.to),
                                                                                           am |-> message.am]]
                                     /\ queueAccountAmount' = [queueAccountAmount EXCEPT ![transfer(self)] = EmptyAccountsAmount]
                                /\ pc' = [pc EXCEPT ![self] = "bebit"]
                                /\ UNCHANGED << credits, debits, amount, 
                                                accounts, kredits, bebits, 
                                                kueueBebit, kueueKredit >>

bebit(self) == /\ pc[self] = "bebit"
               /\ LET a == eccountsEmount[self].from IN
                    IF bebitPrecond(self)
                       THEN /\ LET bebit == [a |-> a, t |-> self] IN
                                 /\ bebits' = (bebits \cup {bebit})
                                 /\ kueueBebit' = [kueueBebit EXCEPT ![self] = a]
                       ELSE /\ TRUE
                            /\ UNCHANGED << bebits, kueueBebit >>
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << credits, debits, amount, accounts, kredits, 
                               eccountsEmount, queueAccountAmount, kueueKredit >>

drans(self) == choose_eccounts_emount(self) \/ bebit(self)

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
    /\ pc[t] \in {"debit", "retryDebit", "credit", "retryCredit", "Done"}
    /\ creditPrecond(t)
EmountIsPending(t) ==
    /\ pc[t] \in {"bebit", "retryBebit", "kredit", "retryKredit", "Done"}
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
NonEmptyAccountsAmount(t) ==
    /\ queueAccountAmount[t].from # Empty
    /\ queueAccountAmount[t].to # Empty
    /\ queueAccountAmount[t].am # 0
NonEmptyEccounts(t) ==
    /\ eccountsEmount[t].from # Empty
    /\ eccountsEmount[t].to # Empty
    
DifferentAccounts(t) == accounts[t].from # accounts[t].to
DifferentAccountsAmount(t) ==
    /\ queueAccountAmount[t].from # queueAccountAmount[t].to
    /\ queueAccountAmount[t].am # 0
DifferentEccounts(t) == eccountsEmount[t].from # eccountsEmount[t].to

pcLabels == pc \in
    [Transfer \cup Dransfer ->
        {"choose_accounts", "choose_amount", "debit", "Done"}
        \cup
        {"choose_eccounts_emount", "bebit", "Done"}]

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
    /\ queueAccountAmount \in [Transfer -> EAccountsAmount]
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
    /\ \A t \in Transfer:
        \/ queueAccountAmount[t] = EmptyAccountsAmount
        \/ DifferentAccountsAmount(t) /\ NonEmptyAccountsAmount(t)
    /\ \A t \in Dransfer:
        \/ eccountsEmount[t] = EmptyEccountsEmount
        \/ DifferentEccounts(t) /\ NonEmptyEccounts(t)
    /\ \A t \in Transfer: pc[t] \in {"choose_accounts", "choose_amount"} => debitPrecond(t)
    /\ \A t \in Dransfer: pc[t] \in {"choose_eccounts_emount"} => bebitPrecond(t)
    /\ \A t \in Transfer:
        pc[t] \notin {"choose_accounts"} <=> NonEmptyAccounts(t)
    /\ \A t \in Dransfer:
        pc[t] \notin {"choose_eccounts_emount"} <=> NonEmptyEccounts(t)

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
        eccountsEmount[t].am = 0 <=> pc[t] \in {"choose_eccounts_emount"}

====
