----MODULE MoneyTransferPendingExplicit----
EXTENDS Naturals, FiniteSets, FiniteSetsExt

CONSTANTS Empty, Eccount, Dransfer, Evail

NNat == Nat \ {0}

EEccount == Eccount \cup {Empty}

EDransfer == Dransfer \cup {Empty}

EmptyEccounts == [from |-> Empty, to |-> Empty]

MapThenFoldSetE(op(_,_), base, f(_), choose(_), S) ==
  LET iter[s \in SUBSET S] ==
        IF s = {} THEN base
        ELSE LET x == choose(s)
             IN  op(f(x), iter[s \ {x}])
  IN  iter[S]

MapThenSumSetE(op(_), set) ==
   MapThenFoldSetE(+, 0, op, LAMBDA s : CHOOSE x \in s : TRUE, set)

(***************************************
Dransfer -> Account -> credit or debit
Dransfer -> amount
***************************************)

(***************************************************************************
--algorithm MoneyDransferPendingExplicit {
    variables
       kredits = {},
       debits = {},
       amount = [t \in Dransfer |-> 0],
       accounts = [t \in Dransfer |-> EmptyAccounts],
       pendingTrans = {}

    define {
        opAmount(dc) == dc[2]

        accountCredits(a) == MapThenSumSetE(LAMBDA c: IF c[1].a = a THEN opAmount(c) ELSE 0, kredits)

        accountDebits(a) == MapThenSumSetE(LAMBDA d: IF d[1].a = a THEN opAmount(d) ELSE 0, debits)

        amountAvail(a) == Evail + accountCredits(a) - accountDebits(a)

        isTransKnownToItem(t, a, dc) == dc[1].a = a /\ dc[1].t = t

        isTransKnown(t, a, bal) == \E dc \in bal: isTransKnownToItem(t, a, dc)

        initPrecond(t) == ~\E a \in Eccount: isTransKnown(t, a, debits)

        debitPrecond(t) == ~\E a \in Eccount:
            \/ isTransKnown(t, a, debits)
            \/ isTransKnown(t, a, kredits)

        creditPrecond(t) ==
            /\ ~\E a \in Eccount: isTransKnown(t, a, kredits)
            /\ ~isTransKnown(t, accounts[t].to, debits)
            /\ isTransKnown(t, accounts[t].from, debits)

        pendingTransAmount(pt) == pt[2]
    }

    process (trans \in Dransfer)
    {
        init:
            with (account1 \in Eccount; account2 \in Eccount \ {account1}; am \in NNat) {
                await amountAvail(account1) > 0;
                await am <= amountAvail(account1);
                accounts[self] := [from |-> account1, to |-> account2];
                amount[self] := am;
            };

        debit:
            with (a = accounts[self].from) {
                if (debitPrecond(self)) {
                    either {
                        debits := debits \cup {<<[a |-> a, t |-> self], amount[self]>>};
                        pendingTrans := pendingTrans \cup {<<self, amount[self]>>};
                    } or skip;
                } else {
                    skip;
                }
            };

        retryDebit:
            if (debitPrecond(self)) {
                goto debit;
            };

        credit:
            with (a = accounts[self].to) {
                if (creditPrecond(self)) {
                    kredits := kredits \cup {<<[a |-> a, t |-> self], amount[self]>>};
                    pendingTrans := pendingTrans \ {<<self, amount[self]>>};
                }
            };
    }
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "7d9585ec" /\ chksum(tla) = "ee80dfb2")
VARIABLES kredits, debits, amount, accounts, pendingTrans, pc

(* define statement *)
opAmount(dc) == dc[2]

accountCredits(a) == MapThenSumSetE(LAMBDA c: IF c[1].a = a THEN opAmount(c) ELSE 0, kredits)

accountDebits(a) == MapThenSumSetE(LAMBDA d: IF d[1].a = a THEN opAmount(d) ELSE 0, debits)

amountAvail(a) == Evail + accountCredits(a) - accountDebits(a)

isTransKnownToItem(t, a, dc) == dc[1].a = a /\ dc[1].t = t

isTransKnown(t, a, bal) == \E dc \in bal: isTransKnownToItem(t, a, dc)

initPrecond(t) == ~\E a \in Eccount: isTransKnown(t, a, debits)

debitPrecond(t) == ~\E a \in Eccount:
    \/ isTransKnown(t, a, debits)
    \/ isTransKnown(t, a, kredits)

creditPrecond(t) ==
    /\ ~\E a \in Eccount: isTransKnown(t, a, kredits)
    /\ ~isTransKnown(t, accounts[t].to, debits)
    /\ isTransKnown(t, accounts[t].from, debits)

pendingTransAmount(pt) == pt[2]


vars == << kredits, debits, amount, accounts, pendingTrans, pc >>

ProcSet == (Dransfer)

Init == (* Global variables *)
        /\ kredits = {}
        /\ debits = {}
        /\ amount = [t \in Dransfer |-> 0]
        /\ accounts = [t \in Dransfer |-> EmptyEccounts]
        /\ pendingTrans = {}
        /\ pc = [self \in ProcSet |-> "init"]

init(self) == /\ pc[self] = "init"
              /\ \E account1 \in Eccount:
                   \E account2 \in Eccount \ {account1}:
                     \E am \in NNat:
                       /\ amountAvail(account1) > 0
                       /\ am <= amountAvail(account1)
                       /\ accounts' = [accounts EXCEPT ![self] = [from |-> account1, to |-> account2]]
                       /\ amount' = [amount EXCEPT ![self] = am]
              /\ pc' = [pc EXCEPT ![self] = "debit"]
              /\ UNCHANGED << kredits, debits, pendingTrans >>

debit(self) == /\ pc[self] = "debit"
               /\ LET a == accounts[self].from IN
                    IF debitPrecond(self)
                       THEN /\ \/ /\ debits' = (debits \cup {<<[a |-> a, t |-> self], amount[self]>>})
                                  /\ pendingTrans' = (pendingTrans \cup {<<self, amount[self]>>})
                               \/ /\ TRUE
                                  /\ UNCHANGED <<debits, pendingTrans>>
                       ELSE /\ TRUE
                            /\ UNCHANGED << debits, pendingTrans >>
               /\ pc' = [pc EXCEPT ![self] = "retryDebit"]
               /\ UNCHANGED << kredits, amount, accounts >>

retryDebit(self) == /\ pc[self] = "retryDebit"
                    /\ IF debitPrecond(self)
                          THEN /\ pc' = [pc EXCEPT ![self] = "debit"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "credit"]
                    /\ UNCHANGED << kredits, debits, amount, accounts, 
                                    pendingTrans >>

credit(self) == /\ pc[self] = "credit"
                /\ LET a == accounts[self].to IN
                     IF creditPrecond(self)
                        THEN /\ kredits' = (kredits \cup {<<[a |-> a, t |-> self], amount[self]>>})
                             /\ pendingTrans' = pendingTrans \ {<<self, amount[self]>>}
                        ELSE /\ TRUE
                             /\ UNCHANGED << kredits, pendingTrans >>
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << debits, amount, accounts >>

trans(self) == init(self) \/ debit(self) \/ retryDebit(self)
                  \/ credit(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Dransfer: trans(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

CreditTotal == MapThenSumSet(opAmount, kredits)

DebitTotal == MapThenSumSet(opAmount, debits)

AmountIsPending(t) ==
    /\ pc[t] \in {"debit", "retryDebit", "credit"}
    /\ creditPrecond(t)

AmountPendingTotal == MapThenSumSet(pendingTransAmount, pendingTrans)

TransInPendingTrans(t) == \E tp \in pendingTrans: tp[1] = t /\ tp[2] = amount[t]

TransPendingEquivalence == \A t \in Dransfer: AmountIsPending(t)
    <=> TransInPendingTrans(t)

Imbalance == CreditTotal - DebitTotal + AmountPendingTotal

NonEmptyEccounts(t) ==
    /\ accounts[t].from # Empty
    /\ accounts[t].to # Empty

DifferentEccounts(t) == accounts[t].from # accounts[t].to

EEccounts == [from: EEccount, to: EEccount]

AT == [a: Eccount, t: Dransfer]

TN == Dransfer \X Nat

pcLabels == pc \in [Dransfer -> {"init", "debit", "retryDebit", "credit", "Done"}]

PendingTransDerived == \A pt \in pendingTrans: \E d \in debits: d[1].t = pt[1] /\ d[2] = pt[2]

TypeOK ==
    /\ kredits \in SUBSET (AT \X Nat)
    /\ IsFiniteSet(kredits)
    /\ debits \in SUBSET (AT \X Nat)
    /\ IsFiniteSet(debits)
    /\ pendingTrans \in SUBSET TN
    /\ IsFiniteSet(pendingTrans)
    /\ amount \in [Dransfer -> Nat]
    /\ accounts \in [Dransfer -> EEccounts]
    /\ pcLabels
    /\ TransPendingEquivalence
    /\ PendingTransDerived

Inv ==
    /\ TypeOK
    /\ Imbalance = 0

IndInv ==
    /\ TypeOK
    /\ Imbalance = 0
    /\ \A t \in Dransfer:
        \/ accounts[t] = EmptyEccounts
        \/ DifferentEccounts(t) /\ NonEmptyEccounts(t)
    /\ \A t \in Dransfer: pc[t] = "init" => initPrecond(t)
    /\ \A t \in Dransfer:
        pc[t] \notin {"init"} <=> NonEmptyEccounts(t)

IndSpec == IndInv /\ [][Next]_vars

CommonIndInv ==
    /\ amount \in [Dransfer -> Nat]
    /\ accounts \in [Dransfer -> EEccounts]
    /\ pcLabels
    /\ Imbalance = 0
    /\ \A t \in Dransfer:
        \/ accounts[t] = EmptyEccounts
        \/ DifferentEccounts(t) /\ NonEmptyEccounts(t)
    /\ \A t \in Dransfer: pc[t] = "init" => initPrecond(t)
    /\ \A t \in Dransfer:
        pc[t] \notin {"init"} <=> NonEmptyEccounts(t)

IndInvInteractiveStateConstraints ==
    /\ \A c \in kredits: \E d \in debits:
        /\ d[1].t = c[1].t
        /\ d[1].a # c[1].a
        /\ opAmount(d) = opAmount(c)
    /\ \A t \in Dransfer:
        amount[t] = 0 <=> pc[t] = "init"


====
