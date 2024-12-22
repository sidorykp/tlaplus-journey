----MODULE MoneyTransferPendingExplicit----
EXTENDS Naturals, FiniteSets, FiniteSetsExt

CONSTANTS Empty, Eccount, Dransfer, Evail

NNat == Nat \ {0}

EEccount == Eccount \cup {Empty}

EmptyEccounts == [from |-> Empty, to |-> Empty]

MapThenSumSetTerse(op(_), S) ==
    LET iter[s \in SUBSET S] ==
        IF s = {} THEN 0
        ELSE LET x == CHOOSE x \in s : TRUE
            IN op(x) + iter[s \ {x}]
    IN iter[S]

(***************************************
Dransfer -> Account -> kredit or bebit
Dransfer -> amount
***************************************)

(***************************************************************************
--algorithm MoneyDransferPendingExplicit {
    variables
       kredits = {},
       bebits = {},
       emount = [t \in Dransfer |-> 0],
       eccounts = [t \in Dransfer |-> EmptyEccounts],
       pendingDrans = {}

    define {
        opEmount(dc) == dc[2]

        accountKredits(a) == MapThenSumSetTerse(LAMBDA c: IF c[1].a = a THEN opEmount(c) ELSE 0, kredits)

        accountBebits(a) == MapThenSumSetTerse(LAMBDA d: IF d[1].a = a THEN opEmount(d) ELSE 0, bebits)

        amountAvail(a) == Evail + accountKredits(a) - accountBebits(a)

        isTransKnown(t, a, bal) == \E dc \in bal: dc[1].a = a /\ dc[1].t = t

        initPrecond(t) == ~\E a \in Eccount: isTransKnown(t, a, bebits)

        debitPrecond(t) == ~\E a \in Eccount:
            \/ isTransKnown(t, a, bebits)
            \/ isTransKnown(t, a, kredits)

        creditPrecond(t) ==
            /\ ~\E a \in Eccount: isTransKnown(t, a, kredits)
            /\ ~isTransKnown(t, eccounts[t].to, bebits)
            /\ isTransKnown(t, eccounts[t].from, bebits)

        pendingTransAmount(pt) == pt[2]
    }

    process (trans \in Dransfer)
    {
        init:
            with (account1 \in Eccount; account2 \in Eccount \ {account1}; am \in NNat) {
                await amountAvail(account1) > 0;
                await am <= amountAvail(account1);
                eccounts[self] := [from |-> account1, to |-> account2];
                emount[self] := am;
            };

        debit:
            with (a = eccounts[self].from) {
                if (debitPrecond(self)) {
                    either {
                        bebits := bebits \cup {<<[a |-> a, t |-> self], emount[self]>>};
                        pendingDrans := pendingDrans \cup {<<self, emount[self]>>};
                    } or skip;
                }
            };

        retryDebit: if (debitPrecond(self)) goto debit;

        credit:
            with (a = eccounts[self].to) {
                if (creditPrecond(self)) {
                    either {
                        kredits := kredits \cup {<<[a |-> a, t |-> self], emount[self]>>};
                        pendingDrans := pendingDrans \ {<<self, emount[self]>>};
                    } or skip;
                }
            };
            
        retryCredit: if (creditPrecond(self)) goto credit;
    }
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "f66f726b" /\ chksum(tla) = "60726b2e")
VARIABLES kredits, bebits, emount, eccounts, pendingDrans, pc

(* define statement *)
opEmount(dc) == dc[2]

accountKredits(a) == MapThenSumSetTerse(LAMBDA c: IF c[1].a = a THEN opEmount(c) ELSE 0, kredits)

accountBebits(a) == MapThenSumSetTerse(LAMBDA d: IF d[1].a = a THEN opEmount(d) ELSE 0, bebits)

amountAvail(a) == Evail + accountKredits(a) - accountBebits(a)

isTransKnown(t, a, bal) == \E dc \in bal: dc[1].a = a /\ dc[1].t = t

initPrecond(t) == ~\E a \in Eccount: isTransKnown(t, a, bebits)

debitPrecond(t) == ~\E a \in Eccount:
    \/ isTransKnown(t, a, bebits)
    \/ isTransKnown(t, a, kredits)

creditPrecond(t) ==
    /\ ~\E a \in Eccount: isTransKnown(t, a, kredits)
    /\ ~isTransKnown(t, eccounts[t].to, bebits)
    /\ isTransKnown(t, eccounts[t].from, bebits)

pendingTransAmount(pt) == pt[2]


vars == << kredits, bebits, emount, eccounts, pendingDrans, pc >>

ProcSet == (Dransfer)

Init == (* Global variables *)
        /\ kredits = {}
        /\ bebits = {}
        /\ emount = [t \in Dransfer |-> 0]
        /\ eccounts = [t \in Dransfer |-> EmptyEccounts]
        /\ pendingDrans = {}
        /\ pc = [self \in ProcSet |-> "init"]

init(self) == /\ pc[self] = "init"
              /\ \E account1 \in Eccount:
                   \E account2 \in Eccount \ {account1}:
                     \E am \in NNat:
                       /\ amountAvail(account1) > 0
                       /\ am <= amountAvail(account1)
                       /\ eccounts' = [eccounts EXCEPT ![self] = [from |-> account1, to |-> account2]]
                       /\ emount' = [emount EXCEPT ![self] = am]
              /\ pc' = [pc EXCEPT ![self] = "debit"]
              /\ UNCHANGED << kredits, bebits, pendingDrans >>

debit(self) == /\ pc[self] = "debit"
               /\ LET a == eccounts[self].from IN
                    IF debitPrecond(self)
                       THEN /\ \/ /\ bebits' = (bebits \cup {<<[a |-> a, t |-> self], emount[self]>>})
                                  /\ pendingDrans' = (pendingDrans \cup {<<self, emount[self]>>})
                               \/ /\ TRUE
                                  /\ UNCHANGED <<bebits, pendingDrans>>
                       ELSE /\ TRUE
                            /\ UNCHANGED << bebits, pendingDrans >>
               /\ pc' = [pc EXCEPT ![self] = "retryDebit"]
               /\ UNCHANGED << kredits, emount, eccounts >>

retryDebit(self) == /\ pc[self] = "retryDebit"
                    /\ IF debitPrecond(self)
                          THEN /\ pc' = [pc EXCEPT ![self] = "debit"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "credit"]
                    /\ UNCHANGED << kredits, bebits, emount, eccounts, 
                                    pendingDrans >>

credit(self) == /\ pc[self] = "credit"
                /\ LET a == eccounts[self].to IN
                     IF creditPrecond(self)
                        THEN /\ \/ /\ kredits' = (kredits \cup {<<[a |-> a, t |-> self], emount[self]>>})
                                   /\ pendingDrans' = pendingDrans \ {<<self, emount[self]>>}
                                \/ /\ TRUE
                                   /\ UNCHANGED <<kredits, pendingDrans>>
                        ELSE /\ TRUE
                             /\ UNCHANGED << kredits, pendingDrans >>
                /\ pc' = [pc EXCEPT ![self] = "retryCredit"]
                /\ UNCHANGED << bebits, emount, eccounts >>

retryCredit(self) == /\ pc[self] = "retryCredit"
                     /\ IF creditPrecond(self)
                           THEN /\ pc' = [pc EXCEPT ![self] = "credit"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << kredits, bebits, emount, eccounts, 
                                     pendingDrans >>

trans(self) == init(self) \/ debit(self) \/ retryDebit(self)
                  \/ credit(self) \/ retryCredit(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Dransfer: trans(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

CreditTotal == MapThenSumSetTerse(opEmount, kredits)

DebitTotal == MapThenSumSetTerse(opEmount, bebits)

AmountIsPending(t) ==
    /\ pc[t] \in {"debit", "retryDebit", "credit", "retryCredit"}
    /\ creditPrecond(t)

AmountPendingTotal == MapThenSumSet(pendingTransAmount, pendingDrans)

TransInPendingTrans(t) == \E tp \in pendingDrans: tp[1] = t /\ tp[2] = emount[t]

TransPendingEquivalence == \A t \in Dransfer: AmountIsPending(t)
    <=> TransInPendingTrans(t)

Imbalance == CreditTotal - DebitTotal + AmountPendingTotal

NonEmptyEccounts(t) ==
    /\ eccounts[t].from # Empty
    /\ eccounts[t].to # Empty

DifferentEccounts(t) == eccounts[t].from # eccounts[t].to

EEccounts == [from: EEccount, to: EEccount]

AT == [a: Eccount, t: Dransfer]

TN == Dransfer \X Nat

pcLabels == pc \in [Dransfer -> {"init", "debit", "retryDebit", "credit", "retryCredit", "Done"}]

PendingTransDerived == \A pt \in pendingDrans: \E d \in bebits: d[1].t = pt[1] /\ d[2] = pt[2]

TypeOK ==
    /\ kredits \in SUBSET (AT \X Nat)
    /\ IsFiniteSet(kredits)
    /\ bebits \in SUBSET (AT \X Nat)
    /\ IsFiniteSet(bebits)
    /\ pendingDrans \in SUBSET TN
    /\ IsFiniteSet(pendingDrans)
    /\ emount \in [Dransfer -> Nat]
    /\ eccounts \in [Dransfer -> EEccounts]
    /\ pcLabels

Inv ==
    /\ TypeOK
    /\ Imbalance = 0

IndInv ==
    /\ TypeOK
    /\ Imbalance = 0
    /\ \A t \in Dransfer:
        \/ eccounts[t] = EmptyEccounts
        \/ DifferentEccounts(t) /\ NonEmptyEccounts(t)
    /\ \A t \in Dransfer: pc[t] = "init" => initPrecond(t)
    /\ \A t \in Dransfer:
        pc[t] \notin {"init"} <=> NonEmptyEccounts(t)
    /\ TransPendingEquivalence
    /\ PendingTransDerived

IndSpec == IndInv /\ [][Next]_vars

CommonIndInv ==
    /\ emount \in [Dransfer -> Nat]
    /\ eccounts \in [Dransfer -> EEccounts]
    /\ pcLabels
    /\ Imbalance = 0
    /\ \A t \in Dransfer:
        \/ eccounts[t] = EmptyEccounts
        \/ DifferentEccounts(t) /\ NonEmptyEccounts(t)
    /\ \A t \in Dransfer: pc[t] = "init" => initPrecond(t)
    /\ \A t \in Dransfer:
        pc[t] \notin {"init"} <=> NonEmptyEccounts(t)

IndInvInteractiveStateConstraints ==
    /\ \A c \in kredits: \E d \in bebits:
        /\ d[1].t = c[1].t
        /\ d[1].a # c[1].a
        /\ opEmount(d) = opEmount(c)
    /\ \A t \in Dransfer:
        emount[t] = 0 <=> pc[t] = "init"


====
