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
Dransfer -> Account -> kredit or bebit
Dransfer -> amount
***************************************)

(***************************************************************************
--algorithm MoneyDransferPendingExplicit {
    variables
       kredits = {},
       bebits = {},
       amount = [t \in Dransfer |-> 0],
       accounts = [t \in Dransfer |-> EmptyEccounts],
       pendingDrans = {}

    define {
        opAmount(dc) == dc[2]

        accountKredits(a) == MapThenSumSetE(LAMBDA c: IF c[1].a = a THEN opAmount(c) ELSE 0, kredits)

        accountBebits(a) == MapThenSumSetE(LAMBDA d: IF d[1].a = a THEN opAmount(d) ELSE 0, bebits)

        amountAvail(a) == Evail + accountKredits(a) - accountBebits(a)

        isTransKnownToItem(t, a, dc) == dc[1].a = a /\ dc[1].t = t

        isTransKnown(t, a, bal) == \E dc \in bal: isTransKnownToItem(t, a, dc)

        initPrecond(t) == ~\E a \in Eccount: isTransKnown(t, a, bebits)

        debitPrecond(t) == ~\E a \in Eccount:
            \/ isTransKnown(t, a, bebits)
            \/ isTransKnown(t, a, kredits)

        creditPrecond(t) ==
            /\ ~\E a \in Eccount: isTransKnown(t, a, kredits)
            /\ ~isTransKnown(t, accounts[t].to, bebits)
            /\ isTransKnown(t, accounts[t].from, bebits)

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
                        bebits := bebits \cup {<<[a |-> a, t |-> self], amount[self]>>};
                        pendingDrans := pendingDrans \cup {<<self, amount[self]>>};
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
                    pendingDrans := pendingDrans \ {<<self, amount[self]>>};
                }
            };
    }
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "360e9d86" /\ chksum(tla) = "e947670c")
VARIABLES kredits, bebits, amount, accounts, pendingDrans, pc

(* define statement *)
opAmount(dc) == dc[2]

accountKredits(a) == MapThenSumSetE(LAMBDA c: IF c[1].a = a THEN opAmount(c) ELSE 0, kredits)

accountBebits(a) == MapThenSumSetE(LAMBDA d: IF d[1].a = a THEN opAmount(d) ELSE 0, bebits)

amountAvail(a) == Evail + accountKredits(a) - accountBebits(a)

isTransKnownToItem(t, a, dc) == dc[1].a = a /\ dc[1].t = t

isTransKnown(t, a, bal) == \E dc \in bal: isTransKnownToItem(t, a, dc)

initPrecond(t) == ~\E a \in Eccount: isTransKnown(t, a, bebits)

debitPrecond(t) == ~\E a \in Eccount:
    \/ isTransKnown(t, a, bebits)
    \/ isTransKnown(t, a, kredits)

creditPrecond(t) ==
    /\ ~\E a \in Eccount: isTransKnown(t, a, kredits)
    /\ ~isTransKnown(t, accounts[t].to, bebits)
    /\ isTransKnown(t, accounts[t].from, bebits)

pendingTransAmount(pt) == pt[2]


vars == << kredits, bebits, amount, accounts, pendingDrans, pc >>

ProcSet == (Dransfer)

Init == (* Global variables *)
        /\ kredits = {}
        /\ bebits = {}
        /\ amount = [t \in Dransfer |-> 0]
        /\ accounts = [t \in Dransfer |-> EmptyEccounts]
        /\ pendingDrans = {}
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
              /\ UNCHANGED << kredits, bebits, pendingDrans >>

debit(self) == /\ pc[self] = "debit"
               /\ LET a == accounts[self].from IN
                    IF debitPrecond(self)
                       THEN /\ \/ /\ bebits' = (bebits \cup {<<[a |-> a, t |-> self], amount[self]>>})
                                  /\ pendingDrans' = (pendingDrans \cup {<<self, amount[self]>>})
                               \/ /\ TRUE
                                  /\ UNCHANGED <<bebits, pendingDrans>>
                       ELSE /\ TRUE
                            /\ UNCHANGED << bebits, pendingDrans >>
               /\ pc' = [pc EXCEPT ![self] = "retryDebit"]
               /\ UNCHANGED << kredits, amount, accounts >>

retryDebit(self) == /\ pc[self] = "retryDebit"
                    /\ IF debitPrecond(self)
                          THEN /\ pc' = [pc EXCEPT ![self] = "debit"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "credit"]
                    /\ UNCHANGED << kredits, bebits, amount, accounts, 
                                    pendingDrans >>

credit(self) == /\ pc[self] = "credit"
                /\ LET a == accounts[self].to IN
                     IF creditPrecond(self)
                        THEN /\ kredits' = (kredits \cup {<<[a |-> a, t |-> self], amount[self]>>})
                             /\ pendingDrans' = pendingDrans \ {<<self, amount[self]>>}
                        ELSE /\ TRUE
                             /\ UNCHANGED << kredits, pendingDrans >>
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << bebits, amount, accounts >>

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

CreditTotal == MapThenSumSetE(opAmount, kredits)

DebitTotal == MapThenSumSetE(opAmount, bebits)

AmountIsPending(t) ==
    /\ pc[t] \in {"debit", "retryDebit", "credit"}
    /\ creditPrecond(t)

AmountPendingTotal == MapThenSumSet(pendingTransAmount, pendingDrans)

TransInPendingTrans(t) == \E tp \in pendingDrans: tp[1] = t /\ tp[2] = amount[t]

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

PendingTransDerived == \A pt \in pendingDrans: \E d \in bebits: d[1].t = pt[1] /\ d[2] = pt[2]

TypeOK ==
    /\ kredits \in SUBSET (AT \X Nat)
    /\ IsFiniteSet(kredits)
    /\ bebits \in SUBSET (AT \X Nat)
    /\ IsFiniteSet(bebits)
    /\ pendingDrans \in SUBSET TN
    /\ IsFiniteSet(pendingDrans)
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
    /\ \A c \in kredits: \E d \in bebits:
        /\ d[1].t = c[1].t
        /\ d[1].a # c[1].a
        /\ opAmount(d) = opAmount(c)
    /\ \A t \in Dransfer:
        amount[t] = 0 <=> pc[t] = "init"


====
