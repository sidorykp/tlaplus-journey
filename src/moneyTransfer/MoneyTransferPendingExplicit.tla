----MODULE MoneyTransferPendingExplicit----
EXTENDS Naturals, FiniteSets, FiniteSetsExt

CONSTANTS Empty, Account, Transfer, NAvail

NNat == Nat \ {0}

EAccount == Account \cup {Empty}

ETransfer == Transfer \cup {Empty}

EmptyAccounts == [from |-> Empty, to |-> Empty]
    
MapThenFoldSetE(op(_,_), base, f(_), choose(_), S) ==
  LET iter[s \in SUBSET S] ==
        IF s = {} THEN base
        ELSE LET x == choose(s)
             IN  op(f(x), iter[s \ {x}])
  IN  iter[S]

MapThenSumSetE(op(_), set) ==
   MapThenFoldSetE(+, 0, op, LAMBDA s : CHOOSE x \in s : TRUE, set)

(***************************************
Transfer -> Account -> credit or debit
Transfer -> amount
***************************************)

(***************************************************************************
--algorithm MoneyTransferPendingExplicit {
    variables
       credits = {},
       debits = {},
       amount = [t \in Transfer |-> 0],
       accounts = [t \in Transfer |-> EmptyAccounts],
       pendingTrans = {}

    define {
        opAmount(dc) == dc[2]

        accountCredits(a) == MapThenSumSetE(LAMBDA c: IF c[1].a = a THEN opAmount(c) ELSE 0, credits)

        accountDebits(a) == MapThenSumSetE(LAMBDA d: IF d[1].a = a THEN opAmount(d) ELSE 0, debits)

        amountAvail(a) == NAvail + accountCredits(a) - accountDebits(a)
        
        isTransKnownToItem(t, a, dc) == dc[1].a = a /\ dc[1].t = t
        
        isTransKnown(t, a, bal) == \E dc \in bal: isTransKnownToItem(t, a, dc)
        
        initPrecond(t) == ~\E a \in Account: isTransKnown(t, a, debits)
        
        debitPrecond(t) == ~\E a \in Account:
            \/ isTransKnown(t, a, debits)
            \/ isTransKnown(t, a, credits)
        
        creditPrecond(t) ==
            /\ ~\E a \in Account: isTransKnown(t, a, credits)
            /\ ~isTransKnown(t, accounts[t].to, debits)
            /\ isTransKnown(t, accounts[t].from, debits)
        
        pendingTransAmount(pt) == pt[2]
    }

    process (trans \in Transfer)    
    {
        init:
            if (initPrecond(self)) {
                with (account1 \in Account; account2 \in Account \ {account1}; am \in NNat) {
                    await amountAvail(account1) > 0;
                    await am <= amountAvail(account1);
                    accounts[self] := [from |-> account1, to |-> account2];
                    amount[self] := am;
                }
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
                    credits := credits \cup {<<[a |-> a, t |-> self], amount[self]>>};
                    pendingTrans := pendingTrans \ {<<self, amount[self]>>};
                }
            };
    }
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "5b1a7a92" /\ chksum(tla) = "f4ad47ad")
VARIABLES credits, debits, amount, accounts, pendingTrans, pc

(* define statement *)
opAmount(dc) == dc[2]

accountCredits(a) == MapThenSumSetE(LAMBDA c: IF c[1].a = a THEN opAmount(c) ELSE 0, credits)

accountDebits(a) == MapThenSumSetE(LAMBDA d: IF d[1].a = a THEN opAmount(d) ELSE 0, debits)

amountAvail(a) == NAvail + accountCredits(a) - accountDebits(a)

isTransKnownToItem(t, a, dc) == dc[1].a = a /\ dc[1].t = t

isTransKnown(t, a, bal) == \E dc \in bal: isTransKnownToItem(t, a, dc)

initPrecond(t) == ~\E a \in Account: isTransKnown(t, a, debits)

debitPrecond(t) == ~\E a \in Account:
    \/ isTransKnown(t, a, debits)
    \/ isTransKnown(t, a, credits)

creditPrecond(t) ==
    /\ ~\E a \in Account: isTransKnown(t, a, credits)
    /\ ~isTransKnown(t, accounts[t].to, debits)
    /\ isTransKnown(t, accounts[t].from, debits)

pendingTransAmount(pt) == pt[2]


vars == << credits, debits, amount, accounts, pendingTrans, pc >>

ProcSet == (Transfer)

Init == (* Global variables *)
        /\ credits = {}
        /\ debits = {}
        /\ amount = [t \in Transfer |-> 0]
        /\ accounts = [t \in Transfer |-> EmptyAccounts]
        /\ pendingTrans = {}
        /\ pc = [self \in ProcSet |-> "init"]

init(self) == /\ pc[self] = "init"
              /\ IF initPrecond(self)
                    THEN /\ \E account1 \in Account:
                              \E account2 \in Account \ {account1}:
                                \E am \in NNat:
                                  /\ amountAvail(account1) > 0
                                  /\ am <= amountAvail(account1)
                                  /\ accounts' = [accounts EXCEPT ![self] = [from |-> account1, to |-> account2]]
                                  /\ amount' = [amount EXCEPT ![self] = am]
                    ELSE /\ TRUE
                         /\ UNCHANGED << amount, accounts >>
              /\ pc' = [pc EXCEPT ![self] = "debit"]
              /\ UNCHANGED << credits, debits, pendingTrans >>

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
               /\ UNCHANGED << credits, amount, accounts >>

retryDebit(self) == /\ pc[self] = "retryDebit"
                    /\ IF debitPrecond(self)
                          THEN /\ pc' = [pc EXCEPT ![self] = "debit"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "credit"]
                    /\ UNCHANGED << credits, debits, amount, accounts, 
                                    pendingTrans >>

credit(self) == /\ pc[self] = "credit"
                /\ LET a == accounts[self].to IN
                     IF creditPrecond(self)
                        THEN /\ credits' = (credits \cup {<<[a |-> a, t |-> self], amount[self]>>})
                             /\ pendingTrans' = pendingTrans \ {<<self, amount[self]>>}
                        ELSE /\ TRUE
                             /\ UNCHANGED << credits, pendingTrans >>
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << debits, amount, accounts >>

trans(self) == init(self) \/ debit(self) \/ retryDebit(self)
                  \/ credit(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Transfer: trans(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
    
CreditTotal == MapThenSumSetE(opAmount, credits)

DebitTotal == MapThenSumSetE(opAmount, debits)

AmountIsPending(t) ==
    /\ pc[t] \in {"credit", "debit", "retryDebit"}
    /\ creditPrecond(t)

AmountPendingTotal == MapThenSumSet(pendingTransAmount, pendingTrans)

TransInPendingTrans(t) == \E tp \in pendingTrans: tp[1] = t /\ tp[2] = amount[t]

TransPendingEquivalence == \A t \in Transfer: AmountIsPending(t)
    <=> TransInPendingTrans(t)

Imbalance == CreditTotal - DebitTotal + AmountPendingTotal

NonEmptyAccounts(t) ==
    /\ accounts[t].from # Empty
    /\ accounts[t].to # Empty
    
DifferentAccounts(t) == accounts[t].from # accounts[t].to

EAccounts == [from: EAccount, to: EAccount]

AT == [a: Account, t: Transfer]

TN == Transfer \X Nat

pcLabels == pc \in [Transfer -> {"Done", "init", "debit", "credit", "retryDebit"}]

PendingTransDerived == \A pt \in pendingTrans: \E d \in debits: d[1].t = pt[1] /\ d[2] = pt[2]

PendingTransUniqueness == ~\E pt1, pt2 \in pendingTrans: pt1 # pt2 /\ pt1[1] = pt2[1]

TypeOK ==
    /\ credits \in SUBSET (AT \X Nat)
    /\ IsFiniteSet(credits)
    /\ debits \in SUBSET (AT \X Nat)
    /\ IsFiniteSet(debits)
    /\ pendingTrans \in SUBSET TN
    /\ IsFiniteSet(pendingTrans)
    /\ amount \in [Transfer -> Nat]
    /\ accounts \in [Transfer -> EAccounts]
    /\ pcLabels
    /\ TransPendingEquivalence
    /\ PendingTransDerived
    /\ PendingTransUniqueness

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
