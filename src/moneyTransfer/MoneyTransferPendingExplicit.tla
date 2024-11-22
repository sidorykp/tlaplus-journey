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

        accountCreditsSum(a) == MapThenSumSetE(LAMBDA c: IF c[1].a = a THEN opAmount(c) ELSE 0, credits)

        accountDebitsSum(a) == MapThenSumSetE(LAMBDA d: IF d[1].a = a THEN opAmount(d) ELSE 0, debits)

        amountAvail(a) == NAvail + accountCreditsSum(a) - accountDebitsSum(a)
        
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
            with (account1 \in Account; account2 \in Account \ {account1}; am \in NNat) {
                await amountAvail(account1) > 0;
                await am <= amountAvail(account1);
                accounts[self] := [from |-> account1, to |-> account2];
                amount[self] := am;
            };
            
        debit:
            with (a = accounts[self].from) {
                if (debitPrecond(self)) {
                    debits := debits \cup {<<[a |-> a, t |-> self], amount[self]>>};
                    pendingTrans := pendingTrans \cup {<<self, amount[self]>>};
                } else {
                    skip;
                }
            };
            
        crash:
            either skip or goto debit;

        credit:
            with (a = accounts[self].to; at = [a |-> a, t |-> self]) {
                if (creditPrecond(self)) {
                    credits := credits \cup {<<at, amount[self]>>};
                    pendingTrans := pendingTrans \ {<<self, amount[self]>>};
                }
            };
    }
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "fb70e6a8" /\ chksum(tla) = "58f42086")
VARIABLES credits, debits, amount, accounts, pendingTrans, pc

(* define statement *)
opAmount(dc) == dc[2]

accountCreditsSum(a) == MapThenSumSetE(LAMBDA c: IF c[1].a = a THEN opAmount(c) ELSE 0, credits)

accountDebitsSum(a) == MapThenSumSetE(LAMBDA d: IF d[1].a = a THEN opAmount(d) ELSE 0, debits)

amountAvail(a) == NAvail + accountCreditsSum(a) - accountDebitsSum(a)

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
              /\ \E account1 \in Account:
                   \E account2 \in Account \ {account1}:
                     \E am \in NNat:
                       /\ amountAvail(account1) > 0
                       /\ am <= amountAvail(account1)
                       /\ accounts' = [accounts EXCEPT ![self] = [from |-> account1, to |-> account2]]
                       /\ amount' = [amount EXCEPT ![self] = am]
              /\ pc' = [pc EXCEPT ![self] = "debit"]
              /\ UNCHANGED << credits, debits, pendingTrans >>

debit(self) == /\ pc[self] = "debit"
               /\ LET a == accounts[self].from IN
                    IF debitPrecond(self)
                       THEN /\ debits' = (debits \cup {<<[a |-> a, t |-> self], amount[self]>>})
                            /\ pendingTrans' = (pendingTrans \cup {<<self, amount[self]>>})
                       ELSE /\ TRUE
                            /\ UNCHANGED << debits, pendingTrans >>
               /\ pc' = [pc EXCEPT ![self] = "crash"]
               /\ UNCHANGED << credits, amount, accounts >>

crash(self) == /\ pc[self] = "crash"
               /\ \/ /\ TRUE
                     /\ pc' = [pc EXCEPT ![self] = "credit"]
                  \/ /\ pc' = [pc EXCEPT ![self] = "debit"]
               /\ UNCHANGED << credits, debits, amount, accounts, pendingTrans >>

credit(self) == /\ pc[self] = "credit"
                /\ LET a == accounts[self].to IN
                     LET at == [a |-> a, t |-> self] IN
                       IF creditPrecond(self)
                          THEN /\ credits' = (credits \cup {<<at, amount[self]>>})
                               /\ pendingTrans' = pendingTrans \ {<<self, amount[self]>>}
                          ELSE /\ TRUE
                               /\ UNCHANGED << credits, pendingTrans >>
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << debits, amount, accounts >>

trans(self) == init(self) \/ debit(self) \/ crash(self) \/ credit(self)

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
    /\ pc[t] \in {"credit", "debit", "crash"}
    /\ creditPrecond(t)

AmountPendingTotal == MapThenSumSet(pendingTransAmount, pendingTrans)

transAmount(t) == amount[t]

AmountPendingTotalE == MapThenSumSet(transAmount, {t \in Transfer: AmountIsPending(t)})

AmountPendingTotalEquivalence == AmountPendingTotalE = AmountPendingTotal

TransInPendingTrans(t) == \E tp \in pendingTrans: tp[1] = t /\ tp[2] = amount[t]

TransPendingEquivalence == \A t \in Transfer: AmountIsPending(t)
    <=> pendingTrans # {} /\ TransInPendingTrans(t)

Imbalance == CreditTotal - DebitTotal + AmountPendingTotal

NonEmptyAccounts(t) ==
    /\ accounts[t].from # Empty
    /\ accounts[t].to # Empty
    
DifferentAccounts(t) == accounts[t].from # accounts[t].to

EAccounts == [from: EAccount, to: EAccount]

AT == [a: Account, t: Transfer]

TN == Transfer \X Nat

pcLabels == pc \in [Transfer -> {"Done", "init", "debit", "credit", "crash"}]

PendingTransDerived == \A pt \in pendingTrans: \E d \in debits: d[1].t = pt[1] /\ d[2] = pt[2]

PendingTransUniqueness == pendingTrans = {} \/ ~\E pt1, pt2 \in pendingTrans: pt1 # pt2 /\ pt1[1] = pt2[1]

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
    /\ AmountPendingTotalEquivalence

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
