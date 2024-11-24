----MODULE MoneyTransfer----
EXTENDS Naturals, FiniteSets, FiniteSetsExt

CONSTANTS Empty, Account, Transfer, NAvail

NNat == Nat \ {0}

EAccount == Account \cup {Empty}

ETransfer == Transfer \cup {Empty}

EmptyAccounts == [from |-> Empty, to |-> Empty]

(***************************************
Transfer -> Account -> credit or debit
Transfer -> amount
***************************************)

(***************************************************************************
--algorithm MoneyTransfer {
    variables
       credits = {},
       debits = {},
       amount = [t \in Transfer |-> 0],
       accounts = [t \in Transfer |-> EmptyAccounts]

    define {
        opAmount(dc) == dc[2]
    
        accountCredits(a) == MapThenSumSet(LAMBDA c: IF c[1].a = a THEN opAmount(c) ELSE 0, credits)
        
        accountDebits(a) == MapThenSumSet(LAMBDA d: IF d[1].a = a THEN opAmount(d) ELSE 0, debits)
        
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
            
        transAmount(t) == amount[t]
    }

    process (trans \in Transfer)    
    {
        pick_accounts:
            with (account1 \in Account; account2 \in Account \ {account1}) {
                accounts[self] := [from |-> account1, to |-> account2];
            };

        pick_amount:
            with (a = accounts[self].from; am \in NNat) {
                await amountAvail(a) > 0;
                await am <= amountAvail(a);
                amount[self] := am;
            };
            
        debit:
            with (a = accounts[self].from) {
                if (debitPrecond(self)) {
                    debits := debits \cup {<<[a |-> a, t |-> self], amount[self]>>};
                } else {
                    skip;
                }
            };
            
        crash:
            either skip or goto debit;

        credit:
            with (a = accounts[self].to) {
                if (creditPrecond(self)) {
                    credits := credits \cup {<<[a |-> a, t |-> self], amount[self]>>};
                }
            };
    }
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "5bd2f2c8" /\ chksum(tla) = "e76fa81")
VARIABLES credits, debits, amount, accounts, pc

(* define statement *)
opAmount(dc) == dc[2]

accountCredits(a) == MapThenSumSet(LAMBDA c: IF c[1].a = a THEN opAmount(c) ELSE 0, credits)

accountDebits(a) == MapThenSumSet(LAMBDA d: IF d[1].a = a THEN opAmount(d) ELSE 0, debits)

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

transAmount(t) == amount[t]


vars == << credits, debits, amount, accounts, pc >>

ProcSet == (Transfer)

Init == (* Global variables *)
        /\ credits = {}
        /\ debits = {}
        /\ amount = [t \in Transfer |-> 0]
        /\ accounts = [t \in Transfer |-> EmptyAccounts]
        /\ pc = [self \in ProcSet |-> "pick_accounts"]

pick_accounts(self) == /\ pc[self] = "pick_accounts"
                       /\ \E account1 \in Account:
                            \E account2 \in Account \ {account1}:
                              accounts' = [accounts EXCEPT ![self] = [from |-> account1, to |-> account2]]
                       /\ pc' = [pc EXCEPT ![self] = "pick_amount"]
                       /\ UNCHANGED << credits, debits, amount >>

pick_amount(self) == /\ pc[self] = "pick_amount"
                     /\ LET a == accounts[self].from IN
                          \E am \in NNat:
                            /\ amountAvail(a) > 0
                            /\ am <= amountAvail(a)
                            /\ amount' = [amount EXCEPT ![self] = am]
                     /\ pc' = [pc EXCEPT ![self] = "debit"]
                     /\ UNCHANGED << credits, debits, accounts >>

debit(self) == /\ pc[self] = "debit"
               /\ LET a == accounts[self].from IN
                    IF debitPrecond(self)
                       THEN /\ debits' = (debits \cup {<<[a |-> a, t |-> self], amount[self]>>})
                       ELSE /\ TRUE
                            /\ UNCHANGED debits
               /\ pc' = [pc EXCEPT ![self] = "crash"]
               /\ UNCHANGED << credits, amount, accounts >>

crash(self) == /\ pc[self] = "crash"
               /\ \/ /\ TRUE
                     /\ pc' = [pc EXCEPT ![self] = "credit"]
                  \/ /\ pc' = [pc EXCEPT ![self] = "debit"]
               /\ UNCHANGED << credits, debits, amount, accounts >>

credit(self) == /\ pc[self] = "credit"
                /\ LET a == accounts[self].to IN
                     IF creditPrecond(self)
                        THEN /\ credits' = (credits \cup {<<[a |-> a, t |-> self], amount[self]>>})
                        ELSE /\ TRUE
                             /\ UNCHANGED credits
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << debits, amount, accounts >>

trans(self) == pick_accounts(self) \/ pick_amount(self) \/ debit(self)
                  \/ crash(self) \/ credit(self)

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

transPending == {t \in Transfer: AmountIsPending(t)}

AmountPendingTotal == MapThenSumSet(transAmount, transPending)

Imbalance == CreditTotal - DebitTotal + AmountPendingTotal

NonEmptyAccounts(t) ==
    /\ accounts[t].from # Empty
    /\ accounts[t].to # Empty
    
DifferentAccounts(t) == accounts[t].from # accounts[t].to

EAccounts == [from: EAccount, to: EAccount]

AT == [a: Account, t: Transfer]

pcLabels == pc \in [Transfer -> {"Done", "pick_accounts", "pick_amount", "debit", "credit", "crash"}]

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
    /\ \A t \in Transfer: pc[t] \in {"pick_accounts", "pick_amount"} => initPrecond(t)
    /\ \A t \in Transfer:
        pc[t] # "pick_accounts" <=> NonEmptyAccounts(t)

IndSpec == IndInv /\ [][Next]_vars

CommonIndInv ==
    /\ amount \in [Transfer -> Nat]
    /\ accounts \in [Transfer -> EAccounts]
    /\ pcLabels
    /\ Imbalance = 0
    /\ \A t \in Transfer:
        \/ accounts[t] = EmptyAccounts
        \/ DifferentAccounts(t) /\ NonEmptyAccounts(t)
    /\ \A t \in Transfer: pc[t] \in {"pick_accounts", "pick_amount"} => initPrecond(t)
    /\ \A t \in Transfer:
        pc[t] # "pick_accounts" <=> NonEmptyAccounts(t)

IndInvInteractiveStateConstraints ==
    /\ \A c \in credits: \E d \in debits: 
        /\ d[1].t = c[1].t
        /\ d[1].a # c[1].a
        /\ opAmount(d) = opAmount(c)
    /\ \A t \in Transfer:
        amount[t] = 0 <=> pc[t] \in {"pick_accounts", "pick_amount"}

====
