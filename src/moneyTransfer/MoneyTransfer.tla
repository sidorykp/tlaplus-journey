----MODULE MoneyTransfer----
EXTENDS Naturals, FiniteSets, FiniteSetsExt, Sequences

CONSTANTS Empty, NAccount, NTransfer, NAvail

NNat == Nat \ {0}

Account == 1..NAccount

Transfer == 1..NTransfer

AT == [a: Account, t: Transfer]

EAccount == Account \cup {Empty}

ETransfer == Transfer \cup {Empty}

EmptyAccounts == [from |-> Empty, to |-> Empty]

(***************************************
Transfer -> Account -> credits/debits
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
        
        transAmount(t) == amount[t]
    
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
                    debits := debits \cup {<<[a |-> a, t |-> self], transAmount(self)>>};
                } else {
                    skip;
                }
            };
            
        crash:
            either skip or goto debit;

        credit:
            with (a = accounts[self].to) {
                if (creditPrecond(self)) {
                    credits := credits \cup {<<[a |-> a, t |-> self], transAmount(self)>>};
                }
            };
    }
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "a0f3b54f" /\ chksum(tla) = "901f83a3")
VARIABLES credits, debits, amount, accounts, pc

(* define statement *)
opAmount(dc) == dc[2]

transAmount(t) == amount[t]

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


vars == << credits, debits, amount, accounts, pc >>

ProcSet == (Transfer)

Init == (* Global variables *)
        /\ credits = {}
        /\ debits = {}
        /\ amount = [t \in Transfer |-> 0]
        /\ accounts = [t \in Transfer |-> EmptyAccounts]
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
              /\ UNCHANGED << credits, debits >>

debit(self) == /\ pc[self] = "debit"
               /\ LET a == accounts[self].from IN
                    IF debitPrecond(self)
                       THEN /\ debits' = (debits \cup {<<[a |-> a, t |-> self], transAmount(self)>>})
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
                        THEN /\ credits' = (credits \cup {<<[a |-> a, t |-> self], transAmount(self)>>})
                        ELSE /\ TRUE
                             /\ UNCHANGED credits
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

transPending == {t \in Transfer: AmountIsPending(t)}

AmountPendingTotal == MapThenSumSet(transAmount, transPending)

Imbalance == CreditTotal - DebitTotal + AmountPendingTotal

NonEmptyAccounts(t) ==
    /\ accounts[t].from # Empty
    /\ accounts[t].to # Empty
    
DifferentAccounts(t) == accounts[t].from # accounts[t].to

EAccounts == [from: EAccount, to: EAccount]

TypeOK ==
    /\ credits \in SUBSET (AT \X Nat)
    /\ IsFiniteSet(credits)
    /\ debits \in SUBSET (AT \X Nat)
    /\ IsFiniteSet(debits)
    /\ amount \in [Transfer -> Nat]
    /\ accounts \in [Transfer -> EAccounts]
    /\ pc \in [Transfer -> {"Done","init","debit","credit", "crash"}]

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
        

IndSpec == /\ IndInv /\ [][Next]_vars

BalanceSmall == 0..1

AmountSmall == 0..2

LimitedIndInv ==
    /\ \A a \in Account: accountCredits(a) \in BalanceSmall
    /\ \A a \in Account: accountDebits(a) \in BalanceSmall
    /\ \A t \in Transfer: transAmount(t) \in AmountSmall


====
